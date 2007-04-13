/*
Copyright (C) 2006  The PARI group.

This file is part of the PARI package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

#include "pari.h"
#include "paripriv.h"
#include "anal.h"
#include "opcode.h"

THREAD char *gp_function_name=NULL;

#define initial_value(ep) ((ep)+1)

/********************************************************************/
/*                                                                  */
/*         break/next/return/allocatemem handling                   */
/*                                                                  */
/********************************************************************/

static THREAD long br_status, br_count;
enum { br_NONE = 0, br_BREAK, br_NEXT, br_MULTINEXT, br_RETURN, br_ALLOCMEM };
static THREAD GEN br_res=NULL;

long
loop_break(void)
{
  switch(br_status)
  {
    case br_MULTINEXT :
      if (! --br_count) br_status = br_NEXT;
      return 1;
    case br_BREAK : if (! --br_count) br_status = br_NONE; /* fall through */
    case br_RETURN: return 1;
    case br_ALLOCMEM: pari_err(talker,"can't allow allocatemem() in loops");
    case br_NEXT: br_status = br_NONE; /* fall through */
  }
  return 0;
}

void
reset_break(void)
{
  br_status = br_NONE;
  if (br_res) { killbloc(br_res); br_res = NULL; }
}

long
did_break(void) { return br_status; }

GEN
return0(GEN x)
{
  GEN y = br_res;
  br_res = (x && x != gnil)? gclone(x): NULL;
  if (y) gunclone(y);
  br_status = br_RETURN; return NULL;
}

GEN
next0(long n)
{
  if (n < 1)
    pari_err(talker,"positive integer expected in next");
  if (n == 1) br_status = br_NEXT;
  else
  {
    br_count = n-1;
    br_status = br_MULTINEXT;
  }
  return NULL;
}

GEN
break0(long n)
{
  if (n < 1)
    pari_err(talker,"positive integer expected in break");
  br_count = n;
  br_status = br_BREAK; return NULL;
}

void
allocatemem0(GEN z)
{
  ulong newsize;
  if (!z) newsize = 0;
  else {
    newsize = itou(z);
    if (signe(z) < 0) pari_err(talker,"negative size in allocatemem");
  }
  (void)allocatemoremem(newsize);
  br_status = br_ALLOCMEM;
}

/*******************************************************************/
/*                                                                 */
/*                            VARIABLES                            */
/*                                                                 */
/*******************************************************************/

/* As a rule, ep->value is a clone (COPY). push_val and pop_val are private
 * functions for use in sumiter: we want a temporary ep->value, which is NOT
 * a clone (PUSH), to avoid unnecessary copies. */

enum {PUSH_VAL = 0, COPY_VAL = 1};

/* ep->args is the stack of old values (INITIAL if initial value, from
 * installep) */
typedef struct var_cell {
  struct var_cell *prev; /* cell associated to previous value on stack */
  GEN value; /* last value (not including current one, in ep->value) */
  char flag; /* status of _current_ ep->value: PUSH or COPY ? */
} var_cell;
#define INITIAL NULL
/* Push x on value stack associated to ep. Assume EpVALENCE(ep)=EpVAR/EpGVAR */
static void
new_val_cell(entree *ep, GEN x, char flag)
{
  var_cell *v = (var_cell*) gpmalloc(sizeof(var_cell));
  v->value  = (GEN)ep->value;
  v->prev   = (var_cell*) ep->pvalue;
  v->flag   = flag;

  /* beware: f(p) = Nv = 0
   *         Nv = p; f(Nv) --> this call would destroy p [ isclone ] */
  ep->value = (flag == COPY_VAL)? gclone(x):
                                  (x && isclone(x))? gcopy(x): x;
  /* Do this last. In case the clone is <C-C>'ed before completion ! */
  ep->pvalue= (char*)v;
  ep->valence=EpVAR;
}

void
freeep(entree *ep)
{
  if (foreignFuncFree && ep->code && (*ep->code == 'x'))
    (*foreignFuncFree)(ep); /* function created by foreign interpreter */

  if (EpSTATIC(ep)) return; /* gp function loaded at init time */
  if (ep->help) {gpfree(ep->help); ep->help=NULL;}
  if (ep->code) {gpfree(ep->code); ep->code=NULL;}
  switch(EpVALENCE(ep))
  {
    case EpUSER:
      gunclone(ep->lvars); ep->lvars=NULL;
      while (ep->pvalue!=INITIAL) pop_val(ep);
      gunclone((GEN)ep->value); ep->value=NULL;
      break;
    case EpVAR:
    case EpGVAR:
      while (ep->pvalue!=INITIAL) pop_val(ep);
      break;
    case EpALIAS:
      gunclone((GEN)ep->value); ep->value=NULL; break;
  }
}

void
push_val(entree *ep, GEN a)
{
  new_val_cell(ep, a, PUSH_VAL); 
}

/* kill ep->value and replace by preceding one, poped from value stack */
void
pop_val(entree *ep)
{
  var_cell *v = (var_cell*) ep->pvalue;

  if (v == INITIAL) return;
  if (v->flag == COPY_VAL) killbloc((GEN)ep->value);
  ep->value  = v->value;
  ep->pvalue = (char*) v->prev;
  if (ep->pvalue == INITIAL)
  {
    if (ep->code) ep->valence=EpUSER;
    else if (ep->value==NULL) ep->valence=EpNEW;
  }
  gpfree((void*)v);
}

INLINE void
copyvalue(entree *ep, GEN x) {
  new_val_cell(ep, x, typ(x) >= t_VEC ? COPY_VAL: PUSH_VAL);
}

/* as above IF ep->value was PUSHed, or was created after block number 'loc'
   return 0 if not deleted, 1 otherwise [for recover()] */
int
pop_val_if_newer(entree *ep, long loc)
{
  var_cell *v = (var_cell*) ep->pvalue;

  if (v == INITIAL) return 0;
  if (v->flag == COPY_VAL && !pop_entree_bloc(ep, loc)) return 0;
  ep->value = v->value;
  ep->pvalue= (char*) v->prev;
  if (ep->pvalue == INITIAL)
  {
    if (ep->code) ep->valence=EpUSER;
    else if (ep->value==NULL) ep->valence=EpNEW;
  }
  gpfree((void*)v); return 1;
}

/* set new value of ep directly to val (COPY), do not save last value unless
 * it's INITIAL. */
void
changevalue(entree *ep, GEN x)
{
  var_cell *v = (var_cell*) ep->pvalue;
  if (v == INITIAL) new_val_cell(ep, x, COPY_VAL);
  else
  {
    x = gclone(x); /* beware: killbloc may destroy old x */
    if (v->flag == COPY_VAL) killbloc((GEN)ep->value); else v->flag = COPY_VAL;
    ep->value = (void*)x;
  }
}

/* as above, but PUSH, not COPY */
void
changevalue_p(entree *ep, GEN x)
{
  var_cell *v = (var_cell*) ep->pvalue;
  if (v == INITIAL) new_val_cell(ep,x, PUSH_VAL);
  else
  {
    if (v->flag == COPY_VAL) { killbloc((GEN)ep->value); v->flag = PUSH_VAL; }
    ep->value = (void*)x;
  }
}

/* make GP variables safe for avma = top */
void
var_make_safe(void)
{
  long n;
  entree *ep;
  for (n = 0; n < functions_tblsz; n++)
    for (ep = functions_hash[n]; ep; ep = ep->next)
      if (EpVALENCE(ep) == EpVAR)
      { /* make sure ep->value is a COPY */
        var_cell *v = (var_cell*)ep->pvalue;
        if (v && v->flag == PUSH_VAL) {
          GEN x = (GEN)ep->value;
          if (x) changevalue(ep, (GEN)ep->value); else pop_val(ep);
        }
      }
}

struct derivgenwrap_s 
{
  GEN (*f)(ANYARG);
  GEN *x;
};

static GEN
derivgenwrap(GEN x, void* E)
{
  struct derivgenwrap_s *c=(struct derivgenwrap_s *) E;
  GEN z = c->f(x,c->x[1],c->x[2],c->x[3],c->x[4],c->x[5],c->x[6],c->x[7]);
  if (!z) 
    /*This cannot actually happen since no functions returning NULL
     *take a GEN as first parameter*/
    pari_err(talker, "break not allowed here");
  return z;
}

static long
check_array_index(long c, long max)
{
  if (c < 1 || c >= max)
  {
    char s[80];
    sprintf(s,"array index (%ld) out of allowed range ",c);
    if (max == 1) strcat(s, "[none]");
    else if (max == 2) strcat(s, "[1]");
    else sprintf(s,"%s[1-%ld]",s,max-1);
    pari_err(talker,s);
  }
  return c;
}

typedef struct matcomp
{
  GEN *ptcell;
  GEN parent;
  int full_col, full_row;
} matcomp;

typedef struct gp_pointer
{
  matcomp c;
  GEN x;
  entree *ep;
} gp_pointer;


/* assign res at *pt in "simple array object" p and return it, or a copy.
 * In the latter case, reset avma to av */
static GEN
change_compo(matcomp *c, GEN res)
{
  GEN p = c->parent, *pt = c->ptcell;
  long i;

  if (typ(p) == t_VECSMALL)
  {
    if (typ(res) != t_INT || is_bigint(res))
      pari_err(talker,"not a suitable VECSMALL component");
    *pt = (GEN)itos(res); return res;
  }
  if (c->full_row)
  {
    if (typ(res) != t_VEC || lg(res) != lg(p))
      pari_err(talker,"incorrect type or length in matrix assignment");
    for (i=1; i<lg(p); i++)
    {
      GEN p1 = gcoeff(p,c->full_row,i); if (isclone(p1)) killbloc(p1);
      gcoeff(p,c->full_row,i) = gclone(gel(res,i));
    }
    return res;
  }
  if (c->full_col)
    if (typ(res) != t_COL || lg(res) != lg(*pt))
      pari_err(talker,"incorrect type or length in matrix assignment");

  res = gclone(res);
  killbloc(*pt);
  return *pt = res;
}

/***************************************************************************
 **                                                                       **
 **                           Byte-code evaluator                         **
 **                                                                       **
 ***************************************************************************/

static long st[1024];
static long sp=0;

static void closure_eval(GEN C);

INLINE GEN
copyupto(GEN z, GEN t)
{
  if (isclone(z) || (z>t && (ulong)z<top))
    return gcopy(z);
  else
    return z;
}

static GEN
derivuserwrap(GEN x, void* E)
{
  pari_sp ltop;
  entree *ep=(entree*)E;
  GEN z;
  long saved_sp=sp;
  long j;
  gel(st,sp)=x;
  for (j=1;j<ep->arity;j++)
    gel(st,sp+j)=gel(st,sp+j-ep->arity);
  sp+=ep->arity;
  ltop=avma;
  closure_eval((GEN) ep->value);
  if (br_status)
  {
    if (br_status!=br_RETURN)
      pari_err(talker, "break/next/allocatemem not allowed here");
    avma=ltop;
    sp = saved_sp;
    z = br_res ? gcopy(br_res) : gnil;
    reset_break();
  }
  else
  {
    z = gerepileupto(ltop, gel(st,--sp));
    if (isclone(z)) z = gcopy(z);
  }
  for(j=1;j<lg(ep->lvars);j++)
    pop_val((entree*)ep->lvars[j]);
  return z;
}

INLINE long
closure_varn(GEN x)
{
  if (typ(x) != t_POL || lg(x) != 4 ||
      !gcmp0(gel(x,2)) || !gcmp1(gel(x,3))) 
    pari_err(varer1,"variable name expected",NULL,NULL);
  return varn(x);
}

INLINE void
closure_castgen(GEN z, long mode)
{
  switch (mode)
  {
  case Ggen:
    gel(st,sp++)=z;
    break;
  case Gsmall:
    st[sp++]=itos(z);
    break;
  case Gvar:
    st[sp++]=closure_varn(z);
    break;
  case Gvoid:
    break;
  default:
    pari_err(bugparier,"closure_castgen, type unknown");
  }
}

INLINE void
closure_castlong(long z, long mode)
{
  switch (mode)
  {
  case Gsmall:
    st[sp++]=z;
    break;
  case Ggen:
    gel(st,sp++)=stoi(z);
    break;
  case Gvar:
    pari_err(varer1,"variable name expected",NULL,NULL);
  default:
    pari_err(bugparier,"closure_castlong, type unknown");
  }
}

static void
closure_eval(GEN C)
{
  gp_pointer ptrs[16];
  long rp=0;
  char *code=GSTR(gel(C,1))-1;
  GEN oper=gel(C,2);
  GEN data=gel(C,3);
  long pc, j;
  for(pc=1;pc<lg(oper);pc++)
  {
    op_code opcode=(op_code) code[pc];
    long operand=oper[pc];
    entree *ep;
    if (sp<0) pari_err(bugparier,"closure_eval, stack underflow");
    if (sp>1000) pari_err(talker,"evaluator stack exhausted");
    switch(opcode)
    {
    case OCpushlong:
        st[sp++]=operand;
        break;
    case OCpushgen:
        gel(st,sp++)=gel(data,operand);
        break;
    case OCpushreal:
        gel(st,sp++)=strtor(GSTR(data[operand]),precreal);
        break;
    case OCpushstoi:
        gel(st,sp++)=stoi(operand);
        break;
    case OCpushvar:
        ep=(entree*)operand;
        if (gel(initial_value(ep),0)==NULL)
          manage_var(manage_var_create,ep);
        gel(st,sp++)=(GEN)initial_value(ep);
        break;
    case OCpushvalue:
        ep=(entree*)operand;
        switch(ep->valence)
        {
        case EpNEW:
          ep->valence=EpVAR;
          manage_var(manage_var_create,ep);
          ep->value=initial_value(ep);
        case EpVAR: case EpGVAR: /*FALL THROUGH*/
          gel(st,sp++)=(GEN)ep->value;
          break;
        default:
          gel(st,sp++)=0;
          goto calluser; /*Maybe it is a function*/
        }
        break;
    case OCnewptr:
        if (rp<16)
        {
          gp_pointer *g = &ptrs[rp++];
          g->ep = (entree*) operand;
          switch (g->ep->valence)
          {
          case EpNEW:
            g->ep->valence=EpVAR;
            manage_var(manage_var_create,g->ep);
            g->ep->value=initial_value(g->ep);
          case EpVAR: case EpGVAR:/*FALL THROUGH*/
            g->x = (GEN) g->ep->value;
            break;
          default:
            pari_err(varer1,"variable name expected",NULL,NULL);
          }
          break;
        }
        else pari_err(impl,"more than 16 references");
    case OCpushptr:
        {
          gp_pointer *g = &ptrs[rp-1];
          gel(st,sp++) = (GEN)&(g->x); 
        }
        break;
    case OCendptr:
        for(j=0;j<operand;j++)
        {
          gp_pointer *g = &(ptrs[--rp]);
          if (g->ep) changevalue(g->ep, g->x);
          else (void)change_compo(&(g->c), g->x);
        }
        break;
    case OCstore:
        ep=(entree *)operand;
        switch (ep->valence)
        {
        case EpNEW:
          ep->valence=EpVAR;
          manage_var(manage_var_create,ep);
          ep->value=initial_value(ep);
        case EpVAR: case EpGVAR:/*FALL THROUGH*/
          changevalue(ep, gel(st,--sp));
          break;
        default:
          pari_err(varer1,"variable name expected",NULL,NULL);
        }
        break;
    case OCstackgen:
        gmael(st,sp-2,operand)=copyupto(gel(st,sp-1),gel(st,sp-2));
        sp--;
        break;
    case OCprecreal:
        st[sp++]=precreal;
        break;
    case OCprecdl:
        st[sp++]=precdl;
        break;
    case OCstoi:
        gel(st,sp-1)=stoi(st[sp-1]);
        break;
    case OCitos:
        st[sp-1]=itos(gel(st,sp-1));
        break;
    case OCtostr:
        if (operand==1)
          st[sp-1] = (long) GSTR(GENtoGENstr(gel(st,sp-1)));
        else
        {
          GEN L=cgetg(operand+1,t_VEC);
          sp-=operand;
          for (j=1; j<=operand; j++)
            gel(L,j) = GENtoGENstr(gel(st,sp-1+j));
          st[sp++] = (long) GSTR(concat(L,NULL));
        }
        break;
    case OCvarn:
        st[sp-1] = closure_varn(gel(st,sp-1));
        break;
    case OCcopy:
        gel(st,sp-1) = gcopy(gel(st,sp-1));
        break;
    case OCcompo1:
        {
          GEN  p=gel(st,sp-2);
          long c=st[sp-1];
          sp-=2;
          switch(typ(p))
          {
          case t_VEC: case t_COL:
            check_array_index(c, lg(p));
            closure_castgen(gel(p,c),operand);
            break;
          case t_LIST:
            check_array_index(c,lgeflist(p)-1);
            closure_castgen(gel(p,c+1),operand);
            break;
          case t_VECSMALL:
            check_array_index(c,lg(p));
            closure_castlong(p[c],operand);
            break;
          default:
            pari_err(talker,"_[_]: not a vector");
            break;
          }
          break;
        }
    case OCcompo1ptr:
        { 
          long c=st[sp-1];
          gp_pointer *g = &ptrs[rp-1];
          matcomp *C=&g->c;
          GEN p;
          if (g->ep)
          {
            g->ep=NULL;
            C->full_col = C->full_row = 0;
            C->parent   = (GEN)    g->x;
            C->ptcell   = (GEN *) &g->x;
          }
          p=*C->ptcell;
          sp--;
          switch(typ(p))
          {
          case t_VEC: case t_COL: case t_VECSMALL:
            check_array_index(c, lg(p));
            C->ptcell = (GEN *) p+c;
            break;
          case t_LIST:
            check_array_index(c,lgeflist(p)-1);
            C->ptcell = (GEN *) p+c+1;
            break;
          default:
            pari_err(talker,"_[_]: not a vector");
          }
          C->parent   = p;
          g->x = *(g->c.ptcell);
          break;
        }
    case OCcompo2:
        {
          GEN  p=gel(st,sp-3);
          long c=st[sp-2];
          long d=st[sp-1];
          if (typ(p)!=t_MAT)
            pari_err(talker,"_[_,_]: not a matrix");
          check_array_index(d, lg(p));
          check_array_index(c, lg(p[d]));
          sp-=3;
          closure_castgen(gcoeff(p,c,d),operand);
          break;
        }
    case OCcompo2ptr:
        {
          long b=st[sp-2];
          long c=st[sp-1];
          gp_pointer *g = &ptrs[rp-1];
          matcomp *C=&g->c;
          GEN p;
          if (g->ep)
          {
            g->ep=NULL;
            C->full_col = C->full_row = 0;
            C->ptcell   = (GEN *) &g->x;
          }
          p=*C->ptcell;
          sp-=2;
          if (typ(p)!=t_MAT)
            pari_err(talker,"_[_,_]: not a matrix");
          check_array_index(b, lg(p));
          check_array_index(c, lg(p[b]));
          C->ptcell = (GEN *) gel(p,c)+b;
          C->parent   = p;
          g->x = *(g->c.ptcell);
          break;
        }
    case OCcompoC:
        {
          GEN  p=gel(st,sp-2);
          long c=st[sp-1];
          if (typ(p)!=t_MAT)
            pari_err(talker,"_[,_]: not a matrix");
          check_array_index(c, lg(p));
          sp--;
          gel(st,sp-1) = gel(p,c);
          break;
        }
    case OCcompoCptr:
        {
          long c=st[sp-1];
          gp_pointer *g = &ptrs[rp-1];
          matcomp *C=&g->c;
          GEN p;
          if (g->ep)
          {
            g->ep=NULL;
            C->full_row = 0;
            C->ptcell   = (GEN *) &g->x;
          }
          p=*C->ptcell;
          sp--;
          if (typ(p)!=t_MAT)
            pari_err(talker,"_[,_]: not a matrix");
          check_array_index(c, lg(p));
          C->ptcell = (GEN *) p+c;
          C->full_col = c;
          C->parent   = p;
          g->x = *(g->c.ptcell);
          break;
        }
    case OCcompoL:
        {
          GEN  p=gel(st,sp-2);
          long r=st[sp-1];
          sp--;
          if (typ(p)!=t_MAT)
            pari_err(talker,"_[_,]: not a matrix");
          if (lg(p)==1) pari_err(talker,"a 0x0 matrix has no elements");
          check_array_index(r,lg(p[1]));
          gel(st,sp-1) = row(p,r);
          break;
        }
    case OCcompoLptr:
        {
          long r=st[sp-1];
          gp_pointer *g = &ptrs[rp-1];
          matcomp *C=&g->c;
          GEN p, p2;
          if (g->ep)
          {
            g->ep=NULL;
            C->full_col = 0;
            C->ptcell   = (GEN *) &g->x;
          }
          p=*C->ptcell;
          sp--;
          if (typ(p)!=t_MAT)
            pari_err(talker,"_[_,]: not a matrix");
          if (lg(p)==1) pari_err(talker,"a 0x0 matrix has no elements");
          check_array_index(r,lg(p[1]));
          p2 = rowcopy(p,r);
          C->full_row = r; /* record row number */
          C->ptcell = &p2;
          C->parent   = p;
          g->x = *(g->c.ptcell);
          break;
        }
    case OCgetarg:
        ep=(entree *)operand;
        if (gel(st,sp-1))
          copyvalue(ep,gel(st,sp-1));
        else
          copyvalue(ep,gen_0);
        sp--;
        break;
    case OCdefaultarg:
        ep=(entree *)operand;
        if (gel(st,sp-2))
          copyvalue(ep,gel(st,sp-2));
        else
        {
          GEN z = closure_evalgen(gel(st,sp-1));
          if (!z) pari_err(talker,"break not allowed in function parameter");
          copyvalue(ep,z);
        }
        sp-=2;
        break;
    case OCglobalvar:
        ep=(entree *)operand;
        if (ep->valence==EpNEW)
        {
          manage_var(manage_var_create,ep);
          ep->value=initial_value(ep);
        }
        ep->valence = EpGVAR;
        if (gel(st,sp-1))
          changevalue(ep,gel(st,sp-1));
        sp--;
        break;
#define ARGS st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7]
    case OCderivgen:
        {
          entree *ep=(entree*)operand;
          GEN res;
          struct derivgenwrap_s c;
          sp-=ep->arity;
          gp_function_name=ep->name;
          c.f = (GEN (*) (ANYARG)) ep->value;
          c.x = (GEN*) st+sp;
          res = derivnum((void*)&c, derivgenwrap, gel(st,sp), precreal);
          gp_function_name=NULL;
          gel(st,sp++)=res;
          break;
        }
    case OCcallgen:
        {
          entree *ep=(entree*)operand;
          GEN res;
          sp-=ep->arity;
          gp_function_name=ep->name;
          res = ((GEN (*)(ANYARG))ep->value)(ARGS);
          if (br_status) return;
          gp_function_name=NULL;
          gel(st,sp++)=res;
          break;
        }
    case OCcallgen2:
        {
          entree *ep=(entree*)operand;
          GEN res;
          sp-=ep->arity;
          gp_function_name=ep->name;
          res = ((GEN (*)(GEN,GEN))ep->value)(gel(st,sp),gel(st,sp+1));
          if (br_status) return;
          gp_function_name=NULL;
          gel(st,sp++)=res;
          break;
        }
    case OCcalllong:
        {
          entree *ep=(entree*)operand;
          long res;
          sp-=ep->arity;
          gp_function_name=ep->name;
          res = ((long (*)(ANYARG))ep->value)(ARGS);
          if (br_status) return;
          gp_function_name=NULL;
          st[sp++] = res;
          break;
        }
    case OCcallint:
        {
          entree *ep=(entree*)operand;
          long res;
          sp-=ep->arity;
          gp_function_name=ep->name;
          res = ((int (*)(ANYARG))ep->value)(ARGS);
          if (br_status) return;
          gp_function_name=NULL;
          st[sp++] = res;
          break;
        }
    case OCcallvoid:
        {
          entree *ep=(entree*)operand;
          sp-=ep->arity;
          gp_function_name=ep->name;
          ((void (*)(ANYARG))ep->value)(ARGS);
          if (br_status) return;
          gp_function_name=NULL;
          break;
        }
#undef ARGS
    case OCderivuser:
        {
          GEN z;
          long n=st[--sp];
          ep = (entree*) operand;
          if (ep->valence!=EpUSER)
            pari_err(talker,"function '%s' not yet defined",ep->name);
          if (n>ep->arity)
            pari_err(talker,"Too many arguments for function '%s'",ep->name);
          for (j=n+1;j<=ep->arity;j++)
            gel(st,sp++)=0;
          z = derivnum((void*)ep, derivuserwrap, gel(st,sp-ep->arity), precreal);
          sp-=ep->arity;
          gel(st, sp++) = z;
          break;
        }
    case OCcalluser: 
calluser:
        {
          pari_sp ltop;
          long n=st[--sp];
          long saved_sp=sp;
          entree *ep = (entree*) operand;
          GEN z, lvars=ep->lvars;
          if (ep->valence!=EpUSER)
          {
            int w;
            if (whatnow_fun && (w = whatnow_fun(ep->name,1)))
              pari_err(obsoler, ep->name, w);
            else
              pari_err(talker,"function '%s' not yet defined",ep->name);
          }
          if (n>ep->arity)
            pari_err(talker,"Too many arguments for function '%s'",ep->name);
          for (j=n+1;j<=ep->arity;j++)
            gel(st,sp++)=0;
#ifdef STACK_CHECK
          if (PARI_stack_limit && (void*) &z <= PARI_stack_limit)
            pari_err(talker, "deep recursion");
#endif
          ltop=avma;
          closure_eval((GEN) ep->value);
          if (br_status)
          {
            if (br_status!=br_RETURN)
              pari_err(talker, "break/next/allocatemem not allowed here");
            avma=ltop;
            sp = saved_sp - n;
            z = br_res ? gcopy(br_res) : gnil;
            reset_break();
          }
          else
          {
            z = gerepileupto(ltop, gel(st,--sp));
            if (isclone(z)) z = gcopy(z);
          }
          for(j=1;j<lg(lvars);j++)
            pop_val((entree*)lvars[j]);
          gel(st, sp++) = z;
          break;
        }
    case OCvec:
        gel(st,sp++)=cgetg(operand,t_VEC);
        break;
    case OCcol:
        gel(st,sp++)=cgetg(operand,t_COL);
        break;
    case OCmat:
        {
          GEN z;
          long l=st[sp-1];
          z=cgetg(operand,t_MAT);
          for(j=1;j<operand;j++)
            gel(z,j) = cgetg(l,t_COL); 
          gel(st,sp-1) = z;
        } 
        break;
    case OCdeffunc:
        ep=(entree*)operand;
        switch(ep->valence)
        {
        case EpUSER: 
          gpfree(ep->code);
          /*FIXME: the function might be in use...
            gunclone(ep->value);
          gunclone(ep->lvars);
          */
          break;
        case EpNEW:
          ep->valence = EpUSER;
          break;
        default:
          pari_err(talker,"function name expected");
        }
        ep->value = (void *) gclone(gel(st,sp-4));
        ep->lvars = gclone(gel(st,sp-3));
        ep->code  = pari_strdup(GSTR(gel(st,sp-2)));
        ep->arity = st[sp-1];
        sp-=4;
        break;
    case OCpop:
        sp-=operand;
        break;
    }
  }
}

GEN
closure_evalgen(GEN C)
{
  pari_sp ltop=avma;
  long saved_sp=sp;
  closure_eval(C);
  if (br_status)
  {
    sp=saved_sp;
    if (br_status!=br_ALLOCMEM) avma=ltop; 
    return NULL;
  }
  return gerepileupto(ltop,gel(st,--sp));
}

void
closure_evalvoid(GEN C)
{
  pari_sp ltop=avma;
  long saved_sp=sp;
  closure_eval(C);
  if (br_status)
  {
    sp=saved_sp;
    if (br_status!=br_ALLOCMEM) avma=ltop; 
  }
  else
    avma=ltop;
}

void
closure_reset(void) {sp=0;}

void
closure_check(void)
{
  if (sp) 
    pari_err(bugparier,"closure_eval, stack not empty");
}

INLINE const char *
disassemble_cast(long mode)
{
  switch (mode)
  {
  case Gsmall:
    return "small";
  case Ggen:
    return "gen";
  case Gvar:
    return "var";
  case Gvoid:
    return "void";
  default:
    return "unknown";
  }
}

void
closure_disassemble(GEN C)
{
  char * code;
  GEN oper;
  long i;
  if (typ(C)==t_STR)
  {
    entree *ep=fetch_entry(GSTR(C),strlen(GSTR(C)));
    if (ep->valence!=EpUSER)
      pari_err(typeer,"disassemble");
    C=(GEN)ep->value;
  }
  if (typ(C)!=t_VEC || lg(C)!=4 || typ(C[1])!=t_STR || typ(C[2])!=t_VECSMALL) 
    pari_err(typeer,"disassemble");
  code=GSTR(gel(C,1))-1;
  oper=gel(C,2);
  for(i=1;i<lg(oper);i++)
  {
    op_code opcode=(op_code) code[i];
    long operand=oper[i];
    entree *ep;
    pariprintf("%05ld\t",i);
    switch(opcode)
    {
    case OCpushlong:
      if (operand==(long)gnil)
        pariprintf("pushlong\tgnil\n");
      else
        pariprintf("pushlong\t%ld\n",operand);
      break;
    case OCpushgen:
      pariprintf("pushgen\t\t%ld\n",operand);
      break;
    case OCpushreal:
      pariprintf("pushreal\t%ld\n",operand);
      break;
    case OCpushstoi:
      pariprintf("pushstoi\t%ld\n",operand);
      break;
    case OCpushvar:
      ep=(entree*)operand;
      pariprintf("pushvar\t%s\n",ep->name);
      break;
    case OCpushvalue:
      ep=(entree*)operand;
      pariprintf("pushvalue\t%s\n",ep->name);
      break;
    case OCnewptr:
      ep=(entree*)operand;
      pariprintf("newptr\t\t%s\n",ep->name);
      break;
    case OCpushptr:
      pariprintf("pushptr\n");
      break;
    case OCstackgen:
      pariprintf("stackgen\t%ld\n",operand);
      break;
    case OCendptr:
      pariprintf("endptr\t\t%ld\n",operand);
      break;
    case OCstore:
      ep=(entree *)operand;
      pariprintf("store\t\t%s\n",ep->name);
      break;
    case OCprecreal:
      pariprintf("precreal\n");
      break;
    case OCprecdl:
      pariprintf("precdl\n");
      break;
    case OCstoi:
      pariprintf("stoi\n");
      break;
    case OCitos:
      pariprintf("itos\n");
      break;
    case OCtostr:
      pariprintf("tostr\t\t%ld\n",operand);
      break;
    case OCvarn:
      pariprintf("varn\n");
      break;
    case OCcopy:
      pariprintf("copy\n");
      break;
    case OCcompo1:
      pariprintf("compo1\t\t%s\n",disassemble_cast(operand));
      break;
    case OCcompo1ptr:
      ep=(entree*)operand;
      pariprintf("compo1ptr\n");
      break;
    case OCcompo2:
      pariprintf("compo2\t\t%s\n",disassemble_cast(operand));
      break;
    case OCcompo2ptr:
      pariprintf("compo2ptr\n");
      break;
    case OCcompoC:
      pariprintf("compoC\n");
      break;
    case OCcompoCptr:
      pariprintf("compoCptr\n");
      break;
    case OCcompoL:
      pariprintf("compoL\n");
      break;
    case OCcompoLptr:
      pariprintf("compoLptr\n");
      break;
    case OCgetarg:
      ep=(entree*)operand;
      pariprintf("getarg\t\t%s\n",ep->name);
      break;
    case OCdefaultarg:
      ep=(entree*)operand;
      pariprintf("defaultarg\t%s\n",ep->name);
      break;
    case OCglobalvar:
      ep=(entree*)operand;
      pariprintf("globalvar\t%s\n",ep->name);
      break;
    case OCderivgen:
      ep=(entree*)operand;
      pariprintf("derivgen\t\t%s\n",ep->name);
      break;
    case OCcallgen:
      ep=(entree*)operand;
      pariprintf("callgen\t\t%s\n",ep->name);
      break;
    case OCcallgen2:
      ep=(entree*)operand;
      pariprintf("callgen2\t%s\n",ep->name);
      break;
    case OCcalllong:
      ep=(entree*)operand;
      pariprintf("calllong\t%s\n",ep->name);
      break;
    case OCcallint:
      ep=(entree*)operand;
      pariprintf("callint\t\t%s\n",ep->name);
      break;
    case OCcallvoid:
      ep=(entree*)operand;
      pariprintf("callvoid\t%s\n",ep->name);
      break;
    case OCderivuser:
      ep=(entree*)operand;
      pariprintf("derivuser\t\t%s\n",ep->name);
      break;
    case OCcalluser:
      ep=(entree*)operand;
      pariprintf("calluser\t%s\n",ep->name);
      break;
    case OCvec:
      pariprintf("vec\t\t%ld\n",operand);
      break;
    case OCcol:
      pariprintf("col\t\t%ld\n",operand);
      break;
    case OCmat:
      pariprintf("mat\t\t%ld\n",operand);
      break;
    case OCdeffunc:
      ep=(entree*)operand;
      pariprintf("deffunc\t\t%s\n",ep->name);
      break;
    case OCpop:
      pariprintf("pop\t\t%ld\n",operand);
      break;
    }
  }
}
