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

/********************************************************************/
/*                                                                  */
/*         break/next/return/allocatemem handling                   */
/*                                                                  */
/********************************************************************/

static THREAD long br_status, br_count;
enum { br_NONE = 0, br_BREAK, br_NEXT, br_MULTINEXT, br_RETURN };
static THREAD GEN br_res;

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
    case br_NEXT: br_status = br_NONE; /* fall through */
  }
  return 0;
}

static void
reset_break(void)
{
  br_status = br_NONE;
  if (br_res) { gunclone_deep(br_res); br_res = NULL; }
}

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
    if (typ(z) != t_INT) pari_err(typeer,"allocatemem");
    newsize = itou(z);
    if (signe(z) < 0) pari_err(talker,"negative size in allocatemem");
  }
  evalstate_reset();
  (void)allocatemoremem(newsize);
  global_err_data = NULL;
  cb_pari_err_recover(-1);
}

/*******************************************************************/
/*                                                                 */
/*                            VARIABLES                            */
/*                                                                 */
/*******************************************************************/

/* As a rule, ep->value is a clone (COPY). push_val and pop_val are private
 * functions for use in sumiter: we want a temporary ep->value, which is NOT
 * a clone (PUSH), to avoid unnecessary copies. */

enum {PUSH_VAL = 0, COPY_VAL = 1, DEFAULT_VAL = 2};

/* ep->args is the stack of old values (INITIAL if initial value, from
 * installep) */
typedef struct var_cell {
  struct var_cell *prev; /* cell associated to previous value on stack */
  GEN value; /* last value (not including current one, in ep->value) */
  char flag; /* status of _current_ ep->value: PUSH or COPY ? */
  long valence; /* valence of entree* associated to 'value', to be restored
                    * by pop_val */
} var_cell;
#define INITIAL NULL

/* Push x on value stack associated to ep. */
static void
new_val_cell(entree *ep, GEN x, char flag)
{
  var_cell *v = (var_cell*) pari_malloc(sizeof(var_cell));
  v->value  = (GEN)ep->value;
  v->prev   = (var_cell*) ep->pvalue;
  v->flag   = flag;
  v->valence= ep->valence;

  /* beware: f(p) = Nv = 0
   *         Nv = p; f(Nv) --> this call would destroy p [ isclone ] */
  ep->value = (flag == COPY_VAL)? gclone(x):
                                  (x && isclone(x))? gcopy(x): x;
  /* Do this last. In case the clone is <C-C>'ed before completion ! */
  ep->pvalue= (char*)v;
  ep->valence=EpVAR;
}

/* kill ep->value and replace by preceding one, poped from value stack */
static void
pop_val(entree *ep)
{
  var_cell *v = (var_cell*) ep->pvalue;

  if (v == INITIAL) return;
  if (v->flag == COPY_VAL) gunclone_deep((GEN)ep->value);
  ep->value  = v->value;
  ep->pvalue = (char*) v->prev;
  ep->valence=v->valence;
  pari_free((void*)v);
}

void
freeep(entree *ep)
{
  if (foreignFuncFree && ep->code && (*ep->code == 'x'))
    (*foreignFuncFree)(ep); /* function created by foreign interpreter */

  if (EpSTATIC(ep)) return; /* gp function loaded at init time */
  if (ep->help) {pari_free((void*)ep->help); ep->help=NULL;}
  if (ep->code) {pari_free((void*)ep->code); ep->code=NULL;}
  switch(EpVALENCE(ep))
  {
    case EpVAR:
      while (ep->pvalue!=INITIAL) pop_val(ep);
      break;
    case EpALIAS:
      killblock((GEN)ep->value); ep->value=NULL; break;
  }
}

INLINE void
pushvalue(entree *ep, GEN x) {
  new_val_cell(ep, x, COPY_VAL);
}

INLINE void
zerovalue (entree *ep)
{
  var_cell *v = (var_cell*) pari_malloc(sizeof(var_cell));
  v->value  = (GEN)ep->value;
  v->prev   = (var_cell*) ep->pvalue;
  v->flag   = PUSH_VAL;
  v->valence= ep->valence;
  ep->value = gen_0;
  ep->pvalue= (char*)v;
  ep->valence=EpVAR;
}


/* as above IF ep->value was PUSHed, or was created after block number 'loc'
   return 0 if not deleted, 1 otherwise [for recover()] */
int
pop_val_if_newer(entree *ep, long loc)
{
  var_cell *v = (var_cell*) ep->pvalue;

  if (v == INITIAL) return 0;
  if (v->flag == COPY_VAL && !pop_entree_block(ep, loc)) return 0;
  ep->value = v->value;
  ep->pvalue= (char*) v->prev;
  ep->valence=v->valence;
  pari_free((void*)v); return 1;
}

/* set new value of ep directly to val (COPY), do not save last value unless
 * it's INITIAL. */
void
changevalue(entree *ep, GEN x)
{
  var_cell *v = (var_cell*) ep->pvalue;
  BLOCK_SIGINT_START
  if (v == INITIAL) new_val_cell(ep, x, COPY_VAL);
  else
  {
    x = gclone(x); /* beware: gunclone_deep may destroy old x */
    if (v->flag == COPY_VAL) gunclone_deep((GEN)ep->value); else v->flag = COPY_VAL;
    ep->value = (void*)x;
  }
  BLOCK_SIGINT_END
}

INLINE GEN
copyvalue(entree *ep)
{
  var_cell *v = (var_cell*) ep->pvalue;
  if (v && v->flag != COPY_VAL)
  {
    ep->value = (void*) gclone((GEN)ep->value);
    v->flag = COPY_VAL;
  }
  return (GEN) ep->value;
}

INLINE void
err_var() { pari_err(talker, "variable name expected"); }

INLINE void
checkvalue(entree *ep)
{
  if (ep->valence==EpNEW)
  {
    pari_var_create(ep);
    ep->valence = EpVAR;
    ep->value = initial_value(ep);
  }
  else if (ep->valence!=EpVAR)
    err_var();
}

/* make GP variables safe for avma = top */
static void
lvar_make_safe(void)
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

static void
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
  long vn;
  long sp;
} gp_pointer;


/* assign res at *pt in "simple array object" p and return it, or a copy.*/
static void
change_compo(matcomp *c, GEN res)
{
  GEN p = c->parent, *pt = c->ptcell;
  long i, t;

  if (typ(p) == t_VECSMALL)
  {
    if (typ(res) != t_INT || is_bigint(res))
      pari_err(talker,"not a suitable VECSMALL component");
    *pt = (GEN)itos(res); return;
  }
  t = typ(res);
  if (c->full_row)
  {
    if (t != t_VEC || lg(res) != lg(p))
      pari_err(talker,"incorrect type or length in matrix assignment");
    for (i=1; i<lg(p); i++)
    {
      GEN p1 = gcoeff(p,c->full_row,i); if (isclone(p1)) gunclone_deep(p1);
      gcoeff(p,c->full_row,i) = gclone(gel(res,i));
    }
    return;
  }
  if (c->full_col)
    if (t != t_COL || lg(res) != lg(*pt))
      pari_err(talker,"incorrect type or length in matrix assignment");

  res = gclone(res);
  gunclone_deep(*pt);
  *pt = res;
}

/***************************************************************************
 **                                                                       **
 **                           Byte-code evaluator                         **
 **                                                                       **
 ***************************************************************************/

struct var_lex
{
  long flag;
  GEN value;
};

struct trace
{
  long *pc;
  GEN closure;
};

static THREAD long sp, rp;
static THREAD long *st;
static THREAD gp_pointer *ptrs;
static THREAD entree **lvars;
static THREAD struct var_lex *var;
static THREAD struct trace *trace;
static THREAD pari_stack s_st, s_ptrs, s_var, s_lvars, s_trace;

static void
changelex(long vn, GEN x)
{
  struct var_lex *v=var+s_var.n+vn;
  x = gclone(x); /* beware: gunclone_deep may destroy old x */
  if (v->flag == COPY_VAL) gunclone_deep(v->value); else v->flag = COPY_VAL;
  v->value = x;
}

INLINE GEN
copylex(long vn)
{
  struct var_lex *v = var+s_var.n+vn;
  if (v->flag!=COPY_VAL)
  {
    v->flag  = COPY_VAL;
    v->value = gclone(v->value);
  }
  return v->value;
}

INLINE void
pushlex(long vn, GEN x)
{
  struct var_lex *v=var+s_var.n+vn;
  v->flag  = PUSH_VAL;
  v->value = x;
}

INLINE void
freelex(long vn)
{
  struct var_lex *v=var+s_var.n+vn;
  if (v->flag == COPY_VAL) gunclone_deep(v->value);
}

INLINE void
restore_vars(long nbmvar, long nblvar)
{
  long j;
  for(j=1;j<=nbmvar;j++)
    freelex(-j);
  s_var.n-=nbmvar;
  for(j=1;j<=nblvar;j++)
    pop_val(lvars[s_lvars.n-j]);
  s_lvars.n-=nblvar;
}

INLINE void
restore_trace(long nbtrace)
{
  long j;
  for(j=1;j<=nbtrace;j++)
  {
    GEN C = trace[s_trace.n-j].closure;
    if (isclone(C)) gunclone(C);
  }
  s_trace.n-=nbtrace;
}

INLINE void
trace_push(long *pc, GEN C)
{
  long tr;
  BLOCK_SIGINT_START
  tr = stack_new(&s_trace);
  trace[tr].pc = pc;
  trace[tr].closure = C;
  BLOCK_SIGINT_END
}

void
push_lex(GEN a, GEN C)
{
  long vn=stack_new(&s_var);
  struct var_lex *v=var+vn;
  v->flag  = PUSH_VAL;
  v->value = a;
  if (C) trace_push(NULL, C);
}

GEN
get_lex(long vn)
{
  struct var_lex *v=var+s_var.n+vn;
  return v->value;
}

void
set_lex(long vn, GEN x)
{
  struct var_lex *v=var+s_var.n+vn;
  if (v->flag == COPY_VAL) { gunclone_deep(v->value); v->flag = PUSH_VAL; }
  v->value = x;
}

void
pop_lex(long n)
{
  long j;
  for(j=1; j<=n; j++)
    freelex(-j);
  s_var.n-=n;
  s_trace.n--;
}

void
pari_init_evaluator(void)
{
  sp=0;
  stack_init(&s_st,sizeof(*st),(void**)&st);
  stack_alloc(&s_st,32);
  s_st.n=s_st.alloc;
  rp=0;
  stack_init(&s_ptrs,sizeof(*ptrs),(void**)&ptrs);
  stack_alloc(&s_ptrs,16);
  s_ptrs.n=s_ptrs.alloc;
  stack_init(&s_var,sizeof(*var),(void**)&var);
  stack_init(&s_lvars,sizeof(*lvars),(void**)&lvars);
  stack_init(&s_trace,sizeof(*trace),(void**)&trace);
  br_res = NULL;
}
void
pari_close_evaluator(void)
{
  stack_delete(&s_st);
  stack_delete(&s_ptrs);
  stack_delete(&s_var);
  stack_delete(&s_lvars);
  stack_delete(&s_trace);
}

static gp_pointer *
new_ptr(void)
{
  if (rp==s_ptrs.n-1)
  {
    long i;
    gp_pointer *old = ptrs;
    (void)stack_new(&s_ptrs);
    if (old != ptrs)
      for(i=0; i<rp; i++)
      {
        gp_pointer *g = &ptrs[i];
        if(g->sp >= 0) gel(st,g->sp) = (GEN) &(g->x);
      }
  }
  return &ptrs[rp++];
}

INLINE GEN
copyupto(GEN z, GEN t)
{
  if (is_universal_constant(z) || (z>(GEN)bot && z<=t))
    return z;
  else
    return gcopy(z);
}

static void closure_eval(GEN C);

INLINE GEN
closure_return(GEN C)
{
  pari_sp ltop=avma;
  closure_eval(C);
  if (br_status)
  {
    GEN z;
    avma=ltop;
    z=br_res?gcopy(br_res):gnil;
    reset_break();
    return z;
  }
  return gerepileupto(ltop,gel(st,--sp));
}

/* for the break_loop debugger. Not memory clean */
GEN
closure_evalbrk(GEN C, long *status)
{
  closure_eval(C);
  *status = br_status;
  if (br_status)
  {
    GEN z = br_res? gcopy(br_res): gnil;
    reset_break();
    return z;
  }
  return gel(st,--sp);
}

INLINE long
closure_varn(GEN x)
{
  if (!x) return -1;
  if (!gcmpX(x)) err_var();
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
    st[sp++]=gtos(z);
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
    err_var();
  default:
    pari_err(bugparier,"closure_castlong, type unknown");
  }
}

const char *
closure_func_err(void)
{
  long fun=s_trace.n-1, pc;
  const char *code;
  GEN C, oper;
  if (fun < 0 || !trace[fun].pc) return NULL;
  pc = *trace[fun].pc; C  = trace[fun].closure;
  code = GSTR(gel(C,2))-1; oper = gel(C,3);
  if (code[pc]==OCcallgen || code[pc]==OCcallgen2 ||
      code[pc]==OCcallint || code[pc]==OCcalllong || code[pc]==OCcallvoid)
    return ((entree*)oper[pc])->name;
  return NULL;
}

/* return the next label for the call chain debugger closure_err(),
 * incorporating the name of the user of member function. Return NULL for an
 * anonymous (inline) closure. */
static char *
get_next_label(const char *s, int member, char **next_fun)
{
  const char *v, *t = s+1;
  char *u, *next_label;

  if (!is_keyword_char(*s)) return NULL;
  while (is_keyword_char(*t)) t++;
  /* e.g. (x->1/x)(0) instead of (x)->1/x */
  if (t[0] == '-' && t[1] == '>') return NULL;
  next_label = (char*)pari_malloc(t - s + 32);
  sprintf(next_label, "in %sfunction ", member? "member ": "");
  u = *next_fun = next_label + strlen(next_label);
  v = s;
  while (v < t) *u++ = *v++;
  *u++ = 0; return next_label;
}

void
closure_err(void)
{
  GEN base;
  const long lastfun = s_trace.n - 1;
  char *next_label, *next_fun;
  long i, fun = lastfun;

  if (fun < 0) return; /*e.g. when called by gp_main_loop's simplify */
  while (lg(trace[fun].closure)==6) fun--;
  for (i=fun; i<=lastfun; i++)
  {
    long *pc=trace[i].pc;
    closure_context(trace[i].closure, pc?*pc:-1);
  }

  i = maxss(0, lastfun - 19);
  if (i > 0) while (lg(trace[i].closure)==6) i--;
  base = gel(trace[i].closure,6); /* gcc -Wall*/
  next_label = pari_strdup(i == 0? "at top-level": "[...] at");
  next_fun = next_label;
  for (; i <= lastfun; i++)
  {
    GEN C = trace[i].closure;
    if (lg(C) >= 7) base=gel(C,6);
    if ((i==lastfun || lg(trace[i+1].closure)>=7) && trace[i].pc)
    {
      /* After a SIGINT, pc can be slightly off: ensure 0 <= pc < lg() */
      long pc = minss(*trace[i].pc, lg(mael(C,5,1))-1);
      long offset = pc? mael3(C,5,1,pc): 0;
      int member;
      const char *s, *sbase;
      if (typ(base)!=t_VEC) sbase = GSTR(base);
      else if (offset>=0)   sbase = GSTR(gel(base,2));
      else { sbase = GSTR(gel(base,1)); offset += strlen(sbase); }
      s = sbase + offset;
      member = offset>0 && (s[-1] == '.');
      /* avoid "in function foo: foo" */
      if (!next_fun || strcmp(next_fun, s)) {
        print_errcontext(next_label, s, sbase);
        pari_putc('\n');
      }
      pari_free(next_label);
      if (i == lastfun) break;

      next_label = get_next_label(s, member, &next_fun);
      if (!next_label) {
        next_label = pari_strdup("in anonymous function");
        next_fun = NULL;
      }
    }
  }
}

INLINE void
st_alloc(long n)
{
  if (sp+n>s_st.n)
  {
    stack_alloc(&s_st,n+16);
    s_st.n=s_st.alloc;
    if (DEBUGMEM>=2) pari_warn(warner,"doubling evaluator stack");
  }
}

static void
closure_eval(GEN C)
{
  const char *code=GSTR(gel(C,2))-1;
  GEN oper=gel(C,3);
  GEN data=gel(C,4);
  long loper=lg(oper);
  long saved_sp=sp-C[1];
  long saved_rp=rp;
  long j, nbmvar=0, nblvar=0;
  long pc = 0; /* pc need to be defined after a ^C */
  if (isclone(C)) ++bl_refc(C);
  trace_push(&pc, C);
  if (lg(C)==8)
  {
    GEN z=gel(C,7);
    long l=lg(z)-1;
    stack_alloc(&s_var,l);
    s_var.n+=l;
    nbmvar+=l;
    for(j=1;j<=l;j++)
    {
      var[s_var.n-j].flag=PUSH_VAL;
      var[s_var.n-j].value=gel(z,j);
    }
  }

  for(pc=1;pc<loper;pc++)
  {
    op_code opcode=(op_code) code[pc];
    long operand=oper[pc];
    if (sp<0) pari_err(bugparier,"closure_eval, stack underflow");
    st_alloc(16);
    CHECK_CTRLC
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
      {
        entree *ep = (entree *)operand;
        pari_var_create(ep);
        gel(st,sp++)=(GEN)initial_value(ep);
        break;
      }
    case OCpushdyn:
      {
        entree *ep = (entree *)operand;
        checkvalue(ep);
        gel(st,sp++)=(GEN)ep->value;
        break;
      }
    case OCpushlex:
      gel(st,sp++)=var[s_var.n+operand].value;
      break;
    case OCsimpleptrdyn:
      {
        gp_pointer *g = new_ptr();
        g->vn=0;
        g->ep = (entree*) operand;
        checkvalue(g->ep);
        g->x = (GEN) g->ep->value;
        g->sp = sp;
        gel(st,sp++) = (GEN)&(g->x);
        break;
      }
    case OCsimpleptrlex:
      {
        gp_pointer *g = new_ptr();
        g->vn=operand;
        g->ep=(entree *)0x1L;
        g->x = (GEN) var[s_var.n+operand].value;
        g->sp = sp;
        gel(st,sp++) = (GEN)&(g->x);
        break;
      }
    case OCnewptrdyn:
      {
        entree *ep = (entree *)operand;
        gp_pointer *g = new_ptr();
        matcomp *C;
        checkvalue(ep);
        g->sp = -1;
        g->x = copyvalue(ep);
        g->vn=0;
        g->ep=NULL;
        C=&g->c;
        C->full_col = C->full_row = 0;
        C->parent   = (GEN)    g->x;
        C->ptcell   = (GEN *) &g->x;
        break;
      }
    case OCnewptrlex:
      {
        gp_pointer *g = new_ptr();
        matcomp *C;
        g->sp = -1;
        g->x = copylex(operand);
        g->vn=0;
        g->ep=NULL;
        C=&g->c;
        C->full_col = C->full_row = 0;
        C->parent   = (GEN)     g->x;
        C->ptcell   = (GEN *) &(g->x);
        break;
      }
    case OCpushptr:
      {
        gp_pointer *g = &ptrs[rp-1];
        g->sp = sp;
        gel(st,sp++) = (GEN)&(g->x);
      }
      break;
    case OCendptr:
      for(j=0;j<operand;j++)
      {
        gp_pointer *g = &ptrs[--rp];
        if (g->ep)
        {
          if (g->vn)
            changelex(g->vn, g->x);
          else
            changevalue(g->ep, g->x);
        }
        else change_compo(&(g->c), g->x);
      }
      break;
    case OCstoredyn:
      {
        entree *ep = (entree *)operand;
        checkvalue(ep);
        changevalue(ep, gel(st,--sp));
        break;
      }
    case OCstorelex:
      changelex(operand,gel(st,--sp));
      break;
    case OCstackgen:
      {
        GEN z = gerepileupto(st[sp-2],gel(st,sp-1));
        gmael(st,sp-3,operand) = copyupto(z,gel(st,sp-2));
        st[sp-2] = avma;
        sp--;
        break;
      }
    case OCprecreal:
      st[sp++]=precreal;
      break;
    case OCprecdl:
      st[sp++]=precdl;
      break;
    case OCavma:
      st[sp++]=avma;
      break;
    case OCcowvardyn:
      {
        entree *ep = (entree *)operand;
        checkvalue(ep);
        (void)copyvalue(ep);
        break;
      }
    case OCcowvarlex:
      (void)copylex(operand);
      break;
    case OCstoi:
      gel(st,sp-1)=stoi(st[sp-1]);
      break;
    case OCitos:
      st[sp+operand]=gtos(gel(st,sp+operand));
      break;
    case OCtostr:
      {
        GEN z=gel(st,sp+operand);
        if (typ(z)!=t_STR)
          z = GENtoGENstr(z);
        st[sp+operand] = (long) GSTR(z);
        break;
      }
    case OCvarn:
      st[sp+operand] = closure_varn(gel(st,sp+operand));
      break;
    case OCcopy:
      gel(st,sp-1) = gcopy(gel(st,sp-1));
      break;
    case OCgerepile:
      sp--;
      if (st[sp-1]-avma>1000000)
      {
        if (DEBUGMEM>=2)
          pari_warn(warnmem,"eval: recovering %ld bytes",st[sp-1]-avma);
        gel(st,sp-1) = gerepileupto(st[sp-1], gel(st,sp));
      }
      else
        gel(st,sp-1) = gel(st,sp);
      break;
    case OCcopyifclone:
      if (isclone(gel(st,sp-1)))
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
          {
            long lx;
            p = list_data(p); lx = p? lg(p): 1;
            check_array_index(c, lx);
            closure_castgen(gel(p,c),operand);
            break;
          }
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
        long lx;
        gp_pointer *g = &ptrs[rp-1];
        matcomp *C=&g->c;
        GEN p = g->x;
        sp--;
        switch(typ(p))
        {
        case t_VEC: case t_COL:
          check_array_index(c, lg(p));
          C->ptcell = (GEN *) p+c;
          g->x = *(C->ptcell);
          break;
        case t_VECSMALL:
          check_array_index(c, lg(p));
          C->ptcell = (GEN *) p+c;
          g->x = stoi(p[c]);
          break;
        case t_LIST:
          p = list_data(p); lx = p? lg(p): 1;
          check_array_index(c,lx);
          C->ptcell = (GEN *) p+c;
          g->x = *(C->ptcell);
          break;
        default:
          pari_err(talker,"_[_]: not a vector");
        }
        C->parent   = p;
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
        long c=st[sp-2];
        long d=st[sp-1];
        gp_pointer *g = &ptrs[rp-1];
        matcomp *C=&g->c;
        GEN p = g->x;
        sp-=2;
        if (typ(p)!=t_MAT)
          pari_err(talker,"_[_,_]: not a matrix");
        check_array_index(d, lg(p));
        check_array_index(c, lg(p[d]));
        C->ptcell = (GEN *) gel(p,d)+c;
        C->parent   = p;
        g->x = *(C->ptcell);
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
        GEN p = g->x;
        sp--;
        if (typ(p)!=t_MAT)
          pari_err(talker,"_[,_]: not a matrix");
        check_array_index(c, lg(p));
        C->ptcell = (GEN *) p+c;
        C->full_col = c;
        C->parent   = p;
        g->x = *(C->ptcell);
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
        GEN p = g->x, p2;
        sp--;
        if (typ(p)!=t_MAT)
          pari_err(talker,"_[_,]: not a matrix");
        if (lg(p)==1) pari_err(talker,"a 0x0 matrix has no elements");
        check_array_index(r,lg(p[1]));
        p2 = rowcopy(p,r);
        C->full_row = r; /* record row number */
        C->ptcell = &p2;
        C->parent   = p;
        g->x = p2;
        break;
      }
    case OCdefaultarg:
      if (var[s_var.n+operand].flag==DEFAULT_VAL)
      {
        GEN z = closure_evalnobrk(gel(st,sp-1));
        pushlex(operand,z);
      }
      sp--;
      break;
    case OClocalvar:
      {
        entree *ep = (entree *)operand;
        long n = stack_new(&s_lvars);
        lvars[n] = ep;
        nblvar++;
        pushvalue(ep,gel(st,--sp));
        break;
      }
    case OClocalvar0:
      {
        entree *ep = (entree *)operand;
        long n = stack_new(&s_lvars);
        lvars[n] = ep;
        nblvar++;
        zerovalue(ep);
        break;
      }

#define EVAL_f(f) \
  switch (ep->arity) \
  { \
    case 0: f(); break; \
    case 1: sp--; f(st[sp]); break; \
    case 2: sp-=2; f(st[sp],st[sp+1]); break; \
    case 3: sp-=3; f(st[sp],st[sp+1],st[sp+2]); break; \
    case 4: sp-=4; f(st[sp],st[sp+1],st[sp+2],st[sp+3]); break; \
    case 5: sp-=5; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4]); break; \
    case 6: sp-=6; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5]); break; \
    case 7: sp-=7; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6]); break; \
    case 8: sp-=8; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7]); break; \
    case 9: sp-=9; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8]); break; \
    case 10: sp-=10; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8],st[sp+9]); break; \
    case 11: sp-=11; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8],st[sp+9],st[sp+10]); break; \
    case 12: sp-=12; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8],st[sp+9],st[sp+10],st[sp+11]); break; \
    case 13: sp-=13; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8],st[sp+9],st[sp+10],st[sp+11],st[sp+12]); break; \
    case 14: sp-=14; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8],st[sp+9],st[sp+10],st[sp+11],st[sp+12],st[sp+13]); break; \
    case 15: sp-=15; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8],st[sp+9],st[sp+10],st[sp+11],st[sp+12],st[sp+13],st[sp+14]); break; \
    case 16: sp-=16; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8],st[sp+9],st[sp+10],st[sp+11],st[sp+12],st[sp+13],st[sp+14],st[sp+15]); break; \
    case 17: sp-=17; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8],st[sp+9],st[sp+10],st[sp+11],st[sp+12],st[sp+13],st[sp+14],st[sp+15],st[sp+16]); break; \
    case 18: sp-=18; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8],st[sp+9],st[sp+10],st[sp+11],st[sp+12],st[sp+13],st[sp+14],st[sp+15],st[sp+16],st[sp+17]); break; \
    case 19: sp-=19; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8],st[sp+9],st[sp+10],st[sp+11],st[sp+12],st[sp+13],st[sp+14],st[sp+15],st[sp+16],st[sp+17],st[sp+18]); break; \
    case 20: sp-=20; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8],st[sp+9],st[sp+10],st[sp+11],st[sp+12],st[sp+13],st[sp+14],st[sp+15],st[sp+16],st[sp+17],st[sp+18],st[sp+19]); break; \
    default: \
      pari_err(impl,"functions with more than 20 parameters");\
      goto endeval; /*not reached*/ \
  }

    case OCcallgen:
      {
        entree *ep = (entree *)operand;
        GEN res;
        /* Macro Madness : evaluate function ep->value on arguments
         * st[sp-ep->arity .. sp]. Set res = result. */
        EVAL_f(res = ((GEN (*)(ANYARG))ep->value));
        if (br_status) goto endeval;
        gel(st,sp++)=res;
        break;
      }
    case OCcallgen2: /*same for ep->arity = 2. Is this optimization worth it ?*/
      {
        entree *ep = (entree *)operand;
        GEN res;
        sp-=2;
        res = ((GEN (*)(GEN,GEN))ep->value)(gel(st,sp),gel(st,sp+1));
        if (br_status) goto endeval;
        gel(st,sp++)=res;
        break;
      }
    case OCcalllong:
      {
        entree *ep = (entree *)operand;
        long res;
        EVAL_f(res = ((long (*)(ANYARG))ep->value));
        if (br_status) goto endeval;
        st[sp++] = res;
        break;
      }
    case OCcallint:
      {
        entree *ep = (entree *)operand;
        long res;
        EVAL_f(res = ((int (*)(ANYARG))ep->value));
        if (br_status) goto endeval;
        st[sp++] = res;
        break;
      }
    case OCcallvoid:
      {
        entree *ep = (entree *)operand;
        EVAL_f(((void (*)(ANYARG))ep->value));
        if (br_status) goto endeval;
        break;
      }
#undef EVAL_f

    case OCcalluser:
      {
        long n=operand;
        GEN fun = gel(st,sp-1-n);
        long arity;
        GEN z;
        if (typ(fun)!=t_CLOSURE) pari_err(notfuncer, fun);
        arity=fun[1];
        if (n>arity)
          pari_err(talker,"too many parameters in user-defined function call");
        for (j=n+1;j<=arity;j++)
          gel(st,sp++)=0;
#ifdef STACK_CHECK
        if (PARI_stack_limit && (void*) &z <= PARI_stack_limit)
          pari_err(talker, "deep recursion");
#endif
        z = closure_return(fun);
        if (br_status) goto endeval;
        gel(st, sp-1) = z;
        break;
      }
    case OCnewframe:
      stack_alloc(&s_var,operand);
      s_var.n+=operand;
      nbmvar+=operand;
      for(j=1;j<=operand;j++)
      {
        var[s_var.n-j].flag=PUSH_VAL;
        var[s_var.n-j].value=gen_0;
      }
      break;
    case OCsaveframe:
      {
        GEN cl = (operand?gcopy:shallowcopy)(gel(st,sp-1));
        long l = lg(gel(cl,7));
        GEN  v = cgetg(l, t_VEC);
        for(j=1; j<l; j++)
        {
          GEN val = var[s_var.n-j].value;
          gel(v,j) = operand?gcopy(val):val;
        }
        gel(cl,7) = v;
        gel(st,sp-1) = cl;
      }
      break;
    case OCgetargs:
      stack_alloc(&s_var,operand);
      s_var.n+=operand;
      nbmvar+=operand;
      sp-=operand;
      for (j=0;j<operand;j++)
      {
        if (gel(st,sp+j))
          pushlex(j-operand,gel(st,sp+j));
        else
        {
          var[s_var.n+j-operand].flag=DEFAULT_VAL;
          var[s_var.n+j-operand].value=gen_0;
        }
      }
      break;
    case OCcheckargs:
      for (j=sp-1;operand;operand>>=1UL,j--)
        if ((operand&1L) && gel(st,j)==NULL)
          pari_err(talker,"missing mandatory argument");
      break;
    case OCcheckargs0:
      for (j=sp-1;operand;operand>>=1UL,j--)
        if ((operand&1L) && gel(st,j))
          pari_err(talker,"argument type not implemented");
      break;
    case OCdefaultitos:
      sp--;
      if (st[sp+operand])
        st[sp+operand]=gtos(gel(st,sp+operand));
      else
        st[sp+operand]=st[sp];
      break;
    case OCvec:
      gel(st,sp++)=cgetg(operand,t_VEC);
      st[sp++]=avma;
      break;
    case OCcol:
      gel(st,sp++)=cgetg(operand,t_COL);
      st[sp++]=avma;
      break;
    case OCmat:
      {
        GEN z;
        long l=st[sp-1];
        z=cgetg(operand,t_MAT);
        for(j=1;j<operand;j++)
          gel(z,j) = cgetg(l,t_COL);
        gel(st,sp-1) = z;
        st[sp++]=avma;
      }
      break;
    case OCpop:
      sp-=operand;
      break;
    }
  }
  if (0)
  {
endeval:
    sp = saved_sp;
    rp = saved_rp;
  }
  s_trace.n--;
  restore_vars(nbmvar, nblvar);
  if (isclone(C)) gunclone(C);
}

GEN
closure_evalgen(GEN C)
{
  pari_sp ltop=avma;
  closure_eval(C);
  if (br_status) { avma=ltop; return NULL; }
  return gerepileupto(ltop,gel(st,--sp));
}

void
evalstate_save(struct pari_evalstate *state)
{
  state->avma = avma;
  state->sp   = sp;
  state->rp   = rp;
  state->var  = s_var.n;
  state->lvars= s_lvars.n;
  state->trace= s_trace.n;
  compilestate_save(&state->comp);
}

void
evalstate_restore(struct pari_evalstate *state)
{
  avma = state->avma;
  sp = state->sp;
  rp = state->rp;
  restore_vars(s_var.n-state->var,s_lvars.n-state->lvars);
  restore_trace(s_trace.n-state->trace);
  reset_break();
  compilestate_restore(&state->comp);
}

void
evalstate_reset(void)
{
  sp = 0;
  rp = 0;
  restore_vars(s_var.n, s_lvars.n);
  s_trace.n = 0;
  reset_break();
  compilestate_reset();
  avma = top;
}

void
evalstate_clone(void)
{
  long i;
  for (i = 1; i<=s_var.n; i++) copylex(-i);
  lvar_make_safe();
  for (i = 0; i< s_trace.n; i++)
  {
    GEN C = trace[i].closure;
    if (isonstack(C)) trace[i].closure = gclone(C);
  }
}

GEN
closure_trapgen(GEN C, long numerr)
{
  VOLATILE GEN x;
  struct pari_evalstate state;
  evalstate_save(&state);
  CATCH(numerr) { x = (GEN)1L; }
  TRY { x = closure_evalgen(C); } ENDCATCH;
  if (x == (GEN)1L) evalstate_restore(&state);
  return x;
}

GEN
closure_evalnobrk(GEN C)
{
  pari_sp ltop=avma;
  closure_eval(C);
  if (br_status) pari_err(talker, "break not allowed here");
  return gerepileupto(ltop,gel(st,--sp));
}

void
closure_evalvoid(GEN C)
{
  pari_sp ltop=avma;
  closure_eval(C);
  avma=ltop;
}

GEN
closure_evalres(GEN C)
{
  return closure_return(C);
}

INLINE GEN
closure_returnupto(GEN C)
{
  pari_sp av=avma;
  return copyupto(closure_return(C),(GEN)av);
}

GEN
closure_callgen1(GEN C, GEN x)
{
  long i;
  gel(st,sp++)=x;
  for(i=2; i<=C[1]; i++) gel(st,sp++) = NULL;
  return closure_returnupto(C);
}

GEN
closure_callgen2(GEN C, GEN x, GEN y)
{
  long i;
  st_alloc(C[1]);
  gel(st,sp++)=x;
  gel(st,sp++)=y;
  for(i=3; i<=C[1]; i++) gel(st,sp++) = NULL;
  return closure_returnupto(C);
}

GEN
closure_callgenvec(GEN C, GEN args)
{
  long i, l = lg(args);
  st_alloc(C[1]);
  for (i = 1; i < l;   i++) gel(st,sp++) = gel(args,i);
  for(      ; i<=C[1]; i++) gel(st,sp++) = NULL;
  return closure_returnupto(C);
}

GEN
closure_callgenall(GEN C, long n, ...)
{
  va_list ap;
  long i;
  va_start(ap,n);
  st_alloc(C[1]);
  for (i = 1; i <=n;   i++) gel(st,sp++) = va_arg(ap, GEN);
  for(      ; i<=C[1]; i++) gel(st,sp++) = NULL;
  va_end(ap);
  return closure_returnupto(C);
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
  if (typ(C)!=t_CLOSURE)
    pari_err(typeer,"disassemble");
  code=GSTR(gel(C,2))-1;
  oper=gel(C,3);
  for(i=1;i<lg(oper);i++)
  {
    op_code opcode=(op_code) code[i];
    long operand=oper[i];
    pari_printf("%05ld\t",i);
    switch(opcode)
    {
    case OCpushlong:
      if (operand==(long)gnil)
        pari_printf("pushlong\tgnil\n");
      else if (operand==(long)gen_m2)
        pari_printf("pushlong\tgen_m2\n");
      else if (operand==(long)gen_m1)
        pari_printf("pushlong\tgen_m1\n");
      else if (operand==(long)gen_0)
        pari_printf("pushlong\tgen_0\n");
      else if (operand==(long)gen_1)
        pari_printf("pushlong\tgen_1\n");
      else if (operand==(long)gen_2)
        pari_printf("pushlong\tgen_2\n");
      else
        pari_printf("pushlong\t%ld\n",operand);
      break;
    case OCpushgen:
      pari_printf("pushgen\t\t%ld\n",operand);
      break;
    case OCpushreal:
      pari_printf("pushreal\t%ld\n",operand);
      break;
    case OCpushstoi:
      pari_printf("pushstoi\t%ld\n",operand);
      break;
    case OCpushvar:
      {
        entree *ep = (entree *)operand;
        pari_printf("pushvar\t%s\n",ep->name);
        break;
      }
    case OCpushdyn:
      {
        entree *ep = (entree *)operand;
        pari_printf("pushdyn\t\t%s\n",ep->name);
        break;
      }
    case OCpushlex:
      pari_printf("pushlex\t\t%ld\n",operand);
      break;
    case OCstoredyn:
      {
        entree *ep = (entree *)operand;
        pari_printf("storedyn\t%s\n",ep->name);
        break;
      }
    case OCstorelex:
      pari_printf("storelex\t%ld\n",operand);
      break;
    case OCsimpleptrdyn:
      {
        entree *ep = (entree *)operand;
        pari_printf("simpleptrdyn\t%s\n",ep->name);
        break;
      }
    case OCsimpleptrlex:
      pari_printf("simpleptrlex\t%ld\n",operand);
      break;
    case OCnewptrdyn:
      {
        entree *ep = (entree *)operand;
        pari_printf("newptrdyn\t%s\n",ep->name);
        break;
      }
    case OCnewptrlex:
      pari_printf("newptrlex\t%ld\n",operand);
      break;
    case OCpushptr:
      pari_printf("pushptr\n");
      break;
    case OCstackgen:
      pari_printf("stackgen\t%ld\n",operand);
      break;
    case OCendptr:
      pari_printf("endptr\t\t%ld\n",operand);
      break;
    case OCprecreal:
      pari_printf("precreal\n");
      break;
    case OCprecdl:
      pari_printf("precdl\n");
      break;
    case OCstoi:
      pari_printf("stoi\n");
      break;
    case OCitos:
      pari_printf("itos\t\t%ld\n",operand);
      break;
    case OCtostr:
      pari_printf("tostr\t\t%ld\n",operand);
      break;
    case OCvarn:
      pari_printf("varn\t\t%ld\n",operand);
      break;
    case OCcopy:
      pari_printf("copy\n");
      break;
    case OCcopyifclone:
      pari_printf("copyifclone\n");
      break;
    case OCcompo1:
      pari_printf("compo1\t\t%s\n",disassemble_cast(operand));
      break;
    case OCcompo1ptr:
      pari_printf("compo1ptr\n");
      break;
    case OCcompo2:
      pari_printf("compo2\t\t%s\n",disassemble_cast(operand));
      break;
    case OCcompo2ptr:
      pari_printf("compo2ptr\n");
      break;
    case OCcompoC:
      pari_printf("compoC\n");
      break;
    case OCcompoCptr:
      pari_printf("compoCptr\n");
      break;
    case OCcompoL:
      pari_printf("compoL\n");
      break;
    case OCcompoLptr:
      pari_printf("compoLptr\n");
      break;
    case OCcheckargs:
      pari_printf("checkargs\t0x%lx\n",operand);
      break;
    case OCcheckargs0:
      pari_printf("checkargs0\t0x%lx\n",operand);
      break;
    case OCdefaultitos:
      pari_printf("defaultitos\t%ld\n",operand);
      break;
    case OCgetargs:
      pari_printf("getargs\t\t%ld\n",operand);
      break;
    case OCdefaultarg:
      pari_printf("defaultarg\t%ld\n",operand);
      break;
    case OClocalvar:
      {
        entree *ep = (entree *)operand;
        pari_printf("localvar\t%s\n",ep->name);
        break;
      }
    case OClocalvar0:
      {
        entree *ep = (entree *)operand;
        pari_printf("localvar0\t%s\n",ep->name);
        break;
      }
    case OCcallgen:
      {
        entree *ep = (entree *)operand;
        pari_printf("callgen\t\t%s\n",ep->name);
        break;
      }
    case OCcallgen2:
      {
        entree *ep = (entree *)operand;
        pari_printf("callgen2\t%s\n",ep->name);
        break;
      }
    case OCcalllong:
      {
        entree *ep = (entree *)operand;
        pari_printf("calllong\t%s\n",ep->name);
        break;
      }
    case OCcallint:
      {
        entree *ep = (entree *)operand;
        pari_printf("callint\t\t%s\n",ep->name);
        break;
      }
    case OCcallvoid:
      {
        entree *ep = (entree *)operand;
        pari_printf("callvoid\t%s\n",ep->name);
        break;
      }
    case OCcalluser:
      pari_printf("calluser\t%ld\n",operand);
      break;
    case OCvec:
      pari_printf("vec\t\t%ld\n",operand);
      break;
    case OCcol:
      pari_printf("col\t\t%ld\n",operand);
      break;
    case OCmat:
      pari_printf("mat\t\t%ld\n",operand);
      break;
    case OCnewframe:
      pari_printf("newframe\t%ld\n",operand);
      break;
    case OCsaveframe:
      pari_printf("saveframe\t%ld\n", operand);
      break;
    case OCpop:
      pari_printf("pop\t\t%ld\n",operand);
      break;
    case OCavma:
      pari_printf("avma\n",operand);
      break;
    case OCgerepile:
      pari_printf("gerepile\n",operand);
      break;
    case OCcowvardyn:
      {
        entree *ep = (entree *)operand;
        pari_printf("cowvardyn\t%s\n",ep->name);
        break;
      }
    case OCcowvarlex:
      pari_printf("cowvarlex\t%ld\n",operand);
      break;
    }
  }
}
