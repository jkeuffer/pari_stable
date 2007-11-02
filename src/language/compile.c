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
#include "tree.h"
#include "opcode.h"

#define tree pari_tree

/***************************************************************************
 **                                                                       **
 **                           String constant expansion                   **
 **                                                                       **
 ***************************************************************************/

static GEN
strntoGENexp(const char *str, long len)
{
  GEN z = cgetg(1+nchar2nlong(len), t_STR);
  char *s=GSTR(z);
  const char *t=str+1;
  while (t<=str+len)
  {
    while (*t == '\\')
    {
      switch(*++t)
      {
        case 'e':  *s='\033'; break; /* escape */
        case 'n':  *s='\n'; break;
        case 't':  *s='\t'; break;
        default:   *s=*t; if (!*t) pari_err(talker,"unfinished string");
      }
      t++; s++;
    }
    if (*t == '"')
    {
      if (t[1] != '"') break;
      t += 2; continue;
    }
    *s++ = *t++;
  }
  *s++=0;
  return z;
}

/***************************************************************************
 **                                                                       **
 **                           Byte-code compiler                          **
 **                                                                       **
 ***************************************************************************/

typedef enum {Llocal, Lmy} Ltype;

struct vars_s
{
  Ltype type; /*Only Llocal and Lmy are allowed */
  entree *ep;
};

static THREAD gp2c_stack s_opcode, s_operand, s_data, s_lvar;
static THREAD char *opcode;
static THREAD long *operand;
static THREAD GEN *data;
static THREAD long offset=-1;
static THREAD struct vars_s *localvars;

void
pari_init_compiler(void)
{
  stack_init(&s_opcode,sizeof(*opcode),(void **)&opcode);
  stack_init(&s_operand,sizeof(*operand),(void **)&operand);
  stack_init(&s_data,sizeof(*data),(void **)&data);
  stack_init(&s_lvar,sizeof(*localvars),(void **)&localvars);
}

struct codepos
{
  long opcode, data, localvars;
  long offset;
};

static void
getcodepos(struct codepos *pos)
{
  pos->opcode=s_opcode.n;
  pos->data=s_data.n;
  pos->offset=offset;
  pos->localvars=s_lvar.n;
  offset=s_data.n-1;
}

void
compiler_reset(void)
{
  s_opcode.n=0;
  s_operand.n=0;
  s_data.n=0;
  s_lvar.n=0;
  offset=-1;
}

static GEN
getfunction(struct codepos *pos, long arity, long nbmvar, GEN text)
{
  long lop =s_opcode.n+1-pos->opcode;
  long ldat=s_data.n+1-pos->data;
  GEN cl=cgetg(nbmvar?7:(text?6:5),t_CLOSURE);
  char *s;
  long i;
  cl[1] = arity;
  gel(cl,2) = cgetg(nchar2nlong(lop)+1, t_STR);
  gel(cl,3) = cgetg(lop,  t_VECSMALL);
  gel(cl,4) = cgetg(ldat, t_VEC);
  if (text) gel(cl,5) = text;
  if (nbmvar) gel(cl,6) = zerovec(nbmvar);
  s=GSTR(gel(cl,2))-1;
  for(i=1;i<lop;i++)
  {
    s[i] = opcode[i+pos->opcode-1];
    mael(cl, 3, i) = operand[i+pos->opcode-1];
  }
  s[i]=0;
  s_opcode.n=pos->opcode;
  s_operand.n=pos->opcode;
  for(i=1;i<ldat;i++)
  {
    gmael(cl, 4, i) = gcopy(data[i+pos->data-1]);
    gunclone(data[i+pos->data-1]);
  }
  s_data.n=pos->data;
  s_lvar.n=pos->localvars;
  offset=pos->offset;
  return cl;
}

static GEN
getclosure(struct codepos *pos)
{
  return getfunction(pos,0,0,NULL);
}

static void
op_push(op_code o, long x)
{
  long n=stack_new(&s_opcode);
  long m=stack_new(&s_operand);
  opcode[n]=o;
  operand[m]=x;
}

static long
data_push(GEN x)
{
  long n=stack_new(&s_data);
  data[n] = gclone(x);
  return n-offset;
}

static void
var_push(entree *ep, Ltype type)
{
  long n=stack_new(&s_lvar);
  localvars[n].ep   = ep;
  localvars[n].type = type;
}

enum FLflag {FLnocopy=1, FLreturn=2};

static void compilenode(long n, int mode, long flag);

typedef enum {PPend,PPstd,PPdefault,PPdefaultmulti,PPstar,PPauto} PPproto;

static PPproto
parseproto(char const **q, char *c)
{
  char  const *p=*q;
  long i;
  switch(*p)
  {
  case 0:
  case '\n':
    return PPend;
  case 'D':
    switch(p[1])
    {
    case 0:
      pari_err(talker,"incomplete prototype");
    case 'G':
    case '&':
    case 'V':
    case 'I':
    case 'E':
    case 'n':
      *c=p[1];
      *q=p+2;
      return PPdefault;
    default:
      for(i=0;*p && i<2;p++) i+=*p==',';
      if (i<2)
        pari_err(talker,"incomplete prototype");
      *c=p[-2];
      *q=p;
      return PPdefaultmulti;
    }
    break;
  case 'p':
  case 'P':
  case 'f':
    *c=*p;
    *q=p+1;
    return PPauto;
  case '&':
    *c='*';
    *q=p+1;
    return PPstd;
  case 'V':
    if (p[1]=='=')
    {
      if (p[2]!='G')
        pari_err(impl,"prototype not supported");
      *c='=';
      p+=2;
    }
    else
      *c=*p;
    *q=p+1;
    return PPstd;
  case 's':
    if (p[1]=='*')
    {
      *c=*p++;
      *q=p+1;
      return PPstar;
    }
    /*fall through*/
  }
  *c=*p;
  *q=p+1;
  return PPstd;
}
/*supported types:
 * type: Gsmall, Ggen, Gvoid, Gvec
 * mode: Gsmall, Ggen, Gvar, Gvoid
 */
static void
compilecast(long n, int type, int mode)
{
  if (type==mode) return;
  switch (mode)
  {
  case Gsmall:
    if (type==Ggen)        op_push(OCitos,0);
    else if (type==Gvoid)  op_push(OCpushlong,0);
    else pari_err(talker2,"this should be a small integer",
             tree[n].str, get_origin());
    break;
  case Ggen:
    if (type==Gsmall)      op_push(OCstoi,0);
    else if (type==Gvoid)  op_push(OCpushlong,(long)gnil);
    break;
  case Gvoid:
    op_push(OCpop, 1);
    break;
  case Gvar:
    if (type==Ggen)        op_push(OCvarn,0);
    else pari_err(varer1, tree[n].str, get_origin());
     break;
  default:
    pari_err(bugparier,"compilecast, type unknown %ld",mode);
  }
}

static entree *
get_entree(long n)
{
  long x=tree[n].x;
  if (tree[x].x==CSTmember)
    return fetch_member(tree[x].str, tree[x].len);
  else
    return fetch_entry(tree[x].str, tree[x].len);
}

/* match any Fentry */
static entree *
getentry(long n)
{
  while (tree[n].f==Ftag)
    n=tree[n].x;
  if (tree[n].f!=Fentry)
    pari_err(talker2,"variable name expected",tree[n].str, get_origin());
  return get_entree(n);
}

/* match Fentry that are not actually EpSTATIC functions called without parens*/
static entree *
getvar(long n)
{
  entree *ep = getentry(n);
  if (EpSTATIC(do_alias(ep)))
    pari_err(talker2,"variable name expected",tree[n].str, get_origin());
  return ep;
}

static long
getmvar(entree *ep)
{
  long i;
  long vn=0;
  for(i=s_lvar.n-1;i>=0;i--)
  {
    if(localvars[i].type==Lmy)
      vn--;
    if(localvars[i].ep==ep)
      return localvars[i].type==Lmy?vn:0;
  }
  return 0;
}

static long
numbmvar(void)
{
  long i;
  long n=0;
  for(i=s_lvar.n-1;i>=0;i--)
    if(localvars[i].type==Lmy)
      n++;
  return n;
}

static entree *
getfunc(long n)
{
  return do_alias(get_entree(n));
}

INLINE int
is_func_named(long x, const char *s)
{
  if (tree[x].x!=CSTentry) return 0;
  if (strlen(s)!=tree[x].len) return 0;
  return !strncmp(tree[x].str, s, tree[x].len);
}

INLINE int
is_node_zero(long n)
{
  while (tree[n].f==Ftag)
    n=tree[n].x;
  return (tree[n].f==Fsmall && tree[n].x==0);
}

static GEN
listtogen(long n, long f)
{
  GEN z;
  long x,i,nb;
  if (n==-1 || tree[n].f==Fnoarg) return cgetg(1,t_VECSMALL);
  for(x=n, i=0; tree[x].f==f ;x=tree[x].x, i++);
  nb=i+1;
  z=cgetg(nb+1, t_VECSMALL);
  for (x=n; i>0; z[i+1]=tree[x].y, x=tree[x].x, i--);
  z[1]=x;
  return z;
}

static long
arg_is_safe(long a)
{
  if (a<0) return 1;
  switch (tree[a].f)
  {
  case FmatrixL: case FmatrixR:
  case Ftag:
    return arg_is_safe(tree[a].x);
  case Fconst: case Fsmall: case Fnoarg:
    return 1;
  case Ffacteurmat:
  case Fmatrix:
    return arg_is_safe(tree[a].x) && arg_is_safe(tree[a].y);
  case Fentry:
    {
      entree *ep=get_entree(a);
      long i;
      for (i=s_lvar.n-1; i>=0; i--)
        if (localvars[i].ep==ep)
          return 1;
      return 0;
    }
  default:
    return 0;
  }
}

static long
first_safe_arg(GEN arg)
{
  long lnc, l=lg(arg);
  for (lnc=l-1; lnc>0 && arg_is_safe(arg[lnc]); lnc--);
  return lnc;
}

static entree *
getlvalue(long n)
{
  while (tree[n].f==Ffacteurmat)
    n=tree[n].x;
  return getvar(n);
}

static void
compilelvalue(long n)
{
  if (tree[n].f==Fentry)
    return;
  else
  {
    long x=tree[n].x;
    long y=tree[n].y;
    long yx=tree[y].x;
    long yy=tree[y].y;
    long f=tree[y].f;
    if (tree[x].f==Ffacteurmat && f==Fmatrix && yy==-1 &&
        tree[tree[x].y].f==FmatrixL)
    {
      compilelvalue(tree[x].x);
      compilenode(tree[tree[x].y].x,Gsmall,0);
      compilenode(yx,Gsmall,0);
      op_push(OCcompo2ptr,0);
      return;
    }
    compilelvalue(x);
    compilenode(yx,Gsmall,0);
    if (f==Fmatrix && yy==-1)
      op_push(OCcompo1ptr,0);
    else
    {
      switch(f)
      {
      case Fmatrix:
        compilenode(yy,Gsmall,0);
        op_push(OCcompo2ptr,0);
        break;
      case FmatrixR:
        op_push(OCcompoCptr,0);
        break;
      case FmatrixL:
        op_push(OCcompoLptr,0);
        break;
      }
    }
  }
}

static void
compilefacteurmat(long n, int mode)
{
  long x=tree[n].x;
  long y=tree[n].y;
  long yx=tree[y].x;
  long yy=tree[y].y;
  long f=tree[y].f;
  compilenode(x,Ggen,FLnocopy);
  compilenode(yx,Gsmall,0);
  if (f==Fmatrix && yy==-1)
  {
    op_push(OCcompo1,mode);
    return;
  }
  switch(f)
  {
  case Fmatrix:
    compilenode(yy,Gsmall,0);
    op_push(OCcompo2,mode);
    return;
  case FmatrixR:
    op_push(OCcompoC,0);
    compilecast(n,Gvec,mode);
    return;
  case FmatrixL:
    op_push(OCcompoL,0);
    compilecast(n,Gvec,mode);
    return;
  default:
    pari_err(bugparier,"compilefacteurmat");
  }
}

static void
compilevec(long n, long mode, op_code op)
{
  pari_sp ltop=avma;
  long x=tree[n].x;
  long i;
  GEN arg=listtogen(x,Fmatrixelts);
  long l=lg(arg),lnc=first_safe_arg(arg);
  op_push(op,l);
  for (i=1;i<l;i++)
  {
    compilenode(arg[i],Ggen,i>=lnc?FLnocopy:0);
    op_push(OCstackgen,i);
  }
  avma=ltop;
  compilecast(n,Gvec,mode);
}

static void
compilemat(long n, long mode)
{
  pari_sp ltop=avma;
  long x=tree[n].x;
  long i,j;
  GEN line=listtogen(x,Fmatrixlines);
  long lglin = lg(line), lgcol=0;
  op_push(OCpushlong, lglin);
  if (lglin==1)
    op_push(OCmat,1);
  for(i=1;i<lglin;i++)
  {
    GEN col=listtogen(line[i],Fmatrixelts);
    long l=lg(col), k;
    if (i==1)
    {
      lgcol=l;
      op_push(OCmat,lgcol);
    }
    else if (l!=lgcol)
      pari_err(talker2,"matrix must be rectangular",
          tree[line[i]].str,get_origin());
    k=i;
    for(j=1;j<lgcol;j++)
    {
      k-=lglin;
      compilenode(col[j], Ggen,0);
      op_push(OCstackgen,k);
    }
  }
  avma=ltop;
  compilecast(n,Gvec,mode);
}


static GEN
cattovec(long n, long fnum)
{
  long x=n, y, i=0, nb;
  GEN stack;
  if (tree[n].f==Fnoarg) return cgetg(1,t_VECSMALL);
  while(1)
  {
    long xx=tree[x].x;
    long xy=tree[x].y;
    if (tree[x].f!=Ffunction || xx!=fnum) break;
    x=tree[xy].x;
    y=tree[xy].y;
    if (tree[y].f==Fnoarg)
      pari_err(talker2,"unexpected character: ",
               tree[y].str, get_origin());
    i++;
  }
  if (tree[x].f==Fnoarg)
    pari_err(talker2,"unexpected character: ",
             tree[x].str, get_origin());
  nb=i+1;
  stack=cgetg(nb+1,t_VECSMALL);
  for(x=n;i>0;i--)
  {
    long y=tree[x].y;
    x=tree[y].x;
    stack[i+1]=tree[y].y;
  }
  stack[1]=x;
  return stack;
}

static void
compilecall(long n, op_code op, int mode)
{
  pari_sp ltop=avma;
  long j;
  long y=tree[n].y;
  GEN arg=listtogen(y,Flistarg);
  long nb=lg(arg)-1;
  for (j=1;j<=nb;j++)
    if (tree[arg[j]].f!=Fnoarg)
      compilenode(arg[j], Ggen,0);
    else
      op_push(OCpushlong,0);
  op_push(op, nb);
  compilecast(n,Ggen,mode);
  avma=ltop;
  return;
}

static void
compileuserfunc(entree *ep, long n, int mode)
{
  long vn=getmvar(ep);
  if (vn)
    op_push(OCpushlex,vn);
  else
    op_push(OCpushdyn,(long)ep);
  compilecall(n, tree[n].f==Fderfunc ? OCderivuser:OCcalluser, mode);
}

/* return type for GP functions */
enum { RET_GEN, RET_INT, RET_LONG, RET_VOID };

static void
compilefunc(entree *ep, long n, int mode)
{
  pari_sp ltop=avma;
  long i,j;
  long x=tree[n].x;
  long y=tree[n].y;
  long ret;
  char const *p,*q;
  char c;
  const char *flags = NULL;
  PPproto mod;
  GEN arg=listtogen(y,Flistarg);
  long lnc=first_safe_arg(arg);
  long nbpointers=0;
  long nb=lg(arg)-1, lev=0;
  entree *ev[8];
  if (tree[n].f==Faffect)
  {
    nb=2; lnc=2; arg=mkvecsmall2(x,y);
  }
  else if (is_func_named(x,"if") && mode==Gvoid)
    ep=is_entry("_void_if");
  else if (is_func_named(x,"my"))
  {
    if (tree[n].f==Fderfunc)
      pari_err(talker2,"can't derive this",tree[n].str,get_origin());
    if (nb) op_push(OCnewframe,nb);
    for(i=1;i<=nb;i++)
      var_push(NULL,Lmy);
    for (i=1;i<=nb;i++)
    {
      long a=arg[i];
      if (tree[a].f==Faffect)
      {
        if (!is_node_zero(tree[a].y))
        {
          compilenode(tree[a].y,Ggen,0);
          op_push(OCstorelex,-nb+i-1);
        }
        a=tree[a].x;
      }
      localvars[s_lvar.n-nb+i-1].ep=getvar(a);
    }
    compilecast(n,Gvoid,mode);
    avma=ltop;
    return;
  }
  else if (is_func_named(x,"local"))
  {
    if (tree[n].f==Fderfunc)
      pari_err(talker2,"can't derive this",tree[n].str,get_origin());
    for (i=1;i<=nb;i++)
    {
      entree *en;
      long a=arg[i];
      op_code op=OClocalvar0;
      if (tree[a].f==Faffect)
      {
        if (!is_node_zero(tree[a].y))
        {
          compilenode(tree[a].y,Ggen,0);
          op=OClocalvar;
        }
        a=tree[a].x;
      }
      en=getvar(a);
      op_push(op,(long)en);
      var_push(en,Llocal);
    }
    compilecast(n,Gvoid,mode);
    avma=ltop;
    return;
  }
  /*We generate dummy code for global() for backward compatibility*/
  else if (is_func_named(x,"global"))
  {
    pari_warn(warner,"global(...) is deprecated");
    if (tree[n].f==Fderfunc)
      pari_err(talker2,"can't derive this",tree[n].str,get_origin());
    for (i=1;i<=nb;i++)
    {
      long a=arg[i];
      long en;
      if (tree[a].f==Faffect)
      {
        compilenode(tree[a].y,Ggen,0);
        a=tree[a].x;
        en=(long)getvar(a);
        op_push(OCstoredyn,en);
      }
      else
      {
        en=(long)getvar(a);
        op_push(OCpushdyn,en);
        op_push(OCpop,1);
      }
    }
    compilecast(n,Gvoid,mode);
    avma=ltop;
    return;
  }
  else if (is_func_named(x,"O") || (compatible==OLDALL && is_func_named(x,"o")))
  {
    long a;
    if (nb!=1) pari_err(talker2,"wrong number of arguments",
        tree[n].str+tree[n].len-1, get_origin());
    if (tree[n].f==Fderfunc)
      pari_err(talker2,"can't derive this",tree[n].str,get_origin());
    a = arg[1];
    if (tree[a].f!=Ffunction || tree[a].x!=OPpow)
    {
      compilenode(a,Ggen,FLnocopy);
      op_push(OCpushlong,1);
    }
    else
    {
      long y=tree[a].y;
      compilenode(tree[y].x,Ggen,0);
      compilenode(tree[y].y,Gsmall,0);
    }
    op_push(OCcallgen2,(long)ep);
    compilecast(n,Ggen,mode);
    avma=ltop;
    return;
  }
  else if (x==OPtrans && tree[y].f==Fvec)
  {
    avma=ltop;
    compilevec(y, mode, OCcol);
    return;
  }
  else if (x==OPcat)
    pari_err(talker2,"expected character: ',' or ')' instead of",
        tree[arg[1]].str+tree[arg[1]].len, get_origin());
  p=ep->code;
  if (!ep->value)
    pari_err(talker2,"unknown function",tree[n].str, get_origin());
  if (*p == 'v') { ret = RET_VOID; p++; }
  else if (*p == 'i') { ret = RET_INT;  p++; }
  else if (*p == 'l') { ret = RET_LONG; p++; }
  else ret = RET_GEN;
  if (tree[n].f==Fderfunc && (ret!=RET_GEN || *p!='G'))
    pari_err(talker2,"can't derive this",tree[n].str,get_origin());
  i=0; j=1;
  if (*p)
  {
    q=p;
    while((mod=parseproto(&p,&c))!=PPend)
    {
      if (j<=nb && tree[arg[j]].f!=Fnoarg
          && (mod==PPdefault || mod==PPdefaultmulti))
        mod=PPstd;
      switch(mod)
      {
      case PPstd:
        if (j>nb)
          pari_err(talker2,"too few arguments",
              tree[n].str+tree[n].len-1, get_origin());
        if (tree[arg[j]].f==Fnoarg && c!='I' && c!='E')
          pari_err(talker2,"missing mandatory argument",
              tree[arg[j]].str, get_origin());
        switch(c)
        {
        case 'G':
          compilenode(arg[j],Ggen,j>=lnc?FLnocopy:0);
          j++;
          break;
        case 'M':
          if (tree[arg[j]].f!=Fsmall)
          {
            if (!flags) flags = ep->code;
            flags = strchr(flags, '\n'); /* Skip to the following '\n' */
            if (!flags)
              pari_err(talker, "not enough flags in string function signature");
            flags++;
            if (tree[arg[j]].f==Fconst && tree[arg[j]].x==CSTstr)
            {
              GEN str=strntoGENexp(tree[arg[j]].str,tree[arg[j]].len);
              op_push(OCpushlong, eval_mnemonic(str, flags));
              j++;
            } else
            {
              compilenode(arg[j++],Ggen,0);
              op_push(OCpushlong,(long)flags);
              op_push(OCcallgen2,(long)is_entry("_eval_mnemonic"));
            }
            break;
          }
        case 'L': /*Fall through*/
          compilenode(arg[j++],Gsmall,0);
          break;
        case 'n':
          compilenode(arg[j++],Gvar,0);
          break;
        case '&': case '*':
          {
            long vn, a=arg[j++];
            entree *ep;
            if (c=='&')
            {
              if (tree[a].f!=Frefarg)
                pari_err(talker2,"expected character: '&'",
                    tree[a].str, get_origin());
              a=tree[a].x;
            }
            ep=getlvalue(a);
            vn=getmvar(ep);
            if (tree[a].f==Fentry)
            {
              if (vn)
                op_push(OCsimpleptrlex, vn);
              else
                op_push(OCsimpleptrdyn, (long) ep);
            }
            else
            {
              if (vn)
                op_push(OCnewptrlex, vn);
              else
                op_push(OCnewptrdyn, (long) ep);
              compilelvalue(a);
              op_push(OCpushptr, 0);
            }
            nbpointers++;
            break;
          }
        case 'I':
        case 'E':
          {
            struct codepos pos;
            long a=arg[j++];
            int type=c=='I'?Gvoid:Ggen;
            long flag=c=='I'?0:FLreturn;
            getcodepos(&pos);
            for(i=0;i<lev;i++)
            {
              if (!ev[i])
                pari_err(talker2,"missing variable name",
                    tree[a].str-1, get_origin());
              var_push(ev[i],Lmy);
            }
            if (tree[a].f==Fnoarg)
              compilecast(a,Gvoid,type);
            else
              compilenode(a,type,flag);
            op_push(OCpushgen, data_push(getclosure(&pos)));
            break;
          }
        case 'V':
          {
            ev[lev++] = getvar(arg[j++]);
            break;
          }
        case 'S':
          {
            entree *ep = getentry(arg[j++]);
            op_push(OCpushlong, (long)ep);
            break;
          }
        case '=':
          {
            long x=tree[arg[j]].x;
            long y=tree[arg[j]].y;
            if (tree[arg[j]].f!=Faffect)
              pari_err(talker2,"expected character: '=' instead of",
                  tree[arg[j]].str+tree[arg[j]].len, get_origin());
            ev[lev++] = getvar(x);
            compilenode(y,Ggen,0);
            i++; j++;
          }
          break;
        case 'r':
          {
            long a=arg[j++];
            if (tree[a].f==Fentry)
            {
              op_push(OCpushgen, data_push(strntoGENstr(tree[tree[a].x].str,tree[tree[a].x].len)));
              op_push(OCtostr, 1);
            }
            else
            {
              compilenode(a,Ggen,FLnocopy);
              op_push(OCtostr, 1);
            }
            break;
          }
        case 's':
          {
            GEN g = cattovec(arg[j++], OPcat);
            long l, nb = lg(g)-1;
            for(l=1; l<=nb; l++)
              compilenode(g[l], Ggen,0);
            op_push(OCtostr, nb);
            break;
          }
        default:
          pari_err(talker,"Unknown prototype code `%c' for `%*s'",c,
              tree[x].len, tree[x].str);
        }
        break;
      case PPauto:
        switch(c)
        {
        case 'p':
          op_push(OCprecreal,0);
          break;
        case 'P':
          op_push(OCprecdl,0);
          break;
        case 'f':
          {
            static long foo;
            op_push(OCpushlong,(long)&foo);
            break;
          }
        }
        break;
      case PPdefault:
        j++;
        switch(c)
        {
        case 'G':
        case '&':
        case 'r':
        case 'E':
        case 'I':
          op_push(OCpushlong,0);
          break;
        case 'n':
          op_push(OCpushlong,-1);
          break;
        case 'V':
          ev[lev++] = NULL;
          break;
        default:
          pari_err(talker,"Unknown prototype code `%c' for `%*s'",c,
              tree[x].len, tree[x].str);
        }
        break;
      case PPdefaultmulti:
        j++;
        switch(c)
        {
        case 'G':
          op_push(OCpushgen,data_push(strntoGENstr(q+1,p-4-q)));
          op_push(OCcallgen,(long)is_entry("eval"));
          break;
        case 'L':
        case 'M':
          op_push(OCpushlong,strtol(q+1,NULL,10));
          break;
        case 'r':
        case 's':
          if (q[1]=='"' && q[2]=='"')
            op_push(OCpushlong,(long)"");
          else
            pari_err(impl,"prototype not supported");
          break;
        default:
          pari_err(talker,"Unknown prototype code `%c' for `%*s'",c,
              tree[x].len, tree[x].str);
        }
        break;
      case PPstar:
        switch(c)
        {
        case 's':
          {
            long n=nb+1-j;
            long k,l,l1,m;
            GEN g=cgetg(n+1,t_VEC);
            for(l1=0,k=1;k<=n;k++)
            {
              gel(g,k)=cattovec(arg[j+k-1],OPcat);
              l1+=lg(g[k])-1;
            }
            op_push(OCvec, l1+1);
            for(m=1,k=1;k<=n;k++)
              for(l=1;l<lg(g[k]);l++,m++)
              {
                compilenode(mael(g,k,l),Ggen,0);
                op_push(OCstackgen,m);
              }
            j=nb+1;
            break;
          }
        default:
          pari_err(talker,"Unknown prototype code `%c*' for `%*s'",c,
              tree[x].len, tree[x].str);
        }
        break;
      default:
        pari_err(bugparier,"PPproto %d in gencallfunc",mod);
      }
      i++;
      q=p;
    }
  }
  if (j<=nb)
    pari_err(talker2,"too many arguments",tree[arg[j]].str,get_origin());
  switch (ret)
  {
  case RET_GEN:
    if (tree[n].f==Fderfunc)
      op_push(OCderivgen, (long) ep);
    else if (ep->arity==2)
      op_push(OCcallgen2, (long) ep);
    else
      op_push(OCcallgen, (long) ep);
    compilecast(n,Ggen,mode);
    break;
  case RET_INT:
    op_push(OCcallint, (long) ep);
    compilecast(n,Gsmall,mode);
    break;
  case RET_LONG:
    op_push(OCcalllong, (long) ep);
    compilecast(n,Gsmall,mode);
    break;
  case RET_VOID:
    op_push(OCcallvoid, (long) ep);
    compilecast(n,Gvoid,mode);
    break;
  }
  if (nbpointers) op_push(OCendptr,nbpointers);
  avma=ltop;
}

static void
compilenode(long n, int mode, long flag)
{
  long x,y;
  if (n<0)
    pari_err(bugparier,"compilenode");
  x=tree[n].x;
  y=tree[n].y;

  switch(tree[n].f)
  {
  case Fseq:
    if (tree[x].f!=Fnoarg)
      compilenode(x,Gvoid,0);
    compilenode(y,mode,flag&FLreturn);
    return;
  case Ffacteurmat:
    compilefacteurmat(n,mode);
    if (mode==Ggen && !(flag&FLnocopy))
      op_push(OCcopy,0);
    break;
  case Faffect:
    if (tree[x].f==Fentry)
    {
      entree *ep=getvar(x);
      long vn=getmvar(ep);
      compilenode(y,Ggen,FLnocopy);
      if (vn)
        op_push(OCstorelex,vn);
      else
        op_push(OCstoredyn,(long)ep);
      if (mode!=Gvoid)
      {
        if (vn)
          op_push(OCpushlex,vn);
        else
          op_push(OCpushdyn,(long)ep);
        if (flag&FLreturn)
          op_push(OCcopyifclone,0);
        compilecast(n,Ggen,mode);
      }
    }
    else
      compilefunc(is_entry("_=_"),n,mode);
    break;
  case Fconst:
    {
      pari_sp ltop=avma;
      if (tree[n].x!=CSTquote)
      {
        if (mode==Gvoid) return;
        if (mode==Gvar)
          pari_err(varer1,tree[n].str,get_origin());
      }
      if (mode==Gsmall)
        pari_err(talker2,"this should be a small integer",
            tree[n].str,get_origin());
      switch(tree[n].x)
      {
      case CSTreal:
        op_push(OCpushreal, data_push(strntoGENstr(tree[n].str,tree[n].len)));
        break;
      case CSTint:
        op_push(OCpushgen,  data_push(strtoi((char*)tree[n].str)));
        compilecast(n,Ggen, mode);
        break;
      case CSTstr:
        op_push(OCpushgen,  data_push(strntoGENexp(tree[n].str,tree[n].len)));
        break;
      case CSTquote:
        {
          entree *ep = fetch_entry(tree[n].str+1,tree[n].len-1);
          if (EpSTATIC(ep))
            pari_err(talker2,"variable name expected",
                tree[n].str+1,get_origin());
          op_push(OCpushvar, (long)ep);
          compilecast(n,Ggen, mode);
          break;
        }
      default:
        pari_err(bugparier,"compilenode, unsupported constant");
      }
      avma=ltop;
      return;
    }
  case Fsmall:
    if (mode==Ggen)
    {
      GEN stog[]={gen_m1, gen_0, gen_1, gen_2};
      if (x>=-1 && x<=2)
        op_push(OCpushlong, (long) stog[x+1]);
      else
        op_push(OCpushstoi, x);
    }
    else
    {
      op_push(OCpushlong, x);
      compilecast(n,Gsmall,mode);
    }
    return;
  case Fvec:
    compilevec(n, mode, OCvec);
    return;
  case Fmat:
    compilemat(n, mode);
    return;
  case Frefarg:
    pari_err(talker,"unexpected &");
    break;
  case Fentry:
    {
      entree *ep=getentry(n);
      long vn=getmvar(ep);
      if (vn)
      {
        op_push(OCpushlex,(long)vn);
        if (flag&FLreturn)
          op_push(OCcopyifclone,0);
        compilecast(n,Ggen,mode);
        break;
      }
      else if (!EpSTATIC(do_alias(ep)))
      {
        op_push(OCpushdyn,(long)ep);
        if (flag&FLreturn)
          op_push(OCcopyifclone,0);
        compilecast(n,Ggen,mode);
        break;
      }
    }
  case Fderfunc: /*Fall through*/
  case Ffunction:
    {
      entree *ep=getfunc(n);
      if (EpVALENCE(ep)==EpVAR || EpVALENCE(ep)==EpNEW)
        compileuserfunc(ep,n,mode);
      else
        compilefunc(ep,n,mode);
      return;
    }
  case Fcall:
    compilenode(x,Ggen,0);
    compilecall(n,OCcalluser,mode);
    return;
  case Flambda:
    {
      pari_sp ltop=avma;
      struct codepos pos;
      long i;
      GEN arg=listtogen(x,Flistarg);
      long nb=lg(arg)-1,nbmvar=numbmvar();
      GEN text=cgetg(3,t_VEC);
      gel(text,1)=strntoGENstr(tree[x].str,tree[x].len);
      gel(text,2)=strntoGENstr(tree[y].str,tree[y].len);
      getcodepos(&pos);
      if (nb) op_push(OCgetargs,nb);
      for(i=1;i<=nb;i++)
        var_push(NULL,Lmy);
      for (i=1;i<=nb;i++)
      {
        long a=arg[i];
        if (tree[a].f==Faffect)
        {
          struct codepos lpos;
          getcodepos(&lpos);
          compilenode(tree[a].y,Ggen,0);
          op_push(OCpushgen, data_push(getclosure(&lpos)));
          op_push(OCdefaultarg,-nb+i-1);
          a=tree[a].x;
        }
        localvars[s_lvar.n-nb+i-1].ep=getvar(a);
      }
      if (y>=0 && tree[y].f!=Fnoarg)
        compilenode(y,Ggen,FLreturn);
      else
        compilecast(n,Gvoid,Ggen);
      op_push(OCpushgen, data_push(getfunction(&pos,nb,nbmvar,text)));
      if(nbmvar) op_push(OCsaveframe,0);
      avma=ltop;
      break;
    }
  case Ftag:
    compilenode(x, mode,0);
    return;
  case Fnoarg:
    compilecast(n,Gvoid,mode);
    return;
  default:
    pari_err(bugparier,"compilenode");
  }
}

GEN
gp_closure(long n)
{
  struct codepos pos={0,0,0,-1};
  compilenode(n,Ggen,0);
  return getclosure(&pos);
}

