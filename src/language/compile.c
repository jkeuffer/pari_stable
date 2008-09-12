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
  GEN z = cgetg(1+nchar2nlong(len-1), t_STR);
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
        default:   *s=*t; if (!*t) compile_err("unfinished string",str);
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

struct frame_s
{
  long pc;
  GEN frame;
};

static THREAD gp2c_stack s_opcode, s_operand, s_data, s_lvar;
static THREAD gp2c_stack s_dbginfo, s_frame;
static THREAD char *opcode;
static THREAD long *operand;
static THREAD GEN *data;
static THREAD long offset;
static THREAD struct vars_s *localvars;
static THREAD const char **dbginfo, *dbgstart;
static THREAD struct frame_s *frames;

void
pari_init_compiler(void)
{
  stack_init(&s_opcode,sizeof(*opcode),(void **)&opcode);
  stack_init(&s_operand,sizeof(*operand),(void **)&operand);
  stack_init(&s_data,sizeof(*data),(void **)&data);
  stack_init(&s_lvar,sizeof(*localvars),(void **)&localvars);
  stack_init(&s_dbginfo,sizeof(*dbginfo),(void **)&dbginfo);
  stack_init(&s_frame,sizeof(*frames),(void **)&frames);
  offset=-1;
}
void
pari_close_compiler(void)
{
  stack_delete(&s_opcode);
  stack_delete(&s_operand);
  stack_delete(&s_data);
  stack_delete(&s_lvar);
}

struct codepos
{
  long opcode, data, localvars, frames;
  long offset;
  const char *dbgstart;
};

static void
getcodepos(struct codepos *pos)
{
  pos->opcode=s_opcode.n;
  pos->data=s_data.n;
  pos->offset=offset;
  pos->localvars=s_lvar.n;
  pos->dbgstart=dbgstart;
  pos->frames=s_frame.n;
  offset=s_data.n-1;
}

void
compiler_reset(void)
{
  s_opcode.n=0;
  s_operand.n=0;
  s_dbginfo.n=0;
  s_data.n=0;
  s_lvar.n=0;
  offset=-1;
}

static GEN
getfunction(struct codepos *pos, long arity, long nbmvar, GEN text)
{
  long lop =s_opcode.n+1-pos->opcode;
  long ldat=s_data.n+1-pos->data;
  long lfram=s_frame.n+1-pos->frames;
  GEN cl=cgetg(nbmvar?8:(text?7:6),t_CLOSURE);
  GEN frpc, fram, dbg;
  char *s;
  long i;
  cl[1] = arity;
  gel(cl,2) = cgetg(nchar2nlong(lop)+1, t_STR);
  gel(cl,3) = cgetg(lop,  t_VECSMALL);
  gel(cl,4) = cgetg(ldat, t_VEC);
  gel(cl,5) = cgetg(4,  t_VEC);
  dbg = cgetg(lop,  t_VECSMALL);
  frpc = cgetg(lfram,  t_VECSMALL);
  fram = cgetg(lfram,  t_VEC);
  gmael(cl,5,1) = dbg;
  gmael(cl,5,2) = frpc;
  gmael(cl,5,3) = fram;
  if (text) gel(cl,6) = text;
  if (nbmvar) gel(cl,7) = zerovec(nbmvar);
  s=GSTR(gel(cl,2))-1;
  for(i=1;i<lop;i++)
  {
    s[i] = opcode[i+pos->opcode-1];
    mael(cl, 3, i) = operand[i+pos->opcode-1];
    dbg[i] = dbginfo[i+pos->opcode-1]-dbgstart;
  }
  s[i]=0;
  s_opcode.n=pos->opcode;
  s_operand.n=pos->opcode;
  s_dbginfo.n=pos->opcode;
  for(i=1;i<ldat;i++)
  {
    gmael(cl, 4, i) = gcopy(data[i+pos->data-1]);
    gunclone(data[i+pos->data-1]);
  }
  s_data.n=pos->data;
  s_lvar.n=pos->localvars;
  for(i=1;i<lfram;i++)
  {
    long j=i+pos->frames-1;
    frpc[i] = frames[j].pc-pos->opcode+1;
    gel(fram, i) = gcopy(frames[j].frame);
    gunclone(frames[j].frame);
  }
  s_frame.n=pos->frames;
  offset=pos->offset;
  dbgstart=pos->dbgstart;
  return cl;
}

static GEN
getclosure(struct codepos *pos)
{
  return getfunction(pos,0,0,NULL);
}

static void
op_push_loc(op_code o, long x, const char *loc)
{
  long n=stack_new(&s_opcode);
  long m=stack_new(&s_operand);
  long d=stack_new(&s_dbginfo);
  opcode[n]=o;
  operand[m]=x;
  dbginfo[d]=loc;
}

static void
op_push(op_code o, long x, long n)
{
  return op_push_loc(o,x,tree[n].str);
}

static void
op_insert_loc(long k, op_code o, long x, const char *loc)
{
  long i;
  long n=stack_new(&s_opcode);
  (void) stack_new(&s_operand);
  (void) stack_new(&s_dbginfo);
  for (i=n-1; i>=k; i--)
  {
    opcode[i+1] = opcode[i];
    operand[i+1]= operand[i];
    dbginfo[i+1]= dbginfo[i];
  }
  opcode[k]  = o;
  operand[k] = x;
  dbginfo[k] = loc;
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

static void
frame_push(GEN x)
{
  long n=stack_new(&s_frame);
  frames[n].pc = s_opcode.n-1;
  frames[n].frame = gclone(x);
}

static GEN
pack_localvars(void)
{
  GEN pack=cgetg(3,t_VEC);
  long i,l=s_lvar.n;
  GEN t=cgetg(1+l,t_VECSMALL);
  GEN e=cgetg(1+l,t_VECSMALL);
  gel(pack,1)=t;
  gel(pack,2)=e;
  for(i=1;i<=l;i++)
  {
    t[i]=localvars[i-1].type;
    e[i]=(long)localvars[i-1].ep;
  }
  return pack;
}

void
closure_context(GEN C, long lpc)
{
  char *code=GSTR(gel(C,2))-1;
  GEN oper=gel(C,3);
  GEN frpc=gmael(C,5,2);
  GEN fram=gmael(C,5,3);
  long pc, j=1;
  for(pc=0; pc<=lpc; pc++)
  {
    if (pc>0 && (code[pc]==OClocalvar || code[pc]==OClocalvar0))
      var_push((entree*)oper[pc],Llocal);
    if (j<lg(frpc) && pc==frpc[j])
    {
      long k;
      GEN e = gel(fram,j);
      for(k=1; k<lg(e); k++)
        var_push((entree*)e[k], Lmy);
      j++;
    }
  }
}

void
localvars_unpack(GEN pack)
{
  GEN t=gel(pack,1);
  GEN e=gel(pack,2);
  long i;
  for(i=1;i<lg(t);i++)
    var_push((entree*)e[i],(Ltype)t[i]);
}

long
localvars_find(GEN pack, entree *ep)
{
  GEN t=gel(pack,1);
  GEN e=gel(pack,2);
  long i;
  long vn=0;
  for(i=lg(e)-1;i>=1;i--)
  {
    if(t[i]==Lmy)
      vn--;
    if(e[i]==(long)ep)
      return t[i]==Lmy?vn:0;
  }
  return 0;
}

enum FLflag {FLnocopy=1, FLreturn=2};

static void compilenode(long n, int mode, long flag);

typedef enum {PPend,PPstd,PPdefault,PPdefaultmulti,PPstar,PPauto} PPproto;

static PPproto
parseproto(char const **q, char *c, const char *str)
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
      compile_err("function has incomplete prototype",str);
    case 'G':
    case '&':
    case 'W':
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
        compile_err("function has incomplete prototype",str);
      *c=p[-2];
      *q=p;
      return PPdefaultmulti;
    }
    break;
  case 'C':
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
        compile_err("function prototype is not supported",str);
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

static long
detag(long n)
{
  while (tree[n].f==Ftag)
    n=tree[n].x;
  return n;
}

/* return type for GP functions */
static op_code
get_ret_type(const char **p, long arity, Gtype *t)
{
  if (**p == 'v') { (*p)++; *t=Gvoid; return OCcallvoid; }
  else if (**p == 'i') { (*p)++; *t=Gsmall; return OCcallint; }
  else if (**p == 'l') { (*p)++; *t=Gsmall; return OCcalllong; }
  else { *t=Ggen; return arity==2?OCcallgen2:OCcallgen; }
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
    if (type==Ggen)        op_push(OCitos,-1,n);
    else if (type==Gvoid)  op_push(OCpushlong,0,n);
    else compile_err("this should be a small integer",tree[n].str);
    break;
  case Ggen:
    if (type==Gsmall)      op_push(OCstoi,0,n);
    else if (type==Gvoid)  op_push(OCpushlong,(long)gnil,n);
    break;
  case Gvoid:
    op_push(OCpop, 1,n);
    break;
  case Gvar:
    if (type==Ggen)        op_push(OCvarn,-1,n);
    else compile_varer1(tree[n].str);
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
getsymbol(long n)
{
  n = detag(n);
  if (tree[n].f!=Fentry)
    compile_varer1(tree[n].str);
  return get_entree(n);
}

/* match any Fentry */
static entree *
getentry(long n)
{
  return do_alias(getsymbol(n));
}

static entree *
getfunc(long n)
{
  return do_alias(get_entree(n));
}

/* match Fentry that are not actually EpSTATIC functions called without parens*/
static entree *
getvar(long n)
{
  entree *ep = getentry(n);
  if (EpSTATIC(do_alias(ep)))
    compile_varer1(tree[n].str);
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
  n = detag(n);
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
    return 1;
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

static void
checkdups(GEN arg, GEN vep)
{
  long l=vecsmall_duplicate(vep);
  if (l!=0) compile_err("variable declared twice",tree[arg[l]].str);
}

static entree *
getlvalue(long n)
{
  while (tree[n].f==Ffacteurmat || tree[n].f==Ftag)
    n=tree[n].x;
  return getvar(n);
}

static void
compilelvalue(long n)
{
  n = detag(n);
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
      op_push(OCcompo2ptr,0,y);
      return;
    }
    compilelvalue(x);
    compilenode(yx,Gsmall,0);
    if (f==Fmatrix && yy==-1)
      op_push(OCcompo1ptr,0,y);
    else
    {
      switch(f)
      {
      case Fmatrix:
        compilenode(yy,Gsmall,0);
        op_push(OCcompo2ptr,0,y);
        break;
      case FmatrixR:
        op_push(OCcompoCptr,0,y);
        break;
      case FmatrixL:
        op_push(OCcompoLptr,0,y);
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
    op_push(OCcompo1,mode,y);
    return;
  }
  switch(f)
  {
  case Fmatrix:
    compilenode(yy,Gsmall,0);
    op_push(OCcompo2,mode,y);
    return;
  case FmatrixR:
    op_push(OCcompoC,0,y);
    compilecast(n,Gvec,mode);
    return;
  case FmatrixL:
    op_push(OCcompoL,0,y);
    compilecast(n,Gvec,mode);
    return;
  default:
    pari_err(bugparier,"compilefacteurmat");
  }
}

static void
compilesmall(long n, long x, long mode)
{
  if (mode==Ggen)
  {
    GEN stog[]={gen_m2, gen_m1, gen_0, gen_1, gen_2};
    if (x>=-2 && x<=2)
      op_push(OCpushlong, (long) stog[x+2], n);
    else
      op_push(OCpushstoi, x, n);
  }
  else
  {
    op_push(OCpushlong, x, n);
    compilecast(n,Gsmall,mode);
  }
}

static void
compilevec(long n, long mode, op_code op)
{
  pari_sp ltop=avma;
  long x=tree[n].x;
  long i;
  GEN arg=listtogen(x,Fmatrixelts);
  long l=lg(arg);
  op_push(op,l,n);
  for (i=1;i<l;i++)
  {
    compilenode(arg[i],Ggen,FLnocopy);
    op_push(OCstackgen,i,n);
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
  op_push(OCpushlong, lglin,n);
  if (lglin==1)
    op_push(OCmat,1,n);
  for(i=1;i<lglin;i++)
  {
    GEN col=listtogen(line[i],Fmatrixelts);
    long l=lg(col), k;
    if (i==1)
    {
      lgcol=l;
      op_push(OCmat,lgcol,n);
    }
    else if (l!=lgcol)
      compile_err("matrix must be rectangular",tree[line[i]].str);
    k=i;
    for(j=1;j<lgcol;j++)
    {
      k-=lglin;
      compilenode(col[j], Ggen,0);
      op_push(OCstackgen,k,n);
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
      compile_err("unexpected character: ", tree[y].str);
    i++;
  }
  if (tree[x].f==Fnoarg)
    compile_err("unexpected character: ", tree[x].str);
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
compilecall(long n, int mode)
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
      op_push(OCpushlong,0,n);
  op_push(OCcalluser,nb,n);
  compilecast(n,Ggen,mode);
  avma=ltop;
  return;
}

static void
compileuserfunc(entree *ep, long n, int mode)
{
  long vn=getmvar(ep);
  if (vn)
    op_push(OCpushlex,vn,n);
  else
    op_push(OCpushdyn,(long)ep,n);
  compilecall(n, mode);
}

static void
compilefunc(entree *ep, long n, int mode)
{
  pari_sp ltop=avma;
  long i,j;
  long x=tree[n].x;
  long y=tree[n].y;
  op_code ret_op;
  Gtype ret_typ;
  char const *p,*q;
  char c;
  const char *flags = NULL;
  const char *str;
  PPproto mod;
  GEN arg=listtogen(y,Flistarg);
  long lnc=first_safe_arg(arg);
  long nbpointers=0, nbopcodes;
  long nb=lg(arg)-1, lev=0;
  entree *ev[8];
  if (x>=OPnboperator)
    str=tree[x].str;
  else
  {
    if (nb==2)
      str=tree[arg[1]].str+tree[arg[1]].len;
    else if (nb==1)
      str=tree[arg[1]].str;
    else
      str=tree[n].str;
  }
  if (tree[n].f==Faffect)
  {
    nb=2; lnc=2; arg=mkvecsmall2(x,y);
  }
  else if (is_func_named(x,"if") && mode==Gvoid)
    ep=is_entry("_void_if");
  else if (is_func_named(x,"my"))
  {
    long lgarg;
    GEN vep = cgetg_copy(arg, &lgarg);
    
    if (nb)
    {
      for(i=1;i<=nb;i++)
      {
        long a=arg[i];
        vep[i]=(long)getvar(tree[a].f==Faffect?tree[a].x:a);
        var_push(NULL,Lmy);
      }
      checkdups(arg,vep);
      op_push_loc(OCnewframe,nb,str);
      frame_push(vep);
      for (i=1;i<=nb;i++)
      {
        long a=arg[i];
        if (tree[a].f==Faffect && !is_node_zero(tree[a].y))
        {
          compilenode(tree[a].y,Ggen,0);
          op_push(OCstorelex,-nb+i-1,a);
        }
        localvars[s_lvar.n-nb+i-1].ep=(entree*)vep[i];
      }
    }
    compilecast(n,Gvoid,mode);
    avma=ltop;
    return;
  }
  else if (is_func_named(x,"local"))
  {
    long lgarg;
    GEN vep = cgetg_copy(arg, &lgarg);
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
      vep[i] = (long) (en = getvar(a));
      op_push(op,vep[i],a);
      var_push(en,Llocal);
    }
    checkdups(arg,vep);
    compilecast(n,Gvoid,mode);
    avma=ltop;
    return;
  }
  /*We generate dummy code for global() for backward compatibility*/
  else if (is_func_named(x,"global"))
  {
    pari_warn(warner,"global(...) is deprecated");
    for (i=1;i<=nb;i++)
    {
      long a=arg[i];
      long en;
      if (tree[a].f==Faffect)
      {
        compilenode(tree[a].y,Ggen,0);
        a=tree[a].x;
        en=(long)getvar(a);
        op_push(OCstoredyn,en,a);
      }
      else
      {
        en=(long)getvar(a);
        op_push(OCpushdyn,en,a);
        op_push(OCpop,1,a);
      }
    }
    compilecast(n,Gvoid,mode);
    avma=ltop;
    return;
  }
  else if (is_func_named(x,"O") || (compatible==OLDALL && is_func_named(x,"o")))
  {
    if (nb!=1)
      compile_err("wrong number of arguments", tree[n].str+tree[n].len-1);
    ep=is_entry("O(_^_)");
    if (tree[arg[1]].f==Ffunction && tree[arg[1]].x==OPpow)
    {
      arg = listtogen(tree[arg[1]].y,Flistarg);
      nb  = lg(arg)-1;
      lnc = first_safe_arg(arg);
    }
  }
  else if (x==OPn && tree[y].f==Fsmall)
  {
    avma=ltop;
    compilesmall(y, -tree[y].x, mode);
    return;
  }
  else if (x==OPtrans && tree[y].f==Fvec)
  {
    avma=ltop;
    compilevec(y, mode, OCcol);
    return;
  }
  else if (x==OPpow && nb==2 && tree[arg[2]].f==Fsmall)
    ep=is_entry("_^s");
  else if (x==OPcat)
    compile_err("expected character: ',' or ')' instead of",
        tree[arg[1]].str+tree[arg[1]].len);
  p=ep->code;
  if (!ep->value)
    compile_err("unknown function",tree[n].str);
  nbopcodes = s_opcode.n;
  ret_op = get_ret_type(&p, ep->arity, &ret_typ);
  i=0; j=1;
  if (*p)
  {
    q=p;
    while((mod=parseproto(&p,&c,tree[n].str))!=PPend)
    {
      if (j<=nb && tree[arg[j]].f!=Fnoarg
          && (mod==PPdefault || mod==PPdefaultmulti))
        mod=PPstd;
      switch(mod)
      {
      case PPstd:
        if (j>nb) compile_err("too few arguments", tree[n].str+tree[n].len-1);
        if (tree[arg[j]].f==Fnoarg && c!='I' && c!='E')
          compile_err("missing mandatory argument", tree[arg[j]].str);
        switch(c)
        {
        case 'G':
          compilenode(arg[j],Ggen,j>=lnc?FLnocopy:0);
          j++;
          break;
        case 'W':
          (void)getlvalue(arg[j]);
          compilenode(arg[j++],Ggen,FLnocopy);
          break;
        case 'M':
          if (tree[arg[j]].f!=Fsmall)
          {
            if (!flags) flags = ep->code;
            flags = strchr(flags, '\n'); /* Skip to the following '\n' */
            if (!flags)
              compile_err("missing flag in string function signature",
                           tree[n].str);
            flags++;
            if (tree[arg[j]].f==Fconst && tree[arg[j]].x==CSTstr)
            {
              GEN str=strntoGENexp(tree[arg[j]].str,tree[arg[j]].len);
              op_push(OCpushlong, eval_mnemonic(str, flags),n);
              j++;
            } else
            {
              compilenode(arg[j++],Ggen,0);
              op_push(OCpushlong,(long)flags,n);
              op_push(OCcallgen2,(long)is_entry("_eval_mnemonic"),n);
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
                compile_err("expected character: '&'", tree[a].str);
              a=tree[a].x;
            }
            a=detag(a);
            ep=getlvalue(a);
            vn=getmvar(ep);
            if (tree[a].f==Fentry)
            {
              if (vn)
                op_push(OCsimpleptrlex, vn,n);
              else
                op_push(OCsimpleptrdyn, (long)ep,n);
            }
            else
            {
              if (vn)
                op_push(OCnewptrlex, vn,n);
              else
                op_push(OCnewptrdyn, (long)ep,n);
              compilelvalue(a);
              op_push(OCpushptr, 0,n);
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
            if (lev)
            {
              GEN vep=cgetg(lev+1,t_VECSMALL);
              for(i=0;i<lev;i++)
              {
                if (!ev[i])
                  compile_err("missing variable name", tree[a].str-1);
                var_push(ev[i],Lmy);
                vep[i+1]=(long)ev[i];
              }
              frame_push(vep);
            }
            if (tree[a].f==Fnoarg)
              compilecast(a,Gvoid,type);
            else
              compilenode(a,type,flag);
            op_push(OCpushgen, data_push(getclosure(&pos)),a);
            break;
          }
        case 'V':
          {
            ev[lev++] = getvar(arg[j++]);
            break;
          }
        case 'S':
          {
            long a = arg[j++];
            entree *ep = getsymbol(a);
            op_push(OCpushlong, (long)ep,a);
            break;
          }
        case '=':
          {
            long x=tree[arg[j]].x;
            long y=tree[arg[j]].y;
            if (tree[arg[j]].f!=Faffect)
              compile_err("expected character: '=' instead of",
                  tree[arg[j]].str+tree[arg[j]].len);
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
              op_push(OCpushgen, data_push(strntoGENstr(tree[tree[a].x].str,tree[tree[a].x].len)),n);
              op_push(OCtostr, -1,n);
            }
            else
            {
              compilenode(a,Ggen,FLnocopy);
              op_push(OCtostr, -1,n);
            }
            break;
          }
        case 's':
          {
            long a = arg[j++];
            GEN g = cattovec(a, OPcat);
            long l, nb = lg(g)-1;
            if (nb==1)
            {
              compilenode(g[1], Ggen,0);
              op_push(OCtostr, -1, a);
            } else
            {
              op_push(OCvec, nb+1, a);
              for(l=1; l<=nb; l++)
              {
                compilenode(g[l], Ggen,0);
                op_push(OCstackgen,l, a);
              }
              op_push(OCcallgen,(long)is_entry("Str"), a);
              op_push(OCtostr, -1, a);
            }
            break;
          }
        default:
          pari_err(talker,"Unknown prototype code `%c' for `%.*s'",c,
              tree[x].len, tree[x].str);
        }
        break;
      case PPauto:
        switch(c)
        {
        case 'p':
          op_push(OCprecreal,0,n);
          break;
        case 'P':
          op_push(OCprecdl,0,n);
          break;
        case 'C':
          op_push(OCpushgen,data_push(pack_localvars()),n);
          break;
        case 'f':
          {
            static long foo;
            op_push(OCpushlong,(long)&foo,n);
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
        case 'E':
        case 'I':
          op_push(OCpushlong,0,n);
          break;
        case 'n':
          op_push(OCpushlong,-1,n);
          break;
        case 'V':
          ev[lev++] = NULL;
          break;
        default:
          pari_err(talker,"Unknown prototype code `%c' for `%.*s'",c,
              tree[x].len, tree[x].str);
        }
        break;
      case PPdefaultmulti:
        j++;
        switch(c)
        {
        case 'G':
          op_push(OCpushgen,data_push(strntoGENstr(q+1,p-4-q)),n);
          op_push(OCcallgen,(long)is_entry("_geval"),n);
          break;
        case 'L':
        case 'M':
          op_push(OCpushlong,strtol(q+1,NULL,10),n);
          break;
        case 'r':
        case 's':
          if (q[1]=='"' && q[2]=='"')
            op_push(OCpushlong,(long)"",n);
          else
            compile_err("function prototype not supported",tree[n].str);
          break;
        default:
          pari_err(talker,"Unknown prototype code `%c' for `%.*s'",c,
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
            op_push_loc(OCvec, l1+1, str);
            for(m=1,k=1;k<=n;k++)
              for(l=1;l<lg(g[k]);l++,m++)
              {
                compilenode(mael(g,k,l),Ggen,0);
                op_push(OCstackgen,m,mael(g,k,l));
              }
            j=nb+1;
            break;
          }
        default:
          pari_err(talker,"Unknown prototype code `%c*' for `%.*s'",c,
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
    compile_err("too many arguments",tree[arg[j]].str);
  op_push_loc(ret_op, (long) ep, str);
  if (ret_typ==Ggen && nbpointers==0 && s_opcode.n>nbopcodes+128)
  {
    op_insert_loc(nbopcodes,OCavma,0,str);
    op_push_loc(OCgerepile,0,str);
  }
  compilecast(n,ret_typ,mode);
  if (nbpointers) op_push_loc(OCendptr,nbpointers, str);
  avma=ltop;
}

static GEN
genclosure(long n, entree *ep)
{
  struct codepos pos;
  long nb=0;
  const char *code=ep->code,*p,*q;
  char c;
  long index=ep->arity;
  long arity=0, maskarg=0, maskarg0=0, stop=0;
  PPproto mod;
  Gtype ret_typ;
  op_code ret_op=get_ret_type(&code,ep->arity,&ret_typ);
  p=code;
  while ((mod=parseproto(&p,&c,NULL))!=PPend)
  {
    if (mod==PPauto)
      stop=1;
    else
    {
      if (stop) return NULL;
      if (c=='V') continue;
      maskarg<<=1; maskarg0<<=1; arity++;
      switch(mod)
      {
      case PPstd:
        maskarg|=1L;
        break;
      case PPdefault:
        switch(c)
        {
        case '&':
        case 'E':
        case 'I':
          maskarg0|=1L;
          break;
        }
        break;
      default:
        break;
      }
    }
  }
  if (*code==0 || (EpSTATIC(ep) && maskarg==0))
    return gen_0;
  getcodepos(&pos);
  dbgstart=tree[n].str;
  if (maskarg)  op_push(OCcheckargs,maskarg,n);
  if (maskarg0) op_push(OCcheckargs0,maskarg0,n);
  p=code;
  while ((mod=parseproto(&p,&c,NULL))!=PPend)
  {
    switch(mod)
    {
    case PPauto:
      switch(c)
      {
      case 'p':
        op_push(OCprecreal,0,n);
        break;
      case 'P':
        op_push(OCprecdl,0,n);
        break;
      case 'C':
        break;
        op_push(OCpushgen,data_push(pack_localvars()),n);
        break;
      case 'f':
        {
          static long foo;
          op_push(OCpushlong,(long)&foo,n);
          break;
        }
      }
    default:
      break;
    }
  }
  q = p = code;
  while ((mod=parseproto(&p,&c,NULL))!=PPend)
  {
    switch(mod)
    {
    case PPstd:
      switch(c)
      {
      case 'G':
        break;
      case 'M':
      case 'L':
        op_push(OCitos,-index,n);
        break;
      case 'n':
        op_push(OCvarn,-index,n);
        break;
      case '&': case '*':
      case 'I':
      case 'E':
      case 'V':
      case 'S':
      case '=':
        return NULL;
      case 'r':
      case 's':
        op_push(OCtostr,-index,n);
        break;
      }
      break;
    case PPauto:
      break;
    case PPdefault:
      switch(c)
      {
      case 'G':
      case '&':
      case 'E':
      case 'I':
      case 'V':
        break;
      case 'n':
        op_push(OCvarn,-index,n);
        break;
      default:
        pari_err(talker,"Unknown prototype code `D%c' for `%s'",c,ep->name);
      }
      break;
    case PPdefaultmulti:
      switch(c)
      {
      case 'G':
        return NULL;
      case 'L':
      case 'M':
        op_push(OCpushlong,strtol(q+1,NULL,10),n);
        op_push(OCdefaultitos,-index,n);
        break;
      case 'r':
      case 's':
        op_push(OCtostr,-index,n);
        break;
      default:
        pari_err(talker,
                 "Unknown prototype code `D...,%c,' for `%s'",c,ep->name);
      }
      break;
    case PPstar:
      switch(c)
      {
      case 's':
        return NULL;
      default:
        pari_err(talker,"Unknown prototype code `%c*' for `%s'",c,ep->name);
      }
      break;
    default:
       return NULL;
    }
    index--;
    q = p;
  }
  op_push(ret_op, (long) ep, n);
  compilecast(n, ret_typ, Ggen);
  return getfunction(&pos,nb+arity,0,strtoGENstr(ep->name));
}

static void
closurefunc(entree *ep, long n, long mode)
{
  pari_sp ltop=avma;
  GEN C;
  if (!ep->value) compile_err("unknown function",tree[n].str);
  C = genclosure(n, ep);
  if (!C) compile_err("sorry, closure not implemented",tree[n].str);
  if (C==gen_0)
  {
    compilefunc(ep,n,mode);
    return;
  }
  op_push(OCpushgen, data_push(C), n);
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
      op_push(OCcopy,0,n);
    return;
  case Faffect:
    x = detag(x);
    if (tree[x].f==Fentry)
    {
      entree *ep=getvar(x);
      long vn=getmvar(ep);
      compilenode(y,Ggen,FLnocopy);
      if (vn)
        op_push(OCstorelex,vn,n);
      else
        op_push(OCstoredyn,(long)ep,n);
      if (mode!=Gvoid)
      {
        if (vn)
          op_push(OCpushlex,vn,n);
        else
          op_push(OCpushdyn,(long)ep,n);
        if (!(flag&FLnocopy))
          op_push(OCcopyifclone,0,n);
        compilecast(n,Ggen,mode);
      }
    }
    else
      compilefunc(is_entry("_=_"),n,mode);
    return;
  case Fconst:
    {
      pari_sp ltop=avma;
      if (tree[n].x!=CSTquote)
      {
        if (mode==Gvoid) return;
        if (mode==Gvar) compile_varer1(tree[n].str);
      }
      if (mode==Gsmall)
        compile_err("this should be a small integer", tree[n].str);
      switch(tree[n].x)
      {
      case CSTreal:
        op_push(OCpushreal, data_push(strntoGENstr(tree[n].str,tree[n].len)),n);
        break;
      case CSTint:
        op_push(OCpushgen,  data_push(strtoi((char*)tree[n].str)),n);
        compilecast(n,Ggen, mode);
        break;
      case CSTstr:
        op_push(OCpushgen,  data_push(strntoGENexp(tree[n].str,tree[n].len)),n);
        break;
      case CSTquote:
        {
          entree *ep = fetch_entry(tree[n].str+1,tree[n].len-1);
          if (EpSTATIC(ep)) compile_varer1(tree[n].str+1);
          op_push(OCpushvar, (long)ep,n);
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
    compilesmall(n, x, mode);
    return;
  case Fvec:
    compilevec(n, mode, OCvec);
    return;
  case Fmat:
    compilemat(n, mode);
    return;
  case Frefarg:
    compile_err("unexpected &",tree[n].str);
    return;
  case Fentry:
    {
      entree *ep=getentry(n);
      long vn=getmvar(ep);
      if (vn)
      {
        op_push(OCpushlex,(long)vn,n);
        if (flag&FLreturn)
          op_push(OCcopyifclone,0,n);
        compilecast(n,Ggen,mode);
      }
      else if (ep->valence==EpVAR || ep->valence==EpNEW)
      {
        op_push(OCpushdyn,(long)ep,n);
        if (!(flag&FLnocopy))
          op_push(OCcopyifclone,0,n);
        compilecast(n,Ggen,mode);
      }
      else
        closurefunc(ep,n,mode);
      return;
    }
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
    compilecall(n,mode);
    return;
  case Flambda:
    {
      pari_sp ltop=avma;
      struct codepos pos;
      long i;
      GEN arg=listtogen(x,Flistarg);
      long nb, lgarg, nbmvar=numbmvar();
      GEN vep = cgetg_copy(arg, &lgarg);
      GEN text=cgetg(3,t_VEC);
      gel(text,1)=strntoGENstr(tree[x].str,tree[x].len);
      gel(text,2)=strntoGENstr(tree[y].str,tree[y].len);
      getcodepos(&pos);
      dbgstart=tree[y].str;
      nb = lgarg-1;
      if (nb)
      {
        for(i=1;i<=nb;i++)
        {
          long a=arg[i];
          vep[i]=(long)getvar(tree[a].f==Faffect?tree[a].x:a);
          var_push(NULL,Lmy);
        }
        checkdups(arg,vep);
        op_push(OCgetargs,nb,y);
        frame_push(vep);
        for (i=1;i<=nb;i++)
        {
          long a=arg[i];
          if (tree[a].f==Faffect)
          {
            struct codepos lpos;
            getcodepos(&lpos);
            compilenode(tree[a].y,Ggen,0);
            op_push(OCpushgen, data_push(getclosure(&lpos)),a);
            op_push(OCdefaultarg,-nb+i-1,a);
          }
          localvars[s_lvar.n-nb+i-1].ep=(entree*)vep[i];
        }
      }
      if (y>=0 && tree[y].f!=Fnoarg)
        compilenode(y,Ggen,FLreturn);
      else
        compilecast(n,Gvoid,Ggen);
      op_push(OCpushgen, data_push(getfunction(&pos,nb,nbmvar,text)),n);
      if(nbmvar) op_push(OCsaveframe,0,n);
      avma=ltop;
      return;
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
  struct codepos pos;
  getcodepos(&pos);
  dbgstart=tree[n].str;
  compilenode(n,Ggen,FLreturn);
  return getfunction(&pos,0,0,strntoGENstr(tree[n].str,tree[n].len));
}

GEN
closure_deriv(GEN G)
{
  pari_sp ltop=avma;
  long i;
  struct codepos pos;
  const char *code;
  GEN text;
  long arity=G[1];
  if (typ(gel(G,6))==t_STR)
  {
    code = GSTR(gel(G,6));
    text = cgetg(1+nchar2nlong(2+strlen(code)),t_STR);
    sprintf(GSTR(text),"%s'",code);
  }
  else
  {
    code = GSTR(gmael(G,6,2));
    text = cgetg(3, t_VEC);
    gel(text,1) = gcopy(gmael(G,6,1));
    gel(text,2) = cgetg(1+nchar2nlong(4+strlen(code)),t_STR);
    sprintf(GSTR(gel(text,2)),"(%s)'",code);
  }
  getcodepos(&pos);
  dbgstart=code;
  op_push_loc(OCgetargs, arity,code);
  op_push_loc(OCpushgen,data_push(G),code);
  op_push_loc(OCvec,arity+1,code);
  for (i=1;i<=arity;i++)
  {
    op_push_loc(OCpushlex,i-arity-1,code);
    op_push_loc(OCstackgen,i,code);
  }
  op_push_loc(OCprecreal,0,code);
  op_push_loc(OCcallgen,(long)is_entry("_derivnum"),code);
  return gerepilecopy(ltop, getfunction(&pos,arity,0,text));
}
