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
 **                           Byte-code compiler                          **
 **                                                                       **
 ***************************************************************************/

static THREAD gp2c_stack s_opcode, s_operand, s_data, s_lvar;
static THREAD char *opcode;
static THREAD long *operand;
static THREAD GEN *data;
static THREAD long offset=-1;
static THREAD long *localvars;

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
getclosure(struct codepos *pos)
{
  long lop =s_opcode.n+1-pos->opcode;
  long ldat=s_data.n+1-pos->data;
  GEN cl=cgetg(4,t_VEC);
  char *s;
  long i;
  gel(cl,1) = cgetg(nchar2nlong(lop)+1, t_STR);
  gel(cl,2) = cgetg(lop,  t_VECSMALL);
  gel(cl,3) = cgetg(ldat, t_VEC);
  s=GSTR(gel(cl,1))-1;
  for(i=1;i<lop;i++)
  {
    s[i] = opcode[i+pos->opcode-1];
    mael(cl, 2, i) = operand[i+pos->opcode-1];
  }
  s[i]=0;
  s_opcode.n=pos->opcode;
  s_operand.n=pos->opcode;
  for(i=1;i<ldat;i++)
  {
    gmael(cl, 3, i) = gcopy(data[i+pos->data-1]);
    gunclone(data[i+pos->data-1]);
  }
  s_data.n=pos->data;
  offset=pos->offset;
  return cl;
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
var_push(long x)
{
  long n=stack_new(&s_lvar);
  localvars[n] = x;
} 

static void compilenode(long n, int mode);

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
      *c=*p;
      p+=2;
      *q=p+1;
      return PPstar;
    }
  case 's': /*fall through*/
    if (p[1]=='*')
    {
      *c=*p++;
      *q=p+1;
      return PPstar;
    }
  default:/*fall through*/
    *c=*p;
    *q=p+1;
    return PPstd;
  }
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
    else pari_err(talker2,"this should be an integer",
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
getentry(long n)
{
  long x=tree[n].x;
  if (tree[x].x==CSTmember)
    return fetch_member(tree[x].str, tree[x].len);
  else
    return fetch_entry(tree[x].str, tree[x].len);
}

static entree *
getfunc(long n)
{
  return do_alias(getentry(n));
}

INLINE int
is_func_named(long x, const char *s)
{
  if (tree[x].x!=CSTentry) return 0;
  if (strlen(s)!=tree[x].len) return 0;
  return !strncmp(tree[x].str, s, tree[x].len);
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

static entree *
getlvalue(long n)
{ 
  while (tree[n].f==Ffacteurmat)
    n=tree[n].x;
  return getentry(n);
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
      compilenode(tree[tree[x].y].x,Gsmall);
      compilenode(yx,Gsmall);
      op_push(OCcompo2ptr,0);
      return;
    }
    compilelvalue(x);
    compilenode(yx,Gsmall);
    if (f==Fmatrix && yy==-1)
      op_push(OCcompo1ptr,0);
    else
    {
      switch(f)
      {
      case Fmatrix:
        compilenode(yy,Gsmall);
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
  compilenode(x,Ggen);
  compilenode(yx,Gsmall);
  if (f==Fmatrix && yy==-1)
  {
    op_push(OCcompo1,mode);
    return;
  }
  switch(f)
  {
  case Fmatrix:
    compilenode(yy,Gsmall);
    op_push(OCcompo2,mode);
    break;
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
  long l=lg(arg);
  op_push(op,l);
  for(i=1;i<l;i++)
  {
    compilenode(arg[i],Ggen);
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
      compilenode(col[j], Ggen);
      op_push(OCstackgen,k);
    }
  }
  avma=ltop;
  compilecast(n,Gvec,mode);
}


static GEN
cattovec(long n, long fnum)
{
  long x=n, i=0, nb;
  GEN stack;
  if (tree[n].f==Fnoarg) return cgetg(1,t_VECSMALL);
  while(1)
  {
    long xx=tree[x].x;
    long xy=tree[x].y;
    if (tree[x].f!=Ffunction || xx!=fnum) break;
    x=tree[xy].x;
    i++;
  }
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
compilefunc(long n, int mode)
{
  pari_sp ltop=avma;
  long i,j;
  long x=tree[n].x;
  long y=tree[n].y;
  long ret;
  char const *p,*q;
  char c;
  PPproto mod;
  GEN arg=listtogen(y,Flistarg);
  long nbpointers=0;
  long nb=lg(arg)-1;
  entree *ep = getfunc(n);
  if (EpVALENCE(ep)==EpVAR || EpVALENCE(ep)==EpGVAR)
    pari_err(talker2,"not a function in function call",
        tree[n].str, get_origin());
  if (EpVALENCE(ep)==EpUSER|| EpVALENCE(ep)==EpNEW)
  {
    for (j=1;j<=nb;j++)
      if (tree[arg[j]].f!=Fnoarg)
        compilenode(arg[j], Ggen);
      else
        op_push(OCpushlong,0);
    op_push(OCpushlong, nb);
    if (tree[n].f==Fderfunc)
      op_push(OCderivuser, (long) ep);
    else
      op_push(OCcalluser, (long) ep);
    compilecast(n,Ggen,mode);
    avma=ltop;
    return;
  }
  if (is_func_named(x,"if") && mode==Gvoid)
    ep=is_entry("_void_if");
  if (is_func_named(x,"local"))
  {
    if (tree[n].f==Fderfunc)
      pari_err(talker2,"can't derive this",tree[n].str,get_origin());
    for (i=1;i<=nb;i++)
    {
      long en, a=arg[i];
      if (tree[a].f==Faffect)
      {
        compilenode(tree[a].y,Ggen);
        a=tree[a].x;
      }
      else
        op_push(OCpushstoi,0);
      if (tree[a].f==Ftag)
        a=tree[a].x;
      en=(long)getentry(a);
      op_push(OCgetarg,en);
      var_push(en);
    }
    compilecast(n,Gvoid,mode);
    avma=ltop;
    return;
  }
  if (is_func_named(x,"global"))
  {
    if (tree[n].f==Fderfunc)
      pari_err(talker2,"can't derive this",tree[n].str,get_origin());
    for (i=1;i<=nb;i++)
    {
      long a=arg[i];
      long en;
      if (tree[a].f==Faffect)
      {
        compilenode(tree[a].y,Ggen);
        a=tree[a].x;
      }
      else
        op_push(OCpushlong,0);
      if (tree[a].f==Ftag)
        a=tree[a].x;
      en=(long)getentry(a);
      op_push(OCglobalvar,en);
    }
    compilecast(n,Gvoid,mode);
    avma=ltop;
    return;
  }
  if (is_func_named(x,"O") || (compatible==OLDALL && is_func_named(x,"o")))
  {
    long a=tree[n].y;
    if (tree[n].f==Fderfunc)
      pari_err(talker2,"can't derive this",tree[n].str,get_origin());
    if (tree[a].f!=Ffunction || tree[a].x!=OPpow)
    {
      compilenode(a,Ggen);
      op_push(OCpushlong,1);
    }
    else
    {
      long y=tree[a].y;
      compilenode(tree[y].x,Ggen);
      compilenode(tree[y].y,Gsmall);
    }
    op_push(OCcallgen,(long)ep);
    compilecast(n,Ggen,mode);
    avma=ltop;
    return;
  }
  if (x==OPtrans && tree[y].f==Fvec)
  {
    avma=ltop;
    compilevec(y, mode, OCcol);
    return;
  }
  if (x==OPcat)
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
              tree[n].str+tree[n].len, get_origin());
        switch(c)
        {
        case 'G':
          compilenode(arg[j++],Ggen);
          break;
        case 'M':
        case 'L':
          compilenode(arg[j++],Gsmall);
          break;
        case 'n':
          compilenode(arg[j++],Gvar);
          break;
        case '&': case '*': 
          {
            long a=arg[j++];
            entree *ep;
            if (c=='&')
            {
              if (tree[a].f!=Frefarg)
                pari_err(talker2,"expected character: '&'",
                    tree[a].str, get_origin());
              a=tree[a].x;
            }
            ep=getlvalue(a);
            op_push(OCnewptr, (long) ep);
            compilelvalue(a);
            op_push(OCpushptr, 0);
            nbpointers++;
            break;
          }
        case 'I':
        case 'E':
          {
            struct codepos pos;
            long a=arg[j++];
            int type=c=='I'?Gvoid:Ggen;
            getcodepos(&pos);
            if (tree[a].f==Fnoarg)
              compilecast(a,Gvoid,type);
            else
              compilenode(a,type);
            op_push(OCpushgen, data_push(getclosure(&pos)));
            break;
          }
        case 'V':
        case 'S':
          {
            entree *ep = getentry(arg[j++]);
            op_push(OCpushlong, (long)ep);
            break;
          }
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
              compilenode(a,Ggen);
              op_push(OCtostr, 1);
            }
            break;
          }
        case 's':
          {
            GEN g = cattovec(arg[j++], OPcat);
            long l, nb = lg(g)-1;
            for(l=1; l<=nb; l++)
              compilenode(g[l], Ggen);
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
        case 'V':
        case 'r':
        case 'E':
        case 'I':
          op_push(OCpushlong,0);
          break;
        case 'n':
          op_push(OCpushlong,-1);
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
        case 'V':
          {
            long x=tree[arg[j]].x;
            long y=tree[arg[j]].y;
            entree *ep;
            if (tree[arg[j]].f!=Faffect)
              pari_err(talker2,"expected character: '=' instead of",
                  tree[n].str+tree[n].len, get_origin());
            ep = getentry(x);
            op_push(OCpushlong, (long)ep);
            compilenode(y,Ggen);
            i++; j++;
          }
          break;
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
                compilenode(mael(g,k,l),Ggen);
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

static void
compilenode(long n, int mode)
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
      compilenode(x,Gvoid);
    compilenode(y,mode);
    return;
  case Ffacteurmat:
    compilefacteurmat(n,mode);
    break;
  case Faffect:
    {
      struct node_loc l;
      l.start=tree[n].str;
      l.end=tree[n].str+tree[n].len;
      compilefunc(newopcall(OPstore,x,y,&l),mode);
    }
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
        op_push(OCpushvar, (long)fetch_entry(tree[n].str+1,tree[n].len-1));
        compilecast(n,Ggen, mode);
        break;
      default:
        pari_err(bugparier,"compilenode, unsupported constant");
      }
      avma=ltop;
      return;
    }
  case Fsmall:
    if (mode==Ggen)
      op_push(OCpushstoi, x);
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
      if (!EpSTATIC(ep))
      {
        op_push(OCpushvalue,(long)ep);
        compilecast(n,Ggen,mode);
        break;
      }
    }
  case Fderfunc: /*Fall through*/
  case Ffunction:
    compilefunc(n, mode);
    return;
  case Fdeffunc:
    {
      pari_sp ltop=avma;
      struct codepos pos;
      long i;
      GEN arg2=listtogen(tree[x].y,Flistarg);
      entree *ep=getfunc(x);
      long loc=y;
      long nbvar;
      GEN lvar;
      long arity=lg(arg2)-1;
      if (loc>=0)
        while (tree[loc].f==Fseq) loc=tree[loc].x;
      if (ep->valence!=EpNEW && ep->valence!=EpUSER)
      {
        if (ep->valence==EpVAR || ep->valence==EpGVAR)
          pari_err(talker2,"this is a variable",
              tree[n].str,get_origin());
        else
          pari_err(talker2,"cannot redefine GP functions",
              tree[n].str,get_origin());
      }
      getcodepos(&pos);
      for (i=1;i<=arity;i++)
      {
        long a = arg2[lg(arg2)-i];
        long en;
        switch (tree[a].f)
        {
        case Ftag:
          a=tree[a].x;
        case Fentry: /*Fall through*/
          en=(long)getentry(a);
          op_push(OCgetarg,en);
          var_push(en);
          break;
        case Faffect:
          { 
            struct codepos lpos;
            getcodepos(&lpos);
            compilenode(tree[a].y,Ggen);
            a=tree[a].x;
            if (tree[a].f==Ftag)
              a=tree[a].x;
            op_push(OCpushgen, data_push(getclosure(&lpos)));
            en=(long)getentry(a);
            op_push(OCdefaultarg,en);
            var_push(en);
            break;
          }
        default: 
          pari_err(talker2,"invalid function definition",
              tree[a].str,get_origin());
        }
      }
      if (y>=0 && tree[y].f!=Fnoarg) compilenode(y,Ggen);
      else compilecast(n,Gvoid,Ggen);
      nbvar=s_lvar.n-pos.localvars;
      s_lvar.n=pos.localvars;
      lvar=cgetg(nbvar+1,t_VECSMALL);
      for(i=1;i<=nbvar;i++)
        lvar[i]=localvars[pos.localvars+i-1];
      if (nbvar > 1)
      { /* check for duplicates */
        GEN x = vecsmall_copy(lvar);
        long k;
        vecsmall_sort(x);
        for (k=x[1],i=2; i<lg(x); k=x[i],i++)
          if (x[i] == k)
            pari_err(talker,"user function %s: variable %s declared twice",
                ep->name, ((entree*)x[i])->name);
      }
      op_push(OCpushgen, data_push(getclosure(&pos)));
      op_push(OCpushgen, data_push(lvar));
      op_push(OCpushgen, data_push(
            strntoGENstr(tree[n].str,tree[n].len)));
      op_push(OCpushlong, arity);
      op_push(OCdeffunc, (long) ep);
      compilecast(n,Gvoid,mode);
      avma=ltop;
      break;
    }
  case Ftag:
    compilenode(x, mode);
    return;
  case Fnoarg:
    return;
  default:
    pari_err(bugparier,"compilenode");
  }
}

GEN
gp_closure(long n)
{
  struct codepos pos={0,0,0,-1};
  compilenode(n,Ggen);
  return getclosure(&pos); 
}

