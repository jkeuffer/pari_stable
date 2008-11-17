/*
Copyright (C) 2006-2008  The PARI group.

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
#include "parse.h"
#include "anal.h"
#include "tree.h"

static THREAD int pari_once;
static THREAD const char *pari_lex_start, *pari_unused_chars;
static THREAD GEN pari_lasterror;

static void pari_error(YYLTYPE *yylloc, char **lex, const char *s)
{
  if (pari_lasterror) cgiv(pari_lasterror);
  pari_lasterror=strtoGENstr(s);
}

static THREAD pari_stack s_node;
THREAD node *pari_tree;

void
pari_init_parser(void)
{
  pari_sp ltop=avma;
  long i;
  const char *opname[]={"_||_", "_&&_", "_==_", "_!=_", "_>=_", "_>_", "_<=_", "_<_", "_-_","_+_","_<<_", "_>>_", "_%_", "_\\/_", "_\\_", "_/_", "_*_","_^_","__","_=_","_--","_++","_-=_", "_+=_", "_<<=_", "_>>=_", "_%=_", "_\\/=_", "_\\=_", "_/=_", "_*=_","+_","-_","!_","_!","_'","_~","%","#_","",""};

  stack_init(&s_node,sizeof(*pari_tree),(void **)&pari_tree);
  stack_alloc(&s_node,OPnboperator);
  s_node.n=OPnboperator;
  for (i=0;i<OPnboperator;i++)
  {
    pari_tree[i].f    = Fconst;
    pari_tree[i].x    = CSTentry;
    pari_tree[i].y    = -1;
    pari_tree[i].str  = opname[i];
    pari_tree[i].len  = strlen(opname[i]);
    pari_tree[i].flags= 0;
  }
  avma=ltop;
}
void
pari_close_parser(void) { stack_delete(&s_node); }

static void
unused_chars(const char *lex, int strict)
{
  long n = 2 * term_width() - (17+19+1); /* Warning + unused... + . */
  if (strict) compile_err("unused characters", lex);
  if ((long)strlen(lex) > n) /* at most 2 lines */
    pari_warn(warner, "unused characters: %.*s[+++]", n-5, lex);
  else
    pari_warn(warner, "unused characters: %s", lex);
}

void
compile_err(const char *msg, const char *str)
{
  pari_err(talker2, msg, str, pari_lex_start);
}

void
compile_varerr(const char *str)
{
  pari_err(talker2, "variable name expected", str, pari_lex_start);
}

void
parser_reset(void)
{
  s_node.n = OPnboperator;
}

GEN
pari_compile_str(char *lex, int strict)
{
  pari_sp ltop=avma;
  GEN code;
  pari_lex_start = lex;
  pari_unused_chars=NULL;
  pari_once=1;
  pari_lasterror=NULL;
  if (pari_parse(&lex))
  {
    if (pari_unused_chars)
      unused_chars(pari_unused_chars,strict);
    else
      compile_err(GSTR(pari_lasterror),lex-1);
  }
  avma=ltop;
  optimizenode(s_node.n-1);
  code=gp_closure(s_node.n-1);
  parser_reset();
  return code;
}

GEN
pari_eval_str(char *lex, int strict)
{
  GEN code=pari_compile_str(lex, strict);
  return closure_evalres(code);
}

static long
newnode(Ffunc f, long x, long y, struct node_loc *loc)
{
  long n=stack_new(&s_node);
  pari_tree[n].f=f;
  pari_tree[n].x=x;
  pari_tree[n].y=y;
  pari_tree[n].str=loc->start;
  pari_tree[n].len=loc->end-loc->start;
  pari_tree[n].flags=0;
  return n;
}

static long
newconst(long x, struct node_loc *loc)
{
  return newnode(Fconst,x,-1,loc);
}

static long
newopcall(OPerator op, long x, long y, struct node_loc *loc)
{
  if (y==-1)
    return newnode(Ffunction,op,x,loc);
  else
    return newnode(Ffunction,op,newnode(Flistarg,x,y,loc),loc);
}

static long
newintnode(struct node_loc *loc)
{
  if (loc->end-loc->start<=(long)(1+LOG10_2*BITS_IN_LONG));
  {
    pari_sp ltop=avma;
    GEN g=strtoi(loc->start);
    long s;
    avma=ltop;
    if (signe(g)==0)      return newnode(Fsmall,0,-1,loc);
    if ((s=itos_or_0(g))) return newnode(Fsmall,s,-1,loc);
  }
  return newconst(CSTint,loc);
}

static long
newfunc(CSTtype t, struct node_loc *func, long args, long code,
                   struct node_loc *loc)
{
  long name=newnode(Fentry,newconst(t,func),-1,func);
  return newnode(Faffect,name,newnode(Flambda,args,code,loc),loc);
}


