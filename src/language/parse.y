%{
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

#define YYERROR_VERBOSE 1
#define YYSTYPE union token_value
#define YYLTYPE struct node_loc
#define YYLLOC_DEFAULT(Current, Rhs, N)     \
	((Current).start  = ((N)?(Rhs)[1].start:(Rhs)[0].end),  \
	 (Current).end    = (Rhs)[N].end)
#include "pari.h"
#include "paripriv.h"
#include "parse.h"
#include "anal.h"
#include "tree.h"

static THREAD int pari_once;
static THREAD const char *pari_lex_start, *pari_unused_chars;
static THREAD GEN pari_lasterror;

static void pari_error(YYLTYPE *yylloc, char **lex, char *s)
{
  if (pari_lasterror) cgiv(pari_lasterror);
  pari_lasterror=strtoGENstr(s);
}

static THREAD gp2c_stack s_node;
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
  }
  avma=ltop;
}

static void
unused_chars(const char *lex, const char *c, int strict)
{
  pari_sp ltop=avma;
  long n = 2 * term_width() - (17+19+1); /* Warning + unused... + . */
  char *s;
  if (strict) pari_err(talker2,"unused characters", lex, c);
  if ((long)strlen(lex) > n)
  {
    s = stackmalloc(n + 1);
    n -= 5;
    (void)strncpy(s,lex, n);
    strcpy(s + n, "[+++]");
  }
  else
    s = (char *)lex;
  pari_warn(warner, "unused characters: %s", s);
  ltop=avma;
}

const char*
get_origin(void) { return pari_lex_start; }

void
parser_reset(void)
{
  s_node.n = OPnboperator;
}

/* check syntax, then execute */

GEN
pari_eval_str(char *lex, int strict)
{
  pari_sp ltop=avma;
  GEN code, res;
  pari_lex_start = lex;
  pari_unused_chars=NULL;
  pari_once=1;
  pari_lasterror=NULL;
  if (pari_parse(&lex))
  {
    if (pari_unused_chars)
      unused_chars(pari_unused_chars,pari_lex_start,strict);
    else
      pari_err(talker2,GSTR(pari_lasterror),lex-1,pari_lex_start);
  }
  avma=ltop;
  code=gp_closure(s_node.n-1);
  parser_reset();
  compiler_reset();
  reset_break();
  res=closure_evalres(code);
  if (!res) return gnil;
  return res;
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
  return n;
}

static long
newconst(long x, struct node_loc *loc)
{
  return newnode(Fconst,x,-1,loc);
}

long
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
  if (loc->end-loc->start<=(long)(1+L2SL10*BITS_IN_LONG));
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

%}
%name-prefix="pari_"
%pure-parser
%parse-param {char **lex}
%lex-param {char **lex}
%token <gen> KINTEGER KREAL
%token KENTRY KSTRING
%left SEQ DEFFUNC
%left KDER
%left INT LVAL
%left ';' ','
%right '=' KPE KSE KME KDE KDRE KEUCE KMODE KSRE KSLE
%left '&' KAND '|' KOR
%left KEQ KNE KGE '<' KLE '>'
%left '+' '-'
%left KSR KSL
%left '%' KDR '\\' '/' '*'
%left SIGN
%right '^'
%left '#'
%left '!' '~' '[' '\''
%left '.' MAT
%token KPP KSS
%left ':'
%type <val> seq sequnused matrix matrix_index expr
%type <val> lvalue
%type <val> matrixelts matrixlines arg listarg definition
%type <val> funcid funcder memberid
%type <val> backticks
%%

sequnused: seq       {$$=$1;}
	 | seq error {$$=$1; pari_unused_chars=@1.end;YYABORT;}

seq: /**/ %prec SEQ  { if(*lex<=pari_lex_start+2)
			 @$.start=@$.end=pari_lex_start;
		       $$=newnode(Fnoarg,-1,-1,&@$);}
   | expr %prec SEQ  {$$=$1;}
   | seq ';'         {$$=$1;}
   | seq ';' expr    {$$=newnode(Fseq,$1,$3,&@$);}
;

matrix_index: '[' expr ',' expr ']' {$$=newnode(Fmatrix,$2,$4,&@$);}
	    | '[' expr ']'          {$$=newnode(Fmatrix,$2,-1,&@$);}
	    | '[' expr ',' ']'      {$$=newnode(FmatrixL,$2,-1,&@$);}
	    | '[' ',' expr ']'      {$$=newnode(FmatrixR,$3,-1,&@$);}
;

backticks: '`' {$$=1;}
	 | backticks '`' {$$=$1+1;}
;

expr: KINTEGER %prec INT  {$$=newintnode(&@1);}
    | KREAL               {$$=newconst(CSTreal,&@$);}
    | '.'                 {$$=newconst(CSTreal,&@$);}
    | KINTEGER '.' KENTRY {$$=newnode(Ffunction,newconst(CSTmember,&@3),
						newintnode(&@1),&@$);}
    | KSTRING       {$$=newconst(CSTstr,&@$);}
    | '\'' KENTRY   {$$=newconst(CSTquote,&@$);}
    | '%'           {$$=newopcall(OPhist,-1,-1,&@$);}
    | '%' KINTEGER  {$$=newopcall(OPhist,newintnode(&@2),-1,&@$);}
    | '%' backticks {$$=newopcall(OPhist,newnode(Fsmall,-$2,-1,&@$),-1,&@$);}
    | funcid            {$$=$1;}
    | funcder           {$$=$1;}
    | lvalue %prec LVAL	{$$=$1;}
    | matrix            {$$=$1;}
    | definition        {$$=$1;}
    | lvalue '=' expr {$$=newnode(Faffect,$1,$3,&@$);}
    | lvalue KPP {$$=newopcall(OPpp,$1,-1,&@$);}
    | lvalue KSS {$$=newopcall(OPss,$1,-1,&@$);}
    | lvalue KME expr {$$=newopcall(OPme,$1,$3,&@$);}
    | lvalue KDE expr {$$=newopcall(OPde,$1,$3,&@$);}
    | lvalue KDRE expr {$$=newopcall(OPdre,$1,$3,&@$);}
    | lvalue KEUCE expr {$$=newopcall(OPeuce,$1,$3,&@$);}
    | lvalue KMODE expr {$$=newopcall(OPmode,$1,$3,&@$);}
    | lvalue KSLE expr {$$=newopcall(OPsle,$1,$3,&@$);}
    | lvalue KSRE expr {$$=newopcall(OPsre,$1,$3,&@$);}
    | lvalue KPE expr {$$=newopcall(OPpe,$1,$3,&@$);}
    | lvalue KSE expr {$$=newopcall(OPse,$1,$3,&@$);}
    | '!' expr 	      {$$=newopcall(OPnb,$2,-1,&@$);}
    | '#' expr 	      {$$=newopcall(OPlength,$2,-1,&@$);}
    | expr KOR  expr  {$$=newopcall(OPor,$1,$3,&@$);}
    | expr '|'  expr  {$$=newopcall(OPor,$1,$3,&@$);}
    | expr KAND expr  {$$=newopcall(OPand,$1,$3,&@$);}
    | expr '&'  expr  {$$=newopcall(OPand,$1,$3,&@$);}
    | expr KEQ  expr  {$$=newopcall(OPeq,$1,$3,&@$);}
    | expr KNE  expr  {$$=newopcall(OPne,$1,$3,&@$);}
    | expr KGE  expr  {$$=newopcall(OPge,$1,$3,&@$);}
    | expr '>'  expr  {$$=newopcall(OPg,$1,$3,&@$);}
    | expr KLE  expr  {$$=newopcall(OPle,$1,$3,&@$);}
    | expr '<'  expr  {$$=newopcall(OPl,$1,$3,&@$);}
    | expr '-'  expr  {$$=newopcall(OPs,$1,$3,&@$);}
    | expr '+'  expr  {$$=newopcall(OPp,$1,$3,&@$);}
    | expr KSL  expr  {$$=newopcall(OPsl,$1,$3,&@$);}
    | expr KSR  expr  {$$=newopcall(OPsr,$1,$3,&@$);}
    | expr '%'  expr  {$$=newopcall(OPmod,$1,$3,&@$);}
    | expr KDR  expr  {$$=newopcall(OPdr,$1,$3,&@$);}
    | expr '\\' expr  {$$=newopcall(OPeuc,$1,$3,&@$);}
    | expr '/'  expr  {$$=newopcall(OPd,$1,$3,&@$);}
    | expr '*'  expr  {$$=newopcall(OPm,$1,$3,&@$);}
  /*| '+' expr %prec SIGN {$$=newopcall(OPpl,$2,-1);}*/
    | '+' expr %prec SIGN {$$=$2;}
    | '-' expr %prec SIGN {$$=newopcall(OPn,$2,-1,&@$);}
    | expr '^' expr {$$=newopcall(OPpow,$1,$3,&@$);}
    | expr '~' {$$=newopcall(OPtrans,$1,-1,&@$);}
    | expr '\'' {$$=newopcall(OPderiv,$1,-1,&@$);}
    | expr '!'  {$$=newopcall(OPfact,$1,-1,&@$);}
    | expr matrix_index %prec MAT {$$=newnode(Ffacteurmat,$1,$2,&@$);}
    | memberid {$$=$1;}
    | expr ':' KENTRY   {$$=newnode(Ftag,$1,0,&@$);}
    | '(' expr ')' {$$=$2;}
;

lvalue: KENTRY              {$$=newnode(Fentry,newconst(CSTentry,&@1),-1,&@$);}
      | lvalue matrix_index {$$=newnode(Ffacteurmat,$1,$2,&@$);}
      | lvalue ':' KENTRY   {$$=newnode(Ftag,$1,newconst(CSTentry,&@2),&@$);}
;

matrixelts: expr {$$=$1;}
	  | matrixelts ',' expr {$$=newnode(Fmatrixelts,$1,$3,&@$);}
;

matrixlines: matrixelts  ';' matrixelts {$$=newnode(Fmatrixlines,$1,$3,&@$);}
	   | matrixlines ';' matrixelts {$$=newnode(Fmatrixlines,$1,$3,&@$);}
;

matrix: '[' ']'             {$$=newnode(Fvec,-1,-1,&@$);}
      | '[' ';' ']'         {$$=newnode(Fmat,-1,-1,&@$);}
      | '[' matrixelts ']'  {$$=newnode(Fvec,$2,-1,&@$);}
      | '[' matrixlines ']' {$$=newnode(Fmat,$2,-1,&@$);}
;

arg: seq        {$$=$1;}
   | '&' lvalue {$$=newnode(Frefarg,$2,-1,&@$);}
   | arg error  {if (!pari_once) { yyerrok; } pari_once=1;}  expr
		     {pari_once=0; $$=newopcall(OPcat,$1,$4,&@$);}
;

listarg: arg {$$=$1;}
       | listarg ',' arg {$$=newnode(Flistarg,$1,$3,&@$);}
;

funcid: KENTRY '(' listarg ')' {$$=newnode(Ffunction,newconst(CSTentry,&@1),$3,&@$);}
;

funcder: KENTRY KDER listarg ')' {$$=newnode(Fderfunc,newconst(CSTentry,&@1),$3,&@$);}
;

memberid:
     expr '.' KENTRY {$$=newnode(Ffunction,newconst(CSTmember,&@3),$1,&@$);}
;

definition: funcid   '=' seq %prec DEFFUNC {$$=newnode(Fdeffunc,$1,$3,&@$);}
	  | memberid '=' seq %prec DEFFUNC {$$=newnode(Fdeffunc,$1,$3,&@$);}
;

%%
