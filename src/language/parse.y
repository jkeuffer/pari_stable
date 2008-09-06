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

#define YYSIZE_T size_t
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

static void pari_error(YYLTYPE *yylloc, char **lex, const char *s)
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
compile_varer1(const char *str)
{
  pari_err(varer1, str, pari_lex_start);
}

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
      unused_chars(pari_unused_chars,strict);
    else
      compile_err(GSTR(pari_lasterror),lex-1);
  }
  avma=ltop;
  code=gp_closure(s_node.n-1);
  parser_reset();
  compiler_reset();
  reset_break();
  gp_function_name=NULL;
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

%}
%name-prefix="pari_"
%pure-parser
%parse-param {char **lex}
%lex-param {char **lex}
%token KPARROW ")->"
%token KARROW "->"
%token KPE   "+="
%token KSE   "-="
%token KME   "*="
%token KDE   "/="
%token KDRE  "\\/="
%token KEUCE "\\="
%token KMODE "%="
%token KAND  "&&"
%token KOR   "||"
%token KEQ   "=="
%token KNE   "!="
%token KGE   ">="
%token KLE   "<="
%token KSRE  ">>="
%token KSLE  "<<="
%token KSR   ">>"
%token KSL   "<<"
%token KDR   "\\/"
%token KPP   "++"
%token KSS   "--"
%token <gen> KINTEGER "integer"
%token <gen> KREAL "real number"
%token KENTRY "variable name"
%token KSTRING "character string"
%left SEQ DEFFUNC
%left INT LVAL
%right ")->" "->"
%left ';' ','
%right '=' "+=" "-=" "*=" "/=" "\\/=" "\\=" "%=" ">>=" "<<="
%left '&' "&&" '|' "||"
%left "==" "!=" '>' ">=" '<' "<="
%left '+' '-'
%left '%' "\\/" '\\' '/' '*' ">>" "<<"
%left SIGN
%right '^'
%left '#'
%left '!' '~' '[' '\''
%left '.' MAT
%left "++" "--"
%left '('
%left ':'
%type <val> seq sequnused matrix matrix_index expr
%type <val> lvalue
%type <val> matrixelts matrixlines arg listarg definition
%type <val> funcid memberid
%type <val> backticks history
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

history: '%'           {$$=newopcall(OPhist,-1,-1,&@$);}
       | '%' KINTEGER  {$$=newopcall(OPhist,newintnode(&@2),-1,&@$);}
       | '%' backticks {$$=newopcall(OPhist,newnode(Fsmall,-$2,-1,&@$),-1,&@$);}
;

expr: KINTEGER %prec INT  {$$=newintnode(&@1);}
    | KREAL               {$$=newconst(CSTreal,&@$);}
    | '.'                 {$$=newconst(CSTreal,&@$);}
    | KINTEGER '.' KENTRY {$$=newnode(Ffunction,newconst(CSTmember,&@3),
						newintnode(&@1),&@$);}
    | KSTRING       {$$=newconst(CSTstr,&@$);}
    | '\'' KENTRY   {$$=newconst(CSTquote,&@$);}
    | history           {$$=$1;}
    | expr '(' listarg ')'  {$$=newnode(Fcall,$1,$3,&@$);}
    | funcid            {$$=$1;}
    | lvalue %prec LVAL	{$$=$1;}
    | matrix            {$$=$1;}
    | definition        {$$=$1;}
    | lvalue '=' expr {$$=newnode(Faffect,$1,$3,&@$);}
    | lvalue "++" {$$=newopcall(OPpp,$1,-1,&@$);}
    | lvalue "--" {$$=newopcall(OPss,$1,-1,&@$);}
    | lvalue "*="   expr {$$=newopcall(OPme,$1,$3,&@$);}
    | lvalue "/="   expr {$$=newopcall(OPde,$1,$3,&@$);}
    | lvalue "\\/=" expr {$$=newopcall(OPdre,$1,$3,&@$);}
    | lvalue "\\="  expr {$$=newopcall(OPeuce,$1,$3,&@$);}
    | lvalue "%="   expr {$$=newopcall(OPmode,$1,$3,&@$);}
    | lvalue "<<="  expr {$$=newopcall(OPsle,$1,$3,&@$);}
    | lvalue ">>="  expr {$$=newopcall(OPsre,$1,$3,&@$);}
    | lvalue "+="   expr {$$=newopcall(OPpe,$1,$3,&@$);}
    | lvalue "-="   expr {$$=newopcall(OPse,$1,$3,&@$);}
    | '!' expr 	       {$$=newopcall(OPnb,$2,-1,&@$);}
    | '#' expr 	       {$$=newopcall(OPlength,$2,-1,&@$);}
    | expr "||"  expr  {$$=newopcall(OPor,$1,$3,&@$);}
    | expr '|'   expr  {$$=newopcall(OPor,$1,$3,&@$);}
    | expr "&&"  expr  {$$=newopcall(OPand,$1,$3,&@$);}
    | expr '&'   expr  {$$=newopcall(OPand,$1,$3,&@$);}
    | expr "=="  expr  {$$=newopcall(OPeq,$1,$3,&@$);}
    | expr "!="  expr  {$$=newopcall(OPne,$1,$3,&@$);}
    | expr ">="  expr  {$$=newopcall(OPge,$1,$3,&@$);}
    | expr '>'   expr  {$$=newopcall(OPg,$1,$3,&@$);}
    | expr "<="  expr  {$$=newopcall(OPle,$1,$3,&@$);}
    | expr '<'   expr  {$$=newopcall(OPl,$1,$3,&@$);}
    | expr '-'   expr  {$$=newopcall(OPs,$1,$3,&@$);}
    | expr '+'   expr  {$$=newopcall(OPp,$1,$3,&@$);}
    | expr "<<"  expr  {$$=newopcall(OPsl,$1,$3,&@$);}
    | expr ">>"  expr  {$$=newopcall(OPsr,$1,$3,&@$);}
    | expr '%'   expr  {$$=newopcall(OPmod,$1,$3,&@$);}
    | expr "\\/" expr  {$$=newopcall(OPdr,$1,$3,&@$);}
    | expr '\\'  expr  {$$=newopcall(OPeuc,$1,$3,&@$);}
    | expr '/'   expr  {$$=newopcall(OPd,$1,$3,&@$);}
    | expr '*'   expr  {$$=newopcall(OPm,$1,$3,&@$);}
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

lvalue: KENTRY %prec LVAL   {$$=newnode(Fentry,newconst(CSTentry,&@1),-1,&@$);}
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

memberid:
     expr '.' KENTRY {$$=newnode(Ffunction,newconst(CSTmember,&@3),$1,&@$);}
;

definition: KENTRY '(' listarg ')' '=' seq %prec DEFFUNC
                                   {$$=newfunc(CSTentry,&@1,$3,$6,&@$);}
          | expr '.' KENTRY '=' seq %prec DEFFUNC
                                   {$$=newfunc(CSTmember,&@3,$1,$5,&@$);}
          | lvalue "->" seq              {$$=newnode(Flambda, $1,$3,&@$);}
          | '(' listarg ")->" seq        {$$=newnode(Flambda, $2,$4,&@$);}
;

%%
