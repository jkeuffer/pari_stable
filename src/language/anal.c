/* $Id$

Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

/*******************************************************************/
/*                                                                 */
/*                  SYNTACTICAL ANALYZER FOR GP                    */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "anal.h"
#include "parinf.h"

/* slightly more efficient than is_keyword_char. Not worth a static array. */
#define is_key(c) (isalnum((int)(c)) || (c)=='_')

#define separe(c) ((c)==';' || (c)==':')
typedef GEN (*PFGEN)(ANYARG);
typedef GEN (*F2GEN)(GEN,GEN);
typedef GEN (*F1GEN)(GEN);

static GEN    constante();
static GEN    expr();
static GEN    facteur();
static GEN    identifier();
static GEN    read_member(GEN x);
static GEN    seq();
static GEN    truc();
static long   number(long *nb);
static void   doskipseq(char *s, int strict);
static void   skip_matrix_block();
static void   skipconstante();
static void   skipexpr();
static void   skipfacteur();
static void   skipidentifier();
static void   skipseq();
static void   skipstring();
static void   skiptruc();
static GEN    strtoGENstr_t();
static entree *entry();
static entree *installep(void *f,char *name,int l,int v,int add,entree **table);
static entree *skipentry(void);

extern void killbloc0(GEN x, int inspect);
extern void err_leave_default(long n);
extern int term_width(void);
extern GEN addsmulsi(long a, long b, GEN Y);

/* last time we began parsing an object of specified type */
static struct
{
  char *identifier, *symbol, *raw, *member, *start;
} mark;

/* when skipidentifier() detects that user function f() is being redefined,
 * (f()= ... ) this is set pointing to the opening parenthesis. Checked in
 * identifier(). Otherwise definition like f(x=1)= would change the value of
 * global variable x
 */
static char *redefine_fun = NULL;

/* points to the part of the string that remains to be parsed */
static char *analyseur = NULL;

/* when non-0, we are checking the syntax of a new function body */
static long skipping_fun_def;

/* when non-NULL, points to the entree of a new user function (currently
 * being checked). Used by the compatibility engine in the following way:
 *   when user types in a function whose name has changed, it is understood
 *   as EpNEW; first syntax error (missing = after function definition
 *   usually) triggers err_new_fun() if check_new_fun is set.
 */
static entree *check_new_fun;

/* for control statements (check_break) */
static long br_status, br_count;
static GEN br_res = NULL;

/*  Special characters:
 *     ' ', '\t', '\n', '\\' are forbidden internally (suppressed by filtre).
 *     { } are forbidden everywhere and will be used to denote optional
 *     lexemes in the sequel.
 *
 *  Definitions: The sequence
 *    { a }* means any number (possibly 0) of object a.
 *
 *  seq: only this one can be empty.
 *    expr { [:;] expr }* { [:;] }
 *
 *  expr:
 *     expression = sequence of "facteurs" separated by binary operators
 *     whose priority are:
 *      1: *, /, \, \/, %, >>, <<                (highest)
 *      2: +, -
 *      3: <, <=, >, >=, !=, ==, <>
 *      4: &, &&, |, ||                  (lowest)
 *     read from left to right.
 *
 *  facteur:
 *    { [+-] } followed by a "truc", then by any succession of the
 *  following:
 *
 *        ~, ', !
 *  or    ^ facteur
 *  or    matrix_index { matrix_index }*
 *  or    .entry
 *
 *  truc:
 *      ! facteur
 *  or  # facteur
 *  or  ' entry
 *  or  identifier
 *  or  constante
 *  or  string {string}*
 *  or  matrix
 *  or  ( expr )
 *  or  % { ` }*  or %number
 *
 *  identifier:
 *    entry  followed by optional
 *
 *      matrix_assignment_block
 *  or  .entry { = seq }
 *  or  {'} ( arg_list )
 *  or  ( arg_list ) = seq
 *
 *  arg_list
 *    { arg } { , arg }*
 *
 *  arg:
 *    expr  or  &entry
 *    Note: &entry (pointer) not yet implemented for user functions
 *
 *  matrix
 *      [ A { ; A}* ] where A = { expr } { , { expr } }*
 *      All A must share the same length.
 *
 *  matrix_index:
 *      [ expr {,} ]
 *   or [ { expr } , expr ]
 *
 *  matrix_assignment_block:
 *     { matrix_index }  followed by
 *        = expr
 *     or ++  or --
 *     or op= expr  where op is one of the operators in expr 1: and 2:
 *
 *  entry:
 *      [A-Za-z][A-Za-z0-9_]*
 *
 *  string:
 *      " any succession of characters [^\]"
 *
 *  constante:
 *      number { . [0-9]* }  { expo }
 *   or .{number} { expo }
 *
 *  expo:
 *      [eE] {[+-]} { number }
 *
 *  number:
 *      [0-9]+
 */
char*
_analyseur(void)
{
  return analyseur;
}

void
_set_analyseur(char *s)
{
  analyseur = s;
}

/* Do not modify (analyseur,mark.start) */
static GEN
lisseq0(char *t, GEN (*f)(void))
{
  const gpmem_t av = avma;
  char *olds = analyseur, *olde = mark.start;
  GEN res;

  if (foreignExprHandler && *t == foreignExprSwitch)
    return (*foreignExprHandler)(t);

  redefine_fun = NULL;
  check_new_fun = NULL;
  skipping_fun_def = 0;
  mark.start = analyseur = t;

  br_status = br_NONE;
  if (br_res) { killbloc(br_res); br_res = NULL; }
  res = f();
  analyseur = olds; mark.start = olde;
  if (br_status != br_NONE)
  {
    if (!br_res) { avma = av; return gnil; }
    return gerepilecopy(av, br_res);
  }
  if (res == NULL) { avma = av; return polx[fetch_user_var("NULL")]; }
  /* ep->value, beware: it may be killed anytime.  */
  if (isclone(res)) { avma = av; return forcecopy(res); }
  return gerepileupto(av, res);
}

/* filtered lisexpr = remove blanks and comments */
static GEN
flisseq0(char *s, GEN (*f)(void))
{
  char *t = filtre(s, (compatible == OLDALL));
  GEN x = lisseq0(t, f);
  free(t); return x;
}

GEN lisseq(char *t)  { return lisseq0(t, seq);  }
GEN lisexpr(char *t) { return lisseq0(t, expr); }
GEN flisseq(char *s) { return flisseq0(s, seq); }
GEN flisexpr(char *s){ return flisseq0(s, expr);}

/* check syntax, then execute */
GEN
readseq(char *c, int strict)
{
  check_new_fun=NULL; skipping_fun_def=0;
  doskipseq(c, strict); return lisseq(c);
}

entree *
install(void *f, char *name, char *code)
{
  long hash;
  entree *ep = is_entry_intern(name, functions_hash, &hash);

  if (ep) err(warner,"[install] '%s' already there. Not replaced", name);
  else
  {
    char *s = name;
    if (isalpha((int)*s))
      while (is_keyword_char(*++s)) /* empty */;
    if (*s) err(talker2,"not a valid identifier", s, name);
    ep = installep(f, name, strlen(name), EpINSTALL, 0, functions_hash + hash);
    ep->code = pari_strdup(code);
  }
  return ep;
}

static void
free_args(gp_args *f)
{
  long i;
  GEN *y = f->arg;
  for (i = f->narg + f->nloc - 1; i>=0; i--)
    if (isclone(y[i])) gunclone(y[i]);
}

void
freeep(entree *ep)
{
  if (foreignFuncFree && ep->code && (*ep->code == 'x'))
    (*foreignFuncFree)(ep); /* function created by foreign interpreter */

  if (EpSTATIC(ep)) return; /* gp function loaded at init time */
  if (ep->help) free(ep->help);
  if (ep->code) free(ep->code);
  if (ep->args)
  {
    switch(EpVALENCE(ep))
    {
      case EpVAR: case EpGVAR: break;
      default: free_args((gp_args*)ep->args);
    }
    free((void*)ep->args);
  }
  free(ep);
}

/*******************************************************************/
/*                                                                 */
/*                            VARIABLES                            */
/*                                                                 */
/*******************************************************************/
/* As a rule, ep->value is a clone (COPY). push_val and pop_val are private
 * functions for use in sumiter: we want a temporary ep->value, which is NOT
 * a clone (PUSH), to avoid unnecessary copies. */

/* ep->args is the stack of old values (INITIAL if initial value, from
 * installep) */
typedef struct var_cell {
  struct var_cell *prev; /* cell associated to previous value on stack */
  GEN value; /* last value (not including current one, in ep->value) */
  char flag; /* status of _current_ ep->value: PUSH or COPY ? */
} var_cell;
#define INITIAL NULL
#define PUSH_VAL 0
#define COPY_VAL 1
#define copyvalue(v,x) new_val_cell(get_ep(v), x, COPY_VAL)
#define pushvalue(v,x) new_val_cell(get_ep(v), x, PUSH_VAL)
#define killvalue(v) pop_val(get_ep(v))

/* Push x on value stack associated to ep. Assume EpVALENCE(ep)=EpVAR/EpGVAR */
static void
new_val_cell(entree *ep, GEN x, char flag)
{
  var_cell *v = (var_cell*) gpmalloc(sizeof(var_cell));
  v->value  = (GEN)ep->value;
  v->prev   = (var_cell*) ep->args;
  v->flag   = flag;

  ep->args  = (void*) v;
  ep->value = (flag == COPY_VAL)? gclone(x): x;
}

void
push_val(entree *ep, GEN a) { new_val_cell(ep,a,PUSH_VAL); }

/* kill ep->value and replace by preceding one, poped from value stack */
void
pop_val(entree *ep)
{
  var_cell *v = (var_cell*) ep->args;

  if (v == INITIAL) return;
  if (v->flag == COPY_VAL) killbloc((GEN)ep->value);
  ep->value = v->value;
  ep->args  = (void*) v->prev;
  free((void*)v);
}

/* as above IF ep->value was PUSHed, or was created after block number 'loc'
   return 0 if not deleted, 1 otherwise [for recover()] */
int
pop_val_if_newer(entree *ep, long loc)
{
  var_cell *v = (var_cell*) ep->args;

  if (v == INITIAL) return 0;
  if (v->flag == COPY_VAL)
  {
    GEN x = (GEN)ep->value;
    if (bl_num(x) < loc) return 0; /* older */
    killbloc((GEN)ep->value);
  }
  ep->value = v->value;
  ep->args  = (void*) v->prev;
  free((void*)v); return 1;
}

/* set new value of ep directly to val (COPY), do not save last value unless
 * it's INITIAL. */
void
changevalue(entree *ep, GEN x)
{
  var_cell *v = (var_cell*) ep->args;
  if (v == INITIAL) new_val_cell(ep,x, COPY_VAL);
  else
  {
    x = gclone(x); /* beware: killbloc may destroy old x */
    if (v->flag == COPY_VAL) killbloc((GEN)ep->value); else v->flag = COPY_VAL;
    ep->value = (void*)x;
  }
}

/* as above, but PUSH, notCOPY */
void
changevalue_p(entree *ep, GEN x)
{
  var_cell *v = (var_cell*) ep->args;
  if (v == INITIAL) new_val_cell(ep,x, PUSH_VAL);
  else
  {
    if (v->flag == COPY_VAL) { killbloc((GEN)ep->value); v->flag = PUSH_VAL; }
    ep->value = (void*)x;
  }
}

void
kill_from_hashlist(entree *ep)
{
  long hash = hashvalue(ep->name);
  entree *ep1;

  if (functions_hash[hash] == ep)
  {
    functions_hash[hash] = ep->next;
    freeep(ep); return;
  }
  for (ep1 = functions_hash[hash]; ep1; ep1 = ep1->next)
    if (ep1->next == ep)
    {
      ep1->next = ep->next;
      freeep(ep); return;
    }
}

static entree*
get_ep(long v)
{
  entree *ep = varentries[v];
  if (!ep) err(talker2,"this function uses a killed variable",
               mark.identifier, mark.start);
  return ep;
}

/* Kill entree ep, i.e free all memory it occupies, remove it from hashtable.
 * If it's a variable set a "black hole" in polx[v], etc. x = 0-th variable
 * can NOT be killed (only the value), because we often use explicitly polx[0]
 */
void
kill0(entree *ep)
{
  long v;

  if (EpSTATIC(ep))
    err(talker2,"can't kill that",mark.symbol,mark.start);
  switch(EpVALENCE(ep))
  {
    case EpVAR:
    case EpGVAR:
      v = varn(initial_value(ep)); killvalue(v);
      if (!v) return; /* never kill x */
      polx[v] = polun[v] = gnil;
      polvar[v+1] = (long)gnil;
      varentries[v] = NULL; break;
    case EpUSER:
      gunclone((GEN)ep->value); break;
  }
  kill_from_hashlist(ep);
}

/*******************************************************************/
/*                                                                 */
/*                              PARSER                             */
/*                                                                 */
/*******************************************************************/

static GEN
seq(void)
{
  const gpmem_t av = avma, lim = stack_lim(av,1);
  GEN res = gnil;

  for(;;)
  {
    while (separe(*analyseur)) analyseur++;
    if (!*analyseur || *analyseur == ')' || *analyseur == ',') return res;
    res = expr();
    if (br_status || !separe(*analyseur)) return res;

    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"seq");
      if (is_universal_constant(res)) avma = av;
      else
	res = gerepilecopy(av, res);
    }
  }
}

static GEN
gshift_l(GEN x, GEN n)  { return gshift(x, itos(n)); }

static GEN
gshift_r(GEN x, GEN n) { return gshift(x,-itos(n)); }

#define UNDEF (GEN)0x1
static GEN
expr(void)
{
  gpmem_t av = avma, lim = stack_lim(av, 2);
  GEN aux,e,e1,e2,e3;
  F2GEN F1,F2,F3;
  int F0 = 0;

  F1 = F2 = F3 = (F2GEN)NULL;
  e1 = e2 = e3 = UNDEF;
L3:
  aux = facteur();
  if (br_status) return NULL;
  e3 = F3? F3(e3,aux): aux;
  switch(*analyseur)
  {
    case '*': analyseur++; F3 = &gmul; goto L3;
    case '/': analyseur++; F3 = &gdiv; goto L3;
    case '%': analyseur++; F3 = &gmod; goto L3;
    case '\\':
      if (analyseur[1] != '/') { analyseur++; F3 = &gdivent; goto L3; }
      analyseur += 2; F3=&gdivround; goto L3;

    case '<':
      if (analyseur[1] != '<') break;
      analyseur += 2; F3 = &gshift_l; goto L3;
    case '>':
      if (analyseur[1] != '>') break;
      analyseur += 2; F3 = &gshift_r; goto L3;
  }
  F3 = (F2GEN)NULL;

L2:
  if (e3 == UNDEF) goto L3;
  e2 = F2? F2(e2,e3): e3;
  e3 = UNDEF;
  if (low_stack(lim, stack_lim(av,2)))
  {
    GEN *gptr[2]; gptr[0]=&e2; gptr[1]=&e1;
    if(DEBUGMEM>1) err(warnmem,"expr");
    gerepilemany(av,gptr,(e1==UNDEF)?1: 2);
  }

  switch(*analyseur)
  {
    case '+': analyseur++; F2=&gadd; goto L3;
    case '-': analyseur++; F2=&gsub; goto L3;
  }
  F2 = (F2GEN)NULL;

L1:
  if (e2 == UNDEF) goto L2;
  e1 = F1? F1(e1,e2): e2;
  e2 = UNDEF;
  switch(*analyseur)
  {
    case '<':
      switch(*++analyseur)
      {
        case '=': analyseur++; F1=&gle; goto L2;
        case '>': analyseur++; F1=&gne; goto L2;
      }
      F1=&glt; goto L2;

    case '>':
      if (*++analyseur == '=') { analyseur++; F1=&gge; goto L2; }
      F1=&ggt; goto L2;

    case '=':
      if (analyseur[1] == '=') { analyseur+=2; F1=&geq; goto L2; }
      goto L1;

    case '!':
      if (analyseur[1] == '=') { analyseur+=2; F1=&gne; goto L2; }
      goto L1;
  }
  F1 = (F2GEN)NULL;

/* L0: */
  if (e1 == UNDEF) goto L1;
  e = F0? (gcmp0(e1)? gzero: gun): e1;
  e1 = UNDEF;
  switch(*analyseur)
  {
    case '&':
      if (*++analyseur == '&') analyseur++;
      if (gcmp0(e)) { skipexpr(); return gzero; }
      F0=1; goto L1;

    case '|':
      if (*++analyseur == '|') analyseur++;
      if (!gcmp0(e)) { skipexpr(); return gun; }
      F0=1; goto L1;
  }
  return e;
}
#undef UNDEF

/********************************************************************/
/**                                                                **/
/**                        CHECK FUNCTIONS                         **/
/**                                                                **/
/********************************************************************/
/* Should raise an error. If neighbouring identifier was a function in
 * 1.39.15, raise "obsolete" error instead. If check_new_fun doesn't help,
 * guess offending function was last identifier */
#define LEN 127
static void
err_new_fun()
{
  char s[LEN+1], *t;
  int n;

  if (check_new_fun == NOT_CREATED_YET) check_new_fun = NULL;
  t = check_new_fun? check_new_fun->name: mark.identifier;
  for (n=0; n < LEN; n++)
    if (!is_keyword_char(t[n])) break;
  (void)strncpy(s,t, n); s[n] = 0;
  if (check_new_fun) { kill0(check_new_fun); check_new_fun = NULL ; }
  if (compatible != NONE) return;

  if (whatnow_fun)
    n = whatnow_fun(s,1);
  else
    n = is_entry_intern(s,funct_old_hash,NULL)? 1: 0;
  if (n) err(obsoler,mark.identifier,mark.start, s,n);
}
#undef LEN

static void
err_match(char *s, char c)
{
  char str[64];
  if (check_new_fun && (c == '(' || c == '=' || c == ',')) err_new_fun();
  sprintf(str,"expected character: '%c' instead of",c);
  err(talker2,str,s,mark.start);
}

#define match2(s,c) if (*s != c) err_match(s,c);
#define match(c) \
  do { match2(analyseur, c); analyseur++; } while (0)

static long
readlong()
{
  const gpmem_t av = avma;
  const char *old = analyseur;
  long m;
  GEN arg = expr();

  if (br_status) err(breaker,"here (reading long)");
  if (typ(arg) != t_INT) err(caseer,old,mark.start);
  m = itos(arg); avma=av; return m;
}

static long
check_array_index(long max)
{
  const char *old = analyseur;
  const long c = readlong();

  if (c < 1 || c >= max)
  {
    char s[80];
    sprintf(s,"array index (%ld) out of allowed range ",c);
    if (max == 1) strcat(s, "[none]");
    else if (max == 2) strcat(s, "[1]");
    else sprintf(s,"%s[1-%ld]",s,max-1);
    err(talker2,s,old,mark.start);
  }
  return c;
}

static long
readvar()
{
  const char *old = analyseur;
  const GEN x = expr();

  if (typ(x) != t_POL || lgef(x) != 4 ||
    !gcmp0((GEN)x[2]) || !gcmp1((GEN)x[3])) err(varer1,old,mark.start);
  return varn(x);
}

/* noparen = 1 means function was called without (). Do we need to insert a
 * default argument ? */
static int
do_switch(int noparen, int matchcomma)
{
  const char *s = analyseur;
  if (noparen || !*s || *s == ')' || separe(*s)) return 1;
  if (*s == ',') /* we just read an arg, or first arg */
  {
    if (!matchcomma && s[-1] == '(') return 1; /* first arg */
    if (s[1] == ',' || s[1] == ')') { analyseur++; return 1; }
  }
  return 0;
}

/********************************************************************/
/**                                                                **/
/**                          READ FUNCTIONS                        **/
/**                                                                **/
/********************************************************************/
typedef struct matcomp
{
  GEN *ptcell;
  GEN parent;
  long full_col, full_row;
} matcomp;

/* Return the content of the matrix cell and sets members of corresponding
 * matrix component 'c'.  Assume *analyseur = '[' */
static GEN
matcell(GEN p, matcomp *C)
{
  GEN *pt = &p;
  long c,r, tx, full_col, full_row;
  tx = full_col = full_row = 0; 
  do {
    analyseur++; p = *pt; tx = typ(p);
    switch(tx)
    {
      case t_LIST:
        c = check_array_index(lgef(p)-1) + 1;
        pt = (GEN*)(p + c); match(']'); break;

      case t_VEC: case t_COL:
        c = check_array_index(lg(p));
        pt = (GEN*)(p + c); match(']'); break;

      case t_VECSMALL:
        c = check_array_index(lg(p));
        pt = (GEN*)(p + c); match(']');
        if (*analyseur == '[') err(caracer1,analyseur,mark.start);
        break;

      case t_MAT:
        if (lg(p)==1) err(talker2,"a 0x0 matrix has no elements",
                                  analyseur,mark.start);
        full_col = full_row = 0;
        if (*analyseur==',') /* whole column */
        {
          analyseur++; full_col = 1;
          c = check_array_index(lg(p));
          pt = (GEN*)(p + c); match(']'); break;
        }

        r = check_array_index(lg(p[1]));
        match(',');
        if (*analyseur == ']') /* whole row */
        {
          GEN p2 = cgetg(lg(p),t_VEC);
          analyseur++;
          if (*analyseur != '[') full_row = r;
          for (c=1; c<lg(p); c++) p2[c] = coeff(p,r,c);
          pt = &p2;
        }
        else
        {
          c = check_array_index(lg(p));
          pt = (GEN*)(((GEN)p[c]) + r); /* &coeff(p,r,c) */
          match(']');
        }
        break;

      default:
        err(caracer1,analyseur-1,mark.start);
    }
  } while (*analyseur == '[');
  C->full_row = full_row;
  C->full_col = full_col;
  C->parent = p; C->ptcell = pt;
  return (tx == t_VECSMALL)? stoi((long)*pt): *pt;
}

static GEN
facteur(void)
{
  const char *old = analyseur;
  GEN x,p1;
  int plus=1;

  switch(*analyseur)
  {
    case '-': plus=0; /* fall through */
    case '+': analyseur++; break;
  }
  x = truc();
  if (br_status) return NULL;

  for(;;)
    switch(*analyseur)
    {
      case '.':
	analyseur++; x = read_member(x);
        if (!x) err(talker2, "not a proper member definition",
                    mark.member, mark.start);
        break;
      case '^':
	analyseur++; p1 = facteur();
        if (br_status) err(breaker,"here (after ^)");
        x = gpow(x,p1,prec); break;
      case '\'':
	analyseur++; x = deriv(x,gvar9(x)); break;
      case '~':
	analyseur++; x = gtrans(x); break;
      case '[':
      {
        matcomp c;
        x = matcell(x, &c);
        if (isonstack(x)) x = gcopy(x);
        break;
      }
      case '!':
	if (analyseur[1] != '=')
	{
	  if (typ(x) != t_INT) err(caseer,old,mark.start);
	  analyseur++; x=mpfact(itos(x)); break;
	} /* Fall through */

      default:
        return (plus || x==gnil)? x: gneg(x);
    }
}

/* table array of length N+1, append one expr, growing array if necessary  */
static void
_append(GEN **table, long *n, long *N)
{
  if (++(*n) == *N)
  {
    *N <<= 1;
    *table = (GEN*)gprealloc((void*)*table,(*N + 1)*sizeof(GEN));
  }
  (*table)[*n] = expr();
  if (br_status) err(breaker,"array context");
}

#define check_var_name() \
  if (!isalpha((int)*analyseur)) err(varer1,analyseur,mark.start);

static GEN
truc(void)
{
  long N,i,j,m,n,p;
  GEN *table,p1;
  char *old;

  if (*analyseur == '!') /* NOT */
  {
    analyseur++; p1 = facteur();
    if (br_status) err(breaker,"here (after !)");
    return gcmp0(p1)? gun: gzero;
  }
  if (*analyseur == '\'') /* QUOTE */
  {
    const char* old;
    entree *ep;
    analyseur++; check_var_name();
    old = analyseur; ep = entry();
    switch(EpVALENCE(ep))
    {
      case EpVAR: case EpGVAR:
        return (GEN)initial_value(ep);
      default: err(varer1,old,mark.start);
    }
  }
  if (*analyseur == '#') /* CARD */
  {
    analyseur++; p1 = facteur();
    if (br_status) err(breaker,"here (after #)");
    return stoi(glength(p1));
  }
  if (isalpha((int)*analyseur)) return identifier();

  if (*analyseur == '"') return strtoGENstr_t();
  if (isdigit((int)*analyseur) || *analyseur == '.') return constante();
  switch(*analyseur++)
  {
    case '(': p1=expr(); match(')'); return p1;

    case '[': /* constant array/vector */
      if (*analyseur == ';' && analyseur[1] == ']')
	{ analyseur += 2; return cgetg(1,t_MAT); } /* [;] */

      n = 0; N = 1024;
      table = (GEN*) gpmalloc((N + 1)*sizeof(GEN));

      if (*analyseur != ']') _append(&table, &n, &N);
      while (*analyseur == ',') { analyseur++; _append(&table, &n, &N); }
      switch (*analyseur++)
      {
	case ']':
        {
          long tx;
          if (*analyseur == '~') { analyseur++; tx=t_COL; } else tx=t_VEC;
	  p1 = cgetg(n+1,tx);
	  for (i=1; i<=n; i++) p1[i] = lcopy(table[i]);
	  break;
        }

	case ';':
	  m = n;
	  do _append(&table, &n, &N); while (*analyseur++ != ']');
	  p1 = cgetg(m+1,t_MAT); p = n/m + 1;
	  for (j=1; j<=m; j++)
	  {
            GEN c = cgetg(p,t_COL); p1[j] = (long)c;
	    for (i=j; i<=n; i+=m) *++c = lcopy(table[i]);
	  }
	  break;

	default: /* can only occur in library mode */
          err(talker,"incorrect vector or matrix");
          return NULL; /* not reached */
      }
      free(table); return p1;

    case '%':
    old = analyseur-1;
    if (!GP_DATA) err(talker2,"history not available", old, mark.start);
    else
    {
      gp_hist *H = GP_DATA->hist;
      p = 0;
      while (*analyseur == '`') { analyseur++; p++; }
      return p ? gp_history(H, -p        , old, mark.start)
               : gp_history(H, number(&n), old, mark.start);
    }
  }
  err(caracer1,analyseur-1,mark.start);
  return NULL; /* not reached */
}

/* valid x opop, e.g x++ */
static GEN
double_op()
{
  static long mun[] = { evaltyp(t_INT) | _evallg(3), 
                        evalsigne(-1)|evallgefint(3), 1 };
  char c = *analyseur;
  if (c == analyseur[1])
    switch(c)
    {
      case '+': analyseur+=2; return gun; /* ++ */
      case '-': analyseur+=2; return mun; /* -- */
    }
  return NULL;
}

/* return op if op= detected */
static F2GEN
get_op_fun()
{
  if (!*analyseur) return (F2GEN)NULL;

  /* op= constructs ? */
  if (analyseur[1] == '=')
  {
    switch(*analyseur)
    {
      case '+' : analyseur += 2; return &gadd;
      case '-' : analyseur += 2; return &gsub;
      case '*' : analyseur += 2; return &gmul;
      case '/' : analyseur += 2; return &gdiv;
      case '\\': analyseur += 2; return &gdivent;
      case '%' : analyseur += 2; return &gmod;
    }
  }
  else if (analyseur[2] == '=')
  {
    switch(*analyseur)
    {
      case '>' :
        if (analyseur[1]=='>') { analyseur += 3; return &gshift_r; }
        break;
      case '<' :
        if (analyseur[1]=='<') { analyseur += 3; return &gshift_l; }
        break;
      case '\\':
        if (analyseur[1]=='/') { analyseur += 3; return &gdivround; }
        break;
    }
  }
  return (F2GEN)NULL;
}

static GEN
expr_ass()
{
  GEN res = expr();
  if (br_status) err(breaker,"assignment");
  return res;
}

F2GEN
affect_block(GEN *res)
{
  F2GEN f;
  GEN r;
  if (*analyseur == '=')
  {
    r = NULL; f = NULL;
    if (analyseur[1] != '=') { analyseur++; r = expr_ass(); }
  }
  else if ((r = double_op()))  f = &gadd;
  else if ((f = get_op_fun())) r = expr_ass();
  *res = r; return f;
}

/* assign res at *pt in "simple array object" p */
static GEN
change_compo(matcomp c, GEN res)
{
  GEN p = c.parent, *pt = c.ptcell;
  long i, full_row = c.full_row, full_col = c.full_col;
  char *old = analyseur;

  if (typ(p) == t_VECSMALL)
  {
    if (typ(res) != t_INT || is_bigint(res))
      err(talker2,"not a suitable VECSMALL component",old,mark.start);
    *pt = (GEN)itos(res); return res;
  }
  if (full_row)
  {
    if (typ(res) != t_VEC || lg(res) != lg(p)) err(caseer2,old,mark.start);
    for (i=1; i<lg(p); i++)
    {
      GEN p1 = gcoeff(p,full_row,i); if (isclone(p1)) killbloc(p1);
      coeff(p,full_row,i) = lclone((GEN)res[i]);
    }
    return res;
  }
  if (full_col)
    if (typ(res) != t_COL || lg(res) != lg(*pt)) err(caseer2,old,mark.start);

  res = gclone(res);
  if (isclone(*pt)) killbloc(*pt);
  return *pt = res;
}

/* extract from p the needed component */
static GEN
matrix_block(GEN p)
{
  char *end, *ini = analyseur;
  GEN res, cpt;
  matcomp c;
  F2GEN fun;

  skip_matrix_block();
  fun = affect_block(&res);
  end = analyseur;
  analyseur = ini;
  cpt = matcell(p, &c);
  if (res)
  {
    if (fun) res = fun(cpt, res);
    res = change_compo(c,res);
    analyseur = end;
  }
  else res = isonstack(cpt)? gcopy(cpt): cpt; /* no assignment */
  return res;
}

static char*
init_buf(long len, char **ptbuf, char **ptlim)
{
  char *buf = (char *)new_chunk(2 + len / sizeof(long));
  *ptbuf = buf; *ptlim = buf + len; return buf;
}

static char*
realloc_buf(char *bp, long len, char **ptbuf,char **ptlimit)
{
  char *buf = *ptbuf;
  long newlen = ((*ptlimit - buf) + len) << 1;
  long oldlen = bp - buf;

  (void)init_buf(newlen, ptbuf, ptlimit);
  memcpy(*ptbuf, buf, oldlen);
  return *ptbuf + oldlen;
}

static char *
expand_string(char *bp, char **ptbuf, char **ptlimit)
{
  char *tmp = NULL; /* -Wall */
  long len = 0; /* -Wall */
  int alloc = 1;

  if (is_keyword_char(*analyseur))
  {
    char *s = analyseur;
    do s++; while (is_keyword_char(*s));

    if ((*s == '"' || *s == ',' || *s == ')') && !is_entry(analyseur))
    { /* Do not create new user variable. Consider as a literal */
      tmp = analyseur;
      len = s - analyseur;
      analyseur = s;
      alloc = 0;
    }
  }

  if (alloc)
  {
    gpmem_t av = avma;
    GEN p1 = expr();
    if (br_status) err(breaker,"here (expanding string)");
    tmp = GENtostr0(p1, &DFLT_OUTPUT, &gen_output);
    len = strlen(tmp); avma = av;
  }
  if (ptlimit && bp + len > *ptlimit)
    bp = realloc_buf(bp, len, ptbuf,ptlimit);
  memcpy(bp,tmp,len); /* ignore trailing \0 */
  if (alloc) free(tmp);
  return bp + len;
}

static char *
translate(char **src, char *s, char **ptbuf, char **ptlim)
{
  char *t = *src;
  while (*t)
  {
    while (*t == '\\')
    {
      switch(*++t)
      {
	case 'e':  *s='\033'; break; /* escape */
	case 'n':  *s='\n'; break;
	case 't':  *s='\t'; break;
	default:   *s=*t; if (!*t) err(talker,"unfinished string");
      }
      t++; s++;
    }
    if (*t == '"')
    {
      if (t[1] != '"') break;
      t += 2; continue;
    }
    if (ptlim && s >= *ptlim)
      s = realloc_buf(s,1, ptbuf,ptlim);
    *s++ = *t++;
  }
  *s=0; *src=t; return s;
}

static char *
readstring_i(char *s, char **ptbuf, char **ptlim)
{
  match('"'); s = translate(&analyseur,s, ptbuf,ptlim); match('"');
  return s;
}

static GEN
any_string()
{
  long n = 0, len = 16;
  GEN res = new_chunk(len + 1);

  while (*analyseur)
  {
    if (*analyseur == ')' || *analyseur == ';') break;
    if (*analyseur == ',')
      analyseur++;
    else
    {
      res[n++] = (long)expr();
      if (br_status) err(breaker,"here (print)");
    }
    if (n == len)
    {
      long newlen = len << 1;
      GEN p1 = new_chunk(newlen + 1);
      for (n = 0; n < len; n++) p1[n] = res[n];
      res = p1; len = newlen;
    }
  }
  res[n] = 0; /* end the sequence with NULL */
  return res;
}

/*  Read a "string" from src. Format then copy it, starting at s. Return
 *  pointer to the \0 which terminates the string.
 */
char *
readstring(char *src, char *s)
{
  match2(src, '"'); src++; s = translate(&src, s, NULL,NULL);
  match2(src, '"'); return s;
}

static GEN
strtoGENstr_t()
{
  char *old = analyseur;
  long n;
  GEN x;

  skipstring(); n = analyseur-old - 1; /* don't count the enclosing '"' */
  old++; /* skip '"' */
  n = (n+BYTES_IN_LONG) >> TWOPOTBYTES_IN_LONG;
  x = cgetg(n+1, t_STR);
  (void)translate(&old, GSTR(x), NULL,NULL);
  return x;
}

/* return the first n0 chars of s as a GEN [s may not be 0­terminated] */
static GEN
_strtoGENstr(char *s, long n0)
{
  long n = (n0+1+BYTES_IN_LONG) >> TWOPOTBYTES_IN_LONG;
  GEN x = cgetg(n+1, t_STR);
  char *t = GSTR(x);
  strncpy(t, s, n0); t[n0] = 0; return x;
}

GEN
strtoGENstr(char *s, long flag)
{
  GEN x;

  if (flag) s = expand_tilde(s);
  x = _strtoGENstr(s, strlen(s));
  if (flag) free(s);
  return x;
}

/* x = gzero: no default value, otherwise a t_STR, formal expression for
 * default argument. Evaluate and return. */
static GEN
make_arg(GEN x) { return (x==gzero)? x: geval(x); }

static GEN
fun_seq(char *p)
{
  GEN res = lisseq(p);
  if (br_status != br_NONE)
    br_status = br_NONE;
  else
    if (! is_universal_constant(res)) /* important for gnil */
      res = forcecopy(res); /* make result safe */
  return res;
}

/* p = NULL + array of variable numbers (longs) + function text */
static GEN
call_fun(GEN p, GEN *arg, GEN *loc, int narg, int nloc)
{
  GEN res;
  long i;

  p++; /* skip NULL */
  /* push new values for formal parameters */
  for (i=0; i<narg; i++) copyvalue(*p++, *arg++);
  for (i=0; i<nloc; i++) pushvalue(*p++, make_arg(*loc++));
  /* dumps arglist from identifier() to the garbage zone */
  res = fun_seq((char *)p);
  /* pop out ancient values of formal parameters */
  for (i=0; i<nloc; i++) killvalue(*--p);
  for (i=0; i<narg; i++) killvalue(*--p);
  return res;
}
/* p = NULL + array of variable numbers (longs) + function text */
static GEN
call_member(GEN p, GEN x)
{
  GEN res;

  p++; /* skip NULL */
  /* push new values for formal parameters */
  pushvalue(*p++, x);
  res = fun_seq((char *)p);
  /* pop out ancient values of formal parameters */
  killvalue(*--p);
  return res;
}

entree *
do_alias(entree *ep)
{
  while (ep->valence == EpALIAS) ep = (entree *) ((GEN)ep->value)[1];
  return ep;
}

static GEN
global0()
{
  GEN res = gnil;
  long i,n;

  for (i=0,n=lg(polvar)-1; n>=0; n--)
  {
    entree *ep = varentries[n];
    if (ep && EpVALENCE(ep) == EpGVAR)
    {
      res=new_chunk(1);
      res[0]=(long)polx[n]; i++;
    }
  }
  if (i) { res = cgetg(1,t_VEC); setlg(res, i+1); }
  return res;
}

static void
check_pointers(unsigned int ptrs, matcomp *init[])
{
  unsigned int i;
  for (i=0; ptrs; i++,ptrs>>=1)
    if (ptrs & 1)
    {
      matcomp *c = init[i];
      GEN *pt = c->ptcell, x = gclone(*pt);
      if (c->parent == NULL)
      {
        if (isclone(*pt)) killbloc(*pt);
        *pt = x;
      }
      else
        (void)change_compo(*c, x);
      free((void*)c);
    }
}

#define match_comma() \
  do { if (matchcomma) match(','); else matchcomma = 1; } while (0)

static void
skipdecl(void)
{
  if (*analyseur == ':') { analyseur++; skipexpr(); }
}

static long
check_args()
{
  long nparam = 0, matchcomma = 0;
  entree *ep;
  char *old;
  GEN cell;

  while (*analyseur != ')')
  {
    old=analyseur; nparam++; match_comma();
    cell = new_chunk(2);
    if (!isalpha((int)*analyseur))
    {
      err_new_fun();
      err(paramer1, mark.identifier, mark.start);
    }
    ep = entry();
    if (EpVALENCE(ep) != EpVAR)
    {
      err_new_fun();
      if (EpVALENCE(ep) == EpGVAR)
        err(talker2,"global variable: ",old , mark.start);
      err(paramer1, old, mark.start);
    }
    cell[0] = varn(initial_value(ep));
    skipdecl();
    if (*analyseur == '=')
    {
      char *old = ++analyseur;
      gpmem_t av = avma;
      skipexpr();
      cell[1] = lclone(_strtoGENstr(old, analyseur-old));
      avma = av;
    }
    else cell[1] = zero;
  }
  return nparam;
}

static GEN
do_call(void *call, GEN x, GEN argvec[])
{
  return ((PFGEN)call)(x, argvec[1], argvec[2], argvec[3], argvec[4],
                          argvec[5], argvec[6], argvec[7], argvec[8]);
}

static GEN
fix(GEN x, long l)
{
  GEN y;
  if (typ(x) == t_COMPLEX)
  {
    y = cgetg(3,t_COMPLEX);
    y[1] = (long)fix((GEN)x[1],l);
    y[2] = (long)fix((GEN)x[2],l);
  }
  else
  {
    y = cgetr(l); gaffect(x,y);
  }
  return y;
}

/* Rationale: (f(2^-e) - f(-2^-e) + O(2^-pr)) / (2 * 2^-e) = f'(0) + O(2^-2e)
 * since 2nd derivatives cancel.
 *   prec(LHS) = pr - e
 *   prec(RHS) = 2e, equal when  pr = 3e = 3/2 fpr (fpr = required final prec)
 *
 * For f'(x), x far from 0: prec(LHS) = pr - e - expo(x)
 * --> pr = 3/2 fpr + expo(x) */
static GEN
num_deriv(void *call, GEN argvec[])
{
  GEN eps,a,b, y, x = argvec[0];
  long fpr, pr, l, e, ex;
  gpmem_t av = avma;
  if (!is_const_t(typ(x)))
  {
    a = do_call(call, x, argvec);
    return gerepileupto(av, deriv(a,gvar9(a)));
  }
  fpr = precision(x)-2; /* required final prec (in sig. words) */
  if (fpr == -2) fpr = prec-2;
  ex = gexpo(x);
  if (ex < 0) ex = 0; /* at 0 */
  pr = (long)ceil(fpr * 1.5 + (ex / BITS_IN_LONG));
  l = 2+pr;
  e = fpr * BITS_IN_HALFULONG; /* 1/2 required prec (in sig. bits) */

  eps = real2n(-e, l);
  y = fix(gsub(x, eps), l); a = do_call(call, y, argvec);
  y = fix(gadd(x, eps), l); b = do_call(call, y, argvec);
  setexpo(eps, e-1);
  return gerepileupto(av, gmul(gsub(b,a), eps));
}

/* as above, for user functions */
static GEN
num_derivU(GEN p, GEN *arg, GEN *loc, int narg, int nloc)
{
  GEN eps,a,b, x = *arg;
  long fpr, pr, l, e, ex;
  gpmem_t av = avma;

  if (!is_const_t(typ(x)))
  {
    a = call_fun(p,arg,loc,narg,nloc);
    return gerepileupto(av, deriv(a,gvar9(a)));
  }
  fpr = precision(x)-2; /* required final prec (in sig. words) */
  if (fpr == -2) fpr = prec-2;
  ex = gexpo(x);
  if (ex < 0) ex = 0; /* at 0 */
  pr = (long)ceil(fpr * 1.5 + (ex / BITS_IN_LONG));
  l = 2+pr;
  e = fpr * BITS_IN_HALFULONG; /* 1/2 required prec (in sig. bits) */

  eps = real2n(-e, l);
  *arg = fix(gsub(x, eps), l); a = call_fun(p,arg,loc,narg,nloc);
  *arg = fix(gadd(x, eps), l); b = call_fun(p,arg,loc,narg,nloc);
  setexpo(eps, e-1);
  return gerepileupto(av, gmul(gsub(b,a), eps));
}

#define DFT_VAR (GEN)-1L
#define DFT_GEN (GEN)NULL
#define _ARGS_ argvec[0], argvec[1], argvec[2], argvec[3],\
               argvec[4], argvec[5], argvec[6], argvec[7], argvec[8]

static GEN
identifier(void)
{
  long m, i, matchcomma, deriv;
  gpmem_t av;
  char *ch1;
  entree *ep;
  GEN res, newfun, ptr;

  mark.identifier = analyseur; ep = entry();
  if (EpVALENCE(ep)==EpVAR || EpVALENCE(ep)==EpGVAR)
  { /* optimized for simple variables */
    switch (*analyseur)
    {
      case ')': case ',': return (GEN)ep->value;
      case '.':
      {
        long len, v;

        analyseur++; ch1 = analyseur;
        if ((res = read_member((GEN)ep->value)))
        {
          if (*analyseur == '[')
          {
            matcomp c;
            res = matcell(res, &c);
          }
          return res;
        }
        /* define a new member function */
        v = varn(initial_value(ep));
        len = analyseur - ch1;
        analyseur++; /* skip = */
        ep = installep(NULL,ch1,len,EpMEMBER,0, members_hash + hashvalue(ch1));
        ch1 = analyseur; skipseq(); len = analyseur-ch1;

        newfun=ptr= (GEN) newbloc(1 + (len>>TWOPOTBYTES_IN_LONG) + 4);
        newfun++; /* this bloc is no GEN, leave the first cell alone ( = 0) */
        *newfun++ = v;

        /* record text */
        strncpy((char *)newfun, ch1, len);
        ((char *) newfun)[len] = 0;
        ep->value = (void *)ptr; return gnil;
      }
    }
    if (*analyseur != '[')
    { /* whole variable, no component */
      F2GEN fun = affect_block(&res);
      if (res)
      {
        if (fun) res = fun((GEN)ep->value, res);
        changevalue(ep,res);
      }
      return (GEN)ep->value;
    }
    return matrix_block((GEN)ep->value);
  }
  ep = do_alias(ep); matchcomma = 0;
#ifdef STACK_CHECK
  if (PARI_stack_limit && (void*) &ptr <= PARI_stack_limit)
      err(talker2, "deep recursion", mark.identifier, mark.start);
#endif

  if (ep->code)
  {
    char *s = ep->code, *oldanalyseur = NULL, *buf, *limit, *bp;
    unsigned int ret, noparen, has_pointer=0;
    long fake;
    void *call = ep->value;
    GEN argvec[9];
    matcomp *init[9];

    deriv = (*analyseur == '\'' && analyseur[1] == '(') && analyseur++;
    if (*analyseur == '(')
    {
      analyseur++;
      noparen=0; /* expect matching ')' */
    }
    else
    { /* if no mandatory argument, no () needed */
      if (EpVALENCE(ep)) match('('); /* error */

      if (!*s || (!s[1] && *s == 'p'))
	return ((GEN (*)(long))call)(prec);
      noparen=1; /* no argument, but valence is ok */
    }
    /* return type */
    if      (*s == 'v') { ret = RET_VOID; s++; }
    else if (*s == 'l') { ret = RET_INT;  s++; }
    else                  ret = RET_GEN;
    /* Optimized for G and p. */
    i = 0;
    while (*s == 'G')
    {
      match_comma(); s++;
      argvec[i++] = expr();
      if (br_status) err(breaker,"here (argument reading)");
    }
    if (*s == 'p') { argvec[i++] = (GEN) prec; s++; }

    while (*s)
      switch (*s++)
      {
	case 'G': /* GEN */
	  match_comma(); argvec[i++] = expr();
          if (br_status) err(breaker,"here (argument reading)");
          break;

	case 'L': /* long */
	  match_comma(); argvec[i++] = (GEN) readlong(); break;

	case 'n': /* var number */
	  match_comma(); argvec[i++] = (GEN) readvar(); break;

        case 'S': /* symbol */
	  match_comma(); mark.symbol=analyseur;
	  argvec[i++] = (GEN)entry(); break;

	case 'V': /* variable */
	  match_comma(); mark.symbol=analyseur;
        {
          entree *e = entry();
          long v = EpVALENCE(e);
          if (v != EpVAR && v != EpGVAR)
            err(talker2,"not a variable:",mark.symbol,mark.start);
	  argvec[i++] = (GEN)e; break;
        }
        case '&': /* *GEN */
	  match_comma(); match('&'); mark.symbol=analyseur;
        {
          matcomp *c = (matcomp*)malloc(sizeof(matcomp));
          entree *ep = entry();

          if (*analyseur == '[')
            (void)matcell((GEN)ep->value, c);
          else
          {
            c->parent = NULL;
            c->ptcell = (GEN*)&ep->value;
          }
          has_pointer |= (1 << i);
          init[i] = c;
	  argvec[i++] = (GEN)c->ptcell; break;
        }
        /* Input position */
        case 'E': /* expr */
	case 'I': /* seq */
	  match_comma();
	  argvec[i++] = (GEN) analyseur;
	  skipseq(); break;

	case 'r': /* raw */
	  match_comma(); mark.raw = analyseur;
          bp = init_buf(256, &buf,&limit);
	  while (*analyseur)
	  {
	    if (*analyseur == ',' || *analyseur == ')') break;
	    if (*analyseur == '"')
	      bp = readstring_i(bp, &buf,&limit);
            else
            {
              if (bp > limit)
                bp = realloc_buf(bp,1, &buf,&limit);
              *bp++ = *analyseur++;
            }
	  }
	  *bp++ = 0; argvec[i++] = (GEN) buf;
	  break;

	case 's': /* expanded string; empty arg yields "" */
	  match_comma();
	  if (*s == '*') /* any number of string objects */
          {
            argvec[i++] = any_string();
            s++; break;
          }

          bp = init_buf(256, &buf,&limit);
          while (*analyseur)
          {
            if (*analyseur == ',' || *analyseur == ')') break;
            bp = expand_string(bp, &buf,&limit);
          }
          *bp++ = 0; argvec[i++] = (GEN)buf;
          break;

	case 'p': /* precision */
	  argvec[i++] = (GEN) prec; break;

	case '=':
	  match('='); matchcomma = 0; break;

	case 'D': /* Has a default value */
	  if (do_switch(noparen,matchcomma))
            switch (*s)
            {
              case 'G':
              case '&':
              case 'I':
              case 'V': argvec[i++]=DFT_GEN; s++; break;
              case 'n': argvec[i++]=DFT_VAR; s++; break;
              default:
                oldanalyseur = analyseur;
                analyseur = s; matchcomma = 0;
                while (*s++ != ',');
            }
          else
            switch (*s)
            {
              case 'G':
              case '&':
              case 'I':
              case 'V':
              case 'n': break;
              default:
                while (*s++ != ',');
            }
	  break;

	 case 'P': /* series precision */
	   argvec[i++] = (GEN) precdl; break;

	 case 'f': /* Fake *long argument */
	   argvec[i++] = (GEN) &fake; break;

	 case 'x': /* Foreign function */
	   argvec[i++] = (GEN) ep; call = foreignHandler; break;

	 case ',': /* Clean up default */
	   if (oldanalyseur)
	   {
	     analyseur = oldanalyseur;
	     oldanalyseur = NULL; matchcomma=1;
	   }
	   break;
	 default: err(bugparier,"identifier (unknown code)");
      }
#if 0 /* uncomment if using purify: unitialized read otherwise */
    for ( ; i<9; i++) argvec[i]=NULL;
#endif
    if (deriv)
    {
      if (!i || (ep->code)[0] != 'G')
        err(talker2, "can't derive this", mark.identifier, mark.start);
      res = num_deriv(call, argvec);
    }
    else switch (ret)
    {
      default: /* case RET_GEN: */
	res = ((PFGEN)call)(_ARGS_);
	break;

      case RET_INT:
	m = ((long (*)(ANYARG))call)(_ARGS_);
	res = stoi(m); break;

      case RET_VOID:
	((void (*)(ANYARG))call)(_ARGS_);
	res = gnil; break;
    }
    if (has_pointer) check_pointers(has_pointer,init);
    if (!noparen) match(')');
    return res;
  }

  if (EpPREDEFINED(ep))
  {
    if (*analyseur != '(')
    {
      if (EpVALENCE(ep) == 88) return global0();
      match('('); /* error */
    }
    analyseur++;
    switch(EpVALENCE(ep))
    {
      case 50: /* O */
        res = truc();
        if (br_status) err(breaker,"here (in O()))");
	if (*analyseur=='^') { analyseur++; m = readlong(); } else m = 1;
	res = ggrando(res,m); break;

      case 80: /* if then else */
        av = avma; res = expr();
        if (br_status) err(breaker,"test expressions");
        m = gcmp0(res); avma = av; match(',');
	if (m) /* false */
	{
	  skipseq();
	  if (*analyseur == ')') res = gnil;
	  else
          {
            match(',');
            res = seq(); if (br_status) { res = NULL; skipseq(); }
          }
	}
	else /* true */
	{
          res = seq(); if (br_status) { res = NULL; skipseq(); }
          if (*analyseur != ')') { match(','); skipseq(); }
	}
	break;

      case 81: /* while do */
        av = avma; ch1 = analyseur;
	for(;;)
	{
          res = expr();
          if (br_status) err(breaker,"test expressions");
	  if (gcmp0(res)) { match(','); break; }

	  avma = av; match(','); (void)seq();
	  if (loop_break()) break;
          analyseur = ch1;
	}
	avma = av; skipseq(); res = gnil; break;

      case 82: /* repeat until */
        av = avma; ch1 = analyseur; skipexpr();
	for(;;)
	{
	  avma = av; match(','); (void)seq();
	  if (loop_break()) break;
	  analyseur = ch1;
          res = expr();
          if (br_status) err(breaker,"test expressions");
	  if (!gcmp0(res)) { match(','); break; }
	}
	avma = av; skipseq(); res = gnil; break;

      case 88: /* global */
        if (*analyseur == ')') return global0();
        while (*analyseur != ')')
        {
          match_comma(); ch1=analyseur;
          check_var_name();
          ep = skipentry();
          switch(EpVALENCE(ep))
          {
            case EpGVAR:
#if 0
              err(warner,"%s already declared global", ep->name);
#endif
              /* fall through */
            case EpVAR: break;
            default: err(talker2,"symbol already in use",ch1,mark.start);
          }
          analyseur=ch1; ep = entry();
          if (*analyseur == '=')
          {
            gpmem_t av=avma; analyseur++;
            res = expr();
            if (br_status) err(breaker,"here (defining global var)");
            changevalue(ep, res); avma=av;
          }
          ep->valence = EpGVAR;
        }
        res = gnil; break;

      default: err(valencer1);
        return NULL; /* not reached */
    }
    match(')'); return res;
  }

  switch (EpVALENCE(ep))
  {
    GEN *defarg; /* = default args, and values for local variables */
    int narg, nloc;
    gp_args *f;

    case EpUSER: /* user-defined functions */
      f = (gp_args*)ep->args;
      defarg = f->arg;
      narg = f->narg;
      nloc = f->nloc;
      deriv = (*analyseur == '\'' && analyseur[1] == '(') && analyseur++;
      if (*analyseur != '(') /* no args */
      {
	if (*analyseur != '='  ||  analyseur[1] == '=')
        {
          GEN *arglist = (GEN*) new_chunk(narg);
          for (i=0; i<narg; i++)
            arglist[i] = make_arg(defarg[i]);
	  return call_fun((GEN)ep->value, arglist, defarg+narg, narg, nloc);
        }
	match('('); /* ==> error */
      }
      if (analyseur != redefine_fun)
      {
        GEN *arglist = (GEN*) new_chunk(narg);
        ch1 = analyseur; analyseur++;
        for (i=0; i<narg; i++)
        {
          if (do_switch(0,matchcomma))
          { /* default arg */
            arglist[i] = make_arg(defarg[i]);
            matchcomma = 1;
          }
          else
          { /* user supplied */
            match_comma();
            arglist[i] = expr();
            skipdecl(); /* we'd be redefining fun, but don't know it yet */
            if (br_status) err(breaker,"here (reading function args)");
          }
        }
        if (*analyseur++ == ')' && (*analyseur != '=' || analyseur[1] == '='))
        {
          if (deriv)
          {
            if (!narg)
              err(talker2, "can't derive this", mark.identifier, mark.start);
            return num_derivU((GEN)ep->value, arglist, defarg+narg, narg, nloc);
          }
          return call_fun((GEN)ep->value, arglist, defarg+narg, narg, nloc);
        }

        /* should happen only in cases like (f()= f()=); f (!!!) */
        analyseur--;
        if (*analyseur != ',' && *analyseur != ')') skipexpr();
        while (*analyseur == ',') { analyseur++; skipexpr(); }
        match(')');
        if (*analyseur != '='  ||  analyseur[1] == '=')
          err(nparamer1,mark.identifier,mark.start);
        matchcomma=0; analyseur = ch1;
      }
      redefine_fun = NULL;
      free_args((gp_args*)ep->args);
    /* Fall through */

    case EpNEW: /* new function */
    {
      GEN tmpargs = (GEN)avma;
      char *start;
      long len;

      check_new_fun = ep;

      /* checking arguments */
      match('('); ch1 = analyseur;
      narg = check_args(); nloc = 0;
      match(')'); 
      /* Dirty, but don't want to define a local() function */
      if (*analyseur != '=' && strcmp(ep->name, "local") == 0)
        err(talker2, "local() bloc must appear before any other expression",
                     mark.identifier,mark.start);
      match('=');
      { /* checking function definition */
        char *oldredef = redefine_fun;
        skipping_fun_def++;
        while (strncmp(analyseur,"local(",6) == 0)
        {
          analyseur += 6;
          nloc += check_args();
          match(')'); while(separe(*analyseur)) analyseur++;
        }
        start = analyseur; skipseq(); len = analyseur-start;
        skipping_fun_def--; redefine_fun = oldredef;
      }
      /* function is ok. record it */
      newfun = ptr = (GEN) newbloc(narg+nloc + (len>>TWOPOTBYTES_IN_LONG) + 4);
      newfun++; /* this bloc is no GEN, leave the first cell alone ( = 0) */

      /* record default args */
      f = (gp_args*) gpmalloc((narg+nloc)*sizeof(GEN) + sizeof(gp_args));
      ep->args = (void*) f;
      f->nloc = nloc;
      f->narg = narg;
      f->arg = defarg = (GEN*)(f + 1);
      narg += nloc; /* record default args and local variables */
      for (i = 1; i <= narg; i++)
      {
        GEN cell = tmpargs-(i<<1);
	*newfun++ =      cell[0];
        *defarg++ = (GEN)cell[1];
      }
      if (narg > 1)
      { /* check for duplicates */
        GEN x = new_chunk(narg), v = ptr+1;
        long k;
        for (i=0; i<narg; i++) x[i] = v[i];
        qsort(x,narg,sizeof(long),(QSCOMP)pari_compare_long);
        for (k=x[0],i=1; i<narg; k=x[i],i++)
          if (x[i] == k)
            err(talker,"user function %s: variable %Z declared twice",
                ep->name, polx[k]);
      }

      /* record text */
      strncpy((char *)newfun, start, len);
      ((char *) newfun)[len] = 0;
      if (EpVALENCE(ep) == EpUSER) gunclone((GEN)ep->value);
     /* have to wait till here because of strncopy above. In pathological
      * cases, e.g. (f()=f()=x), new text is given by value of old one! */
      ep->value = (void *)ptr;
      ep->valence = EpUSER;
      check_new_fun=NULL;
      avma = (gpmem_t)tmpargs; return gnil;
    }
  }
  err(valencer1); return NULL; /* not reached */
}

static long
number(long *nb)
{
  long m = 0;
  for (*nb = 0; *nb < 9 && isdigit((int)*analyseur); (*nb)++)
    m = 10*m + (*analyseur++ - '0');
  return m;
}

static GEN
constante()
{
  static long pw10[] = { 1, 10, 100, 1000, 10000, 100000, 1000000,
                        10000000, 100000000, 1000000000 };
  long i, l, m, n = 0, nb;
  gpmem_t av = avma;
  GEN z,y;

  y = stoi(number(&nb)); i = 0;
  while (isdigit((int)*analyseur))
  {
    if (++i == 4) { avma = av; i = 0; } /* HACK gerepile */
    m = number(&nb);
    y = addsmulsi(m, pw10[nb], y);
  }
  switch(*analyseur)
  {
    default: return y; /* integer */
    case '.':
      if (isalpha((int)analyseur[1])
          && analyseur[1] != 'e' && analyseur[1] != 'E')
        return y; /* member function */
      analyseur++; i = 0;
      while (isdigit((int)*analyseur))
      {
        if (++i == 4) { avma = av; i = 0; } /* HACK gerepile */
        m = number(&nb); n -= nb;
        y = addsmulsi(m, pw10[nb], y);
      }
      if (*analyseur != 'E' && *analyseur != 'e')
      {
        if (!signe(y)) { avma = av; return realzero(prec); }
        break;
      }
    /* Fall through */
    case 'E': case 'e':
    {
      char *old = analyseur;
      switch(*++analyseur)
      {
        case '-': analyseur++; n -= number(&nb); break;
        case '+': analyseur++; /* Fall through */
        default: n += number(&nb);
      }
      if (nb > 8) err(talker2,"exponent too large",old,mark.start);
      if (!signe(y))
      {
        avma = av; y = cgetr(3);
        n = (n > 0)? (long)(n/L2SL10): (long)-((-n)/L2SL10 + 1);
        y[1] = evalsigne(0) | evalexpo(n);
        y[2] = 0; return y;
      }
    }
  }
  l=lgefint(y); if (l<prec) l=prec;
  if (n)
  {
    (void)new_chunk(l); /* HACK: mulrr and divrr need exactly l words */
    z = itor(y, l);
    y = gpowgs(stor(10,l), labs(n));
    avma = av; /* hidden gerepile */
    return n > 0 ?  mulrr(z,y) : divrr(z,y);
  }
  return itor(y, l);
}

/********************************************************************/
/**                                                                **/
/**                   HASH TABLE MANIPULATIONS                     **/
/**                                                                **/
/********************************************************************/
long
is_keyword_char(char c) { return is_key(c); }

/* return hashing value for identifier s (analyseur is s = NULL) */
long
hashvalue(char *s)
{
  long update, n = 0;

  if (!s) { s = analyseur; update = 1; } else update = 0;
  while (is_key(*s)) { n = (n<<1) ^ *s; s++; }
  if (update) analyseur = s;
  if (n < 0) n = -n;
  return n % functions_tblsz;
}

/* Looking for entry in hashtable. ep1 is the cell's first element */
static entree *
findentry(char *name, long len, entree *ep1)
{
  entree *ep;

  for (ep = ep1; ep; ep = ep->next)
    if (!strncmp(ep->name, name, len) && !(ep->name)[len]) return ep;

  if (foreignAutoload) /* Try to autoload. */
    return foreignAutoload(name, len);
  return NULL; /* not found */
}

entree *
is_entry(char *s)
{
  return is_entry_intern(s,functions_hash,NULL);
}

entree *
is_entry_intern(char *s, entree **table, long *pthash)
{
  char *old = analyseur;
  long hash, len;

  analyseur = s; hash = hashvalue(NULL);
  len = analyseur - s; analyseur = old;
  if (pthash) *pthash = hash;
  return findentry(s,len,table[hash]);
}

int
is_identifier(char *s)
{
  while (*s && is_keyword_char(*s)) s++;
  return *s? 0: 1;
}

static entree *
installep(void *f, char *name, int len, int valence, int add, entree **table)
{
  entree *ep = (entree *) gpmalloc(sizeof(entree) + add + len+1);
  const entree *ep1 = initial_value(ep);
  char *u = (char *) ep1 + add;

  ep->name    = u; strncpy(u, name,len); u[len]=0;
  ep->args    = INITIAL; /* necessary, see var_cell definition */
  ep->help = NULL; ep->code = NULL;
  ep->value   = f? f: (void *) ep1;
  ep->next    = *table;
  ep->valence = valence;
  ep->menu    = 0;
  return *table = ep;
}

long
manage_var(long n, entree *ep)
{
  static long max_avail = MAXVARN; /* first user variable not yet used */
  static long nvar; /* first GP free variable */
  long var;
  GEN p;

  if (n) /* special behaviour */
  {
    switch(n)
    {
      case 2: return nvar=0;
      case 3: return nvar;
      case 4: return max_avail;
      case 5:
      {
        long v = (long)ep;
        if (v != nvar-1) err(talker,"can't pop gp variable");
        setlg(polvar, nvar);
        return --nvar;
      }
    }

    /* user wants to delete one of his/her/its variables */
    if (max_avail == MAXVARN-1) return 0; /* nothing to delete */
    free(polx[++max_avail]); /* frees both polun and polx */
    return max_avail+1;
  }

  if (nvar == max_avail) err(talker2,"no more variables available",
                             mark.identifier, mark.start);
  if (ep)
  {
    p = (GEN)ep->value;
    var=nvar++;
  }
  else
  {
    p = (GEN) gpmalloc(7*sizeof(long));
    var=max_avail--;
  }

  /* create polx[var] */
  p[0] = evaltyp(t_POL) | evallg(4);
  p[1] = evalsigne(1) | evallgef(4) | evalvarn(var);
  p[2] = zero; p[3] = un;
  polx[var] = p;

  /* create polun[nvar] */
  p += 4;
  p[0] = evaltyp(t_POL) | evallg(3);
  p[1] = evalsigne(1) | evallgef(3) | evalvarn(var);
  p[2] = un;
  polun[var] = p;

  varentries[var] = ep;
  if (ep) { polvar[nvar] = (long) ep->value; setlg(polvar, nvar+1); }
  return var;
}

long
fetch_var(void)
{
  return manage_var(0,NULL);
}

entree *
fetch_named_var(char *s, int doerr)
{
  entree *ep = is_entry(s);
  if (ep)
  {
    if (doerr) err(talker,"identifier already in use: %s", s);
    return ep;
  }
  ep = installep(NULL,s,strlen(s),EpVAR, 7*sizeof(long),
                 functions_hash + hashvalue(s));
  (void)manage_var(0,ep); return ep;
}

long
fetch_user_var(char *s)
{
  entree *ep = is_entry(s);
  gpmem_t av;
  GEN p1;

  if (ep)
  {
    switch (EpVALENCE(ep))
    {
      case EpVAR: case EpGVAR:
        return varn(initial_value(ep));
    }
    err(talker, "%s already exists with incompatible valence", s);
  }
  av=avma; p1 = lisexpr(s); avma=av;
  return varn(p1);
}

void
delete_named_var(entree *ep)
{
  (void)manage_var(5, (entree*)varn(initial_value(ep)));
  kill0(ep);
}

long
delete_var(void)
{
  return manage_var(1,NULL);
}

void
name_var(long n, char *s)
{
  entree *ep;
  char *u;

  if (n < manage_var(3,NULL))
    err(talker, "renaming a GP variable is forbidden");
  if (n > MAXVARN)
    err(talker, "variable number too big");

  ep = (entree*)gpmalloc(sizeof(entree) + strlen(s) + 1);
  u = (char *)initial_value(ep);
  ep->valence = EpVAR;
  ep->name = u; strcpy(u,s);
  ep->value = gzero; /* in case geval would be called */
  if (varentries[n]) free(varentries[n]);
  varentries[n] = ep;
}

/* Find entry or create it */
static entree *
entry(void)
{
  char *old = analyseur;
  const long hash = hashvalue(NULL), len = analyseur - old;
  entree *ep = findentry(old,len,functions_hash[hash]);
  long val,n;

  if (ep) return ep;
  if (compatible == WARN)
  {
    ep = findentry(old,len,funct_old_hash[hash]);
    if (ep) return ep; /* the warning was done in skipentry() */
  }
  /* ep does not exist. Create it */
  if (*analyseur == '(')
    { n=0; val=EpNEW; }
  else
    { n=7*sizeof(long); val=EpVAR; }
  ep = installep(NULL,old,len,val,n, functions_hash + hash);

  if (n) (void)manage_var(0,ep); /* Variable */
  return ep;
}

/********************************************************************/
/**                                                                **/
/**                          SKIP FUNCTIONS                        **/
/**                                                                **/
/********************************************************************/
/* as skipseq without modifying analyseur && al */
static void
doskipseq(char *c, int strict)
{
  char *olds = analyseur;

  mark.start = c; analyseur = c; skipseq();
  if (*analyseur)
  {
    char *s;
    long L,n;
    if (strict) err(talker2,"unused characters", analyseur, c);
    L = term_width();
    n = 2 * L - (17+19+1); /* Warning + unused... + . */
    if (strlen(analyseur) > n)
    {
      s = gpmalloc(n + 1);
      n -= 5;
      (void)strncpy(s,analyseur, n);
      s[n] = 0; strcat(s,"[+++]");
    }
    else s = pari_strdup(analyseur);
    err(warner, "unused characters: %s", s);
    free(s);
  }
  analyseur = olds;
}

/* skip any number of concatenated strings */
static void
skipstring()
{
  match('"');
  while (*analyseur)
    switch (*analyseur++)
    {
      case '"': if (*analyseur != '"') return;
      /* fall through */
      case '\\': analyseur++;
    }
  match('"');
}

static void
skip_matrix_block()
{
  while (*analyseur == '[')
  {
    analyseur++;
    if (*analyseur == ',') { analyseur++; skipexpr(); }
    else
    {
      skipexpr();
      if (*analyseur == ',')
	if (*++analyseur != ']') skipexpr();
    }
    match(']');
  }
}

/* return 1 if we would be assigning some value after expansion. 0 otherwise.
 * Skip all chars corresponding to the assignment (and assigned value) */
static int
skip_affect_block()
{
  if (*analyseur == '=')
  {
    if (analyseur[1] != '=') { analyseur++; skipexpr(); return 1; }
  }
  else if (double_op()) return 1;
  else if (get_op_fun()) { skipexpr(); return 1; }
  return 0;
}

static void
skipseq(void)
{
  for(;;)
  {
    while (separe(*analyseur)) analyseur++;
    if (*analyseur == ',' || *analyseur == ')' || !*analyseur) return;
    skipexpr(); if (!separe(*analyseur)) return;
  }
}

static void
skipexpr(void)
{
  int e1 = 0, e2 = 0, e3;

L3:
  e3=1; skipfacteur();
  switch(*analyseur)
  {
    case '*': case '/': case '%':
      analyseur++; goto L3;
    case '\\':
      if (*++analyseur == '/') analyseur++;
      goto L3;
    case '<': case '>':
      if (analyseur[1]==*analyseur) { analyseur +=2; goto L3; }
  }

L2:
  if (!e3) goto L3;
  e3=0; e2=1;
  switch(*analyseur)
  {
    case '+': case '-':
      analyseur++; goto L3;
  }

L1:
  if (!e2) goto L2;
  e2=0; e1=1;
  switch(*analyseur)
  {
    case '<':
      switch(*++analyseur)
      {
        case '=': case '>': analyseur++;
      }
      goto L2;

    case '>':
      if (*++analyseur == '=') analyseur++;
      goto L2;

    case '=': case '!':
      if (analyseur[1] == '=') { analyseur+=2; goto L2; }
      goto L1;
  }

/* L0: */
  if (!e1) goto L1;
  e1=0;
  switch(*analyseur)
  {
    case '&':
      if (*++analyseur == '&') analyseur++;
      goto L1;
    case '|':
      if (*++analyseur == '|') analyseur++;
      goto L1;
  }
}

static void
skipfacteur(void)
{
  if (*analyseur == '+' || *analyseur == '-') analyseur++;
  skiptruc();
  for(;;)
    switch(*analyseur)
    {
      case '.':
	analyseur++; while (isalnum((int)*analyseur)) analyseur++;
        if (*analyseur == '=' && analyseur[1] != '=')
          { analyseur++; skipseq(); }
        break;
      case '^':
	analyseur++; skipfacteur(); break;
      case '~': case '\'':
	analyseur++; break;
      case '[':
      {
        char *old;
	skip_matrix_block(); old = analyseur;
        if (skip_affect_block()) err(caracer1,old,mark.start);
        break;
      }
      case '!':
	if (analyseur[1] != '=') { analyseur++; break; }
      default: return;
    }
}

/* return the number of elements we need to read if array/matrix */
static void
skiptruc(void)
{
  long i,m,n;
  char *old;

  switch(*analyseur)
  {
    case '"': skipstring(); return;
    case '!': case '#': analyseur++; skipfacteur(); return;
    case '&': case '\'':
      analyseur++; check_var_name();
      (void)skipentry(); return;
  }
  if (isalpha((int)*analyseur)) { skipidentifier(); return; }
  if (isdigit((int)*analyseur) || *analyseur== '.') { skipconstante(); return; }
  switch(*analyseur++)
  {
    case '(':
      skipexpr(); match(')'); return;
    case '[':
      old = analyseur-1;
      if (*analyseur == ';' && analyseur[1] == ']')  /* [;] */
        { analyseur+=2; return; }
      n = 0;
      if (*analyseur != ']')
      {
	do { n++; skipexpr(); old=analyseur; } while (*analyseur++ == ',');
	analyseur--;
      }
      switch (*analyseur)
      {
	case ']': analyseur++; return;
	case ';': analyseur++;
          for (m=2; ; m++)
          {
            for (i=1; i<n; i++) { skipexpr(); match(','); }
            skipexpr();
            if (*analyseur == ']') break;
            match(';');
          }
          analyseur++; return;
	default:
	  err(talker2,"; or ] expected",old,mark.start);
      }
    case '%':
      if (*analyseur == '`') { while (*++analyseur == '`') /*empty*/; return; }
      (void)number(&n); return;
  }
  err(caracer1,analyseur-1,mark.start);
}

static void
check_var()
{
  char *old = analyseur;
  check_var_name();
  switch(EpVALENCE(skipentry()))
  {
    case EpVAR: break;
    case EpGVAR:
      err(talker2,"global variable not allowed", old,mark.start);
    default: err(varer1,old,mark.start);
  }
}

static void
check_matcell()
{
  char *old = analyseur;
  check_var_name();
  switch(EpVALENCE(skipentry()))
  {
    case EpVAR:
    case EpGVAR: break;
    default: err(varer1,old,mark.start);
  }
  skip_matrix_block();
}

static void
skipidentifier(void)
{
  int matchcomma=0;
  entree *ep;
  char *old;

  mark.identifier = analyseur; ep = do_alias(skipentry());
  if (ep->code)
  {
    char *s = ep->code;

    if (*analyseur == '\'') analyseur++;
    if (*analyseur != '(')
    {
      if (EpVALENCE(ep) == 0) return; /* no mandatory argument */
      match('('); /* ==> error */
    }
    analyseur++;

    /* Optimized for G and p. */
    while (*s == 'G') { match_comma(); skipexpr(); s++; }
    if (*s == 'p') s++;
    while (*s) switch (*s++)
    {
      case 'G': case 'n': case 'L':
        match_comma();
        if (*analyseur == ',' || *analyseur == ')') break;
        skipexpr(); break;
      case 'E':
        match_comma(); skipexpr(); break;
      case 'I':
        match_comma(); skipseq(); break;
      case 'r':
        match_comma();
        while (*analyseur)
        {
          if (*analyseur == '"') skipstring();
          if (*analyseur == ',' || *analyseur == ')') break;
          analyseur++;
        }
        break;
      case 's':
        match_comma();
        if (*s == '*')
        {
          while (*analyseur)
          {
            if (*analyseur == '"') skipstring();
            if (*analyseur == ')') break;
            if (*analyseur == ',') analyseur++;
            else skipexpr();
          }
          s++;
          break;
        }

        while (*analyseur)
        {
          if (*analyseur == '"') skipstring();
          if (*analyseur == ',' || *analyseur == ')') break;
          skipexpr();
        }
        break;

      case 'S': match_comma();
        check_var_name(); (void)skipentry(); break;
      case '&': match_comma(); match('&'); check_matcell(); break;
      case 'V': match_comma(); check_var(); break;

      case 'p': case 'P': case 'l': case 'v': case 'f': case 'x':
        break;

      case 'D':
        if ( *analyseur == ')' ) { analyseur++; return; }
        if (*s == 'G' || *s == '&' || *s == 'n' || *s == 'I' || *s == 'V')
          break;
        while (*s++ != ',');
        break;
      case '=':
        match('='); matchcomma = 0; break;
      case ',':
        matchcomma=1; break;
      default:
        err(bugparier,"skipidentifier (unknown code)");
    }
    match(')');
    return;
  }
  if (EpPREDEFINED(ep))
  {
    if (*analyseur != '(')
    {
      switch(EpVALENCE(ep))
      {
        case 0:
        case 88: return;
      }
      match('('); /* error */
    }
    analyseur++;
    switch(EpVALENCE(ep))
    {
      case 50: skiptruc();
	if (*analyseur == '^') { analyseur++; skipfacteur(); };
	break;
      case 80: skipexpr(); match(','); skipseq();
          if (*analyseur != ')') { match(','); skipseq(); }
	  break;
      case 81: case 82: skipexpr(); match(','); skipseq(); break;
      case 88:
        while (*analyseur != ')') { match_comma(); skipexpr(); };
        break;
      default: err(valencer1);
    }
    match(')'); return;
  }
  switch (EpVALENCE(ep))
  {
    case EpGVAR:
    case EpVAR: /* variables */
      skip_matrix_block(); (void)skip_affect_block(); return;

    case EpUSER: /* fonctions utilisateur */
    {
      char *ch1 = analyseur;
      gp_args *f;
      int i;

      if (*analyseur == '\'') analyseur++;
      if (*analyseur != '(')
      {
	if ( *analyseur != '='  ||  analyseur[1] == '=' ) return;
	match('('); /* error */
      }
      f = (gp_args*)ep->args;
      analyseur++;  /* skip '(' */
      for (i = f->nloc + f->narg; i; i--)
      {
	if (do_switch(0,matchcomma))
          matchcomma = 1;
	else { match_comma(); skipexpr(); skipdecl(); }
      }

      if (*analyseur == ')')
	if ( analyseur[1] != '=' || analyseur[2] == '=' )
	  { analyseur++; return; }

      /* here we are redefining a user function */
      old = analyseur;
      if (*analyseur != ',' && *analyseur != ')') skipexpr();
      while (*analyseur == ',') { analyseur++; skipexpr(); }
      match(')');

      if (*analyseur != '=' || analyseur[1] == '=')
      {
        if (skipping_fun_def) return;
        err(nparamer1,old,mark.start);
      }
      analyseur = ch1; matchcomma = 0;
      if (!redefine_fun) redefine_fun = analyseur;
    } /* fall through */

    case EpNEW: /* new function */
      if (check_new_fun && ! skipping_fun_def)
      {
	err_new_fun(); /* ep not created yet: no need to kill it */
	err(paramer1, mark.identifier, mark.start);
      }
      check_new_fun = NOT_CREATED_YET; match('(');
      while (*analyseur != ')') { match_comma(); skipexpr(); skipdecl(); };
      match(')');
      if (*analyseur == '=' && analyseur[1] != '=')
      {
	skipping_fun_def++;
	analyseur++; skipseq();
	skipping_fun_def--;
      }
      check_new_fun=NULL; return;

    default: err(valencer1);
  }
}

static void
skipconstante(void)
{
  while (isdigit((int)*analyseur)) analyseur++;
  if ( *analyseur!='.' && *analyseur!='e' && *analyseur!='E' ) return;
  if (*analyseur=='.')
  {
    if (isalpha((int)analyseur[1])
        && analyseur[1] != 'e' && analyseur[1] != 'E')
      return; /* member function */
    analyseur++;
  }
  while (isdigit((int)*analyseur)) analyseur++;
  if ( *analyseur=='e'  ||  *analyseur=='E' )
  {
    analyseur++;
    if ( *analyseur=='+' || *analyseur=='-' ) analyseur++;
    while (isdigit((int)*analyseur)) analyseur++;
  }
}

static entree *
skipentry(void)
{
  static entree fakeEpNEW = { "",EpNEW };
  static entree fakeEpVAR = { "",EpVAR };
  char *old = analyseur;
  const long hash = hashvalue(NULL), len = analyseur - old;
  entree *ep = findentry(old,len,functions_hash[hash]);

  if (ep) return ep;
  if (compatible == WARN)
  {
    ep = findentry(old,len,funct_old_hash[hash]);
    if (ep)
    {
      err(warner,"using obsolete function %s",ep->name);
      return ep;
    }
  }
  return (*analyseur == '(') ? &fakeEpNEW : &fakeEpVAR;
}

/********************************************************************/
/**                                                                **/
/**                          MEMBER FUNCTIONS                      **/
/**                                                                **/
/********************************************************************/
#define is_ell(x) (typ(x) == t_VEC && lg(x)>=14)
#define is_bigell(x) (typ(x) == t_VEC && lg(x)>=20)
static GEN
e(GEN x)
{
  x = get_primeid(x);
  if (!x) err(member,"e",mark.member,mark.start);
  return (GEN)x[3];
}

static GEN
f(GEN x)
{
  x = get_primeid(x);
  if (!x) err(member,"f",mark.member,mark.start);
  return (GEN)x[4];
}

static GEN
p(GEN x)
{
  int t; (void)get_nf(x,&t);
  if (t == typ_GAL)
    return gmael(x,2,1);
  x = get_primeid(x);
  if (!x) err(member,"p",mark.member,mark.start);
  return (GEN)x[1];
}

static GEN
bnf(GEN x)
{
  int t; x = get_bnf(x,&t);
  if (!x) err(member,"bnf",mark.member,mark.start);
  return x;
}

static GEN
nf(GEN x)
{
  int t; x = get_nf(x,&t);
  if (!x) err(member,"nf",mark.member,mark.start);
  return x;
}

/* integral basis */
static GEN
zk(GEN x)
{
  int t; GEN y = get_nf(x,&t);
  if (!y)
  {
    switch(t)
    {
      case typ_CLA: return gmael(x,1,4);
      case typ_Q: y = cgetg(3,t_VEC);
        y[1]=un; y[2]=lpolx[varn(x[1])]; return y;
    }
    err(member,"zk",mark.member,mark.start);
  }
  return (GEN)y[7];
}

static GEN
disc(GEN x) /* discriminant */
{
  int t; GEN y = get_nf(x,&t);
  if (!y)
  {
    switch(t)
    {
      case typ_Q  : return discsr((GEN)x[1]);
      case typ_CLA:
        x = gmael(x,1,3);
        if (typ(x) != t_VEC || lg(x) != 3) break;
        return (GEN)x[1];
      case typ_ELL: return (GEN)x[12];
    }
    err(member,"disc",mark.member,mark.start);
  }
  return (GEN)y[3];
}

static GEN
pol(GEN x) /* polynomial */
{
  int t; GEN y = get_nf(x,&t);
  if (!y)
  {
    switch(t)
    {
      case typ_CLA: return gmael(x,1,1);
      case typ_POL: return x;
      case typ_Q  : return (GEN)x[1];
      case typ_GAL: return (GEN)x[1];
    }
    if (typ(x)==t_POLMOD) return (GEN)x[2];
    err(member,"pol",mark.member,mark.start);
  }
  return (GEN)y[1];
}

static GEN
mod(GEN x) /* modulus */
{
  int t; (void)get_nf(x,&t);
  if (t == typ_GAL)
    return gmael(x,2,3);
  switch(typ(x))
  {
    case t_INTMOD: case t_POLMOD: case t_QUAD: break;
    default: err(member,"mod",mark.member,mark.start);
  }
  return (GEN)x[1];
}

static GEN
sign(GEN x) /* signature */
{
  int t; GEN y = get_nf(x,&t);
  if (!y)
  {
    if (t == typ_CLA) return gmael(x,1,2);
    err(member,"sign",mark.member,mark.start);
  }
  return (GEN)y[2];
}

/* x assumed to be output by get_nf: ie a t_VEC with length 11 */
static GEN
nfmats(GEN x)
{
  GEN y;
  if (!x) return NULL;
  y = (GEN)x[5];
  if (typ(y) == t_VEC && lg(y) != 8) return NULL;
  return y;
}

static GEN
t2(GEN x) /* T2 matrix */
{
  int t; x = nfmats(get_nf(x,&t));
  if (!x) err(member,"t2",mark.member,mark.start);
  return gram_matrix((GEN)x[2]);
}

static GEN
diff(GEN x) /* different */
{
  int t; x = nfmats(get_nf(x,&t));
  if (!x) err(member,"diff",mark.member,mark.start);
  return (GEN)x[5];
}

static GEN
codiff(GEN x) /* codifferent */
{
  int t; GEN y = nfmats(get_nf(x,&t));
  if (!y) err(member,"codiff",mark.member,mark.start);
  return gdiv((GEN)y[6], absi((GEN)x[3]));
}

static GEN
mroots(GEN x) /* roots */
{
  int t; GEN y = get_nf(x,&t);
  if (!y)
  {
    if (t == typ_ELL && is_bigell(x)) return (GEN)x[14];
    if (t == typ_GAL) return (GEN)x[3];
    err(member,"roots",mark.member,mark.start);
  }
  return (GEN)y[6];
}

/* assume x output by get_bnf: ie a t_VEC with length 10 */
static GEN
check_RES(GEN x, char *s)
{
  GEN y = (GEN)x[8];
  if (typ(y) != t_VEC || lg(y) < 4)
    err(member,s,mark.member,mark.start);
  return y;
}

static GEN
clgp(GEN x) /* class group (3-component row vector) */
{
  int t; GEN y = get_bnf(x,&t);
  if (!y)
  {
    switch(t)
    {
      case typ_QUA:
        y = cgetg(4,t_VEC);
        for(t=1; t<4; t++) y[t] = x[t];
        return y;
      case typ_CLA: return gmael(x,1,5);
    }
    if (typ(x)==t_VEC)
      switch(lg(x))
      {
        case 3: /* no gen */
        case 4: return x;
      }
    err(member,"clgp",mark.member,mark.start);
  }
  if (t==typ_BNR) return (GEN)x[5];
  y = check_RES(y, "clgp");
  return (GEN)y[1];
}

static GEN
reg(GEN x) /* regulator */
{
  int t; GEN y = get_bnf(x,&t);
  if (!y)
  {
    switch(t)
    {
      case typ_CLA: return gmael(x,1,6);
      case typ_QUA: return (GEN)x[4];
    }
    err(member,"reg",mark.member,mark.start);
  }
  if (t == typ_BNR) err(impl,"ray regulator");
  y = check_RES(y, "reg");
  return (GEN)y[2];
}

static GEN
fu(GEN x) /* fundamental units */
{
  int t; GEN y = get_bnf(x,&t);
  if (!y)
  {
    switch(t)
    {
      case typ_CLA: x = (GEN)x[1]; if (lg(x)<11) break;
        return (GEN)x[9];
      case typ_Q:
        x = discsr((GEN)x[1]);
        return (signe(x)<0)? cgetg(1,t_VEC): fundunit(x);
    }
    err(member,"fu",mark.member,mark.start);
  }
  if (t == typ_BNR) err(impl,"ray units");
  return check_units(y,".fu");
}

/* torsion units. return [w,e] where w is the number of roots of 1, and e a
 * polymod generator */
static GEN
tu(GEN x)
{
  int t; GEN y = get_bnf(x,&t), res = cgetg(3,t_VEC);
  if (!y)
  {
    switch(t)
    {
      case typ_Q:
        y = discsr((GEN)x[1]);
        if (signe(y)<0 && cmpis(y,-4)>=0)
          y = stoi((itos(y) == -4)? 4: 6);
        else
        { y = gdeux; x=negi(gun); }
        res[1] = (long)y;
        res[2] = (long)x; return res;
      case typ_CLA:
        if (lg(x[1])==11)
        {
          x = (GEN) x[1]; y=(GEN)x[8];
          if (typ(y) == t_VEC || lg(y) == 3) break;
        }
      default: err(member,"tu",mark.member,mark.start);
    }
  }
  else
  {
    if (t == typ_BNR) err(impl,"ray torsion units");
    x = (GEN)y[7]; y=(GEN)y[8];
    if (typ(y) == t_VEC && lg(y) > 5) y = (GEN)y[4];
    else
    {
      y = rootsof1(x);
      y[2] = lmul((GEN)x[7], (GEN)y[2]);
    }
  }
  res[2] = y[2];
  res[1] = y[1]; return res;
}

static GEN
futu(GEN x) /*  concatenation of fu and tu, w is lost */
{
  GEN fuc = fu(x);
  return concatsp(fuc, (GEN)tu(x)[2]);
}

static GEN
tufu(GEN x) /*  concatenation of tu and fu, w is lost */
{
  GEN fuc = fu(x);
  return concatsp((GEN)tu(x)[2], fuc);
}

static GEN
zkst(GEN bid)
/* structure of (Z_K/m)^*, where bid is an idealstarinit (with or without gen)
   or a bnrinit (with or without gen) */
{
  if (typ(bid)==t_VEC)
    switch(lg(bid))
    {
      case 6: return (GEN) bid[2];   /* idealstarinit */
      case 7: bid = (GEN)bid[2]; /* bnrinit */
        if (typ(bid) == t_VEC && lg(bid) > 2)
          return (GEN)bid[2];
    }
  err(member,"zkst",mark.member,mark.start);
  return NULL; /* not reached */
}

static GEN
no(GEN clg) /* number of elements of a group (of type clgp) */
{
  clg = clgp(clg);
  if (typ(clg)!=t_VEC  || (lg(clg)!=3 && lg(clg)!=4))
    err(member,"no",mark.member,mark.start);
  return (GEN) clg[1];
}

static GEN
cyc(GEN clg) /* cyclic decomposition (SNF) of a group (of type clgp) */
{
  clg = clgp(clg);
  if (typ(clg)!=t_VEC  || (lg(clg)!=3 && lg(clg)!=4))
    err(member,"cyc",mark.member,mark.start);
  return (GEN) clg[2];
}

/* SNF generators of a group (of type clgp), or generators of a prime
 * ideal
 */
static GEN
gen(GEN x)
{
  int t;
  GEN y = get_primeid(x);
  if (y)
  {
    x = cgetg(3,t_VEC);
    x[1] = y[1];
    x[2] = y[2]; return x;
  }
  (void)get_nf(x,&t);
  if (t == typ_GAL)
    return (GEN)x[7];
  x = clgp(x);
  if (typ(x)!=t_VEC || lg(x)!=4)
    err(member,"gen",mark.member,mark.start);
  if (typ(x[1]) == t_COL) return (GEN)x[2]; /* from bnfisprincipal */
  return (GEN) x[3];
}
static GEN
group(GEN x)
{
  int t; (void)get_nf(x,&t);
  if (t == typ_GAL)
    return (GEN)x[6];
  err(member,"group",mark.member,mark.start);
  return NULL; /* not reached */
}
static GEN
orders(GEN x)
{
  int t; (void)get_nf(x,&t);
  if (t == typ_GAL)
    return (GEN)x[8];
  err(member,"orders",mark.member,mark.start);
  return NULL; /* not reached */
}

static GEN
a1(GEN x)
{
  if (!is_ell(x)) err(member,"a1",mark.member,mark.start);
  return (GEN)x[1];
}

static GEN
a2(GEN x)
{
  if (!is_ell(x)) err(member,"a2",mark.member,mark.start);
  return (GEN)x[2];
}

static GEN
a3(GEN x)
{
  if (!is_ell(x)) err(member,"a3",mark.member,mark.start);
  return (GEN)x[3];
}

static GEN
a4(GEN x)
{
  if (!is_ell(x)) err(member,"a4",mark.member,mark.start);
  return (GEN)x[4];
}

static GEN
a6(GEN x)
{
  if (!is_ell(x)) err(member,"a6",mark.member,mark.start);
  return (GEN)x[5];
}

static GEN
b2(GEN x)
{
  if (!is_ell(x)) err(member,"b2",mark.member,mark.start);
  return (GEN)x[6];
}

static GEN
b4(GEN x)
{
  if (!is_ell(x)) err(member,"b4",mark.member,mark.start);
  return (GEN)x[7];
}

static GEN
b6(GEN x)
{
  if (!is_ell(x)) err(member,"b6",mark.member,mark.start);
  return (GEN)x[8];
}

static GEN
b8(GEN x)
{
  if (!is_ell(x)) err(member,"b8",mark.member,mark.start);
  return (GEN)x[9];
}

static GEN
c4(GEN x)
{
  if (!is_ell(x)) err(member,"c4",mark.member,mark.start);
  return (GEN)x[10];
}

static GEN
c6(GEN x)
{
  if (!is_ell(x)) err(member,"c6",mark.member,mark.start);
  return (GEN)x[11];
}

static GEN
j(GEN x)
{
  if (!is_ell(x)) err(member,"j",mark.member,mark.start);
  return (GEN)x[13];
}

static GEN
momega(GEN x)
{
  GEN y;

  if (!is_bigell(x)) err(member,"omega",mark.member,mark.start);
  if (gcmp0((GEN)x[19])) err(talker,"curve not defined over R");
  y=cgetg(3,t_VEC); y[1]=x[15]; y[2]=x[16];
  return y;
}

static GEN
meta(GEN x)
{
  GEN y;

  if (!is_bigell(x)) err(member,"eta",mark.member,mark.start);
  if (gcmp0((GEN)x[19])) err(talker,"curve not defined over R");
  y=cgetg(3,t_VEC); y[1]=x[17]; y[2]=x[18];
  return y;
}

static GEN
area(GEN x)
{
  if (!is_bigell(x)) err(member,"area",mark.member,mark.start);
  if (gcmp0((GEN)x[19])) err(talker,"curve not defined over R");
  return (GEN)x[19];
}

static GEN
tate(GEN x)
{
  GEN z = cgetg(3,t_VEC);
  if (!is_bigell(x)) err(member,"tate",mark.member,mark.start);
  if (!gcmp0((GEN)x[19])) err(talker,"curve not defined over a p-adic field");
  z[1]=x[15];
  z[2]=x[16];
  z[3]=x[17]; return z;
}

static GEN
w(GEN x)
{
  if (!is_bigell(x)) err(member,"w",mark.member,mark.start);
  if (!gcmp0((GEN)x[19])) err(talker,"curve not defined over a p-adic field");
  return (GEN)x[18];
}

/*
 * Only letters and digits in member names. AT MOST 8 of THEM
 * (or modify gp_rl.c::pari_completion)
 */
entree gp_member_list[] = {
{"a1",0,(void*)a1},
{"a2",0,(void*)a2},
{"a3",0,(void*)a3},
{"a4",0,(void*)a4},
{"a6",0,(void*)a6},
{"area",0,(void*)area},
{"b2",0,(void*)b2},
{"b4",0,(void*)b4},
{"b6",0,(void*)b6},
{"b8",0,(void*)b8},
{"bnf",0,(void*)bnf},
{"c4",0,(void*)c4},
{"c6",0,(void*)c6},
{"clgp",0,(void*)clgp},
{"codiff",0,(void*)codiff},
{"cyc",0,(void*)cyc},
{"diff",0,(void*)diff},
{"disc",0,(void*)disc},
{"e",0,(void*)e},
{"eta",0,(void*)meta},
{"f",0,(void*)f},
{"fu",0,(void*)fu},
{"futu",0,(void*)futu},
{"gen",0,(void*)gen},
{"group",0,(void*)group},
{"j",0,(void*)j},
{"mod",0,(void*)mod},
{"nf",0,(void*)nf},
{"no",0,(void*)no},
{"omega",0,(void*)momega},
{"orders",0,(void*)orders},
{"p",0,(void*)p},
{"pol",0,(void*)pol},
{"reg",0,(void*)reg},
{"roots",0,(void*)mroots},
{"sign",0,(void*)sign},
{"tate",0,(void*)tate},
{"t2",0,(void*)t2},
{"tu",0,(void*)tu},
{"tufu",0,(void*)tufu},
{"w",0,(void*)w},
{"zk",0,(void*)zk},
{"zkst",0,(void*)zkst},
{NULL,0,NULL}
};

static entree*
find_member()
{
  char *old = analyseur;
  const long hash = hashvalue(NULL), len = analyseur - old;
  return findentry(old,len,members_hash[hash]);
}

static GEN
read_member(GEN x)
{
  entree *ep;

  mark.member = analyseur;
  ep = find_member();
  if (ep)
  {
    if (*analyseur == '=' && analyseur[1] != '=')
    {
      if (EpPREDEFINED(ep))
        err(talker2,"can't modify a pre-defined member: ",
            mark.member,mark.start);
      gunclone((GEN)ep->value); return NULL;
    }
    if (EpVALENCE(ep) == EpMEMBER)
      return call_member((GEN)ep->value, x);
    else
    {
      GEN y = ((F1GEN)ep->value)(x);
      if (isonstack(y)) y = gcopy(y);
      return y;
    }
  }
  if (*analyseur != '=' || analyseur[1] == '=')
    err(talker2,"unknown member function",mark.member,mark.start);
  return NULL; /* to be redefined */
}

/********************************************************************/
/**                                                                **/
/**                        SIMPLE GP FUNCTIONS                     **/
/**                                                                **/
/********************************************************************/

long
loop_break()
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

long
did_break() { return br_status; }

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
    err(talker2,"positive integer expected",mark.identifier,mark.start);
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
    err(talker2,"positive integer expected",mark.identifier,mark.start);
  br_count = n;
  br_status = br_BREAK; return NULL;
}

void
alias0(char *s, char *old)
{
  entree *ep, *e;
  long hash;
  GEN x;

  ep = is_entry(old);
  if (!ep) err(talker2,"unknown function",mark.raw,mark.start);
  switch(EpVALENCE(ep))
  {
    case EpVAR: case EpGVAR:
      err(talker2,"only functions can be aliased",mark.raw,mark.start);
  }

  if ( (e = is_entry_intern(s, functions_hash, &hash)) )
  {
    if (EpVALENCE(e) != EpALIAS)
      err(talker2,"can't replace an existing symbol by an alias",
          mark.raw, mark.start);
    kill0(e);
  }
  ep = do_alias(ep); x = newbloc(2);
  x[0] = evaltyp(t_STR)|evallg(2); /* for getheap */
  x[1] = (long)ep;
  (void)installep(x, s, strlen(s), EpALIAS, 0, functions_hash + hash);
}

/* Try f (trapping error e), recover using r (break_loop, if NULL) */
GEN
trap0(char *e, char *r, char *f)
{
  VOLATILE gpmem_t av = avma;
  VOLATILE long numerr = -1;
  VOLATILE GEN x = gnil;
  char *F;
       if (!strcmp(e,"errpile")) numerr = errpile;
  else if (!strcmp(e,"typeer")) numerr = typeer;
  else if (!strcmp(e,"gdiver2")) numerr = gdiver2;
  else if (!strcmp(e,"invmoder")) numerr = invmoder;
  else if (!strcmp(e,"accurer")) numerr = accurer;
  else if (!strcmp(e,"archer")) numerr = archer;
  else if (*e) err(impl,"this trap keyword");
  /* TO BE CONTINUED */

  if (f && r)
  { /* explicit recovery text */
    char *a = analyseur;
    void *catcherr;
    jmp_buf env;

    if (setjmp(env))
    {
      avma = av;
      err_leave(&catcherr);
      x = lisseq(r);
      skipseq();
    }
    else
    {
      catcherr = err_catch(numerr, env, NULL);
      x = lisseq(f);
      err_leave(&catcherr);
    }
    analyseur = a;
    return x;
  }

  F = f? f: r; /* define a default handler */
 /* default will execute F (or start a break loop), then jump to
  * environnement */
  if (F)
  {
    if (!*F || (*F == '"' && F[1] == '"')) /* unset previous handler */
    {/* TODO: find a better interface
      * TODO: no leaked handler from the library should have survived
      */
      err_leave_default(numerr);
      return x;
    }
    F = pari_strdup(F);
  }
  (void)err_catch(numerr, NULL, F);
  return x;
}

