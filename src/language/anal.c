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

extern void killsubblocs(GEN x);

static GEN    constante();
static GEN    expr();
static GEN    facteur();
static GEN    identifier();
static GEN    read_member(GEN x);
static GEN    seq();
static GEN    truc();
static ulong  number(int *pn, char **ps);
static void   doskipseq(char *s, int strict);
static void   skipconstante();
static void   skipexpr();
static void   skipfacteur();
static void   skipidentifier();
static void   skipseq();
static void   skipstring();
static void   skiptruc();
static entree *entry();
static entree *skipentry(void);

static entree *installep(void *f,char *name,int l,int v,int add,entree **table);
#define VAR_POLS_LONGS		7	/* 4 words for polx, 3 for polun */
/* Is the name proper??? */
#define SIZEOF_VAR_POLS		(VAR_POLS_LONGS*sizeof(long))

extern int term_width(void);
extern GEN addumului(ulong a, ulong b, GEN Y);
extern GEN rpowsi(ulong a, GEN n, long prec);

/* last time we began parsing an object of specified type */
static struct
{
  char *identifier, *symbol, *raw, *member, *start;
} mark;

/* points to the part of the string that remains to be parsed */
static char *analyseur = NULL;

/* when non-0, we are checking the syntax of a new function body */
static long skipping_fun_def;

/* when non-NULL, points to the entree of a new user function (currently
 * being checked). Used by the compatibility engine in the following way:
 *   when user types in a function whose name has changed, it is understood
 *   as EpNEW; first syntax error (missing = after function definition
 *   usually) triggers err_new_fun() if check_new_fun is set. */
static entree *check_new_fun;

/* for control statements (check_break) */
static long br_status, br_count;
static GEN br_res = NULL;

/* Mnemonic codes parser:
 *
 * TEMPLATE is assumed to be ";"-separated list of items.  Each item
 * may have one of the following forms: id=value id==value id|value id&~value.
 * Each id consists of alphanum characters, dashes and underscores.
 * IDs are case-sensitive.

 * ARG consists of several IDs separated by punctuation (and optional
 * whitespace).  Each modifies the return value in a "natural" way: an
 * ID from id=value should be the first in the sequence and sets RETVAL to
 * VALUE (and cannot be negated), ID from id|value bit-ORs RETVAL with
 * VALUE (and bit-ANDs RETVAL with ~VALUE if negated), ID from
 * id&~value behaves as if it were noid|value, ID from
 * id==value behaves the same as id=value, but should come alone.

 * For items of the form id|value and id&~value negated forms are
 * allowed: either when arg looks like no[-_]id, or when id looks like
 * this, and arg is not-negated. */

enum { A_ACTION_ASSIGN, A_ACTION_SET, A_ACTION_UNSET };
enum { PARSEMNU_TEMPL_TERM_NL, PARSEMNU_ARG_WHITESP };
#define IS_ID(c)	(isalnum((int)c) || ((c) == '_') || ((c) == '-'))
#define ERR(reason)	STMT_START {	\
    if (failure && first) {		\
	*failure = reason; *failure_arg = NULL; return 0;		\
    } else err(talker,reason); } STMT_END
#define ERR2(reason,s)	STMT_START {	\
    if (failure && first) {		\
	*failure = reason; *failure_arg = s; return 0;		\
    } else err(talker,reason,s); } STMT_END

unsigned long
parse_option_string(char *arg, char *tmplate, long flag, char **failure, char **failure_arg)
{
    unsigned long retval = 0;
    char *etmplate = NULL;

    if (flag & PARSEMNU_TEMPL_TERM_NL)
	etmplate = strchr(tmplate, '\n');
    if (!etmplate)
	etmplate = tmplate + strlen(tmplate);

    if (failure)
	*failure = NULL;
    while (1) {
	long numarg;
	char *e, *id;
	char *negated;			/* action found with 'no'-ID */
	int negate;			/* Arg has 'no' prefix removed */
	unsigned int l, action = 0, first = 1, singleton = 0;
	char b[80], *buf, *inibuf;

	if (flag & PARSEMNU_ARG_WHITESP)
	    while (isspace((int)*arg)) arg++;
	if (!*arg)
	    break;
	e = arg;
	while (IS_ID(*e)) e++;
	/* Now the ID is whatever is between arg and e. */
	l = e - arg;
	if (l >= sizeof(b))
	    ERR("id too long in a stringified flag");
	if (!l)				/* Garbage after whitespace? */
	    ERR("a stringified flag does not start with an id");
	strncpy(b, arg, l);
	b[l] = 0;
	arg = e;
	e = inibuf = buf = b;
	while (('0' <= *e) && (*e <= '9'))
	    e++;
	if (*e == 0)
	    ERR("numeric id in a stringified flag");	
	negate = 0;
	negated = NULL;
      find:
	id = tmplate;
	while ((id = strstr(id, buf)) && id < etmplate) {
	    if (IS_ID(id[l])) {		/* We do not allow abbreviations yet */
		id += l;		/* False positive */
		continue;
	    }
	    if ((id >= tmplate + 2) && (IS_ID(id[-1]))) {
		char *s = id;

		if ( !negate && s >= tmplate+3
		     && ((id[-1] == '_') || (id[-1] == '-')) )
		    s--;
		/* Check whether we are preceeded by "no" */
		if ( negate		/* buf initially started with "no" */
		     || (s < tmplate+2) || (s[-1] != 'o') || (s[-2] != 'n')
		     || (s >= tmplate+3 && IS_ID(s[-3]))) {
		    id += l;		/* False positive */
		    continue;
		}
		/* Found noID in the template! */
		id += l;
		negated = id;
		continue;		/* Try to find without 'no'. */
	    }
	    /* Found as is */
	    id += l;
	    break;
	}
	if ( !id && !negated && !negate
	     && (l > 2) && buf[0] == 'n' && buf[1] == 'o' ) {
	    /* Try to find the flag without the prefix "no". */
	    buf += 2; l -= 2;
	    if ((buf[0] == '_') || (buf[0] == '-')) { buf++; l--; }
	    negate = 1;
	    if (buf[0])
		goto find;
	}
	if (!id && negated) {	/* Negated and AS_IS forms, prefer AS_IS */
	    id = negated;	/* Otherwise, use negated form */
	    negate = 1;
	}
	if (!id)
	    ERR2("Unrecognized id '%s' in a stringified flag", inibuf);
	if (singleton && !first)
	    ERR("Singleton id non-single in a stringified flag");
	if (id[0] == '=') {
	    if (negate)
		ERR("Cannot negate id=value in a stringified flag");
	    if (!first)
		ERR("Assign action should be first in a stringified flag");
	    action = A_ACTION_ASSIGN;
	    id++;
	    if (id[0] == '=') {
		singleton = 1;
		id++;
	    }
	} else if (id[0] == '^') {
	    if (id[1] != '~')
		err(talker, "Unrecognized action in a template");
	    id += 2;
	    if (negate)
		action = A_ACTION_SET;
	    else
		action = A_ACTION_UNSET;
	} else if (id[0] == '|') {
	    id++;
	    if (negate)
		action = A_ACTION_UNSET;
	    else
		action = A_ACTION_SET;
	}

	e = id;

	while ((*e >= '0' && *e <= '9')) e++;
	while (isspace((int)*e))
	    e++;
	if (*e && (*e != ';') && (*e != ','))
	    err(talker, "Non-numeric argument of an action in a template");
	numarg = atol(id);		/* Now it is safe to get it... */
	switch (action) {
	case A_ACTION_SET:
	    retval |= numarg;
	    break;
	case A_ACTION_UNSET:
	    retval &= ~numarg;
	    break;
	case A_ACTION_ASSIGN:
	    retval = numarg;
	    break;
	default:
	    ERR("error in parse_option_string");
	}
	first = 0;
	if (flag & PARSEMNU_ARG_WHITESP)
	    while (isspace((int)*arg))
		arg++;
	if (*arg && !(ispunct((int)*arg) && *arg != '-'))
	    ERR("Junk after an id in a stringified flag");
	/* Skip punctuation */
	if (*arg)
	    arg++;
    }
    return retval;
}

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
get_analyseur(void)
{
  return analyseur;
}

void
set_analyseur(char *s)
{
  analyseur = s;
}

/* Do not modify (analyseur,mark.start) */
static GEN
lisseq0(char *t, GEN (*f)(void))
{
  const pari_sp av = avma;
  char *olds = analyseur, *olde = mark.start;
  GEN res;

  if (foreignExprHandler && *t == foreignExprSwitch)
    return (*foreignExprHandler)(t);

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

/* for sumiter: (void)lisseq(t) */
void
lisseq_void(char *t)
{
  const pari_sp av = avma;
  char *olds = analyseur, *olde = mark.start;

  if (foreignExprHandler && *t == foreignExprSwitch)
  {
    (void)(*foreignExprHandler)(t); return; 
  }

  check_new_fun = NULL;
  skipping_fun_def = 0;
  mark.start = analyseur = t;

  br_status = br_NONE;
  if (br_res) { killbloc(br_res); br_res = NULL; }
  (void)seq();
  analyseur = olds; mark.start = olde;
  avma = av;
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
  GEN z;
  check_new_fun=NULL; skipping_fun_def=0;
  added_newline = 1;
  doskipseq(c, strict);
  z = lisseq0(c, seq);
  if (!added_newline) pariputc('\n'); /* last output was print1() */
  return z;
}

static void
check_proto(char *code)
{
  char *s = code, *old;
  if (*s == 'l' || *s == 'v' || *s == 'i') s++;
  while (*s && *s != '\n') switch (*s++)
  {
    case '&':
    case '=':
    case 'E':
    case 'G':
    case 'I':
    case 'L':
    case 'M':
    case 'P':
    case 'S':
    case 'V':
    case 'f':
    case 'n':
    case 'p':
    case 'r':
    case 'x': break;
    case 's':
      if (*s == '*') s++;
      break;
    case 'D':
      if (*s == 'G' || *s == '&' || *s == 'n' || *s == 'I' || *s == 'V')
      {
        s++; break;
      }
      old = s; while (*s != ',') s++;
      if (*s != ',') err(talker2, "missing comma", old, code);
      break;
    case ',': break;
    case '\n': return; /* Before the mnemonic */

    case 'l':
    case 'i':
    case 'v': err(talker2, "this code has to come first", s-1, code);
    default: err(talker2, "unknown parser code", s-1, code);
  }
}

entree *
install(void *f, char *name, char *code)
{
  long hash;
  entree *ep = is_entry_intern(name, functions_hash, &hash);

  check_proto(code);
  if (ep)
  {
    if (ep->valence != EpINSTALL)
      err(talker,"[install] identifier '%s' already in use", name);
    err(warner, "[install] updating '%s' prototype; module not reloaded", name);
    if (ep->code) free(ep->code);
  }
  else
  {
    char *s = name;
    if (isalpha((int)*s))
      while (is_keyword_char(*++s)) /* empty */;
    if (*s) err(talker2,"not a valid identifier", s, name);
    ep = installep(f, name, strlen(name), EpINSTALL, 0, functions_hash + hash);
  }
  ep->code = pari_strdup(code);
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

/* make GP variables safe for avma = top */
void
var_make_safe()
{
  long n;
  entree *ep;
  for (n = 0; n < functions_tblsz; n++)
    for (ep = functions_hash[n]; ep; ep = ep->next)
      if (EpVALENCE(ep) == EpVAR)
      { /* make sure ep->value is a COPY */
        var_cell *v = (var_cell*)ep->args;
        if (v && v->flag == PUSH_VAL) changevalue(ep, (GEN)ep->value);
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
  const pari_sp av = avma, lim = stack_lim(av,1);
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
  pari_sp av = avma, lim = stack_lim(av, 2);
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
  STMT_START { match2(analyseur, c); analyseur++; } STMT_END

static long
readlong()
{
  const pari_sp av = avma;
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

  if (typ(x) != t_POL || lg(x) != 4 ||
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
/**                            STRINGS                             **/
/**                                                                **/
/********************************************************************/

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
    pari_sp av = avma;
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
  long n = 1, len = 16;
  GEN res = cget1(len + 1, t_VEC);

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
      GEN p1 = cget1(newlen + 1, t_VEC);
      for (n = 1; n < len; n++) p1[n] = res[n];
      res = p1; len = newlen;
    }
  }
  setlg(res, n); return res;
}

/*  Read a "string" from src. Format then copy it, starting at s. Return
 *  pointer to char following the end of the input string */
char *
readstring(char *src, char *s)
{
  match2(src, '"'); src++; s = translate(&src, s, NULL,NULL);
  match2(src, '"'); return src+1;
}

/* return the first n0 chars of s as a GEN [s may not be 0-terminated] */
static GEN
_strtoGENstr(const char *s, long n0)
{
  long n = nchar2nlong(n0+1);
  GEN x = cgetg(n+1, t_STR);
  char *t = GSTR(x);
  strncpy(t, s, n0); t[n0] = 0; return x;
}

GEN
STRtoGENstr(const char *s) { return _strtoGENstr(s, strlen(s)); }

/* FIXME: obsolete, kept for gp2c compatibility */
GEN
strtoGENstr(char *s, long flag)
{
  GEN x;

  if (flag) s = expand_tilde(s);
  x = _strtoGENstr(s, strlen(s));
  if (flag) free(s);
  return x;
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
  int full_col, full_row;
  void *extra; /* so far used by check_pointers only */
} matcomp;

/* Return the content of the matrix cell and sets members of corresponding
 * matrix component 'c'.  Assume *analyseur = '[' */
static GEN
matcell(GEN p, matcomp *C)
{
  GEN *pt = &p;
  long c, r;
  C->full_col = C->full_row = 0;
  do {
    analyseur++; p = *pt;
    switch(typ(p))
    {
      case t_VEC: case t_COL:
        c = check_array_index(lg(p));
        pt = (GEN*)(p + c); match(']'); break;

      case t_LIST:
        c = check_array_index(lgeflist(p)-1) + 1;
        pt = (GEN*)(p + c); match(']'); break;

      case t_VECSMALL:
        c = check_array_index(lg(p));
        pt = (GEN*)(p + c); match(']');
        if (*analyseur == '[') err(caracer1,analyseur,mark.start);
        C->parent = p;
        C->ptcell = pt; return stoi((long)*pt);

      case t_MAT:
        if (lg(p)==1) err(talker2,"a 0x0 matrix has no elements",
                                  analyseur,mark.start);
        C->full_col = C->full_row = 0;
        if (*analyseur==',') /* whole column */
        {
          analyseur++;
          c = check_array_index(lg(p));
          match(']');
          if (*analyseur == '[')
          { /* collapse [,c][r] into [r,c] */
            analyseur++;
            r = check_array_index(lg(p[c]));
            pt = (GEN*)(((GEN)p[c]) + r); /* &coeff(p,r,c) */
            match(']');
          }
          else
          {
            C->full_col = 1;
            pt = (GEN*)(p + c);
          }
          break;
        }

        r = check_array_index(lg(p[1]));
        match(',');
        if (*analyseur == ']') /* whole row */
        {
          analyseur++;
          if (*analyseur == '[')
          { /* collapse [r,][c] into [r,c] */
            analyseur++;
            c = check_array_index(lg(p));
            pt = (GEN*)(((GEN)p[c]) + r); /* &coeff(p,r,c) */
            match(']');
          }
          else
          {
            GEN p2 = cgetg(lg(p),t_VEC);
            C->full_row = r; /* record row number */
            for (c=1; c<lg(p); c++) p2[c] = coeff(p,r,c);
            pt = &p2;
          }
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
  C->parent = p;
  C->ptcell = pt; return *pt;
}

static GEN
facteur(void)
{
  const char *old = analyseur;
  GEN x, p1;
  int plus;

  switch(*analyseur)
  {
    case '-': analyseur++; plus = 0; break;
    case '+': analyseur++; plus = 1; break;
    default: plus = 1; break;
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
  long N, i, j, m, n, p;
  GEN *table, z;
  char *old;

  if (isalpha((int)*analyseur)) return identifier();
  if (isdigit((int)*analyseur) || *analyseur == '.') return constante();

  switch(*analyseur)
  {
    case '!': /* NOT */
      analyseur++; z = facteur();
      if (br_status) err(breaker,"here (after !)");
      return gcmp0(z)? gun: gzero;

    case ('\''): { /* QUOTE */
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
    case '#': /* cardinal */
      analyseur++; z = facteur();
      if (br_status) err(breaker,"here (after #)");
      return stoi(glength(z));

    case '"': /* string */
      analyseur++; old = analyseur;
      skipstring();
      n = nchar2nlong(analyseur - old); /* do not count enclosing '"' */
      z = cgetg(n+1, t_STR);
      (void)translate(&old, GSTR(z), NULL,NULL);
      return z;

    case '(':
      analyseur++;
      z = expr(); match(')'); return z;

    case '[': /* constant array/vector */
      analyseur++;
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
	  z = cgetg(n+1,tx);
	  for (i=1; i<=n; i++) z[i] = lcopy(table[i]);
	  break;
        }

	case ';':
	  m = n;
	  do _append(&table, &n, &N); while (*analyseur++ != ']');
	  z = cgetg(m+1,t_MAT); p = n/m + 1;
	  for (j=1; j<=m; j++)
	  {
            GEN c = cgetg(p,t_COL); z[j] = (long)c;
	    for (i=j; i<=n; i+=m) *++c = lcopy(table[i]);
	  }
	  break;

	default: /* can only occur in library mode */
          err(talker,"incorrect vector or matrix");
          return NULL; /* not reached */
      }
      free(table); return z;

    case '%':
    old = analyseur; analyseur++;
    if (!GP_DATA) err(talker2,"history not available", old, mark.start);
    else
    {
      gp_hist *H = GP_DATA->hist;
      int junk;
      p = 0;
      while (*analyseur == '`') { analyseur++; p++; }
      return p ? gp_history(H, -p        , old, mark.start)
               : gp_history(H, (long)number(&junk,&analyseur), old, mark.start);
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
  char c = *analyseur, c1 = analyseur[1];
  if (c && c1)
  {
    if (c1 == '=')
    {
      switch(c)
      {
        case '+' : analyseur += 2; return &gadd;
        case '-' : analyseur += 2; return &gsub;
        case '*' : analyseur += 2; return &gmul;
        case '/' : analyseur += 2; return &gdiv;
        case '%' : analyseur += 2; return &gmod;
        case '\\': analyseur += 2; return &gdivent;
      }
    }
    else if (analyseur[2] == '=')
    {
      switch(c)
      {
        case '>' : if (c1=='>') { analyseur += 3; return &gshift_r; }
          break;
        case '<' : if (c1=='<') { analyseur += 3; return &gshift_l; }
          break;
        case '\\': if (c1=='/') { analyseur += 3; return &gdivround; }
          break;
      }
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
change_compo(matcomp *c, GEN res)
{
  GEN p = c->parent, *pt = c->ptcell;
  long i;
  char *old = analyseur;

  if (typ(p) == t_VECSMALL)
  {
    if (typ(res) != t_INT || is_bigint(res))
      err(talker2,"not a suitable VECSMALL component",old,mark.start);
    *pt = (GEN)itos(res); return res;
  }
  if (c->full_row)
  {
    if (typ(res) != t_VEC || lg(res) != lg(p)) err(caseer2,old,mark.start);
    for (i=1; i<lg(p); i++)
    {
      GEN p1 = gcoeff(p,c->full_row,i); if (isclone(p1)) killbloc(p1);
      coeff(p,c->full_row,i) = lclone((GEN)res[i]);
    }
    return res;
  }
  if (c->full_col)
    if (typ(res) != t_COL || lg(res) != lg(*pt)) err(caseer2,old,mark.start);

  res = gclone(res);
  killsubblocs(*pt);
  return *pt = res;
}

/* extract from p the needed component, and assign result if needed */
static GEN
matrix_block(GEN p)
{
  matcomp c;
  GEN cpt = matcell(p, &c);

  if (*analyseur != ',' && *analyseur != ')') /* fast shortcut */
  {
    GEN res;
    F2GEN fun = affect_block(&res);
    if (res)
    {
      if (fun) res = fun(cpt, res);
      return change_compo(&c,res);
    }
  }
  return isonstack(cpt)? gcopy(cpt): cpt; /* no assignment */
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
call_fun(GEN p, GEN *arg, gp_args *f)
{
  GEN res, *loc = f->arg + f->narg;
  long i;

  p++; /* skip NULL */
  /* push new values for formal parameters */
  for (i=0; i<f->narg; i++) copyvalue(*p++, *arg++);
  for (i=0; i<f->nloc; i++) pushvalue(*p++, make_arg(*loc++));
  /* dumps arglist from identifier() to the garbage zone */
  res = fun_seq((char *)p);
  /* pop out ancient values of formal parameters */
  for (i=0; i<f->nloc; i++) killvalue(*--p);
  for (i=0; i<f->narg; i++) killvalue(*--p);
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
        if (isclone(c->extra)) killbloc((GEN)c->extra);
        *pt = x;
      }
      else
        (void)change_compo(c, x);
      free((void*)c);
    }
}

#define match_comma() \
  STMT_START { if (matchcomma) match(','); else matchcomma = 1; } STMT_END

static void
skipdecl(void)
{
  if (*analyseur == ':') { analyseur++; skipexpr(); }
}

static void
skip_arg_block(gp_args *f)
{
  int i, matchcomma = 0;
  for (i = f->narg; i; i--)
  {
    if (do_switch(0,matchcomma))
      matchcomma = 1;
    else { match_comma(); skipexpr(); skipdecl(); }
  }
}

static long
check_args()
{
  long nparam = 0, matchcomma = 0;
  entree *ep;
  char *old;
  GEN cell;

  match('(');
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
      pari_sp av = avma;
      skipexpr();
      cell[1] = lclone(_strtoGENstr(old, analyseur-old));
      avma = av;
    }
    else cell[1] = zero;
  }
  analyseur++; /* match(')') */
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
  pari_sp av = avma;
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
num_derivU(GEN p, GEN *arg, gp_args *f)
{
  GEN eps,a,b, x = *arg;
  long fpr, pr, l, e, ex;
  pari_sp av = avma;

  if (!is_const_t(typ(x)))
  {
    a = call_fun(p,arg,f);
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
  *arg = fix(gsub(x, eps), l); a = call_fun(p,arg,f);
  *arg = fix(gadd(x, eps), l); b = call_fun(p,arg,f);
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
  pari_sp av;
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

        newfun=ptr= (GEN) newbloc(2 + nchar2nlong(len+1));
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
  ep = do_alias(ep);
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
    char *flags = NULL;

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
    else if (*s == 'i') { ret = RET_INT;  s++; }
    else if (*s == 'l') { ret = RET_LONG; s++; }
    else                  ret = RET_GEN;
    /* Optimized for G and p. */
    i = 0;
    matchcomma = 0;
    while (*s == 'G')
    {
      match_comma(); s++;
      argvec[i++] = expr();
      if (br_status) err(breaker,"here (argument reading)");
    }
    if (*s == 'p') { argvec[i++] = (GEN) prec; s++; }

    while (*s && *s != '\n')
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
            c->extra = (GEN*)ep->value;
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

	case 'M': /* Mnemonic flag */
	  match_comma(); argvec[i] = expr();
          if (br_status) err(breaker,"here (argument reading)");
	  if (typ(argvec[i]) == t_STR) {
	      if (!flags)
		  flags = ep->code;
	      flags = strchr(flags, '\n'); /* Skip to the following '\n' */
	      if (!flags)
		  err(talker, "not enough flags in string function signature");
	      flags++;
	      argvec[i] = (GEN) parse_option_string((char*)(argvec[i] + 1),
			  flags, PARSEMNU_ARG_WHITESP | PARSEMNU_TEMPL_TERM_NL,
			  NULL, NULL);
	  } else
	      argvec[i] = (GEN)itos(argvec[i]);
	  i++;
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
              case 'V': matchcomma=1; argvec[i++]=DFT_GEN; s++; break;
              case 'n': matchcomma=1; argvec[i++]=DFT_VAR; s++; break;
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
	m = (long)((int (*)(ANYARG))call)(_ARGS_);
	res = stoi(m); break;

      case RET_LONG:
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
        matchcomma = 0;
        while (*analyseur != ')')
        {
          match_comma(); ch1=analyseur;
          check_var_name();
          ep = skipentry();
          switch(EpVALENCE(ep))
          {
            case EpGVAR:
            case EpVAR: break;
            default: err(talker2,"symbol already in use",ch1,mark.start);
          }
          analyseur=ch1; ep = entry();
          if (*analyseur == '=')
          {
            pari_sp av=avma; analyseur++;
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
    GEN *arglist;
    gp_args *f;

    case EpUSER: /* user-defined functions */
      f = (gp_args*)ep->args;
      deriv = (*analyseur == '\'' && analyseur[1] == '(') && analyseur++;
      arglist = (GEN*) new_chunk(f->narg);
      if (*analyseur != '(') /* no args */
      {
	if (*analyseur != '='  ||  analyseur[1] == '=')
        {
          for (i=0; i<f->narg; i++)
            arglist[i] = make_arg(f->arg[i]);
	  return call_fun((GEN)ep->value, arglist, f);
        }
	match('('); /* ==> error */
      }
      analyseur++; /* skip '(' */
      ch1 = analyseur;
      skip_arg_block(f);
      if (*analyseur == ')' && (analyseur[1] != '=' || analyseur[2] == '='))
      {
        matchcomma = 0;
        analyseur = ch1;
        for (i=0; i<f->narg; i++)
        {
          if (do_switch(0,matchcomma))
          { /* default arg */
            arglist[i] = make_arg(f->arg[i]);
            matchcomma = 1;
          }
          else
          { /* user supplied */
            match_comma();
            arglist[i] = expr();
            if (br_status) err(breaker,"here (reading function args)");
          }
        }
        analyseur++; /* skip ')' */
        if (deriv)
        {
          if (!f->narg)
            err(talker2, "can't derive this", mark.identifier, mark.start);
          return num_derivU((GEN)ep->value, arglist, f);
        }
        return call_fun((GEN)ep->value, arglist, f);
      }

      /* REDEFINE function */
      if (*analyseur != ',' && *analyseur != ')') skipexpr();
      while (*analyseur == ',') { analyseur++; skipexpr(); }
      match(')');
      if (*analyseur != '='  ||  analyseur[1] == '=')
        err(nparamer1,mark.identifier,mark.start);
      analyseur = ch1-1; /* points to '(' */

      free_args((gp_args*)ep->args);
      free(ep->args);
      ep->valence = EpNEW;
    /* Fall through */

    case EpNEW: /* new function */
    {
      GEN tmpargs = (GEN)avma;
      char *start;
      long len, narg, nloc;

      check_new_fun = ep;

      /* checking arguments */
      narg = check_args(); nloc = 0;
      /* Dirty, but don't want to define a local() function */
      if (*analyseur != '=' && strcmp(ep->name, "local") == 0)
        err(talker2, "local() bloc must appear before any other expression",
                     mark.identifier,mark.start);
      match('=');
      { /* checking function definition */
        skipping_fun_def++;
        while (strncmp(analyseur,"local(",6) == 0)
        {
          analyseur += 5; /* on '(' */
          nloc += check_args();
          while(separe(*analyseur)) analyseur++;
        }
        start = analyseur; skipseq(); len = analyseur-start;
        skipping_fun_def--;
      }
      /* function is ok. record it */
      /* record default args */
      f = (gp_args*) gpmalloc((narg+nloc)*sizeof(GEN) + sizeof(gp_args));
      ep->args = (void*) f;
      f->nloc = nloc;
      f->narg = narg;
      f->arg = defarg = (GEN*)(f + 1);

      narg += nloc; /* record default args and local variables */
      newfun = ptr = (GEN) newbloc(1 + narg + nchar2nlong(len+1));
      newfun++; /* this bloc is no GEN, leave the first cell alone ( = 0) */
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
     /* wait till here for gunclone because of strncopy above. In pathological
      * cases, e.g. (f()=f()=x), new text is given by value of old one! */
      if (EpVALENCE(ep) == EpUSER) gunclone((GEN)ep->value);
      ep->value = (void *)ptr;
      ep->valence = EpUSER;
      check_new_fun=NULL;
      avma = (pari_sp)tmpargs; return gnil;
    }
  }
  err(valencer1); return NULL; /* not reached */
}

static ulong
number(int *n, char **s)
{
  ulong m = 0;
  for (*n = 0; *n < 9 && isdigit((int)**s); (*n)++,(*s)++)
    m = 10*m + (**s - '0');
  return m;
}

ulong
u_pow10(int n)
{
  static ulong pw10[] = { 1UL, 10UL, 100UL, 1000UL, 10000UL, 100000UL,
                        1000000UL, 10000000UL, 100000000UL, 1000000000UL };
  return pw10[n];
}

static GEN
int_read_more(GEN y, char **ps)
{
  pari_sp av = avma;
  int i = 0, nb;
  while (isdigit((int)**ps))
  {
    ulong m = number(&nb, ps);
    if (avma != av && ++i > 4) { avma = av; i = 0; } /* HACK gerepile */
    y = addumului(m, u_pow10(nb), y);
  }
  return y;
}

static GEN
constante()
{
  pari_sp av = avma;
  long l, n = 0;
  int nb;
  GEN y = utoi(number(&nb, &analyseur));
  if (nb == 9) y = int_read_more(y, &analyseur);
  switch(*analyseur)
  {
    default: return y; /* integer */
    case '.':
    {
      char *old = ++analyseur;
      y = int_read_more(y, &analyseur);
      n = old - analyseur;
      if (*analyseur != 'E' && *analyseur != 'e')
      {
        if (!signe(y)) { avma = av; return realzero(prec); }
        break;
      }
    }
    /* Fall through */
    case 'E': case 'e':
    {
      char *old = analyseur;
      switch(*++analyseur)
      {
        case '-': analyseur++; n -= (long)number(&nb, &analyseur); break;
        case '+': analyseur++; /* Fall through */
        default: n += (long)number(&nb, &analyseur);
      }
      if (nb > 8) err(talker2,"exponent too large",old,mark.start);
      if (!signe(y))
      {
        avma = av;
        n = (n > 0)? (long)(n/L2SL10): (long)-((-n)/L2SL10 + 1);
        return realzero_bit(n);
      }
    }
  }
  l = lgefint(y); if (l < (long)prec) l = (long)prec;
  y = itor(y, l);
  if (n)
  {
    GEN t = rpowsi(10UL, stoi(labs(n)), l+1); /* 10^|n| */
    y = (n > 0)? mulrr(y,t): divrr(y,t);
    y = gerepileuptoleaf(av, y);
  }
  return y;
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
  static long max_avail = MAXVARN; /* max variable not yet used */
  static long nvar; /* first GP free variable */
  long var;
  GEN p;

  switch(n) {
      case manage_var_init: return nvar=0;
      case manage_var_next: return nvar;
      case manage_var_max_avail: return max_avail;
      case manage_var_pop:
      {
        long v = (long)ep;
        if (v != nvar-1) err(talker,"can't pop gp variable");
        setlg(polvar, nvar);
        return --nvar;
      }
      case manage_var_delete:
	/* user wants to delete one of his/her/its variables */
	if (max_avail == MAXVARN-1) return 0; /* nothing to delete */
	free(polx[++max_avail]); /* frees both polun and polx */
	return max_avail+1;
      case manage_var_create: break;
      default: err(talker, "panic");
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
    p = (GEN) gpmalloc(SIZEOF_VAR_POLS);
    var=max_avail--;
  }

  /* create polx[var] */
  p[0] = evaltyp(t_POL) | evallg(4);
  p[1] = evalsigne(1) | evalvarn(var);
  p[2] = zero;
  p[3] = un;
  polx[var] = p;

  /* create polun[nvar] */
  p += 4;
  p[0] = evaltyp(t_POL) | evallg(3);
  p[1] = evalsigne(1) | evalvarn(var);
  p[2] = un;
  polun[var] = p;

  varentries[var] = ep;
  if (ep) { polvar[nvar] = (long) ep->value; setlg(polvar, nvar+1); }
  return var;
}

long
fetch_var(void)
{
  return manage_var(manage_var_create,NULL);
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
  ep = installep(NULL,s,strlen(s),EpVAR, SIZEOF_VAR_POLS,
                 functions_hash + hashvalue(s));
  (void)manage_var(manage_var_create,ep); return ep;
}

long
fetch_user_var(char *s)
{
  entree *ep = is_entry(s);
  pari_sp av;
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
  (void)manage_var(manage_var_pop, (entree*)varn(initial_value(ep)));
  kill0(ep);
}

long
delete_var(void)
{
  return manage_var(manage_var_delete,NULL);
}

void
name_var(long n, char *s)
{
  entree *ep;
  char *u;

  if (n < manage_var(manage_var_next,NULL))
    err(talker, "renaming a GP variable is forbidden");
  if (n > (long)MAXVARN)
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
    { n=SIZEOF_VAR_POLS; val=EpVAR; }
  ep = installep(NULL,old,len,val,n, functions_hash + hash);

  if (n) (void)manage_var(manage_var_create, ep); /* Variable */
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
    if ((long)strlen(analyseur) > n)
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

/* analyseur points on the character following the starting " */
/* skip any number of concatenated strings */
static void
skipstring()
{
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
  long i, m, n;
  char *old;

  if (isalpha((int)*analyseur)) { skipidentifier(); return; }
  if (isdigit((int)*analyseur) || *analyseur== '.') { skipconstante(); return; }
  switch(*analyseur)
  {
    case '"':
      analyseur++; skipstring(); return;

    case '!':
    case '#':
      analyseur++; skipfacteur(); return;

    case '&':
    case '\'':
      analyseur++; check_var_name();
      (void)skipentry(); return;

    case '(':
      analyseur++; skipexpr(); match(')'); return;

    case '[':
      old = analyseur; analyseur++;
      if (*analyseur == ';' && analyseur[1] == ']')  /* [;] */
        { analyseur+=2; return; }
      n = 0;
      if (*analyseur != ']')
      {
	do { n++; skipexpr(); old=analyseur; } while (*analyseur++ == ',');
	analyseur--;
      }
      switch (*analyseur++)
      {
	case ']': return;
	case ';':
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
    {
      int junk;
      analyseur++;
      if (*analyseur == '`') { while (*++analyseur == '`') /*empty*/; return; }
      (void)number(&junk, &analyseur); return;
    }
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
  int matchcomma;
  entree *ep;

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

    if (*s == 'v' || *s == 'l' || *s == 'i') s++;
    /* Optimized for G and p. */
    matchcomma = 0;
    while (*s == 'G') { match_comma(); skipexpr(); s++; }
    if (*s == 'p') s++;
    while (*s && *s != '\n') switch (*s++)
    {
      case 'G': case 'n': case 'L': case 'M':
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
          if (*analyseur == '"') { analyseur++; skipstring(); }
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
            if (*analyseur == '"') { analyseur++; skipstring(); }
            if (*analyseur == ')') break;
            if (*analyseur == ',') analyseur++;
            else skipexpr();
          }
          s++;
          break;
        }

        while (*analyseur)
        {
          if (*analyseur == '"') { analyseur++; skipstring(); }
          if (*analyseur == ',' || *analyseur == ')') break;
          skipexpr();
        }
        break;

      case 'S': match_comma();
        check_var_name(); (void)skipentry(); break;
      case '&': match_comma(); match('&'); check_matcell(); break;
      case 'V': match_comma(); check_var(); break;

      case 'p': case 'P': case 'f': case 'x':
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
      case '\n':			/* Before the mnemonic */
	break;
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
        matchcomma = 0;
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

      if (*analyseur == '\'') analyseur++;
      if (*analyseur != '(')
      {
	if ( *analyseur != '='  ||  analyseur[1] == '=' ) return;
	match('('); /* error */
      }
      analyseur++;  /* skip '(' */
      skip_arg_block((gp_args*)ep->args);
      if (*analyseur == ')' && (analyseur[1] != '=' || analyseur[2] == '='))
	  { analyseur++; return; }

      /* here we are redefining a user function */
      if (*analyseur != ',' && *analyseur != ')') skipexpr();
      while (*analyseur == ',') { analyseur++; skipexpr(); }
      match(')');

      if (*analyseur != '=' || analyseur[1] == '=')
      {
        if (skipping_fun_def) return;
        err(nparamer1,mark.identifier,mark.start);
      }
      analyseur = ch1;
    } /* fall through */

    case EpNEW: /* new function */
      if (check_new_fun && ! skipping_fun_def)
      {
	err_new_fun(); /* ep not created yet: no need to kill it */
	err(paramer1, mark.identifier, mark.start);
      }
      check_new_fun = NOT_CREATED_YET; match('(');
      matchcomma = 0;
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

/*
 * Only letters and digits in member names. AT MOST 8 of THEM
 * (or modify gp_rl.c::pari_completion)
 */
#include "members.h"

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

void
member_err(char *s)
{
  err(member,s,mark.member,mark.start);
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

