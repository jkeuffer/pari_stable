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

/*************************************************************************/
/*                                                                       */
/*                 Declarations specific to the analyzer                 */
/*                                                                       */
/*************************************************************************/
BEGINEXTERN

/* GP control structures */
typedef struct {
  entree *ep;
  GEN code;
} exprdat;
GEN gp_eval(GEN x, void *dat);
#define EXPR_WRAP(ep, ch, call) \
{ GEN z; exprdat __E; __E.code = ch; __E.ep = ep;\
  push_val(ep,NULL); z = call; pop_val(ep); return z; }
#define EXPR_ARG &__E, &gp_eval

/* to manipulate 'blocs' */
#define BL_HEAD 4
#define bl_base(x) ((x) - BL_HEAD)
#define bl_refc(x) (((GEN)x)[-4])
#define bl_next(x) (((GEN)x)[-3])
#define bl_prev(x) (((GEN)x)[-2])
#define bl_num(x)  (((GEN)x)[-1])

/* stacks */
typedef struct stack {
  struct stack *prev;
  void *value;
} stack;

void push_stack(stack **pts, void *a);
void *pop_stack(stack **pts);

/* functions */
void   changevalue_p(entree *ep, GEN x);
void   changevalue(entree *ep, GEN val);
entree *do_alias(entree *ep);
entree *is_entry_intern(const char *s, entree **table, long *hash);
long   is_keyword_char(char c);
long   loop_break(void);
void   reset_break(void);
long   did_break(void);

const char*  get_origin(void);

extern THREAD char *gp_function_name;
extern int  (*whatnow_fun)(char *, int);
extern void (*sigint_fun)(void);
extern void *foreignHandler;
extern GEN  (*foreignExprHandler)(char*);
extern char foreignExprSwitch;
extern entree * (*foreignAutoload)(const char*, long len);
extern void (*foreignFuncFree)(entree *);
extern int (*default_exception_handler)(long);

extern const long functions_tblsz;  /* hashcodes table size */
/* Variables containing the list of PARI functions */
extern entree **functions_hash;    /* functions hashtable */
extern entree functions_basic[];

/* Variables containing the list of specific GP functions */
extern entree  functions_gp[];
extern entree  functions_highlevel[];

/* Variables containing the list of old PARI fonctions (up to 1.39.15) */
extern entree **funct_old_hash;    /* hashtable */
extern entree  oldfonctions[], functions_oldgp[];

/* colors */
extern long    gp_colors[];
extern int     disable_color;

/* backward compatibility */
extern ulong compatible;
enum { NONE, WARN, OLDFUN, OLDALL };
#define new_fun_set (compatible == NONE || compatible == WARN)

/* return type for GP functions */
enum { RET_GEN, RET_INT, RET_LONG, RET_VOID };

#ifdef STACK_CHECK
extern THREAD void *PARI_stack_limit;
#endif

/* entrees */
#define EpVALENCE(ep) ((ep)->valence & 0xFF)
#define EpSTATIC(ep) ((ep)->valence & 0x100)
#define EpSETSTATIC(ep) ((ep)->valence |= 0x100)
#define EpPREDEFINED(ep) (EpVALENCE(ep) < EpUSER)
enum { EpUSER = 100, EpNEW, EpALIAS, EpVAR, EpGVAR, EpMEMBER, EpINSTALL };
#define initial_value(ep) ((ep)+1)

extern entree  **varentries;

/* defaults  */
char* get_sep(const char *t);
long get_int(const char *s, long dflt);
ulong get_uint(const char *s);
int  gp_init_functions(void);

extern char *current_logfile;
extern ulong readline_state;
#define DO_MATCHED_INSERT	2
#define DO_ARGS_COMPLETE	4

typedef struct default_type {
  char *name;
  void *fun;
} default_type;
extern default_type gp_default_list[];

/* prompts */
#define DFT_PROMPT "? "
#define BREAK_LOOP_PROMPT "break> "
#define COMMENTPROMPT "comment> "
#define CONTPROMPT ""
#define DFT_INPROMPT ""
#define MAX_PROMPT_LEN 128

/* general printing */
void print_prefixed_text(char *s, char *prefix, char *str);
#define print_text(s) print_prefixed_text((s),NULL,NULL);

/* GP output && output format */
enum { f_RAW, f_PRETTYMAT, f_PRETTYOLD, f_PRETTY, f_TEX };

void error0(GEN g);
void gpwritebin(char *s, GEN x);
void print   (GEN g);
void print0(GEN g, long flag);
void print1  (GEN g);
void printp  (GEN g);
void printp1 (GEN g);
void printtex(GEN g);
void write0  (const char *s, GEN g);
void write1  (const char *s, GEN g);
void writetex(const char *s, GEN g);
GEN Str(GEN g);
GEN Strexpand(GEN g);
GEN Strtex(GEN g);

/* gp specific routines */
void alias0(char *s, char *old);
void allocatemem0(GEN z);
GEN  break0(long n);
GEN  extern0(char *cmd);
void gp_quit(void);
GEN  input0(void);
void kill0(entree *ep);
GEN  next0(long n);
GEN  read0(char *s);
GEN  return0(GEN x);
void system0(char *cmd);
GEN  trap0(char *e, GEN f, GEN r);
int  whatnow(char *s, int silent);

struct node_loc
{
  const char *start,*end;  
}; 

union token_value {
  int val;
  GEN gen;
};

int pari_lex(union token_value *yylval, struct node_loc *yylloc, char **lex);
int pari_parse(char **lex);
entree* fetch_entry(const char *s, long len);
entree* fetch_member(const char *s, long len);
void pari_init_parser(void);
void pari_init_compiler(void);
void pari_init_evaluator(void);
GEN  pari_eval_str(char *lex, int strict);
void parser_reset(void);
void compiler_reset(void);
GEN  gp_closure(long n);

INLINE GEN 
closure_evalnobrk(GEN code)
{
  GEN r=closure_evalgen(code);
  if(!r)
    pari_err(talker, "break not allowed here");
  return r;
}

typedef struct
{
  long offset;
  long n;
  long alloc;
  size_t size;
} gp2c_stack;

void **stack_base(gp2c_stack *s);
void stack_alloc(gp2c_stack *s, long nb);
void stack_init(gp2c_stack *s, size_t size, void **data);
long stack_new(gp2c_stack *s);

ENDEXTERN
