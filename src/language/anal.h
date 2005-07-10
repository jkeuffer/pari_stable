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
/* modules */
typedef struct module {
  entree *func;
  char **help;
} module;

/* GP control structures */
typedef struct {
  entree *ep;
  char *ch;
} exprdat;
GEN _gp_eval(GEN x, void *dat);
#define EXPR_START(ep, ch) exprdat __E; __E.ch=ch; __E.ep=ep; push_val(ep,NULL);
#define EXPR_END(ep) pop_val(ep);
#define EXPR_WRAP(ep, ch, call) \
{ GEN z; EXPR_START(ep, ch); z = call; EXPR_END(ep); return z; }
#define EXPR_ARG &__E, &_gp_eval

void push_val(entree *ep, GEN a);
void pop_val(entree *ep);

/* binary I/O */
typedef struct GENbin {
  size_t len; /* taille(x) */
  GEN x; /* binary copy of x */
  GEN base; /* base address of p->x */
  int canon; /* 1: t_INT in canonical (native kernel) form,
                0: t_INT according to current kernel */
} GENbin;
#define GENbase(p) ((GEN)(p + 1))

GENbin* copy_bin(GEN x);
GENbin* copy_bin_canon(GEN x);
GEN bin_copy(GENbin *p);

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
int    is_identifier(char *s);
entree *is_entry_intern(char *s, entree **table, long *hash);
long   is_keyword_char(char c);
char   *readstring(char *src, char *s);
long   loop_break(void);
long   did_break(void);
void   readseq_void(char *t);
GEN    readseq_nobreak(char *t);
GEN    readexpr_nobreak(char *t);

char*  get_analyseur(void);
void   set_analyseur(char *s);

void term_color(int c);
char *term_get_color(int c);
void hit_return(void);

extern ulong prec;
extern GEN gnil;

extern char *gp_function_name;
extern int  (*whatnow_fun)(char *, int);
extern void (*sigint_fun)(void);
extern void *foreignHandler;
extern GEN  (*foreignExprHandler)(char*);
extern char foreignExprSwitch;
extern entree * (*foreignAutoload)(char*, long);
extern void (*foreignFuncFree)(entree *);
extern int (*default_exception_handler)(long);

/* Variables containing the list of PARI functions */
extern module *pari_modules;       /* list of functions modules */
extern entree **functions_hash;    /* functions hashtable */
extern entree **members_hash;      /* members hashtable */
extern char   *helpmessages_basic[];
extern entree functions_basic[];
extern const int functions_tblsz;  /* hashcodes table size */

/* Variables containing the list of specific GP functions */
extern char   *helpmessages_gp[];
extern entree  functions_gp[];
extern entree  gp_member_list[];
extern char   *helpmessages_highlevel[];
extern entree  functions_highlevel[];
extern int     gp_colors[];
extern int     disable_color;

/* Variables containing the list of old PARI fonctions (up to 1.39.15) */
extern module *pari_oldmodules;    /* list of functions modules */
extern entree **funct_old_hash;    /* hashtable */
extern char   *oldhelpmessage[], *helpmessages_oldgp[];
extern entree  oldfonctions[], functions_oldgp[];

/* backward compatibility */
extern ulong compatible;
enum { NONE, WARN, OLDFUN, OLDALL };
#define new_fun_set (compatible == NONE || compatible == WARN)

/* return type for GP functions */
enum { RET_GEN, RET_INT, RET_LONG, RET_VOID };

#ifdef STACK_CHECK
extern void *PARI_stack_limit;
#endif

/* entrees */
#define EpVALENCE(ep) ((ep)->valence & 0xFF)
#define EpSTATIC(ep) ((ep)->valence & 0x100)
#define EpSETSTATIC(ep) ((ep)->valence |= 0x100)
#define EpPREDEFINED(ep) (EpVALENCE(ep) < EpUSER)
enum { EpUSER = 100, EpNEW, EpALIAS, EpVAR, EpGVAR, EpMEMBER, EpINSTALL };

/* signals */
extern ulong init_opts;
#define INIT_JMPm 1
#define INIT_SIGm 2
#define INIT_JMP     (init_opts & INIT_JMPm)
#define INIT_SIG     (init_opts & INIT_SIGm)
#define INIT_JMP_on  (init_opts |= INIT_JMPm)
#define INIT_SIG_on  (init_opts |= INIT_SIGm)
#define INIT_JMP_off (init_opts &= ~INIT_JMPm)
#define INIT_SIG_off (init_opts &= ~INIT_SIGm)

/* defaults  */
#define is_default(s) setdefault((s),"",d_EXISTS) == gen_1
enum { d_ACKNOWLEDGE, d_INITRC, d_SILENT, d_RETURN, d_EXISTS };
char* get_sep(const char *t);
long get_int(const char *s, long dflt);
ulong get_uint(const char *s);
int  gp_init_functions(int force);

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

/* gp_colors */
void decode_color(int n, int *c);
#define c_NONE 0xffffUL
enum { c_ERR, c_HIST, c_PROMPT, c_INPUT, c_OUTPUT, c_HELP, c_TIME, c_LAST };

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
void allocatemem0(size_t newsize);
GEN  break0(long n);
GEN  default0(char *a, char *b, long flag);
GEN  extern0(char *cmd);
void gp_quit(void);
GEN  input0(void);
void kill0(entree *ep);
GEN  next0(long n);
GEN  read0(char *s);
GEN  return0(GEN x);
void system0(char *cmd);
GEN  trap0(char *e, char *f, char *r);
int  whatnow(char *s, int silent);
