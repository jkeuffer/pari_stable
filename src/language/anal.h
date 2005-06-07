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
/* structs */
typedef struct default_type {
  char *name;
  void *fun;
} default_type;

extern default_type gp_default_list[];
extern char *keyword_list[];

typedef struct gp_args {
  int nloc, narg;
  GEN *arg;
} gp_args;

typedef struct module {
  entree *func;
  char **help;
} module;
int  gp_init_entrees(module *modlist, entree **hash, int force);

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

/* history */
typedef struct {
  GEN *res;    /* array of previous results, FIFO */
  size_t size; /* # res */
  ulong total; /* # of results computed since big bang */
} gp_hist;

/* prettyprinter */
typedef struct {
  pariFILE *file;
  char *cmd;
} gp_pp;

/* path */
typedef struct {
  char *PATH;
  char **dirs;
} gp_path;

void push_stack(stack **pts, void *a);
void *pop_stack(stack **pts);
void delete_dirs(gp_path *p);
void gp_expand_path(gp_path *p);

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
void   print_prefixed_text(char *s, char *prefix, char *str);
GEN    gp_history(gp_hist *H, long p, char *old, char *entry);
GEN    set_hist_entry(gp_hist *H, GEN x);
void   lisseq_void(char *t);
GEN    lisseq_nobreak(char *t);
GEN    lisexpr_nobreak(char *t);

char*  get_analyseur(void);
void   set_analyseur(char *s);

void term_color(int c);
char *term_get_color(int c);
void hit_return(void);

extern ulong prec;
extern GEN gnil;

extern char *gp_function_name;
extern int  (*whatnow_fun)(char *, int);
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

#ifdef __EMX__
#  define STACK_CHECK
#endif

#ifdef STACK_CHECK
extern void *PARI_stack_limit;
#endif

#if defined(__EMX__) || defined(_WIN32) || defined(__CYGWIN32__)
#  define PATH_SEPARATOR ';' /* beware DOSish 'C:' disk drives */
#else
#  define PATH_SEPARATOR ':'
#endif

/* entrees */
#define EpVALENCE(ep) ((ep)->valence & 0xFF)
#define EpSTATIC(ep) ((ep)->valence & 0x100)
#define EpSETSTATIC(ep) ((ep)->valence |= 0x100)
#define EpPREDEFINED(ep) (EpVALENCE(ep) < EpUSER)
enum { EpUSER = 100, EpNEW, EpALIAS, EpVAR, EpGVAR, EpMEMBER, EpINSTALL };

/* blocs */
#define BL_HEAD 3
#define bl_base(x) ((x) - BL_HEAD)
#define bl_next(x) (((GEN)x)[-3])
#define bl_prev(x) (((GEN)x)[-2])
#define bl_num(x)  (((GEN)x)[-1])

/* signals */
#define INIT_JMPm 1
#define INIT_SIGm 2
#define INIT_JMP     (init_opts & INIT_JMPm)
#define INIT_SIG     (init_opts & INIT_SIGm)
#define INIT_JMP_on  (init_opts |= INIT_JMPm)
#define INIT_SIG_on  (init_opts |= INIT_SIGm)
#define INIT_JMP_off (init_opts &= ~INIT_JMPm)
#define INIT_SIG_off (init_opts &= ~INIT_SIGm)

/* gp_colors */
void decode_color(int n, int *c);
#define c_NONE 0xffffUL
enum { c_ERR, c_HIST, c_PROMPT, c_INPUT, c_OUTPUT, c_HELP, c_TIME, c_LAST };

/* general printing */
#define print_text(s) print_prefixed_text((s),NULL,NULL);

/* infiles */
#define MAX_BUFFER 64
#define mf_IN    1
#define mf_PIPE  2
#define mf_FALSE 4
#define mf_OUT   8
#define mf_PERM 16
#define mf_TEST 32

/* for filtre */
typedef struct {
  char *s, *t, *end; /* source, target, last char read */
  int in_string, in_comment, more_input, wait_for_brace, downcase;
  void *data;
} filtre_t;

#define LBRACE '{'
#define RBRACE '}'
#define separator(c)  ((c)==';')

int get_line_from_readline(char *prompt, char *bare_prompt, filtre_t *F);
char *filtre0(filtre_t *F);
char *filtre(char *s, int flag);
void check_filtre(filtre_t *F);

typedef struct Buffer {
  char *buf;
  ulong len;
  jmp_buf env;
} Buffer;

typedef struct input_method {
  int free;
  char *prompt;
  FILE *file;
  char * (*fgets)(char *,int,FILE*);
  char * (*getline)(Buffer*, char**, struct input_method*);
  void (*onempty)(void);
} input_method;

void fix_buffer(Buffer *b, long newlbuf);
int input_loop(filtre_t *F, input_method *IM);

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

/* for output */
typedef struct {
  char format; /* e,f,g */
  long fieldw; /* 0 (ignored) or field width */
  long sigd;   /* -1 (all) or number of significant digits printed */
  int sp;      /* 0 = suppress whitespace from output */
  int prettyp; /* output style: raw, prettyprint, etc */
  int TeXstyle;
} pariout_t;

void gen_output(GEN x, pariout_t *T);
char *GENtostr0(GEN x, pariout_t *T, void(*do_out)(GEN, pariout_t *));
void bruti(GEN g, pariout_t *T, int nosign);
void matbruti(GEN g, pariout_t *T);
void sori(GEN g, pariout_t *T);
void texi(GEN g, pariout_t *T, int nosign);
void texi_nobrace(GEN g, pariout_t *T, int nosign);
extern pariout_t DFLT_OUTPUT;

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

/* GP_DATA->flags */
enum { QUIET=1, TEST=2, SIMPLIFY=4, CHRONO=8, ECHO=16, STRICTMATCH=32,
       USE_READLINE=64, SECURE=128, EMACS=256, TEXMACS=512};
/* GP */
#define pariputs_opt(s) if (!(GP_DATA->flags & QUIET)) pariputs(s)

/* time */
enum { ti_NOPRINT, ti_REGULAR, ti_LAST, ti_INTERRUPT };
char *gp_format_time(long flag);

/* TeXmacs */
#define DATA_BEGIN  ((char) 2)
#define DATA_END    ((char) 5)
#define DATA_ESCAPE ((char) 27)

typedef struct {
  jmp_buf env;
  gp_hist *hist;
  gp_pp *pp;
  gp_path *path;
  pariout_t *fmt;
  ulong flags, lim_lines;
  char *help;
  pari_timer *T;
} gp_data;

extern gp_data *GP_DATA;
void gp_output(GEN z, gp_data *G);
