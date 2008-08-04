/* $Id$

Copyright (C) 2000-2003  The PARI group.

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
/*                INITIALIZING THE SYSTEM, ERRORS                  */
/*                                                                 */
/*******************************************************************/
#include <string.h>
#include "pari.h"
#include "paripriv.h"
#include "anal.h"
#ifdef _WIN32
#  ifndef WINCE
#    include <process.h>
#  endif
#endif

const double LOG2    = 0.6931471805599453; /* log(2) */
const double LOG10_2 = 0.3010299956639812; /* log_10(2) */
const double LOG2_10 = 3.321928094887362;  /* log_2(10) */

GEN     gnil, gen_0, gen_1, gen_m1, gen_2, gen_m2, ghalf, gi;
THREAD GEN     gpi, geuler, bernzone;
GEN     primetab; /* private primetable */
byteptr diffptr;
FILE    *pari_outfile, *pari_errfile, *pari_logfile, *pari_infile;
char    *current_logfile, *current_psfile, *pari_datadir;
long    gp_colors[c_LAST];
int     disable_color;
ulong   DEBUGFILES, DEBUGLEVEL, DEBUGMEM;
ulong   compatible, precreal, precdl, logstyle;
gp_data *GP_DATA;

GEN pari_colormap = NULL, pari_graphcolors = NULL;

entree  **varentries;

THREAD pari_sp bot, top, avma;
size_t memused;
void    *global_err_data = NULL;

static growarray MODULES, OLDMODULES;
const long functions_tblsz = 135; /* size of functions_hash */
entree **functions_hash, **funct_old_hash;

void *foreignHandler; 	              /* Handler for foreign commands.   */
char foreignExprSwitch = 3; 	      /* Just some unprobable char.      */
GEN  (*foreignExprHandler)(char*);    /* Handler for foreign expressions.*/
entree* (*foreignAutoload)(const char*, long len); /* Autoloader         */
void (*foreignFuncFree)(entree *);    /* How to free external entree.    */

int  (*default_exception_handler)(long);
int  (*whatnow_fun)(const char *, int);
void (*sigint_fun)(void);

typedef struct {
  jmp_buf *penv;
  long flag;
} cell;

static THREAD stack *err_catch_stack;
static THREAD GEN *dft_handler;

#define BLOCK_SIGINT_START           \
{                                    \
  int block=PARI_SIGINT_block;       \
  PARI_SIGINT_block = 1;

#define BLOCK_SIGINT_END             \
  PARI_SIGINT_block = block;         \
  if (!block && PARI_SIGINT_pending) \
  {                                  \
    int sig = PARI_SIGINT_pending;   \
    PARI_SIGINT_pending = 0;         \
    raise(sig);                      \
  }                                  \
}

void
push_stack(stack **pts, void *a)
{
  stack *v = (stack*) pari_malloc(sizeof(stack));
  v->value = a;
  v->prev  = *pts; *pts = v;
}

void *
pop_stack(stack **pts)
{
  stack *s = *pts, *v;
  void *a;
  if (!s) return NULL; /* initial value */
  v = s->prev; *pts = v;
  a = s->value; pari_free((void*)s);
  return a;
}

/*********************************************************************/
/*                                                                   */
/*                               BLOCS                               */
/*                                                                   */
/*********************************************************************/
/*#define DEBUG*/
static THREAD long next_bloc;
static THREAD GEN cur_bloc=NULL; /* current bloc in bloc list */
#ifdef DEBUG
static THREAD long NUM = 0;
#endif

/* Return x, where:
 * x[-4]: reference count
 * x[-3]: adress of next bloc
 * x[-2]: adress of preceding bloc.
 * x[-1]: number of allocated blocs.
 * x[0..n-1]: malloc-ed memory. */
GEN
newbloc(long n)
{
  long *x = (long *) pari_malloc((n + BL_HEAD)*sizeof(long)) + BL_HEAD;

  bl_refc(x) = 1;
  bl_next(x) = 0; /* the NULL address */
  bl_prev(x) = (long)cur_bloc;
  bl_num(x)  = next_bloc++;
  if (cur_bloc) bl_next(cur_bloc) = (long)x;
#ifdef DEBUG
  fprintferr("+ %ld\n", ++NUM);
#endif
  if (DEBUGMEM)
  {
    if (!n) pari_warn(warner,"mallocing NULL object in newbloc");
    if (DEBUGMEM > 2)
      fprintferr("new bloc, size %6lu (no %ld): %08lx\n", n, next_bloc-1, x);
  }
  return cur_bloc = x;
}

void
gclone_refc(GEN x) { ++bl_refc(x); }

void
gunclone(GEN x)
{
  if (--bl_refc(x) > 0) return;
  BLOCK_SIGINT_START;
  if (bl_next(x)) bl_prev(bl_next(x)) = bl_prev(x);
  else
  {
    cur_bloc = (GEN)bl_prev(x);
    next_bloc = bl_num(x);
  }
  if (bl_prev(x)) bl_next(bl_prev(x)) = bl_next(x);
  if (DEBUGMEM > 2)
    fprintferr("killing bloc (no %ld): %08lx\n", bl_num(x), x);
  free((void*)bl_base(x)); /* pari_free not needed: we already block */
  BLOCK_SIGINT_END;
#ifdef DEBUG
  fprintferr("- %ld\n", NUM--);
#endif
}

/* Recursively look for clones in the container and kill them. Then kill
 * container if clone. SIGINT could be blocked until it returns */
void
killbloc(GEN x)
{
  long i, lx;
  GEN v;
  switch(typ(x))
  {
    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x);
      for (i=1;i<lx;i++) killbloc(gel(x,i));
      break;
    case t_LIST:
      v = list_data(x); lx = v? lg(v): 1;
      for (i=1;i<lx;i++) killbloc(gel(v,i));
      pari_free(v); break;
  }
  if (isclone(x)) gunclone(x);
}

int
pop_entree_bloc(entree *ep, long loc)
{
  GEN x = (GEN)ep->value;
  if (bl_num(x) < loc) return 0; /* older */
  if (DEBUGMEM>2)
    fprintferr("popping %s (bloc no %ld)\n", ep->name, bl_num(x));
  killbloc(x); return 1;
}

/*********************************************************************/
/*                                                                   */
/*                       C STACK SIZE CONTROL                        */
/*                (avoid core dump on deep recursion)                */
/*********************************************************************/
THREAD void *PARI_stack_limit = NULL;

#ifdef STACK_CHECK
/* adapted from Perl code written by Dominic Dunlop */

#  ifdef __EMX__				/* Emulate */
void
pari_stackcheck_init(void *stack_base)
{
  (void) stack_base;
  if (!stack_base) { PARI_stack_limit = NULL; return; }
  PARI_stack_limit = get_stack(1./16, 32*1024);
}
#  else /* !__EMX__ */
#include <sys/types.h>
#include <sys/time.h>
#include <sys/resource.h>

/* Set PARI_stack_limit to (a little above) the lowest safe address that can
 * be used on the stack. Leave PARI_stack_limit at its initial value (NULL)
 * to show no check should be made [init failed]. Assume stack grows downward.
 */
void
pari_stackcheck_init(void *stack_base)
{
  struct rlimit rip;
  ulong size;
  if (!stack_base) { PARI_stack_limit = NULL; return; }
  if (getrlimit(RLIMIT_STACK, &rip)) return;
  size = rip.rlim_cur;
  if (size == (ulong)RLIM_INFINITY || size > (ulong)stack_base)
    PARI_stack_limit = (void*)(((ulong)stack_base) / 16);
  else
    PARI_stack_limit = (void*)((ulong)stack_base - (size/16)*15);
}
#  endif /* !__EMX__ */

#else
void
pari_stackcheck_init(void *stack_base)
{
  PARI_stack_limit = NULL;
}
#endif /* STACK_CHECK */

/*********************************************************************/
/*                                                                   */
/*                       SYSTEM INITIALIZATION                       */
/*                                                                   */
/*********************************************************************/
static int try_to_recover = 0;
VOLATILE int PARI_SIGINT_block  = 0, PARI_SIGINT_pending = 0;
static GEN universal_constants;
static void pari_sighandler(int sig);

void
pari_free(void *pointer)
{
  BLOCK_SIGINT_START;
  free(pointer);
  BLOCK_SIGINT_END;
}

void*
pari_malloc(size_t size)
{
  if (size)
  {
    char *tmp;
    BLOCK_SIGINT_START;
    tmp = (char*)malloc(size);
    BLOCK_SIGINT_END;
    if (!tmp) pari_err(memer);
    return tmp;
  }
  if (DEBUGMEM) pari_warn(warner,"mallocing NULL object");
  return NULL;
}

void*
pari_realloc(void *pointer, size_t size)
{
  char *tmp;

  BLOCK_SIGINT_START;
  if (!pointer) tmp = (char *) malloc(size);
  else tmp = (char *) realloc(pointer,size);
  BLOCK_SIGINT_END;
  if (!tmp) pari_err(memer);
  return tmp;
}

void*
pari_calloc(size_t size)
{
  void *t = pari_malloc(size);
  memset(t, 0, size); return t;
}

GEN
cgetalloc(long t, size_t l)
{
  GEN x = (GEN)pari_malloc(l * sizeof(long));
  x[0] = evaltyp(t) | evallg(l); return x;
}

static void
dflt_sigint_fun(void) { pari_err(talker, "user interrupt"); }

static void
pari_handle_SIGINT(void)
{
#ifdef _WIN32
  if (++win32ctrlc >= 5) _exit(3);
#else
  sigint_fun();
#endif
}

#if defined(HAS_WAITPID) && defined(HAS_SETSID)
#  include <sys/wait.h>
/* Properly fork a process, detaching from main process group without creating
 * zombies on exit. Parent returns 1, son returns 0 */
int
pari_daemon(void)
{
  pid_t pid = fork();
  switch(pid) {
      case -1: return 1; /* father, fork failed */
      case 0:
	(void)setsid(); /* son becomes process group leader */
	if (fork()) exit(0); /* now son exits, also when fork fails */
	break; /* grandson: its father is the son, which exited,
		* hence father becomes 'init', that'll take care of it */
      default: /* father, fork succeeded */
	(void)waitpid(pid,NULL,0); /* wait for son to exit, immediate */
	return 1;
  }
  /* grandson */
  return 0;
}
#else
int
pari_daemon(void)
{
  pari_err(impl,"pari_daemon without waitpid & setsid");
  return 0;
}
#endif

static void
pari_sighandler(int sig)
{
  const char *msg;
#ifndef HAS_SIGACTION
  /*SYSV reset the signal handler in the handler*/
  (void)os_signal(sig,pari_sighandler);
#endif
  switch(sig)
  {
#ifdef SIGBREAK
    case SIGBREAK:
      if (PARI_SIGINT_block) PARI_SIGINT_pending=SIGBREAK;
      else pari_handle_SIGINT();
      return;
#endif

#ifdef SIGINT
    case SIGINT:
      if (PARI_SIGINT_block) PARI_SIGINT_pending=SIGINT;
      else pari_handle_SIGINT();
      return;
#endif

#ifdef SIGSEGV
    case SIGSEGV:
      msg="PARI/GP (Segmentation Fault)"; break;
#endif
#ifdef SIGBUS
    case SIGBUS:
      msg="PARI/GP (Bus Error)"; break;
#endif
#ifdef SIGFPE
    case SIGFPE:
      msg="PARI/GP (Floating Point Exception)"; break;
#endif

#ifdef SIGPIPE
    case SIGPIPE:
    {
      pariFILE *f = GP_DATA->pp->file;
      if (f && pari_outfile == f->file)
      {
	pari_err(talker, "Broken Pipe, resetting file stack...");
	GP_DATA->pp->file = NULL; /* to avoid oo recursion on error */
	pari_outfile = stdout; pari_fclose(f);
      }
      /*Do not attempt to write to stdout in case it triggered the SIGPIPE*/
      return; /* not reached */
    }
#endif

    default: msg="signal handling"; break;
  }
  pari_err(bugparier,msg);
}

#if defined(_WIN32) || defined(__CYGWIN32__)
int win32ctrlc = 0;

void
dowin32ctrlc(void)
{
  win32ctrlc = 0;
  sigint_fun();
}
#endif

/* Initialize hashtable */
static void
init_hashtable(entree **table, long tblsz)
{
  entree *ep, *EP, *last;
  long i;

  for (i = 0; i < tblsz; i++)
  {
    last = NULL; ep = table[i]; table[i] = NULL;
    for ( ; ep; ep = EP)
    {
      EP = ep->next;
      switch(EpVALENCE(ep))
      {
	case EpVAR: case EpINSTALL: /* keep this one */
	  if (last)
	    last->next = ep;
	  else
	    table[i] = ep;
	  last = ep; last->next = NULL;
	  break;
	default: freeep(ep);
      }
    }
  }
}

void
pari_init_defaults(void)
{
  initout(1);

#ifdef LONG_IS_64BIT
  precreal = 4;
#else
  precreal = 5;
#endif

  precdl = 16;
  compatible = NONE;
  DEBUGFILES = DEBUGLEVEL = DEBUGMEM = 0;
  disable_color = 1;
  logstyle = logstyle_none;

  current_psfile = pari_strdup("pari.ps");
  current_logfile= pari_strdup("pari.log");
  pari_logfile = NULL;

  pari_datadir = os_getenv("GP_DATA_DIR");
  if (!pari_datadir) pari_datadir = (char*)GPDATADIR;
  if (pari_datadir) pari_datadir = pari_strdup(pari_datadir);

  next_bloc=0;
  (void)sd_graphcolormap("[\"white\",\"black\",\"blue\",\"violetred\",\"red\",\"green\",\"grey\",\"gainsboro\"]", d_SILENT);
  (void)sd_graphcolors("[4, 5]", d_SILENT);
}

/* pari stack is a priori not available. Don't use it */
void
grow_append(growarray A, void *e)
{
  if (A->n == A->len-1)
  {
    A->len <<= 1;
    A->v = (void**)pari_realloc(A->v, A->len * sizeof(void*));
  }
  A->v[A->n++] = e;
}
void
grow_copy(growarray A, growarray B)
{
  long i;
  if (!A) { grow_init(B); return; }
  B->len = A->len;
  B->n = A->n;
  B->v = (void**)pari_malloc(B->len * sizeof(void*));
  for (i = 0; i < A->n; i++) B->v[i] = A->v[i];
}
void
grow_init(growarray A)
{
  A->len = 4;
  A->n   = 0;
  A->v   = (void**)pari_malloc(A->len * sizeof(void*));
}
void
grow_kill(growarray A) { pari_free(A->v); }

/* Load modules in A in hashtable hash. */
static int
gp_init_entrees(growarray A, entree **hash)
{
  long i;
  init_hashtable(hash, functions_tblsz);
  for (i = 0; i < A->n; i++) pari_fill_hashtable(hash, (entree*)A->v[i]);
  return (hash == functions_hash);
}

void
pari_sig_init(void (*f)(int))
{
#ifdef SIGBUS
  (void)os_signal(SIGBUS,f);
#endif
#ifdef SIGFPE
  (void)os_signal(SIGFPE,f);
#endif
#ifdef SIGINT
  (void)os_signal(SIGINT,f);
#endif
#ifdef SIGBREAK
  (void)os_signal(SIGBREAK,f);
#endif
#ifdef SIGPIPE
  (void)os_signal(SIGPIPE,f);
#endif
#ifdef SIGSEGV
  (void)os_signal(SIGSEGV,f);
#endif
}

static void
reset_traps(void)
{
  long i;
  if (DEBUGLEVEL) pari_warn(warner,"Resetting all traps");
  for (i=0; i <= noer; i++) dft_handler[i] = NULL;
}

static void
init_universal_constants(void)
{
  /* 2 (gnil) + 2 (gen_0)
   * + 3 (gen_1) + 3 (gen_m1) + 3 (gen_2) + 3 (gen_m2)
   * + 3 (half) + 3 (gi) */
  GEN p = universal_constants = (long*) pari_malloc(22*sizeof(long));
  gen_0 = p; p+=2; gnil = p; p+=2;
  gen_0[0] = gnil[0] = evaltyp(t_INT) | _evallg(2);
  gen_0[1] = gnil[1] = evallgefint(2);

  gen_1 = p; p+=3;
  gen_2 = p; p+=3;
  gen_1[0] = gen_2[0] = evaltyp(t_INT) | _evallg(3);
  gen_1[1] = gen_2[1] = evalsigne(1) | evallgefint(3);
  gen_1[2] = 1; gen_2[2]= 2;

  gen_m1 = p; p+=3;
  gen_m1[0] = evaltyp(t_INT) | _evallg(3);
  gen_m1[1] = evalsigne(-1) | evallgefint(3);
  gen_m1[2] = 1;

  gen_m2 = p; p+=3;
  gen_m2[0] = evaltyp(t_INT) | _evallg(3);
  gen_m2[1] = evalsigne(-1) | evallgefint(3);
  gen_m2[2] = 2;

  ghalf = p; p+=3; gi = p; p+=3;
  ghalf[0] = evaltyp(t_FRAC) | _evallg(3);
  gel(ghalf,1) = gen_1;
  gel(ghalf,2) = gen_2;
  gi[0] = evaltyp(t_COMPLEX) | _evallg(3);
  gel(gi,1) = gen_0;
  gel(gi,2) = gen_1;
}

static size_t
fix_size(size_t a)
{
  size_t b = (a / sizeof(long)) * sizeof(long); /* Align */
  if (b < 1024) b = 1024;
  return b;
}

static size_t
init_stack(size_t size)
{
  size_t s = fix_size(size), old = 0;
  if (bot)
  {
    old = top - bot;
    pari_free((void*)bot);
  }
  BLOCK_SIGINT_START;
  bot = (pari_sp)malloc(s); /* NOT pari_malloc, memer would be deadly */
  if (!bot)
    for (s = old;; s>>=1)
    {
      char buf[128];
      if (!s) pari_err(memer); /* no way out. Die */
      /* must use sprintf: pari stack is currently dead */
      sprintf(buf, "not enough memory, new stack %lu", (ulong)s);
      pari_warn(warner, buf, s);
      bot = (pari_sp)malloc(s);
      if (bot) break;
    }
  BLOCK_SIGINT_END;
  avma = top = bot+s;
  memused = 0; return s;
}

static entree **
init_fun_hash(void) {
  entree **H = (entree **) pari_malloc(sizeof(entree*)*functions_tblsz);
  long i;
  for (i = 0; i < functions_tblsz; i++) H[i] = NULL;
  return H;
}

growarray *pari_get_modules(void) { return &MODULES; }
growarray *pari_get_oldmodules(void) { return &OLDMODULES; }

int
gp_init_functions(void)
{
  return gp_init_entrees(new_fun_set? MODULES: OLDMODULES, functions_hash);
}

void
pari_thread_init(size_t parisize)
{
  (void)init_stack(parisize);
  pari_init_floats();
  pari_init_seadata();
}

void
pari_thread_close(void)
{
  pari_free((void *)bot);
  pari_close_floats();
  pari_close_seadata();
}

/* initialize PARI data. Initialize [new|old]fun to NULL for default set. */
void
pari_init_opts(size_t parisize, ulong maxprime, ulong init_opts)
{
  ulong u;

  pari_stackcheck_init(&u);
  if ((init_opts&INIT_DFTm)) {
    GP_DATA = default_gp_data(); gp_expand_path(GP_DATA->path);
    pari_init_defaults();
  }

  err_catch_stack=NULL;
  if ((init_opts&INIT_JMPm) && setjmp(GP_DATA->env))
  {
    fprintferr("  ***   Error in the PARI system. End of program.\n");
    exit(1);
  }
  if ((init_opts&INIT_SIGm)) pari_sig_init(pari_sighandler);
  bot = top = 0;
  (void)init_stack(parisize);
  diffptr = initprimes(maxprime);
  init_universal_constants();
  if (pari_kernel_init()) pari_err(talker,"Cannot initialize kernel");
  pari_init_parser();
  pari_init_compiler();
  pari_init_evaluator();

  varentries = (entree**) pari_malloc((MAXVARN+1)*sizeof(entree*));
  for (u=0; u <= MAXVARN; u++) varentries[u] = NULL;
  pari_init_floats();
  pari_init_seadata();

  primetab = (GEN) pari_malloc(1 * sizeof(long));
  primetab[0] = evaltyp(t_VEC) | _evallg(1);

  funct_old_hash = init_fun_hash();
  functions_hash = init_fun_hash();

  pari_fill_hashtable(funct_old_hash, oldfonctions);

  grow_init(MODULES);    grow_append(MODULES, functions_basic);
  grow_init(OLDMODULES); grow_append(OLDMODULES, oldfonctions);
  pari_fill_hashtable(functions_hash,
		      new_fun_set? functions_basic:oldfonctions);

  whatnow_fun = NULL;
  sigint_fun = dflt_sigint_fun;
  dft_handler = (GEN*) pari_malloc((noer + 1) *sizeof(GEN));
  reset_traps();
  default_exception_handler = NULL;

  pari_var_init();
  try_to_recover = 1;
}

void
pari_init(size_t parisize, ulong maxprime)
{
  pari_init_opts(parisize, maxprime, INIT_JMPm | INIT_SIGm | INIT_DFTm);
}

void
pari_close_opts(ulong init_opts)
{
  long i;

  BLOCK_SIGINT_START;
  if ((init_opts&INIT_SIGm)) pari_sig_init(SIG_DFL);

  while (delete_var()) /* empty */;
  for (i = 0; i < functions_tblsz; i++)
  {
    entree *ep = functions_hash[i];
    while (ep) {
      entree *epn = ep->next;
      if (!EpSTATIC(ep)) { freeep(ep); free(ep); }
      ep = epn;
    }
  }
  free((void*)varentries);
  free((void*)primetab);
  free((void*)universal_constants);
  pari_close_parser();
  pari_close_compiler();
  pari_close_evaluator();

  while (cur_bloc) gunclone(cur_bloc);
  killallfiles(1);
  free((void*)functions_hash);
  free((void*)funct_old_hash);
  free((void*)dft_handler);
  free((void*)bot);
  free((void*)diffptr);
  free(current_logfile);
  free(current_psfile);
  grow_kill(MODULES);
  grow_kill(OLDMODULES);
  if (pari_datadir) free(pari_datadir);
  if (init_opts&INIT_DFTm)
  { /* delete GP_DATA */
    if (GP_DATA->hist->res) free((void*)GP_DATA->hist->res);
    if (GP_DATA->pp->cmd) free((void*)GP_DATA->pp->cmd);
    if (GP_DATA->help) free((void*)GP_DATA->help);
    delete_dirs(GP_DATA->path);
    free((void*)GP_DATA->path->PATH);
  }
  BLOCK_SIGINT_END;
}

void
pari_close(void)
{
  pari_close_opts(INIT_JMPm | INIT_SIGm | INIT_DFTm);
}

struct getheap_t { long n, l; };
static void
f_getheap(GEN x, void *D)
{
  struct getheap_t *T = (struct getheap_t*)D;
  T->n++;
  T->l += taille(x);
}
GEN
getheap(void)
{
  struct getheap_t T = { 0, 0 };
  traverseheap(&f_getheap, &T);
  return mkvec2s(T.n, T.l + BL_HEAD * T.n);
}

void
traverseheap( void(*f)(GEN, void *), void *data )
{
  GEN x;
  for (x = cur_bloc; x; x = (GEN)bl_prev(x)) f(x, data);
}

/*******************************************************************/
/*                                                                 */
/*                         ERROR RECOVERY                          */
/*                                                                 */
/*******************************************************************/
/* if flag = 0: record address of next bloc allocated.
 * if flag = 1: (after an error) recover all memory allocated since last call
 */
void
recover(int flag)
{
  static long listloc;
  long n;
  entree *ep, *epnext;
  void (*sigfun)(int);

  if (!flag) { listloc = next_bloc; return; }

 /* disable recover() and SIGINT. Better: sigint_[block|release] as in
  * readline/rltty.c ? */
 if (DEBUGMEM>2) fprintferr("entering recover(), loc = %ld\n", listloc);
  try_to_recover=0;
  sigfun = os_signal(SIGINT, SIG_IGN);

  for (n = 0; n < functions_tblsz; n++)
    for (ep = functions_hash[n]; ep; ep = epnext)
    {
      epnext = ep->next;
      switch(EpVALENCE(ep))
      {
	case EpVAR:
	  while (pop_val_if_newer(ep,listloc)) /* empty */;
	  break;
	case EpNEW: break;
      }
    }
  parser_reset();
  compiler_reset();
  closure_reset();
  if (DEBUGMEM>2) fprintferr("leaving recover()\n");
  try_to_recover=1;
  (void)os_signal(SIGINT, sigfun);
}

static THREAD long dbg = -1;
void
dbg_block() { if (DEBUGLEVEL) { dbg = DEBUGLEVEL; DEBUGLEVEL = 0; } }
void
dbg_release() { if (dbg >= 0) { DEBUGLEVEL = dbg; dbg = -1; } }

#define MAX_PAST 25
#define STR_LEN 20
/* Outputs a beautiful error message (not \n terminated)
 *   msg is errmessage to print.
 *   s points to the offending chars.
 *   entry tells how much we can go back from s[0].
 */
void
errcontext(const char *msg, const char *s, const char *entry)
{
  long past = (s-entry);
  char str[STR_LEN + 2];
  char *buf, *t, *pre;

  if (!s || !entry) { print_prefixed_text(msg,"  ***   ",NULL); return; }

  t = buf = (char*)pari_malloc(strlen(msg) + MAX_PAST + 5 + 2 * 16);
  sprintf(t,"%s: ", msg);
  if (past <= 0) past = 0;
  else
  {
    t += strlen(t);
    if (past > MAX_PAST) { past=MAX_PAST; strcpy(t, "..."); t += 3; }
    strcpy(t, term_get_color(c_OUTPUT));
    t += strlen(t);
    strncpy(t, s - past, past); t[past] = 0;
  }

  t = str; if (!past) *t++ = ' ';
  strncpy(t, s, STR_LEN); t[STR_LEN] = 0;
  pre = (char*)pari_malloc(2 * 16 + 1);
  strcpy(pre, term_get_color(c_ERR));
  strcat(pre, "  ***   ");
  print_prefixed_text(buf, pre, str);
  pari_free(buf); pari_free(pre);
}

void *
err_catch(long errnum, jmp_buf *penv)
{
  cell *v;
  /* for fear of infinite recursion... */
  if (errnum == memer) pari_err(talker, "can't trap memory errors");
  if (errnum == CATCH_ALL) errnum = noer;
  if (errnum > noer) pari_err(talker, "no such error number: %ld", errnum);
  v = (cell*)pari_malloc(sizeof(cell));
  v->penv  = penv;
  v->flag = errnum;
  push_stack(&err_catch_stack, (void*)v);
  return (void*)v;
}

static void
pop_catch_cell(stack **s)
{
  cell *c = (cell*)pop_stack(s);
  if (c) pari_free(c);
}

/* reset traps younger than v (included).
 * Note the address of v is passed instead because we do not want compiler
 * to put v into a register (could be clobbered by longjmp) */
void
err_leave(void **pv)
{
  while (err_catch_stack)
  {
    cell *t = (cell*)err_catch_stack->value;
    pop_catch_cell(&err_catch_stack);
    if (t == (cell*)(*pv)) return;
  }
  reset_traps();
}

/* Get last (most recent) handler for error n (or generic noer) killing all
 * more recent non-applicable handlers (now obsolete) */
static cell *
err_seek(long n)
{
  while (err_catch_stack)
  {
    cell *t = (cell*)err_catch_stack->value;
    if (t->flag == n || t->flag == noer) return t;
    pop_catch_cell(&err_catch_stack);
  }
  return NULL;
}

/* untrapped error: kill all error handlers */
static void
err_clean(void)
{
  while (err_catch_stack)
    pop_catch_cell(&err_catch_stack);
  gp_function_name = NULL;
}

static int
is_warn(long num)
{
  return num == warner || num == warnmem || num == warnfile || num == warnprec;
}

void
err_recover(long numerr)
{
  initout(0);
  dbg_release();
  killallfiles(0);
  err_clean();

  if (pariErr->die) pariErr->die();    /* Caller wants to catch exceptions? */
  global_err_data = NULL;
  fprintferr("\n"); flusherr();

  /* reclaim memory stored in "blocs" */
  if (try_to_recover) recover(1);
  longjmp(GP_DATA->env, numerr);
}

void
pari_warn(long numerr, ...)
{
  char *ch1;
  PariOUT *out = pariOut;
  va_list ap;

  va_start(ap,numerr);

  if (!pari_last_was_newline())
    pari_putc('\n'); /* make sure pari_err msg starts at the beginning of line */
  pari_flush(); pariOut = pariErr;
  pari_flush(); term_color(c_ERR);

  if (numerr == user) {
    GEN g = va_arg(ap, GEN);
    pari_printf("  ***   user warning: ");
    print0(g, f_RAW);
    pari_putc('\n');
  } else {
    if (gp_function_name)
      pari_printf("  *** %s: %s", gp_function_name, errmessage[numerr]);
    else
      pari_printf("  ***   %s", errmessage[numerr]);
    switch (numerr)
    {
      case warnmem: case warner:
        pari_putc(' '); ch1=va_arg(ap, char*);
        pari_vprintf(ch1,ap); pari_puts(".\n");
        break;

      case warnprec:
        pari_vprintf(" in %s; new prec = %ld\n",ap);
        break;

      case warnfile:
        ch1=va_arg(ap, char*);
        pari_printf(" %s: %s\n", ch1, va_arg(ap, char*));
        break;
    }
  }
  term_color(c_NONE); va_end(ap);
  pariOut = out;
  flusherr();
}

#define HAS_CONTEXT(num) (num < talker)
#define SYNTAX_ERROR(num) (num < openfiler)

void
pari_err(long numerr, ...)
{
  char s[128], *ch1;
  PariOUT *out = pariOut;
  va_list ap;

  va_start(ap,numerr);
  if (is_warn(numerr)) pari_err(talker,"use pari_warn for warnings");

  global_err_data = NULL;
  if (err_catch_stack && !SYNTAX_ERROR(numerr))
  {
    cell *trapped = NULL;
    if ( (trapped = err_seek(numerr)) )
    {
      jmp_buf *e = trapped->penv;
      if (numerr == invmoder)
      {
	(void)va_arg(ap, char*); /* junk 1st arg */
	global_err_data = (void*)va_arg(ap, GEN);
      }
      longjmp(*e, numerr);
    }
  }
  /* make sure pari_err msg starts at the beginning of line */
  if (!pari_last_was_newline()) pari_putc('\n');
  pariOut->flush();
  pariErr->flush();
  pariOut = pariErr;
  term_color(c_ERR);

  if (HAS_CONTEXT(numerr))
  {
    strcpy(s, errmessage[numerr]);
    switch (numerr)
    {
      case obsoler:
	errcontext(s,NULL,NULL);
	ch1 = va_arg(ap,char *);
	whatnow_new_syntax(ch1, va_arg(ap,int));
	break;

      case openfiler:
	sprintf(s+strlen(s), "%s file", va_arg(ap,char*));
	ch1 = va_arg(ap,char *);
	errcontext(s,ch1,ch1); break;

      case talker2:
	strcat(s,va_arg(ap, char*)); /* fall through */
      default:
	ch1 = va_arg(ap,char *);
	errcontext(s,ch1,va_arg(ap,char *));
    }
  }
  else if (numerr == user)
  {
    GEN g = va_arg(ap, GEN);
    pari_printf("  ***   user error: ");
    print0(g, f_RAW);
  }
  else
  {
    if (gp_function_name)
      pari_printf("  *** %s: %s", gp_function_name, errmessage[numerr]);
    else
      pari_printf("  ***   %s", errmessage[numerr]);
    switch (numerr)
    {
      case talker: case siginter: case alarmer: case invmoder:
	ch1=va_arg(ap, char*);
	pari_vprintf(ch1,ap); pari_putc('.'); break;

      case impl:
	ch1=va_arg(ap, char*);
	pari_printf(" %s is not yet implemented.",ch1); break;

      case typeer: case mattype1:
      case infprecer: case negexper:
      case constpoler: case notpoler: case redpoler:
      case zeropoler: case consister: case flagerr: case precer:
	pari_printf(" in %s.",va_arg(ap, char*)); break;

      case bugparier:
	pari_printf(" %s, please report",va_arg(ap, char*)); break;

      case operi: case operf:
      {
        const char *f, *op = va_arg(ap, const char*);
	GEN x = va_arg(ap, GEN);
	GEN y = va_arg(ap, GEN);
	     if (*op == '+') f = "addition";
	else if (*op == '*') f = "multiplication";
	else if (*op == '/' || *op == '%' || *op == '\\') f = "division";
	else if (*op == 'g') { op = ","; f = "gcd"; }
	else { op = "-->"; f = "assignment"; }
	pari_printf(" %s %s %s %s.",f,type_name(typ(x)),op,type_name(typ(y)));
	break;
      }

      case primer2:
	pari_printf("%lu.", va_arg(ap, ulong));
	break;
    }
  }
  term_color(c_NONE); va_end(ap);
  if (numerr==errpile)
  {
    size_t d = top - bot;
    char buf[256];
    /* don't use pari_printf: it needs the PARI stack for %.3f conversion */
    sprintf(buf, "\n  current stack size: %lu (%.3f Mbytes)\n",
                 (ulong)d, (double)d/1048576.);
    pariErr->puts(buf);
    pariErr->puts("  [hint] you can increase GP stack with allocatemem()\n");
  }
  pariOut = out;
  gp_function_name=NULL;
  if (default_exception_handler && !SYNTAX_ERROR(numerr))
  {
    if (dft_handler[numerr])
      global_err_data = (void *) dft_handler[numerr];
    else
      global_err_data = (void *) dft_handler[noer];
    if (default_exception_handler(numerr)) { flusherr(); return; }
  }
  err_recover(numerr);
}

void
whatnow_new_syntax(const char *f, long n)
{
  term_color(c_NONE);
  print_text("\nFor full compatibility with GP 1.39.15, type \"default(compatible,3)\", or set \"compatible = 3\" in your GPRC file.");
  pari_putc('\n');
  (void)whatnow_fun(f, -n);
}

static void
kill_dft_handler(int numerr)
{
  GEN s = dft_handler[numerr];
  if (s && s != BREAK_LOOP) gunclone(s);
  dft_handler[numerr] = NULL;
}


/* Try f (trapping error e), recover using r (break_loop, if NULL) */
GEN
trap0(const char *e, GEN r, GEN f)
{
  long numerr = CATCH_ALL;
  GEN F;
       if (!strcmp(e,"errpile")) numerr = errpile;
  else if (!strcmp(e,"typeer")) numerr = typeer;
  else if (!strcmp(e,"gdiver")) numerr = gdiver;
  else if (!strcmp(e,"invmoder")) numerr = invmoder;
  else if (!strcmp(e,"archer")) numerr = archer;
  else if (!strcmp(e,"siginter")) numerr = siginter;
  else if (!strcmp(e,"alarmer")) numerr = alarmer;
  else if (!strcmp(e,"talker")) numerr = talker;
  else if (!strcmp(e,"user")) numerr = user;
  else if (*e) pari_err(impl,"this trap keyword");
  /* TO BE CONTINUED */

  if (f && r)
  { /* explicit recovery text */
    GEN x = closure_trapgen(numerr,f);
    if (x == (GEN)1L) { gp_function_name = NULL; x = closure_evalgen(r); }
    return x;
  }

  F = f? f: r; /* define a default handler */
 /* will execute F (break loop if F = NULL), then jump to 'env' */
  if (numerr == CATCH_ALL) numerr = noer;
  kill_dft_handler(numerr);
  dft_handler[numerr] = F? gclone(F): BREAK_LOOP;
  return gnil;
}

/*******************************************************************/
/*                                                                */
/*                       CLONING & COPY                            */
/*                  Replicate an existing GEN                      */
/*                                                                 */
/*******************************************************************/
/* lontyp[tx] = 0 (non recursive type) or number of codewords for type tx */
const  long lontyp[] = { 0,0,0,1,1,2,1,2,1,1, 2,2,0,1,1,1,1,1,1,1, 0,0,0,2 };

static GEN
list_internal_copy(GEN z, long nmax)
{
  long i, l;
  GEN a;
  if (!z) return NULL;
  l = lg(z);
  a = (GEN)pari_malloc((nmax+1) * sizeof(long));
  for (i = 1; i < l; i++) gel(a,i) = gclone( gel(z,i) );
  a[0] = z[0]; return a;
}

static void
listassign(GEN x, GEN y)
{
  long nmax = list_nmax(x);
  GEN L = list_data(x);
  if (!nmax && L) nmax = lg(L) + 32; /* not malloc'ed yet */
  list_nmax(y) = nmax;
  list_data(y) = list_internal_copy(L, nmax);
}

/* copy lisst on the PARI stack */
GEN
listcopy(GEN x)
{
  GEN y = listcreate(), L = list_data(x), a;
  long i, lx;
  if (!L) return y;
  lx = lg(L); list_data(y) = a = cgetg(lx, t_VEC);
  for (i = 1; i < lx; i++) gel(a,i) = gcopy(gel(L,i));
  return y;
}

/* x is a t_INT equal to 0 ? tx == t_INT && lx == 2 */
#define is_0INT(x) \
    (((x)[0] & (TYPBITS|LGBITS)) == (evaltyp(t_INT)|_evallg(2)))

/* assume x is non-recursive. For efficiency return gen_0 instead of a copy
 * for a 0 t_INT */
INLINE GEN
copy_leaf(GEN x, long tx)
{
  long i, lx;
  GEN y;

  if (is_0INT(x)) return gen_0; /* very common */
  switch(tx)
  {
    case t_INT:
      lx = lgefint(x);
      y = cgeti(lx); break;
    case t_LIST: return listcopy(x); /* allocated on the stack */
    default:
      lx = lg(x);
      y = cgetg_copy(lx, x); break;
  }
  for (i=1; i<lx; i++) y[i] = x[i]; /* no memcpy: avma and x may overlap */
  return y;
}

GEN
gcopy(GEN x)
{
  long tx = typ(x), lx, i;
  GEN y;

  if (! is_recursive_t(tx)) return copy_leaf(x, tx);
  lx = lg(x); y = cgetg_copy(lx, x);
  if (lontyp[tx] == 1) i = 1; else { y[1] = x[1]; i = 2; }
  for (; i<lx; i++) gel(y,i) = gcopy(gel(x,i));
  return y;
}

/* as gcopy, but truncate to the first lx components if recursive type
 * [ leaves use their own lg ]. No checks. */
GEN
gcopy_lg(GEN x, long lx)
{
  long tx = typ(x), i;
  GEN y;

  if (! is_recursive_t(tx)) return copy_leaf(x, tx);
  y = cgetg(lx, tx); /* cgetg_copy would be incorrect if lx < lg(x) */
  if (lontyp[tx] == 1) i = 1; else { y[1] = x[1]; i = 2; }
  for (; i<lx; i++) gel(y,i) = gcopy(gel(x,i));
  return y;
}

GEN
shallowcopy(GEN x)
{
  long tx = typ(x), lx = lg(x), i;
  GEN y = cgetg_copy(lx, x);

  switch(tx)
  {
    case t_POLMOD:
      y[1] = x[1]; gel(y,2) = shallowcopy(gel(x,2));
      break;
    case t_MAT:
      for (i=lx-1;i;i--) gel(y,i) = shallowcopy(gel(x,i));
      break;
    default:
      for (i=lx-1;i;i--) y[i] = x[i];
  }
  return y;
}

/* cf cgetg_copy: "allocate" (by updating first codeword only) for subsequent
 * copy of x, as if avma = *AVMA. Assume lg(x) == lx */
INLINE GEN
cgetg_copy_av(long lx, GEN x, pari_sp *AVMA) {
  GEN z = ((GEN)*AVMA) - lx;
  z[0] = x[0] & (TYPBITS|LGBITS);
  *AVMA = (pari_sp)z; return z;
}

/* copy x as if avma = *AVMA, update *AVMA */
GEN
gcopy_avma(GEN x, pari_sp *AVMA)
{
  long i, lx, tx = typ(x);
  GEN y;

  if (! is_recursive_t(tx))
  {
    switch(tx)
    {
      case t_INT:
        *AVMA = (pari_sp)icopy_avma(x, *AVMA);
        return (GEN)*AVMA;
      case t_LIST:
	y = cgetg_copy_av(3, x, AVMA);
	listassign(x, y); return y;
    }
    lx = lg(x); y = cgetg_copy_av(lx, x, AVMA);
    for (i=1; i<lx; i++) y[i] = x[i];
  }
  else
  {
    lx = lg(x); y = cgetg_copy_av(lx, x, AVMA);
    if (lontyp[tx] == 1) i = 1; else { y[1] = x[1]; i = 2; }
    for (; i<lx; i++) gel(y,i) = gcopy_avma(gel(x,i), AVMA);
  }
  return y;
}

/* [copy_bin/bin_copy:] same as gcopy_avma but use NULL to code an exact 0, and
 * make shallow copies of t_LISTs */
static GEN
gcopy_av0(GEN x, pari_sp *AVMA)
{
  long i, lx, tx = typ(x);
  GEN y;

  if (! is_recursive_t(tx))
  {
    if (is_0INT(x)) return NULL; /* special marker */
    if (tx == t_INT) {
      *AVMA = (pari_sp)icopy_avma(x, *AVMA);
      return (GEN)*AVMA;
    }
    lx = lg(x); y = cgetg_copy_av(lx, x, AVMA);
    for (i=1; i<lx; i++) y[i] = x[i];
  }
  else
  {
    lx = lg(x); y = cgetg_copy_av(lx, x, AVMA);
    if (lontyp[tx] == 1) i = 1; else { y[1] = x[1]; i = 2; }
    for (; i<lx; i++) gel(y,i) = gcopy_av0(gel(x,i), AVMA);
  }
  return y;
}

INLINE GEN
icopy_avma_canon(GEN x, pari_sp AVMA)
{
  long i, lx = lgefint(x);
  GEN y = ((GEN)AVMA) - lx;
  y[0] = evaltyp(t_INT)|evallg(lx); /* kills isclone */
  y[1] = x[1]; x = int_MSW(x);
  for (i=2; i<lx; i++, x = int_precW(x)) y[i] = *x;
  return y;
}

/* [copy_bin_canon/bin_copy_canon:] same as gcopy_av0, but copy integers in
 * canonical (native kernel) form and make a full copy of t_LISTs */
static GEN
gcopy_av0_canon(GEN x, pari_sp *AVMA)
{
  long i,lx,tx=typ(x);
  GEN y;

  if (! is_recursive_t(tx))
  {
    if (is_0INT(x)) return NULL; /* special marker */
    switch(tx)
    {
      case t_INT: 
        *AVMA = (pari_sp)icopy_avma_canon(x, *AVMA);
        return (GEN)*AVMA;
      case t_LIST:
      {
	GEN y = cgetg_copy_av(3, x, AVMA), z = list_data(x);
	if (z) {
	  list_data(y) = gcopy_av0_canon(z, AVMA);
	  list_nmax(y) = lg(z)-1;
	} else {
	  list_data(y) = NULL;
	  list_nmax(y) = 0;
	}
	return y;
      }
    }
    lx = lg(x); y = cgetg_copy_av(lx, x, AVMA);
    for (i=1; i<lx; i++) y[i] = x[i];
  }
  else
  {
    lx = lg(x); y = cgetg_copy_av(lx, x, AVMA);
    if (lontyp[tx] == 1) i = 1; else { y[1] = x[1]; i = 2; }
    for (; i<lx; i++) gel(y,i) = gcopy_av0_canon(gel(x,i), AVMA);
  }
  return y;
}

/* [copy_bin/bin_copy:] size (number of words) required for gcopy_av0(x) */
static long
taille0(GEN x)
{
  long i,n,lx, tx = typ(x);
  if (!is_recursive_t(tx))
  {
    if (is_0INT(x)) return 0;
    switch(tx)
    {
      case t_INT: return lgefint(x);
      case t_LIST:
      {
	GEN L = list_data(x);
	return L? 3 + taille0(L): 3;
      }
      default: return lg(x);
    }
  }
  n = lx = lg(x);
  for (i=lontyp[tx]; i<lx; i++) n += taille0(gel(x,i));
  return n;
}

/* [copy_bin/bin_copy:] size (number of words) required for gcopy_av0(x) */
static long
taille0_nolist(GEN x)
{
  long i,n,lx, tx = typ(x);
  if (!is_recursive_t(tx))
  {
    if (is_0INT(x)) return 0;
    return (tx == t_INT)? lgefint(x): lg(x);
  }
  n = lx = lg(x);
  for (i=lontyp[tx]; i<lx; i++) n += taille0_nolist(gel(x,i));
  return n;
}

long
taille(GEN x)
{
  long i,n,lx, tx = typ(x);
  if (!is_recursive_t(tx))
    return (tx == t_INT)? lgefint(x): lg(x);
  n = lx = lg(x);
  for (i=lontyp[tx]; i<lx; i++) n += taille(gel(x,i));
  return n;
}

long
taille2(GEN x) { return taille(x) * sizeof(long); }

GEN
gclone(GEN x)
{
  long i,lx,tx = typ(x), t = taille(x);
  GEN y = newbloc(t);
  if (!is_recursive_t(tx))
  {
    switch(tx)
    {
      case t_INT:
	lx = lgefint(x);
	y[0] = evaltyp(t_INT)|evallg(lx);
	for (i=1; i<lx; i++) y[i] = x[i];
	break;
      case t_LIST:
	y[0] = evaltyp(t_LIST)|_evallg(3);
	listassign(x, y);
	break;
      default:
	lx = lg(x);
	for (i=0; i<lx; i++) y[i] = x[i];
	break;
    }
  }
  else
  {
    pari_sp AVMA = (pari_sp)(y + t);
    lx = lg(x);
    y[0] = x[0];
    if (lontyp[tx] == 1) i = 1; else { y[1] = x[1]; i = 2; }
    for (; i<lx; i++) gel(y,i) = gcopy_avma(gel(x,i), &AVMA);
  }
  setisclone(y); return y;
}

static void
shiftaddress(GEN x, long dec)
{
  long i, lx, tx = typ(x);
  if (is_recursive_t(tx))
  {
    lx = lg(x);
    for (i=lontyp[tx]; i<lx; i++) {
      if (!x[i]) gel(x,i) = gen_0;
      else
      {
	x[i] += dec;
	shiftaddress(gel(x,i), dec);
      }
    }
  }
}

static void
shiftaddress_canon(GEN x, long dec)
{
  long i, lx, tx = typ(x);
  if (!is_recursive_t(tx))
  {
    if (tx == t_INT) {
      GEN y;
      lx = lgefint(x); if (lx <= 3) return;
      y = x + 2;
      x = int_MSW(x);  if (x == y) return;
      while (x > y) { lswap(*x, *y); x = int_precW(x); y++; }
    } else if (tx == t_LIST) {
      GEN Lx = list_data(x);
      if (Lx) {
	pari_sp av = avma;
	GEN L = (GEN)((long)Lx+dec);
	shiftaddress_canon(L, dec);
	list_data(x) = list_internal_copy(L, lg(L)); avma = av;
      }
    }
  }
  else
  {
    lx = lg(x);
    for (i=lontyp[tx]; i<lx; i++) {
      if (!x[i]) gel(x,i) = gen_0;
      else
      {
	x[i] += dec;
	shiftaddress_canon(gel(x,i), dec);
      }
    }
  }
}

/* return a clone of x structured as a gcopy */
GENbin*
copy_bin(GEN x)
{
  long t = taille0_nolist(x);
  GENbin *p = (GENbin*)pari_malloc(sizeof(GENbin) + t*sizeof(long));
  pari_sp AVMA = (pari_sp)(GENbase(p) + t);
  p->canon = 0;
  p->len = t;
  p->x   = gcopy_av0(x, &AVMA);
  p->base= (GEN)AVMA; return p;
}

/* same, writing t_INT in canonical native form */
GENbin*
copy_bin_canon(GEN x)
{
  long t = taille0(x);
  GENbin *p = (GENbin*)pari_malloc(sizeof(GENbin) + t*sizeof(long));
  pari_sp AVMA = (pari_sp)(GENbase(p) + t);
  p->canon = 1;
  p->len = t;
  p->x   = gcopy_av0_canon(x, &AVMA);
  p->base= (GEN)AVMA; return p;
}

/* p from copy_bin. Copy p->x back to stack, then destroy p */
GEN
bin_copy(GENbin *p)
{
  GEN x, y, base;
  long dx, len;

  x   = p->x; if (!x) { pari_free(p); return gen_0; }
  len = p->len;
  base= p->base; dx = x - base;
  y = (GEN)memcpy((void*)new_chunk(len), (void*)GENbase(p), len*sizeof(long));
  y += dx;
  if (p->canon)
    shiftaddress_canon(y, (y-x)*sizeof(long));
  else
    shiftaddress(y, (y-x)*sizeof(long));
  pari_free(p); return y;
}

/*******************************************************************/
/*                                                                 */
/*                         STACK MANAGEMENT                        */
/*                                                                 */
/*******************************************************************/
/* gerepileupto(av, gcopy(x)) */
GEN
gerepilecopy(pari_sp av, GEN x)
{
  GENbin *p = copy_bin(x);
  avma = av; return bin_copy(p);
}

/* Takes an array of pointers to GENs, of length n. Copies all
 * objects to contiguous locations and cleans up the stack between
 * av and avma. */
void
gerepilemany(pari_sp av, GEN* gptr[], int n)
{
  GENbin **l = (GENbin**)pari_malloc(n*sizeof(GENbin*));
  int i;
  for (i=0; i<n; i++) l[i] = copy_bin(*(gptr[i]));
  avma = av;
  for (i=0; i<n; i++) *(gptr[i]) = bin_copy(l[i]);
  pari_free(l);
}

void
gerepileall(pari_sp av, int n, ...)
{
  GENbin **l = (GENbin**)pari_malloc(n*sizeof(GENbin*));
  GEN **gptr  = (GEN**)  pari_malloc(n*sizeof(GEN*));
  int i;
  va_list a; va_start(a, n);

  for (i=0; i<n; i++) { gptr[i] = va_arg(a,GEN*); l[i] = copy_bin(*(gptr[i])); }
  avma = av;
  for (--i; i>=0; i--) *(gptr[i]) = bin_copy(l[i]);
  pari_free(l); pari_free(gptr);
}

void
gerepilecoeffs(pari_sp av, GEN x, int n)
{
  int i;
  for (i=0; i<n; i++) gel(x,i) = (GEN)copy_bin(gel(x,i));
  avma = av;
  for (i=0; i<n; i++) gel(x,i) = bin_copy((GENbin*)x[i]);
}

void
gerepilecoeffs2(pari_sp av, GEN x, int n, GEN y, int o)
{
  int i;
  for (i=0; i<n; i++) gel(x,i) = (GEN)copy_bin(gel(x,i));
  for (i=0; i<o; i++) gel(y,i) = (GEN)copy_bin(gel(y,i));
  avma = av;
  for (i=0; i<n; i++) gel(x,i) = bin_copy((GENbin*)x[i]);
  for (i=0; i<o; i++) gel(y,i) = bin_copy((GENbin*)y[i]);
}

INLINE void
dec_gerepile(pari_sp *x, pari_sp av0, pari_sp av, pari_sp tetpil, size_t dec)
{
  if (*x < av && *x >= av0)
  { /* update address if in stack */
    if (*x < tetpil) *x += dec;
    else pari_err(talker, "significant pointers lost in gerepile! (please report)");
  }
}

void
gerepileallsp(pari_sp av, pari_sp tetpil, int n, ...)
{
  const pari_sp av0 = avma;
  const size_t dec = av-tetpil;
  int i;
  va_list a; va_start(a, n);
  (void)gerepile(av,tetpil,NULL);
  for (i=0; i<n; i++) dec_gerepile((pari_sp*)va_arg(a,GEN*), av0,av,tetpil,dec);
}

/* Takes an array of pointers to GENs, of length n.
 * Cleans up the stack between av and tetpil, updating those GENs. */
void
gerepilemanysp(pari_sp av, pari_sp tetpil, GEN* gptr[], int n)
{
  const pari_sp av0 = avma;
  const size_t dec = av-tetpil;
  int i;
  (void)gerepile(av,tetpil,NULL);
  for (i=0; i<n; i++) dec_gerepile((pari_sp*)gptr[i], av0, av, tetpil, dec);
}

/* Takes an array of GENs (cast to longs), of length n.
 * Cleans up the stack between av and tetpil, updating those GENs. */
void
gerepilecoeffssp(pari_sp av, pari_sp tetpil, long *g, int n)
{
  const pari_sp av0 = avma;
  const size_t dec = av-tetpil;
  int i;
  (void)gerepile(av,tetpil,NULL);
  for (i=0; i<n; i++,g++) dec_gerepile((pari_sp*)g, av0, av, tetpil, dec);
}

static int
dochk_gerepileupto(GEN av, GEN x)
{
  long i,lx,tx;
  if (!isonstack(x)) return 1;
  if (x > av)
  {
    pari_warn(warner,"bad object %Ps",x);
    return 0;
  }
  tx = typ(x);
  if (! is_recursive_t(tx)) return 1;

  lx = lg(x);
  for (i=lontyp[tx]; i<lx; i++)
    if (!dochk_gerepileupto(av, gel(x,i)))
    {
      pari_warn(warner,"bad component %ld in object %Ps",i,x);
      return 0;
    }
  return 1;
}
/* check that x and all its components are out of stack, or have been
 * created after av */
int
chk_gerepileupto(GEN x) { return dochk_gerepileupto(x, x); }

/* print stack between avma & av */
void
dbg_gerepile(pari_sp av)
{
  GEN x = (GEN)avma;
  while (x < (GEN)av)
  {
    const long tx = typ(x), lx = lg(x);
    GEN a;

    pari_printf(" [%ld] %Ps:", x - (GEN)avma, x);
    if (! is_recursive_t(tx)) { pari_putc('\n'); x += lx; continue; }
    a = x + lontyp[tx]; x += lx;
    for (  ; a < x; a++) pari_printf("  %Ps,", *a);
    pari_printf("\n");
  }
}
void
dbg_gerepileupto(GEN q)
{
  fprintferr("%Ps:\n", q);
  dbg_gerepile((pari_sp) (q+lg(q)));
}

GEN
gerepile(pari_sp av, pari_sp tetpil, GEN q)
{
  const size_t dec = av - tetpil;
  const pari_sp av0 = avma;
  GEN x, a;

  if (dec == 0) return q;
  if ((long)dec < 0) pari_err(talker,"lbot>ltop in gerepile");

  /* dec_gerepile(&q, av0, av, tetpil, dec), saving 1 comparison */
  if (q >= (GEN)av0 && q < (GEN)tetpil)
    q = (GEN) (((pari_sp)q) + dec);

  for (x = (GEN)av, a = (GEN)tetpil; a > (GEN)av0; ) *--x = *--a;
  avma = (pari_sp)x;
  while (x < (GEN)av)
  {
    const long tx = typ(x), lx = lg(x);

    if (! is_recursive_t(tx)) { x += lx; continue; }
    a = x + lontyp[tx]; x += lx;
    for (  ; a < x; a++) dec_gerepile((pari_sp*)a, av0, av, tetpil, dec);
  }
  return q;
}

long
allocatemoremem(size_t newsize)
{
  size_t s;
  if (!newsize) newsize = (top - bot) << 1;
  s = init_stack(newsize);
  pari_warn(warner,"new stack size = %lu (%.3f Mbytes)", s, s/1048576.);
  return s;
}

/* alternate stack management routine */
stackzone *
switch_stack(stackzone *z, long n)
{
  if (!z)
  { /* create parallel stack */
    size_t size = n*sizeof(long) + sizeof(stackzone);
    z = (stackzone*) pari_malloc(size);
    z->zonetop = ((pari_sp)z) + size;
    return z;
  }

  if (n)
  { /* switch to parallel stack */
    z->bot     = bot;
    z->top     = top;
    z->avma    = avma;
    z->memused = memused;
    bot     = (pari_sp) (z+1);
    top     = z->zonetop;
    avma    = top;
    memused = DISABLE_MEMUSED;
  }
  else
  { /* back to normalcy */
    bot     = z->bot;
    top     = z->top;
    avma    = z->avma;
    memused = z->memused;
  }
  return NULL;
}

void
fill_stack(void)
{
  GEN x = ((GEN)bot);
  while (x < (GEN)avma) *x++ = 0xfefefefeUL;
}

void
debug_stack(void)
{
  GEN z;
  fprintferr("bot=0x%lx\ttop=0x%lx\n", bot, top);
  for (z = (GEN)top; z >= (GEN)avma; z--)
    fprintferr("%p:\t0x%lx\t%lu\n",z,*z,*z);
}

long
getstack(void) { return top-avma; }

/*******************************************************************/
/*                                                                 */
/*                               TIMER                             */
/*                                                                 */
/*******************************************************************/

#if !defined(USE_GETRUSAGE) && !defined(USE_FTIME)
static long
_get_time(pari_timer *T, long Ticks, long TickPerSecond)
{
  long s  = Ticks / TickPerSecond;
  long us = (long) ((Ticks % TickPerSecond) * (1000000. / TickPerSecond));
  long delay = 1000 * (s - T->s) + (us - T->us) / 1000;
  T->us = us;
  T->s  = s; return delay;
}
#endif

#ifdef USE_TIMES

# include <sys/times.h>
# include <sys/time.h>
# include <time.h>
long
TIMER(pari_timer *T)
{
  struct tms t; times(&t);
  return _get_time(T, t.tms_utime,
#ifdef _SC_CLK_TCK
		      sysconf(_SC_CLK_TCK)
#else
		      CLK_TCK
#endif
  );
}
#elif defined(USE_GETRUSAGE)

# include <sys/time.h>
# include <sys/resource.h>
long
TIMER(pari_timer *T)
{
  struct rusage r;
  struct timeval t;
  long delay;

  getrusage(0,&r); t = r.ru_utime;
  delay = 1000 * (t.tv_sec - T->s) + (t.tv_usec - T->us) / 1000;
  T->us = t.tv_usec;
  T->s  = t.tv_sec; return delay;
}
#elif defined(USE_FTIME)

# include <sys/timeb.h>
long
TIMER(pari_timer *T)
{
  struct timeb t;
  long delay;

  ftime(&t);
  delay = 1000 * (t.time - T->s) + (t.millitm - T->us / 1000);
  T->us = t.millitm * 1000;
  T->s  = t.time; return delay;
}
#elif defined(WINCE)
long
TIMER(pari_timer *T)
{
  return _get_time(T, GetTickCount(), 1000);
}
#else

# include <time.h>
# ifndef CLOCKS_PER_SEC
#   define CLOCKS_PER_SEC 1000000 /* may be false on YOUR system */
# endif
long
TIMER(pari_timer *T)
{
  return _get_time(T, clock(), CLOCKS_PER_SEC);
}
#endif
void
TIMERstart(pari_timer *T) { (void)TIMER(T); }

long
timer(void)   { static THREAD pari_timer T; return TIMER(&T);}
long
timer2(void)  { static THREAD pari_timer T; return TIMER(&T);}

void
msgTIMER(pari_timer *T, const char *format, ...)
{
  va_list args;
  PariOUT *out = pariOut; pariOut = pariErr;

  pari_puts("Time "); va_start(args, format);
  pari_vprintf(format,args); va_end(args);
  pari_printf(": %ld\n", TIMER(T)); pari_flush();
  pariOut = out;
}

void
msgtimer(const char *format, ...)
{
  va_list args;
  PariOUT *out = pariOut; pariOut = pariErr;

  pari_puts("Time "); va_start(args, format);
  pari_vprintf(format,args); va_end(args);
  pari_printf(": %ld\n", timer2()); pari_flush();
  pariOut = out;
}

long
gettime(void) { return timer(); }

/*******************************************************************/
/*                                                                 */
/*                   FUNCTIONS KNOWN TO THE ANALYZER               */
/*                                                                 */
/*******************************************************************/
GEN
pari_version(void) {
  GEN v = cgetg(4, t_VEC);
  const ulong mask = (1<<PARI_VERSION_SHIFT) - 1;
  ulong major, minor, patch, n = PARI_VERSION_CODE;
  patch = n & mask; n >>= PARI_VERSION_SHIFT;
  minor = n & mask; n >>= PARI_VERSION_SHIFT;
  major = n;
  gel(v,1) = utoi(major);
  gel(v,2) = utoi(minor);
  gel(v,3) = utoi(patch); return v;
}

GEN
geni(void) { return gi; }

/* List of GP functions:
 * ---------------------
 * Format (struct entree) :
 *   char *name    : name (under GP).
 *   ulong valence : used to form arg list, now often handled by code.
 *   void *value   : For PREDEFINED FUNCTIONS: C function to call.
 *                   For USER FUNCTIONS: pointer to defining data (bloc) =
 *                    entree*: NULL, list of entree (arguments), NULL
 *                    char*  : function text
 *   long menu     : which help section do we belong to (See below).
 *   char *code    : argument list (See below).
 *   entree *next  : next entree (init to NULL, used in hashing code).
 *   char *help    : short help text (init to NULL).
 *   void *args    : For USER FUNCTIONS: default arguments (NULL terminated).
 *                   For VARIABLES: (esp. loop indexes): push_val history.
 *                   (while processing a loop, ep->value may not be a bloc)
 * menu:
 * -----
 *  1: Standard monadic or dyadic OPERATORS
 *  2: CONVERSIONS and similar elementary functions
 *  3: TRANSCENDENTAL functions
 *  4: NUMBER THEORETICAL functions
 *  5: Functions related to ELLIPTIC CURVES
 *  6: Functions related to general NUMBER FIELDS
 *  7: POLYNOMIALS and power series
 *  8: Vectors, matrices, LINEAR ALGEBRA and sets
 *  9: SUMS, products, integrals and similar functions
 *  10: GRAPHIC functions
 *  11: PROGRAMMING under GP
 *
 * code: describe function prototype. NULL = use valence instead.
 * -----
 * Arguments:
 *  I  closure whose value is ignored, like in for() loop
 *  E  closure whose value is used, like in sum() loop
 *  G  GEN
 *  L  long
 *  S  symbol (i.e GP function name) as a entree *
 *  V  lexical variable
 *  C  lexical context
 *  n  variable number
 *  &  *GEN
 *  f  Fake *long (function requires it, but we don't use the resulting long)
 *  p  real precision (prec for the C library)
 *  P  series precision (precdl for the C library)
 *  r  raw input (treated as a string without quotes).
 *     Quoted args are copied as strings. Stops at first unquoted ')' or ','.
 *     Special chars can be quoted using '\'.  Ex : aa"b\n)"c => "aab\n)c".
 *  s  expanded string. Example: Pi"x"2 yields "3.142x2".
 *     The unquoted components can be of any pari type (converted according to
 *     the current output format)
 *  s* any number of strings (see s)
 *  M  Mnemonic or a flag (converted to a long); description follows
 *	 after \n at the end of the argument description
 *  D  Has a default value. Format is "Dvalue,type," (the ending comma is
 *     mandatory). Ex: D0,L, (arg is long, 0 by default).
 *     Special syntax:
 *       if type = G, &, I or V:  D[G&IV] all send NULL.
 *       if type = n: Dn sends -1.
 *
 *     The user-given args are read first, then completed by the defaults
 *
 * Return type (first char or immediately after 'x'): GEN by default, otherwise
 *  l Return long
 *  i Return int
 *  v Return void
 *
 * Syntax requirements:
 *  = Separator '=' required.
 *
 * Origin:
 *  x Installed foreign function. Put the ep of the function as the
 *       first argument, fill the rest with PARI arguments,
 *       then call installedHandler with these arguments.
 *       Should be the first char in the code.
 *
 ****************************************************************************
 * If new codes are added, change identifier and skipidentifier.
 *
 * Currently the following functions have no code word, but a valence code.
 * 'O' 50, 'if' 80, 'until' 82, 'while' 81, 'global' 88,
 * Valences:
 * 0  for functions without mandatory args.
 * 1  for functions with mandatory args.
 * 50 'O'
 * 80 'if'
 * 82 'until'
 * 81 'while'
 * 88 'global'
 */
#include "init.h"
