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
#include "anal.h"
#ifdef _WIN32
#  ifndef WINCE
#    include <process.h>
#  endif
#endif

const int     functions_tblsz = 135; /* size of functions_hash          */
/*      Variables statiques communes :         */
FILE    *pari_outfile, *errfile, *logfile, *infile;
ulong   logstyle = logstyle_none;
GEN     *polun, *polx;
GEN     gnil, gzero, gun, gdeux, ghalf, polvar, gi;
GEN     gpi=NULL, geuler=NULL, bernzone=NULL;
GEN     primetab; /* private primetable */
byteptr diffptr;
char    *current_logfile, *current_psfile, *pari_datadir = NULL;
int     gp_colors[c_LAST];
int     disable_color = 1, added_newline = 1;

entree  **varentries;

void    *global_err_data;
long    *ordvar;
ulong   DEBUGFILES, DEBUGLEVEL, DEBUGMEM, compatible;
ulong   prec, precdl;
ulong   init_opts = INIT_JMPm | INIT_SIGm;
pari_sp bot = 0, top = 0, avma;
size_t memused;

gp_data *GP_DATA = NULL;

void *foreignHandler; 	              /* Handler for foreign commands.   */
char foreignExprSwitch = 3; 	      /* Just some unprobable char.      */
GEN  (*foreignExprHandler)(char*);    /* Handler for foreign expressions.*/
entree * (*foreignAutoload)(char*, long); /* Autoloader                      */
void (*foreignFuncFree)(entree *);    /* How to free external entree.    */

int  (*default_exception_handler)(long);
int  (*whatnow_fun)(char *, int);
pariout_t DFLT_OUTPUT = { 'g', 0, -1, 1, 0, f_RAW, 0 };

extern void  delete_dirs(gp_path *p);
extern void  initout(int initerr);
extern int   term_width(void);

#ifdef BOTH_GNUPLOT_AND_X11
/* Satisfy DLL dependencies: dummy only */
#define EXTERM_DLL_DPES *PL_markstack_ptr, PL_stack_max, *PL_Sv, *PL_stack_sp, \
  *PL_tmps_floor, *PL_tmps_ix, *PL_markstack_max, *PL_stack_base, *PL_na, \
  *PL_sv_yes, *PL_sv_no, *PL_curpad, *PL_op
extern int EXTERM_DLL_DPES;
int EXTERM_DLL_DPES;
#endif	/* defined BOTH_GNUPLOT_AND_X11 */

typedef struct {
  jmp_buf *penv;
  long flag;
} cell;

static stack *err_catch_stack = NULL;
static char **dft_handler;
static jmp_buf environnement;

void
push_stack(stack **pts, void *a)
{
  stack *v = (stack*) gpmalloc(sizeof(stack));
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
  a = s->value; free((void*)s);
  return a;
}

void
debug_stack(void)
{
  GEN z;
  fprintferr("bot=0x%lx\t top=0x%lx\n",bot,top);
  for(z=(GEN)top;z>=(GEN)avma;z--)
    fprintferr("0x%p:\t0x%lx\t%lu\n",z,*z,*z);
}

/*********************************************************************/
/*                                                                   */
/*                               BLOCS                               */
/*                                                                   */
/*********************************************************************/
static long next_bloc;
static GEN cur_bloc=NULL; /* current bloc in bloc list */

/* Return x, where:
 * x[-3]: adress of next bloc
 * x[-2]: adress of preceding bloc.
 * x[-1]: number of allocated blocs.
 * x[0..n-1]: malloc-ed memory. */
GEN
newbloc(long n)
{
  long *x = (long *) gpmalloc((n + BL_HEAD)*sizeof(long)) + BL_HEAD;

  bl_next(x) = 0; /* the NULL address */
  bl_prev(x) = (long)cur_bloc;
  bl_num(x)  = next_bloc++;
  if (n) *x = 0; /* initialize first cell to 0. See killbloc */
  if (cur_bloc) bl_next(cur_bloc) = (long)x;
  if (DEBUGMEM)
  {
    if (!n) err(warner,"mallocing NULL object in newbloc");
    if (DEBUGMEM > 2)
      fprintferr("new bloc, size %6lu (no %ld): %08lx\n", n, next_bloc-1, x);
  }
  return cur_bloc = x;
}

static void
free_bloc(GEN x)
{
  if (DEBUGMEM > 2)
    fprintferr("killing bloc (no %ld): %08lx\n", bl_num(x), x);
  free((void*)bl_base(x));
}

static void
delete_from_bloclist(GEN x)
{
  if (bl_next(x)) bl_prev(bl_next(x)) = bl_prev(x);
  else
  {
    cur_bloc = (GEN)bl_prev(x);
    next_bloc = bl_num(x);
  }
  if (bl_prev(x)) bl_next(bl_prev(x)) = bl_next(x);
  free_bloc(x);
}

/* Recursively look for clones in the container and kill them. Then kill
 * container if clone. */
void
killsubblocs(GEN x)
{
  long i, lx;
  switch(typ(x)) /* HACK: if x is not a GEN, we have typ(x)=0 */
  {
    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x);
      for (i=1;i<lx;i++) killsubblocs((GEN)x[i]);
      break;
    case t_LIST:
      lx = lgeflist(x);
      for (i=2;i<lx;i++) killsubblocs((GEN)x[i]);
      break;
  }
  if (isclone(x)) delete_from_bloclist(x);
}

/* FIXME: SIGINT should be blocked until killsubblocs() returns */
void
killbloc(GEN x) { killsubblocs(x); }
void
gunclone(GEN x) { delete_from_bloclist(x); }

/*********************************************************************/
/*                                                                   */
/*                       C STACK SIZE CONTROL                        */
/*                (avoid core dump on deep recursion)                */
/*********************************************************************/
#ifdef STACK_CHECK
/* adapted from Perl code written by Dominic Dunlop */
void *PARI_stack_limit = NULL;

#  ifdef __EMX__				/* Emulate */
extern void* get_stack(double,int);
#    define STACK_CHECK_INIT(b)		\
	((void)b, PARI_stack_limit = get_stack(1./16, 32*1024))
#  else /* !__EMX__ */
#include <sys/types.h>
#include <sys/time.h>
#include <sys/resource.h>

/* Set PARI_stack_limit to (a little above) the lowest safe address that can
 * be used on the stack. Leave PARI_stack_limit at its initial value (NULL)
 * to show no check should be made [init failed]. Assume stack grows downward.
 */
static void
pari_init_stackcheck(void *stack_base)
{
  struct rlimit rip;
  ulong size;

  if (getrlimit(RLIMIT_STACK, &rip)) return;
  size = rip.rlim_cur;
  if (size == RLIM_INFINITY || size > (ulong)stack_base)
    PARI_stack_limit = (void*)(((ulong)stack_base) / 16);
  else
    PARI_stack_limit = (void*)((ulong)stack_base - (size/16)*15);
}
#    define STACK_CHECK_INIT(b) pari_init_stackcheck(b)
#  endif /* !__EMX__ */

#else
#    define STACK_CHECK_INIT(b)		((void)b)
#endif /* STACK_CHECK */

/*********************************************************************/
/*                                                                   */
/*                       SYSTEM INITIALIZATION                       */
/*                                                                   */
/*********************************************************************/
static int var_not_changed; /* altered in reorder() */
static int try_to_recover = 0;
static GEN universal_constants;

#if __MWERKS__
static void *
macalloc(size_t size)
{
  OSErr resultCode;
  Handle newH = TempNewHandle((size),&resultCode);
  if (!newH) return NULL;
  HLock(newH); return (void*) *newH;
}
#  define __gpmalloc(size)  ((size) > 1000000)? macalloc(size): malloc((size))
#else
#  define __gpmalloc(size)  (malloc(size))
#endif

char*
gpmalloc(size_t size)
{
  if (size)
  {
    char *tmp = (char*)__gpmalloc(size);
    if (!tmp) err(memer);
    return tmp;
  }
  if (DEBUGMEM) err(warner,"mallocing NULL object");
  return NULL;
}

char*
gprealloc(void *pointer, size_t size)
{
  char *tmp;

  if (!pointer) tmp = (char *) malloc(size);
  else tmp = (char *) realloc(pointer,size);
  if (!tmp) err(memer);
  return tmp;
}

static void
pari_handle_SIGINT(void)
{
#ifdef _WIN32
  if (++win32ctrlc >= 5) _exit(3);
#else
  err(talker, "user interrupt");
#endif
}

static void
pari_sighandler(int sig)
{
  char *msg;
  (void)os_signal(sig,pari_sighandler);
  switch(sig)
  {
#ifdef SIGBREAK
    case SIGBREAK: pari_handle_SIGINT(); return;
#endif
#ifdef SIGINT
    case SIGINT:   pari_handle_SIGINT(); return;
#endif

#ifdef SIGSEGV
    case SIGSEGV:
      msg="segmentation fault: bug in PARI or calling program";
      break;
#endif

#ifdef SIGBUS
    case SIGBUS:
      msg="bus error: bug in PARI or calling program";
      break;
#endif

#ifdef SIGFPE
    case SIGFPE:
      msg="floating point exception: bug in PARI or calling program";
      break;
#endif

#ifdef SIGPIPE
    case SIGPIPE:
      msg="broken pipe";
      break;
#endif

    default:
      msg="unknown signal";
  }
  err(talker,msg);
}

#ifdef _WIN32
int win32ctrlc = 0;

void
dowin32ctrlc()
{
   win32ctrlc = 0;
   err(talker,"user interrupt");
}
#endif

/* Initialize hashtable */
static void
init_hashtable(entree **table, int tblsz)
{
  entree *ep, *ep1, *last;
  long i, v;

  for (i = 0; i < tblsz; i++)
  {
    last = NULL; ep = table[i]; table[i] = NULL;
    for ( ; ep; ep = ep1)
    {
      ep1 = ep->next; v = EpVALENCE(ep);
      if (v == EpVAR || v == EpINSTALL) /* keep this one */
      {
        if (last)
          last->next = ep;
        else
          table[i] = ep;
        last = ep; last->next = NULL;
      }
      else freeep(ep);
    }
  }
}

static void
fill_hashtable(entree **table, entree *ep, char **helpmessage)
{
  long n;

  for ( ; ep->name; ep++)
  {
    EpSETSTATIC(ep);
    ep->help = helpmessage? *helpmessage++: NULL;
    n = hashvalue(ep->name);
    ep->next = table[n]; table[n] = ep;
    ep->args = NULL;
  }
}

void
init_defaults(int force)
{
  static int done=0;

  if (done && !force) return;
  done = 1;

#ifdef LONG_IS_64BIT
  prec=4;
#else
  prec=5;
#endif

  precdl = 16;
  compatible = NONE;
  DEBUGFILES = DEBUGLEVEL = DEBUGMEM = 0;

  current_psfile = pari_strdup("pari.ps");
  current_logfile= pari_strdup("pari.log");
  logfile = NULL;
  initout(1); next_bloc=0;
}

/* does elt belong to list, after position start (excluded) ? */
static int
list_isin(void **list, void *elt, int start)
{
  long indelt=0;

  if (list)
  {
    while (*list)
    {
      if (indelt>start && *list==elt) return indelt;
      list++; indelt++;
    }
  }
  return -1;
}

static void
list_prepend(void ***listptr, void *elt)
{
  void **list=*listptr;
  long nbelt=0;

  if (list)
    while (list[nbelt]) nbelt++;
  list = (void **) gpmalloc(sizeof(void *)*(nbelt+2));
  list[0]=elt;
  if (nbelt)
  {
    memcpy(list+1,*listptr,nbelt*sizeof(void *));
    free(*listptr);
  }
  list[nbelt+1]=NULL; *listptr=list;
}

/* Load modlist in hashtable hash. If force == 0, do not load twice the
 * same list in the same hashtable, which would only destroy user variables.
 * As it stands keep a complete history (instead of most recent changes).
 */
int
gp_init_entrees(module *modlist, entree **hash, int force)
{
  static void **oldmodlist=NULL, **oldhash=NULL;

  if (!force)
  {
    const long indhash = list_isin(oldhash,(void *)hash,-1);
    if (indhash != -1 && oldmodlist[indhash]==modlist) return 0;
  }
  /* record the new pair (hash,modlist) */
  list_prepend(&oldmodlist,(void *)modlist);
  list_prepend(&oldhash,(void *)hash);

  init_hashtable(hash,functions_tblsz);
  while (modlist && modlist->func)
  {
    fill_hashtable(hash, modlist->func, modlist->help);
    modlist++;
  }
  return (hash == functions_hash);
}

module *pari_modules    = NULL;
module *pari_oldmodules = NULL;
module *pari_membermodules = NULL;
entree **functions_hash = NULL;
entree **funct_old_hash = NULL;
entree **members_hash   = NULL;

/* add to modlist the functions in func, with helpmsg help */
void
pari_addfunctions(module **modlist_p, entree *func, char **help)
{
  module *modlist = *modlist_p;
  int nbmodules = 0;

  while (modlist && modlist->func) { nbmodules++; modlist++; }
  modlist = *modlist_p;
  *modlist_p = (module*) gpmalloc(sizeof(module)*(nbmodules+2));
  if (nbmodules)
  {
    memcpy(1+ *modlist_p, modlist, sizeof(module)*nbmodules);
    free(modlist);
  }
  modlist = *modlist_p;
  modlist->func = func;
  modlist->help = help;

  modlist += nbmodules+1;
  modlist->func = NULL;
  modlist->help = NULL;
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
reset_traps()
{
  long i;
  if (DEBUGLEVEL) err(warner,"Resetting all traps");
  for (i=0; i <= noer; i++) dft_handler[i] = NULL;
}

static void
init_universal_constants(void)
{
  /* 2 (gnil) + 2 (gzero) + 3 (gun) + 3 (gdeux) + 3 (half) + 3 (gi) */
  GEN p = universal_constants = (long*) gpmalloc(16*sizeof(long));
  gzero = p; p+=2; gnil = p; p+=2;
  gzero[0] = gnil[0] = evaltyp(t_INT) | evallg(2);
  gzero[1] = gnil[1] = evallgefint(2);

  gun = p; p+=3; gdeux = p; p+=3;
  gun[0] = gdeux[0] = evaltyp(t_INT) | evallg(3);
  gun[1] = gdeux[1] = evalsigne(1) | evallgefint(3);
  gun[2] = 1; gdeux[2]= 2;

  ghalf = p; p+=3; gi = p; p+=3;
  ghalf[0] = evaltyp(t_FRAC) | evallg(3);
  ghalf[1] = un;
  ghalf[2] = deux;
  gi[0] = evaltyp(t_COMPLEX) | evallg(3);
  gi[1] = zero;
  gi[2] = un;
}

static size_t
fix_size(size_t a)
{
  size_t b = a - (a & (BYTES_IN_LONG-1)); /* sizeof(long) | b <= a */
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
    free((void*)bot);
  }
  /* NOT gpmalloc, memer would be deadly */
  bot = (pari_sp)__gpmalloc(s);
  if (!bot)
    for (s = old;; s>>=1)
    {
      if (!s) err(memer); /* no way out. Die */
      err(warner,"not enough memory, new stack %lu",s);
      bot = (pari_sp)__gpmalloc(s);
      if (bot) break;
    }
  avma = top = bot+s;
  memused = 0; return s;
}

extern int pari_kernel_init(void);

/* initialize PARI data. You can call pari_addfunctions() first to add other
 * routines to the default set */
void
pari_init(size_t parisize, ulong maxprime)
{
  ulong u;
  long i;

  STACK_CHECK_INIT(&i);
  init_defaults(0);
  if (INIT_JMP && setjmp(environnement))
  {
    fprintferr("  ***   Error in the PARI system. End of program.\n");
    exit(1);
  }
  if (INIT_SIG) pari_sig_init(pari_sighandler);
  (void)init_stack(parisize);
  diffptr = initprimes(maxprime);
  init_universal_constants();
  if (pari_kernel_init()) err(talker,"Cannot initialize kernel");

  varentries = (entree**) gpmalloc((MAXVARN+1)*sizeof(entree*));
  polvar = (GEN) gpmalloc((MAXVARN+1)*sizeof(long));
  ordvar = (GEN) gpmalloc((MAXVARN+1)*sizeof(long));
  polx  = (GEN*) gpmalloc((MAXVARN+1)*sizeof(GEN));
  polun = (GEN*) gpmalloc((MAXVARN+1)*sizeof(GEN));
  polvar[0] = evaltyp(t_VEC) | evallg(1);
  for (u=0; u <= MAXVARN; u++) { ordvar[u] = u; varentries[u] = NULL; }

  (void)fetch_var(); /* create polx/polun[MAXVARN] */
  primetab = (GEN) gpmalloc(1 * sizeof(long));
  primetab[0] = evaltyp(t_VEC) | evallg(1);

  pari_addfunctions(&pari_modules, functions_basic,helpmessages_basic);
  functions_hash = (entree **) gpmalloc(sizeof(entree*)*functions_tblsz);
  for (i = 0; i < functions_tblsz; i++) functions_hash[i] = NULL;

  pari_addfunctions(&pari_oldmodules, oldfonctions,oldhelpmessage);
  funct_old_hash = (entree **) gpmalloc(sizeof(entree*)*functions_tblsz);
  for (i = 0; i < functions_tblsz; i++) funct_old_hash[i] = NULL;
  gp_init_entrees(pari_oldmodules, funct_old_hash, 1);

  if (new_fun_set)
    gp_init_entrees(pari_modules, functions_hash, 1);
  else
    gp_init_entrees(pari_oldmodules, functions_hash, 1);

  pari_addfunctions(&pari_membermodules, gp_member_list, NULL);
  members_hash = (entree **) gpmalloc(sizeof(entree*)*functions_tblsz);
  for (i = 0; i < functions_tblsz; i++) members_hash[i] = NULL;
  gp_init_entrees(pari_membermodules, members_hash, 1);

  whatnow_fun = NULL;
  dft_handler = (char **) gpmalloc((noer + 1) *sizeof(char *));
  reset_traps();
  default_exception_handler = NULL;

  (void)manage_var(manage_var_init,NULL); /* init nvar */
  var_not_changed = 1; (void)fetch_named_var("x", 0);
  try_to_recover=1;
  if (!pari_datadir) /* GP may set it */
  {
    pari_datadir = os_getenv("GP_DATA_DIR");
    if (!pari_datadir) pari_datadir = GPDATADIR;
  }
}

static void
delete_hist(gp_hist *h)
{
  if (h->res) free((void*)h->res);
}
static void
delete_pp(gp_pp *p)
{
  if (p->cmd) free((void*)p->cmd);
}
static void
delete_path(gp_path *p)
{
  delete_dirs(p);
  free((void*)p->PATH);
}

static void
free_gp_data(gp_data *D)
{
  if (!D) return;
  delete_hist(D->hist);
  delete_path(D->path);
  delete_pp(D->pp);
  if (D->help) free((void*)D->help);
}

void
freeall(void)
{
  long i;
  entree *ep,*ep1;

  while (delete_var()) /* empty */;
  for (i = 0; i < functions_tblsz; i++)
  {
    for (ep = functions_hash[i]; ep; ep = ep1) { ep1 = ep->next; freeep(ep); }
    for (ep =   members_hash[i]; ep; ep = ep1) { ep1 = ep->next; freeep(ep); }
  }
  free((void*)varentries);
  free((void*)ordvar);
  free((void*)polvar);
  free((void*)polx[MAXVARN]);
  free((void*)polx);
  free((void*)polun);
  free((void*)primetab);
  free((void*)universal_constants);

  while (cur_bloc) delete_from_bloclist(cur_bloc);
  killallfiles(1);
  free((void *)functions_hash);
  free((void *)bot);
  free((void *)diffptr);
  free(current_logfile);
  free(current_psfile);

  free_gp_data(GP_DATA);
}

GEN
getheap(void)
{
  long m=0,l=0;
  GEN x;

  for (x = cur_bloc; x; x = (GEN)bl_prev(x))
  {
    m++; l+=4;
    if (! x[0]) /* user function */
      l += (strlen((char *)(x+2))) / sizeof(long);
    else if (x==bernzone)
      l += x[0];
    else /* GEN */
      l += taille(x);
  }
  x=cgetg(3,t_VEC); x[1]=lstoi(m); x[2]=lstoi(l);
  return x;
}

/********************************************************************/
/**                                                                **/
/**                       VARIABLE ORDERING                        **/
/**                                                                **/
/********************************************************************/

/* Substitution globale des composantes du vecteur y aux variables de x */
GEN
changevar(GEN x, GEN y)
{
  long tx, ty, lx, vx, vy, i;
  pari_sp av, tetpil;
  GEN  p1,p2,z;

  if (var_not_changed && y==polvar) return x;
  tx=typ(x); if (!is_recursive_t(tx)) return gcopy(x);
  ty=typ(y); if (! is_vec_t(ty)) err(changer1);
  if (is_scalar_t(tx))
  {
    if (tx!=t_POLMOD) return gcopy(x);
    av=avma;
    p1=changevar((GEN)x[1],y);
    p2=changevar((GEN)x[2],y); tetpil=avma;
    return gerepile(av,tetpil, gmodulcp(p2,p1));
  }
  if (is_rfrac_t(tx))
  {
    av=avma;
    p1=changevar((GEN)x[1],y);
    p2=changevar((GEN)x[2],y); tetpil=avma;
    return gerepile(av,tetpil, gdiv(p1,p2));
  }

  lx = (tx==t_POL)? lgef(x): lg(x);
  if (tx == t_POL || tx == t_SER)
  {
    vx=varn(x)+1; if (vx>=lg(y)) return gcopy(x);
    p1=(GEN)y[vx];
    if (!signe(x))
    {
      vy=gvar(p1); if (vy > (long)MAXVARN) err(changer1);
      z=gcopy(x); setvarn(z,vy); return z;
    }
    av=avma; p2=changevar((GEN)x[lx-1],y);
    for (i=lx-2; i>=2; i--)
    {
      p2 = gmul(p2,p1);
      p2 = gadd(p2, changevar((GEN)x[i],y));
    }
    if (tx==t_SER)
    {
      p2 = gadd(p2, ggrando(p1,lx-2));
      if (valp(x))
        p2 = gmul(gpuigs(p1,valp(x)), p2);
    }
    return gerepileupto(av,p2);
  }
  z=cgetg(lx,tx);
  for (i=1; i<lx; i++) z[i]=lchangevar((GEN)x[i],y);
  return z;
}

GEN
reorder(GEN x)
{
  long tx,lx,i,n, nvar = manage_var(manage_var_next,NULL);
  int *var,*varsort,*t1;

  if (!x) return polvar;
  tx=typ(x); lx=lg(x)-1;
  if (! is_vec_t(tx)) err(typeer,"reorder");
  if (! lx) return polvar;

  varsort = (int *) gpmalloc(lx*sizeof(int));
  var = (int *) gpmalloc(lx*sizeof(int));
  t1 = (int *) gpmalloc(nvar*sizeof(int));

  for (n=0; n<nvar; n++) t1[n] = 0;
  for (n=0; n<lx; n++)
  {
    var[n] = i = gvar((GEN)x[n+1]);
    varsort[n] = ordvar[var[n]]; /* position in polvar */
    if (i >= nvar) err(talker,"variable out of range in reorder");
    /* check if x is a permutation */
    if (t1[i]) err(talker,"duplicated indeterminates in reorder");
    t1[i] = 1;
  }
  qsort(varsort,lx,sizeof(int),(QSCOMP)pari_compare_int);

  for (n=0; n<lx; n++)
  {
    /* variables are numbered 0,1 etc... while polvar starts at 1. */
    polvar[varsort[n]+1] = lpolx[var[n]];
    ordvar[var[n]] = varsort[n];
  }

  var_not_changed=1;
  for (i=0; i<nvar; i++)
    if (ordvar[i]!=i) { var_not_changed=0; break; }

  free(t1); free(var); free(varsort);
  return polvar;
}

/*******************************************************************/
/*                                                                 */
/*                         ERROR RECOVERY                          */
/*                                                                 */
/*******************************************************************/
extern int pop_val_if_newer(entree *ep, long loc);
extern void kill_from_hashlist(entree *ep);

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
        case EpNEW:
          kill_from_hashlist(ep);
          break;
        case EpUSER:
        case EpALIAS:
        case EpMEMBER:
          if (bl_num(ep->value) >= listloc)
          {
            gunclone((GEN)ep->value);
            ep->value = (void*)initial_value(ep);
            kill_from_hashlist(ep);
          }
      }
    }
#if 0
 /* This causes SEGV on lists and GP-2.0 vectors: internal component is
  * destroyed while global object is not updated. Two solutions:
  *  - comment it out: should not be a big memory problem except for huge
  *  vec. components. Has the added advantadge that the results computed so
  *  far are not lost.
  *
  *  - tag every variable whose component has been modified in the last
  *  cycle. Untag it at the begining of each cycle. Maybe this should be
  *  done. But do we really want to destroy a huge global vector if one of
  *  its components was modified before the error ? (we don't copy the whole
  *  thing anymore). K.B.
  */
  {
    GEN y;
    for (x = cur_bloc; x && bl_num(x) >= listloc; x = y)
    {
      y = (GEN)bl_prev(x);
      if (x != gpi && x != geuler && x != bernzone) killbloc(x);
    }
  }
#endif
  try_to_recover=1;
  (void)os_signal(SIGINT, sigfun);
}

void
disable_dbg(long val)
{
  static long oldval = -1;
  if (val < 0)
  {
    if (oldval >= 0) { DEBUGLEVEL = oldval; oldval = -1; }
  }
  else if (DEBUGLEVEL)
    { oldval = DEBUGLEVEL; DEBUGLEVEL = val; }
}

#define MAX_PAST 25
#define STR_LEN 20
/* Outputs a beautiful error message (not \n terminated)
 *   msg is errmessage to print.
 *   s points to the offending chars.
 *   entry tells how much we can go back from s[0].
 */
void
errcontext(char *msg, char *s, char *entry)
{
  int past = (s-entry);
  char str[STR_LEN + 2];
  char *buf, *t, *pre;

  if (!s || !entry) { print_prefixed_text(msg,"  ***   ",NULL); return; }

  t = buf = gpmalloc(strlen(msg) + MAX_PAST + 5 + 2 * 16);
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
  pre = gpmalloc(2 * 16 + 1);
  strcpy(pre, term_get_color(c_ERR));
  strcat(pre, "  ***   ");
  print_prefixed_text(buf, pre, str);
  free(buf); free(pre);
}

void *
err_catch(long errnum, jmp_buf *penv)
{
  cell *v;
  /* for fear of infinite recursion... */
  if (errnum == memer) err(talker, "can't trap memory errors");
  if (errnum == CATCH_ALL) errnum = noer;
  if (errnum > noer) err(talker, "no such error number: %ld", errnum);
  v = (cell*)gpmalloc(sizeof(cell));
  v->penv  = penv;
  v->flag = errnum;
  push_stack(&err_catch_stack, (void*)v);
  return (void*)v;
}

static void
pop_catch_cell(stack **s)
{
  cell *c = (cell*)pop_stack(s);
  if (c)
  {
    free(c);
  }
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
void
err_clean(void)
{
  while (err_catch_stack)
    pop_catch_cell(&err_catch_stack);
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
  disable_dbg(-1);
  killallfiles(0);
  err_clean();

  if (pariErr->die) pariErr->die();    /* Caller wants to catch exceptions? */
  global_err_data = NULL;
  fprintferr("\n"); flusherr();

  /* reclaim memory stored in "blocs" */
  if (try_to_recover) recover(1);
  longjmp(GP_DATA? GP_DATA->env: environnement, numerr);
}

void
err(long numerr, ...)
{
  char s[128], *ch1;
  int ret = 0;
  PariOUT *out = pariOut;
  va_list ap;

  va_start(ap,numerr);

  global_err_data = NULL;
  if (err_catch_stack && !is_warn(numerr))
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

  if (!added_newline) { pariputc('\n'); added_newline=1; }
  pariflush(); pariOut = pariErr;
  pariflush(); term_color(c_ERR);

  if (numerr <= cant_deflate)
  {
    pariputsf("  ***   Bug in PARI, please report.  Uncatched error: %s",
	      errmessage[numerr]);
  }
  else if (numerr < talker)
  {
    strcpy(s, errmessage[numerr]);
    switch (numerr)
    {
      case obsoler:
        ch1 = va_arg(ap,char *);
        errcontext(s,ch1,va_arg(ap,char *));
        if (whatnow_fun)
        {
          term_color(c_NONE);
          print_text("\nFor full compatibility with GP 1.39, type \"default(compatible,3)\" (you can also set \"compatible = 3\" in your GPRC file)");
          pariputc('\n');
          ch1 = va_arg(ap,char *);
          (void)whatnow_fun(ch1, - va_arg(ap,int));
        }
        break;

      case openfiler:
        sprintf(s+strlen(s), "%s file", va_arg(ap,char*));
        ch1 = va_arg(ap,char *);
        errcontext(s,ch1,ch1); break;

      case talker2:
      case member:
        strcat(s,va_arg(ap, char*)); /* fall through */
      default:
        ch1 = va_arg(ap,char *);
        errcontext(s,ch1,va_arg(ap,char *));
    }
  }
  else if (numerr == user)
  {
    GEN g = va_arg(ap, GEN);
    pariputsf("  ###   user error: ");
    print0(g, f_RAW);
  }
  else
  {
    pariputsf("  ***   %s", errmessage[numerr]);
    switch (numerr)
    {
      case talker: case siginter: case invmoder:
        ch1=va_arg(ap, char*);
        vpariputs(ch1,ap); pariputc('.'); break;

      case impl:
        ch1=va_arg(ap, char*);
        pariputsf(" %s is not yet implemented.",ch1); break;

      case breaker: case typeer: case mattype1: case overwriter:
      case accurer: case infprecer: case negexper: case polrationer:
      case funder2: case constpoler: case notpoler: case redpoler:
      case zeropoler: case consister: case flagerr: case precer:
        pariputsf(" in %s.",va_arg(ap, char*)); break;

      case bugparier:
        pariputsf(" %s, please report",va_arg(ap, char*)); break;

      case operi: case operf:
      {
        char *f, *op = va_arg(ap, char*);
        GEN x = va_arg(ap, GEN);
        GEN y = va_arg(ap, GEN);
             if (*op == '+') f = "addition";
        else if (*op == '*') f = "multiplication";
        else if (*op == '/' || *op == '%' || *op == '\\') f = "division";
        else if (*op == 'g') { op = ","; f = "gcd"; }
        else { op = "-->"; f = "assignment"; }
        pariputsf(" %s %s %s %s.",f,type_name(typ(x)),op,type_name(typ(y)));
        break;
      }

      case primer2:
        pariputsf("%lu.", va_arg(ap, ulong));
        break;

      /* the following 4 are only warnings (they return) */
      case warnmem: case warner:
        pariputc(' '); ch1=va_arg(ap, char*);
        vpariputs(ch1,ap); pariputs(".\n");
        ret = 1; break;

      case warnprec:
        vpariputs(" in %s; new prec = %ld\n",ap);
        ret = 1; break;

      case warnfile:
        ch1=va_arg(ap, char*);
        pariputsf(" %s: %s", ch1, va_arg(ap, char*));
        ret = 1; break;
    }
  }
  term_color(c_NONE); va_end(ap);
  if (numerr==errpile)
  {
    fprintferr("\n  current stack size: %lu (%.3f Mbytes)\n",
      top-bot, (top-bot)/1048576.);
    fprintferr("  [hint] you can increase GP stack with allocatemem()\n");
  }
  pariOut = out;
  if (ret) { flusherr(); return; }
  if (default_exception_handler)
  {
    if (dft_handler[numerr])
      global_err_data = dft_handler[numerr];
    else
      global_err_data = dft_handler[noer];
    if (default_exception_handler(numerr)) { flusherr(); return; }
  }
  err_recover(numerr);
}

static char *BREAK_LOOP = "";

static void
kill_dft_handler(int numerr)
{
  char *s = dft_handler[numerr];
  if (s && s != BREAK_LOOP) free(s);
  dft_handler[numerr] = NULL;
}

/* Try f (trapping error e), recover using r (break_loop, if NULL) */
GEN
trap0(char *e, char *r, char *f)
{
  long numerr = CATCH_ALL;
  char *F;
       if (!strcmp(e,"errpile")) numerr = errpile;
  else if (!strcmp(e,"typeer")) numerr = typeer;
  else if (!strcmp(e,"gdiver")) numerr = gdiver;
  else if (!strcmp(e,"invmoder")) numerr = invmoder;
  else if (!strcmp(e,"accurer")) numerr = accurer;
  else if (!strcmp(e,"archer")) numerr = archer;
  else if (!strcmp(e,"talker")) numerr = talker;
  else if (!strcmp(e,"siginter")) numerr = siginter;
  else if (*e) err(impl,"this trap keyword");
  /* TO BE CONTINUED */

  if (f && r)
  { /* explicit recovery text */
    char *a = get_analyseur();
    pari_sp av = avma;
    VOLATILE GEN x;

    CATCH(numerr) { x = NULL; }
    TRY { x = lisseq(f); } ENDCATCH;
    if (!x) { avma = av; x = lisseq(r); }
    set_analyseur(a); return x;
  }

  F = f? f: r; /* define a default handler */
 /* will execute F (break loop if F = NULL), then jump to environnement */
  if (numerr == CATCH_ALL) numerr = noer;
  kill_dft_handler(numerr);
  if (!F)
    dft_handler[numerr] = BREAK_LOOP;
  else if (*F && (*F != '"' || F[1] != '"'))
  {
    F = pari_strdup(F);
    dft_handler[numerr] = F;
  }
  return gnil;
}

/*******************************************************************/
/*                                                                 */
/*                       CLONING & COPY                            */
/*                  Replicate an existing GEN                      */
/*                                                                 */
/*******************************************************************/
/* lontyp = 0 means non recursive type
 * otherwise:
 *   lontyp = number of codewords
 *   if not in stack, we don't copy the words in [lontyp,lontyp2[
 */
const  long  lontyp[] = { 0,0,0,1,1,1,1,2,1,1, 2,2,0,1,1,1,1,1,1,1, 2,0,0 };
static long lontyp2[] = { 0,0,0,2,1,1,1,3,2,2, 2,2,0,1,1,1,1,1,1,1, 2,0,0 };

/* can't do a memcpy there: avma and x may overlap. memmove is slower */
GEN
gcopy(GEN x)
{
  long tx=typ(x),lx,i;
  GEN y;

  if (tx == t_SMALL) return x;
  if (! is_recursive_t(tx))
  {
    if (tx == t_INT && !signe(x)) return gzero; /* very common case */
    lx = lg(x); y = new_chunk(lx);
    for (i=lx-1; i>=0; i--) y[i]=x[i];
  }
  else
  {
    lx = lg(x); y = new_chunk(lx);
    if (tx==t_POL) lx = lgef(x); else if (tx==t_LIST) lx = lgeflist(x);
    for (i=0; i<lontyp[tx];  i++) y[i]=x[i];
    for (   ; i<lontyp2[tx]; i++) copyifstack(x[i],y[i]);
    for (   ; i<lx;          i++) y[i]=lcopy((GEN)x[i]);
  }
  unsetisclone(y); return y;
}

GEN
gcopy_i(GEN x, long lx)
{
  long tx=typ(x),i;
  GEN y;

  if (tx == t_SMALL) return x;
  y=cgetg(lx,tx);
  if (! is_recursive_t(tx))
    for (i=lx-1; i>0; i--) y[i]=x[i];
  else
  {
    for (i=1; i<lontyp[tx];  i++) y[i]=x[i];
    for (   ; i<lontyp2[tx]; i++) copyifstack(x[i],y[i]);
    for (   ; i<lx;          i++) y[i]=lcopy((GEN)x[i]);
  }
  unsetisclone(y); return y;
}

GEN
forcecopy(GEN x)
{
  long tx=typ(x),lx,i;
  GEN y;

  if (tx == t_SMALL) return x;
  if (! is_recursive_t(tx))
  {
    if (tx == t_INT && !signe(x)) return gzero; /* very common case */
    lx = lg(x); y = new_chunk(lx);
    for (i=lx-1; i>=0; i--) y[i]=x[i];
  }
  else
  {
    lx = lg(x); y = new_chunk(lx);
    if (tx==t_POL) lx = lgef(x); else if (tx==t_LIST) lx = lgeflist(x);
    for (i=0; i<lontyp[tx]; i++) y[i]=x[i];
    for (   ; i<lx;         i++) y[i]=(long)forcecopy((GEN)x[i]);
  }
  unsetisclone(y); return y;
}

/* Replace heap components in INTMOD / POLMOD by stack copies, in place.
 * Useful after x = gneg(y), y a clone. stackify(x) less wasteful than
 * x = gerepileupto(av, forcecopy(x))   [ 1 partial copy instead of 2 full
 * ones ] */
GEN
stackify(GEN x)
{
  long tx=typ(x),lx,i;

  if (tx == t_SMALL) return x;
  if (isclone(x)) return forcecopy(x);
  if (is_recursive_t(tx))
  {
    if (tx == t_POLMOD || tx == t_INTMOD)
    {
      if (!isonstack(x[1])) x[1] = (long)forcecopy((GEN)x[1]);
      x[2] = (long)stackify((GEN)x[2]);
    }
    else
    {
      if (tx==t_POL) lx = lgef(x);
      else if (tx==t_LIST) lx = lgeflist(x);
      else lx = lg(x);
      for (i=lontyp[tx]; i<lx; i++) x[i] = (long)stackify((GEN)x[i]);
    }
  }
  return x;
}

GEN
dummycopy(GEN x)
{
  long tx=typ(x), lx=lg(x),i;
  GEN y=new_chunk(lx);

  switch(tx)
  {
    case t_POLMOD:
      y[1]=x[1]; y[2]=(long)dummycopy((GEN)x[2]);
      break;
    case t_MAT:
      for (i=lx-1;i;i--) y[i]=(long)dummycopy((GEN)x[i]);
      break;
    default:
      for (i=lx-1;i;i--) y[i]=x[i];
  }
  y[0]=x[0]; return y;
}

/* copy x as if avma = *AVMA, update *AVMA */
GEN
gcopy_av(GEN x, GEN *AVMA)
{
  long i,lx,tx=typ(x);
  GEN y;

  if (! is_recursive_t(tx))
  {
    if (tx == t_SMALL) return x;
    if (tx == t_INT)
    {
      lx = lgefint(x);
      *AVMA = y = *AVMA - lx;
      y[0] = evaltyp(t_INT)|evallg(lx);
      for (i=1; i<lx; i++) y[i] = x[i];
      return y;
    }
    lx = lg(x);
    *AVMA = y = *AVMA - lx;
    for (i=0; i<lx; i++) y[i] = x[i];
  }
  else
  {
    lx = lg(x); *AVMA = y = *AVMA - lx;
    if (tx==t_POL) lx = lgef(x); else if (tx==t_LIST) lx = lgeflist(x);
    for (i=0; i<lontyp[tx]; i++) y[i] = x[i];
    for (   ; i<lx; i++)         y[i] = (long)gcopy_av((GEN)x[i], AVMA);
  }
  unsetisclone(y); return y;
}

/* [copy_bin/bin_copy:] same but use NULL to code an exact 0 */
static GEN
gcopy_av0(GEN x, GEN *AVMA)
{
  long i,lx,tx=typ(x);
  GEN y;

  if (! is_recursive_t(tx))
  {
    if (tx == t_SMALL) return x;
    if (tx == t_INT)
    {
      if (!signe(x)) return NULL; /* special marker */
      lx = lgefint(x);
      *AVMA = y = *AVMA - lx;
      y[0] = evaltyp(t_INT)|evallg(lx); /* kills isclone */
      for (i=1; i<lx; i++) y[i] = x[i];
      return y;
    }
    lx = lg(x);
    *AVMA = y = *AVMA - lx;
    for (i=0; i<lx; i++) y[i] = x[i];
  }
  else
  {
    lx = lg(x); *AVMA = y = *AVMA - lx;
    if (tx==t_POL) lx = lgef(x); else if (tx==t_LIST) lx = lgeflist(x);
    for (i=0; i<lontyp[tx]; i++) y[i] = x[i];
    for (   ; i<lx; i++)         y[i] = (long)gcopy_av0((GEN)x[i], AVMA);
  }
  unsetisclone(y); return y;
}

/* [copy_bin_canon/bin_copy_canon:] same as gcopy_av0, but copy integers in
 * canonical (native kernel) form */
static GEN
gcopy_av0_canon(GEN x, GEN *AVMA)
{
  long i,lx,tx=typ(x);
  GEN y;

  if (! is_recursive_t(tx))
  {
    if (tx == t_SMALL) return x;
    if (tx == t_INT)
    {
      if (!signe(x)) return NULL; /* special marker */
      lx = lgefint(x);
      *AVMA = y = *AVMA - lx;
      y[0] = evaltyp(t_INT)|evallg(lx); /* kills isclone */
      y[1] = x[1]; x = int_MSW(x);
      for (i=2; i<lx; i++, x = int_precW(x)) y[i] = *x;
      return y;
    }
    lx = lg(x);
    *AVMA = y = *AVMA - lx;
    for (i=0; i<lx; i++) y[i] = x[i];
  }
  else
  {
    lx = lg(x); *AVMA = y = *AVMA - lx;
    if (tx==t_POL) lx = lgef(x); else if (tx==t_LIST) lx = lgeflist(x);
    for (i=0; i<lontyp[tx]; i++) y[i] = x[i];
    for (   ; i<lx; i++)         y[i] = (long)gcopy_av0_canon((GEN)x[i], AVMA);
  }
  unsetisclone(y); return y;
}

/* [copy_bin/bin_copy:] size (number of words) required for gcopy_av0(x) */
static long
taille0(GEN x)
{
  long i,n,lx, tx = typ(x);
  if (!is_recursive_t(tx))
  {
    if (tx == t_INT) return signe(x)? lgefint(x): 0;
    n = lg(x);
  }
  else
  {
    n = lg(x);
    if (tx==t_POL) lx = lgef(x);
    else if (tx==t_LIST) lx = lgeflist(x);
    else lx = n;
    for (i=lontyp[tx]; i<lx; i++) n += taille0((GEN)x[i]);
  }
  return n;
}

long
taille(GEN x)
{
  long i,n,lx, tx = typ(x);
  if (!is_recursive_t(tx))
  {
    if (tx == t_INT) return lgefint(x);
    n = lg(x);
  }
  else
  {
    n = lg(x);
    if (tx==t_POL) lx = lgef(x);
    else if (tx==t_LIST) lx = lgeflist(x);
    else lx = n;
    for (i=lontyp[tx]; i<lx; i++) n += taille((GEN)x[i]);
  }
  return n;
}

long
taille2(GEN x) { return taille(x) * sizeof(long); }

#define LG(x, tx) tx == t_POL? lgef(x): tx == t_LIST? lgeflist(x): lg(x)

GEN
gclone(GEN x)
{
  long i,lx,tx = typ(x), t = taille(x);
  GEN y = newbloc(t);
  if (!is_recursive_t(tx))
  {
    lx = (tx==t_INT)? lgefint(x): lg(x);
    for (i=0; i<lx; i++) y[i] = x[i];
  }
  else
  {
    GEN AVMA = y + t;
    lx = LG(x, tx);
    for (i=0; i<lontyp[tx]; i++) y[i] = x[i];
    for (   ; i<lx; i++)         y[i] = (long)gcopy_av((GEN)x[i], &AVMA);
  }
  setisclone(y); return y;
}

static void
shiftaddress(GEN x, long dec)
{
  long i, lx, tx = typ(x);
  if (is_recursive_t(tx))
  {
    lx = LG(x, tx);
    for (i=lontyp[tx]; i<lx; i++) {
      if (!x[i]) x[i] = zero;
      else
      {
        x[i] += dec;
        shiftaddress((GEN)x[i], dec);
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
    if (tx == t_INT)
    {
      GEN y;
      lx = lgefint(x); if (lx <= 3) return;
      y = x + 2;
      x = int_MSW(x);  if (x == y) return;
      while (x > y)
      {
        long m=*x; *x=*y; *y=m;
        x = int_precW(x); y++;
      }
    }
  }
  else
  {
    lx = LG(x, tx);
    for (i=lontyp[tx]; i<lx; i++) {
      if (!x[i]) x[i] = zero;
      else
      {
        x[i] += dec;
        shiftaddress_canon((GEN)x[i], dec);
      }
    }
  }
}

/* return a clone of x structured as a gcopy */
GENbin*
copy_bin(GEN x)
{
  long t = taille0(x);
  GENbin *p = (GENbin*)gpmalloc(sizeof(GENbin) + t*sizeof(long));
  GEN AVMA = GENbase(p) + t;
  p->canon = 0;
  p->len = t;
  p->x   = gcopy_av0(x, &AVMA);
  p->base= AVMA; return p;
}

/* same, writing t_INT in canonical native form */
GENbin*
copy_bin_canon(GEN x)
{
  long t = taille0(x);
  GENbin *p = (GENbin*)gpmalloc(sizeof(GENbin) + t*sizeof(long));
  GEN AVMA = GENbase(p) + t;
  p->canon = 1;
  p->len = t;
  p->x   = gcopy_av0_canon(x, &AVMA);
  p->base= AVMA; return p;
}

/* p from copy_bin. Copy p->x back to stack, then destroy p */
GEN
bin_copy(GENbin *p)
{
  GEN x, y, base;
  long dx, len;

  x   = p->x; if (!x) { free(p); return gzero; }
  len = p->len;
  base= p->base; dx = x - base;
  y = (GEN)memcpy((void*)new_chunk(len), (void*)GENbase(p), len*sizeof(long));
  y += dx;
  if (p->canon)
    shiftaddress_canon(y, (y-x)*sizeof(long));
  else
    shiftaddress(y, (y-x)*sizeof(long));
  free(p); return y;
}

/*******************************************************************/
/*                                                                 */
/*                         STACK MANAGEMENT                        */
/*                                                                 */
/*******************************************************************/
/* Inhibit some area gerepile-wise: declare it to be a non recursive
 * type, of length l. Thus gerepile won't inspect the zone, just copy it.
 * For the following situation:
 *   z = cgetg(t,a); garbage of length l;
 *   for (i=1; i<HUGE; i++) z[i] = ...
 *   stackdummy(z,l); z += l; We lose l words but save a costly gerepile.
 */
void
stackdummy(GEN z, long l) { z[0] = evaltyp(t_VECSMALL) | evallg(l); }

/* gerepileupto(av, forcecopy(x)) */
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
  GENbin **l = (GENbin**)gpmalloc(n*sizeof(GENbin*));
  int i;
  for (i=0; i<n; i++) l[i] = copy_bin(*(gptr[i]));
  avma = av;
  for (i=0; i<n; i++) *(gptr[i]) = bin_copy(l[i]);
  free(l);
}

void
gerepileall(pari_sp av, int n, ...)
{
  GENbin **l = (GENbin**)gpmalloc(n*sizeof(GENbin*));
  GEN **gptr  = (GEN**)  gpmalloc(n*sizeof(GEN*));
  int i;
  va_list a; va_start(a, n);

  for (i=0; i<n; i++) { gptr[i] = va_arg(a,GEN*); l[i] = copy_bin(*(gptr[i])); }
  avma = av;
  for (--i; i>=0; i--) *(gptr[i]) = bin_copy(l[i]);
  free(l); free(gptr);
}

void
gerepilemanycoeffs(pari_sp av, GEN x, int n)
{
  int i;
  for (i=0; i<n; i++) x[i] = (long)copy_bin((GEN)x[i]);
  avma = av;
  for (i=0; i<n; i++) x[i] = (long)bin_copy((GENbin*)x[i]);
}

void
gerepilemanycoeffs2(pari_sp av, GEN x, int n, GEN y, int o)
{
  int i;
  for (i=0; i<n; i++) x[i] = (long)copy_bin((GEN)x[i]);
  for (i=0; i<o; i++) y[i] = (long)copy_bin((GEN)y[i]);
  avma = av;
  for (i=0; i<n; i++) x[i] = (long)bin_copy((GENbin*)x[i]);
  for (i=0; i<o; i++) y[i] = (long)bin_copy((GENbin*)y[i]);
}

/* Takes an array of pointers to GENs, of length n.
 * Cleans up the stack between av and tetpil, updating those GENs. */
void
gerepilemanysp(pari_sp av, pari_sp tetpil, GEN* gptr[], int n)
{
  const pari_sp av2 = avma;
  const size_t dec = av-tetpil;
  int i;

  (void)gerepile(av,tetpil,NULL);
  for (i=0; i<n; i++)
  {
    pari_sp *g1 = (pari_sp*) gptr[i];
    if (*g1 < tetpil)
    {
      if (*g1 >= av2) *g1 += dec; /* Update address if in stack */
      else if (*g1 >= av) err(gerper);
    }
  }
}

/* Takes an array of GENs (cast to longs), of length n.
 * Cleans up the stack between av and tetpil, updating those GENs. */
void
gerepilemanyvec(pari_sp av, pari_sp tetpil, long *g, int n)
{
  const pari_sp av2 = avma;
  const size_t dec = av-tetpil;
  int i;

  (void)gerepile(av,tetpil,NULL);
  for (i=0; i<n; i++,g++)
    if ((pari_sp)*g < tetpil)
    {
      if ((pari_sp)*g >= av2) *g += dec;/* Update addresses if in stack */
      else if ((pari_sp)*g >= av) err(gerper);
    }
}

GEN
gerepileupto(pari_sp av, GEN q)
{
  if (!isonstack(q)) { avma = av; return q; } /* universal object */
  /* empty garbage */
  if (av <= (pari_sp)q) return q;
  /* The garbage is only empty when av==q. It's probably a mistake if
   * av < q. But "temporary variables" from sumiter are a problem since
   * ep->values are returned as-is by identifier() and they can be in the
   * stack: if we put a gerepileupto in lisseq(), we get an error. Maybe add,
   * if (DEBUGMEM) err(warner,"av>q in gerepileupto") ???
   */

  /* Beware: (long)(q+i) --> ((long)q)+i*sizeof(long) */
  return gerepile(av, (pari_sp) (q+lg(q)), q);
}

/* internal */
GEN
gerepileuptoleaf(pari_sp av, GEN q)
{
  long i;
  GEN q0;

  if (!isonstack(q) || av==(pari_sp)q) { avma = av; return q; }
  i=lg(q); avma = (pari_sp)(((GEN)av) -  i);
  q0 = (GEN)avma; while (--i >= 0) q0[i]=q[i];
  return q0;
}
/* internal */
GEN
gerepileuptoint(pari_sp av, GEN q)
{
  if (!isonstack(q) || (GEN)av==q) { avma = av; return q; }
  avma = (pari_sp)icopy_av(q, (GEN)av);
  return (GEN)avma;
}

static int
_ok_gerepileupto(GEN av, GEN x)
{
  long i,lx,tx;
  if (!isonstack(x)) return 1;
  if (x > av)
  {
    err(warner,"bad object %Z",x);
    return 0;
  }
  tx = typ(x);
  if (! is_recursive_t(tx)) return 1;

  lx = LG(x, tx);
  for (i=lontyp[tx]; i<lx; i++)
    if (!_ok_gerepileupto(av, (GEN)x[i]))
    {
      err(warner,"bad component %ld in object %Z",i,x);
      return 0;
    }
  return 1;
}
/* check that x and all its components are out of stack, or have been
 * created after av */
int
ok_gerepileupto(GEN x) { return _ok_gerepileupto(x, x); }

GEN
gerepile(pari_sp av, pari_sp tetpil, GEN q)
{
  pari_sp avmb;
  size_t dec = av - tetpil;
  GEN ll,a,b;

  if (dec==0) return q;
  if ((long)dec<0) err(talker,"lbot>ltop in gerepile");

  if ((pari_sp)q >= avma && (pari_sp)q < tetpil)
    q = (GEN) (((pari_sp)q) + dec);

  for (ll=(GEN)av, a=(GEN)tetpil; a > (GEN)avma; ) *--ll= *--a;
  avmb = (pari_sp)ll;
  while (ll < (GEN)av)
  {
    const long tl=typ(ll);

    if (! is_recursive_t(tl)) { ll+=lg(ll); continue; }
    a = ll+lontyp[tl];
    if (tl==t_POL) { b=ll+lgef(ll); ll+=lg(ll); } else { ll+=lg(ll); b=ll; }
    for (  ; a<b; a++)
      if ((pari_sp)*a < av && (pari_sp)*a >= avma)
      {
	if ((pari_sp)*a < tetpil) *a += dec; else err(gerper);
      }
  }
  avma = avmb; return q;
}

long
allocatemoremem(size_t newsize)
{
  if (!newsize)
  {
    newsize = (top - bot) << 1;
    err(warner,"doubling stack size; new stack = %lu (%.3f Mbytes)",
                newsize, newsize/1048576.);
  }
  return init_stack(newsize);
}

/* alternate stack management routine */
stackzone *
switch_stack(stackzone *z, long n)
{
  if (!z)
  { /* create parallel stack */
    size_t size = n*sizeof(long) + sizeof(stackzone);
    z = (stackzone*) gpmalloc(size);
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
    memused = (size_t)-1;
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
checkmemory(GEN z)
{
#ifdef MEMSTEP
  if (DEBUGMEM && memused != (size_t)-1 &&
       ((GEN)memused > z + MEMSTEP || z > (GEN)memused + MEMSTEP))
  {
    memused=(size_t)z;
#if MEMSTEP >= 1048576
    fprintferr("...%4.0lf Mbytes used\n",(top-memused)/1048576.);
#else
    fprintferr("...%5.1lf Mbytes used\n",(top-memused)/1048576.);
#endif
  }
#endif
}

void
fill_stack(void)
{
  GEN x = ((GEN)bot);
  while (x < (GEN)avma) *x++ = 0xfefefefeUL;
}

/*******************************************************************/
/*                                                                 */
/*                               TIMER                             */
/*                                                                 */
/*******************************************************************/
long
_get_time(pari_timer *T, long Ticks, long TickPerSecond)
{
  long s  = Ticks / TickPerSecond;
  long us = (long) ((Ticks % TickPerSecond) * (1000000. / TickPerSecond));
  long delay = 1000 * (s - T->s) + (us - T->us) / 1000;
  T->us = us;
  T->s  = s; return delay;
}

#ifdef WINCE
long
TIMER(pari_timer *T)
{
  return _get_time(T, GetTickCount(), 1000);
}
#elif defined(macintosh)
# include <Events.h>
long
TIMER(pari_timer *T)
{
  return _get_time(T, TickCount(), 60);
}
#elif USE_TIMES

# include <sys/times.h>
# include <sys/time.h>
# include <time.h>
long
TIMER(pari_timer *T)
{
  struct tms t; times(&t);
  return _get_time(T, t.tms_utime, CLK_TCK);
}
#elif USE_GETRUSAGE

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
#elif USE_FTIME

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
timer(void)   { static pari_timer T; return TIMER(&T);}
long
timer2(void)  { static pari_timer T; return TIMER(&T);}

void
msgTIMER(pari_timer *T, char *format, ...)
{
  va_list args;
  PariOUT *out = pariOut; pariOut = pariErr;

  pariputs("Time "); va_start(args, format);
  vpariputs(format,args); va_end(args);
  pariputsf(": %ld\n", TIMER(T)); pariflush();
  pariOut = out;
}

void
msgtimer(char *format, ...)
{
  va_list args;
  PariOUT *out = pariOut; pariOut = pariErr;

  pariputs("Time "); va_start(args, format);
  vpariputs(format,args); va_end(args);
  pariputsf(": %ld\n", timer2()); pariflush();
  pariOut = out;
}

/*******************************************************************/
/*                                                                 */
/*                   FUNCTIONS KNOWN TO THE ANALYZER               */
/*                                                                 */
/*******************************************************************/
extern void alias0(char *s, char *old);
extern GEN break0(long n);
extern GEN next0(long n);
extern GEN return0(GEN x);

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
 *  I  input position (to be processed with lisseq) - a string with a
 *     sequence of PARI expressions.
 *  E  input position (to be processed with lisexpr) - a string with a
 *     PARI expression.
 *  G  GEN
 *  L  long
 *  S  symbol (i.e GP function name)
 *  V  variable (same as S, but valence must equal EpVAR/EpGVAR)
 *  n  variable number
 *  &  *GEN
 *  F  Fake *GEN (function requires a *GEN, but we don't use the resulting GEN)
 *  f  Fake *long
 *  p  real precision (prec for the C library)
 *  P  series precision (precdl dor the C library)
 *  r  raw input (treated as a string without quotes).
 *     Quoted args are copied as strings. Stops at first unquoted ')' or ','.
 *     Special chars can be quoted using '\'.  Ex : aa"b\n)"c => "aab\n)c".
 *  s  expanded string. Example: pi"x"2 yields "3.142x2".
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
