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

/*      Variables statiques communes :         */
FILE    *pari_outfile, *errfile, *logfile, *infile;
GEN     *polun, *polx;
GEN     gnil, gzero, gun, gdeux, ghalf, polvar, gi;
GEN     gpi=NULL, geuler=NULL, bernzone=NULL;
GEN     primetab; /* private primetable */
byteptr diffptr;
char    *current_logfile, *current_psfile;
int     gp_colors[c_LAST];
int     disable_color = 1, added_newline = 1;
int     under_emacs = 0, under_texmacs = 0;

int     functions_tblsz = 135; /* size of functions_hash          */
entree  **varentries;

void    *global_err_data;
jmp_buf environnement;
long    *ordvar;
long    DEBUGFILES,DEBUGLEVEL,DEBUGMEM,compatible;
long    prec,precdl;
ulong   init_opts = INIT_JMPm | INIT_SIGm;
ulong   top, bot, avma, memused;

void *foreignHandler; 	              /* Handler for foreign commands.   */
char foreignExprSwitch = 3; 	      /* Just some unprobable char.      */
GEN  (*foreignExprHandler)(char*);    /* Handler for foreign expressions.*/
entree * (*foreignAutoload)(char*, long); /* Autoloader                      */
void (*foreignFuncFree)(entree *);    /* How to free external entree.    */

int  (*default_exception_handler)(long);
GEN  (*gp_history_fun)(long, long, char *, char *);
int  (*whatnow_fun)(char *, int);
void (*output_fun)(GEN);

extern void  initout(int initerr);
extern int   term_width(void);

typedef struct cell {
  void *env;
  void *data;
  long flag;
} cell;

static stack *err_catch_stack = NULL;
static long *err_catch_array;

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

#ifdef STACK_CHECK
/*********************************************************************/
/*                                                                   */
/*                       C STACK SIZE CONTROL                        */
/*             (to avoid core dump on deep recursion)                */
/*                                                                   */
/*********************************************************************/

/* adapted from Perl code written by Dominic Dunlop */
#include <sys/resource.h>
void *PARI_stack_limit = NULL;

/* Set PARI_stack_limit to (a little above) the lowest safe address that can
 * be used on the stack. Leave PARI_stack_limit at its initial value (NULL)
 * to show no check should be made [init failed]. Assume stack grows downward.
 */
static void
pari_init_stackcheck(void *stack_base)
{
  struct rlimit rip;

  if (getrlimit(RLIMIT_STACK, &rip) || rip.rlim_cur  == RLIM_INFINITY) return;
/* DEC cc doesn't like this line:
 * PARI_stack_limit = stack_base - ((rip.rlim_cur/16)*15); */
  PARI_stack_limit = (void*)((long)stack_base - (rip.rlim_cur/16)*15);
}
#endif /* STACK_CHECK */

/*********************************************************************/
/*                                                                   */
/*                       SYSTEM INITIALIZATION                       */
/*                                                                   */
/*********************************************************************/
static int var_not_changed; /* altered in reorder() */
static int try_to_recover = 0;
static long next_bloc;
static GEN cur_bloc=NULL; /* current bloc in bloc list */
static long *universal_constants;

static void
pari_handle_SIGINT()
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
  os_signal(sig,pari_sighandler);
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

static long 
fix_size(long a)
{
  /* BYTES_IN_LONG*ceil(a/BYTES_IN_LONG) */
  ulong b = a+BYTES_IN_LONG - (((a-1) & (BYTES_IN_LONG-1)) + 1);
  if (b > VERYBIGINT) err(talker,"stack too large");
  return b;
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
reset_traps(int warn)
{
  long i;
  if (warn) err(warner,"missing cell in err_catch_stack. Resetting all traps");
  for (i=0; i <= noer; i++) err_catch_array[i] = 0;
}

/* initialise les donnees de la bibliotheque PARI. Peut être précédée d'un
 * appel à pari_addfunctions si on ajoute d'autres fonctions au pool de base.
 */
void
pari_init(long parisize, long maxprime)
{
  long i, size;
  GEN p;

#ifdef STACK_CHECK
  pari_init_stackcheck(&i);
#endif
  init_defaults(0);
  if (INIT_JMP && setjmp(environnement))
  {
    fprintferr("  ***   Error in the PARI system. End of program.\n");
    exit(1);
  }
  if (INIT_SIG) pari_sig_init(pari_sighandler);
  size = fix_size(parisize);
#if __MWERKS__
  {
    OSErr resultCode;
    Handle newHand = TempNewHandle(size,&resultCode);

    if (!newHand) err(memer);
    HLock(newHand);
    bot = (long)*newHand;
  }
#else
  bot = (long) gpmalloc(size);
#endif
  top = avma = memused = bot+size;
  diffptr = initprimes(maxprime);

  varentries = (entree**) gpmalloc((MAXVARN+1)*sizeof(entree*));
  polvar = (GEN) gpmalloc((MAXVARN+1)*sizeof(long));
  ordvar = (GEN) gpmalloc((MAXVARN+1)*sizeof(long));
  polx  = (GEN*) gpmalloc((MAXVARN+1)*sizeof(GEN));
  polun = (GEN*) gpmalloc((MAXVARN+1)*sizeof(GEN));
  polvar[0] = evaltyp(t_VEC) | evallg(1);
  for (i=0; i <= MAXVARN; i++) { ordvar[i] = i; varentries[i] = NULL; }

  /* 2 (gnil) + 2 (gzero) + 3 (gun) + 3 (gdeux) + 3 (half) + 3 (gi) */
  p = universal_constants = (long *) gpmalloc(16*sizeof(long));

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
  fetch_var(); /* create polx/polun[MAXVARN] */
  primetab = (GEN) gpmalloc((NUMPRTBELT+2)*sizeof(long));
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

  gp_history_fun = NULL;
  whatnow_fun = NULL;
  output_fun = &outbrute;
  err_catch_array = (long *) gpmalloc((noer + 1) *sizeof(long));
  reset_traps(0);
  default_exception_handler = NULL;

  (void)manage_var(2,NULL); /* init nvar */
  (void)get_timer(-1); /* init timers */
  var_not_changed = 1; fetch_named_var("x", 0);
  try_to_recover=1;
}

void
freeall(void)
{
  long i;
  entree *ep,*ep1;

  while (delete_var()) /* empty */;
  for (i = 0; i < functions_tblsz; i++)
  {
    for (ep = functions_hash[i]; ep; ep = ep1)
    {
      ep1 = ep->next; freeep(ep);
    }
    for (ep = members_hash[i]; ep; ep = ep1)
    {
      ep1 = ep->next; freeep(ep);
    }
  }
  free((void*)varentries); free((void*)ordvar); free((void*)polvar);
  free((void*)polx[MAXVARN]); free((void*)polx); free((void*)polun);
  free((void*)primetab);
  free((void*)universal_constants);

  /* set first cell to 0 to inhibit recursion in all cases */
  while (cur_bloc) { *cur_bloc=0; killbloc(cur_bloc); }
  killallfiles(1);
  free((void *)functions_hash);
  free((void *)bot); free((void *)diffptr);
  free(current_logfile);
  free(current_psfile);

  if (gp_history_fun)
    gp_history_fun(0,-1,NULL,NULL);
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

/* Return x, where:
 * x[-3]: adress of next bloc
 * x[-2]: adress of preceding bloc.
 * x[-1]: number of allocated blocs.
 * x[0..n-1]: malloc-ed memory.
 */
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
      fprintferr("new bloc, size %6ld (no %ld): %08lx\n", n, next_bloc-1, x);
  }
  return cur_bloc = x;
}

void
killbloc0(GEN x, int inspect)
{
  long tx,lx,l,i,j;
  GEN p1;

  if (!x || isonstack(x)) return;
  if (bl_next(x)) bl_prev(bl_next(x)) = bl_prev(x);
  else 
  {
    cur_bloc = (GEN)bl_prev(x);
    next_bloc = bl_num(x);
  }
  if (bl_prev(x)) bl_next(bl_prev(x)) = bl_next(x);
  if (DEBUGMEM > 2)
    fprintferr("killing bloc (no %ld): %08lx\n", bl_num(x), x);
  if (inspect)
  {
    /* FIXME: SIGINT should be blocked at this point */
    tx=typ(x); /* if x is not a GEN, we will have tx=0 */
    if (is_vec_t(tx))
    {
      lx = lg(x);
      for (i=1;i<lx;i++)
      {
        p1=(GEN)x[i];
        if (isclone(p1)) killbloc(p1);
      }
    }
    else if (tx==t_MAT)
    {
      lx = lg(x);
      if (lx>1)
      {
        l=lg(x[1]);
        if (l>1)
          for (i=1;i<lx;i++)
            for (j=1;j<l;j++)
            {
              p1=gmael(x,i,j);
              if (isclone(p1)) killbloc(p1);
            }
      }
    }
    else if (tx==t_LIST)
    {
      lx = lgef(x);
      for (i=2;i<lx;i++)
      {
        p1=(GEN)x[i];
        if (isclone(p1)) killbloc(p1);
      }
    }
    unsetisclone(x);
    /* FIXME: SIGINT should be released here */
  }
  free((void *)bl_base(x));
}
void
killbloc(GEN x) { killbloc0(x,1); }
void
gunclone(GEN x) { killbloc0(x,0); }

/********************************************************************/
/**                                                                **/
/**                       VARIABLE ORDERING                        **/
/**                                                                **/
/********************************************************************/

/* Substitution globale des composantes du vecteur y aux variables de x */
GEN
changevar(GEN x, GEN y)
{
  long tx,ty,lx,vx,vy,i,av,tetpil;
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
      vy=gvar(p1); if (vy>MAXVARN) err(changer1);
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
  long tx,lx,i,n, nvar = manage_var(3,NULL);
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
  os_signal(SIGINT, sigfun);
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
/* Outputs a beautiful error message
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
err_catch(long errnum, jmp_buf env, void *data)
{
  cell *v = (cell*)gpmalloc(sizeof(cell));
  if (errnum < 0) errnum = noer;
  v->data = data;
  v->env  = env;
  v->flag = errnum;
  err_catch_array[errnum]++;
  push_stack(&err_catch_stack, (void*)v);
  return (void*)v;
}

/* reset traps younger than V (included) */
void
err_leave(void **V)
{
  cell *t, *v = (cell*)*V;

  for (;;)
  {
    t = (cell*)pop_stack(&err_catch_stack);
    if (t == v || !t) break;
    err_catch_array[t->flag]--;
    free(t);
  }
  if (!t) reset_traps(1);
  err_catch_array[v->flag]--;
  free(v);
}

/* get last (most recent) handler for error n */
static cell *
err_seek(long n)
{
  stack *s = err_catch_stack;
  cell *t = NULL;

  for (;s; s = s->prev)
  {
    t = (cell*)s->value;
    if (!t || t->flag == n) break;
  }
  if (!t) reset_traps(1);
  return t;
}

/* kill last handler for error n */
void 
err_leave_default(long n)
{
  stack *s = err_catch_stack, *lasts = NULL;
  cell *c;

  if (n < 0) n = noer;
  if (!s || !err_catch_array[n]) return;
  for (;s; s = s->prev)
  {
    c = (cell*)s->value;
    if (c->flag == n)
    { /* kill */
      stack *v = s->prev;
      free((void*)s); s = v;
      if (lasts) lasts->prev = s;
      break;
    }
    else lasts = s;
  }
  if (!lasts)
  {
    err_catch_stack = s;
    if (!s) reset_traps(0);
  }
}

/* untrapped error: remove all traps depending from a longjmp */
void
err_clean()
{
  stack *s = err_catch_stack, *lasts = NULL;
  cell *c;

  if (!s) return;
  while (s)
  {
    c = (cell*)s->value;
    if (c->env)
    { /* kill */
      stack *v = s->prev;
      free((void*)s); s = v;
      if (lasts) lasts->prev = s;
    }
    else
    { /* preserve */
      if (lasts) lasts->prev = s; else err_catch_stack = s;
      lasts = s; s = s->prev;
    }
  }
  if (!lasts)
  {
    err_catch_stack = NULL;
    reset_traps(0);
  }
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
  get_timer(-1);
  killallfiles(0);

  if (pariErr->die) pariErr->die();    /* Caller wants to catch exceptions? */
  global_err_data = NULL;
  err_clean();
  fprintferr("\n"); flusherr();
  if (!environnement) exit(1);

  /* reclaim memory stored in "blocs" */
  if (try_to_recover) recover(1);
  longjmp(environnement, numerr);
}

void
err(long numerr, ...)
{
  char s[128], *ch1;
  int ret = 0;
  PariOUT *out = pariOut;
  va_list ap;
  cell *trapped = NULL;

  va_start(ap,numerr);

  if (err_catch_stack && !is_warn(numerr))
  {
    int trap = 0;
    if (numerr != memer)
    { /* for fear of infinite recursion don't trap memory errors */
      if (err_catch_array[numerr]) trap = numerr;
      else if (err_catch_array[noer]) trap = noer;
    }
    if (trap) trapped = err_seek(trap); else err_clean();
  }
  if (trapped)
  { /* all errors (noer), or numerr individually trapped */
    void *e = trapped->env;
    global_err_data = trapped->data;
    if (e) longjmp(e, numerr);
  }
  else
    global_err_data = NULL;

  if (!added_newline) { pariputc('\n'); added_newline=1; }
  pariflush(); pariOut = pariErr;
  pariflush(); term_color(c_ERR);

  if (numerr < talker)
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
          print_text("For full compatibility with GP 1.39, type \"default(compatible,3)\" (you can also set \"compatible = 3\" in your GPRC file)");
          pariputc('\n');
          ch1 = va_arg(ap,char *);
          whatnow_fun(ch1, - va_arg(ap,int));
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
  else
  {
    pariputsf("  ***   %s", errmessage[numerr]);
    switch (numerr)
    {
      case talker: case siginter:
        ch1=va_arg(ap, char*);
        vpariputs(ch1,ap); pariputc('.'); break;

      case impl:
        ch1=va_arg(ap, char*);
        pariputsf(" %s is not yet implemented.",ch1); break;

      case breaker: case typeer: case mattype1: case overwriter:
      case accurer: case infprecer: case negexper: case polrationer:
      case funder2: case constpoler: case notpoler: case redpoler:
      case zeropoler: case consister: case flagerr:
        pariputsf(" in %s.",va_arg(ap, char*)); break;

      case bugparier:
        pariputsf(" %s, please report",va_arg(ap, char*)); break;

      case operi: case operf:
      {
        char *f, *op = va_arg(ap, char*);
        long   x = va_arg(ap, long);
        long   y = va_arg(ap, long);
             if (*op == '+') f = "addition";
        else if (*op == '*') f = "multiplication";
        else if (*op == '/' || *op == '%') f = "division";
        else if (*op == 'g') { op = ","; f = "gcd"; }
        else { op = "-->"; f = "assignment"; }
        pariputsf(" %s %s %s %s.",f,type_name(x),op,type_name(y));
        break;
      }

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
    fprintferr("\n  current stack size: %.1f Mbytes\n", (double)(top-bot)/1E6);
    fprintferr("  [hint] you can increase GP stack with allocatemem()\n");
  }
  pariOut = out;
  if (ret || (trapped && default_exception_handler &&
              default_exception_handler(numerr))) { flusherr(); return; }
  err_recover(numerr);
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
stackdummy(GEN z, long l)
{
  z[0] = evaltyp(t_STR) | evallg(l);
}

/* Takes an array of pointers to GENs, of length n. Copies all
 * objects to contiguous locations and cleans up the stack between
 * av and avma.
 */
void
gerepilemany(long av, GEN* gptr[], long n)
{
  GEN *l = (GEN*)gpmalloc(n*sizeof(GEN));
  long i;

  /* copy objects */
  for (i=0; i<n; i++) l[i] = gclone(*(gptr[i]));
  avma = av;
  /* copy them back, kill clones */
  for (--i; i>=0; i--)
  {
    *(gptr[i]) = forcecopy(l[i]);
    gunclone(l[i]);
  }
  free(l);
}

void
gerepilemanycoeffs(long av, GEN x, long n)
{
  long i;

  /* copy objects */
  for (i=0; i<n; i++) x[i] = lclone((GEN)x[i]);
  avma = av;
  /* copy them back, kill clones */
  for (--i; i>=0; i--)
  {
    GEN p1 = (GEN)x[i];
    x[i] = (long)forcecopy(p1); gunclone(p1);
  }
}

/* Takes an array of pointers to GENs, of length n.
 * Cleans up the stack between av and tetpil, updating those GENs.
 */
void
gerepilemanysp(long av, long tetpil, GEN* gptr[], long n)
{
  const long av2 = avma, dec = av-tetpil;
  long i;

  (void)gerepile(av,tetpil,NULL);
  for (i=0; i<n; i++)
  {
    ulong *g1 = (ulong*) gptr[i];
    if (*g1 < (ulong)tetpil)
    {
      if (*g1 >= (ulong)av2) *g1 += dec; /* Update address if in stack */
      else if (*g1 >=(ulong)av) err(gerper);
    }
  }
}

/* Takes an array of GENs (casted to longs), of length n. Cleans up the
 * stack between av and tetpil, and update those GENs.
 */
void
gerepilemanyvec(long av, long tetpil, long *g, long n)
{
  const long av2 = avma, dec = av-tetpil;
  long i;

  (void)gerepile(av,tetpil,NULL);
  for (i=0; i<n; i++,g++)
    if ((ulong)*g < (ulong)tetpil)
    {
      if ((ulong)*g >= (ulong)av2) *g += dec;/* Update addresses if in stack */
      else if ((ulong)*g >= (ulong)av) err(gerper);
    }
}

GEN
gerepileupto(long av, GEN q)
{
  if (!isonstack(q)) { avma=av; return q; } /* universal object */
  /* empty garbage */
  if ((ulong)av <= (ulong)q) return q;
  /* The garbage is only empty when av==q. It's probably a mistake if
   * av < q. But "temporary variables" from sumiter are a problem since
   * ep->values are returned as-is by identifier() and they can be in the
   * stack: if we put a gerepileupto in lisseq(), we get an error. Maybe add,
   * if (DEBUGMEM) err(warner,"av>q in gerepileupto") ???
   */

  /* Beware: (long)(q+i) --> ((long)q)+i*sizeof(long) */
  return gerepile(av, (long) (q+lg(q)), q);
}

/* internal */
GEN
gerepileuptoleaf(long av, GEN q)
{
  long i;
  GEN q0;

  if (!isonstack(q) || av==(long)q) { avma=av; return q; }
  i=lg(q); avma = (long)(((GEN)av) -  i);
  q0 = (GEN)avma; while (--i >= 0) q0[i]=q[i];
  return q0;
}
/* internal */
GEN
gerepileuptoint(long av, GEN q)
{
  if (!isonstack(q) || av==(long)q) { avma=av; return q; }
  avma = (long)icopy_av(q, (GEN)av);
  return (GEN)avma;
}

/* check that x and all its components are out of stack, or have been
 * created after av */
int
ok_for_gerepileupto(long r, GEN x)
{
  long i,lx = lg(x),tx = typ(x);
  if (! is_recursive_t(tx))
    return !isonstack(x) || x <= (GEN)r;
  if (x > (GEN)r)
  {
    err(warner,"bad object %Z",x);
    return 0;
  }

  lx = lg(x);
  if (tx==t_POL || tx==t_LIST) lx = lgef(x);
  for (i=lontyp[tx]; i<lx; i++)
    if (!ok_for_gerepileupto(r, (GEN)x[i]))
    {
      err(warner,"bad component %ld in object %Z",i,x);
      return 0;
    }
  return 1;
}

GEN
gerepile(long av, long tetpil, GEN q)
{
  long avmb, dec = av - tetpil;
  GEN ll,a,b;

  if (dec==0) return q;
  if (dec<0) err(talker,"lbot>ltop in gerepile");

  if ((ulong)q>=(ulong)avma && (ulong)q<(ulong)tetpil)
    q = (GEN) (((long)q) + dec);

  for (ll=(GEN)av, a=(GEN)tetpil; a > (GEN)avma; ) *--ll= *--a;
  avmb = (long)ll;
  while (ll < (GEN)av)
  {
    const long tl=typ(ll);

    if (! is_recursive_t(tl)) { ll+=lg(ll); continue; }
    a = ll+lontyp[tl];
    if (tl==t_POL) { b=ll+lgef(ll); ll+=lg(ll); } else { ll+=lg(ll); b=ll; }
    for (  ; a<b; a++)
      if ((ulong)*a < (ulong)av && (ulong)*a >= (ulong)avma)
      {
	if ((ulong)*a < (ulong)tetpil) *a += dec; else err(gerper);
      }
  }
  avma = avmb; return q;
}

long
allocatemoremem(ulong newsize)
{
  long sizeold = top - bot, newbot;

  if (!newsize)
  {
    newsize = sizeold << 1;
    err(warner,"doubling stack size; new stack = %.1f MBytes",newsize/1E6);
  }
  else if ((long)newsize < 1000L)
    err(talker,"required stack memory too small");
  /* can't do bot = malloc directly, in case we lack memory */
  newsize = fix_size(newsize);
  newbot = (long) gpmalloc(newsize);
  free((void*)bot); bot = newbot;
  memused = avma = top = bot + newsize;
  return newsize;
}

/* alternate stack management routine */
stackzone *
switch_stack(stackzone *z, long n)
{
  if (!z)
  { /* create parallel stack */
    long size = n*sizeof(long) + sizeof(stackzone);
    z = (stackzone*) gpmalloc(size);
    z->zonetop = ((long)z) + size;
    return z;
  }

  if (n)
  { /* switch to parallel stack */
    z->bot     = bot;
    z->top     = top;
    z->avma    = avma;
    z->memused = memused;
    bot     = (long) (z+1);
    top     = z->zonetop;
    avma    = top;
    memused = (ulong)-1;
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

#if 0 /* for a specific broken machine (readline not correctly installed) */
char *xmalloc(long x) { return malloc(x); }
char *xrealloc(char *c,long x) { return realloc(c,x); }
#endif

char*
gpmalloc(size_t bytes)
{
  char *tmp;

  if (bytes)
  {
    tmp = (char *) malloc(bytes);
    if (!tmp) err(memer);
    return tmp;
  }
  if (DEBUGMEM)
    err(warner,"mallocing NULL object");
  return NULL;
}

#if __MWERKS__
static void *
macrealloc(void *p, size_t newsize, size_t oldsize)
{
  char *q = gpmalloc(newsize), *qq = q, *pp = p;
  int l = newsize > oldsize ? oldsize : newsize;

  while (l--) *qq++ = *pp++;
  free(p); return q;
}
#endif

char*
gprealloc(void *pointer, size_t newsize, size_t oldsize)
{
  char *tmp;

  if (!pointer) tmp = (char *) malloc(newsize);
#if __MWERKS__
  else tmp = (char *) macrealloc(pointer,newsize,oldsize);
#else
  else tmp = (char *) realloc(pointer,newsize);
#endif
  if (!tmp) err(memer,oldsize);
  return tmp;
}

#ifdef MEMSTEP
void
checkmemory(GEN z)
{
  if (DEBUGMEM && memused != (ulong)-1 &&
       ((GEN)memused > z + MEMSTEP || z > (GEN)memused + MEMSTEP))
  {
    memused=(ulong)z;
#if MEMSTEP >= 1048576
    fprintferr("...%4.0lf Mbytes used\n",(top-memused)/1048576.);
#else
    fprintferr("...%5.1lf Mbytes used\n",(top-memused)/1048576.);
#endif
  }
}
#endif

/*******************************************************************/
/*                                                                 */
/*                               TIMER                             */
/*                                                                 */
/*******************************************************************/
#define MAX_TIMER 32
#define MIN_TIMER 3

#ifdef WINCE
  static long
  timer_proto(int i)
  {
    static DWORD oldticks[MAX_TIMER];
    DWORD ticks = GetTickCount();
    DWORD delay = ticks - oldticks[i];
    oldticks[i] = ticks;
    return delay;
  }
#elif defined(macintosh)
# include <Events.h>
  static long
  timer_proto(int i)
  {
    static long oldticks[MAX_TIMER];
    long ticks = TickCount(), delay = ticks - oldticks[i];

    oldticks[i] = ticks;
    return 50 * delay / 3;
  }
#elif USE_TIMES

# include <sys/times.h>
# include <sys/time.h>
  static long
  timer_proto(int i)
  {
    static clock_t oldticks[MAX_TIMER];
    struct tms t;
    long delay;

    times(&t);
    delay = (long)((t.tms_utime - oldticks[i]) * (1000. / CLK_TCK));
    oldticks[i] = t.tms_utime;
    return delay;
  }
#elif USE_GETRUSAGE

# include <sys/time.h>
# include <sys/resource.h>
  static long
  timer_proto(int i)
  {
    static long oldmusec[MAX_TIMER],oldsec[MAX_TIMER];
    struct rusage r;
    struct timeval t;
    long delay;

    getrusage(0,&r); t=r.ru_utime;
    delay = 1000 * (t.tv_sec - oldsec[i]) + (t.tv_usec - oldmusec[i]) / 1000;
    oldmusec[i] = t.tv_usec; oldsec[i] = t.tv_sec;
    return delay;
  }
#elif USE_FTIME

# include <sys/timeb.h>
  static long
  timer_proto(int i)
  {
    static long oldmsec[MAX_TIMER],oldsec[MAX_TIMER];
    struct timeb t;
    long delay;

    ftime(&t);
    delay = 1000 * (t.time - oldsec[i]) + (t.millitm - oldmsec[i]);
    oldmsec[i] = t.millitm; oldsec[i] = t.time;
    return delay;
  }
#else

# include <time.h>
# ifndef CLOCKS_PER_SEC
#   define CLOCKS_PER_SEC 1000000 /* may be false on YOUR system */
# endif
  static long
  timer_proto(int i)
  {
    static clock_t oldclocks[MAX_TIMER];
    clock_t t = clock();
    long delay = (long)((t-oldclocks[i]) * 1000. / CLOCKS_PER_SEC);

    oldclocks[i] = t;
    return delay;
  }
#endif

#define is_valid_timer(t) ((t) < MAX_TIMER || (t) >= MIN_TIMER)
long
gptimer() {return timer_proto(0);}
long
timer(void)   {return timer_proto(1);}
long
timer2(void)  {return timer_proto(2);}
long
gentimer(long t)
{
  if (!is_valid_timer(t))
    err(talker,"not an available timer (%ld)",t);
  return timer_proto(t);
}

/* internal */

long
get_timer(long t)
{
  static int used[MAX_TIMER];
  int i;
  if (!t)
  { /* get new timer */
    for (i=MIN_TIMER; i < MAX_TIMER; i++)
      if (!used[i]) { used[i] = 1; t = i; break; }
    if (!t) { t = 2; err(warner, "no timers left! Using timer2()"); }
    timer_proto(t); /* init timer */
  }
  else if (t < 0)
  { /* initialize */
    for (i=MIN_TIMER; i < MAX_TIMER; i++) used[i] = 0;
  }
  else
  { /* delete */
    if (!is_valid_timer(t) || !used[t])
      err(warner, "timer %ld wasn't in use", t);
    else
      used[t] = 0;
  }
  return t;
}

void
genmsgtimer(long t, char *format, ...)
{
  va_list args;
  PariOUT *out = pariOut; pariOut = pariErr;

  pariputs("Time "); va_start(args, format);
  vpariputs(format,args); va_end(args);
  pariputsf(": %ld\n", timer_proto(t)); pariflush();
  pariOut = out;
}

void
msgtimer(char *format, ...)
{
  va_list args;
  PariOUT *out = pariOut; pariOut = pariErr;

  pariputs("Time "); va_start(args, format);
  vpariputs(format,args); va_end(args);
  pariputsf(": %ld\n", timer_proto(2)); pariflush();
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
 *  s*p idem, setting prettyp=1
 *  s*t idem, in TeX format.
 *  D  Has a default value. Format is "Dvalue,type," (the ending comma is
 *     mandatory). Ex: D0,L, (arg is long, 0 by default).
 *     Special syntax:
 *       if type = G, &, I or V:  D[G&IV] all send NULL.
 *       if type = v: Dn sends -1.
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
 * Currently the following functions have no code word:
 * 'O' 50, 'if' 80, 'until' 82, 'while' 81, 'global' 88,
 *
 * Valence 0 reserved for functions without mandatory args.
 * Valence 99 reserved for codes which do not correspond 1-to-1 to valences.
 * Any other valence (what to do with 0?) should correspond to exactly
 *  one code.
 */
entree functions_basic[]={
{"Euler",0,(void*)mpeuler,3,"p"},
{"I",0,(void*)geni,3,""},
{"List",0,(void*)gtolist,2,"DG"},
{"Mat",0,(void*)gtomat,2,"DG"},
{"Mod",25,(void*)Mod0,2,"GGD0,L,"},
{"O",50,NULL,7,NULL},
{"Pi",0,(void*)mppi,3,"p"},
{"Pol",14,(void*)gtopoly,2,"GDn"},
{"Polrev",14,(void*)gtopolyrev,2,"GDn"},
{"Qfb",99,(void*)Qfb0,2,"GGGDGp"},
{"Ser",14,(void*)gtoser,2,"GDn"},
{"Set",0,(void*)gtoset,2,"DG"},
{"Str",0,(void*)strtoGENstr,2,"D\"\",s,D0,L,"},
{"Vec",0,(void*)gtovec,2,"DG"},
{"abs",1,(void*)gabs,3,"Gp"},
{"acos",1,(void*)gacos,3,"Gp"},
{"acosh",1,(void*)gach,3,"Gp"},
{"addprimes",0,(void*)addprimes,4,"DG"},
{"agm",29,(void*)agm,3,"GGp"},
{"algdep",99,(void*)algdep0,8,"GLD0,L,p"},
{"alias",99,(void*)alias0,11,"vrr"},
{"arg",1,(void*)garg,3,"Gp"},
{"asin",1,(void*)gasin,3,"Gp"},
{"asinh",1,(void*)gash,3,"Gp"},
{"atan",1,(void*)gatan,3,"Gp"},
{"atanh",1,(void*)gath,3,"Gp"},
{"bernfrac",11,(void*)bernfrac,3,"L"},
{"bernreal",99,(void*)bernreal,3,"Lp"},
{"bernvec",11,(void*)bernvec,3,"L"},
{"besseljh",29,(void*)jbesselh,3,"GGp"},
{"besselk",99,(void*)kbessel0,3,"GGD0,L,p"},
{"bestappr",2,(void*)bestappr,4,"GG"},
{"bezout",2,(void*)vecbezout,4,"GG"},
{"bezoutres",2,(void*)vecbezoutres,4,"GG"},
{"bigomega",18,(void*)gbigomega,4,"G"},
{"binary",18,(void*)binaire,2,"G"},
{"binomial",21,(void*)binome,4,"GL"},
{"bitand",2,(void*)gbitand,2,"GG"},
{"bitneg",99,(void*)gbitneg,2,"GD-1,L,"},
{"bitnegimply",2,(void*)gbitnegimply,2,"GG"},
{"bitor",2,(void*)gbitor,2,"GG"},
{"bittest",2,(void*)gbittest,2,"GG"},
{"bitxor",2,(void*)gbitxor,2,"GG"},
{"bnfcertify",10,(void*)certifybuchall,6,"lG"},
{"bnfclassunit",99,(void*)bnfclassunit0,6,"GD0,L,DGp"},
{"bnfclgp",99,(void*)classgrouponly,6,"GDGp"},
{"bnfdecodemodule",2,(void*)decodemodule,6,"GG"},
{"bnfinit",91,(void*)bnfinit0,6,"GD0,L,DGp"},
{"bnfisintnorm",99,(void*)bnfisintnorm,6,"GG"},
{"bnfisnorm",99,(void*)bnfisnorm,6,"GGD1,L,p"},
{"bnfisprincipal",99,(void*)isprincipalall,6,"GGD1,L,"},
{"bnfissunit",99,(void*)bnfissunit,6,"GGG"},
{"bnfisunit",2,(void*)isunit,6,"GG"},
{"bnfmake",1,(void*)bnfmake,6,"Gp"},
{"bnfnarrow",18,(void*)buchnarrow,6,"G"},
{"bnfreg",99,(void*)regulator,6,"GDGp"},
{"bnfsignunit",18,(void*)signunits,6,"G"},
{"bnfsunit",99,(void*)bnfsunit,6,"GGp"},
{"bnfunit",1,(void*)buchfu,6,"Gp"},
{"bnrL1",99,(void*)bnrL1,6,"GGD0,L,p"},
{"bnrclass",99,(void*)bnrclass0,6,"GGD0,L,p"},
{"bnrclassno",2,(void*)rayclassno,6,"GG"},
{"bnrclassnolist",2,(void*)rayclassnolist,6,"GG"},
{"bnrconductor",62,(void*)bnrconductor,6,"GDGDGD0,L,p"},
{"bnrconductorofchar",29,(void*)bnrconductorofchar,6,"GGp"},
{"bnrdisc",62,(void*)bnrdisc0,6,"GDGDGD0,L,p"},
{"bnrdisclist",99,(void*)bnrdisclist0,6,"GGDGD0,L,"},
{"bnrinit",99,(void*)bnrinit0,6,"GGD0,L,p"},
{"bnrisconductor",99,(void*)bnrisconductor,6,"lGDGDGp"},
{"bnrisprincipal",99,(void*)isprincipalrayall,6,"GGD1,L,"},
{"bnrrootnumber",99,(void*)bnrrootnumber,6,"GGD0,L,p"},
{"bnrstark",99,(void*)bnrstark,6,"GGD0,L,p"},
{"break",0,(void*)break0,11,"D1,L,"},
{"ceil",18,(void*)gceil,2,"G"},
{"centerlift",99,(void*)centerlift0,2,"GDn"},
{"changevar",2,(void*)changevar,2,"GG"},
{"charpoly",99,(void*)charpoly0,8,"GDnD0,L,"},
{"chinese",2,(void*)chinois,4,"GG"},
{"component",21,(void*)compo,2,"GL"},
{"concat",99,(void*)concat,8,"GDG"},
{"conj",18,(void*)gconj,2,"G"},
{"conjvec",1,(void*)conjvec,2,"Gp"},
{"content",18,(void*)content,4,"G"},
{"contfrac",99,(void*)contfrac0,4,"GDGD0,L,"},
{"contfracpnqn",18,(void*)pnqn,4,"G"},
{"core",99,(void*)core0,4,"GD0,L,"},
{"coredisc",99,(void*)coredisc0,4,"GD0,L,"},
{"cos",1,(void*)gcos,3,"Gp"},
{"cosh",1,(void*)gch,3,"Gp"},
{"cotan",1,(void*)gcotan,3,"Gp"},
{"denominator",18,(void*)denom,2,"G"},
{"deriv",14,(void*)deriv,7,"GDn"},
{"dilog",1,(void*)dilog,3,"Gp"},
{"dirdiv",2,(void*)dirdiv,4,"GG"},
{"direuler",99,(void*)direulerall,4,"V=GGEDG"},
{"dirmul",2,(void*)dirmul,4,"GG"},
{"dirzetak",2,(void*)dirzetak,6,"GG"},
{"divisors",18,(void*)divisors,4,"G"},
{"divrem",2,(void*)gdiventres,1,"GG"},
{"eint1",99,(void*)veceint1,3,"GDGp"},
{"elladd",3,(void*)addell,5,"GGG"},
{"ellak",2,(void*)akell,5,"GG"},
{"ellan",23,(void*)anell,5,"GL"},
{"ellap",25,(void*)ellap0,5,"GGD0,L,"},
{"ellbil",99,(void*)bilhell,5,"GGGp"},
{"ellchangecurve",2,(void*)coordch,5,"GG"},
{"ellchangepoint",2,(void*)pointch,5,"GG"},
{"elleisnum",99,(void*)elleisnum,5,"GLD0,L,p"},
{"elleta",1,(void*)elleta,5,"Gp"},
{"ellglobalred",18,(void*)globalreduction,5,"G"},
{"ellheight",99,(void*)ellheight0,5,"GGD0,L,p"},
{"ellheightmatrix",29,(void*)mathell,5,"GGp"},
{"ellinit",99,(void*)ellinit0,5,"GD0,L,p"},
{"ellisoncurve",20,(void*)oncurve,5,"lGG"},
{"ellj",1,(void*)jell,5,"Gp"},
{"elllocalred",2,(void*)localreduction,5,"GG"},
{"elllseries",99,(void*)lseriesell,5,"GGDGp"},
{"ellorder",2,(void*)orderell,5,"GG"},
{"ellordinate",29,(void*)ordell,5,"GGp"},
{"ellpointtoz",29,(void*)zell,5,"GGp"},
{"ellpow",99,(void*)powell,5,"GGGp"},
{"ellrootno",99,(void*)ellrootno,5,"lGDG"},
{"ellsigma",99,(void*)ellsigma,5,"GGD0,L,p"},
{"ellsub",99,(void*)subell,5,"GGGp"},
{"elltaniyama",1,(void*)taniyama,5,"Gp"},
{"elltors",99,(void*)elltors0,5,"GD0,L,p"},
{"ellwp",99,(void*)ellwp0,5,"GDGD0,L,pP"},
{"ellzeta",99,(void*)ellzeta,5,"GGp"},
{"ellztopoint",29,(void*)pointell,5,"GGp"},
{"erfc",1,(void*)gerfc,3,"Gp"},
{"eta",99,(void*)eta0,3,"GD0,L,p"},
{"eulerphi",18,(void*)gphi,4,"G"},
{"eval",18,(void*)geval,7,"G"},
{"exp",1,(void*)gexp,3,"Gp"},
{"factor",99,(void*)factor0,4,"GD-1,L,"},
{"factorback",99,(void*)factorback,4,"GDG"},
{"factorcantor",2,(void*)factcantor,4,"GG"},
{"factorff",3,(void*)factmod9,4,"GGG"},
{"factorial",99,(void*)mpfactr,4,"Lp"},
{"factorint",99,(void*)factorint,4,"GD0,L,"},
{"factormod",25,(void*)factormod0,4,"GGD0,L,"},
{"factornf",2,(void*)polfnf,6,"GG"},
{"factorpadic",99,(void*)factorpadic0,7,"GGLD0,L,"},
{"ffinit",99,(void*)ffinit,4,"GLDn"},
{"fibonacci",11,(void*)fibo,4,"L"},
{"floor",18,(void*)gfloor,2,"G"},
{"for",83,(void*)forpari,11,"vV=GGI"},
{"fordiv",84,(void*)fordiv,11,"vGVI"},
{"forprime",83,(void*)forprime,11,"vV=GGI"},
{"forstep",86,(void*)forstep,11,"vV=GGGI"},
{"forsubgroup",99,(void*)forsubgroup,11,"vV=GD0,L,I"},
{"forvec",87,(void*)forvec,11,"vV=GID0,L,"},
{"frac",18,(void*)gfrac,2,"G"},
{"galoisfixedfield",99,(void*)galoisfixedfield,6,"GGD0,L,Dn"},
{"galoisinit",99,(void*)galoisinit,6,"GDG,"},
{"galoispermtopol",2,(void*)galoispermtopol,6,"GG"},
{"galoissubcyclo",99,(void*)galoissubcyclo,6,"LGDGDn"},
{"gamma",1,(void*)ggamma,3,"Gp"},
{"gammah",1,(void*)ggamd,3,"Gp"},
{"gcd",25,(void*)gcd0,4,"GGD0,L,"},
{"getheap",0,(void*)getheap,11,""},
{"getrand",0,(void*)getrand,11,"l"},
{"getstack",0,(void*)getstack,11,"l"},
{"gettime",0,(void*)gettime,11,"l"},
{"hilbert",99,(void*)hil0,4,"lGGDG"},
{"hyperu",99,(void*)hyperu,3,"GGGp"},
{"idealadd",3,(void*)idealadd,6,"GGG"},
{"idealaddtoone",99,(void*)idealaddtoone0,6,"GGDG"},
{"idealappr",25,(void*)idealappr0,6,"GGD0,L,"},
{"idealchinese",3,(void*)idealchinese,6,"GGG"},
{"idealcoprime",3,(void*)idealcoprime,6,"GGG"},
{"idealdiv",99,(void*)idealdiv0,6,"GGGD0,L,"},
{"idealfactor",2,(void*)idealfactor,6,"GG"},
{"idealhnf",99,(void*)idealhnf0,6,"GGDG"},
{"idealintersect",3,(void*)idealintersect,6,"GGG"},
{"idealinv",25,(void*)idealinv0,6,"GGD0,L,"},
{"ideallist",99,(void*)ideallist0,6,"GLD4,L,"},
{"ideallistarch",99,(void*)ideallistarch0,6,"GGDGD0,L,"},
{"ideallog",99,(void*)zideallog,6,"GGGp"},
{"idealmin",99,(void*)minideal,6,"GGDGp"},
{"idealmul",99,(void*)idealmul0,6,"GGGD0,L,p"},
{"idealnorm",2,(void*)idealnorm,6,"GG"},
{"idealpow",99,(void*)idealpow0,6,"GGGD0,L,p"},
{"idealprimedec",29,(void*)primedec,6,"GG"},
{"idealprincipal",2,(void*)principalideal,6,"GG"},
{"idealred",99,(void*)ideallllred,6,"GGDGp"},
{"idealstar",99,(void*)idealstar0,6,"GGD1,L,"},
{"idealtwoelt",99,(void*)ideal_two_elt0,6,"GGDG"},
{"idealval",30,(void*)idealval,6,"lGGG"},
{"ideleprincipal",29,(void*)principalidele,6,"GGp"},
{"if",80,NULL,11,NULL},
{"imag",18,(void*)gimag,2,"G"},
{"incgam",99,(void*)incgam0,3,"GGDGp"},
{"incgamc",29,(void*)incgam3,3,"GGp"},
{"intformal",14,(void*)integ,7,"GDn"},
{"intnum",99,(void*)intnum0,9,"V=GGED0,L,p"},
{"isfundamental",18,(void*)gisfundamental,4,"G"},
{"isprime",99,(void*)gisprime,4,"GD0,L,"},
{"ispseudoprime",18,(void*)gispsp,4,"G"},
{"issquare",99,(void*)gcarrecomplet,4,"GD&"},
{"issquarefree",18,(void*)gissquarefree,4,"G"},
{"kronecker",2,(void*)gkronecker,4,"GG"},
{"lcm",2,(void*)glcm,4,"GG"},
{"length",10,(void*)glength,2,"lG"},
{"lex",20,(void*)lexcmp,1,"lGG"},
{"lift",99,(void*)lift0,2,"GDn"},
{"lindep",99,(void*)lindep0,8,"GD0,L,p"},
{"listcreate",11,(void*)listcreate,8,"L"},
{"listinsert",99,(void*)listinsert,8,"GGL"},
{"listkill",99,(void*)listkill,8,"vG"},
{"listput",25,(void*)listput,8,"GGD0,L,"},
{"listsort",99,(void*)listsort,8,"GD0,L,"},
{"lngamma",1,(void*)glngamma,3,"Gp"},
{"log",99,(void*)log0,3,"GD0,L,p"},
{"matadjoint",18,(void*)adj,8,"G"},
{"matalgtobasis",2,(void*)matalgtobasis,6,"GG"},
{"matbasistoalg",2,(void*)matbasistoalg,6,"GG"},
{"matcompanion",18,(void*)assmat,8,"G"},
{"matdet",99,(void*)det0,8,"GD0,L,"},
{"matdetint",18,(void*)detint,8,"G"},
{"matdiagonal",18,(void*)diagonal,8,"G"},
{"mateigen",1,(void*)eigen,8,"Gp"},
{"mathess",18,(void*)hess,8,"G"},
{"mathilbert",11,(void*)mathilbert,8,"L"},
{"mathnf",99,(void*)mathnf0,8,"GD0,L,"},
{"mathnfmod",2,(void*)hnfmod,8,"GG"},
{"mathnfmodid",2,(void*)hnfmodid,8,"GG"},
{"matid",11,(void*)idmat,8,"L"},
{"matimage",99,(void*)matimage0,8,"GD0,L,"},
{"matimagecompl",18,(void*)imagecompl,8,"G"},
{"matindexrank",18,(void*)indexrank,8,"G"},
{"matintersect",2,(void*)intersect,8,"GG"},
{"matinverseimage",2,(void*)inverseimage,8,"GG"},
{"matisdiagonal",10,(void*)isdiagonal,8,"lG"},
{"matker",99,(void*)matker0,8,"GD0,L,p"},
{"matkerint",99,(void*)matkerint0,8,"GD0,L,"},
{"matmuldiagonal",2,(void*)matmuldiagonal,8,"GG"},
{"matmultodiagonal",2,(void*)matmultodiagonal,8,"GG"},
{"matpascal",99,(void*)matqpascal,8,"LDG"},
{"matrank",10,(void*)rank,8,"lG"},
{"matrix",49,(void*)matrice,8,"GGDVDVDI"},
{"matrixqz",2,(void*)matrixqz0,8,"GG"},
{"matsize",18,(void*)matsize,8,"G"},
{"matsnf",99,(void*)matsnf0,8,"GD0,L,"},
{"matsolve",2,(void*)gauss,8,"GG"},
{"matsolvemod",99,(void*)matsolvemod0,8,"GGGD0,L,"},
{"matsupplement",1,(void*)suppl,8,"Gp"},
{"mattranspose",18,(void*)gtrans,8,"G"},
{"max",2,(void*)gmax,1,"GG"},
{"min",2,(void*)gmin,1,"GG"},
{"modreverse",18,(void*)polymodrecip,6,"G"},
{"moebius",18,(void*)gmu,4,"G"},
{"newtonpoly",2,(void*)newtonpoly,6,"GG"},
{"next",0,(void*)next0,11,"D1,L,"},
{"nextprime",18,(void*)gnextprime,4,"G"},
{"nfalgtobasis",2,(void*)algtobasis,6,"GG"},
{"nfbasis",99,(void*)nfbasis0,6,"GD0,L,DG"},
{"nfbasistoalg",2,(void*)basistoalg,6,"GG"},
{"nfdetint",2,(void*)nfdetint,6,"GG"},
{"nfdisc",99,(void*)nfdiscf0,6,"GD0,L,DG"},
{"nfeltdiv",3,(void*)element_div,6,"GGG"},
{"nfeltdiveuc",3,(void*)nfdiveuc,6,"GGG"},
{"nfeltdivmodpr",4,(void*)element_divmodpr,6,"GGGG"},
{"nfeltdivrem",3,(void*)nfdivres,6,"GGG"},
{"nfeltmod",3,(void*)nfmod,6,"GGG"},
{"nfeltmul",3,(void*)element_mul,6,"GGG"},
{"nfeltmulmodpr",4,(void*)element_mulmodpr2,6,"GGGG"},
{"nfeltpow",3,(void*)element_pow,6,"GGG"},
{"nfeltpowmodpr",4,(void*)element_powmodpr,6,"GGGG"},
{"nfeltreduce",3,(void*)element_reduce,6,"GGG"},
{"nfeltreducemodpr",3,(void*)nfreducemodpr2,6,"GGG"},
{"nfeltval",30,(void*)element_val,6,"lGGG"},
{"nffactor",99,(void*)nffactor,6,"GG"},
{"nffactormod",99,(void*)nffactormod,6,"GGG"},
{"nfgaloisapply",3,(void*)galoisapply,6,"GGG"},
{"nfgaloisconj",99,(void*)galoisconj0,6,"GD0,L,DGp"},
{"nfhilbert",99,(void*)nfhilbert0,6,"lGGGDG"},
{"nfhnf",2,(void*)nfhermite,6,"GG"},
{"nfhnfmod",3,(void*)nfhermitemod,6,"GGG"},
{"nfinit",99,(void*)nfinit0,6,"GD0,L,p"},
{"nfisideal",20,(void*)isideal,6,"lGG"},
{"nfisincl",2,(void*)nfisincl,6,"GG"},
{"nfisisom",2,(void*)nfisisom,6,"GG"},
{"nfkermodpr",3,(void*)nfkermodpr,6,"GGG"},
{"nfmodprinit",2,(void*)nfmodprinit,6,"GG"},
{"nfnewprec",1,(void*)nfnewprec,6,"Gp"},
{"nfroots",99,(void*)nfroots,6,"GG"},
{"nfrootsof1",1,(void*)rootsof1,6,"G"},
{"nfsnf",2,(void*)nfsmith,6,"GG"},
{"nfsolvemodpr",4,(void*)nfsolvemodpr,6,"GGGG"},
{"nfsubfields",99,(void*)subfields0,6,"GDG"},
{"norm",18,(void*)gnorm,2,"G"},
{"norml2",18,(void*)gnorml2,2,"G"},
{"numdiv",18,(void*)gnumbdiv,4,"G"},
{"numerator",18,(void*)numer,2,"G"},
{"numtoperm",24,(void*)permute,2,"LG"},
{"omega",18,(void*)gomega,4,"G"},
{"padicappr",2,(void*)apprgen9,7,"GG"},
{"padicprec",20,(void*)padicprec,2,"lGG"},
{"permtonum",18,(void*)permuteInv,2,"G"},
{"polcoeff",99,(void*)polcoeff0,7,"GLDn"},
{"polcompositum",25,(void*)polcompositum0,6,"GGD0,L,"},
{"polcyclo",99,(void*)cyclo,7,"LDn"},
{"poldegree",99,(void*)poldegree,7,"lGDn"},
{"poldisc",99,(void*)poldisc0,7,"GDn"},
{"poldiscreduced",18,(void*)reduceddiscsmith,7,"G"},
{"polgalois",99,(void*)galois,6,"Gp"},
{"polhensellift",99,(void*)polhensellift,7,"GGGL"},
{"polinterpolate",31,(void*)polint,7,"GDGDGD&"},
{"polisirreducible",18,(void*)gisirreducible,7,"G"},
{"pollead",99,(void*)pollead,7,"GDn"},
{"pollegendre",99,(void*)legendre,7,"LDn"},
{"polrecip",18,(void*)polrecip,7,"G"},
{"polred",99,(void*)polred0,6,"GD0,L,DGp"},
{"polredabs",99,(void*)polredabs0,6,"GD0,L,p"},
{"polredord",1,(void*)ordred,6,"Gp"},
{"polresultant",99,(void*)polresultant0,7,"GGDnD0,L,"},
{"polroots",99,(void*)roots0,7,"GD0,L,p"},
{"polrootsmod",25,(void*)rootmod0,7,"GGD0,L,"},
{"polrootspadic",32,(void*)rootpadic,7,"GGL"},
{"polsturm",99,(void*)sturmpart,7,"lGDGDG"},
{"polsubcyclo",99,(void*)subcyclo,7,"GGDn"},
{"polsylvestermatrix",29,(void*)sylvestermatrix,7,"GGp"},
{"polsym",21,(void*)polsym,7,"GL"},
{"poltchebi",99,(void*)tchebi,7,"LDn"},
{"poltschirnhaus",18,(void*)tschirnhaus,6,"G"},
{"polylog",99,(void*)polylog0,3,"LGD0,L,p"},
{"polzagier",99,(void*)polzag,7,"LL"},
{"precision",99,(void*)precision0,2,"GD0,L,"},
{"precprime",18,(void*)gprecprime,4,"G"},
{"prime",11,(void*)prime,4,"L"},
{"primes",11,(void*)primes,4,"L"},
{"prod",47,(void*)produit,9,"V=GGEDG"},
{"prodeuler",37,(void*)prodeuler,9,"V=GGEp"},
{"prodinf",99,(void*)prodinf0,9,"V=GED0,L,p"},
{"psi",1,(void*)gpsi,3,"Gp"},
{"qfbclassno",99,(void*)qfbclassno0,4,"GD0,L,"},
{"qfbcompraw",2,(void*)compraw,4,"GG"},
{"qfbhclassno",18,(void*)hclassno,4,"G"},
{"qfbnucomp",3,(void*)nucomp,4,"GGG"},
{"qfbnupow",2,(void*)nupow,4,"GG"},
{"qfbpowraw",23,(void*)powraw,4,"GL"},
{"qfbprimeform",29,(void*)primeform,4,"GGp"},
{"qfbred",99,(void*)qfbred0,4,"GD0,L,DGDGDG"},
{"qfgaussred",18,(void*)sqred,8,"G"},
{"qfjacobi",1,(void*)jacobi,8,"Gp"},
{"qflll",99,(void*)qflll0,8,"GD0,L,p"},
{"qflllgram",99,(void*)qflllgram0,8,"GD0,L,p"},
{"qfminim",33,(void*)qfminim0,8,"GGGD0,L,p"},
{"qfperfection",18,(void*)perf,8,"G"},
{"qfsign",18,(void*)signat,8,"G"},
{"quadclassunit",96,(void*)quadclassunit0,4,"GD0,L,DGp"},
{"quaddisc",18,(void*)quaddisc,4,"G"},
{"quadgen",18,(void*)quadgen,4,"G"},
{"quadhilbert",99,(void*)quadhilbert,4,"GDGp"},
{"quadpoly",99,(void*)quadpoly0,4,"GDn"},
{"quadray",99,(void*)quadray,4,"GGDGp"},
{"quadregulator",1,(void*)gregula,4,"Gp"},
{"quadunit",1,(void*)gfundunit,4,"Gp"},
{"random",0,(void*)genrand,2,"DG"},
{"real",18,(void*)greal,2,"G"},
{"removeprimes",0,(void*)removeprimes,4,"DG"},
{"reorder",0,(void*)reorder,11,"DG"},
{"return",0,(void*)return0,11,"DG"},
{"rnfalgtobasis",2,(void*)rnfalgtobasis,6,"GG"},
{"rnfbasis",2,(void*)rnfbasis,6,"GG"},
{"rnfbasistoalg",2,(void*)rnfbasistoalg,6,"GG"},
{"rnfcharpoly",99,(void*)rnfcharpoly,6,"GGGDn"},
{"rnfconductor",29,(void*)rnfconductor,6,"GGp"},
{"rnfdedekind",99,(void*)rnfdedekind,6,"GGG"},
{"rnfdet",99,(void*)rnfdet0,6,"GGDG"},
{"rnfdisc",2,(void*)rnfdiscf,6,"GG"},
{"rnfeltabstorel",2,(void*)rnfelementabstorel,6,"GG"},
{"rnfeltdown",2,(void*)rnfelementdown,6,"GG"},
{"rnfeltreltoabs",2,(void*)rnfelementreltoabs,6,"GG"},
{"rnfeltup",2,(void*)rnfelementup,6,"GG"},
{"rnfequation",25,(void*)rnfequation0,6,"GGD0,L,"},
{"rnfhnfbasis",2,(void*)rnfhermitebasis,6,"GG"},
{"rnfidealabstorel",2,(void*)rnfidealabstorel,6,"GG"},
{"rnfidealdown",2,(void*)rnfidealdown,6,"GG"},
{"rnfidealhnf",2,(void*)rnfidealhermite,6,"GG"},
{"rnfidealmul",2,(void*)rnfidealmul,6,"GG"},
{"rnfidealnormabs",2,(void*)rnfidealnormabs,6,"GG"},
{"rnfidealnormrel",2,(void*)rnfidealnormrel,6,"GG"},
{"rnfidealreltoabs",2,(void*)rnfidealreltoabs,6,"GG"},
{"rnfidealtwoelt",2,(void*)rnfidealtwoelement,6,"GG"},
{"rnfidealup",2,(void*)rnfidealup,6,"GG"},
{"rnfinit",29,(void*)rnfinitalg,6,"GGp"},
{"rnfisfree",20,(void*)rnfisfree,6,"lGG"},
{"rnfisnorm",99,(void*)rnfisnorm,6,"GGGD1,L,p"},
{"rnfkummer",99,(void*)rnfkummer,6,"GGD0,L,p"},
{"rnflllgram",99,(void*)rnflllgram,6,"GGGp"},
{"rnfnormgroup",2,(void*)rnfnormgroup,6,"GG"},
{"rnfpolred",29,(void*)rnfpolred,6,"GGp"},
{"rnfpolredabs",99,(void*)rnfpolredabs,6,"GGD0,L,p"},
{"rnfpseudobasis",2,(void*)rnfpseudobasis,6,"GG"},
{"rnfsteinitz",2,(void*)rnfsteinitz,6,"GG"},
{"round",99,(void*)round0,2,"GD&"},
{"serconvol",2,(void*)convol,7,"GG"},
{"serlaplace",18,(void*)laplace,7,"G"},
{"serreverse",18,(void*)recip,7,"G"},
{"setintersect",2,(void*)setintersect,8,"GG"},
{"setisset",10,(void*)setisset,8,"lG"},
{"setminus",2,(void*)setminus,8,"GG"},
{"setrand",99,(void*)setrand,11,"lL"},
{"setsearch",99,(void*)setsearch,8,"lGGD0,L,"},
{"setunion",2,(void*)setunion,8,"GG"},
{"shift",99,(void*)gshift,1,"GL"},
{"shiftmul",99,(void*)gmul2n,1,"GL"},
{"sigma",99,(void*)gsumdivk,4,"GD1,L,"},
{"sign",10,(void*)gsigne,1,"lG"},
{"simplify",18,(void*)simplify,2,"G"},
{"sin",1,(void*)gsin,3,"Gp"},
{"sinh",1,(void*)gsh,3,"Gp"},
{"sizebyte",10,(void*)taille2,2,"lG"},
{"sizedigit",10,(void*)gsize,2,"lG"},
{"solve",37,(void*)zbrent,9,"V=GGEp"},
{"sqr",18,(void*)gsqr,3,"G"},
{"sqrt",1,(void*)gsqrt,3,"Gp"},
{"sqrtint",1,(void*)racine,4,"G"},
{"sqrtn",99,(void*)gsqrtn,3,"GGD&p"},
{"subgrouplist",99,(void*)subgrouplist0,6,"GD0,L,D0,L,p"},
{"subst",26,(void*)gsubst,7,"GnG"},
{"sum",48,(void*)somme,9,"V=GGEDG"},
{"sumalt",99,(void*)sumalt0,9,"V=GED0,L,p"},
{"sumdiv",22,(void*)divsum,9,"GVE"},
{"suminf",27,(void*)suminf,9,"V=GEp"},
{"sumpos",99,(void*)sumpos0,9,"V=GED0,L,p"},
{"tan",1,(void*)gtan,3,"Gp"},
{"tanh",1,(void*)gth,3,"Gp"},
{"taylor",12,(void*)tayl,7,"GnP"},
{"teichmuller",1,(void*)teich,3,"Gp"},
{"theta",29,(void*)theta,3,"GGp"},
{"thetanullk",99,(void*)thetanullk,3,"GLp"},
{"thue",99,(void*)thue,7,"GGDG"},
{"thueinit",99,(void*)thueinit,7,"GD0,L,p"},
{"trace",1,(void*)gtrace,8,"Gp"},
{"truncate",99,(void*)trunc0,2,"GD&"},
{"until",82,NULL,11,NULL},
{"valuation",20,(void*)ggval,2,"lGG"},
{"variable",18,(void*)gpolvar,2,"G"},
{"vecextract",99,(void*)extract0,8,"GGDG"},
{"vecmax",1,(void*)vecmax,1,"Gp"},
{"vecmin",1,(void*)vecmin,1,"Gp"},
{"vecsort",99,(void*)vecsort0,8,"GDGD0,L,"},
{"vector",28,(void*)vecteur,8,"GDVDI"},
{"vectorv",28,(void*)vvecteur,8,"GDVDI"},
{"weber",99,(void*)weber0,3,"GD0,L,p"},
{"while",81,NULL,11,NULL},
{"zeta",1,(void*)gzeta,3,"Gp"},
{"zetak",99,(void*)gzetakall,6,"GGD0,L,p"},
{"zetakinit",1,(void*)initzeta,6,"Gp"},
{"znlog",2,(void*)znlog,4,"GG"},
{"znorder",18,(void*)order,4,"G"},
{"znprimroot",18,(void*)ggener,4,"G"},
{"znstar",1,(void*)znstar,4,"Gp"},

/* DO NOT REMOVE THIS BLANK LINE: chname & helpsynchro depend on it */
{NULL,0,NULL,0,NULL} /* sentinel */
};
