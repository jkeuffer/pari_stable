/******************************************************************/
/* This file contains memory and I/O management definitions       */
/* $Id$ */

typedef unsigned char *byteptr;

typedef struct stackzone
{
  long zonetop, bot, top, avma, memused;
} stackzone;

typedef struct entree {
  char *name;
  ulong valence;
  void *value;
  long menu;
  char *code;
  struct entree *next;
  char *help;
  void *args;
} entree;

typedef struct PariOUT {
  void (*putch)(char);
  void (*puts)(char*);
  void (*flush)();     /* Finalize a report of a non fatal-error. */
  void (*die)();       /* If not-NULL, should be called to finalize
                          a report of a fatal error (no "\n" required). */
} PariOUT;

typedef struct pariFILE {
  FILE *file;
  int type;
  char *name;
  struct pariFILE* prev;
  struct pariFILE* next;
} pariFILE;
/* Common global variables: */

extern PariOUT *pariOut, *pariErr;
extern FILE    *pari_outfile, *logfile, *infile, *errfile;

extern ulong avma,bot,top,memused;
extern byteptr diffptr;
extern entree  **varentries;
extern char    *errmessage[], *current_psfile;


/* This may not be exact on all machines [Ptitboul] */
#define is_universal_constant(x) \
  ((long)(x) >= (long)gzero && (long)(x)<=(long)gi)

#define copyifstack(x,y) {long t=(long)(x); \
			  (y)=(t>=bot &&t<top)? lcopy((GEN)t): t;}
#define icopyifstack(x,y) {long t=(long)(x); \
			  (y)=(t>=bot &&t<top)? licopy((GEN)t): t;}
#define isonstack(x) ((GEN)(x)>=(GEN)bot && (GEN)(x)<(GEN)top)

/* Define this to (1) locally (in a given file, NOT here) to check
 * "random" garbage collecting
 */
#ifdef DYNAMIC_STACK
#  define low_stack(x,l) (avma < (l))
#else
#  define low_stack(x,l) (avma < (x))
#endif

#define stack_lim(av,n) (bot + (((av)-bot)>>(n)))
