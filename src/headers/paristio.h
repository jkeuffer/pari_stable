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

/* This file contains memory and I/O management definitions       */

typedef struct {
  long s, us;
} pari_timer;

typedef unsigned char *byteptr;
typedef ulong pari_sp;

/* binary I/O */
typedef struct GENbin {
  size_t len; /* gsizeword(x) */
  GEN x; /* binary copy of x */
  GEN base; /* base address of p->x */
  int canon; /* 1: t_INT in canonical (native kernel) form,
                0: t_INT according to current kernel */
} GENbin;

struct pari_mainstack
{
  pari_sp top, bot, avma;
  size_t memused;
};

struct pari_thread
{
  struct pari_mainstack st;
  GEN data;
};

typedef struct pariFILE {
  FILE *file;
  int type;
  const char *name;
  struct pariFILE* prev;
  struct pariFILE* next;
} pariFILE;
/* pariFILE.type */
enum { mf_IN  = 1, mf_PIPE = 2, mf_FALSE = 4, mf_OUT = 8, mf_PERM = 16 };

typedef struct entree {
  const char *name;
  ulong valence;
  void *value;
  long menu;
  const char *code;
  const char *help;
  void *pvalue;
  long arity;
  struct entree *next;
} entree;

struct pari_parsestate
{
  long node;
  int once;
  const char *lex_start, *unused_chars;
  GEN lasterror;
};

struct pari_compilestate
{
  long opcode, operand, data, localvars, frames, dbginfo;
  long offset;
  const char *dbgstart;
};

struct pari_evalstate
{
  pari_sp avma;
  long sp;
  long rp;
  long var;
  long lvars;
  long trace;
  struct pari_compilestate comp;
};

struct gp_context
{
  long listloc;
  struct pari_evalstate eval;
  struct pari_parsestate parse;
  pariFILE *file;
};

typedef struct PariOUT {
  void (*putch)(char);
  void (*puts)(const char*);
  void (*flush)(void);
} PariOUT;

/* hashtables */
typedef struct hashentry {
  void *key, *val;
  ulong hash; /* hash(key) */
  struct hashentry *next;
} hashentry;

typedef struct hashtable {
  ulong len; /* table length */
  hashentry **table; /* the table */
  ulong nb, maxnb; /* number of entries stored and max nb before enlarging */
  ulong pindex; /* prime index */
  ulong (*hash) (void *k); /* hash function */
  int (*eq) (void *k1, void *k2); /* equality test */
} hashtable;

typedef struct {
  long offset;
  long n;
  long alloc;
  size_t size;
} pari_stack;

/* Common global variables: */

extern PariOUT *pariOut, *pariErr;
extern FILE    *pari_outfile, *pari_logfile, *pari_infile, *pari_errfile;
extern ulong    logstyle;

enum logstyles {
    logstyle_none,        /* 0 */
    logstyle_plain,        /* 1 */
    logstyle_color,        /* 2 */
    logstyle_TeX         /* 3 */
};

#define TEXSTYLE_PAREN        2
#define TEXSTYLE_BREAK        4

extern THREAD pari_sp avma, bot, top;
#define DISABLE_MEMUSED (size_t)-1
extern THREAD size_t memused;
extern byteptr diffptr;
extern char *errmessage[], *current_psfile, *pari_datadir;

#define gcopyifstack(x,y)  STMT_START {pari_sp _t=(pari_sp)(x); \
  (y)=(_t>=bot &&_t<top)? gcopy((GEN)_t): (GEN)_t;} STMT_END
#define copyifstack(x,y)  STMT_START {pari_sp _t=(pari_sp)(x); \
  (y)=(_t>=bot &&_t<top)? gcopy((GEN)_t): (GEN)_t;} STMT_END
#define icopyifstack(x,y) STMT_START {pari_sp _t=(pari_sp)(x); \
  (y)=(_t>=bot &&_t<top)? icopy((GEN)_t): (GEN)_t;} STMT_END

/* Define this to (1) locally (in a given file, NOT here) to check
 * "random" garbage collecting */
#ifdef DYNAMIC_STACK
#  define low_stack(x,l) (avma < (pari_sp)(l))
#else
#  define low_stack(x,l) (avma < (pari_sp)(x))
#endif

#define stack_lim(av,n) (bot + (((av)-bot)>>(n)))

#ifndef SIG_IGN
#  define SIG_IGN (void(*)())1
#endif
#ifndef SIGINT
#  define SIGINT 2
#endif
