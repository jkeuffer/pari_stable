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
typedef ulong gpmem_t;

typedef struct stackzone
{
  gpmem_t zonetop, bot, top, avma;
  size_t memused;
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
  void (*flush)(void);     /* Finalize a report of a non fatal-error. */
  void (*die)(void);       /* If not-NULL, should be called to finalize
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

extern gpmem_t avma,bot,top;
extern size_t memused;
extern byteptr diffptr;
extern entree  **varentries;
extern char    *errmessage[], *current_psfile;

#define is_universal_constant(x) ((GEN)(x) >= gzero && (GEN)(x) <= gi)

#define copyifstack(x,y)  STMT_START {gpmem_t _t=(gpmem_t)(x); \
  (y)=(_t>=bot &&_t<top)? lcopy((GEN)_t): (long)_t;} STMT_END
#define icopyifstack(x,y) STMT_START {gpmem_t _t=(gpmem_t)(x); \
  (y)=(_t>=bot &&_t<top)? licopy((GEN)_t): (long)_t;} STMT_END
#define isonstack(x) ((gpmem_t)(x)>=bot && (gpmem_t)(x)<top)

/* Define this to (1) locally (in a given file, NOT here) to check
 * "random" garbage collecting
 */
#ifdef DYNAMIC_STACK
#  define low_stack(x,l) (avma < (gpmem_t)(l))
#else
#  define low_stack(x,l) (avma < (gpmem_t)(x))
#endif

#define stack_lim(av,n) (bot + (((av)-bot)>>(n)))

#ifndef SIG_IGN
#  define SIG_IGN (void(*)())1
#endif
#ifndef SIGINT
#  define SIGINT 2
#endif
