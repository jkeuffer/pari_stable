/* $Id$ */

#ifndef __GENPARI__
#define __GENPARI__
#include "paricfg.h"

#ifdef macintosh
#  include <Types.h>
#  include <StdLib.h>
#else
#  if defined(__cplusplus) || !defined(__M68K__)
#    include <stdlib.h>   /* malloc, free, atoi */
#  endif
#  ifdef UNIX
#    define _INCLUDE_POSIX_SOURCE /* for HPUX */
#    include <sys/types.h> /* size_t */
#  endif
#endif

#ifdef WINCE
#  include <windows.h>
#else
#  include <signal.h>
#  include <stdio.h>
#endif

#include <stdarg.h>
#include <setjmp.h>
#include <string.h>
#if !defined(_WIN32) && !defined(WINCE)
#  include <unistd.h>
#endif
#include <math.h>
#ifdef alliant
/* string.h */
#  undef strcpy
#  undef strlen
#  undef strncpy
/* math.h */
#  undef atan
#  undef cos
#  undef exp
#  undef fabs
#  undef log
#  undef sin
#  undef sqrt
#else /* ! alliant */
#  include <memory.h>
#endif
#include <ctype.h>

#ifdef WINCE
#  include "parice.h" 
#endif
#include "paritype.h"
#include "parisys.h"
#include "parigen.h"
#include "paricast.h"
#include "paristio.h"
#include "paricom.h"
#include "parierr.h"
#include "paridecl.h"

#if defined(__MWERKS__)
#  include <SIOUX.h>
#  include <Memory.h>
#  define malloc(x) NewPtr(x)
#  define free(x) DisposePtr((Ptr)(x))
#  define CodeWarrior_Bug
#  pragma pointers_in_D0
   void *macrealloc(void *p, size_t olds, size_t news);
#  pragma pointers_in_A0
#endif

#if defined(__M68K__) || ( defined(macintosh) && !defined(powerc) )
#  include "pari68k.h"
#else
#  include "pariport.h"
#endif

#include "pariinl.h"
#endif
