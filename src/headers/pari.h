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
