#line 2 "../src/kernel/x86-64/asm0.h"
/* $Id$

Copyright (C) 2004  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

/* Written by Bill Allombert from the ix86 version by Bruno Haible. Basically
 * change insl to insq*/

#ifndef ASMINLINE

#define LOCAL_OVERFLOW
#define LOCAL_HIREMAINDER

BEGINEXTERN
  extern ulong overflow, hiremainder;
  extern long addll(ulong a, ulong b);
  extern long addllx(ulong a, ulong b);
  extern long subll(ulong a, ulong b);
  extern long subllx(ulong a, ulong b);
  extern long shiftl(ulong x, ulong y);
  extern long shiftlr(ulong x, ulong y);
  extern long mulll(ulong x, ulong y);
  extern long addmul(ulong x, ulong y);
  extern long divll(ulong x, ulong y);
  extern long bfffo(ulong x);
ENDEXTERN

#else /* ASMINLINE */

#define LOCAL_HIREMAINDER  register ulong hiremainder
#define LOCAL_OVERFLOW     register ulong overflow

/* Different assemblers have different syntax for the "shldl" and "shrdl"
   instructions. */
#if defined(__EMX__) || defined(__DJGCC__) || defined(__GO32__) || (defined(linux) && !defined(__ELF__)) || defined(__386BSD__) || defined(__NetBSD__) || defined(__FreeBSD__) || defined(NeXT) || defined(__CYGWIN32__) || defined(__MINGW32__) || defined(COHERENT)
#  define SHCL "%%cl,"
#else
#  define SHCL
#endif


#define addll(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ("addq %3,%0 ; adcq %1,%1" \
        : "=r" (__value), "=r" (overflow) \
        : "0" (__arg1), "g" (__arg2), "1" ((ulong)0) \
        : "cc"); \
  __value; \
})

#define addllx(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b), __temp; \
   __asm__ ("subq %5,%2 ; adcq %4,%0 ; adcq %1,%1" \
        : "=r" (__value), "=r" (overflow), "=r" (__temp) \
        : "0" (__arg1), "g" (__arg2), "g" (overflow), "1" ((ulong)0), "2" ((ulong)0) \
        : "cc"); \
  __value; \
})

#define subll(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ("subq %3,%0 ; adcq %1,%1" \
        : "=r" (__value), "=r" (overflow) \
        : "0" (__arg1), "g" (__arg2), "1" ((ulong)0) \
        : "cc"); \
  __value; \
})

#define subllx(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b), __temp; \
   __asm__ ("subq %5,%2 ; sbbq %4,%0 ; adcq %1,%1" \
        : "=r" (__value), "=r" (overflow), "=r" (__temp) \
        : "0" (__arg1), "g" (__arg2), "g" (overflow), "1" ((ulong)0), "2" ((ulong)0) \
        : "cc"); \
  __value; \
})

#define shiftl(a,c) \
({ ulong __valuelo = (a), __count = (c), __valuehi; \
   __asm__ ("shldq "SHCL"%2,%0" /* shift %0 left by %cl bits, feeding in %2 from the right */ \
        : "=q" (__valuehi) \
        : "0" ((ulong)0), "q" (__valuelo), "c" /* %ecx */ (__count)); \
   hiremainder = __valuehi; \
   __valuelo << __count; \
})
#define shiftlr(a,c) \
({ ulong __valuehi = (a), __count = (c), __valuelo; \
   __asm__ ("shrdq "SHCL"%2,%0" /* shift %0 right by %cl bits, feeding in %2 from the left */ \
        : "=q" (__valuelo) \
        : "0" ((ulong)0), "q" (__valuehi), "c" /* %ecx */ (__count)); \
   hiremainder = __valuelo; \
   __valuehi >> __count; \
})

#define mulll(a,b) \
({ ulong __valuelo, __arg1 = (a), __arg2 = (b); \
   __asm__ ("mulq %3" \
        : "=a" /* %eax */ (__valuelo), "=d" /* %edx */ (hiremainder) \
        : "0" (__arg1), "rm" (__arg2)); \
   __valuelo; \
})

#define addmul(a,b) \
({ ulong __valuelo, __arg1 = (a), __arg2 = (b), __temp; \
   __asm__ ("mulq %4 ; addq %5,%0 ; adcq %6,%1" \
        : "=a" /* %eax */ (__valuelo), "=&d" /* %edx */ (hiremainder), "=r" (__temp) \
        : "0" (__arg1), "rm" (__arg2), "g" (hiremainder), "2" ((ulong)0)); \
   __valuelo; \
})

#define divll(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ("divq %4" \
        : "=a" /* %eax */ (__value), "=d" /* %edx */ (hiremainder) \
        : "0" /* %eax */ (__arg1), "1" /* %edx */ (hiremainder), "mr" (__arg2)); \
   __value; \
})

#define bfffo(x) \
({ ulong __arg = (x); \
   long leading_one_position; \
  __asm__ ("bsrq %1,%0" : "=r" (leading_one_position) : "rm" (__arg)); \
  63 - leading_one_position; \
})
#endif
