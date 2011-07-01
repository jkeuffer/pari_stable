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

/*
ASM addll mulll bfffo divll
*/
/* Written by Bill Allombert from the ix86 version by Bruno Haible. Basically
 * change insl to insq*/
#ifdef ASMINLINE
#define LOCAL_HIREMAINDER  register ulong hiremainder
#define LOCAL_OVERFLOW     register ulong overflow

#define addll(a,b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ("addq %3,%0 ; adcq %1,%1" \
        : "=r" (__value), "=r" (overflow) \
        : "0" (__arg1), "g" (__arg2), "1" ((ulong)0) \
        : "cc"); \
  __value; \
})

#define addllx(a,b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b), __temp; \
   __asm__ ("subq %5,%2 ; adcq %4,%0 ; adcq %1,%1" \
        : "=r" (__value), "=&r" (overflow), "=&r" (__temp) \
        : "0" (__arg1), "g" (__arg2), "g" (overflow), "1" ((ulong)0), "2" ((ulong)0) \
        : "cc"); \
  __value; \
})

#define addllx8(a,b,c,overflow) \
do { long *__arg1 = a, *__arg2 = b, *__out = c; \
     ulong __temp; \
   __asm__ ("subq %6, %1 \n\t" \
            "movq    (%3), %1 ; adcq    (%4),%1; movq %1,    (%5) \n\t" \
            "movq  -8(%3), %1 ; adcq  -8(%4),%1; movq %1,  -8(%5) \n\t" \
            "movq -16(%3), %1 ; adcq -16(%4),%1; movq %1, -16(%5) \n\t" \
            "movq -24(%3), %1 ; adcq -24(%4),%1; movq %1, -24(%5) \n\t" \
            "movq -32(%3), %1 ; adcq -32(%4),%1; movq %1, -32(%5) \n\t" \
            "movq -40(%3), %1 ; adcq -40(%4),%1; movq %1, -40(%5) \n\t" \
            "movq -48(%3), %1 ; adcq -48(%4),%1; movq %1, -48(%5) \n\t" \
            "movq -56(%3), %1 ; adcq -56(%4),%1; movq %1, -56(%5) \n\t" \
            "adcq  %2, %2" \
        : "=m" (*__out), "=&r" (__temp), "=&g" (overflow) \
        : "r" (__arg1), "r" (__arg2), "r" (__out), "g" (overflow), "1" ((ulong)0), "2" ((ulong)0) \
        : "cc"); \
} while(0)

#define subll(a,b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ("subq %3,%0 ; adcq %1,%1" \
        : "=r" (__value), "=r" (overflow) \
        : "0" (__arg1), "g" (__arg2), "1" ((ulong)0) \
        : "cc"); \
  __value; \
})

#define subllx(a,b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b), __temp; \
   __asm__ ("subq %5,%2 ; sbbq %4,%0 ; adcq %1,%1" \
        : "=r" (__value), "=&r" (overflow), "=&r" (__temp) \
        : "0" (__arg1), "g" (__arg2), "g" (overflow), "1" ((ulong)0), "2" ((ulong)0) \
        : "cc"); \
  __value; \
})

#define mulll(a,b) \
__extension__ ({ ulong __valuelo, __arg1 = (a), __arg2 = (b); \
   __asm__ ("mulq %3" \
        : "=a" /* %eax */ (__valuelo), "=d" /* %edx */ (hiremainder) \
        : "0" (__arg1), "rm" (__arg2)); \
   __valuelo; \
})

#define addmul(a,b) \
__extension__ ({ ulong __valuelo, __arg1 = (a), __arg2 = (b), __temp; \
   __asm__ ("mulq %4 ; addq %5,%0 ; adcq %6,%1" \
        : "=a" /* %eax */ (__valuelo), "=&d" /* %edx */ (hiremainder), "=r" (__temp) \
        : "0" (__arg1), "rm" (__arg2), "g" (hiremainder), "2" ((ulong)0)); \
   __valuelo; \
})

#define divll(a,b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ("divq %4" \
        : "=a" /* %eax */ (__value), "=&d" /* %edx */ (hiremainder) \
        : "0" /* %eax */ (__arg1), "1" /* %edx */ (hiremainder), "mr" (__arg2)); \
   __value; \
})

#define bfffo(x) \
__extension__ ({ ulong __arg = (x); \
   long leading_one_position; \
  __asm__ ("bsrq %1,%0" : "=r" (leading_one_position) : "rm" (__arg)); \
  63 - leading_one_position; \
})
#endif
