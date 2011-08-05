#line 2 "../src/kernel/ix86/asm0.h"
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

/* This file defines some "level 0" kernel functions for Intel ix86  */
/* It is intended for use with an external "asm" definition          */

/*
ASM addll mulll bfffo divll
*/
#ifdef ASMINLINE
/* Written by Bruno Haible, 1996-1998. */

/* This file can assume the GNU C extensions.
   (It is included only if __GNUC__ is defined.) */

/* Use local variables whenever possible. */
#define LOCAL_HIREMAINDER  register ulong hiremainder
#define LOCAL_OVERFLOW     register ulong overflow

#define addll(a,b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ("addl %3,%0 ; adcl %1,%1" \
        : "=r" (__value), "=r" (overflow) \
        : "0" (__arg1), "g" (__arg2), "1" ((ulong)0) \
        : "cc"); \
  __value; \
})

#define addllx(a,b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b), __temp; \
   __asm__ ("subl %5,%2 ; adcl %4,%0 ; adcl %1,%1" \
        : "=r" (__value), "=&r" (overflow), "=&r" (__temp) \
        : "0" (__arg1), "g" (__arg2), "g" (overflow), "1" ((ulong)0), "2" ((ulong)0) \
        : "cc"); \
  __value; \
})

#define addllx8(a,b,c,overflow) \
do { long *__arg1 = a, *__arg2 = b, *__out = c; \
     ulong __temp; \
   __asm__ ("subl %6, %1 \n\t" \
            "movl    (%3), %1 ; adcl    (%4),%1; movl %1,    (%5) \n\t" \
            "movl  -4(%3), %1 ; adcl  -4(%4),%1; movl %1,  -4(%5) \n\t" \
            "movl  -8(%3), %1 ; adcl  -8(%4),%1; movl %1,  -8(%5) \n\t" \
            "movl -12(%3), %1 ; adcl -12(%4),%1; movl %1, -12(%5) \n\t" \
            "movl -16(%3), %1 ; adcl -16(%4),%1; movl %1, -16(%5) \n\t" \
            "movl -20(%3), %1 ; adcl -20(%4),%1; movl %1, -20(%5) \n\t" \
            "movl -24(%3), %1 ; adcl -24(%4),%1; movl %1, -24(%5) \n\t" \
            "movl -28(%3), %1 ; adcl -28(%4),%1; movl %1, -28(%5) \n\t" \
            "adcl  %2, %2" \
        : "=m" (*__out), "=&r" (__temp), "=&r" (overflow) \
        : "r" (__arg1), "r" (__arg2), "r" (__out), "g" (overflow), "1" ((ulong)0), "2" ((ulong)0)        : "cc"); \
} while(0)

#define subll(a,b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ("subl %3,%0 ; adcl %1,%1" \
        : "=r" (__value), "=r" (overflow) \
        : "0" (__arg1), "g" (__arg2), "1" ((ulong)0) \
        : "cc"); \
  __value; \
})

#define subllx(a,b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b), __temp; \
   __asm__ ("subl %5,%2 ; sbbl %4,%0 ; adcl %1,%1" \
        : "=r" (__value), "=&r" (overflow), "=&r" (__temp) \
        : "0" (__arg1), "g" (__arg2), "g" (overflow), "1" ((ulong)0), "2" ((ulong)0) \
        : "cc"); \
  __value; \
})

#define subllx8(a,b,c,overflow) \
do { long *__arg1 = a, *__arg2 = b, *__out = c; \
     ulong __temp; \
   __asm__ ("subl %6, %1 \n\t" \
            "movl    (%3), %1 ; sbbl    (%4),%1; movl %1,    (%5) \n\t" \
            "movl  -4(%3), %1 ; sbbl  -4(%4),%1; movl %1,  -4(%5) \n\t" \
            "movl  -8(%3), %1 ; sbbl  -8(%4),%1; movl %1,  -8(%5) \n\t" \
            "movl -12(%3), %1 ; sbbl -12(%4),%1; movl %1, -12(%5) \n\t" \
            "movl -16(%3), %1 ; sbbl -16(%4),%1; movl %1, -16(%5) \n\t" \
            "movl -20(%3), %1 ; sbbl -20(%4),%1; movl %1, -20(%5) \n\t" \
            "movl -24(%3), %1 ; sbbl -24(%4),%1; movl %1, -24(%5) \n\t" \
            "movl -28(%3), %1 ; sbbl -28(%4),%1; movl %1, -28(%5) \n\t" \
            "adcl  %2, %2" \
        : "=m" (*__out), "=&r" (__temp), "=&r" (overflow) \
        : "r" (__arg1), "r" (__arg2), "r" (__out), "g" (overflow), "1" ((ulong)0), "2" ((ulong)0)        : "cc"); \
} while(0)


#define mulll(a,b) \
__extension__ ({ ulong __valuelo, __arg1 = (a), __arg2 = (b); \
   __asm__ ("mull %3" \
        : "=a" /* %eax */ (__valuelo), "=d" /* %edx */ (hiremainder) \
        : "0" (__arg1), "rm" (__arg2)); \
   __valuelo; \
})

#define addmul(a,b) \
__extension__ ({ ulong __valuelo, __arg1 = (a), __arg2 = (b), __temp; \
   __asm__ ("mull %4 ; addl %5,%0 ; adcl %6,%1" \
        : "=a" /* %eax */ (__valuelo), "=&d" /* %edx */ (hiremainder), "=r" (__temp) \
        : "0" (__arg1), "rm" (__arg2), "g" (hiremainder), "2" ((ulong)0)); \
   __valuelo; \
})

#define divll(a,b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ("divl %4" \
        : "=a" /* %eax */ (__value), "=&d" /* %edx */ (hiremainder) \
        : "0" /* %eax */ (__arg1), "1" /* %edx */ (hiremainder), "mr" (__arg2)); \
   __value; \
})

#define bfffo(x) \
__extension__ ({ ulong __arg = (x); \
   int leading_one_position; \
  __asm__ ("bsrl %1,%0" : "=r" (leading_one_position) : "rm" (__arg)); \
  31 - leading_one_position; \
})

#endif
