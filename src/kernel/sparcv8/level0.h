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

/* This file defines some "level 0" kernel functions for SPARC V8 */
/* These functions can be inline, with gcc                        */
/* If not gcc, they are defined externally with "level0.s"        */
/* This file is common to SuperSparc and MicroSparc               */
/*                                                                */
/* These following symbols can be inlined                         */
/* overflow hiremainder                                           */
/* addll addllx subll subllx shiftl shiftlr mulll addmul          */
/*                                                                */
/* These functions are always in level0.s                         */
/* The following symbols are always defined in this file :        */
/* divll bfffo (& tabshi)                                         */
/*   But divll have to use hiremainder, so it is different when   */
/*   hiremainder is inline or not                                 */
/*   If libpari.so is compiled with gcc, you should compile all   */
/*   files with gcc                                               */

#define LOCAL_OVERFLOW
#define LOCAL_HIREMAINDER

BEGINEXTERN
extern long divll(ulong x, ulong y);
extern int  bfffo(ulong x);
ENDEXTERN

#ifndef ASMINLINE
BEGINEXTERN
  extern ulong hiremainder, overflow;
  extern long addll(ulong a, ulong b);
  extern long addllx(ulong a, ulong b);
  extern long subll(ulong a, ulong b);
  extern long subllx(ulong a, ulong b);
  extern long shiftl(ulong x, ulong y);
  extern long shiftlr(ulong x, ulong y);
  extern long mulll(ulong x, ulong y);
  extern long addmul(ulong x, ulong y);
ENDEXTERN

#else /* ASMINLINE */

#define REGISTER_MP_OPERANDS
register ulong hiremainder __asm__("%g5");
register ulong overflow __asm__("%g6");

#define addll(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ( "addcc %2,%3,%0; \
          addx  %%g0,%%g0,%1" \
	 : "=r" (__value), "=r" (overflow) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%g6","cc"); \
__value; })								

#define addllx(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ( "subcc %%g0,%%g6,%%g0; \
          addxcc %2,%3,%0; \
          addx  %%g0,%%g0,%1" \
	 : "=r" (__value), "=r" (overflow) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%g6","cc"); \
__value; })								

#define subll(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ( "subcc %2,%3,%0; \
          addx  %%g0,%%g0,%1" \
	 : "=r" (__value), "=r" (overflow) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%g6","cc"); \
__value; })								

#define subllx(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ( "subcc %%g0,%%g6,%%g0; \
          subxcc %2,%3,%0; \
          addx  %%g0,%%g0,%1" \
	 : "=r" (__value), "=r" (overflow) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%g6","cc"); \
__value; })								

#define shiftl(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ( "neg %3,%%o4; \
          srl %2,%%o4,%1; \
          sll %2,%3,%0" \
	 : "=r" (__value), "=r" (hiremainder) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%o4","%g5"); \
__value; })								

#define shiftlr(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ( "neg %3,%%o4; \
          sll %2,%%o4,%1; \
          srl %2,%3,%0" \
	 : "=r" (__value), "=r" (hiremainder) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%o4","%g5"); \
__value; }) 			

#define mulll(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ( "umul %2,%3,%0; \
          rd  %%y,%1" \
	 : "=r" (__value), "=r" (hiremainder) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%g5");	\
__value;})								

#define addmul(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ( "umul %2,%3,%0; \
          rd  %%y,%%o4; \
          addcc %0,%%g5,%0; \
          addx %%g0,%%o4,%1" \
	 : "=r" (__value), "=r" (hiremainder) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%o4","%g5","cc");	\
__value;})								

#define divllasm(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__( "wr      %%g5,%%g0,%%y;\
         mov     %2,%%o4;\
	 udivcc  %2,%3,%0;\
         bvc     1f;\
         umul    %0,%3,%%o5;\
         mov     47,%%o0;\
         call    err,1;\
         nop         ;\
1:	 sub     %%o4,%%o5,%1"\
	: "=r" (__value), "=r" (hiremainder) \
	: "r" (__arg1), "r" (__arg2) \
        : "%o4","%o5","%g5","cc");	\
__value;})								

#endif /* ASMINLINE */
