/* $Id$ */

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
#define SAVE_OVERFLOW
#define LOCAL_HIREMAINDER
#define SAVE_HIREMAINDER

BEGINEXTERN
extern long divll(unsigned long x, unsigned long y);
extern int  bfffo(unsigned long x);
ENDEXTERN

#ifndef ASMINLINE
BEGINEXTERN
extern unsigned long hiremainder, overflow;
extern long addll(unsigned long a, unsigned long b);
extern long addllx(unsigned long a, unsigned long b);
extern long subll(unsigned long a, unsigned long b);
extern long subllx(unsigned long a, unsigned long b);
extern long shiftl(unsigned long x, unsigned long y);
extern long shiftlr(unsigned long x, unsigned long y);
extern long mulll(unsigned long x, unsigned long y);
extern long addmul(unsigned long x, unsigned long y);
ENDEXTERN

#else /* ASMINLINE */

register unsigned long hiremainder __asm__("%g5");
register unsigned long overflow __asm__("%g6");

#define addll(a,b) \
({ unsigned long __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ( "addcc %2,%3,%0; \
          addx  %%g0,%%g0,%1" \
	 : "=r" (__value), "=r" (overflow) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%g6","cc"); \
__value; })								

#define addllx(a,b) \
({ unsigned long __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ( "subcc %%g0,%%g6,%%g0; \
          addxcc %2,%3,%0; \
          addx  %%g0,%%g0,%1" \
	 : "=r" (__value), "=r" (overflow) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%g6","cc"); \
__value; })								

#define subll(a,b) \
({ unsigned long __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ( "subcc %2,%3,%0; \
          addx  %%g0,%%g0,%1" \
	 : "=r" (__value), "=r" (overflow) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%g6","cc"); \
__value; })								

#define subllx(a,b) \
({ unsigned long __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ( "subcc %%g0,%%g6,%%g0; \
          subxcc %2,%3,%0; \
          addx  %%g0,%%g0,%1" \
	 : "=r" (__value), "=r" (overflow) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%g6","cc"); \
__value; })								

#define shiftl(a,b) \
({ unsigned long __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ( "neg %3,%%o4; \
          srl %2,%%o4,%1; \
          sll %2,%3,%0" \
	 : "=r" (__value), "=r" (hiremainder) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%o4","%g5"); \
__value; })								

#define shiftl2(a,b,c) \
({ unsigned long __value, __arg1 = (a), __arg2 = (b), __arg3 = (c); \
   __asm__ ( "srl %2,%4,%1; \
          sll %2,%3,%0" \
	 : "=r" (__value), "=r" (hiremainder) \
	 : "r" (__arg1), "r" (__arg2), "r" (__arg3) \
         : "%g5"); \
__value; }) 			

#define shiftlr(a,b) \
({ unsigned long __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ( "neg %3,%%o4; \
          sll %2,%%o4,%1; \
          srl %2,%3,%0" \
	 : "=r" (__value), "=r" (hiremainder) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%o4","%g5"); \
__value; }) 			

#define shiftlr1(a) \
({ unsigned long __value, __arg1 = (a); \
   __asm__ ( "sll %2,31,%1; \
          srl %2,1,%0" \
	 : "=r" (__value), "=r" (hiremainder) \
	 : "r" (__arg1) \
         : "%g5"); \
__value; }) 			

#define shiftlr2(a,b,c) \
({ unsigned long __value, __arg1 = (a), __arg2 = (b), __arg3 = (c); \
   __asm__ ( "sll %2,%4,%1; \
          srl %2,%3,%0" \
	 : "=r" (__value), "=r" (hiremainder) \
	 : "r" (__arg1), "r" (__arg2), "r" (__arg3) \
         : "%g5"); \
__value; }) 			

#define mulll(a,b) \
({ unsigned long __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ( "umul %2,%3,%0; \
          rd  %%y,%1" \
	 : "=r" (__value), "=r" (hiremainder) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%g5");	\
__value;})								

#define addmul(a,b) \
({ unsigned long __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ( "umul %2,%3,%0; \
          rd  %%y,%%o4; \
          addcc %0,%%g5,%0; \
          addx %%g0,%%o4,%1" \
	 : "=r" (__value), "=r" (hiremainder) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%o4","%g5","cc");	\
__value;})								

#define divllasm(a,b) \
({ unsigned long __value, __arg1 = (a), __arg2 = (b); \
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
