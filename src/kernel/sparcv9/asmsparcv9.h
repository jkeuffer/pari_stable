/* $Id$ */
#ifndef __ASMSPARCV9_H__
#define __ASMSPARCV9_H__

register ulong hiremainder asm("%g5");
register ulong overflow asm("%g6");

#define addll(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   asm ( "addcc %2,%3,%0; \
          addc  %%g0,%%g0,%1" \
	 : "=r" (__value), "=r" (overflow) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%g6","cc"); \
__value; })								

#define subll(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   asm ( "subcc %2,%3,%0; \
          addc  %%g0,%%g0,%1" \
	 : "=r" (__value), "=r" (overflow) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%g6","cc"); \
__value; })								

#define addllx(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   asm ( "subcc %%g0,%%g6,%%g0; \
          addccc %2,%3,%0; \
          addc  %%g0,%%g0,%1" \
	 : "=r" (__value), "=r" (overflow) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%g6","cc"); \
__value; })								

#define subllx(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   asm ( "subcc %%g0,%%g6,%%g0; \
          subccc %2,%3,%0; \
          addc  %%g0,%%g0,%1" \
	 : "=r" (__value), "=r" (overflow) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%g6","cc"); \
__value; })								

#define shiftl(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   asm ( "neg %3,%%o4; \
          srl %2,%%o4,%1; \
          sll %2,%3,%0" \
	 : "=r" (__value), "=r" (hiremainder) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%o4","%g5"); \
__value; })								

#define shiftl2(a,b,c) \
({ ulong __value, __arg1 = (a), __arg2 = (b), __arg3 = (c); \
   asm ( "srl %2,%4,%1; \
          sll %2,%3,%0" \
	 : "=r" (__value), "=r" (hiremainder) \
	 : "r" (__arg1), "r" (__arg2), "r" (__arg3) \
         : "%g5"); \
__value; }) 			

#define shiftlr(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   asm ( "neg %3,%%o4; \
          sll %2,%%o4,%1; \
          srl %2,%3,%0" \
	 : "=r" (__value), "=r" (hiremainder) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%o4","%g5"); \
__value; }) 			

#define shiftlr1(a) \
({ ulong __value, __arg1 = (a); \
   asm ( "sll %2,31,%1; \
          srl %2,1,%0" \
	 : "=r" (__value), "=r" (hiremainder) \
	 : "r" (__arg1) \
         : "%g5"); \
__value; }) 			

#define shiftlr2(a,b,c) \
({ ulong __value, __arg1 = (a), __arg2 = (b), __arg3 = (c); \
   asm ( "sll %2,%4,%1; \
          srl %2,%3,%0" \
	 : "=r" (__value), "=r" (hiremainder) \
	 : "r" (__arg1), "r" (__arg2), "r" (__arg3) \
         : "%g5"); \
__value; }) 			

#define mulll(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   asm ( "umul %2,%3,%0; \
          srlx %0,32,%1" \
	 : "=r" (__value), "=r" (hiremainder) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%g5");	\
__value;})								

#define addmul(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   asm ( "umul %2,%3,%0; \
          add  %0,%%g5,%0; \
          srlx %0,32,%1" \
	 : "=r" (__value), "=r" (hiremainder) \
	 : "r" (__arg1), "r" (__arg2) \
         : "%g5");	\
__value;})								

#define divll(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   asm( "wr      %%g5,%%g0,%%y;\
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

#endif
