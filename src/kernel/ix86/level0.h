/* $Id$ */

/* This file defines some "level 0" kernel functions for Intel x386  */
/* It is intended for use with an external "asm" definition          */

#ifndef ASMINLINE
#define LOCAL_OVERFLOW
#define SAVE_OVERFLOW
#define LOCAL_HIREMAINDER
#define SAVE_HIREMAINDER

BEGINEXTERN
extern  ulong overflow;
extern  ulong hiremainder;
extern long addll(ulong x, ulong y);
extern long addllx(ulong x, ulong y);
extern long subll(ulong x, ulong y);
extern long subllx(ulong x, ulong y);
extern long shiftl(ulong x, ulong y);
extern long shiftlr(ulong x, ulong y);
extern long mulll(ulong x, ulong y);
extern long addmul(ulong x, ulong y);
extern long divll(ulong x, ulong y);
extern int  bfffo(ulong x);
ENDEXTERN

#else /* ASMINLINE */

/* $Id$ */
/* Written by Bruno Haible, 1996-1998. */

/* This file can assume the GNU C extensions.
   (It is included only if __GNUC__ is defined.) */


/* Use local variables whenever possible. */
#define LOCAL_HIREMAINDER  register ulong hiremainder
#define SAVE_OVERFLOW \
     { ulong _temp_overf = overflow; \
       extern ulong overflow; \
       overflow = _temp_overf; }
#define LOCAL_OVERFLOW  ulong overflow
#define SAVE_HIREMAINDER \
     { ulong _temp_hirem = hiremainder; \
       extern ulong hiremainder; \
       hiremainder = _temp_hirem; }
/* The global variable `hiremainder' is still necessary for the 2nd value of
   divss, divis, divsi. The global variable `overflow' is not necessary. */
extern ulong overflow;
extern ulong hiremainder;


/* Different assemblers have different syntax for the "shldl" and "shrdl"
   instructions. */
#if defined(__EMX__) || defined(__DJGCC__) || defined(__GO32__) || (defined(linux) && !defined(__ELF__)) || defined(__386BSD__) || defined(__NetBSD__) || defined(__FreeBSD__) || defined(NeXT) || defined(__CYGWIN32__) || defined(__MINGW32__) || defined(COHERENT)
#  define SHCL "%%cl,"
#else
#  define SHCL
#endif


#define addll(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ("addl %3,%0 ; adcl %1,%1" \
        : "=r" (__value), "=r" (overflow) \
        : "0" (__arg1), "g" (__arg2), "1" ((ulong)0) \
        : "cc"); \
  __value; \
})

#define addllx(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b), __temp; \
   __asm__ ("subl %5,%2 ; adcl %4,%0 ; adcl %1,%1" \
        : "=r" (__value), "=r" (overflow), "=r" (__temp) \
        : "0" (__arg1), "g" (__arg2), "g" (overflow), "1" ((ulong)0), "2" ((ulong)0) \
        : "cc"); \
  __value; \
})


#define subll(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ("subl %3,%0 ; adcl %1,%1" \
        : "=r" (__value), "=r" (overflow) \
        : "0" (__arg1), "g" (__arg2), "1" ((ulong)0) \
        : "cc"); \
  __value; \
})

#define subllx(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b), __temp; \
   __asm__ ("subl %5,%2 ; sbbl %4,%0 ; adcl %1,%1" \
        : "=r" (__value), "=r" (overflow), "=r" (__temp) \
        : "0" (__arg1), "g" (__arg2), "g" (overflow), "1" ((ulong)0), "2" ((ulong)0) \
        : "cc"); \
  __value; \
})


#if 1
#define shiftl(a,c) \
({ ulong __valuelo = (a), __count = (c), __valuehi; \
   __asm__ ("shldl "SHCL"%2,%0" /* shift %0 left by %cl bits, feeding in %2 from the right */ \
        : "=q" (__valuehi) \
        : "0" ((ulong)0), "q" (__valuelo), "c" /* %ecx */ (__count)); \
   hiremainder = __valuehi; \
   __valuelo << __count; \
})
#define shiftlr(a,c) \
({ ulong __valuehi = (a), __count = (c), __valuelo; \
   __asm__ ("shrdl "SHCL"%2,%0" /* shift %0 right by %cl bits, feeding in %2 from the left */ \
        : "=q" (__valuelo) \
        : "0" ((ulong)0), "q" (__valuehi), "c" /* %ecx */ (__count)); \
   hiremainder = __valuelo; \
   __valuehi >> __count; \
})
#else
#define shiftl(a,c) \
({ ulong __valuelo = (a), __count = (c), __valuehi; \
   __asm__ ("shldl "SHCL"%2,%0" /* shift %0 left by %cl bits, feeding in %2 from the right */ \
        : "=d" (hiremainder) \
        : "0" ((ulong)0), "q" (__valuelo), "c" /* %ecx */ (__count)); \
   __valuelo << __count; \
})
#define shiftlr(a,c) \
({ ulong __valuehi = (a), __count = (c), __valuelo; \
   __asm__ ("shrdl "SHCL"%2,%0" /* shift %0 right by %cl bits, feeding in %2 from the left */ \
        : "=d" (hiremainder) \
        : "0" ((ulong)0), "q" (__valuehi), "c" /* %ecx */ (__count)); \
   __valuehi >> __count; \
})
#endif


#define mulll(a,b) \
({ ulong __valuelo, __arg1 = (a), __arg2 = (b); \
   __asm__ ("mull %3" \
        : "=a" /* %eax */ (__valuelo), "=d" /* %edx */ (hiremainder) \
        : "0" (__arg1), "rm" (__arg2)); \
   __valuelo; \
})

#define addmul(a,b) \
({ ulong __valuelo, __arg1 = (a), __arg2 = (b), __temp; \
   __asm__ ("mull %4 ; addl %5,%0 ; adcl %6,%1" \
        : "=a" /* %eax */ (__valuelo), "=&d" /* %edx */ (hiremainder), "=r" (__temp) \
        : "0" (__arg1), "rm" (__arg2), "g" (hiremainder), "2" ((ulong)0)); \
   __valuelo; \
})

#define addmullow(a,b) \
({ ulong __valuelo, __arg1 = (a), __arg2 = (b), __temp; \
   __asm__ ("mull %3 ; addl %4,%0" \
        : "=a" /* %eax */ (__valuelo), "=&d" /* %edx */ (__temp) \
        : "0" (__arg1), "rm" (__arg2), "g" (hiremainder)); \
   __valuelo; \
})

#define divll(a,b) \
({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ("divl %4" \
        : "=a" /* %eax */ (__value), "=d" /* %edx */ (hiremainder) \
        : "0" /* %eax */ (__arg1), "1" /* %edx */ (hiremainder), "g" (__arg2)); \
   __value; \
})

#ifndef _ASMI386INLINE_H_
#  define _ASMI386INLINE_H_
#  ifdef INLINE
static inline int
bfffo(ulong x)
{
  int leading_one_position;
  __asm__ ("bsrl %1,%0" : "=r" (leading_one_position) : "rm" (x));
  return 31-leading_one_position;
}
#  endif
#endif

#endif /* ASMINLINE */
