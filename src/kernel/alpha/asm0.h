ulong overflow;
ulong hiremainder;

#define LOCAL_OVERFLOW
#define LOCAL_HIREMAINDER
#define SAVE_OVERFLOW
#define SAVE_HIREMAINDER


/* From the PARI source, using gcc __asm__ format. */

#define addll(a, b)\
({ register ulong __value, __arg1 = (a), __arg2 = (b); \
  __asm__ volatile ("addq %2,%3,%0\n\tcmpult %4,%2,%1" \
   : "=r" (__value), "=r" (overflow) \
   : "r" (__arg1), "r" (__arg2), "0" ((ulong) 0)); \
  __value; \
})

#define addllx(a, b)\
({ register ulong __value, __arg1 = (a), __arg2 = (b), __temp; \
 __asm__ volatile ("addq %3,%4,%0\n\tcmpult %5,%3,%2\n\taddq %5,%6,%0\n\tcmpult %5,%6,%1\n\taddq %6,%7,%1\n\t" \
   : "=r" (__value), "=r" (overflow), "=r" (__temp) \
   : "r" (__arg1), "r" (__arg2), "0" ((ulong) 0), "1" (overflow), "2" ((ulong) 0)); \
__value; \
})

#define subll(a, b)\
({ register ulong __value, __arg1 = (a), __arg2 = (b); \
  __asm__ volatile ("subq %2,%3,%0\n\tcmpult %2,%4,%1" \
   : "=r" (__value), "=r" (overflow) \
   : "r" (__arg1), "r" (__arg2), "0" ((ulong)0)); \
  __value; \
})

#define subllx(a, b)\
({ register ulong __value, __arg1 = (a), __arg2 = (b), __temp1, __temp2; \
__asm__ volatile ("subq %4,%5,%2\n\tcmpult %4,%8,%3\n\tsubq %8,%7,%0\n\tcmpult %8,%6,%1\n\taddq %7,%9,%1\n\t" \
   : "=r" (__value), "=r" (overflow), "=r" (__temp1), "=r" (__temp2)  \
   : "r" (__arg1), "r" (__arg2), "0" ((ulong)0), "1" (overflow), "2" ((ulong)0), "3" ((ulong)0)); \
 __value; \
})

#define shiftl(a, b) \
({ register ulong __value, __arg1 = (a), __arg2 = (b), __temp; \
 __asm__ volatile ("subq %5,%4,%2\n\tsll %3,%4,%0\n\tsrl %3,%6,%1\n\t" \
   : "=r" (__value), "=r" (hiremainder), "=r" (__temp) \
   : "r" (__arg1), "r" (__arg2), "n" ((ulong) 64), "2" ((ulong)0)); \
 __value; \
})

#define shiftlr(a, b) \
({ register ulong __value, __arg1 = (a), __arg2 = (b), __temp; \
 __asm__ volatile ("subq %5,%4,%2\n\tsrl %3,%4,%0\n\tsll %3,%6,%1\n\t" \
   : "=r" (__value), "=r" (hiremainder), "=r" (__temp) \
   : "r" (__arg1), "r" (__arg2), "n" ((ulong) 64), "2" ((ulong)0)); \
 __value; \
})

#define mulll(a, b) \
({ register ulong __value, __arg1 = (a), __arg2 = (b); \
 __asm__ volatile ("umulh %2,%3,%1\n\tmulq %2,%3,%0\n\t" \
   : "=r" (__value), "=r" (hiremainder) \
   : "r" (__arg1), "r" (__arg2)); \
 __value; \
})

#define addmul(a, b) \
({ register ulong __value, __arg1 = (a), __arg2 = (b), __temp; \
 __asm__ volatile ("mulq %3,%4,%0\n\tumulh %3,%4,%2\n\taddq %5,%6,%0\n\tcmpult %5,%6,%1\n\taddq %7,%6,%1\n\t" \
   : "=r" (__value), "=r" (hiremainder), "=r" (__temp) \
   : "r" (__arg1), "r" (__arg2), "0" ((ulong) 0), "1" (hiremainder), "2" ((ulong) 0)); \
 __value; \
})

 /* 
   The end of the present file is a slight adaptation of source code
   extracted from gmp-3.1.1 (from T. Granlund), files longlong.h and 
   gmp-impl.h 

   Copyright (C) 1991, 1992, 1993, 1994, 1996, 1997, 1999, 2000 Free Software
   Foundation, Inc. 
 */

extern const unsigned char __clz_tab[]; 
extern ulong invert_word(ulong); 

#define bfffo(x)                           \
  ({                                       \
    ulong __xr = (x);                      \
    ulong __a;                             \
                                           \
        for (__a = 56; __a > 0; __a -= 8)  \
          if (((__xr >> __a) & 0xff) != 0) \
            break;                         \
    64 - (__clz_tab[__xr >> __a] + __a);   \
  })

#define sub_ddmmss(sh, sl, ah, al, bh, bl)                              \
  do {                                                                  \
    ulong __x;                                                          \
    __x = (al) - (bl);                                                  \
    (sh) = (ah) - (bh) - (__x > (al));                                  \
    (sl) = __x;                                                         \
  } while (0)

#define divll(x, y)                                                     \
({                                                                      \
  register ulong _di, _x = (x), _y = (y), _q, _ql, _r;                  \
  register ulong _xh, _xl, _k, __hire;                                  \
                                                                        \
  if (_y & 0x8000000000000000UL)                                        \
      { _k = 0; __hire = hiremainder; }                                 \
  else                                                                  \
  {                                                                     \
    _k = bfffo(_y);                                                     \
    __hire = (hiremainder << _k) | (_x >> (64 - _k));                   \
    _x <<= _k; _y <<=  _k;                                              \
  }                                                                     \
  _di = invert_word(_y);                                                \
  _ql = mulll (__hire, _di);                                            \
  _q = __hire + hiremainder;                                            \
  _xl = mulll(_q, _y); _xh = hiremainder;                               \
  sub_ddmmss (_xh, _r, __hire, _x, _xh, _xl);                           \
  if (_xh != 0)                                                         \
    {                                                                   \
      sub_ddmmss (_xh, _r, _xh, _r, 0, _y); _q += 1;                    \
      if (_xh != 0)                                                     \
        { sub_ddmmss (_xh, _r, _xh, _r, 0, _y); _q += 1; }              \
    }                                                                   \
  if (_r >= _y)                                                         \
    { _r -= _y; _q += 1; }                                              \
  hiremainder = _r >> _k;                                               \
  _q;                                                                   \
})


