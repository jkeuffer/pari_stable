#include <stdio.h>

// typedef unsigned long ulong;
#define LOCAL_HIREMAINDER  register ulong hiremainder
#define LOCAL_OVERFLOW     register ulong overflow

#define addll(a, b)                           \
({ ulong __arg1 = (a), __arg2 = (b), __value; \
 __value = __arg1 + __arg2;                   \
 overflow = (__value < __arg1);               \
 __value;                                     \
})

#define addllx(a, b)                                          \
({ ulong __arg1 = (a), __arg2 = (b), __value, __tmp;          \
 __tmp = __arg1 + overflow;                                   \
 overflow = (__tmp < __arg1);                                 \
 __value = __tmp + __arg2;                                    \
 overflow |= (__value < __tmp);                               \
 __value;                                                     \
})

#define subll(a, b)                                           \
({ ulong __arg1 = (a), __arg2 = (b);                          \
   overflow = (__arg2 > __arg1);                              \
   __arg1 - __arg2;                                           \
})

#define subllx(a, b)                                  \
({ ulong __arg1 = (a), __arg2 = (b), __tmp, __value;  \
   __tmp = __arg1 - overflow;                         \
   overflow = (__arg1 < overflow);                    \
   __value = __tmp - __arg2;                          \
   overflow |= (__arg2 > __tmp);                      \
   __value;                                           \
})

#define shiftl(a, b)                                           \
({ ulong __arg1 = (a), __shift = (b), __cshift = 64 - __shift; \
   hiremainder = __arg1 >> __cshift;                           \
   __arg1 << __shift;                                          \
})

#define shiftlr(a, b)                                          \
({ ulong __arg1 = (a), __shift = (b), __cshift = 64 - __shift; \
   hiremainder = __arg1 << __cshift;                           \
   __arg1 >> __shift;                                          \
})

#define bfffo(a)                                                        \
({ ulong __arg1 = (a), __tmp, _a, _c;                                   \
    __asm__ ("mux1 %0 = %1, @rev" : "=r" (__tmp) : "r" (__arg1));       \
    __asm__ ("czx1.l %0 = %1" : "=r" (_a) : "r" (-__tmp | __tmp));      \
    _c = (_a - 1) << 3;                                                 \
    __arg1 >>= _c;                                                      \
    if (__arg1 >= 1 << 4)                                               \
      __arg1 >>= 4, _c += 4;                                            \
    if (__arg1 >= 1 << 2)                                               \
      __arg1 >>= 2, _c += 2;                                            \
    _c += __arg1 >> 1;                                                  \
    63 - _c;                                                            \
})

#define mulll(a, b)                                                     \
({                                                                      \
  ulong __arg1 = (a), __arg2 = (b), __value;                            \
  __asm__ ("xma.hu %0 = %2, %3, f0\n\t;;\n\txma.l %1 = %2, %3, f0"      \
           : "=&f" (hiremainder), "=f" (__value)                        \
           : "f" (__arg1), "f" (__arg2));                               \
  __value;                                                              \
})

#define addmul(a, b)                                                    \
({                                                                      \
  ulong __arg1 = (a), __arg2 = (b), __value;                            \
  __asm__ ("xma.hu %0 = %2, %3, %4\n\txma.l %1 = %2, %3, %4"            \
           : "=&f" (hiremainder), "=f" (__value)                        \
           : "f" (__arg1), "f" (__arg2), "f" (hiremainder));            \
  __value;                                                              \
})


