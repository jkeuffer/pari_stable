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

/* This file is a slight adaptation of source code extracted from gmp-3.1.1
  (from T. Granlund), files longlong.h and gmp-impl.h

  Copyright (C) 2000 Free Software Foundation, Inc. */

#ifdef __GNUC__

#define divll(n0, d) 							\
({ 									\
    ulong __d1, __d0, __q1, __q0, __r1, __r0, __m, __n1, __n0;	        \
    ulong __k, __d;                                                     \
                                                                        \
    __n1 = hiremainder; __n0 = n0; __d = d;                             \
   if (__d & 0x80000000UL)                                              \
      {                                                                 \
	  __k = 0;                                                      \
	  __d1 = __d >> 16; __d0 = __d & 0xffff;                        \
      }                                                                 \
    else                                                                \
    {                                                                   \
      __k = bfffo(__d);                                                 \
      __n1 = (__n1 << __k) | (__n0 >> (32 - __k));                      \
      __n0 <<= __k;                                                     \
      __d = __d << __k; __d0 = __d & 0xffff; __d1 = __d >> 16;          \
    }                                                                   \
    __q1 = __n1 / __d1;						        \
    __r1 = __n1 - __q1 * __d1;					        \
    __m = (ulong) __q1 * __d0;					        \
    __r1 = __r1 * 0x10000 | (__n0 >> 16);				\
    if (__r1 < __m)							\
      {									\
	__q1--, __r1 += __d;						\
	if (__r1 >= __d) /* i.e. we didn't get carry when adding to __r1 */\
	  if (__r1 < __m)						\
	    __q1--, __r1 += __d;					\
      }									\
    __r1 -= __m;							\
    __q0 = __r1 / __d1;							\
    __r0 = __r1  - __q0 * __d1;						\
    __m = (ulong) __q0 * __d0;					        \
    __r0 = __r0 * 0x10000 | (__n0 & 0xffff);				\
    if (__r0 < __m)							\
      {									\
	__q0--, __r0 += __d;						\
	if (__r0 >= __d)						\
	  if (__r0 < __m)						\
	    __q0--, __r0 += __d;					\
      }									\
    hiremainder = (__r0 - __m) >> __k;		                        \
    (ulong) __q1 * 0x10000 | __q0;				\
})

#else /* __GNUC__ */

static ulong divll
(ulong n0, ulong d) 							
{ 									
    ulong __d1, __d0, __q1, __q0, __r1, __r0, __m, __n1, __n0;	
    ulong __k, __d;                                        
								
    __n1 = hiremainder; __n0 = n0; 

    if (d & 0x80000000UL)                                               
      {                                                                 
	  __k = 0; __d1 = d >> 16; __d0 = d & 0xffff;                            
      }                                                                 
    else                                                                
    {                                                                   
      __k = bfffo(d);                                                   
      __n1 = (__n1 << __k) | (__n0 >> (32 - __k));               
      __n0 = __n0 << __k;                                               
      __d = (d) << __k; __d0 = __d & 0xffff; __d1 = __d >> 16;          
    }                                                                   
    __q1 = __n1 / __d1;						        
    __r1 = __n1 - __q1 * __d1;					        
    __m = (ulong) __q1 * __d0;					
    __r1 = __r1 * 0x10000 | (__n0 >> 16);				
    if (__r1 < __m)							
      {									
	__q1--, __r1 += __d;						
	if (__r1 >= __d) /* i.e. we didn't get carry when adding to __r1 */
	  if (__r1 < __m)						
	    __q1--, __r1 += __d;					
      }									
    __r1 -= __m;							
                                                                        
    __q0 = __r1 / __d1;							
    __r0 = __r1  - __q0 * __d1;						
    __m = (ulong) __q0 * __d0;					
    __r0 = __r0 * 0x10000 | (__n0 & 0xffff);				
    if (__r0 < __m)							
      {									
	__q0--, __r0 += __d;						
	if (__r0 >= __d)						
	  if (__r0 < __m)						
	    __q0--, __r0 += __d;					
      }									
    hiremainder = (__r0 - __m) >> __k;					
    return (ulong) __q1 * 0x10000 | __q0;			       
}

#endif /* __GNUC__ */
