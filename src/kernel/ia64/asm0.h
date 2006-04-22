#line 2 "../src/kernel/ia64/asm0.h"
/* $Id$

Copyright (C) 2006  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

/*
ASM mulll
NOASM addll bfffo divll
*/

#ifdef ASMINLINE
/* Written by Guillaume Hanrot */
#define LOCAL_HIREMAINDER  register ulong hiremainder

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
#endif
