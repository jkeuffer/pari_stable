/* $Id$

Copyright (C) 2003  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

/* This file originally adapted from gmp-3.1.1 (from T. Granlund), files
 * longlong.h and gmp-impl.h

  Copyright (C) 2000 Free Software Foundation, Inc. */

#if !defined(INLINE) || defined(INLINE_IS_STATIC)
long divll(ulong x, ulong y);
#else

#define __GLUE(hi, lo) (((hi) << BITS_IN_HALFULONG) | (lo))
#define __SPLIT(a, b, c) b = HIGHWORD(a); c = LOWWORD(a)
#define __LDIV(a, b, q, r) q = a / b; r = a - q*b

/* divide (hiremainder * 2^BITS_IN_LONG + n0) by d; assume hiremainder < d.
 * Return quotient, set hiremainder to remainder */
INLINE long
divll(ulong __n0, ulong __d)
{
  ulong d1, d0, q1, q0, r1, r0, m, k, n0 = __n0, n1 = hiremainder, d = __d;

  if (n1 == 0)
  { /* Only one division needed */
    __LDIV(n0, d, q1, hiremainder);
  }
  else if (d < LOWMASK)
  { /* Two half-word divisions  */
    n1 = __GLUE(n1, HIGHWORD(n0));
    __LDIV(n1, d, q1, r1);
    n1 = __GLUE(r1,  LOWWORD(n0));
    __LDIV(n1, d, q0, hiremainder);
    q1 = __GLUE(q1, q0);
  }
  else
  { /* General case */
    if (d & HIGHBIT)
    {
      k = 0; __SPLIT(d, d1, d0);
    }
    else
    {
      k = bfffo(d);
      n1 = (n1 << k) | (n0 >> (BITS_IN_LONG - k));
      n0 = n0 << k;
      d = d << k; __SPLIT(d, d1, d0);
    }
    __LDIV(n1, d1, q1, r1);
    m =  q1 * d0;
    r1 = __GLUE(r1, HIGHWORD(n0));
    if (r1 < m)
      {
        q1--, r1 += d;
        if (r1 >= d) /* we didn't get carry when adding to r1 */
          if (r1 < m) q1--, r1 += d;
      }
    r1 -= m;
    __LDIV(r1, d1, q0, r0);
    m =  q0 * d0;
    r0 = __GLUE(r0, LOWWORD(n0));
    if (r0 < m)
      {
        q0--, r0 += d;
        if (r0 >= d)
          if (r0 < m) q0--, r0 += d;
      }
    hiremainder = (r0 - m) >> k;
    q1 = __GLUE(q1, q0);
  }
  return q1;
}
#endif
