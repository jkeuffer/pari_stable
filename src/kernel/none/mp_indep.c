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

#include "pari.h"
/********************************************************************/
/**                                                                **/
/**                         RANDOM INTEGERS                        **/
/**                                                                **/
/********************************************************************/
extern GEN int_normalize(GEN x, long known_zero_words);
static long pari_randseed = 1;

/* BSD rand gives this: seed = 1103515245*seed + 12345 */
/*Return 31 ``random'' bits.*/
long
pari_rand31(void)
{
  pari_randseed = (1000276549*pari_randseed + 12347) & 0x7fffffff;
  return pari_randseed;
}

long
setrand(long seed) { return (pari_randseed = seed); }

long
getrand(void) { return pari_randseed; }

ulong
pari_rand(void)
{
#define GLUE2(hi, lo) (((hi) << BITS_IN_HALFULONG) | (lo))
#if !defined(LONG_IS_64BIT)
  return GLUE2((pari_rand31()>>12)&LOWMASK,
               (pari_rand31()>>12)&LOWMASK);
#else
#define GLUE4(hi1,hi2, lo1,lo2) GLUE2(((hi1)<<16)|(hi2), ((lo1)<<16)|(lo2))
#  define LOWMASK2 0xffffUL
  return GLUE4((pari_rand31()>>12)&LOWMASK2,
               (pari_rand31()>>12)&LOWMASK2,
               (pari_rand31()>>12)&LOWMASK2,
               (pari_rand31()>>12)&LOWMASK2);
#endif
}

GEN
randomi(GEN N)
{
  long lx, i, t, n;
  GEN x, xMSW, xd, Nd;

  lx = lgefint(N); x = cgeti(lx);
  x[1] = evalsigne(1) | evallgefint(lx);
  xMSW = xd = int_MSW(x);
  for (i=2; i<lx; i++) { *xd = pari_rand(); xd = int_precW(xd); }

  Nd = int_MSW(N); n = *Nd;
  xd = xMSW; t = lx-1;
  for (i=2; i<t; i++)
  {
    if ((ulong)*xd < (ulong)*Nd) break;
    xd = int_precW(xd);
    Nd = int_precW(Nd);
  }
  if (i == t) n--;
  /* MSW needs to be generated between 0 and n */
  if (n) n = (long)((((ulong)*xMSW) / (HIGHBIT*2.)) * (n + 1));
  *xMSW = (long)n;
  if (!n) x = int_normalize(x, 1);
  return x;
}
