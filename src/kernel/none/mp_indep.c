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

/* assume N > 0 */
GEN
randomi(GEN N)
{
  long lx, i, n;
  GEN x, xMSW, xd, Nd;

  lx = lgefint(N); x = cgeti(lx);
  x[1] = evalsigne(1) | evallgefint(lx);
  xMSW = xd = int_MSW(x);
  for (i=2; i<lx; i++) { *xd = pari_rand(); xd = int_precW(xd); }

  Nd = int_MSW(N); n = *Nd;
  xd = xMSW;
  if (lx == 3) n--;
  else
    for (i=3; i<lx; i++)
    {
      xd = int_precW(xd);
      Nd = int_precW(Nd);
      if (*xd != *Nd) {
        if ((ulong)*xd > (ulong)*Nd) n--;
        break;
      }
    }
  /* MSW needs to be generated between 0 and n */
  if (n) n = (long)((((ulong)*xMSW) / (HIGHBIT*2.)) * (n + 1));
  *xMSW = (long)n;
  if (!n) x = int_normalize(x, 1);
  return x;
}

/********************************************************************/
/**                                                                **/
/**              EXPONENT / CONVERSION t_REAL --> double           **/
/**                                                                **/
/********************************************************************/

#ifdef LONG_IS_64BIT
long
expodb(double x)
{
  union { double f; ulong i; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */

  if (x==0.) return -exp_mid;
  fi.f = x;
  return ((fi.i & (HIGHBIT-1)) >> mant_len) - exp_mid;
}

GEN
dbltor(double x)
{
  GEN z;
  long e;
  union { double f; ulong i; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */
  const int expo_len = 11; /* number of bits of exponent */
  LOCAL_HIREMAINDER;

  if (x==0.) return realzero_bit(-exp_mid);
  fi.f = x; z = cgetr(DEFAULTPREC);
  e = ((fi.i & (HIGHBIT-1)) >> mant_len) - exp_mid;
  z[1] = evalexpo(e) | evalsigne(x<0? -1: 1);
  z[2] = (fi.i << expo_len) | HIGHBIT;
  return z;
}

double
rtodbl(GEN x)
{
  long ex,s=signe(x);
  ulong a;
  union { double f; ulong i; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */
  const int expo_len = 11; /* number of bits of exponent */
  LOCAL_HIREMAINDER;

  if (typ(x)==t_INT && !s) return 0.0;
  if (typ(x)!=t_REAL) err(typeer,"rtodbl");
  if (!s || (ex=expo(x)) < - exp_mid) return 0.0;

  /* start by rounding to closest */
  a = (x[2] & (HIGHBIT-1)) + 0x400;
  if (a & HIGHBIT) { ex++; a=0; }
  if (ex >= exp_mid) err(rtodber);
  fi.i = ((ex + exp_mid) << mant_len) | (a >> expo_len);
  if (s<0) fi.i |= HIGHBIT;
  return fi.f;
}

#else /* LONG_IS_64BIT */

#if   PARI_DOUBLE_FORMAT == 1
#  define INDEX0 1
#  define INDEX1 0
#elif PARI_DOUBLE_FORMAT == 0
#  define INDEX0 0
#  define INDEX1 1
#endif

long
expodb(double x)
{
  union { double f; ulong i[2]; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */
  const int shift = mant_len-32;

  if (x==0.) return -exp_mid;
  fi.f = x;
  {
    const ulong a = fi.i[INDEX0];
    return ((a & (HIGHBIT-1)) >> shift) - exp_mid;
  }
}

GEN
dbltor(double x)
{
  GEN z;
  long e;
  union { double f; ulong i[2]; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */
  const int expo_len = 11; /* number of bits of exponent */
  const int shift = mant_len-32;

  if (x==0.) return realzero_bit(-exp_mid);
  fi.f = x; z=cgetr(DEFAULTPREC);
  {
    const ulong a = fi.i[INDEX0];
    const ulong b = fi.i[INDEX1];
    e = ((a & (HIGHBIT-1)) >> shift) - exp_mid;
    z[1] = evalexpo(e) | evalsigne(x<0? -1: 1);
    z[3] = b << expo_len;
    z[2] = HIGHBIT | b >> (BITS_IN_LONG-expo_len) | (a << expo_len);
  }
  return z;
}

double
rtodbl(GEN x)
{
  long ex,s=signe(x),lx=lg(x);
  ulong a,b,k;
  union { double f; ulong i[2]; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */
  const int expo_len = 11; /* number of bits of exponent */
  const int shift = mant_len-32;

  if (typ(x)==t_INT && !s) return 0.0;
  if (typ(x)!=t_REAL) err(typeer,"rtodbl");
  if (!s || (ex=expo(x)) < - exp_mid) return 0.0;

  /* start by rounding to closest */
  a = x[2] & (HIGHBIT-1);
  if (lx > 3)
  {
    b = x[3] + 0x400UL; if (b < 0x400UL) a++;
    if (a & HIGHBIT) { ex++; a=0; }
  }
  else b = 0;
  if (ex > exp_mid) err(rtodber);
  ex += exp_mid;
  k = (a >> expo_len) | (ex << shift);
  if (s<0) k |= HIGHBIT;
  fi.i[INDEX0] = k;
  fi.i[INDEX1] = (a << (BITS_IN_LONG-expo_len)) | (b >> expo_len);
  return fi.f;
}
#endif /* LONG_IS_64BIT */

