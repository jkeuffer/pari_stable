/* $Id$ */

/* This file defines some "level 0" kernel functions                 */
/* These functions can be inline, with gcc                           */
/* If not gcc, they are defined externally with "level0.c"           */
/* NB: Those functions are not defined in mp.s                       */

/* level0.c includes this file and never needs to be changed         */
/* The following seven lines are necessary for level0.c and level1.c */
#ifdef  LEVEL0
#undef  INLINE
#define INLINE
#endif
#ifdef  LEVEL1
#undef  INLINE
#endif

#define LOCAL_OVERFLOW
#define SAVE_OVERFLOW
#define LOCAL_HIREMAINDER
#define SAVE_HIREMAINDER

#ifndef INLINE
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

#else

ulong overflow;
ulong hiremainder;

INLINE long
addll(ulong x, ulong y)
{
  const ulong z = x+y;
  overflow=(z<x);
  return (long) z;
}

INLINE long
addllx(ulong x, ulong y)
{
  const ulong z = x+y+overflow;
  overflow = (z<x || (z==x && overflow));
  return (long) z;
}

INLINE long
subll(ulong x, ulong y)
{
  const ulong z = x-y;
  overflow = (z>x);
  return (long) z;
}

INLINE long
subllx(ulong x, ulong y)
{
  const ulong z = x-y-overflow;
  overflow = (z>x || (z==x && overflow));
  return (long) z;
}

INLINE long
shiftl(ulong x, ulong y)
{
  hiremainder=x>>(BITS_IN_LONG-y);
  return (x<<y);
}

INLINE long
shiftlr(ulong x, ulong y)
{
  hiremainder=x<<(BITS_IN_LONG-y);
  return (x>>y);
}

#define HIGHWORD(a) ((a) >> BITS_IN_HALFULONG)
#define LOWWORD(a) ((a) & LOWMASK)

/* Version Peter Montgomery */
/*
 *      Assume (for presentation) that BITS_IN_LONG = 32.
 *      Then 0 <= xhi, xlo, yhi, ylo <= 2^16 - 1.  Hence
 *
 * -2^31 + 2^16 <= (xhi-2^15)*(ylo-2^15) + (xlo-2^15)*(yhi-2^15) <= 2^31.
 *
 *      If xhi*ylo + xlo*yhi = 2^32*overflow + xymid, then
 *
 * -2^32 + 2^16 <= 2^32*overflow + xymid - 2^15*(xhi + ylo + xlo + yhi) <= 0.
 *
 * 2^16*overflow <= (xhi+xlo+yhi+ylo)/2 - xymid/2^16 <= 2^16*overflow + 2^16-1
 *
 *       This inequality was derived using exact (rational) arithmetic;
 *       it remains valid when we truncate the two middle terms.
 */
INLINE long
mulll(ulong x, ulong y)
{
  const ulong xlo = LOWWORD(x), xhi = HIGHWORD(x);
  const ulong ylo = LOWWORD(y), yhi = HIGHWORD(y);
  ulong xylo,xymid,xyhi,xymidhi,xymidlo;

  xylo = xlo*ylo; xyhi = xhi*yhi;
  xymid = (xhi+xlo)*(yhi+ylo) - (xyhi+xylo);

  xymidhi = HIGHWORD(xymid);
  xymidlo = xymid << BITS_IN_HALFULONG;

  xylo += xymidlo;
  hiremainder = xyhi + xymidhi + (xylo < xymidlo)
     + (((((xhi+xlo) + (yhi+ylo)) >> 1) - xymidhi) & HIGHMASK);

  return xylo;
}

INLINE long
addmul(ulong x, ulong y)
{
  const ulong xlo = LOWWORD(x), xhi = HIGHWORD(x);
  const ulong ylo = LOWWORD(y), yhi = HIGHWORD(y);
  ulong xylo,xymid,xyhi,xymidhi,xymidlo;

  xylo = xlo*ylo; xyhi = xhi*yhi;
  xymid = (xhi+xlo)*(yhi+ylo) - (xyhi+xylo);

  xylo += hiremainder; xyhi += (xylo < hiremainder);

  xymidhi = HIGHWORD(xymid);
  xymidlo = xymid << BITS_IN_HALFULONG;

  xylo += xymidlo;
  hiremainder = xyhi + xymidhi + (xylo < xymidlo)
     + (((((xhi+xlo) + (yhi+ylo)) >> 1) - xymidhi) & HIGHMASK);

  return xylo;
}

/* version Peter Montgomery */

INLINE int
bfffo(ulong x)
{
  int sc;
  static int tabshi[16]={4,3,2,2,1,1,1,1,0,0,0,0,0,0,0,0};

  sc = BITS_IN_LONG - 4;
#ifdef LONG_IS_64BIT
  if (x & 0xffffffff00000000) {sc -= 32; x >>= 32;}
#endif
  if (x > 0xffffUL) {sc -= 16; x >>= 16;}
  if (x > 0x00ffUL) {sc -= 8; x >>= 8;}
  if (x > 0x000fUL) {sc -= 4; x >>= 4;}
  return sc + tabshi[x];
}

/* Version Peter Montgomery */

INLINE long
divll(ulong x, ulong y)
{
#define GLUE(hi, lo) (((hi) << BITS_IN_HALFULONG) + (lo))
#define SPLIT(a, b, c) b = HIGHWORD(a); c = LOWWORD(a)

  ulong v1, v2, u3, u4, q1, q2, aux, aux1, aux2;
  int k;
  if (hiremainder >= y) err(talker, "Invalid arguments to divll");
  if (hiremainder == 0)
  {    /* Only one division needed */
    hiremainder = x % y;
    return x/y;
  }
  if (y <= LOWMASK)
  {    /* Use two half-word divisions */
    hiremainder = GLUE(hiremainder, HIGHWORD(x));
    q1 = hiremainder / y;
    hiremainder = GLUE(hiremainder % y, LOWWORD(x));
    q2 = hiremainder / y;
    hiremainder = hiremainder % y;
    return GLUE(q1, q2);
  }
  if (y & HIGHBIT) k = 0;
  else
  {
    k = bfffo(y);
    hiremainder = (hiremainder << k) + (x >> (BITS_IN_LONG - k));
    x <<= k; y <<= k;
  }
  SPLIT(y, v1, v2);
  SPLIT(x, u3, u4);
  q1 = hiremainder / v1; if (q1 > LOWMASK) q1 = LOWMASK;
  hiremainder -= q1 * v1;
  aux = v2 * q1;
again:
  SPLIT(aux, aux1, aux2);
  if (aux2 > u3) aux1++;
  if (aux1 > hiremainder) {q1--; hiremainder += v1; aux -= v2; goto again;}

  hiremainder = GLUE(hiremainder - aux1, LOWWORD(u3 - aux2));
  q2 = hiremainder / v1; if (q2 > LOWMASK) q2 = LOWMASK;
  hiremainder -= q2 * v1;
  aux = v2 * q2;
again2:
  SPLIT(aux, aux1, aux2);
  if (aux2 > u4) aux1++;
  if (aux1 > hiremainder) {q2--; hiremainder += v1; aux -= v2; goto again2;}
  hiremainder = GLUE(hiremainder - aux1, LOWWORD(u4 - aux2)) >> k;
  return GLUE(q1, q2);
}

#endif
