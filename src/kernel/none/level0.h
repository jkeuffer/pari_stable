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

/* This file defines "level 0" kernel functions.
 * These functions can be inline; if not, they are defined externally in
 * level0.c, which includes this file and never needs to be changed
 * The following lines are necessary for level0.c and level1.c */
#ifdef  LEVEL0
#  undef  INLINE_IS_STATIC
#  undef  INLINE
#  define INLINE
#endif
#ifdef  LEVEL1
#  undef  INLINE_IS_STATIC
#  undef  INLINE
#endif

#define LOCAL_OVERFLOW
#define LOCAL_HIREMAINDER

#if !defined(INLINE) || defined(INLINE_IS_STATIC)
ulong overflow, hiremainder;
long addll(ulong x, ulong y);
long addllx(ulong x, ulong y);
long subll(ulong x, ulong y);
long subllx(ulong x, ulong y);
long shiftl(ulong x, ulong y);
long shiftlr(ulong x, ulong y);
long mulll(ulong x, ulong y);
long addmul(ulong x, ulong y);
long divll(ulong x, ulong y);
int  bfffo(ulong x);

#else

extern ulong overflow;
extern ulong hiremainder;

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
#endif
