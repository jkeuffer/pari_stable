#line 2 "../src/kernel/none/level0.h"
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

#define LOCAL_OVERFLOW
#define LOCAL_HIREMAINDER

#if !defined(INLINE)
extern ulong overflow, hiremainder;
extern long addll(ulong x, ulong y);
extern long addllx(ulong x, ulong y);
extern long subll(ulong x, ulong y);
extern long subllx(ulong x, ulong y);
extern long shiftl(ulong x, ulong y);
extern long shiftlr(ulong x, ulong y);
extern long mulll(ulong x, ulong y);
extern long addmul(ulong x, ulong y);

#else

extern ulong overflow, hiremainder;

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
  ulong xhl,yhl;

  xylo = xlo*ylo; xyhi = xhi*yhi;
  xhl = xhi+xlo; yhl = yhi+ylo;
  xymid = xhl*yhl - (xyhi+xylo);

  xymidhi = HIGHWORD(xymid);
  xymidlo = xymid << BITS_IN_HALFULONG;

  xylo += xymidlo;
  hiremainder = xyhi + xymidhi + (xylo < xymidlo)
     + ((((xhl + yhl) >> 1) - xymidhi) & HIGHMASK);

  return xylo;
}

INLINE long
addmul(ulong x, ulong y)
{
  const ulong xlo = LOWWORD(x), xhi = HIGHWORD(x);
  const ulong ylo = LOWWORD(y), yhi = HIGHWORD(y);
  ulong xylo,xymid,xyhi,xymidhi,xymidlo;
  ulong xhl,yhl;

  xylo = xlo*ylo; xyhi = xhi*yhi;
  xhl = xhi+xlo; yhl = yhi+ylo;
  xymid = xhl*yhl - (xyhi+xylo);

  xylo += hiremainder; xyhi += (xylo < hiremainder);

  xymidhi = HIGHWORD(xymid);
  xymidlo = xymid << BITS_IN_HALFULONG;

  xylo += xymidlo;
  hiremainder = xyhi + xymidhi + (xylo < xymidlo)
     + ((((xhl + yhl) >> 1) - xymidhi) & HIGHMASK);

  return xylo;
}
#endif
