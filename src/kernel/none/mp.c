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

/***********************************************************************/
/**								      **/
/**		         MULTIPRECISION KERNEL           	      **/
/**                                                                   **/
/***********************************************************************/
/* most of the routines in this file are commented out in 68k */
/* version (#ifdef __M68K__) since they are defined in mp.s   */
#include "pari.h"

/* NOTE: arguments of "spec" routines (muliispec, addiispec, etc.) aren't
 * GENs but pairs (long *a, long na) representing a list of digits (in basis
 * BITS_IN_LONG) : a[0], ..., a[na-1]. [ In ordre to facilitate splitting: no
 * need to reintroduce codewords ]
 * Use speci(a,na) to visualize the coresponding GEN.
 */

/* z2 := z1[imin..imax].f shifted left sh bits (feeding f from the right) */
/* These macros work only for sh != 0 !!! */
#define shift_left2(z2,z1,imin,imax,f, sh,m) {\
  register ulong _l,_k = ((ulong)f)>>m;\
  GEN t1 = z1 + imax, t2 = z2 + imax, T = z1 + imin;\
  while (t1 > T) {\
    _l = *t1--;\
    *t2-- = (_l<<(ulong)sh) | _k;\
    _k = _l>>(ulong)m;\
  }\
  *t2 = (*t1<<(ulong)sh) | _k;\
}
#define shift_left(z2,z1,imin,imax,f, sh) {\
  register const ulong _m = BITS_IN_LONG - sh;\
  shift_left2((z2),(z1),(imin),(imax),(f),(sh),(_m));\
}

#define shift_words_r(target,source,source_end,prepend, sh, sh_complement) {\
  register ulong _k,_l = *source++;\
  *target++ = (_l>>(ulong)sh) | ((ulong)prepend<<(ulong)sh_complement);\
  while (source < source_end) {\
    _k = _l<<(ulong)sh_complement; _l = *source++;\
    *target++ = (_l>>(ulong)sh) | _k;\
  }\
}
#define shift_right2(z2,z1,imin,imax,f, sh,m) {\
  register GEN s = (z1) + (imin), ta = (z2) + (imin), se = (z1) + (imax);\
  shift_words_r(ta,s,se,(f),(sh),(m));				\
}
/* z2 := f.z1[imin..imax-1] shifted right sh bits (feeding f from the left) */
#define shift_right(z2,z1,imin,imax,f, sh) {\
  register const ulong _m = BITS_IN_LONG - (sh);\
  shift_right2((z2),(z1),(imin),(imax),(f),(sh),(_m));\
}

#define MASK(x) (((ulong)(x)) & (LGEFINTBITS | SIGNBITS))
int
egalii(GEN x, GEN y)
{
  long i;
  if (MASK(x[1]) != MASK(y[1])) return 0;
  i = lgefint(x)-1; while (i>1 && x[i]==y[i]) i--;
  return i==1;
}
#undef MASK

#ifdef INLINE
INLINE
#endif
GEN
addsispec(long s, GEN x, long nx)
{
  GEN xd, zd = (GEN)avma;
  long lz;
  LOCAL_OVERFLOW;

  lz = nx+3; (void)new_chunk(lz);
  xd = x + nx;
  *--zd = addll(*--xd, s);
  if (overflow)
    for(;;)
    {
      if (xd == x) { *--zd = 1; break; } /* enlarge z */
      *--zd = ((ulong)*--xd) + 1;
      if (*zd) { lz--; break; }
    }
  else lz--;
  while (xd > x) *--zd = *--xd;
  *--zd = evalsigne(1) | evallgefint(lz);
  *--zd = evaltyp(t_INT) | evallg(lz);
  avma=(long)zd; return zd;
}

#define swapspec(x,y, nx,ny) {long _a=nx;GEN _z=x; nx=ny; ny=_a; x=y; y=_z;}

#ifdef INLINE
INLINE
#endif
GEN
addiispec(GEN x, GEN y, long nx, long ny)
{
  GEN xd,yd,zd;
  long lz;
  LOCAL_OVERFLOW;

  if (nx < ny) swapspec(x,y, nx,ny);
  if (ny == 1) return addsispec(*y,x,nx);
  zd = (GEN)avma;
  lz = nx+3; (void)new_chunk(lz);
  xd = x + nx;
  yd = y + ny;
  *--zd = addll(*--xd, *--yd);
  while (yd > y) *--zd = addllx(*--xd, *--yd);
  if (overflow)
    for(;;)
    {
      if (xd == x) { *--zd = 1; break; } /* enlarge z */
      *--zd = ((ulong)*--xd) + 1;
      if (*zd) { lz--; break; }
    }
  else lz--;
  while (xd > x) *--zd = *--xd;
  *--zd = evalsigne(1) | evallgefint(lz);
  *--zd = evaltyp(t_INT) | evallg(lz);
  avma=(long)zd; return zd;
}

/* assume x >= y */
#ifdef INLINE
INLINE
#endif
GEN
subisspec(GEN x, long s, long nx)
{
  GEN xd, zd = (GEN)avma;
  long lz;
  LOCAL_OVERFLOW;

  lz = nx+2; (void)new_chunk(lz);
  xd = x + nx;
  *--zd = subll(*--xd, s);
  if (overflow)
    for(;;)
    {
      *--zd = ((ulong)*--xd) - 1;
      if (*xd) break;
    }
  if (xd == x)
    while (*zd == 0) { zd++; lz--; } /* shorten z */
  else
    do  *--zd = *--xd; while (xd > x);
  *--zd = evalsigne(1) | evallgefint(lz);
  *--zd = evaltyp(t_INT) | evallg(lz);
  avma=(long)zd; return zd;
}

/* assume x > y */
#ifdef INLINE
INLINE
#endif
GEN
subiispec(GEN x, GEN y, long nx, long ny)
{
  GEN xd,yd,zd;
  long lz;
  LOCAL_OVERFLOW;

  if (ny==1) return subisspec(x,*y,nx);
  zd = (GEN)avma;
  lz = nx+2; (void)new_chunk(lz);
  xd = x + nx;
  yd = y + ny;
  *--zd = subll(*--xd, *--yd);
  while (yd > y) *--zd = subllx(*--xd, *--yd);
  if (overflow)
    for(;;)
    {
      *--zd = ((ulong)*--xd) - 1;
      if (*xd) break;
    }
  if (xd == x)
    while (*zd == 0) { zd++; lz--; } /* shorten z */
  else
    do  *--zd = *--xd; while (xd > x);
  *--zd = evalsigne(1) | evallgefint(lz);
  *--zd = evaltyp(t_INT) | evallg(lz);
  avma=(long)zd; return zd;
}

#ifndef __M68K__

/* prototype of positive small ints */
static long pos_s[] = {
  evaltyp(t_INT) | m_evallg(3), evalsigne(1) | evallgefint(3), 0 };

/* prototype of negative small ints */
static long neg_s[] = {
  evaltyp(t_INT) | m_evallg(3), evalsigne(-1) | evallgefint(3), 0 };

void
affir(GEN x, GEN y)
{
  const long s=signe(x),ly=lg(y);
  long lx,sh,i;

  if (!s)
  {
    y[1] = evalexpo(-bit_accuracy(ly));
    return;
  }

  lx=lgefint(x); sh=bfffo(x[2]);
  y[1] = evalsigne(s) | evalexpo(bit_accuracy(lx)-sh-1);
  if (sh)
  {
    if (lx>ly)
    { shift_left(y,x,2,ly-1, x[ly],sh); }
    else
    {
      for (i=lx; i<ly; i++) y[i]=0;
      shift_left(y,x,2,lx-1, 0,sh);
    }
    return;
  }

  if (lx>=ly)
    for (i=2; i<ly; i++) y[i]=x[i];
  else
  {
    for (i=2; i<lx; i++) y[i]=x[i];
    for (   ; i<ly; i++) y[i]=0;
  }
}

void
affrr(GEN x, GEN y)
{
  long lx,ly,i;

  y[1] = x[1]; if (!signe(x)) return;

  lx=lg(x); ly=lg(y);
  if (lx>=ly)
    for (i=2; i<ly; i++) y[i]=x[i];
  else
  {
    for (i=2; i<lx; i++) y[i]=x[i];
    for (   ; i<ly; i++) y[i]=0;
  }
}

GEN
shifti(GEN x, long n)
{
  return shifti3(x, n, 0);
}

GEN
shifti3(GEN x, long n, long flag)
{
  const long s=signe(x);
  long lx,ly,i,m;
  GEN y;

  if (!s) return gzero;
  if (!n) return icopy(x);
  lx = lgefint(x);
  if (n > 0)
  {
    GEN z = (GEN)avma;
    long d = n>>TWOPOTBITS_IN_LONG;

    ly = lx+d; y = new_chunk(ly);
    for ( ; d; d--) *--z = 0;
    m = n & (BITS_IN_LONG-1);
    if (!m) for (i=2; i<lx; i++) y[i]=x[i];
    else
    {
      register const ulong sh = BITS_IN_LONG - m;
      shift_left2(y,x, 2,lx-1, 0,m,sh);
      i = ((ulong)x[2]) >> sh;
      if (i) { ly++; y = new_chunk(1); y[2] = i; }
    }
  }
  else
  {
    long lyorig;

    n = -n;
    ly = lyorig = lx - (n>>TWOPOTBITS_IN_LONG);
    if (ly<3)
	return flag ? stoi(-1) : gzero;
    y = new_chunk(ly);
    m = n & (BITS_IN_LONG-1);
    if (m) {
      shift_right(y,x, 2,ly, 0,m);
      if (y[2] == 0)
      {
        if (ly==3) { avma = (ulong)(y+3); return flag ? stoi(-1) : gzero; }
        ly--; avma = (ulong)(++y);
      }
    } else {
      for (i=2; i<ly; i++) y[i]=x[i]; 
    }
    /* With FLAG: round up instead of rounding down */
    if (flag) {				/* Check low bits of x */
      i = lx; flag = 0;
      while (--i >= lyorig)
	if (x[i]) { flag = 1; break; }  /* Need to increment y by 1 */
      if (!flag && m)
	flag = x[lyorig - 1] & ((1<<m) - 1);
    }
    if (flag) {				/* Increment y */
      for (i = ly;;)
      {
	if (--i < 2)
        { /* Extend y on the left */
	  if (avma <= bot) err(errpile);
	  avma = (ulong)(--y); ly++;
	  y[2] = 1; break;
	}
	if (++y[i]) break;
	/* Now propagate the bit into the next longword */
      }
    }
  }
  y[1] = evalsigne(s)|evallgefint(ly);
  y[0] = evaltyp(t_INT)|evallg(ly); return y;
}

GEN
mptrunc(GEN x)
{
  long d,e,i,s,m;
  GEN y;

  if (typ(x)==t_INT) return icopy(x);
  if ((s=signe(x)) == 0 || (e=expo(x)) < 0) return gzero;
  d = (e>>TWOPOTBITS_IN_LONG) + 3;
  m = e & (BITS_IN_LONG-1);
  if (d > lg(x)) err(precer, "mptrunc (precision loss in truncation)");

  y=cgeti(d); y[1] = evalsigne(s) | evallgefint(d);
  if (++m == BITS_IN_LONG)
    for (i=2; i<d; i++) y[i]=x[i];
  else
  {
    register const ulong sh = BITS_IN_LONG - m;
    shift_right2(y,x, 2,d,0, sh,m);
  }
  return y;
}

/* integral part */
GEN
mpent(GEN x)
{
  long d,e,i,lx,m;
  GEN y;

  if (typ(x)==t_INT) return icopy(x);
  if (signe(x) >= 0) return mptrunc(x);
  if ((e=expo(x)) < 0) return stoi(-1);
  d = (e>>TWOPOTBITS_IN_LONG) + 3;
  m = e & (BITS_IN_LONG-1);
  lx=lg(x); if (d>lx) err(precer, "mpent (precision loss in trucation)");
  y = new_chunk(d);
  if (++m == BITS_IN_LONG)
  {
    for (i=2; i<d; i++) y[i]=x[i];
    i=d; while (i<lx && !x[i]) i++;
    if (i==lx) goto END;
  }
  else
  {
    register const ulong sh = BITS_IN_LONG - m;
    shift_right2(y,x, 2,d,0, sh,m);
    if (x[d-1]<<m == 0)
    {
      i=d; while (i<lx && !x[i]) i++;
      if (i==lx) goto END;
    }
  }
  /* set y:=y+1 */
  for (i=d-1; i>=2; i--) { y[i]++; if (y[i]) goto END; }
  y=new_chunk(1); y[2]=1; d++;
END:
  y[1] = evalsigne(-1) | evallgefint(d);
  y[0] = evaltyp(t_INT) | evallg(d); return y;
}

int
cmpsi(long x, GEN y)
{
  ulong p;

  if (!x) return -signe(y);

  if (x>0)
  {
    if (signe(y)<=0) return 1;
    if (lgefint(y)>3) return -1;
    p=y[2]; if (p == (ulong)x) return 0;
    return p < (ulong)x ? 1 : -1;
  }

  if (signe(y)>=0) return -1;
  if (lgefint(y)>3) return 1;
  p=y[2]; if (p == (ulong)-x) return 0;
  return p < (ulong)(-x) ? -1 : 1;
}

int
cmpii(GEN x, GEN y)
{
  const long sx = signe(x), sy = signe(y);
  long lx,ly,i;

  if (sx<sy) return -1;
  if (sx>sy) return 1;
  if (!sx) return 0;

  lx=lgefint(x); ly=lgefint(y);
  if (lx>ly) return sx;
  if (lx<ly) return -sx;
  i=2; while (i<lx && x[i]==y[i]) i++;
  if (i==lx) return 0;
  return ((ulong)x[i] > (ulong)y[i]) ? sx : -sx;
}

int
cmprr(GEN x, GEN y)
{
  const long sx = signe(x), sy = signe(y);
  long ex,ey,lx,ly,lz,i;

  if (sx<sy) return -1;
  if (sx>sy) return 1;
  if (!sx) return 0;

  ex=expo(x); ey=expo(y);
  if (ex>ey) return sx;
  if (ex<ey) return -sx;

  lx=lg(x); ly=lg(y); lz = (lx<ly)?lx:ly;
  i=2; while (i<lz && x[i]==y[i]) i++;
  if (i<lz) return ((ulong)x[i] > (ulong)y[i]) ? sx : -sx;
  if (lx>=ly)
  {
    while (i<lx && !x[i]) i++;
    return (i==lx) ? 0 : sx;
  }
  while (i<ly && !y[i]) i++;
  return (i==ly) ? 0 : -sx;
}

GEN
addss(long x, long y)
{
  if (!x) return stoi(y);
  if (x>0) { pos_s[2] = x; return addsi(y,pos_s); }
  neg_s[2] = -x; return addsi(y,neg_s);
}

GEN
addsi(long x, GEN y)
{
  long sx,sy,ly;
  GEN z;

  if (!x) return icopy(y);
  sy=signe(y); if (!sy) return stoi(x);
  if (x<0) { sx=-1; x=-x; } else sx=1;
  if (sx==sy)
  {
    z = addsispec(x,y+2, lgefint(y)-2);
    setsigne(z,sy); return z;
  }
  ly=lgefint(y);
  if (ly==3)
  {
    const long d = y[2] - x;
    if (!d) return gzero;
    z=cgeti(3);
    if (y[2] < 0 || d > 0) {
      z[1] = evalsigne(sy) | evallgefint(3);
      z[2] = d;
    }
    else {
      z[1] = evalsigne(-sy) | evallgefint(3);
      z[2] =-d;
    }
    return z;
  }
  z = subisspec(y+2,x, ly-2);
  setsigne(z,sy); return z;
}

GEN
addii(GEN x, GEN y)
{
  long sx = signe(x);
  long sy = signe(y);
  long lx,ly;
  GEN z;

  if (!sx) return sy? icopy(y): gzero;
  if (!sy) return icopy(x);
  lx=lgefint(x); ly=lgefint(y);

  if (sx==sy)
    z = addiispec(x+2,y+2,lx-2,ly-2);
  else
  { /* sx != sy */
    long i = lx - ly;
    if (i==0)
    {
      i = absi_cmp(x,y);
      if (!i) return gzero;
    }
    if (i<0) { sx=sy; swapspec(x,y, lx,ly); } /* ensure |x| >= |y| */
    z = subiispec(x+2,y+2,lx-2,ly-2);
  }
  setsigne(z,sx); return z;
}

GEN
addsr(long x, GEN y)
{
  if (!x) return rcopy(y);
  if (x>0) { pos_s[2]=x; return addir(pos_s,y); }
  neg_s[2] = -x; return addir(neg_s,y);
}

GEN
addir(GEN x, GEN y)
{
  long e,l,ly;
  GEN z;

  if (!signe(x)) return rcopy(y);
  e = expo(y)-expi(x);
  if (!signe(y))
  {
#if 0
    if (e>0) err(adder3);
#else /* design issue: make 0.0 "absorbing" */
    if (e>0) return rcopy(y);
#endif
    z = cgetr(3 + ((-e)>>TWOPOTBITS_IN_LONG));
    affir(x,z); return z;
  }

  ly=lg(y);
  if (e>0)
  {
    l = ly - (e>>TWOPOTBITS_IN_LONG);
    if (l<3) return rcopy(y);
  }
  else l = ly + ((-e)>>TWOPOTBITS_IN_LONG)+1;
  z=cgetr(l); affir(x,z); y=addrr(z,y);
  z = y+l; ly = lg(y); while (ly--) z[ly] = y[ly];
  avma=(long)z; return z;
}

GEN
addrr(GEN x, GEN y)
{
  long sx=signe(x),sy=signe(y),ex=expo(x),ey=expo(y);
  long e,m,flag,i,j,f2,lx,ly,lz;
  GEN z;
  LOCAL_OVERFLOW;

  e = ey-ex;
  if (!sy)
  {
    if (!sx)
    {
      if (e > 0) ex=ey;
      return realzero_bit(ex);
    }
    if (e > 0) return realzero_bit(ey);
    lz = 3 + ((-e)>>TWOPOTBITS_IN_LONG);
    lx = lg(x); if (lz>lx) lz=lx;
    z = cgetr(lz); while(--lz) z[lz]=x[lz];
    return z;
  }
  if (!sx)
  {
    if (e < 0) return realzero_bit(ex);
    lz = 3 + (e>>TWOPOTBITS_IN_LONG);
    ly = lg(y); if (lz>ly) lz=ly;
    z = cgetr(lz); while (--lz) z[lz]=y[lz];
    return z;
  }

  if (e < 0) { z=x; x=y; y=z; ey=ex; i=sx; sx=sy; sy=i; e=-e; }
  /* now ey >= ex */
  lx=lg(x); ly=lg(y);
  if (e)
  {
    long d = e >> TWOPOTBITS_IN_LONG, l = ly-d;
    if (l > lx)     { flag=0; lz=lx+d+1; }
    else if (l > 2) { flag=1; lz=ly; lx=l; }
    else return rcopy(y);
    m = e & (BITS_IN_LONG-1);
  }
  else
  {
    if (lx > ly) lx = ly;
    flag=2; lz=lx; m=0;
  }
  z = cgetr(lz);
  if (m)
  { /* shift right x m bits */
    const ulong sh = BITS_IN_LONG-m;
    GEN p1 = x; x = new_chunk(lx+1);
    shift_right2(x,p1,2,lx, 0,m,sh);
    if (flag==0)
    {
      x[lx] = p1[lx-1] << sh;
      if (x[lx]) { flag = 3; lx++; }
    }
  }

  if (sx==sy)
  { /* addition */
    i=lz-1; avma = (long)z;
    if (flag==0) { z[i] = y[i]; i--; }
    overflow=0;
    for (j=lx-1; j>=2; i--,j--) z[i] = addllx(x[j],y[i]);

    if (overflow)
      for (;;)
      {
        if (i==1)
        {
          shift_right(z,z, 2,lz, 1,1);
          ey=evalexpo(ey+1);
          z[1] = evalsigne(sx) | ey; return z;
        }
        z[i] = y[i]+1; if (z[i--]) break;
      }
    for (; i>=2; i--) z[i]=y[i];
    z[1] = evalsigne(sx) | evalexpo(ey); return z;
  }

  /* subtraction */
  if (e) f2 = 1;
  else
  {
    i=2; while (i<lx && x[i]==y[i]) i++;
    if (i==lx)
    {
      avma = (long)(z+lz);
      return realzero_bit(ey - bit_accuracy(lx));
    }
    f2 = ((ulong)y[i] > (ulong)x[i]);
  }

  /* result is non-zero. f2 = (y > x) */
  i=lz-1;
  if (f2)
  {
    if (flag==0) { z[i] = y[i]; i--; }
    j=lx-1; z[i] = subll(y[i],x[j]); i--; j--;
    for (; j>=2; i--,j--) z[i] = subllx(y[i],x[j]);
    if (overflow)
      for (;;) { z[i] = y[i]-1; if (y[i--]) break; }
    for (; i>=2; i--) z[i]=y[i];
    sx = sy;
  }
  else
  {
    if (flag==0) { z[i] = -y[i]; i--; overflow=1; } else overflow=0;
    for (; i>=2; i--) z[i]=subllx(x[i],y[i]);
  }

  x = z+2; i=0; while (!x[i]) i++;
  lz -= i; z += i; m = bfffo(z[2]);
  e = evalexpo(ey - (m | (i<<TWOPOTBITS_IN_LONG)));
  if (m) shift_left(z,z,2,lz-1, 0,m);
  z[1] = evalsigne(sx) | e;
  z[0] = evaltyp(t_REAL) | evallg(lz);
  avma = (long)z; return z;
}

GEN
mulss(long x, long y)
{
  long s,p1;
  GEN z;
  LOCAL_HIREMAINDER;

  if (!x || !y) return gzero;
  if (x<0) { s = -1; x = -x; } else s=1;
  if (y<0) { s = -s; y = -y; }
  p1 = mulll(x,y);
  if (hiremainder)
  {
    z=cgeti(4); z[1] = evalsigne(s) | evallgefint(4);
    z[2]=hiremainder; z[3]=p1; return z;
  }
  z=cgeti(3); z[1] = evalsigne(s) | evallgefint(3);
  z[2]=p1; return z;
}
#endif

GEN
muluu(ulong x, ulong y)
{
  long p1;
  GEN z;
  LOCAL_HIREMAINDER;

  if (!x || !y) return gzero;
  p1 = mulll(x,y);
  if (hiremainder)
  {
    z=cgeti(4); z[1] = evalsigne(1) | evallgefint(4);
    z[2]=hiremainder; z[3]=p1; return z;
  }
  z=cgeti(3); z[1] = evalsigne(1) | evallgefint(3);
  z[2]=p1; return z;
}

/* assume ny > 0 */
#ifdef INLINE
INLINE
#endif
GEN
mulsispec(long x, GEN y, long ny)
{
  GEN yd, z = (GEN)avma;
  long lz = ny+3;
  LOCAL_HIREMAINDER;

  (void)new_chunk(lz);
  yd = y + ny; *--z = mulll(x, *--yd);
  while (yd > y) *--z = addmul(x,*--yd);
  if (hiremainder) *--z = hiremainder; else lz--;
  *--z = evalsigne(1) | evallgefint(lz);
  *--z = evaltyp(t_INT) | evallg(lz);
  avma=(long)z; return z;
}

GEN
mului(ulong x, GEN y)
{
  long s = signe(y);
  GEN z;

  if (!s || !x) return gzero;
  z = mulsispec(x, y+2, lgefint(y)-2);
  setsigne(z,s); return z;
}

/* a + b*Y, assume Y >= 0, 0 <= a,b <= VERYBIGINT */
GEN
addsmulsi(long a, long b, GEN Y)
{
  GEN yd,y,z;
  long ny,lz;
  LOCAL_HIREMAINDER;
  LOCAL_OVERFLOW;

  if (!signe(Y)) return stoi(a);

  y = Y+2; z = (GEN)avma;
  ny = lgefint(Y)-2;
  lz = ny+3;

  (void)new_chunk(lz);
  yd = y + ny; *--z = addll(a, mulll(b, *--yd));
  if (overflow) hiremainder++; /* can't overflow */
  while (yd > y) *--z = addmul(b,*--yd);
  if (hiremainder) *--z = hiremainder; else lz--;
  *--z = evalsigne(1) | evallgefint(lz);
  *--z = evaltyp(t_INT) | evallg(lz);
  avma=(long)z; return z;
}

#ifndef __M68K__

GEN
mulsi(long x, GEN y)
{
  long s = signe(y);
  GEN z;

  if (!s || !x) return gzero;
  if (x<0) { s = -s; x = -x; }
  z = mulsispec(x, y+2, lgefint(y)-2);
  setsigne(z,s); return z;
}

GEN
mulsr(long x, GEN y)
{
  long lx,i,s,garde,e,sh,m;
  GEN z;
  LOCAL_HIREMAINDER;

  if (!x) return gzero;
  s = signe(y);
  if (!s)
  {
    if (x<0) x = -x;
    e = expo(y) + (BITS_IN_LONG-1)-bfffo(x);
    return realzero_bit(e);
  }
  if (x<0) { s = -s; x = -x; }
  if (x==1) { z=rcopy(y); setsigne(z,s); return z; }

  lx = lg(y); e = expo(y);
  z=cgetr(lx); y--; garde=mulll(x,y[lx]);
  for (i=lx-1; i>=3; i--) z[i]=addmul(x,y[i]);
  z[2]=hiremainder;

  sh = bfffo(hiremainder); m = BITS_IN_LONG-sh;
  if (sh) shift_left2(z,z, 2,lx-1, garde,sh,m);
  z[1] = evalsigne(s) | evalexpo(m+e); return z;
}

GEN
mulrr(GEN x, GEN y)
{
  long sx = signe(x), sy = signe(y);
  long i,j,ly,lz,lzz,e,flag,p1;
  ulong garde;
  GEN z, y1;
  LOCAL_HIREMAINDER;
  LOCAL_OVERFLOW;

  e = expo(x)+expo(y);
  if (!sx || !sy) return realzero_bit(e);
  if (sy<0) sx = -sx;
  lz=lg(x); ly=lg(y);
  if (lz>ly) { lz=ly; z=x; x=y; y=z; flag=1; } else flag = (lz!=ly);
  z=cgetr(lz); z[1] = evalsigne(sx) | evalexpo(e);
  if (lz==3)
  {
    if (flag)
    {
      (void)mulll(x[2],y[3]);
      garde = addmul(x[2],y[2]);
    }
    else
      garde = mulll(x[2],y[2]);
    if ((long)hiremainder<0) { z[2]=hiremainder; z[1]++; }
    else z[2]=(hiremainder<<1) | (garde>>(BITS_IN_LONG-1));
    return z;
  }

  if (flag) { (void)mulll(x[2],y[lz]); garde = hiremainder; } else garde=0;
  lzz=lz-1; p1=x[lzz];
  if (p1)
  {
    (void)mulll(p1,y[3]);
    garde = addll(addmul(p1,y[2]), garde);
    z[lzz] = overflow+hiremainder;
  }
  else z[lzz]=0;
  for (j=lz-2, y1=y-j; j>=3; j--)
  {
    p1 = x[j]; y1++;
    if (p1)
    {
      (void)mulll(p1,y1[lz+1]);
      garde = addll(addmul(p1,y1[lz]), garde);
      for (i=lzz; i>j; i--)
      {
        hiremainder += overflow;
	z[i] = addll(addmul(p1,y1[i]), z[i]);
      }
      z[j] = hiremainder+overflow;
    }
    else z[j]=0;
  }
  p1=x[2]; y1++;
  garde = addll(mulll(p1,y1[lz]), garde);
  for (i=lzz; i>2; i--)
  {
    hiremainder += overflow;
    z[i] = addll(addmul(p1,y1[i]), z[i]);
  }
  z[2] = hiremainder+overflow;
  if (z[2] < 0) z[1]++;
  else
    shift_left(z,z,2,lzz,garde, 1);
  return z;
}

GEN
mulir(GEN x, GEN y)
{
  long sx=signe(x),sy,lz,lzz,ey,e,p1,i,j;
  ulong garde;
  GEN z,y1;
  LOCAL_HIREMAINDER;
  LOCAL_OVERFLOW;

  if (!sx) return gzero;
  if (!is_bigint(x)) return mulsr(itos(x),y);
  sy=signe(y); ey=expo(y);
  if (!sy) return realzero_bit(expi(x)+ey);

  if (sy<0) sx = -sx;
  lz=lg(y); z=cgetr(lz);
  y1=cgetr(lz+1);
  affir(x,y1); x=y; y=y1;
  e = evalexpo(expo(y)+ey);
  z[1] = evalsigne(sx) | e;
  if (lz==3)
  {
    (void)mulll(x[2],y[3]);
    garde=addmul(x[2],y[2]);
    if ((long)hiremainder < 0) { z[2]=hiremainder; z[1]++; }
    else z[2]=(hiremainder<<1) | (garde>>(BITS_IN_LONG-1));
    avma=(long)z; return z;
  }

  (void)mulll(x[2],y[lz]); garde=hiremainder;
  lzz=lz-1; p1=x[lzz];
  if (p1)
  {
    (void)mulll(p1,y[3]);
    garde=addll(addmul(p1,y[2]),garde);
    z[lzz] = overflow+hiremainder;
  }
  else z[lzz]=0;
  for (j=lz-2, y1=y-j; j>=3; j--)
  {
    p1=x[j]; y1++;
    if (p1)
    {
      (void)mulll(p1,y1[lz+1]);
      garde = addll(addmul(p1,y1[lz]), garde);
      for (i=lzz; i>j; i--)
      {
        hiremainder += overflow;
        z[i] = addll(addmul(p1,y1[i]), z[i]);
      }
      z[j] = hiremainder+overflow;
    }
    else z[j]=0;
  }
  p1=x[2]; y1++;
  garde = addll(mulll(p1,y1[lz]), garde);
  for (i=lzz; i>2; i--)
  {
    hiremainder += overflow;
    z[i] = addll(addmul(p1,y1[i]), z[i]);
  }
  z[2] = hiremainder+overflow;
  if (z[2] < 0) z[1]++;
  else
    shift_left(z,z,2,lzz,garde, 1);
  avma=(long)z; return z;
}

/* written by Bruno Haible following an idea of Robert Harley */
long
vals(ulong z)
{
  static char tab[64]={-1,0,1,12,2,6,-1,13,3,-1,7,-1,-1,-1,-1,14,10,4,-1,-1,8,-1,-1,25,-1,-1,-1,-1,-1,21,27,15,31,11,5,-1,-1,-1,-1,-1,9,-1,-1,24,-1,-1,20,26,30,-1,-1,-1,-1,23,-1,19,29,-1,22,18,28,17,16,-1};
#ifdef LONG_IS_64BIT
  long s;
#endif

  if (!z) return -1;
#ifdef LONG_IS_64BIT
  if (! (z&0xffffffff)) { s = 32; z >>=32; } else s = 0;
#endif
  z |= ~z + 1;
  z += z << 4;
  z += z << 6;
  z ^= z << 16; /* or  z -= z<<16 */
#ifdef LONG_IS_64BIT
  return s + tab[(z&0xffffffff)>>26];
#else
  return tab[z>>26];
#endif
}

GEN
modss(long x, long y)
{
  LOCAL_HIREMAINDER;

  if (!y) err(moder1);
  if (y<0) y=-y;
  hiremainder=0; divll(labs(x),y);
  if (!hiremainder) return gzero;
  return (x < 0) ? stoi(y-hiremainder) : stoi(hiremainder);
}

GEN
resss(long x, long y)
{
  LOCAL_HIREMAINDER;

  if (!y) err(reser1);
  hiremainder=0; divll(labs(x),labs(y));
  return (x < 0) ? stoi(-((long)hiremainder)) : stoi(hiremainder);
}

GEN
divsi(long x, GEN y)
{
  long p1, s = signe(y);
  LOCAL_HIREMAINDER;

  if (!s) err(diver2);
  if (!x || lgefint(y)>3 || ((long)y[2])<0)
  {
    hiremainder=x; SAVE_HIREMAINDER; return gzero;
  }
  hiremainder=0; p1=divll(labs(x),y[2]);
  if (x<0) { hiremainder = -((long)hiremainder); p1 = -p1; }
  if (s<0) p1 = -p1;
  SAVE_HIREMAINDER; return stoi(p1);
}
#endif

GEN
modui(ulong x, GEN y)
{
  LOCAL_HIREMAINDER;

  if (!signe(y)) err(diver2);
  if (!x || lgefint(y)>3) hiremainder=x;
  else
  {
    hiremainder=0; (void)divll(x,y[2]);
  }
  return utoi(hiremainder);
}

ulong
umodiu(GEN y, ulong x)
{
  long sy=signe(y),ly,i;
  LOCAL_HIREMAINDER;

  if (!x) err(diver4);
  if (!sy) return 0;
  ly = lgefint(y);
  if (x <= (ulong)y[2]) hiremainder=0;
  else
  {
    if (ly==3) return (sy > 0)? (ulong)y[2]: x - (ulong)y[2];
    hiremainder=y[2]; ly--; y++;
  }
  for (i=2; i<ly; i++) (void)divll(y[i],x);
  if (!hiremainder) return 0;
  return (sy > 0)? hiremainder: x - hiremainder;
}

GEN
modiu(GEN y, ulong x) { return utoi(umodiu(y,x)); }

#ifndef __M68K__

GEN
modsi(long x, GEN y)
{
  long s = signe(y);
  GEN p1;
  LOCAL_HIREMAINDER;

  if (!s) err(diver2);
  if (!x || lgefint(y)>3 || ((long)y[2])<0) hiremainder=x;
  else
  {
    hiremainder=0; (void)divll(labs(x),y[2]);
    if (x<0) hiremainder = -((long)hiremainder);
  }
  if (!hiremainder) return gzero;
  if (x>0) return stoi(hiremainder);
  if (s<0)
    { setsigne(y,1); p1=addsi(hiremainder,y); setsigne(y,-1); }
  else
    p1=addsi(hiremainder,y);
  return p1;
}

GEN
divis(GEN y, long x)
{
  long sy=signe(y),ly,s,i;
  GEN z;
  LOCAL_HIREMAINDER;

  if (!x) err(diver4);
  if (!sy) { hiremainder=0; SAVE_HIREMAINDER; return gzero; }
  if (x<0) { s = -sy; x = -x; } else s=sy;

  ly = lgefint(y);
  if ((ulong)x <= (ulong)y[2]) hiremainder=0;
  else
  {
    if (ly==3) { hiremainder=itos(y); SAVE_HIREMAINDER; return gzero; }
    hiremainder=y[2]; ly--; y++;
  }
  z = cgeti(ly); z[1] = evallgefint(ly) | evalsigne(s);
  for (i=2; i<ly; i++) z[i]=divll(y[i],x);
  if (sy<0) hiremainder = - ((long)hiremainder);
  SAVE_HIREMAINDER; return z;
}

GEN
divir(GEN x, GEN y)
{
  GEN xr,z;
  long av,ly;

  if (!signe(y)) err(diver5);
  if (!signe(x)) return gzero;
  ly=lg(y); z=cgetr(ly); av=avma; xr=cgetr(ly+1); affir(x,xr);
  affrr(divrr(xr,y),z); avma=av; return z;
}

GEN
divri(GEN x, GEN y)
{
  GEN yr,z;
  long av,lx,s=signe(y);

  if (!s) err(diver8);
  if (!signe(x)) return realzero_bit(expo(x) - expi(y));
  if (!is_bigint(y)) return divrs(x, s>0? y[2]: -y[2]);

  lx=lg(x); z=cgetr(lx);
  av=avma; yr=cgetr(lx+1); affir(y,yr);
  affrr(divrr(x,yr),z); avma=av; return z;
}

void
diviiz(GEN x, GEN y, GEN z)
{
  long av=avma,lz;
  GEN xr,yr;

  if (typ(z)==t_INT) { affii(divii(x,y),z); avma=av; return; }
  lz=lg(z); xr=cgetr(lz); affir(x,xr); yr=cgetr(lz); affir(y,yr);
  affrr(divrr(xr,yr),z); avma=av;
}

void
mpdivz(GEN x, GEN y, GEN z)
{
  long av=avma;

  if (typ(z)==t_INT)
  {
    if (typ(x)==t_REAL || typ(y)==t_REAL) err(divzer1);
    affii(divii(x,y),z); avma=av; return;
  }
  if (typ(x)==t_INT)
  {
    GEN xr,yr;
    long lz;

    if (typ(y)==t_REAL) { affrr(divir(x,y),z); avma=av; return; }
    lz=lg(z); xr=cgetr(lz); affir(x,xr); yr=cgetr(lz); affir(y,yr);
    affrr(divrr(xr,yr),z); avma=av; return;
  }
  if (typ(y)==t_REAL) { affrr(divrr(x,y),z); avma=av; return; }
  affrr(divri(x,y),z); avma=av;
}

GEN
divsr(long x, GEN y)
{
  long av,ly;
  GEN p1,z;

  if (!signe(y)) err(diver3);
  if (!x) return gzero;
  ly=lg(y); z=cgetr(ly); av=avma;
  p1=cgetr(ly+1); affsr(x,p1); affrr(divrr(p1,y),z);
  avma=av; return z;
}

GEN
modii(GEN x, GEN y)
{
  switch(signe(x))
  {
    case 0: return gzero;
    case 1: return resii(x,y);
    default:
    {
      long av = avma;
      (void)new_chunk(lgefint(y));
      x = resii(x,y); avma=av;
      if (x==gzero) return x;
      return subiispec(y+2,x+2,lgefint(y)-2,lgefint(x)-2);
    }
  }
}

void
modiiz(GEN x, GEN y, GEN z)
{
  const long av = avma;
  affii(modii(x,y),z); avma=av;
}

GEN
divrs(GEN x, long y)
{
  long i,lx,ex,garde,sh,s=signe(x);
  GEN z;
  LOCAL_HIREMAINDER;

  if (!y) err(diver6);
  if (!s) return realzero_bit(expo(x) - (BITS_IN_LONG-1)+bfffo(y));
  if (y<0) { s = -s; y = -y; }
  if (y==1) { z=rcopy(x); setsigne(z,s); return z; }

  z=cgetr(lx=lg(x)); hiremainder=0;
  for (i=2; i<lx; i++) z[i]=divll(x[i],y);

  /* we may have hiremainder != 0 ==> garde */
  garde=divll(0,y); sh=bfffo(z[2]); ex=evalexpo(expo(x)-sh);
  if (sh) shift_left(z,z, 2,lx-1, garde,sh);
  z[1] = evalsigne(s) | ex;
  return z;
}

GEN
divrr(GEN x, GEN y)
{
  long sx=signe(x), sy=signe(y), lx,ly,lz,e,i,j;
  ulong si,saux;
  GEN z,x1;

  if (!sy) err(diver9);
  e = expo(x) - expo(y);
  if (!sx) return realzero_bit(e);
  if (sy<0) sx = -sx;
  lx=lg(x); ly=lg(y);
  if (ly==3)
  {
    ulong k = x[2], l = (lx>3)? x[3]: 0;
    LOCAL_HIREMAINDER;
    if (k < (ulong)y[2]) e--;
    else
    {
      l >>= 1; if (k&1) l |= HIGHBIT;
      k >>= 1;
    }
    z = cgetr(3); z[1] = evalsigne(sx) | evalexpo(e);
    hiremainder=k; z[2]=divll(l,y[2]); return z;
  }

  lz = min(lx,ly); z = new_chunk(lz);
  x1 = z-1;
  x1[1]=0; for (i=2; i<lz; i++) x1[i]=x[i];
  x1[lz] = (lx>lz)? x[lz]: 0;
  x=z; si=y[2]; saux=y[3];
  for (i=0; i<lz-1; i++)
  { /* x1 = x + (i-1) */
    ulong k,qp;
    LOCAL_HIREMAINDER;
    LOCAL_OVERFLOW;
    if ((ulong)x1[1] == si)
    {
      qp = MAXULONG; k=addll(si,x1[2]);
    }
    else
    {
      if ((ulong)x1[1] > si) /* can't happen if i=0 */
      {
        GEN y1 = y+1;
	overflow=0;
	for (j=lz-i; j>0; j--) x1[j] = subllx(x1[j],y1[j]);
	j=i; do x[--j]++; while (j && !x[j]);
      }
      hiremainder=x1[1]; overflow=0;
      qp=divll(x1[2],si); k=hiremainder;
    }
    if (!overflow)
    {
      long k3 = subll(mulll(qp,saux), x1[3]);
      long k4 = subllx(hiremainder,k);
      while (!overflow && k4) { qp--; k3=subll(k3,saux); k4=subllx(k4,si); }
    }
    j = lz-i+1;
    if (j<ly) (void)mulll(qp,y[j]); else { hiremainder=0 ; j=ly; }
    for (j--; j>1; j--)
    {
      x1[j] = subll(x1[j], addmul(qp,y[j]));
      hiremainder += overflow;
    }
    if ((ulong)x1[1] != hiremainder)
    {
      if ((ulong)x1[1] < hiremainder)
      {
        qp--;
        overflow=0; for (j=lz-i; j>1; j--) x1[j]=addllx(x1[j], y[j]);
      }
      else
      {
	x1[1] -= hiremainder;
	while (x1[1])
	{
	  qp++; if (!qp) { j=i; do x[--j]++; while (j && !x[j]); }
          overflow=0; for (j=lz-i; j>1; j--) x1[j]=subllx(x1[j],y[j]);
	  x1[1] -= overflow;
	}
      }
    }
    x1[1]=qp; x1++;
  }
  x1 = x-1; for (j=lz-1; j>=2; j--) x[j]=x1[j];
  if (*x) { shift_right(x,x, 2,lz, 1,1); } else e--;
  x[0] = evaltyp(t_REAL)|evallg(lz);
  x[1] = evalsigne(sx) | evalexpo(e);
  return x;
}
#endif /* !defined(__M68K__) */

/* The following ones are not in mp.s (mulii is, with a different algorithm) */

/* Integer division x / y: such that sign(r) = sign(x)
 *   if z = ONLY_REM return remainder, otherwise return quotient
 *   if z != NULL set *z to remainder
 *   *z is the last object on stack (and thus can be disposed of with cgiv
 *   instead of gerepile)
 * If *z is zero, we put gzero here and no copy.
 * space needed: lx + ly
 */
GEN
dvmdii(GEN x, GEN y, GEN *z)
{
  long sx=signe(x),sy=signe(y);
  long av,lx,ly,lz,i,j,sh,k,lq,lr;
  ulong si,qp,saux, *xd,*rd,*qd;
  GEN r,q,x1;

  if (!sy) err(dvmer1);
  if (!sx)
  {
    if (!z || z == ONLY_REM) return gzero;
    *z=gzero; return gzero;
  }
  lx=lgefint(x);
  ly=lgefint(y); lz=lx-ly;
  if (lz <= 0)
  {
    if (lz == 0)
    {
      for (i=2; i<lx; i++)
        if (x[i] != y[i])
        {
          if ((ulong)x[i] > (ulong)y[i]) goto DIVIDE;
          goto TRIVIAL;
        }
      if (z == ONLY_REM) return gzero;
      if (z) *z = gzero;
      if (sx < 0) sy = -sy;
      return stoi(sy);
    }
TRIVIAL:
    if (z == ONLY_REM) return icopy(x);
    if (z) *z = icopy(x);
    return gzero;
  }
DIVIDE: /* quotient is non-zero */
  av=avma; if (sx<0) sy = -sy;
  if (ly==3)
  {
    LOCAL_HIREMAINDER;
    si = y[2];
    if (si <= (ulong)x[2]) hiremainder=0;
    else
    {
      hiremainder = x[2]; lx--; x++;
    }
    q = new_chunk(lx); for (i=2; i<lx; i++) q[i]=divll(x[i],si);
    if (z == ONLY_REM)
    {
      avma=av; if (!hiremainder) return gzero;
      r=cgeti(3);
      r[1] = evalsigne(sx) | evallgefint(3);
      r[2]=hiremainder; return r;
    }
    q[1] = evalsigne(sy) | evallgefint(lx);
    q[0] = evaltyp(t_INT) | evallg(lx);
    if (!z) return q;
    if (!hiremainder) { *z=gzero; return q; }
    r=cgeti(3);
    r[1] = evalsigne(sx) | evallgefint(3);
    r[2] = hiremainder; *z=r; return q;
  }

  x1 = new_chunk(lx); sh = bfffo(y[2]);
  if (sh)
  { /* normalize so that highbit(y) = 1 (shift left x and y by sh bits)*/
    register const ulong m = BITS_IN_LONG - sh;
    r = new_chunk(ly);
    shift_left2(r, y,2,ly-1, 0,sh,m); y = r;
    shift_left2(x1,x,2,lx-1, 0,sh,m);
    x1[1] = ((ulong)x[2]) >> m;
  }
  else
  {
    x1[1]=0; for (j=2; j<lx; j++) x1[j]=x[j];
  }
  x=x1; si=y[2]; saux=y[3];
  for (i=0; i<=lz; i++)
  { /* x1 = x + i */
    LOCAL_HIREMAINDER;
    LOCAL_OVERFLOW;
    if ((ulong)x1[1] == si)
    {
      qp = MAXULONG; k=addll(si,x1[2]);
    }
    else
    {
      hiremainder=x1[1]; overflow=0;
      qp=divll(x1[2],si); k=hiremainder;
    }
    if (!overflow)
    {
      long k3 = subll(mulll(qp,saux), x1[3]);
      long k4 = subllx(hiremainder,k);
      while (!overflow && k4) { qp--; k3=subll(k3,saux); k4=subllx(k4,si); }
    }
    hiremainder=0;
    for (j=ly-1; j>1; j--)
    {
      x1[j] = subll(x1[j], addmul(qp,y[j]));
      hiremainder+=overflow;
    }
    if ((ulong)x1[1] < hiremainder)
    {
      overflow=0; qp--;
      for (j=ly-1; j>1; j--) x1[j] = addllx(x1[j],y[j]);
    }
    x1[1]=qp; x1++;
  }

  lq = lz+2;
  if (!z)
  {
    qd = (ulong*)av;
    xd = (ulong*)(x + lq);
    if (x[1]) { lz++; lq++; }
    while (lz--) *--qd = *--xd;
    *--qd = evalsigne(sy) | evallgefint(lq);
    *--qd = evaltyp(t_INT) | evallg(lq);
    avma = (long)qd; return (GEN)qd;
  }

  j=lq; while (j<lx && !x[j]) j++;
  lz = lx-j;
  if (z == ONLY_REM)
  {
    if (lz==0) { avma = av; return gzero; }
    rd = (ulong*)av; lr = lz+2;
    xd = (ulong*)(x + lx);
    if (!sh) while (lz--) *--rd = *--xd;
    else
    { /* shift remainder right by sh bits */
      const ulong shl = BITS_IN_LONG - sh;
      ulong l;
      xd--;
      while (--lz) /* fill r[3..] */
      {
        l = *xd >> sh;
        *--rd = l | (*--xd << shl);
      }
      l = *xd >> sh;
      if (l) *--rd = l; else lr--;
    }
    *--rd = evalsigne(sx) | evallgefint(lr);
    *--rd = evaltyp(t_INT) | evallg(lr);
    avma = (long)rd; return (GEN)rd;
  }

  lr = lz+2;
  rd = NULL; /* gcc -Wall */
  if (lz)
  { /* non zero remainder: initialize rd */
    xd = (ulong*)(x + lx);
    if (!sh)
    {
      rd = (ulong*)avma; (void)new_chunk(lr);
      while (lz--) *--rd = *--xd;
    }
    else
    { /* shift remainder right by sh bits */
      const ulong shl = BITS_IN_LONG - sh;
      ulong l;
      rd = (ulong*)x; /* overwrite shifted y */
      xd--;
      while (--lz)
      {
        l = *xd >> sh;
        *--rd = l | (*--xd << shl);
      }
      l = *xd >> sh;
      if (l) *--rd = l; else lr--;
    }
    *--rd = evalsigne(sx) | evallgefint(lr);
    *--rd = evaltyp(t_INT) | evallg(lr);
    rd += lr;
  }
  qd = (ulong*)av;
  xd = (ulong*)(x + lq);
  if (x[1]) lq++;
  j = lq-2; while (j--) *--qd = *--xd;
  *--qd = evalsigne(sy) | evallgefint(lq);
  *--qd = evaltyp(t_INT) | evallg(lq);
  q = (GEN)qd;
  if (lr==2) *z = gzero;
  else
  { /* rd has been properly initialized: we had lz > 0 */
    while (lr--) *--qd = *--rd;
    *z = (GEN)qd;
  }
  avma = (long)qd; return q;
}

/* assume y > x > 0. return y mod x */
ulong
mppgcd_resiu(GEN y, ulong x)
{
  long i, ly = lgefint(y);
  LOCAL_HIREMAINDER;

  hiremainder = 0;
  for (i=2; i<ly; i++) (void)divll(y[i],x);
  return hiremainder;
}

/* Assume x>y>0, both of them odd. return x-y if x=y mod 4, x+y otherwise */
void
mppgcd_plus_minus(GEN x, GEN y, GEN res)
{
  long av = avma;
  long lx = lgefint(x)-1;
  long ly = lgefint(y)-1, lt,m,i;
  GEN t;

  if ((x[lx]^y[ly]) & 3) /* x != y mod 4*/
    t = addiispec(x+2,y+2,lx-1,ly-1);
  else
    t = subiispec(x+2,y+2,lx-1,ly-1);

  lt = lgefint(t)-1; while (!t[lt]) lt--;
  m = vals(t[lt]); lt++;
  if (m == 0) /* 2^32 | t */
  {
    for (i = 2; i < lt; i++) res[i] = t[i];
  }
  else if (t[2] >> m)
  {
    shift_right(res,t, 2,lt, 0,m);
  }
  else
  {
    lt--; t++;
    shift_right(res,t, 2,lt, t[1],m);
  }
  res[1] = evalsigne(1)|evallgefint(lt);
  avma = av;
}

/* private version of mulss */
ulong
smulss(ulong x, ulong y, ulong *rem)
{
  LOCAL_HIREMAINDER;
  x=mulll(x,y); *rem=hiremainder; return x;
}

#ifdef LONG_IS_64BIT
#  define DIVCONVI 7
#else
#  define DIVCONVI 14
#endif

/* convert integer --> base 10^9 [assume x > 0] */
GEN
convi(GEN x)
{
  ulong av=avma, lim;
  long lz;
  GEN z,p1;

  lz = 3 + ((lgefint(x)-2)*15)/DIVCONVI;
  z=new_chunk(lz); z[1] = -1; p1 = z+2;
  lim = stack_lim(av,1);
  for(;;)
  {
    x = divis(x,1000000000); *p1++ = hiremainder;
    if (!signe(x)) { avma=av; return p1; }
    if (low_stack(lim, stack_lim(av,1))) x = gerepileuptoint((long)z,x);
  }
}
#undef DIVCONVI

/* convert fractional part --> base 10^9 [assume expo(x) < 0] */
GEN
confrac(GEN x)
{
  long lx=lg(x), ex = -expo(x)-1, d,m,ly,ey,lr,i,j;
  GEN y,y1;

  ey = ex + bit_accuracy(lx);
  ly = 1 + ((ey-1) >> TWOPOTBITS_IN_LONG);
  d = ex >> TWOPOTBITS_IN_LONG;
  m = ex & (BITS_IN_LONG-1);
  y = new_chunk(ly); y1 = y + (d-2);
  while (d--) y[d]=0;
  if (!m)
    for (i=2; i<lx; i++) y1[i] = x[i];
  else
  { /* shift x left sh bits */
    const ulong sh=BITS_IN_LONG-m;
    ulong k=0, l;
    for (i=2; i<lx; i++)
    {
      l = x[i];
      y1[i] = (l>>m)|k;
      k = l<<sh;
    }
    y1[i] = k;
  }
  lr = 1 + ((long) (ey*L2SL10))/9;
  y1 = new_chunk(lr);
  for (j=0; j<lr; j++)
  {
    LOCAL_HIREMAINDER;
    hiremainder=0;
    for (i=ly-1; i>=0; i--) y[i]=addmul(y[i],1000000000);
    y1[j]=hiremainder;
  }
  return y1;
}

GEN
truedvmdii(GEN x, GEN y, GEN *z)
{
  long av = avma;
  GEN r, q = dvmdii(x,y,&r); /* assume that r is last on stack */
  GEN *gptr[2];

  if (signe(r)>=0)
  {
    if (z == ONLY_REM) return gerepileuptoint(av,r);
    if (z) *z = r; else cgiv(r);
    return q;
  }

  if (z == ONLY_REM)
  { /* r += sign(y) * y, that is |y| */
    r = subiispec(y+2,r+2, lgefint(y)-2,lgefint(r)-2);
    return gerepileuptoint(av, r);
  }
  q = addsi(-signe(y),q);
  if (!z) return gerepileuptoint(av, q);

  *z = subiispec(y+2,r+2, lgefint(y)-2,lgefint(r)-2);
  gptr[0]=&q; gptr[1]=z; gerepilemanysp(av,(long)r,gptr,2);
  return q;
}

/* EXACT INTEGER DIVISION */

/* Find c such that 1=c*b mod 2^BITS_IN_LONG, assuming b odd (unchecked) */
static ulong
invrev(ulong b)
{
  ulong x;
  switch(b & 7)
  {
    case 3:
    case 5:  x = b+8; break;
    default: x = b; break;
  } /* x = b^(-1) mod 2^4 */
  x = x*(2-b*x);
  x = x*(2-b*x);
  x = x*(2-b*x); /* b^(-1) mod 2^32 (Newton applied to 1/x - b = 0) */
#ifdef LONG_IS_64BIT
  x = x*(2-b*x); /* b^(-1) mod 2^64 */
#endif
  return x;
}

/* assume xy>0, y odd */
GEN 
diviuexact(GEN x, ulong y)
{
  long i,lz,lx;
  ulong q, yinv;
  GEN z, z0, x0, x0min;

  if (y == 1) return icopy(x);
  lx = lgefint(x);
  if (lx == 3) return stoi((ulong)x[2] / y);
  yinv = invrev(y);
  lz = (y <= (ulong)x[2]) ? lx : lx-1;
  z = new_chunk(lz);
  z0 = z + lz;
  x0 = x + lx; x0min = x + lx-lz+2;

  while (x0 > x0min)
  {
    *--z0 = q = yinv*((ulong)*--x0); /* i-th quotient */
    if (!q) continue;
    /* x := x - q * y */
    { /* update neither lowest word (could set it to 0) nor highest ones */
      register GEN x1 = x0 - 1;
      LOCAL_HIREMAINDER;
      (void)mulll(q,y);
      if (hiremainder)
      {
        if ((ulong)*x1 < hiremainder)
        {
          *x1 -= hiremainder;
          do (*--x1)--; while ((ulong)*x1 == MAXULONG);
        }
        else
          *x1 -= hiremainder;
      }
    }
  }
  i=2; while(!z[i]) i++;
  z += i-2; lz -= i-2;
  z[0] = evaltyp(t_INT)|evallg(lz);
  z[1] = evalsigne(1)|evallg(lz);
  avma = (ulong)z; return z;
}

/* Find z such that x=y*z, knowing that y | x (unchecked)
 * Method: y0 z0 = x0 mod B = 2^BITS_IN_LONG ==> z0 = 1/y0 mod B.
 *    Set x := (x - z0 y) / B, updating only relevant words, and repeat */
GEN
diviiexact(GEN x, GEN y)
{
  long av,lx,ly,lz,vy,i,ii,sx = signe(x), sy = signe(y);
  ulong y0inv,q;
  GEN z;

  if (!sy) err(dvmer1);
  if (!sx) return gzero;
  vy = vali(y); av = avma;
  (void)new_chunk(lgefint(x)); /* enough room for z */
  if (vy)
  { /* make y odd */
#if 0
    if (vali(x) < vy) err(talker,"impossible division in diviiexact");
#endif
    y = shifti(y,-vy);
    x = shifti(x,-vy);
  }
  else x = icopy(x); /* necessary because we destroy x */
  avma = av; /* will erase our x,y when exiting */
  /* now y is odd */
  ly = lgefint(y);
  if (ly == 3) 
  {
    x = diviuexact(x,(ulong)y[2]);
    if (signe(x)) setsigne(x,sx*sy); /* should have x != 0 at this point */
    return x;
  }
  lx = lgefint(x); if (ly>lx) err(talker,"impossible division in diviiexact");
  y0inv = invrev(y[ly-1]);
  i=2; while (i<ly && y[i]==x[i]) i++;
  lz = (i==ly || (ulong)y[i] < (ulong)x[i]) ? lx-ly+3 : lx-ly+2;
  z = new_chunk(lz);

  y += ly - 1; /* now y[-i] = i-th word of y */
  for (ii=lx-1,i=lz-1; i>=2; i--,ii--)
  {
    long limj;
    LOCAL_HIREMAINDER;
    LOCAL_OVERFLOW;

    z[i] = q = y0inv*((ulong)x[ii]); /* i-th quotient */
    if (!q) continue;

    /* x := x - q * y */
    (void)mulll(q,y[0]); limj = max(lx - lz, ii+3-ly);
    { /* update neither lowest word (could set it to 0) nor highest ones */
      register GEN x0 = x + (ii - 1), y0 = y - 1, xlim = x + limj; 
      for (; x0 >= xlim; x0--, y0--)
      {
        *x0 = subll(*x0, addmul(q,*y0));
        hiremainder += overflow;
      }
      if (hiremainder && limj != lx - lz)
      {
        if ((ulong)*x0 < hiremainder)
        {
          *x0 -= hiremainder;
          do (*--x0)--; while ((ulong)*x0 == MAXULONG);
        }
        else
          *x0 -= hiremainder;
      }
    }
  }
#if 0
  i=2; while(i<lz && !z[i]) i++;
  if (i==lz) err(bugparier,"diviiexact");
#else
  i=2; while(!z[i]) i++;
#endif
  z += i-2; lz -= (i-2);
  z[0] = evaltyp(t_INT)|evallg(lz);
  z[1] = evalsigne(sx*sy)|evallg(lz);
  avma = (ulong)z; return z;
}

long
smodsi(long x, GEN y)
{
  if (x<0) err(talker,"negative small integer in smodsi");
  (void)divsi(x,y); return hiremainder;
}

/* x and y are integers. Return 1 if |x| == |y|, 0 otherwise */
int
absi_equal(GEN x, GEN y)
{
  long lx,i;

  if (!signe(x)) return !signe(y);
  if (!signe(y)) return 0;

  lx=lgefint(x); if (lx != lgefint(y)) return 0;
  i=2; while (i<lx && x[i]==y[i]) i++;
  return (i==lx);
}

/* x and y are integers. Return sign(|x| - |y|) */
int
absi_cmp(GEN x, GEN y)
{
  long lx,ly,i;

  if (!signe(x)) return signe(y)? -1: 0;
  if (!signe(y)) return 1;

  lx=lgefint(x); ly=lgefint(y);
  if (lx>ly) return 1;
  if (lx<ly) return -1;
  i=2; while (i<lx && x[i]==y[i]) i++;
  if (i==lx) return 0;
  return ((ulong)x[i] > (ulong)y[i])? 1: -1;
}

/* x and y are reals. Return sign(|x| - |y|) */
int
absr_cmp(GEN x, GEN y)
{
  long ex,ey,lx,ly,lz,i;

  if (!signe(x)) return signe(y)? -1: 0;
  if (!signe(y)) return 1;

  ex=expo(x); ey=expo(y);
  if (ex>ey) return  1;
  if (ex<ey) return -1;

  lx=lg(x); ly=lg(y); lz = (lx<ly)?lx:ly;
  i=2; while (i<lz && x[i]==y[i]) i++;
  if (i<lz) return ((ulong)x[i] > (ulong)y[i])? 1: -1;
  if (lx>=ly)
  {
    while (i<lx && !x[i]) i++;
    return (i==lx)? 0: 1;
  }
  while (i<ly && !y[i]) i++;
  return (i==ly)? 0: -1;
}

/********************************************************************/
/**                                                                **/
/**               INTEGER MULTIPLICATION (KARATSUBA)               **/
/**                                                                **/
/********************************************************************/
#define _sqri_l 47
#define _muli_l 25 /* optimal on PII 350MHz + gcc 2.7.2.1 (gp-dyn) */

#if 0 /* for tunings */
long KARATSUBA_SQRI_LIMIT = _sqri_l;
long KARATSUBA_MULI_LIMIT = _muli_l;

void setsqri(long a) { KARATSUBA_SQRI_LIMIT = a; }
void setmuli(long a) { KARATSUBA_MULI_LIMIT = a; }

GEN
speci(GEN x, long nx)
{
  GEN z;
  long i;
  if (!nx) return gzero;
  z = cgeti(nx+2); z[1] = evalsigne(1)|evallgefint(nx+2);
  for (i=0; i<nx; i++) z[i+2] = x[i];
  return z;
}
#else
#  define KARATSUBA_SQRI_LIMIT _sqri_l
#  define KARATSUBA_MULI_LIMIT _muli_l
#endif

/* nx >= ny = num. of digits of x, y (not GEN, see mulii) */
#ifdef INLINE
INLINE
#endif
GEN
muliispec(GEN x, GEN y, long nx, long ny)
{
  GEN z2e,z2d,yd,xd,ye,zd;
  long p1,lz;
  LOCAL_HIREMAINDER;

  if (!ny) return gzero;
  zd = (GEN)avma; lz = nx+ny+2;
  (void)new_chunk(lz);
  xd = x + nx;
  yd = y + ny;
  ye = yd; p1 = *--xd;

  *--zd = mulll(p1, *--yd); z2e = zd;
  while (yd > y) *--zd = addmul(p1, *--yd);
  *--zd = hiremainder;

  while (xd > x)
  {
    LOCAL_OVERFLOW;
    yd = ye; p1 = *--xd;

    z2d = --z2e;
    *z2d = addll(mulll(p1, *--yd), *z2d); z2d--;
    while (yd > y)
    {
      hiremainder += overflow;
      *z2d = addll(addmul(p1, *--yd), *z2d); z2d--;
    }
    *--zd = hiremainder + overflow;
  }
  if (*zd == 0) { zd++; lz--; } /* normalize */
  *--zd = evalsigne(1) | evallgefint(lz);
  *--zd = evaltyp(t_INT) | evallg(lz);
  avma=(long)zd; return zd;
}

#ifdef INLINE
INLINE
#endif
GEN
sqrispec(GEN x, long nx)
{
  GEN z2e,z2d,yd,xd,zd,x0,z0;
  long p1,lz;
  LOCAL_HIREMAINDER;

  if (!nx) return gzero;
  zd = (GEN)avma; lz = (nx+1) << 1;
  z0 = new_chunk(lz);
  if (nx == 1)
  {
    *--zd = mulll(*x, *x);
    *--zd = hiremainder; goto END;
  }
  xd = x + nx;
  
  /* compute double products --> zd */
  p1 = *--xd; yd = xd; --zd;
  *--zd = mulll(p1, *--yd); z2e = zd;
  while (yd > x) *--zd = addmul(p1, *--yd);
  *--zd = hiremainder;

  x0 = x+1;
  while (xd > x0)
  {
    LOCAL_OVERFLOW;
    p1 = *--xd; yd = xd;

    z2e -= 2; z2d = z2e;
    *z2d = addll(mulll(p1, *--yd), *z2d); z2d--;
    while (yd > x)
    {
      hiremainder += overflow;
      *z2d = addll(addmul(p1, *--yd), *z2d); z2d--;
    }
    *--zd = hiremainder + overflow;
  }
  /* multiply zd by 2 (put result in zd - 1) */
  zd[-1] = ((*zd & HIGHBIT) != 0);
  shift_left(zd, zd, 0, (nx<<1)-3, 0, 1);

  /* add the squares */
  xd = x + nx; zd = z0 + lz;
  p1 = *--xd;
  zd--; *zd = mulll(p1,p1);
  zd--; *zd = addll(hiremainder, *zd);
  while (xd > x)
  {
    p1 = *--xd;
    zd--; *zd = addll(mulll(p1,p1)+ overflow, *zd);
    zd--; *zd = addll(hiremainder + overflow, *zd);
  }

END:
  if (*zd == 0) { zd++; lz--; } /* normalize */
  *--zd = evalsigne(1) | evallgefint(lz);
  *--zd = evaltyp(t_INT) | evallg(lz);
  avma=(long)zd; return zd;
}

/* return (x shifted left d words) + y. Assume d > 0, x > 0 and y >= 0 */
static GEN
addshiftw(GEN x, GEN y, long d)
{
  GEN z,z0,y0,yd, zd = (GEN)avma;
  long a,lz,ly = lgefint(y);

  z0 = new_chunk(d);
  a = ly-2; yd = y+ly;
  if (a >= d)
  {
    y0 = yd-d; while (yd > y0) *--zd = *--yd; /* copy last d words of y */
    a -= d;
    if (a)
      z = addiispec(x+2, y+2, lgefint(x)-2, a);
    else
      z = icopy(x);
  }
  else
  {
    y0 = yd-a; while (yd > y0) *--zd = *--yd; /* copy last a words of y */
    while (zd >= z0) *--zd = 0;    /* complete with 0s */
    z = icopy(x);
  }
  lz = lgefint(z)+d;
  z[1] = evalsigne(1) | evallgefint(lz);
  z[0] = evaltyp(t_INT) | evallg(lz); return z;
}

/* Fast product (Karatsuba) of integers. a and b are "special" GENs
 * c,c0,c1,c2 are genuine GENs.
 */
static GEN
quickmulii(GEN a, GEN b, long na, long nb)
{
  GEN a0,c,c0;
  long av,n0,n0a,i;

  if (na < nb) swapspec(a,b, na,nb);
  if (nb == 1) return mulsispec(*b, a, na);
  if (nb == 0) return gzero;
  if (nb < KARATSUBA_MULI_LIMIT) return muliispec(a,b,na,nb);
  i=(na>>1); n0=na-i; na=i;
  av=avma; a0=a+na; n0a=n0;
  while (!*a0 && n0a) { a0++; n0a--; }

  if (n0a && nb > n0)
  { /* nb <= na <= n0 */
    GEN b0,c1,c2;
    long n0b;

    nb -= n0;
    c = quickmulii(a,b,na,nb);
    b0 = b+nb; n0b = n0;
    while (!*b0 && n0b) { b0++; n0b--; }
    if (n0b)
    {
      c0 = quickmulii(a0,b0, n0a,n0b);

      c2 = addiispec(a0,a, n0a,na);
      c1 = addiispec(b0,b, n0b,nb);
      c1 = quickmulii(c1+2,c2+2, lgefint(c1)-2,lgefint(c2)-2);
      c2 = addiispec(c0+2, c+2, lgefint(c0)-2,lgefint(c) -2);

      c1 = subiispec(c1+2,c2+2, lgefint(c1)-2,lgefint(c2)-2);
    }
    else
    {
      c0 = gzero;
      c1 = quickmulii(a0,b, n0a,nb);
    }
    c = addshiftw(c,c1, n0);
  }
  else
  {
    c = quickmulii(a,b,na,nb);
    c0 = quickmulii(a0,b,n0a,nb);
  }
  return gerepileuptoint(av, addshiftw(c,c0, n0));
}

/* actual operations will take place on a+2 and b+2: we strip the codewords */
GEN
mulii(GEN a,GEN b)
{
  long sa,sb;
  GEN z;

  sa=signe(a); if (!sa) return gzero;
  sb=signe(b); if (!sb) return gzero;
  if (sb<0) sa = -sa;
  z = quickmulii(a+2,b+2, lgefint(a)-2,lgefint(b)-2);
  setsigne(z,sa); return z;
}

GEN
resiimul(GEN x, GEN sy)
{
  GEN r, q, y = (GEN)sy[1], invy;
  long av = avma, k;

  k = cmpii(x, y);
  if (k <= 0) return k? icopy(x): gzero;
  invy = (GEN)sy[2];
  q = mulir(x,invy);
  q = mptrunc(q); /* <= divii(x, y) (at most 1 less) */
  r = subii(x, mulii(y,q));
  /* resii(x,y) + y >= r >= resii(x,y) */
  k = cmpii(r, y);
  if (k >= 0)
  {
    if (k == 0) { avma = av; return gzero; }
    r = subiispec(r+2, y+2, lgefint(r)-2, lgefint(y)-2);
  }
#if 0
  q = subii(r,resii(x,y));
  if (signe(q))
    err(talker,"bug in resiimul: x = %Z\ny = %Z\ndif = %Z", x,y,q);
#endif
  return gerepileuptoint(av, r); /* = resii(x, y) */
}

/* x % (2^n), assuming x, n >= 0 */
GEN
resmod2n(GEN x, long n)
{
  long hi,l,k,lx,ly;
  GEN z, xd, zd;
  
  if (!signe(x) || !n) return gzero;

  l = n & (BITS_IN_LONG-1);    /* n % BITS_IN_LONG */   
  k = n >> TWOPOTBITS_IN_LONG; /* n / BITS_IN_LONG */
  lx = lgefint(x);
  if (lx < k+3) return icopy(x);

  xd = x + (lx-k-1);
  /* x = |_|...|#|1|...|k| : copy the last l bits of # and the last k words
   *            ^--- initial xd  */
  hi = *xd & ((1<<l) - 1); /* last l bits of # = top bits of result */
  if (!hi)
  { /* strip leading zeroes from result */
    xd++; while (k && !*xd) { k--; xd++; }
    if (!k) return gzero;
    ly = k+2; xd--;
  }
  else
    ly = k+3;

  zd = z = cgeti(ly);
  *++zd = evalsigne(1) | evallgefint(ly);
  if (hi) *++zd = hi;
  for ( ;k; k--) *++zd = *++xd;
  return z;
}

static GEN
quicksqri(GEN a, long na)
{
  GEN a0,c;
  long av,n0,n0a,i;

  if (na < KARATSUBA_SQRI_LIMIT) return sqrispec(a,na);
  i=(na>>1); n0=na-i; na=i;
  av=avma; a0=a+na; n0a=n0;
  while (!*a0 && n0a) { a0++; n0a--; }
  c = quicksqri(a,na);
  if (n0a)
  {
    GEN t, c1, c0 = quicksqri(a0,n0a);
#if 0
    c1 = shifti(quickmulii(a0,a, n0a,na),1);
#else /* slower !!! */
    t = addiispec(a0,a,n0a,na);
    t = quicksqri(t+2,lgefint(t)-2);
    c1= addiispec(c0+2,c+2, lgefint(c0)-2, lgefint(c)-2);
    c1= subiispec(t+2, c1+2, lgefint(t)-2, lgefint(c1)-2);
#endif
    c = addshiftw(c,c1, n0);
    c = addshiftw(c,c0, n0);
  }
  else
    c = addshiftw(c,gzero,n0<<1);
  return gerepileuptoint(av, c);
}

GEN
sqri(GEN a) { return quicksqri(a+2, lgefint(a)-2); }

#define MULRR_LIMIT  32
#define MULRR2_LIMIT 32

#if 0
GEN
karamulrr1(GEN x, GEN y)
{
  long sx,sy;
  long i,i1,i2,lx=lg(x),ly=lg(y),e,flag,garde;
  long lz2,lz3,lz4;
  GEN z,lo1,lo2,hi;

  /* ensure that lg(y) >= lg(x) */
  if (lx>ly) { lx=ly; z=x; x=y; y=z; flag=1; } else flag = (lx!=ly);
  if (lx < MULRR_LIMIT) return mulrr(x,y);
  sx=signe(x); sy=signe(y); e = expo(x)+expo(y);
  if (!sx || !sy) return realzero_bit(e);
  if (sy<0) sx = -sx;
  ly=lx+flag; z=cgetr(lx);
  lz2 = (lx>>1); lz3 = lx-lz2;
  x += 2; lx -= 2;
  y += 2; ly -= 2;
  hi = quickmulii(x,y,lz2,lz2);
  i1=lz2; while (i1<lx && !x[i1]) i1++;
  lo1 = quickmulii(y,x+i1,lz2,lx-i1);
  i2=lz2; while (i2<ly && !y[i2]) i2++;
  lo2 = quickmulii(x,y+i2,lz2,ly-i2);

  if (signe(lo1))
  {
    if (flag) { lo2 = addshiftw(lo1,lo2,1); lz3++; } else lo2=addii(lo1,lo2);
  }
  lz4=lgefint(lo2)-lz3;
  if (lz4>0) hi = addiispec(hi+2,lo2+2, lgefint(hi)-2,lz4);
  if (hi[2] < 0)
  {
    e++; garde=hi[lx+2];
    for (i=lx+1; i>=2 ; i--) z[i]=hi[i];
  }
  else
  {
    garde = (hi[lx+2] << 1);
    shift_left(z,hi,2,lx+1, garde, 1);
  }
  z[1]=evalsigne(sx) | evalexpo(e);
  if (garde < 0)
  { /* round to nearest */
    i=lx+2; do z[--i]++; while (z[i]==0);
    if (i==1) z[2]=HIGHBIT;
  }
  avma=(long)z; return z;
}

GEN
karamulrr2(GEN x, GEN y)
{
  long sx,sy,i,lx=lg(x),ly=lg(y),e,flag,garde;
  GEN z,hi;

  if (lx>ly) { lx=ly; z=x; x=y; y=z; flag=1; } else flag = (lx!=ly);
  if (lx < MULRR2_LIMIT) return mulrr(x,y);
  ly=lx+flag; sx=signe(x); sy=signe(y);
  e = expo(x)+expo(y);
  if (!sx || !sy) return realzero_bit(e);
  if (sy<0) sx = -sx;
  z=cgetr(lx);
  hi=quickmulii(y+2,x+2,ly-2,lx-2);
  if (hi[2] < 0)
  {
    e++; garde=hi[lx];
    for (i=2; i<lx ; i++) z[i]=hi[i];
  }
  else
  {
    garde = (hi[lx] << 1);
    shift_left(z,hi,2,lx-1, garde, 1);
  }
  z[1]=evalsigne(sx) | evalexpo(e);
  if (garde < 0)
  { /* round to nearest */
    i=lx; do z[--i]++; while (z[i]==0);
    if (i==1) z[2]=HIGHBIT;
  }
  avma=(long)z; return z;
}

GEN
karamulrr(GEN x, GEN y, long flag)
{
  switch(flag)
  {
    case 1: return karamulrr1(x,y);
    case 2: return karamulrr2(x,y);
    default: err(flagerr,"karamulrr");
  }
  return NULL; /* not reached */
}

GEN
karamulir(GEN x, GEN y, long flag)
{
  long sx=signe(x),lz,i;
  GEN z,temp,z1;

  if (!sx) return gzero;
  lz=lg(y); z=cgetr(lz);
  temp=cgetr(lz+1); affir(x,temp);
  z1=karamulrr(temp,y,flag);
  for (i=1; i<lz; i++) z[i]=z1[i];
  avma=(long)z; return z;
}
#endif

#ifdef LONG_IS_64BIT
GEN
dbltor(double x)
{
  GEN z = cgetr(3);
  long e;
  union { double f; ulong i; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */
  const int expo_len = 11; /* number of bits of exponent */
  LOCAL_HIREMAINDER;

  if (x==0) return realzero_bit(-308);
  fi.f = x;
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

GEN
dbltor(double x)
{
  GEN z;
  long e;
  union { double f; ulong i[2]; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */
  const int shift = mant_len-32;
  const int expo_len = 11; /* number of bits of exponent */

  if (x==0) return realzero_bit(-308);
  fi.f = x; z=cgetr(4);
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
  const int shift = mant_len-32;
  const int expo_len = 11; /* number of bits of exponent */

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

/* Old cgiv without reference count (which was not used anyway)
 * Should be a macro.
 */
void
cgiv(GEN x)
{
  if (x == (GEN) avma)
    avma = (long) (x+lg(x));
}

/********************************************************************/
/**                                                                **/
/**               INTEGER EXTENDED GCD  (AND INVMOD)               **/
/**                                                                **/
/********************************************************************/

/* GN 1998Oct25, originally developed in January 1998 under 2.0.4.alpha,
 * in the context of trying to improve elliptic curve cryptosystem attacking
 * algorithms.  2001Jan02 -- added bezout() functionality.
 *
 * Two basic ideas - (1) avoid many integer divisions, especially when the
 * quotient is 1 (which happens more than 40% of the time).  (2) Use Lehmer's
 * trick as modified by Jebelean of extracting a couple of words' worth of
 * leading bits from both operands, and compute partial quotients from them
 * as long as we can be sure of their values.  The Jebelean modifications
 * consist in reliable inequalities from which we can decide fast whether
 * to carry on or to return to the outer loop, and in re-shifting after the
 * first word's worth of bits has been used up.  All of this is described
 * in R. Lercier's these [pp148-153 & 163f.], except his outer loop isn't
 * quite right  (the catch-up divisions needed when one partial quotient is
 * larger than a word are missing).
 *
 * The API consists of invmod() and bezout() below;  the single-word routines
 * xgcduu and xxgcduu may be called directly if desired;  lgcdii() probably
 * doesn't make much sense out of context.
 *
 * The whole lot is a factor 6 .. 8 faster on word-sized operands, and asym-
 * ptotically about a factor 2.5 .. 3, depending on processor architecture,
 * than the naive continued-division code.  Unfortunately, thanks to the
 * unrolled loops and all, the code is a bit lengthy.
 */

/*==================================
 * xgcduu(d,d1,f,v,v1,s)
 * xxgcduu(d,d1,f,u,u1,v,v1,s)
 * rgcduu(d,d1,vmax,u,u1,v,v1,s)
 *==================================*/
/*
 * Fast `final' extended gcd algorithm, acting on two ulongs.  Ideally this
 * should be replaced with assembler versions wherever possible.  The present
 * code essentially does `subtract, compare, and possibly divide' at each step,
 * which is reasonable when hardware division (a) exists, (b) is a bit slowish
 * and (c) does not depend a lot on the operand values (as on i486).  When
 * wordsize division is in fact an assembler routine based on subtraction,
 * this strategy may not be the most efficient one.
 *
 * xxgcduu() should be called with  d > d1 > 0, returns gcd(d,d1), and assigns
 * the usual signless cont.frac. recurrence matrix to [u, u1; v, v1]  (i.e.,
 * the product of all the [0, 1; 1 q_j] where the leftmost factor arises from
 * the quotient of the first division step),  and the information about the
 * implied signs to s  (-1 when an odd number of divisions has been done,
 * 1 otherwise).  xgcduu() is exactly the same except that u,u1 are not com-
 * puted (and not returned, of course).
 *
 * The input flag f should be set to 1 if we know in advance that gcd(d,d1)==1
 * (so we can stop the chain division one step early:  as soon as the remainder
 * equals 1).  Use this when you intend to use only what would be v, or only
 * what would be u and v, after that final division step, but not u1 and v1.
 * With the flag in force and thus without that final step, the interesting
 * quantity/ies will still sit in [u1 and] v1, of course.
 *
 * For computing the inverse of a single-word INTMOD known to exist, pass f=1
 * to xgcduu(), and obtain the result from s and v1.  (The routine does the
 * right thing when d1==1 already.)  For finishing a multiword modinv known
 * to exist, pass f=1 to xxgcduu(), and multiply the returned matrix  (with
 * properly adjusted signs)  onto the values v' and v1' previously obtained
 * from the multiword division steps.  Actually, just take the scalar product
 * of [v',v1'] with [u1,-v1], and change the sign if s==-1.  (If the final
 * step had been carried out, it would be [-u,v], and s would also change.)
 * For reducing a rational number to lowest terms, pass f=0 to xgcduu().
 * Finally, f=0 with xxgcduu() is useful for Bezout computations.
 * [Harrumph.  In the above prescription, the sign turns out to be precisely
 * wrong.]
 * (It is safe for invmod() to call xgcduu() with f=1, because f&1 doesn't
 * make a difference when gcd(d,d1)>1.  The speedup is negligible.)
 *
 * In principle, when gcd(d,d1) is known to be 1, it is straightforward to
 * recover the final u,u1 given only v,v1 and s.  However, it probably isn't
 * worthwhile, as it trades a few multiplications for a division.
 *
 * Note that these routines do not know and do not need to know about the
 * PARI stack.
 * 
 * Added 2001Jan15:
 * rgcduu() is a variant of xxgcduu() which does not have f  (the effect is
 * that of f=0),  but instead has a ulong vmax parameter, for use in rational
 * reconstruction below.  It returns when v1 exceeds vmax;  v will never
 * exceed vmax.  (vmax=0 is taken as a synonym of MAXULONG i.e. unlimited,
 * in which case rgcduu behaves exactly like xxgcduu with f=0.)  The return
 * value of rgcduu() is typically meaningless;  the interesting part is the
 * matrix.
 */

ulong
xgcduu(ulong d, ulong d1, int f, ulong* v, ulong* v1, long *s)
{
  ulong xv,xv1, xs, q,res;
  LOCAL_HIREMAINDER;

  /* The above blurb contained a lie.  The main loop always stops when d1
   * has become equal to 1.  If (d1 == 1 && !(f&1)) after the loop, we do
   * the final `division' of d by 1 `by hand' as it were.
   *
   * The loop has already been unrolled once.  Aggressive optimization could
   * well lead to a totally unrolled assembler version...
   *
   * On modern x86 architectures, this loop is a pig anyway.  The division
   * instruction always puts its result into the same pair of registers, and
   * we always want to use one of them straight away, so pipeline performance
   * will suck big time.  An assembler version should probably do a first loop
   * computing and storing all the quotients -- their number is bounded in
   * advance -- and then assembling the matrix in a second pass.  On other
   * architectures where we can cycle through four or so groups of registers
   * and exploit a fast ALU result-to-operand feedback path, this is much less
   * of an issue.  (Intel sucks.  See http://www.x86.org/ ...)
   */
  xs = res = 0;
  xv = 0UL; xv1 = 1UL;
  while (d1 > 1UL)
  {
    d -= d1;			/* no need to use subll */
    if (d >= d1)
    {
      hiremainder = 0; q = 1 + divll(d,d1); d = hiremainder;
      xv += q * xv1;
    }
    else
      xv += xv1;
				/* possible loop exit */
    if (d <= 1UL) { xs=1; break; }
				/* repeat with inverted roles */
    d1 -= d;
    if (d1 >= d)
    {
      hiremainder = 0; q = 1 + divll(d1,d); d1 = hiremainder;
      xv1 += q * xv;
    }
    else
      xv1 += xv;
  } /* while */

  if (!(f&1))			/* division by 1 postprocessing if needed */
  {
    if (xs && d==1)
    { xv1 += d1 * xv; xs = 0; res = 1UL; }
    else if (!xs && d1==1)
    { xv += d * xv1; xs = 1; res = 1UL; }
  }

  if (xs)
  {
    *s = -1; *v = xv1; *v1 = xv;
    return (res ? res : (d==1 ? 1UL : d1));
  }
  else
  {
    *s = 1; *v = xv; *v1 = xv1;
    return (res ? res : (d1==1 ? 1UL : d));
  }
}


ulong
xxgcduu(ulong d, ulong d1, int f,
	ulong* u, ulong* u1, ulong* v, ulong* v1, long *s)
{
  ulong xu,xu1, xv,xv1, xs, q,res;
  LOCAL_HIREMAINDER;

  xs = res = 0;
  xu = xv1 = 1UL;
  xu1 = xv = 0UL;
  while (d1 > 1UL)
  {
    d -= d1;			/* no need to use subll */
    if (d >= d1)
    {
      hiremainder = 0; q = 1 + divll(d,d1); d = hiremainder;
      xv += q * xv1;
      xu += q * xu1;
    }
    else
    { xv += xv1; xu += xu1; }
				/* possible loop exit */
    if (d <= 1UL) { xs=1; break; }
				/* repeat with inverted roles */
    d1 -= d;
    if (d1 >= d)
    {
      hiremainder = 0; q = 1 + divll(d1,d); d1 = hiremainder;
      xv1 += q * xv;
      xu1 += q * xu;
    }
    else
    { xv1 += xv; xu1 += xu; }
  } /* while */

  if (!(f&1))			/* division by 1 postprocessing if needed */
  {
    if (xs && d==1)
    {
      xv1 += d1 * xv;
      xu1 += d1 * xu;
      xs = 0; res = 1UL;
    }
    else if (!xs && d1==1)
    {
      xv += d * xv1;
      xu += d * xu1;
      xs = 1; res = 1UL;
    }
  }

  if (xs)
  {
    *s = -1; *u = xu1; *u1 = xu; *v = xv1; *v1 = xv;
    return (res ? res : (d==1 ? 1UL : d1));
  }
  else
  {
    *s = 1; *u = xu; *u1 = xu1; *v = xv; *v1 = xv1;
    return (res ? res : (d1==1 ? 1UL : d));
  }
}

ulong
rgcduu(ulong d, ulong d1, ulong vmax,
       ulong* u, ulong* u1, ulong* v, ulong* v1, long *s)
{
  ulong xu,xu1, xv,xv1, xs, q, res=0;
  int f = 0;
  LOCAL_HIREMAINDER;

  if (vmax == 0) vmax = MAXULONG;
  xs = res = 0;
  xu = xv1 = 1UL;
  xu1 = xv = 0UL;
  while (d1 > 1UL)
  {
    d -= d1;			/* no need to use subll */
    if (d >= d1)
    {
      hiremainder = 0; q = 1 + divll(d,d1); d = hiremainder;
      xv += q * xv1;
      xu += q * xu1;
    }
    else
    { xv += xv1; xu += xu1; }
				/* possible loop exit */
    if (xv > vmax) { f=xs=1; break; }
    if (d <= 1UL) { xs=1; break; }
				/* repeat with inverted roles */
    d1 -= d;
    if (d1 >= d)
    {
      hiremainder = 0; q = 1 + divll(d1,d); d1 = hiremainder;
      xv1 += q * xv;
      xu1 += q * xu;
    }
    else
    { xv1 += xv; xu1 += xu; }
				/* possible loop exit */
    if (xv1 > vmax) { f=1; break; }
  } /* while */

  if (!(f&1))			/* division by 1 postprocessing if needed */
  {
    if (xs && d==1)
    {
      xv1 += d1 * xv;
      xu1 += d1 * xu;
      xs = 0; res = 1UL;
    }
    else if (!xs && d1==1)
    {
      xv += d * xv1;
      xu += d * xu1;
      xs = 1; res = 1UL;
    }
  }

  if (xs)
  {
    *s = -1; *u = xu1; *u1 = xu; *v = xv1; *v1 = xv;
    return (res ? res : (d==1 ? 1UL : d1));
  }
  else
  {
    *s = 1; *u = xu; *u1 = xu1; *v = xv; *v1 = xv1;
    return (res ? res : (d1==1 ? 1UL : d));
  }
}

/*==================================
 * lgcdii(d,d1,u,u1,v,v1,vmax)
 *==================================*/
/* Lehmer's partial extended gcd algorithm, acting on two t_INT GENs.
 *
 * Tries to determine, using the leading 2*BITS_IN_LONG significant bits of d
 * and a quantity of bits from d1 obtained by a shift of the same displacement,
 * as many partial quotients of d/d1 as possible, and assigns to [u,u1;v,v1]
 * the product of all the [0, 1; 1, q_j] thus obtained, where the leftmost
 * factor arises from the quotient of the first division step.
 * 
 * For use in rational reconstruction, input param vmax can be given a
 * nonzero value.  In this case, we will return early as soon as v1 > vmax
 * (i.e. it is guaranteed that v <= vmax). --2001Jan15
 *
 * MUST be called with  d > d1 > 0, and with  d  occupying more than one
 * significant word  (if it doesn't, the caller has no business with us;
 * he/she/it should use xgcduu() instead).  Returns the number of reduction/
 * swap steps carried out, possibly zero, or under certain conditions minus
 * that number.  When the return value is nonzero, the caller should use the
 * returned recurrence matrix to update its own copies of d,d1.  When the
 * return value is non-positive, and the latest remainder after updating
 * turns out to be nonzero, the caller should at once attempt a full division,
 * rather than first trying lgcdii() again -- this typically happens when we
 * are about to encounter a quotient larger than half a word.  (This is not
 * detected infallibly -- after a positive return value, it is perfectly
 * possible that the next stage will end up needing a full division.  After
 * a negative return value, however, this is certain, and should be acted
 * upon.)
 *
 * (The sign information, for which xgcduu() has its return argument s, is now
 * implicit in the LSB of our return value, and the caller may take advantage
 * of the fact that a return value of +-1 implies u==0,u1==v==1  [only v1 pro-
 * vides interesting information in this case].  One might also use the fact
 * that if the return value is +-2, then u==1, but this is rather marginal.)
 *
 * If it was not possible to determine even the first quotient, either because
 * we're too close to an integer quotient or because the quotient would be
 * larger than one word  (if the `leading digit' of d1 after shifting is all
 * zeros),  we return 0 and do not bother to assign anything to the last four
 * args.
 *
 * The division chain might (sometimes) even run to completion.  It will be
 * up to the caller to detect this case.
 *
 * This routine does _not_ change d or d1;  this will also be up to the caller.
 *
 * Note that this routine does not know and does not need to know about the
 * PARI stack.
 */
/*#define DEBUG_LEHMER 1 */
int
lgcdii(ulong* d, ulong* d1,
       ulong* u, ulong* u1, ulong* v, ulong* v1,
       ulong vmax)
{
  /* Strategy:  (1) Extract/shift most significant bits.  We assume that d
   * has at least two significant words, but we can cope with a one-word d1.
   * Let dd,dd1 be the most significant dividend word and matching part of the
   * divisor.
   * (2) Check for overflow on the first division.  For our purposes, this
   * happens when the upper half of dd1 is zero.  (Actually this is detected
   * during extraction.)
   * (3) Get a fix on the first quotient.  We compute q = floor(dd/dd1), which
   * is an upper bound for floor(d/d1), and which gives the true value of the
   * latter if (and-almost-only-if) the remainder dd' = dd-q*dd1 is >= q.
   * (If it isn't, we give up.  This is annoying because the subsequent full
   * division will repeat some work already done, but it happens very infre-
   * quently.  Doing the extra-bit-fetch in this case would be awkward.)
   * (4) Finish initializations.
   *
   * The remainder of the action is comparatively boring... The main loop has
   * been unrolled once  (so we don't swap things and we can apply Jebelean's
   * termination conditions which alternatingly take two different forms during
   * successive iterations).  When we first run out of sufficient bits to form
   * a quotient, and have an extra word of each operand, we pull out two whole
   * word's worth of dividend bits, and divisor bits of matching significance;
   * to these we apply our partial matrix (disregarding overflow because the
   * result mod 2^(2*BITS_IN_LONG) will in fact give the correct values), and
   * re-extract one word's worth of the current dividend and a matching amount
   * of divisor bits.  The affair will normally terminate with matrix entries
   * just short of a whole word.  (We terminate the inner loop before these can
   * possibly overflow.)
   */
  ulong dd,dd1,ddlo,dd1lo, sh,shc;        /* `digits', shift count */
  ulong xu,xu1, xv,xv1, q,res;	/* recurrences, partial quotient, count */
  ulong tmp0,tmp1,tmp2,tmpd,tmpu,tmpv; /* temps */
  long ld, ld1, lz;		/* t_INT effective lengths */
  int skip = 0;			/* a boolean flag */
  LOCAL_OVERFLOW;
  LOCAL_HIREMAINDER;

#ifdef DEBUG_LEHMER
  voir(d, -1); voir(d1, -1);
#endif
  /* following is just for convenience: vmax==0 means no bound */
  if (vmax == 0) vmax = MAXULONG;
  ld = lgefint(d); ld1 = lgefint(d1); lz = ld - ld1; /* >= 0 */
  if (lz > 1) return 0;		/* rare, quick and desperate exit */

  d += 2; d1 += 2;		/* point at the leading `digits' */
  dd1lo = 0;		        /* unless we find something better */
  sh = bfffo(*d);		/* obtain dividend left shift count */

  if (sh)
  {				/* do the shifting */
    shc = BITS_IN_LONG - sh;
    if (lz)
    {				/* dividend longer than divisor */
      dd1 = (*d1 >> shc);
      if (!(HIGHMASK & dd1)) return 0;  /* overflow detected */
      if (ld1 > 3)
        dd1lo = (*d1 << sh) + (d1[1] >> shc);
      else
        dd1lo = (*d1 << sh);
    }
    else
    {				/* dividend and divisor have the same length */
      /* dd1 = shiftl(d1,sh) would have left hiremainder==0, and dd1 != 0. */
      dd1 = (*d1 << sh);
      if (!(HIGHMASK & dd1)) return 0;
      if (ld1 > 3)
      {
        dd1 += (d1[1] >> shc);
        if (ld1 > 4)
          dd1lo = (d1[1] << sh) + (d1[2] >> shc);
        else
          dd1lo = (d1[1] << sh);
      }
    }
    /* following lines assume d to have 2 or more significant words */
    dd = (*d << sh) + (d[1] >> shc);
    if (ld > 4)
      ddlo = (d[1] << sh) + (d[2] >> shc);
    else
      ddlo = (d[1] << sh);
  }
  else
  {				/* no shift needed */
    if (lz) return 0;		/* div'd longer than div'r: o'flow automatic */
    dd1 = *d1;
    if (!(HIGHMASK & dd1)) return 0;
    if(ld1 > 3) dd1lo = d1[1];
    /* assume again that d has another significant word */
    dd = *d; ddlo = d[1];
  }
#ifdef DEBUG_LEHMER
  fprintferr("  %lx:%lx, %lx:%lx\n", dd, ddlo, dd1, dd1lo);
#endif

  /* First subtraction/division stage.  (If a subtraction initially suffices,
   * we don't divide at all.)  If a Jebelean condition is violated, and we
   * can't fix it even by looking at the low-order bits in ddlo,dd1lo, we
   * give up and ask for a full division.  Otherwise we commit the result,
   * possibly deciding to re-shift immediately afterwards.
   */
  dd -= dd1;
  if (dd < dd1)
  {				/* first quotient known to be == 1 */
    xv1 = 1UL;
    if (!dd)			/* !(Jebelean condition), extraspecial case */
    {				/* note this can actually happen...  Now
    				 * q==1 is known, but we underflow already.
				 * OTOH we've just shortened d by a whole word.
				 * Thus we feel pleased with ourselves and
				 * return.  (The re-shift code below would
				 * do so anyway.) */
      *u = 0; *v = *u1 = *v1 = 1UL;
      return -1;		/* Next step will be a full division. */
    } /* if !(Jebelean) then */
  }
  else
  {				/* division indicated */
    hiremainder = 0;
    xv1 = 1 + divll(dd, dd1);	/* xv1: alternative spelling of `q', here ;) */
    dd = hiremainder;
    if (dd < xv1)		/* !(Jebelean cond'), non-extra special case */
    {				/* Attempt to complete the division using the
				 * less significant bits, before skipping right
				 * past the 1st loop to the reshift stage. */
      ddlo = subll(ddlo, mulll(xv1, dd1lo));
      dd = subllx(dd, hiremainder);

      /* If we now have an overflow, q was _certainly_ too large.  Thanks to
       * our decision not to get here unless the original dd1 had bits set in
       * the upper half of the word, however, we now do know that the correct
       * quotient is in fact q-1.  Adjust our data accordingly. */
      if (overflow)
      {
	xv1--;
	ddlo = addll(ddlo,dd1lo);
	dd = addllx(dd,dd1);	/* overflows again which cancels the borrow */
	/* ...and fall through to skip=1 below */
      }
      else
      /* Test Jebelean condition anew, at this point using _all_ the extracted
       * bits we have.  This is clutching at straws; we have a more or less
       * even chance of succeeding this time.  Note that if we fail, we really
       * do not know whether the correct quotient would have been q or some
       * smaller value. */
	if (!dd && ddlo < xv1) return 0;

      /* Otherwise, we now know that q is correct, but we cannot go into the
       * 1st loop.  Raise a flag so we'll remember to skip past the loop.
       * Get here also after the q-1 adjustment case. */
      skip = 1;
    } /* if !(Jebelean) then */
  }
  res = 1;
#ifdef DEBUG_LEHMER
  fprintferr("  q = %ld, %lx, %lx\n", xv1, dd1, dd);
#endif
  if (xv1 > vmax)
  {				/* gone past the bound already */
    *u = 0UL; *u1 = 1UL; *v = 1UL; *v1 = xv1;
    return res;
  }
  xu = 0UL; xv = xu1 = 1UL;

  /* Some invariants from here across the first loop:
   *
   * At this point, and again after we are finished with the first loop and
   * subsequent conditional, a division and the associated update of the
   * recurrence matrix have just been carried out completely.  The matrix
   * xu,xu1;xv,xv1 has been initialized (or updated, possibly with permuted
   * columns), and the current remainder == next divisor (dd at the moment)
   * is nonzero (it might be zero here, but then skip will have been set).
   *
   * After the first loop, or when skip is set already, it will also be the
   * case that there aren't sufficiently many bits to continue without re-
   * shifting.  If the divisor after reshifting is zero, or indeed if it
   * doesn't have more than half a word's worth of bits, we will have to
   * return at that point.  Otherwise, we proceed into the second loop.
   *
   * Furthermore, when we reach the re-shift stage, dd:ddlo and dd1:dd1lo will
   * already reflect the result of applying the current matrix to the old
   * ddorig:ddlo and dd1orig:dd1lo.  (For the first iteration above, this
   * was easy to achieve, and we didn't even need to peek into the (now
   * no longer existent!) saved words.  After the loop, we'll stop for a
   * moment to merge in the ddlo,dd1lo contributions.)
   *
   * Note that after the first division, even an a priori quotient of 1 cannot
   * be trusted until we've checked Jebelean's condition -- it cannot be too
   * large, of course, but it might be too small.
   */

  if (!skip)
  {
    for(;;)
    {
      /* First half of loop divides dd into dd1, and leaves the recurrence
       * matrix xu,...,xv1 groomed the wrong way round (xu,xv will be the newer
       * entries) when successful. */
      tmpd = dd1 - dd;
      if (tmpd < dd)
      {				/* quotient suspected to be 1 */
#ifdef DEBUG_LEHMER
	q = 1;
#endif
	tmpu = xu + xu1;	/* cannot overflow -- everything bounded by
				 * the original dd during first loop */
	tmpv = xv + xv1;
      }
      else
      {				/* division indicated */
	hiremainder = 0;
	q = 1 + divll(tmpd, dd);
	tmpd = hiremainder;
	tmpu = xu + q*xu1;	/* can't overflow, but may need to be undone */
	tmpv = xv + q*xv1;
      }

      tmp0 = addll(tmpv, xv1);
      if ((tmpd < tmpu) || overflow ||
	  (dd - tmpd < tmp0))	/* !(Jebelean cond.) */
	break;			/* skip ahead to reshift stage */
      else
      {				/* commit dd1, xu, xv */
	res++;
	dd1 = tmpd; xu = tmpu; xv = tmpv;
#ifdef DEBUG_LEHMER
	fprintferr("  q = %ld, %lx, %lx [%lu,%lu;%lu,%lu]\n",
		   q, dd, dd1, xu1, xu, xv1, xv);
#endif
	if (xv > vmax)
	{			/* time to return */
	  *u = xu1; *u1 = xu; *v = xv1; *v1 = xv;
	  return res;
	}
      }

      /* Second half of loop divides dd1 into dd, and the matrix returns to its
       * normal arrangement. */
      tmpd = dd - dd1;
      if (tmpd < dd1)
      {				/* quotient suspected to be 1 */
#ifdef DEBUG_LEHMER
	q = 1;
#endif
	tmpu = xu1 + xu;	/* cannot overflow */
	tmpv = xv1 + xv;
      }
      else
      {				/* division indicated */
	hiremainder = 0;
	q = 1 + divll(tmpd, dd1);
	tmpd = hiremainder;
	tmpu = xu1 + q*xu;
	tmpv = xv1 + q*xv;
      }

      tmp0 = addll(tmpu, xu);
      if ((tmpd < tmpv) || overflow ||
	  (dd1 - tmpd < tmp0))	/* !(Jebelean cond.) */
	break;			/* skip ahead to reshift stage */
      else
      {				/* commit dd, xu1, xv1 */
	res++;
	dd = tmpd; xu1 = tmpu; xv1 = tmpv;
#ifdef DEBUG_LEHMER
	fprintferr("  q = %ld, %lx, %lx [%lu,%lu;%lu,%lu]\n",
		q, dd1, dd, xu, xu1, xv, xv1);
#endif
	if (xv1 > vmax)
	{			/* time to return */
	  *u = xu; *u1 = xu1; *v = xv; *v1 = xv1;
	  return res;
	}
      }

    } /* end of first loop */

    /* Intermezzo: update dd:ddlo, dd1:dd1lo.  (But not if skip is set.) */

    if (res&1)
    {
      /* after failed division in 1st half of loop:
       * [dd1:dd1lo,dd:ddlo] = [ddorig:ddlo,dd1orig:dd1lo]
       *                       * [ -xu, xu1 ; xv, -xv1 ]
       * (Actually, we only multiply [ddlo,dd1lo] onto the matrix and
       * add the high-order remainders + overflows onto [dd1,dd].)
       */
      tmp1 = mulll(ddlo, xu); tmp0 = hiremainder;
      tmp1 = subll(mulll(dd1lo,xv), tmp1);
      dd1 += subllx(hiremainder, tmp0);
      tmp2 = mulll(ddlo, xu1); tmp0 = hiremainder;
      ddlo = subll(tmp2, mulll(dd1lo,xv1));
      dd += subllx(tmp0, hiremainder);
      dd1lo = tmp1;
    }
    else
    {
      /* after failed division in 2nd half of loop:
       * [dd:ddlo,dd1:dd1lo] = [ddorig:ddlo,dd1orig:dd1lo]
       *                       * [ xu1, -xu ; -xv1, xv ]
       * (Actually, we only multiply [ddlo,dd1lo] onto the matrix and
       * add the high-order remainders + overflows onto [dd,dd1].)
       */
      tmp1 = mulll(ddlo, xu1); tmp0 = hiremainder;
      tmp1 = subll(tmp1, mulll(dd1lo,xv1));
      dd += subllx(tmp0, hiremainder);
      tmp2 = mulll(ddlo, xu); tmp0 = hiremainder;
      dd1lo = subll(mulll(dd1lo,xv), tmp2);
      dd1 += subllx(hiremainder, tmp0);
      ddlo = tmp1;
    }
#ifdef DEBUG_LEHMER
    fprintferr("  %lx:%lx, %lx:%lx\n", dd, ddlo, dd1, dd1lo);
#endif
  } /* end of skip-pable section:  get here also, with res==1, when there
     * was a problem immediately after the very first division. */

  /* Re-shift.  Note:  the shift count _can_ be zero, viz. under the following
   * precise conditions:  The original dd1 had its topmost bit set, so the 1st
   * q was 1, and after subtraction, dd had its topmost bit unset.  If now
   * dd==0, we'd have taken the return exit already, so we couldn't have got
   * here.  If not, then it must have been the second division which has gone
   * amiss  (because dd1 was very close to an exact multiple of the remainder
   * dd value, so this will be very rare).  At this point, we'd have a fairly
   * slim chance of fixing things by re-examining dd1:dd1lo vs. dd:ddlo, but
   * this is not guaranteed to work.  Instead of trying, we return at once.
   * The caller will see to it that the initial subtraction is re-done using
   * _all_ the bits of both operands, which already helps, and the next round
   * will either be a full division  (if dd occupied a halfword or less),  or
   * another llgcdii() first step.  In the latter case, since we try a little
   * harder during our first step, we may actually be able to fix the problem,
   * and get here again with improved low-order bits and with another step
   * under our belt.  Otherwise we'll have given up above and forced a full-
   * blown division.
   *
   * If res is even, the shift count _cannot_ be zero.  (The first step forces
   * a zero into the remainder's MSB, and all subsequent remainders will have
   * inherited it.)
   *
   * The re-shift stage exits if the next divisor has at most half a word's
   * worth of bits.
   *
   * For didactic reasons, the second loop will be arranged in the same way
   * as the first -- beginning with the division of dd into dd1, as if res
   * was odd.  To cater for this, if res is actually even, we swap things
   * around during reshifting.  (During the second loop, the parity of res
   * does not matter;  we know in which half of the loop we are when we decide
   * to return.)
   */
#ifdef DEBUG_LEHMER
  fprintferr("(sh)");
#endif

  if (res&1)
  {				/* after odd number of division(s) */
    if (dd1 && (sh = bfffo(dd1)))
    {
      shc = BITS_IN_LONG - sh;
      dd = (ddlo >> shc) + (dd << sh);
      if (!(HIGHMASK & dd))
      {
	*u = xu; *u1 = xu1; *v = xv; *v1 = xv1;
	return -res;		/* full division asked for */
      }
      dd1 = (dd1lo >> shc) + (dd1 << sh);
    }
    else
    {				/* time to return: <= 1 word left, or sh==0 */
      *u = xu; *u1 = xu1; *v = xv; *v1 = xv1;
      return res;
    }
  }
  else
  {				/* after even number of divisions */
    if (dd)
    {
      sh = bfffo(dd);		/* Known to be positive. */
      shc = BITS_IN_LONG - sh;
				/* dd:ddlo will become the new dd1, and v.v. */
      tmpd = (ddlo >> shc) + (dd << sh);
      dd = (dd1lo >> shc) + (dd1 << sh);
      dd1 = tmpd;
      /* This has completed the swap;  now dd is again the current divisor.
       * The following test originally inspected dd1 -- a most subtle and
       * most annoying bug. The Management. */
      if (HIGHMASK & dd)
      {
	/* recurrence matrix is the wrong way round;  swap it. */
	tmp0 = xu; xu = xu1; xu1 = tmp0;
	tmp0 = xv; xv = xv1; xv1 = tmp0;
      }
      else
      {
	/* recurrence matrix is the wrong way round;  fix this. */
	*u = xu1; *u1 = xu; *v = xv1; *v1 = xv;
	return -res;		/* full division asked for */
      }
    }
    else
    {				/* time to return: <= 1 word left */
      *u = xu1; *u1 = xu; *v = xv1; *v1 = xv;
      return res;
    }
  } /* end reshift */

#ifdef DEBUG_LEHMER
  fprintferr("  %lx:%lx, %lx:%lx\n", dd, ddlo, dd1, dd1lo);
#endif

  /* The Second Loop.  Rip-off of the first, but we now check for overflow
   * in the recurrences.  Returns instead of breaking when we cannot fix the
   * quotient any longer.
   */

  for(;;)
  {
    /* First half of loop divides dd into dd1, and leaves the recurrence
     * matrix xu,...,xv1 groomed the wrong way round (xu,xv will be the newer
     * entries) when successful. */
    tmpd = dd1 - dd;
    if (tmpd < dd)
    {				/* quotient suspected to be 1 */
#ifdef DEBUG_LEHMER
      q = 1;
#endif
      tmpu = xu + xu1;
      tmpv = addll(xv, xv1);	/* xv,xv1 will overflow first */
      tmp1 = overflow;
    }
    else
    {				/* division indicated */
      hiremainder = 0;
      q = 1 + divll(tmpd, dd);
      tmpd = hiremainder;
      tmpu = xu + q*xu1;
      tmpv = addll(xv, mulll(q,xv1));
      tmp1 = overflow | hiremainder;
    }

    tmp0 = addll(tmpv, xv1);
    if ((tmpd < tmpu) || overflow || tmp1 ||
	(dd - tmpd < tmp0))	/* !(Jebelean cond.) */
    {
      /* The recurrence matrix has not yet been warped... */
      *u = xu; *u1 = xu1; *v = xv; *v1 = xv1;
      break;
    }
    /* commit dd1, xu, xv */
    res++;
    dd1 = tmpd; xu = tmpu; xv = tmpv;
#ifdef DEBUG_LEHMER
    fprintferr("  q = %ld, %lx, %lx\n", q, dd, dd1);
#endif
    if (xv > vmax)
    {				/* time to return */
      *u = xu1; *u1 = xu; *v = xv1; *v1 = xv;
      return res;
    }

    /* Second half of loop divides dd1 into dd, and the matrix returns to its
     * normal arrangement. */
    tmpd = dd - dd1;
    if (tmpd < dd1)
    {				/* quotient suspected to be 1 */
#ifdef DEBUG_LEHMER
      q = 1;
#endif
      tmpu = xu1 + xu;
      tmpv = addll(xv1, xv);
      tmp1 = overflow;
    }
    else
    {				/* division indicated */
      hiremainder = 0;
      q = 1 + divll(tmpd, dd1);
      tmpd = hiremainder;
      tmpu = xu1 + q*xu;
      tmpv = addll(xv1, mulll(q, xv));
      tmp1 = overflow | hiremainder;
    }

    tmp0 = addll(tmpu, xu);
    if ((tmpd < tmpv) || overflow || tmp1 ||
	(dd1 - tmpd < tmp0))	/* !(Jebelean cond.) */
    {
      /* The recurrence matrix has not yet been unwarped, so it is
       * the wrong way round;  fix this. */
      *u = xu1; *u1 = xu; *v = xv1; *v1 = xv;
      break;
    }
  
    res++; /* commit dd, xu1, xv1 */
    dd = tmpd; xu1 = tmpu; xv1 = tmpv;
#ifdef DEBUG_LEHMER
    fprintferr("  q = %ld, %lx, %lx\n", q, dd1, dd);
#endif
    if (xv1 > vmax)
    {				/* time to return */
      *u = xu; *u1 = xu1; *v = xv; *v1 = xv1;
      return res;
    }
  } /* end of second loop */

  return res;
}

/*==================================
 * invmod(a,b,res)
 *==================================
 *    If a is invertible, return 1, and set res  = a^{ -1 }
 *    Otherwise, return 0, and set res = gcd(a,b)
 * 
 * This is sufficiently different from bezout() to be implemented separately
 * instead of having a bunch of extra conditionals in a single function body
 * to meet both purposes.
 */

int
invmod(GEN a, GEN b, GEN *res)
{
  GEN v,v1,d,d1,q,r;
  long av,av1,lim;
  long s;
  ulong g;
  ulong xu,xu1,xv,xv1;		/* Lehmer stage recurrence matrix */
  int lhmres;			/* Lehmer stage return value */

  if (typ(a) != t_INT || typ(b) != t_INT) err(arither1);
  if (!signe(b)) { *res=absi(a); return 0; }
  av = avma;
  if (lgefint(b) == 3) /* single-word affair */
  {
    d1 = modiu(a, (ulong)(b[2]));
    if (d1 == gzero)
    {
      if (b[2] == 1L)
        { *res = gzero; return 1; }
      else
        { *res = absi(b); return 0; }
    }
    g = xgcduu((ulong)(b[2]), (ulong)(d1[2]), 1, &xv, &xv1, &s);
#ifdef DEBUG_LEHMER
    fprintferr(" <- %lu,%lu\n", (ulong)(b[2]), (ulong)(d1[2]));
    fprintferr(" -> %lu,%ld,%lu; %lx\n", g,s,xv1,avma);
#endif
    avma = av;
    if (g != 1UL) { *res = utoi(g); return 0; }
    xv = xv1 % (ulong)(b[2]); if (s < 0) xv = ((ulong)(b[2])) - xv;
    *res = utoi(xv); return 1;
  }

  (void)new_chunk(lgefint(b));
  d = absi(b); d1 = modii(a,d);

  v=gzero; v1=gun;	/* general case */
#ifdef DEBUG_LEHMER
  fprintferr("INVERT: -------------------------\n");
  output(d1);
#endif
  av1 = avma; lim = stack_lim(av,1);

  while (lgefint(d) > 3 && signe(d1))
  {
#ifdef DEBUG_LEHMER
    fprintferr("Calling Lehmer:\n");
#endif
    lhmres = lgcdii((ulong*)d, (ulong*)d1, &xu, &xu1, &xv, &xv1, MAXULONG);
    if (lhmres != 0)		/* check progress */
    {				/* apply matrix */
#ifdef DEBUG_LEHMER
      fprintferr("Lehmer returned %d [%lu,%lu;%lu,%lu].\n",
	      lhmres, xu, xu1, xv, xv1);
#endif
      if ((lhmres == 1) || (lhmres == -1))
      {
	if (xv1 == 1)
	{
	  r = subii(d,d1); d=d1; d1=r;
	  a = subii(v,v1); v=v1; v1=a;
	}
	else
	{
	  r = subii(d, mului(xv1,d1)); d=d1; d1=r;
	  a = subii(v, mului(xv1,v1)); v=v1; v1=a;
	}
      }
      else
      {
	r  = subii(muliu(d,xu),  muliu(d1,xv));
	a  = subii(muliu(v,xu),  muliu(v1,xv));
	d1 = subii(muliu(d,xu1), muliu(d1,xv1)); d = r;
	v1 = subii(muliu(v,xu1), muliu(v1,xv1)); v = a;
        if (lhmres&1)
	{
          setsigne(d,-signe(d));
          setsigne(v,-signe(v));
        }
        else
	{
          if (signe(d1)) { setsigne(d1,-signe(d1)); }
          setsigne(v1,-signe(v1));
        }
      }
    }
#ifdef DEBUG_LEHMER
    else
      fprintferr("Lehmer returned 0.\n");
    output(d); output(d1); output(v); output(v1);
    sleep(1);
#endif

    if (lhmres <= 0 && signe(d1))
    {
      q = dvmdii(d,d1,&r);
#ifdef DEBUG_LEHMER
      fprintferr("Full division:\n");
      printf("  q = "); output(q); sleep (1);
#endif
      a = subii(v,mulii(q,v1));
      v=v1; v1=a;
      d=d1; d1=r;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[4]; gptr[0]=&d; gptr[1]=&d1; gptr[2]=&v; gptr[3]=&v1;
      if(DEBUGMEM>1) err(warnmem,"invmod");
      gerepilemany(av1,gptr,4);
    }
  } /* end while */

  /* Postprocessing - final sprint */
  if (signe(d1))
  {
    /* Assertions: lgefint(d)==lgefint(d1)==3, and
     * gcd(d,d1) is nonzero and fits into one word
     */
    g = xxgcduu((ulong)(d[2]), (ulong)(d1[2]), 1, &xu, &xu1, &xv, &xv1, &s);
#ifdef DEBUG_LEHMER
    output(d);output(d1);output(v);output(v1);
    fprintferr(" <- %lu,%lu\n", (ulong)(d[2]), (ulong)(d1[2]));
    fprintferr(" -> %lu,%ld,%lu; %lx\n", g,s,xv1,avma);
#endif
    if (g != 1UL) { avma = av; *res = utoi(g); return 0; }
    /* (From the xgcduu() blurb:)
     * For finishing the multiword modinv, we now have to multiply the
     * returned matrix  (with properly adjusted signs)  onto the values
     * v' and v1' previously obtained from the multiword division steps.
     * Actually, it is sufficient to take the scalar product of [v',v1']
     * with [u1,-v1], and change the sign if s==1.
     */
    v = subii(muliu(v,xu1),muliu(v1,xv1));
    if (s > 0) setsigne(v,-signe(v));
    avma = av; *res = modii(v,b);
#ifdef DEBUG_LEHMER
    output(*res); fprintfderr("============================Done.\n");
    sleep(1);
#endif
    return 1;
  }
  /* get here when the final sprint was skipped (d1 was zero already) */
  avma = av;
  if (!egalii(d,gun)) { *res = icopy(d); return 0; }
  *res = modii(v,b);
#ifdef DEBUG_LEHMER
  output(*res); fprintferr("============================Done.\n");
  sleep(1);
#endif
  return 1;
}

/*==================================
 * bezout(a,b,pu,pv)
 *==================================
 *    Return g = gcd(a,b) >= 0, and assign GENs u,v through pointers pu,pv
 *    such that g = u*a + v*b.
 * Special cases:
 *    a == b == 0 ==> pick u=1, v=0
 *    a != 0 == b ==> keep v=0
 *    a == 0 != b ==> keep u=0
 *    |a| == |b| != 0 ==> keep u=0, set v=+-1
 * Assignments through pu,pv will be suppressed when the corresponding
 * pointer is NULL  (but the computations will happen nonetheless).
 */

GEN
bezout(GEN a, GEN b, GEN *pu, GEN *pv)
{
  GEN t,u,u1,v,v1,d,d1,q,r;
  GEN *pt;
  long av,av1,lim;
  long s;
  int sa, sb;
  ulong g;
  ulong xu,xu1,xv,xv1;		/* Lehmer stage recurrence matrix */
  int lhmres;			/* Lehmer stage return value */

  if (typ(a) != t_INT || typ(b) != t_INT) err(arither1);
  s = absi_cmp(a,b);
  if (s < 0)
  {
    t=b; b=a; a=t;
    pt=pu; pu=pv; pv=pt;
  }
  /* now |a| >= |b| */

  sa = signe(a); sb = signe(b);
  if (!sb)
  {
    if (pv != NULL) *pv = gzero;
    switch(sa)
    {
    case  0:
      if (pu != NULL) *pu = gun; return gzero;
    case  1:
      if (pu != NULL) *pu = gun; return icopy(a);
    case -1:
      if (pu != NULL) *pu = negi(gun); return(negi(a));
    }
  }
  if (s == 0)			/* |a| == |b| != 0 */
  {
    if (pu != NULL) *pu = gzero;
    if (sb > 0)
    {
      if (pv != NULL) *pv = gun; return icopy(b);
    }
    else
    {
      if (pv != NULL) *pv = negi(gun); return(negi(b));
    }
  }
  /* now |a| > |b| > 0 */

  if (lgefint(a) == 3)		/* single-word affair */
  {
    g = xxgcduu((ulong)(a[2]), (ulong)(b[2]), 0, &xu, &xu1, &xv, &xv1, &s);
    sa = s > 0 ? sa : -sa;
    sb = s > 0 ? -sb : sb;
    if (pu != NULL)
    {
      if (xu == 0) *pu = gzero; /* can happen when b divides a */
      else if (xu == 1) *pu = sa < 0 ? negi(gun) : gun;
      else if (xu == 2) *pu = sa < 0 ? negi(gdeux) : gdeux;
      else
      {
	*pu = cgeti(3);
	(*pu)[1] = evalsigne(sa)|evallgefint(3);
	(*pu)[2] = xu;
      }
    }
    if (pv != NULL)
    {
      if (xv == 1) *pv = sb < 0 ? negi(gun) : gun;
      else if (xv == 2) *pv = sb < 0 ? negi(gdeux) : gdeux;
      else
      {
	*pv = cgeti(3);
	(*pv)[1] = evalsigne(sb)|evallgefint(3);
	(*pv)[2] = xv;
      }
    }
    if (g == 1) return gun;
    else if (g == 2) return gdeux;
    else
    {
      r = cgeti(3);
      r[1] = evalsigne(1)|evallgefint(3);
      r[2] = g;
      return r;
    }
  }

  /* general case */
  av = avma;
  (void)new_chunk(lgefint(b) + (lgefint(a)<<1)); /* room for u,v,gcd */
  /* if a is significantly larger than b, calling lgcdii() is not the best
   * way to start -- reduce a mod b first
   */
  if (lgefint(a) > lgefint(b))
  {
    d = absi(b), q = dvmdii(absi(a), d, &d1);
    if (!signe(d1))		/* a == qb */
    {
      avma = av;
      if (pu != NULL) *pu = gzero;
      if (pv != NULL) *pv = sb < 0 ? negi(gun) : gun;
      return (icopy(d));
    }
    else
    {
      u = gzero;
      u1 = v = gun;
      v1 = negi(q);
    }
    /* if this results in lgefint(d) == 3, will fall past main loop */
  }
  else
  {
    d = absi(a); d1 = absi(b);
    u = v1 = gun; u1 = v = gzero;
  }
  av1 = avma; lim = stack_lim(av, 1);

  /* main loop is almost identical to that of invmod() */
  while (lgefint(d) > 3 && signe(d1))
  {
    lhmres = lgcdii((ulong *)d, (ulong *)d1, &xu, &xu1, &xv, &xv1, MAXULONG);
    if (lhmres != 0)		/* check progress */
    {				/* apply matrix */
      if ((lhmres == 1) || (lhmres == -1))
      {
	if (xv1 == 1)
	{
	  r = subii(d,d1); d=d1; d1=r;
	  a = subii(u,u1); u=u1; u1=a;
	  a = subii(v,v1); v=v1; v1=a;
	}
	else
	{
	  r = subii(d, mului(xv1,d1)); d=d1; d1=r;
	  a = subii(u, mului(xv1,u1)); u=u1; u1=a;
	  a = subii(v, mului(xv1,v1)); v=v1; v1=a;
	}
      }
      else
      {
	r  = subii(muliu(d,xu),  muliu(d1,xv));
	d1 = subii(muliu(d,xu1), muliu(d1,xv1)); d = r;
	a  = subii(muliu(u,xu),  muliu(u1,xv));
	u1 = subii(muliu(u,xu1), muliu(u1,xv1)); u = a;
	a  = subii(muliu(v,xu),  muliu(v1,xv));
	v1 = subii(muliu(v,xu1), muliu(v1,xv1)); v = a;
        if (lhmres&1)
	{
          setsigne(d,-signe(d));
          setsigne(u,-signe(u));
          setsigne(v,-signe(v));
        }
        else
	{
          if (signe(d1)) { setsigne(d1,-signe(d1)); }
          setsigne(u1,-signe(u1));
          setsigne(v1,-signe(v1));
        }
      }
    }
    if (lhmres <= 0 && signe(d1))
    {
      q = dvmdii(d,d1,&r);
#ifdef DEBUG_LEHMER
      fprintferr("Full division:\n");
      printf("  q = "); output(q); sleep (1);
#endif
      a = subii(u,mulii(q,u1));
      u=u1; u1=a;
      a = subii(v,mulii(q,v1));
      v=v1; v1=a;
      d=d1; d1=r;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[6]; gptr[0]=&d; gptr[1]=&d1; gptr[2]=&u; gptr[3]=&u1;
      gptr[4]=&v; gptr[5]=&v1;
      if(DEBUGMEM>1) err(warnmem,"bezout");
      gerepilemany(av1,gptr,6);
    }
  } /* end while */

  /* Postprocessing - final sprint */
  if (signe(d1))
  {
    /* Assertions: lgefint(d)==lgefint(d1)==3, and
     * gcd(d,d1) is nonzero and fits into one word
     */
    g = xxgcduu((ulong)(d[2]), (ulong)(d1[2]), 0, &xu, &xu1, &xv, &xv1, &s);
    u = subii(muliu(u,xu), muliu(u1, xv));
    v = subii(muliu(v,xu), muliu(v1, xv));
    if (s < 0) { sa = -sa; sb = -sb; }
    avma = av;
    if (pu != NULL) *pu = sa < 0 ? negi(u) : icopy(u);
    if (pv != NULL) *pv = sb < 0 ? negi(v) : icopy(v);
    if (g == 1) return gun;
    else if (g == 2) return gdeux;
    else
    {
      r = cgeti(3);
      r[1] = evalsigne(1)|evallgefint(3);
      r[2] = g;
      return r;
    }
  }
  /* get here when the final sprint was skipped (d1 was zero already).
   * Now the matrix is final, and d contains the gcd.
   */
  avma = av;
  if (pu != NULL) *pu = sa < 0 ? negi(u) : icopy(u);
  if (pv != NULL) *pv = sb < 0 ? negi(v) : icopy(v);
  return icopy(d);
}

/*==================================
 * cbezout(a,b,uu,vv)
 *==================================
 * Same as bezout() but for C longs.
 *    Return g = gcd(a,b) >= 0, and assign longs u,v through pointers uu,vv
 *    such that g = u*a + v*b.
 * Special cases:
 *    a == b == 0 ==> pick u=1, v=0 (and return 1, surprisingly)
 *    a != 0 == b ==> keep v=0
 *    a == 0 != b ==> keep u=0
 *    |a| == |b| != 0 ==> keep u=0, set v=+-1
 * Assignments through uu,vv happen unconditionally;  non-NULL pointers
 * _must_ be used.
 */
long
cbezout(long a,long b,long *uu,long *vv)
{
  long s,*t;
  ulong d = labs(a), d1 = labs(b);
  ulong r,u,u1,v,v1;

#ifdef DEBUG_CBEZOUT
  fprintferr("> cbezout(%ld,%ld,%p,%p)\n", a, b, (void *)uu, (void *)vv);
#endif
  if (!b)
  {
    *vv=0L;
    if (!a)
    {
      *uu=1L;
#ifdef DEBUG_CBEZOUT
      fprintferr("< %ld (%ld, %ld)\n", 1L, *uu, *vv);
#endif
      return 0L;
    }
    *uu = a < 0 ? -1L : 1L;
#ifdef DEBUG_CBEZOUT
    fprintferr("< %ld (%ld, %ld)\n", (long)d, *uu, *vv);
#endif
    return (long)d;
  }
  else if (!a || (d == d1))
  {
    *uu = 0L; *vv = b < 0 ? -1L : 1L;
#ifdef DEBUG_CBEZOUT
    fprintferr("< %ld (%ld, %ld)\n", (long)d1, *uu, *vv);
#endif
    return (long)d1;
  }
  else if (d == 1)		/* frequently used by nfinit */
  {
    *uu = a; *vv = 0L;
#ifdef DEBUG_CBEZOUT
    fprintferr("< %ld (%ld, %ld)\n", 1L, *uu, *vv);
#endif
    return 1L;
  }
  else if (d < d1)
  {
/* bug in gcc-2.95.3:
 * s = a; a = b; b = s; produces wrong result a = b. This is OK:  */
    { long _x = a; a = b; b = _x; }	/* in order to keep the right signs */
    r = d; d = d1; d1 = r;
    t = uu; uu = vv; vv = t;
#ifdef DEBUG_CBEZOUT
    fprintferr("  swapping\n");
#endif
  }
  /* d > d1 > 0 */
  r = xxgcduu(d, d1, 0, &u, &u1, &v, &v1, &s);
  if (s < 0)
  {
    *uu = a < 0 ? u : -(long)u;
    *vv = b < 0 ? -(long)v : v;
  }
  else
  {
    *uu = a < 0 ? -(long)u : u;
    *vv = b < 0 ? v : -(long)v;
  }
#ifdef DEBUG_CBEZOUT
  fprintferr("< %ld (%ld, %ld)\n", (long)r, *uu, *vv);
#endif
  return (long)r;
}

/*==========================================================
 * ratlift(GEN x, GEN m, GEN *a, GEN *b, GEN amax, GEN bmax)
 *==========================================================
 * Reconstruct rational number from its residue x mod m
 *    Given t_INT x, m, amax>=0, bmax>0 such that
 * 	0 <= x < m;  2*amax*bmax < m
 *    attempts to find t_INT a, b such that
 * 	(1) a = b*x (mod m)
 * 	(2) |a| <= amax, 0 < b <= bmax
 * 	(3) gcd(m, b) = gcd(a, b)
 *    If unsuccessful, it will return 0 and leave a,b unchanged  (and
 *    caller may deduce no such a,b exist).  If successful, sets a,b
 *    and returns 1.  If there exist a,b satisfying (1), (2), and
 * 	(3') gcd(m, b) = 1
 *    then they are uniquely determined subject to (1),(2) and
 * 	(3'') gcd(a, b) = 1,
 *    and will be returned by the routine.  (The caller may wish to
 *    check gcd(a,b)==1, either directly or based on known prime
 *    divisors of m, depending on the application.)
 * Reference:
 @article {MR97c:11116,
     AUTHOR = {Collins, George E. and Encarnaci{\'o}n, Mark J.},
      TITLE = {Efficient rational number reconstruction},
    JOURNAL = {J. Symbolic Comput.},
   FJOURNAL = {Journal of Symbolic Computation},
     VOLUME = {20},
       YEAR = {1995},
     NUMBER = {3},
      PAGES = {287--297},
       ISSN = {0747-7171},
    MRCLASS = {11Y16 (68Q40)},
   MRNUMBER = {97c:11116},
 MRREVIEWER = {Maurice Mignotte},
 }
 *    Preprint available from:
 *    ftp://ftp.risc.uni-linz.ac.at/pub/techreports/1994/94-64.ps.gz
 */

/* #define DEBUG_RATLIFT */

int
ratlift(GEN x, GEN m, GEN *a, GEN *b, GEN amax, GEN bmax)
{
  GEN d,d1,v,v1,q,r;
  ulong av = avma, av1, lim;
  long lb,lr,lbb,lbr,s,s0;
  ulong vmax;
  ulong xu,xu1,xv,xv1;		/* Lehmer stage recurrence matrix */
  int lhmres;			/* Lehmer stage return value */

  if ((typ(x) | typ(m) | typ(amax) | typ(bmax)) != t_INT) err(arither1);
  if (signe(bmax) <= 0)
    err(talker, "ratlift: bmax must be > 0, found\n\tbmax=%Z\n", bmax);
  if (signe(amax) < 0)
    err(talker, "ratilft: amax must be >= 0, found\n\tamax=%Z\n", amax);
  /* check 2*amax*bmax < m */
  if (cmpii(shifti(mulii(amax, bmax), 1), m) >= 0)
    err(talker, "ratlift: must have 2*amax*bmax < m, found\n\tamax=%Z\n\tbmax=%Z\n\tm=%Z\n", amax,bmax,m);
  /* we _could_ silently replace x with modii(x,m) instead of the following,
   * but let's leave this up to the caller
   */
  avma = av; s = signe(x);
  if (s < 0 || cmpii(x,m) >= 0)
    err(talker, "ratlift: must have 0 <= x < m, found\n\tx=%Z\n\tm=%Z\n", x,m);

  /* special cases x=0 and/or amax=0 */
  if (s == 0)
  {
    if (a != NULL) *a = gzero;
    if (b != NULL) *b = gun;
    return 1;
  }
  else if (signe(amax)==0)
    return 0;
  /* assert: m > x > 0, amax > 0 */

  /* check here whether a=x, b=1 is a solution */
  if (cmpii(x,amax) <= 0)
  {
    if (a != NULL) *a = icopy(x);
    if (b != NULL) *b = gun;
    return 1;
  }

  /* There is no special case for single-word numbers since this is
   * mainly meant to be used with large moduli.
   */
  (void)new_chunk(lgefint(bmax) + lgefint(amax)); /* room for a,b */
  d = m; d1 = x;
  v = gzero; v1 = gun;
  /* assert d1 > amax, v1 <= bmax here */
  lb = lgefint(bmax);
  lbb = bfffo(bmax[2]);
  s = 1;
  av1 = avma; lim = stack_lim(av, 1);

  /* general case: Euclidean division chain starting with m div x, and
   * with bounds on the sequence of convergents' denoms v_j.
   * Just to be different from what invmod and bezout are doing, we work
   * here with the all-nonnegative matrices [u,u1;v,v1]=prod_j([0,1;1,q_j]).
   * Loop invariants:
   * (a) (sign)*[-v,v1]*x = [d,d1] (mod m)  (componentwise)
   * (sign initially +1, changes with each Euclidean step)
   * so [a,b] will be obtained in the form [-+d,v] or [+-d1,v1];
   * this congruence is a consequence of
   * (b) [x,m]~ = [u,u1;v,v1]*[d1,d]~,
   * where u,u1 is the usual numerator sequence starting with 1,0
   * instead of 0,1  (just multiply the eqn on the left by the inverse
   * matrix, which is det*[v1,-u1;-v,u], where "det" is the same as the
   * "(sign)" in (a)).  From m = v*d1 + v1*d and
   * (c) d > d1 >= 0, 0 <= v < v1,
   * we have d >= m/(2*v1), so while v1 remains smaller than m/(2*amax),
   * the pair [-(sign)*d,v] satisfies (1) but violates (2) (d > amax).
   * Conversely, v1 > bmax indicates that no further solutions will be
   * forthcoming;  [-(sign)*d,v] will be the last, and first, candidate.
   * Thus there's at most one point in the chain division where a solution
   * can live:  v < bmax, v1 >= m/(2*amax) > bmax,  and this is acceptable
   * iff in fact d <= amax  (e.g. m=221, x=34 or 35, amax=bmax=10 fail on
   * this count while x=32,33,36,37 succeed).  However, a division may leave
   * a zero residue before we ever reach this point  (consider m=210, x=35,
   * amax=bmax=10),  and our caller may find that gcd(d,v) > 1  (numerous
   * examples -- keep m=210 and consider any of x=29,31,32,33,34,36,37,38,
   * 39,40,41).
   * Furthermore, at the start of the loop body we have in fact
   * (c') 0 <= v < v1 <= bmax, d > d1 > amax >= 0,
   * (and are never done already).
   * 
   * Main loop is similar to those of invmod() and bezout(), except for
   * having to determine appropriate vmax bounds, and checking termination
   * conditions.  The signe(d1) condition is only for paranoia
   */
  while (lgefint(d) > 3 && signe(d1))
  {
    /* determine vmax for lgcdii so as to ensure v won't overshoot.
     * If v+v1 > bmax, the next step would take v1 beyond the limit, so
     * since [+-d1,v1] is not a solution, we give up.  Otherwise if v+v1
     * is way shorter than bmax, use vmax=MAXULUNG.  Otherwise, set vmax
     * to a crude lower approximation of bmax/(v+v1), or to 1, which will
     * allow the inner loop to do one step
     */
    r = addii(v,v1);
    lr = lb - lgefint(r);
    lbr = bfffo(r[2]);
    if (cmpii(r,bmax) > 0)	/* done, not found */
    {
      avma = av;
      return 0;
    }
    else if (lr > 1)		/* still more than a word's worth to go */
    {
      vmax = MAXULONG;
    }
    else			/* take difference of bit lengths */
    {
      lr = (lr << TWOPOTBITS_IN_LONG) - lbb + lbr;
      if (lr > BITS_IN_LONG)
	vmax = MAXULONG;
      else if (lr == 0)
	vmax = 1UL;
      else
	vmax = 1UL << (lr-1);
      /* the latter is pessimistic but faster than a division */
    }
    /* do a Lehmer-Jebelean round */
    lhmres = lgcdii((ulong *)d, (ulong *)d1, &xu, &xu1, &xv, &xv1, vmax);
    if (lhmres != 0)		/* check progress */
    {				/* apply matrix */
      if ((lhmres == 1) || (lhmres == -1))
      {
	s = -s;
	if (xv1 == 1)
	{
	  /* re-use v+v1 computed above */
	  v=v1; v1=r;
	  r = subii(d,d1); d=d1; d1=r;
	}
	else
	{
	  r = subii(d, mului(xv1,d1)); d=d1; d1=r;
	  r = addii(v, mului(xv1,v1)); v=v1; v1=r;
	}
      }
      else
      {
	r  = subii(muliu(d,xu),  muliu(d1,xv));
	d1 = subii(muliu(d,xu1), muliu(d1,xv1)); d = r;
	r  = addii(muliu(v,xu),  muliu(v1,xv));
	v1 = addii(muliu(v,xu1), muliu(v1,xv1)); v = r;
        if (lhmres&1)
	{
          setsigne(d,-signe(d));
	  s = -s;
        }
        else if (signe(d1))
	{
          setsigne(d1,-signe(d1));
        }
      }
      /* check whether we're done.  Assert v <= bmax here.  Examine v1:
       * if v1 > bmax, check d and return 0 or 1 depending on the outcome;
       * if v1 <= bmax, check d1 and return 1 if d1 <= amax, otherwise
       * proceed.
       */
      if (cmpii(v1,bmax) > 0) /* certainly done */
      {
	avma = av;
	if (cmpii(d,amax) <= 0) /* done, found */
	{
	  if (a != NULL)
	  {
	    *a = icopy(d);
	    setsigne(*a,-s);	/* sign opposite to s */
	  }
	  if (b != NULL) *b = icopy(v);
	  return 1;
	}
	else			/* done, not found */
	  return 0;
      }
      else if (cmpii(d1,amax) <= 0) /* also done, found */
      {
	avma = av;
	if (a != NULL)
	{
	  if (signe(d1))
	  {
	    *a = icopy(d1);
	    setsigne(*a,s);	/* same sign as s */
	  }
	  else
	    *a = gzero;
	}
	if (b != NULL) *b = icopy(v1);
	return 1;
      }
    } /* lhmres != 0 */

    if (lhmres <= 0 && signe(d1))
    {
      q = dvmdii(d,d1,&r);
#ifdef DEBUG_LEHMER
      fprintferr("Full division:\n");
      printf("  q = "); output(q); sleep (1);
#endif
      d=d1; d1=r;
      r = addii(v,mulii(q,v1));
      v=v1; v1=r;
      s = -s;
      /* check whether we are done now.  Since we weren't before the div, it
       * suffices to examine v1 and d1 -- the new d (former d1) cannot cut it
       */
      if (cmpii(v1,bmax) > 0) /* done, not found */
      {
	avma = av;
	return 0;
      }
      else if (cmpii(d1,amax) <= 0) /* done, found */
      {
	avma = av;
	if (a != NULL)
	{
	  if (signe(d1))
	  {
	    *a = icopy(d1);
	    setsigne(*a,s);	/* same sign as s */
	  }
	  else
	    *a = gzero;
	}
	if (b != NULL) *b = icopy(v1);
	return 1;
      }
    }

    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[4]; gptr[0]=&d; gptr[1]=&d1; gptr[2]=&v; gptr[3]=&v1;
      if(DEBUGMEM>1) err(warnmem,"ratlift");
      gerepilemany(av1,gptr,4);
    }
  } /* end while */

  /* Postprocessing - final sprint.  Since we usually underestimate vmax,
   * this function needs a loop here instead of a simple conditional.
   * Note we can only get here when amax fits into one word  (which will
   * typically not be the case!).  The condition is bogus -- d1 is never
   * zero at the start of the loop.  There will be at most a few iterations,
   * so we don't bother collecting garbage
   */
  while (signe(d1))
  {
    /* Assertions: lgefint(d)==lgefint(d1)==3.
     * Moreover, we aren't done already, or we would have returned by now.
     * Recompute vmax...
     */
#ifdef DEBUG_RATLIFT
    fprintferr("rl-fs: d,d1=%Z,%Z\n", d, d1);
    fprintferr("rl-fs: v,v1=%Z,%Z\n", v, v1);
#endif
    r = addii(v,v1);
    lr = lb - lgefint(r);
    lbr = bfffo(r[2]);
    if (cmpii(r,bmax) > 0)	/* done, not found */
    {
      avma = av;
      return 0;
    }
    else if (lr > 1)		/* still more than a word's worth to go */
    {
      vmax = MAXULONG;		/* (cannot in fact happen) */
    }
    else			/* take difference of bit lengths */
    {
      lr = (lr << TWOPOTBITS_IN_LONG) - lbb + lbr;
      if (lr > BITS_IN_LONG)
	vmax = MAXULONG;
      else if (lr == 0)
	vmax = 1UL;
      else
	vmax = 1UL << (lr-1);	/* as above */
    }
#ifdef DEBUG_RATLIFT
    fprintferr("rl-fs: vmax=%lu\n", vmax);
#endif
    /* single-word "Lehmer", discarding the gcd or whatever it returns */
    (void)rgcduu((ulong)d[2], (ulong)d1[2], vmax, &xu, &xu1, &xv, &xv1, &s0);
#ifdef DEBUG_RATLIFT
    fprintferr("rl-fs: [%lu,%lu; %lu,%lu] %s\n",
	       xu, xu1, xv, xv1,
	       s0 < 0 ? "-" : "+");
#endif
    if (xv1 == 1)		/* avoid multiplications */
    {
      /* re-use v+v1 computed above */
      v=v1; v1=r;
      r = subii(d,d1); d=d1; d1=r;
      s = -s;
    }
    else if (xu == 0)		/* and xv==1, xu1==1, xv1 > 1 */
    {
      r = subii(d, mului(xv1,d1)); d=d1; d1=r;
      r = addii(v, mului(xv1,v1)); v=v1; v1=r;
      s = -s;
    }
    else
    {
      r  = subii(muliu(d,xu),  muliu(d1,xv));
      d1 = subii(muliu(d,xu1), muliu(d1,xv1)); d = r;
      r  = addii(muliu(v,xu),  muliu(v1,xv));
      v1 = addii(muliu(v,xu1), muliu(v1,xv1)); v = r;
      if (s0 < 0)
      {
	setsigne(d,-signe(d));
	s = -s;
      }
      else if (signe(d1))		/* sic: might vanish now */
      {
	setsigne(d1,-signe(d1));
      }
    }
    /* check whether we're done, as above.  Assert v <= bmax.  Examine v1:
     * if v1 > bmax, check d and return 0 or 1 depending on the outcome;
     * if v1 <= bmax, check d1 and return 1 if d1 <= amax, otherwise proceed.
     */
    if (cmpii(v1,bmax) > 0) /* certainly done */
    {
      avma = av;
      if (cmpii(d,amax) <= 0) /* done, found */
      {
	if (a != NULL)
	{
	  *a = icopy(d);
	  setsigne(*a,-s);	/* sign opposite to s */
	}
	if (b != NULL) *b = icopy(v);
	return 1;
      }
      else			/* done, not found */
	return 0;
    }
    else if (cmpii(d1,amax) <= 0) /* also done, found */
    {
      avma = av;
      if (a != NULL)
      {
	if (signe(d1))
	{
	  *a = icopy(d1);
	  setsigne(*a,s);	/* same sign as s */
	}
	else
	  *a = gzero;
      }
      if (b != NULL) *b = icopy(v1);
      return 1;
    }
  } /* while */

  /* get here when we have run into d1 == 0 before returning... in fact,
   * this cannot happen.
   */
  err(talker, "ratlift failed to catch d1 == 0\n");
  /* NOTREACHED */
  return 0;
}

/********************************************************************/
/**                                                                **/
/**                      INTEGER SQUARE ROOT                       **/
/**                                                                **/
/********************************************************************/

/* sqrt()'s result may be off by 1 when a is not representable exactly as a
 * double [64bit machine] */
ulong
usqrtsafe(ulong a)
{
  ulong x = (ulong)sqrt((double)a);
#ifdef LONG_IS_64BIT
  ulong y = x+1; if (y <= MAXHALFULONG && y*y <= a) x = y;
#endif
  return x;
}

/* Assume a >= 0 has <= 4 words, return trunc[sqrt(a)] */
ulong
mpsqrtl(GEN a)
{
  long l = lgefint(a);
  ulong x,y,z,k,m;
  int L, s;
  
  if (l <= 3) return l==2? 0: usqrtsafe((ulong)a[2]);
  s = bfffo(a[2]);
  if (s > 1)
  {
    s &= ~1UL; /* make it even */
    z = BITS_IN_LONG - s;
    m = (ulong)(a[2] << s) | (a[3] >> z);
    L = z>>1;
  }
  else
  {
    m = (ulong)a[2];
    L = BITS_IN_LONG/2;
  }
  /* m = BIL-1 (bffo odd) or BIL first bits of a */
  k = (long) sqrt((double)m);
  if (L == BITS_IN_LONG/2 && k == MAXHALFULONG)
    x = MAXULONG;
  else
    x = (k+1) << L;
  do
  {
    LOCAL_HIREMAINDER;
    LOCAL_OVERFLOW;
    hiremainder = a[2];
    if (hiremainder >= x) return x;
    z = addll(x, divll(a[3],x));
    z >>= 1; if (overflow) z |= HIGHBIT;
    y = x; x = z;
  }
  while (x < y);
  return y;
}

/* target should point to a buffer of source_end - source + 1 ulongs.

   fills this buffer by bits of ulongs in source..source_end-1 shifted
   right sh units; the "most significant" sh bits of the result are
   set to be the least significant sh bits of prepend.

   The ordering of bits in this bitmap is the same as for t_INT.

   sh should not exceed BITS_IN_LONG.
 */
void
shift_r(ulong *target, ulong *source, ulong *source_end, ulong prepend, ulong sh)
{
    if (sh) {				/* shift_words_r() works */
	register ulong sh_complement = BITS_IN_LONG - sh;

	shift_words_r(target, source, source_end, prepend, sh, sh_complement);
    } else {
	int i;

	for (i=0; i < source_end - source; i++)
	    target[i] = source[i];
    }
}
