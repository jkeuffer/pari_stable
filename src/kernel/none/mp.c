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
#include "pari.h"

int pari_kernel_init(void)
{
  /*nothing to do*/
  return 0;
}

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

/***********************************************************************/
/**								      **/
/**		         ADDITION / SUBTRACTION          	      **/
/**                                                                   **/
/***********************************************************************/

INLINE GEN
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
  avma=(pari_sp)zd; return zd;
}

#define swapspec(x,y, nx,ny) {long _a=nx;GEN _z=x; nx=ny; ny=_a; x=y; y=_z;}

INLINE GEN
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
  avma=(pari_sp)zd; return zd;
}

/* assume x >= y */
INLINE GEN
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
  avma=(pari_sp)zd; return zd;
}

/* assume x > y */
INLINE GEN
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
  avma=(pari_sp)zd; return zd;
}

/* prototype of positive small ints */
static long pos_s[] = {
  evaltyp(t_INT) | _evallg(3), evalsigne(1) | evallgefint(3), 0 };

/* prototype of negative small ints */
static long neg_s[] = {
  evaltyp(t_INT) | _evallg(3), evalsigne(-1) | evallgefint(3), 0 };

static void
roundr_up_ip(GEN x, long l)
{
  long i = l;
  for(;;)
  {
    if (++x[--i]) break;
    if (i == 2) { x[2] = HIGHBIT; setexpo(x, expo(x)+1); break; }
  }
}

void
affir(GEN x, GEN y)
{
  const long s = signe(x), ly = lg(y);
  long lx, sh, i;

  if (!s)
  {
    y[1] = evalexpo(-bit_accuracy(ly));
    return;
  }

  lx = lgefint(x); sh = bfffo(x[2]);
  y[1] = evalsigne(s) | evalexpo(bit_accuracy(lx)-sh-1);
  if (sh) {
    if (lx <= ly)
    {
      for (i=lx; i<ly; i++) y[i]=0;
      shift_left(y,x,2,lx-1, 0,sh);
      return;
    }
    shift_left(y,x,2,ly-1, x[ly],sh);
    /* lx > ly: round properly */
    if ((x[ly]<<sh) & HIGHBIT) roundr_up_ip(y, ly);
  }
  else {
    if (lx <= ly)
    {
      for (i=2; i<lx; i++) y[i]=x[i];
      for (   ; i<ly; i++) y[i]=0;
      return;
    }
    for (i=2; i<ly; i++) y[i]=x[i];
    /* lx > ly: round properly */
    if (x[ly] & HIGHBIT) roundr_up_ip(y, ly);
  }
}

void
affrr(GEN x, GEN y)
{
  long lx,ly,i;

  y[1] = x[1]; if (!signe(x)) return;

  lx=lg(x); ly=lg(y);
  if (lx <= ly)
  {
    for (i=2; i<lx; i++) y[i]=x[i];
    for (   ; i<ly; i++) y[i]=0;
    return;
  }
  for (i=2; i<ly; i++) y[i]=x[i];
  /* lx > ly: round properly */
  if (x[ly] & HIGHBIT) roundr_up_ip(y, ly);
}

static GEN
shifti_spec(GEN x, long lx, long n)
{
  long ly, i, m, s = signe(x);
  GEN y;
  if (!s) return gzero;
  if (!n) 
  {
    y = cgeti(lx); 
    y[1] = evalsigne(s) | evallgefint(lx);
    while (--lx > 1) y[lx]=x[lx];
    return y;
  }
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
      /* Extend y on the left? */
      if (i) { ly++; y = new_chunk(1); y[2] = i; }
    }
  }
  else
  {
    n = -n;
    ly = lx - (n>>TWOPOTBITS_IN_LONG);
    if (ly<3) return gzero;
    y = new_chunk(ly);
    m = n & (BITS_IN_LONG-1);
    if (m) {
      shift_right(y,x, 2,ly, 0,m);
      if (y[2] == 0)
      {
        if (ly==3) { avma = (pari_sp)(y+3); return gzero; }
        ly--; avma = (pari_sp)(++y);
      }
    } else {
      for (i=2; i<ly; i++) y[i]=x[i];
    }
  }
  y[1] = evalsigne(s)|evallgefint(ly);
  y[0] = evaltyp(t_INT)|evallg(ly); return y;
}

GEN
shifti(GEN x, long n)
{
  return shifti_spec(x, lgefint(x), n);
}

GEN
shifti3(GEN x, long n, long flag)
{
  long s, lyorig, ly, i, m, lx = lgefint(x);
  GEN y = shifti_spec(x, lx, n);

  if (!flag || n >= 0 || (s = signe(x)) >= 0) return y;
  if (y == gzero) return stoi(-1);
  n = -n;
  /* With FLAG: round up instead of rounding down */
  ly = lgefint(y);
  lyorig = lx - (n>>TWOPOTBITS_IN_LONG);
  m = n & (BITS_IN_LONG-1);
  /* Check low bits of x */
  i = lx; flag = 0;
  while (--i >= lyorig)
    if (x[i]) { flag = 1; break; }  /* Need to increment y by 1 */
  if (!flag && m)
    flag = x[lyorig - 1] & ((1<<m) - 1);
  if (flag) { /* Increment y */
    for (i = ly;;)
    { /* Extend y on the left? */
      if (--i < 2) { ly++; y = new_chunk(1); y[2] = 1; break; }
      if (++y[i]) break;
      /* Now propagate the bit into the next longword */
    }
  }
  y[1] = evalsigne(s)|evallgefint(ly);
  y[0] = evaltyp(t_INT)|evallg(ly); return y;
}

GEN ishiftr_spec(GEN x, long lx, long n)
{
  /*This is a kludge since x is not an integer*/
  return shifti_spec(x, lx, n);
}


GEN ishiftr(GEN x, long s)
{
  long ex,lx,n;
  if (!signe(x)) return gzero;
  ex = expo(x) + s; if (ex < 0) return gzero;
  lx = lg(x);
  n=ex - bit_accuracy(lx) + 1;
  return ishiftr_spec(x, lx, n);
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
    return itor(x, 3 + ((-e)>>TWOPOTBITS_IN_LONG));
  }

  ly = lg(y);
  if (e > 0)
  {
    l = ly - (e>>TWOPOTBITS_IN_LONG);
    if (l<3) return rcopy(y);
  }
  else l = ly + ((-e)>>TWOPOTBITS_IN_LONG)+1;
  z = (GEN)avma;
  y = addrr(itor(x,l), y);
  ly = lg(y); while (ly--) *--z = y[ly];
  avma = (pari_sp)z; return z;
}

GEN
addrr(GEN x, GEN y)
{
  long lx, sx = signe(x), ex = expo(x);
  long ly, sy = signe(y), ey = expo(y);
  long e, i, j, lz, ez;
  int flag, f2;
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
    long m, d = e >> TWOPOTBITS_IN_LONG, l = ly-d;
    if (l > lx)     { flag=0; lz=lx+d+1; }
    else if (l > 2) { flag=1; lz=ly; lx=l; }
    else return rcopy(y);
    z = cgetr(lz);
    m = e & (BITS_IN_LONG-1);
    if (m)
    { /* shift right x m bits */
      const ulong sh = BITS_IN_LONG-m;
      GEN p1 = x; x = new_chunk(lx+1);
      shift_right2(x,p1,2,lx, 0,m,sh);
      if (flag==0)
      {
        x[lx] = p1[lx-1] << sh;
        if (x[lx]) { flag = 2; lx++; }
      }
    }
  }
  else
  {
    flag = 1;
    if (lx > ly) lx = ly;
    lz = lx;
    z = cgetr(lz);
  }

  if (sx==sy)
  { /* addition */
    i=lz-1; avma = (pari_sp)z;
    if (flag==0) { z[i] = y[i]; i--; }
    overflow=0;
    for (j=lx-1; j>=2; i--,j--) z[i] = addllx(x[j],y[i]);

    if (overflow)
      for (;;)
      {
        if (i==1)
        {
          shift_right(z,z, 2,lz, 1,1);
          z[1] = evalsigne(sx) | evalexpo(ey+1); return z;
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
      avma = (pari_sp)(z+lz);
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
  lz -= i; z += i;
  j = bfffo(z[2]); /* need to shift left by j bits to normalize mantissa */
  ez = ey - (j | (i<<TWOPOTBITS_IN_LONG));
  if (flag != 1)
  { /* z was extended by d+1 words [should be e bits = d words + m bits] */
    long m = e & (BITS_IN_LONG-1);

    /* not worth keeping extra word if less than 3 significant bits in there */
    if (m - j < 3 && lz > 3)
    { /* shorten z */
      ulong last = (ulong)z[--lz]; /* cancelled word */

      /* if we need to shift anyway, shorten from left
       * If not, shorten from right, neutralizing last word of z */
      if (j == 0) stackdummy(z + lz, 1);
      else
      {
        GEN t = z;
        z++; shift_left(z,t,2,lz-1, last,j);
      }
      if ((last<<j) & HIGHBIT)
      { /* round up */
        i = lz-1;
        while (++z[i] == 0 && i > 1) i--;
        if (i == 1) { ez++; z[2] = HIGHBIT; }
      }
    }
    else if (j) shift_left(z,z,2,lz-1, 0,j);
  }
  else if (j) shift_left(z,z,2,lz-1, 0,j);
  z[1] = evalsigne(sx) | evalexpo(ez);
  z[0] = evaltyp(t_REAL) | evallg(lz);
  avma = (pari_sp)z; return z;
}

/***********************************************************************/
/**								      **/
/**		          MULTIPLICATION                 	      **/
/**                                                                   **/
/***********************************************************************/
#define _sqri_l 47
#define _muli_l 25 /* optimal on PII 350MHz + gcc 2.7.2.1 (gp-dyn) */
#define _mulr_l 333

#if 1 /* for tunings */
long KARATSUBA_SQRI_LIMIT = _sqri_l;
long KARATSUBA_MULI_LIMIT = _muli_l;
long KARATSUBA_MULR_LIMIT = _mulr_l;

void setsqri(long a) { KARATSUBA_SQRI_LIMIT = a; }
void setmuli(long a) { KARATSUBA_MULI_LIMIT = a; }
void setmulr(long a) { KARATSUBA_MULR_LIMIT = a; }

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
#  define KARATSUBA_MULR_LIMIT _mulr_l
#endif

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
INLINE GEN
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
  avma=(pari_sp)z; return z;
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
  avma=(pari_sp)z; return z;
}

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

static GEN quickmulii(GEN a, GEN b, long na, long nb);
/*#define KARAMULR_VARIANT*/

#ifdef KARAMULR_VARIANT
static GEN addshiftw(GEN x, GEN y, long d);
static GEN
karamulrr1(GEN y, GEN x, long ly, long lz)
{
  long i, l, lz2 = (lz+2)>>1, lz3 = lz-lz2;
  GEN lo1, lo2, hi;

  hi = quickmulii(x,y, lz2,lz2);
  i = lz2; while (i<lz && !x[i]) i++;
  lo1 = quickmulii(y,x+i, lz2,lz-i);
  i = lz2; while (i<ly && !y[i]) i++;
  lo2 = quickmulii(x,y+i, lz2,ly-i);
  if (signe(lo1))
  {
    if (ly!=lz) { lo2 = addshiftw(lo1,lo2,1); lz3++; }
    else lo2 = addii(lo1,lo2);
  }
  l = lgefint(lo2)-(lz3+2);
  if (l > 0) hi = addiispec(hi+2,lo2+2, lgefint(hi)-2,l);
  return hi;
}
#endif

/* set z <-- x*y, floating point multiplication.
 * lz = lg(z) = lg(x) <= ly <= lg(y), sz = signe(z) */
INLINE void
mulrrz_i(GEN z, GEN x, GEN y, long lz, long ly, long sz)
{
  const int flag = (lz != ly);
  long ez = expo(x) + expo(y);
  long i, j, lzz, p1;
  ulong garde;
  GEN y1;
  LOCAL_HIREMAINDER;
  LOCAL_OVERFLOW;

  if (lz > KARATSUBA_MULR_LIMIT) 
  {
    pari_sp av = avma;
#ifdef KARAMULR_VARIANT
    GEN hi = karamulrr1(y+2, x+2, lz+flag-2, lz-2); 
#else
    GEN hi = quickmulii(y+2, x+2, lz+flag-2, lz-2);
#endif
    long i, garde = hi[lz];
    if (hi[2] < 0)
    {
      ez++;
      for (i=2; i<lz ; i++) z[i] = hi[i];
    }
    else
    {
      garde <<= 1;
      shift_left(z,hi,2,lz-1, garde, 1);
    }
    if (garde < 0)
    { /* round to nearest */
      i = lz; do z[--i]++; while (z[i]==0 && i > 1);
      if (i == 1) { z[2] = HIGHBIT; ez++; }
    }
    z[1] = evalsigne(sz)|evalexpo(ez);
    avma = av; return;
  }
  if (lz == 3)
  {
    if (flag)
    {
      (void)mulll(x[2],y[3]);
      garde = addmul(x[2],y[2]);
    }
    else
      garde = mulll(x[2],y[2]);
    if (hiremainder & HIGHBIT)
    {
      ez++;
      /* hiremainder < (2^BIL-1)^2 / 2^BIL, hence hiremainder+1 != 0 */
      if (garde & HIGHBIT) hiremainder++; /* round properly */
    }
    else
    {
      hiremainder = (hiremainder<<1) | (garde>>(BITS_IN_LONG-1));
      if (garde & (HIGHBIT-1))
      {
        hiremainder++; /* round properly */
        if (!hiremainder) { hiremainder = HIGHBIT; ez++; }
      }
    }
    z[1] = evalsigne(sz) | evalexpo(ez);
    z[2] = hiremainder; return;
  }

  if (flag) { (void)mulll(x[2],y[lz]); garde = hiremainder; } else garde = 0;
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
  p1 = x[2]; y1++;
  garde = addll(mulll(p1,y1[lz]), garde);
  for (i=lzz; i>2; i--)
  {
    hiremainder += overflow;
    z[i] = addll(addmul(p1,y1[i]), z[i]);
  }
  z[2] = hiremainder+overflow;
  if (z[2] < 0) ez++; else shift_left(z,z,2,lzz,garde, 1);
  z[1] = evalsigne(sz) | evalexpo(ez);
}

GEN
mulrr(GEN x, GEN y)
{
  long ly, lz, sx = signe(x), sy = signe(y);
  GEN z;

  if (!sx || !sy) return realzero_bit(expo(x) + expo(y));
  if (sy < 0) sx = -sx;
  lz = lg(x);
  ly = lg(y); if (lz > ly) { lz = ly; z = x; x = y; y = z; }
  z = cgetr(lz);
  mulrrz_i(z, x,y, lz,ly, sx);
  return z;
}

GEN
mulir(GEN x, GEN y)
{
  long sx = signe(x), sy, lz;
  GEN z;

  if (!sx) return gzero;
  if (!is_bigint(x)) return mulsr(itos(x), y);
  sy = signe(y);
  if (!sy) return realzero_bit(expi(x) + expo(y));
  if (sy < 0) sx = -sx;
  lz = lg(y);
  z = cgetr(lz);
  mulrrz_i(z, itor(x,lz),y, lz,lz, sx);
  avma = (pari_sp)z; return z;
}

/***********************************************************************/
/**								      **/
/**		          DIVISION                       	      **/
/**                                                                   **/
/***********************************************************************/

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
  hiremainder=0; (void)divll(labs(x),y);
  if (!hiremainder) return gzero;
  return (x < 0) ? stoi(y-hiremainder) : stoi(hiremainder);
}

GEN
resss(long x, long y)
{
  LOCAL_HIREMAINDER;

  if (!y) err(reser1);
  hiremainder=0; (void)divll(labs(x),labs(y));
  return (x < 0) ? stoi(-((long)hiremainder)) : stoi(hiremainder);
}

GEN
divsi_rem(long x, GEN y, ulong *rem)
{
  long p1, s = signe(y);
  LOCAL_HIREMAINDER;

  if (!s) err(diver2);
  if (!x || lgefint(y)>3 || ((long)y[2])<0) { *rem = x; return gzero; }
  hiremainder=0; p1=divll(labs(x),y[2]);
  if (x<0) { hiremainder = -((long)hiremainder); p1 = -p1; }
  if (s<0) p1 = -p1;
  *rem = hiremainder; return stoi(p1);
}

GEN
divsi(long x, GEN y)
{
  long p1, s = signe(y);
  LOCAL_HIREMAINDER;

  if (!s) err(diver2);
  if (!x || lgefint(y)>3 || ((long)y[2])<0) return gzero;
  hiremainder=0; p1=divll(labs(x),y[2]);
  if (x<0) { hiremainder = -((long)hiremainder); p1 = -p1; }
  if (s<0) p1 = -p1;
  return stoi(p1);
}

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

/* return |y| \/ x */
GEN
diviu_rem(GEN y, ulong x, ulong *rem)
{
  long ly,i;
  GEN z;
  LOCAL_HIREMAINDER;

  if (!x) err(diver4);
  if (!signe(y)) { *rem = 0; return gzero; }

  ly = lgefint(y);
  if (x <= (ulong)y[2]) hiremainder=0;
  else
  {
    if (ly==3) { *rem = (ulong)y[2]; return gzero; }
    hiremainder=y[2]; ly--; y++;
  }
  z = cgeti(ly); z[1] = evallgefint(ly) | evalsigne(1);
  for (i=2; i<ly; i++) z[i]=divll(y[i],x);
  *rem = hiremainder; return z;
}

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
divis_rem(GEN y, long x, ulong *rem)
{
  long sy=signe(y),ly,s,i;
  GEN z;
  LOCAL_HIREMAINDER;

  if (!x) err(diver4);
  if (!sy) { *rem=0; return gzero; }
  if (x<0) { s = -sy; x = -x; } else s = sy;

  ly = lgefint(y);
  if ((ulong)x <= (ulong)y[2]) hiremainder=0;
  else
  {
    if (ly==3) { *rem = itos(y); return gzero; }
    hiremainder=y[2]; ly--; y++;
  }
  z = cgeti(ly); z[1] = evallgefint(ly) | evalsigne(s);
  for (i=2; i<ly; i++) z[i]=divll(y[i],x);
  if (sy<0) hiremainder = - ((long)hiremainder);
  *rem = hiremainder; return z;
}

GEN
divis(GEN y, long x)
{
  long sy=signe(y),ly,s,i;
  GEN z;
  LOCAL_HIREMAINDER;

  if (!x) err(diver4);
  if (!sy) return gzero;
  if (x<0) { s = -sy; x = -x; } else s = sy;

  ly = lgefint(y);
  if ((ulong)x <= (ulong)y[2]) hiremainder=0;
  else
  {
    if (ly==3) return gzero;
    hiremainder=y[2]; ly--; y++;
  }
  z = cgeti(ly); z[1] = evallgefint(ly) | evalsigne(s);
  for (i=2; i<ly; i++) z[i]=divll(y[i],x);
  return z;
}

GEN
divir(GEN x, GEN y)
{
  GEN z;
  long ly;
  pari_sp av;

  if (!signe(y)) err(diver5);
  if (!signe(x)) return gzero;
  ly = lg(y); z = cgetr(ly); av = avma; 
  affrr(divrr(itor(x, ly+1), y), z);
  avma = av; return z;
}

GEN
divri(GEN x, GEN y)
{
  long lx, s = signe(y);
  pari_sp av;
  GEN z;

  if (!s) err(diver8);
  if (!signe(x)) return realzero_bit(expo(x) - expi(y));
  if (!is_bigint(y)) return divrs(x, s>0? y[2]: -y[2]);

  lx = lg(x); z = cgetr(lx); av = avma;
  affrr(divrr(x, itor(y, lx+1)), z);
  avma = av; return z;
}

void
diviiz(GEN x, GEN y, GEN z)
{
  pari_sp av = avma;
  if (typ(z) == t_INT) affii(divii(x,y), z);
  else {
    long lz = lg(z);
    affrr(divrr(itor(x,lz), itor(y,lz)), z);
  }
  avma = av;
}

void
mpdivz(GEN x, GEN y, GEN z)
{
  pari_sp av = avma;
  GEN r;

  if (typ(z)==t_INT)
  {
    if (typ(x) == t_REAL || typ(y) == t_REAL) err(divzer1);
    affii(divii(x,y), z);
    avma = av; return;
  }

  if (typ(x) == t_INT)
  {
    if (typ(y) == t_REAL)
      r = divir(x,y);
    else
    {
      long lz = lg(z);
      r = divrr(itor(x,lz), itor(y,lz));
    }
  }
  else if (typ(y) == t_REAL)
    r = divrr(x,y);
  else
    r = divri(x,y);
  affrr(r, z); avma = av;
}

GEN
divsr(long x, GEN y)
{
  pari_sp av;
  long ly;
  GEN z;

  if (!signe(y)) err(diver3);
  if (!x) return gzero;
  ly = lg(y); z = cgetr(ly); av = avma;
  affrr(divrr(stor(x,ly+1), y), z);
  avma = av; return z;
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
      pari_sp av = avma;
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
  const pari_sp av = avma;
  affii(modii(x,y),z); avma=av;
}

GEN
divrs(GEN x, long y)
{
  long i,lx,garde,sh,s=signe(x);
  GEN z;
  LOCAL_HIREMAINDER;

  if (!y) err(diver6);
  if (!s) return realzero_bit(expo(x) - (BITS_IN_LONG-1)+bfffo(y));
  if (y<0) { s = -s; y = -y; }
  if (y==1) { z=rcopy(x); setsigne(z,s); return z; }

  z=cgetr(lx=lg(x)); hiremainder=0;
  for (i=2; i<lx; i++) z[i]=divll(x[i],y);

  /* we may have hiremainder != 0 ==> garde */
  garde=divll(0,y); sh=bfffo(z[2]);
  if (sh) shift_left(z,z, 2,lx-1, garde,sh);
  z[1] = evalsigne(s) | evalexpo(expo(x)-sh);
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
  /* i = lz-1 */
  /* round correctly */
  if ((ulong)x1[1] > si>>1)
  {
    j=i; do x[--j]++; while (j && !x[j]);
  }
  x1 = x-1; for (j=i; j>=2; j--) x[j]=x1[j];
  if (*x == 0) e--;
  else if (*x == 1) { shift_right(x,x, 2,lz, 1,1); }
  else { /* possible only when rounding up to 0x2 0x0 ... */
    x[2] = HIGHBIT; e++;
  }
  x[0] = evaltyp(t_REAL)|evallg(lz);
  x[1] = evalsigne(sx) | evalexpo(e);
  return x;
}

/* Integer division x / y: such that sign(r) = sign(x)
 *   if z = ONLY_REM return remainder, otherwise return quotient
 *   if z != NULL set *z to remainder
 *   *z is the last object on stack (and thus can be disposed of with cgiv
 *   instead of gerepile)
 * If *z is zero, we put gzero here and no copy.
 * space needed: lx + ly */
GEN
dvmdii(GEN x, GEN y, GEN *z)
{
  long sx=signe(x),sy=signe(y);
  long lx, ly, lz, i, j, sh, k, lq, lr;
  pari_sp av;
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
    avma = (pari_sp)qd; return (GEN)qd;
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
    avma = (pari_sp)rd; return (GEN)rd;
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
  avma = (pari_sp)qd; return q;
}

GEN
truedvmdii(GEN x, GEN y, GEN *z)
{
  pari_sp av = avma;
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
  gptr[0]=&q; gptr[1]=z; gerepilemanysp(av,(pari_sp)r,gptr,2);
  return q;
}

/* Montgomery reduction.
 * N has k words, assume T >= 0 has less than 2k.
 * Return res := T / B^k mod N, where B = 2^BIL
 * such that 0 <= res < T/B^k + N  and  res has less than k words */
GEN
red_montgomery(GEN T, GEN N, ulong inv)
{
  pari_sp av;
  GEN Te, Td, Ne, Nd, scratch;
  ulong i, j, m, t, d, k = lgefint(N)-2;
  int carry;
  LOCAL_HIREMAINDER;
  LOCAL_OVERFLOW;

  if (k == 0) return gzero;
  d = lgefint(T)-2; /* <= 2*k */
#ifdef DEBUG
  if (d > 2*k) err(bugparier,"red_montgomery");
#endif
  if (k == 1)
  { /* as below, special cased for efficiency */
    ulong n = (ulong)N[2];
    t = (ulong)T[d+1];
    m = t * inv;
    (void)addll(mulll(m, n), t); /* = 0 */
    t = hiremainder + overflow;
    if (d == 2)
    {
      t = addll((ulong)T[2], t);
      if (overflow) t -= n; /* t > n doesn't fit in 1 word */
    }
    return utoi(t);
  }
  /* assume k >= 2 */
  av = avma; scratch = new_chunk(k<<1); /* >= k + 2: result fits */

  /* copy T to scratch space (pad with zeroes to 2k words) */
  Td = (GEN)av;
  Te = T + (d+2);
  for (i=0; i < d     ; i++) *--Td = *--Te;
  for (   ; i < (k<<1); i++) *--Td = 0;

  Te = (GEN)av; /* 1 beyond end of T mantissa */
  Ne = N + k+2; /* 1 beyond end of N mantissa */

  carry = 0;
  for (i=0; i<k; i++) /* set T := T/B nod N, k times */
  {
    Td = Te; /* one beyond end of (new) T mantissa */
    Nd = Ne;
    m = *--Td * inv; /* solve T + m N = O(B) */

    /* set T := (T + mN) / B */
    Te = Td;
    (void)addll(mulll(m, *--Nd), *Td); /* = 0 */
    for (j=1; j<k; j++)
    {
      hiremainder += overflow;
      t = addll(addmul(m, *--Nd), *--Td); *Td = t;
    }
    overflow += hiremainder;
    t = addll(overflow, *--Td); *Td = t + carry;
    carry = (overflow || (carry && *Td == 0));
  }
  if (carry)
  { /* Td > N overflows (k+1 words), set Td := Td - N */
    Td = Te;
    Nd = Ne;
    t = subll(*--Td, *--Nd); *Td = t;
    while (Td > scratch) { t = subllx(*--Td, *--Nd); *Td = t; }
  }

  /* copy result */
  Td = (GEN)av;
  while (! *scratch) scratch++; /* strip leading zeroes */
  while (Te > scratch) *--Td = *--Te;
  k = ((GEN)av - Td) + 2;
  *--Td = evalsigne(1) | evallgefint(k);
  *--Td = evaltyp(t_INT) | evallg(k);
#ifdef DEBUG
{
  long l = lgefint(N)-2, s = BITS_IN_LONG*l;
  GEN R = shifti(gun, s);
  GEN res = resii(mulii(T, mpinvmod(R, N)), N);
  if (k > lgefint(N)
    || !egalii(resii(Td,N),res)
    || cmpii(Td, addii(shifti(T, -s), N)) >= 0) err(bugparier,"red_montgomery");
}
#endif
  avma = (pari_sp)Td; return Td;
}

/* EXACT INTEGER DIVISION */

/* assume xy>0, y odd */
GEN
diviuexact(GEN x, ulong y)
{
  long i,lz,lx;
  ulong q, yinv;
  GEN z, z0, x0, x0min;

  if (y == 1) return icopy(x);
  lx = lgefint(x);
  if (lx == 3) return utoi((ulong)x[2] / y);
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
  avma = (pari_sp)z; return z;
}

/* Find z such that x=y*z, knowing that y | x (unchecked)
 * Method: y0 z0 = x0 mod B = 2^BITS_IN_LONG ==> z0 = 1/y0 mod B.
 *    Set x := (x - z0 y) / B, updating only relevant words, and repeat */
GEN
diviiexact(GEN x, GEN y)
{
  long lx, ly, lz, vy, i, ii, sx = signe(x), sy = signe(y);
  pari_sp av;
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
  avma = (pari_sp)z; return z;
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
/* nx >= ny = num. of digits of x, y (not GEN, see mulii) */
INLINE GEN
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
  avma=(pari_sp)zd; return zd;
}

INLINE GEN
sqrispec(GEN x, long nx)
{
  GEN z2e,z2d,yd,xd,zd,x0,z0;
  long p1,lz;
  LOCAL_HIREMAINDER;
  LOCAL_OVERFLOW;

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
  avma=(pari_sp)zd; return zd;
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
  long n0, n0a, i;
  pari_sp av;

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
  long k;
  pari_sp av = avma;

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
  long n0, n0a, i;
  pari_sp av;

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

/* Old cgiv without reference count (which was not used anyway)
 * Should be a macro.
 */
void
cgiv(GEN x)
{
  if (x == (GEN) avma)
    avma = (pari_sp) (x+lg(x));
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

/* Assume a has <= 4 words, return trunc[sqrt(abs(a))] */
static ulong
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

/* Use l as lgefint(a) [a may have more digits] */
static GEN
racine_r(GEN a, long l)
{
  pari_sp av;
  long s;
  GEN x,y,z;

  if (l <= 4) return utoi(mpsqrtl(a));
  av = avma;
  s = 2 + ((l-1) >> 1);
  setlgefint(a, s);
  x = addis(racine_r(a, s), 1); setlgefint(a, l);
  /* x = good approx (from above) of sqrt(a): about l/2 correct bits */
  x = shifti(x, (l - s)*(BITS_IN_LONG/2));
  do
  { /* one or two iterations should do the trick */
    z = shifti(addii(x,divii(a,x)), -1);
    y = x; x = z;
  }
  while (cmpii(x,y) < 0);
  avma = (pari_sp)y;
  return gerepileuptoint(av,y);
}

/* Return trunc(sqrt(abs(a)))). a must be an integer*/
GEN isqrti(GEN a) {return racine_r(a,lgefint(a));}

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

/* Normalize a non-negative integer.  */
GEN
int_normalize(GEN x, long known_zero_words)
{
  long lx = lgefint(x);
  long i = 2 + known_zero_words;
  for ( ; i < lx; i++)
    if (x[i]) 
    {
      if (i != 2)
      {
        GEN x0 = x;
        i -= 2; x += i;
        if (x0 == (GEN)avma) avma = (pari_sp)x; else stackdummy(x0, i);
        lx -= i;
        x[0] = evaltyp(t_INT) | evallg(lx);
        x[1] = evalsigne(1) | evallgefint(lx);
      }
      return x;
    }
  x[1] = evalsigne(0) | evallgefint(2); return x;
}
