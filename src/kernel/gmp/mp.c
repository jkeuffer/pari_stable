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
/**		                GMP KERNEL                     	      **/
/**                                                                   **/
/** BA2002Sep24                                                       **/
/***********************************************************************/
/*
 * GMP t_INT as just like normal t_INT, just the mantissa is the other way
 * round
 *
 * 
 *   `How would you like to live in Looking-glass House, Kitty?  I
 *   wonder if they'd give you milk in there?  Perhaps Looking-glass
 *   milk isn't good to drink--But oh, Kitty! now we come to the
 *   passage.  You can just see a little PEEP of the passage in
 *   Looking-glass House, if you leave the door of our drawing-room
 *   wide open:  and it's very like our passage as far as you can see,
 *   only you know it may be quite different on beyond.  Oh, Kitty!
 *   how nice it would be if we could only get through into Looking-
 *   glass House!  I'm sure it's got, oh! such beautiful things in it!
 *                                                                             
 *  Through the Looking Glass,  Lewis Carrol
 *  
 *  (pityful attempt to beat GN code/comments rate)
 *  */

#include "pari.h"
#include <gmp.h>

#ifndef REGISTER_MP_OPERANDS
ulong overflow;
ulong hiremainder;
#endif

void setmontgomerylimit(long n); 
int pari_kernel_init(void)
{
  /*Montgomery mult is not supported*/
  setmontgomerylimit(0);
  /*setresiilimit(50);*/
  /* Use gpmalloc instead of malloc */
  mp_set_memory_functions((void *(*)(unsigned int)) gpmalloc
		  	,(void *(*)(void *, unsigned int, unsigned int)) gprealloc
		        ,NULL);

  return 0;
}

#define LIMBS(x)  ((mp_limb_t *)((x)+2))
#define NLIMBS(x) (lgefint(x)-2)

#ifdef INLINE
INLINE
#endif
void
xmpn_copy(mp_limb_t *x, mp_limb_t *y, long n)
{
  while (--n >= 0) x[n]=y[n];
}

#ifdef INLINE
INLINE
#endif
void
xmpn_mirror(mp_limb_t *x, long n)
{
  long i;
  for(i=0;i<(n>>1);i++)
  {
    ulong m=x[i];
    x[i]=x[n-1-i];
    x[n-1-i]=m;
  }
}

#ifdef INLINE
INLINE
#endif
GEN
icopy_ef(GEN x, long l)
{
  register long lx = lgefint(x);
  const GEN y = cgeti(l);

  while (--lx > 0) y[lx]=x[lx];
  return y;
}

/* NOTE: arguments of "spec" routines (muliispec, addiispec, etc.) aren't
 * GENs but pairs (long *a, long na) representing a list of digits (in basis
 * BITS_IN_LONG) : a[0], ..., a[na-1]. [ In ordre to facilitate splitting: no
 * need to reintroduce codewords ]
 * Use speci(a,na) to visualize the corresponding GEN.
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
  if (MASK(x[1]) != MASK(y[1])) return 0;
  return !mpn_cmp(LIMBS(x),LIMBS(y),NLIMBS(x)); /* Note that NLIMBS(x)==NLIMBS(y)*/
}
#undef MASK

/***********************************************************************/
/**								      **/
/**		         ADDITION / SUBTRACTION          	      **/
/**                                                                   **/
/***********************************************************************/

#ifdef INLINE
INLINE
#endif
GEN
addsispec(long s, GEN x, long nx)
{
  GEN  zd;
  long lz;

  lz = nx+3; zd = cgeti(lz);
  if (mpn_add_1(LIMBS(zd),(mp_limb_t *)x,nx,s))
    zd[lz-1]=1;
  else
    lz--;
  zd[1] = evalsigne(1) | evallgefint(lz);
  return zd;
}

#define swapspec(x,y, nx,ny) {long _a=nx;GEN _z=x; nx=ny; ny=_a; x=y; y=_z;}

#ifdef INLINE
INLINE
#endif
GEN
addiispec(GEN x, GEN y, long nx, long ny)
{
  GEN zd;
  long lz;

  if (nx < ny) swapspec(x,y, nx,ny);
  if (ny == 1) return addsispec(*y,x,nx);
  lz = nx+3; zd = cgeti(lz);

  if (mpn_add(LIMBS(zd),(mp_limb_t *)x,nx,(mp_limb_t *)y,ny))
    zd[lz-1]=1;
  else
    lz--;

  zd[1] = evalsigne(1) | evallgefint(lz);
  return zd;
}

/* assume x >= y */
#ifdef INLINE
INLINE
#endif
GEN
subisspec(GEN x, long s, long nx)
{
  GEN zd;
  long lz;
  lz = nx + 2; zd = cgeti(lz);
  
  mpn_sub_1 (LIMBS(zd), (mp_limb_t *)x, nx, s);
  if (! zd[lz - 1]) { --lz; }

  zd[1] = evalsigne(1) | evallgefint(lz);
  return zd;
}

/* assume x > y */
#ifdef INLINE
INLINE
#endif
GEN
subiispec(GEN x, GEN y, long nx, long ny)
{
  GEN zd;
  long lz;
  if (ny==1) return subisspec(x,*y,nx);
  lz = nx+2; zd = cgeti(lz);
  
  mpn_sub (LIMBS(zd), (mp_limb_t *)x, nx, (mp_limb_t *)y, ny);
  while (lz >= 3 && zd[lz - 1] == 0) { lz--; }
  
  zd[1] = evalsigne(1) | evallgefint(lz);
  return zd;
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
  lx = lgefint(x); sh = bfffo(*int_MSW(x));
  y[1] = evalsigne(s) | evalexpo(bit_accuracy(lx)-sh-1);
  if (sh) {
    if (lx <= ly)
    {
      for (i=lx; i<ly; i++) y[i]=0;
      if(mpn_lshift(LIMBS(y),LIMBS(x),lx-2,sh)) err(talker,"GMP affir 2");
      xmpn_mirror(LIMBS(y),lx-2);
      return;
    }
    if(mpn_lshift(LIMBS(y),LIMBS(x)+lx-ly,ly-2,sh)) err(talker,"GMP affir 1");
    y[2]|=((ulong) x[lx-ly+1])>>(BITS_IN_LONG-sh);
    xmpn_mirror(LIMBS(y),ly-2);
    /* lx > ly: round properly */
    if ((x[lx-ly+1]<<sh) & HIGHBIT) roundr_up_ip(y, ly);
  }
  else {
    GEN xd=int_MSW(x);
    if (lx <= ly)
    {
      for (i=2; i<lx; i++,xd=int_precW(xd)) y[i]=*xd;
      for (   ; i<ly; i++) y[i]=0;
      return;
    }
    for (i=2; i<ly; i++,xd=int_precW(xd)) y[i]=*xd;
    /* lx > ly: round properly */
    if (x[2+lx-ly] & HIGHBIT) roundr_up_ip(y, ly);
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

GEN
shifti(GEN x, long n)
{
  const long s=signe(x);
  long lz,lx,m;
  GEN z;

  if (!s) return gzero;
  if (!n) return icopy(x);
  lx = lgefint(x);
  if (n > 0)
  {
    long d = n>>TWOPOTBITS_IN_LONG;
    long i;

    m = n & (BITS_IN_LONG-1);

    lz = lx + d + (m!=0);  
    z = cgeti(lz); 
    for (i=0; i<d; i++) LIMBS(z)[i] = 0;

    if (!m) xmpn_copy(LIMBS(z)+d, LIMBS(x), NLIMBS(x)); 
    else
    {
      ulong carry = mpn_lshift(LIMBS(z)+d, LIMBS(x), NLIMBS(x), m); 
      if (carry) z[lz - 1] = carry; 
      else lz--; 
    }
  }
  else
  {
    long d = (-n)>>TWOPOTBITS_IN_LONG;

    n = -n;
    lz = lx - d;
    if (lz<3) return gzero;
    z = cgeti(lz);
    m = n & (BITS_IN_LONG-1);

    if (!m) xmpn_copy(LIMBS(z), LIMBS(x) + d, NLIMBS(x) - d);
    else
    {
      mpn_rshift(LIMBS(z), LIMBS(x) + d, NLIMBS(x) - d, m); 
      if (z[lz - 1] == 0)
      {
        if (lz == 3) { avma = (pari_sp)(z+3); return gzero; }
        lz--; 
      }
    }
  }
  z[1] = evalsigne(s)|evallgefint(lz);
  return z;
}

GEN
shifti3(GEN x, long n, long flag)
{
  long s, lyorig, ly, i, m, lx = lgefint(x);
  GEN y = shifti(x, n);

  if (!flag || n >= 0 || (s = signe(x)) >= 0) return y;
  if (y == gzero) return stoi(-1);
  err(impl,"GMP shifti3");
  n = -n;
  /* With FLAG: round up instead of rounding down */
  ly = lgefint(y);
  lyorig = lx - (n>>TWOPOTBITS_IN_LONG);
  m = n & (BITS_IN_LONG-1);
  /* Check low bits of x */
  i = lx; flag = 0;
  while (--i >= lyorig)
    if (x[lx-i]) { flag = 1; break; }  /* Need to increment y by 1 */
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

GEN
ishiftr_spec(GEN x, long lx, long n)
{
  long ly, i, m, s = signe(x);
  GEN y;
  if (!s) return gzero;
  if (!n) 
  {
    y = cgeti(lx); /* cf icopy. But applies to a t_REAL! */
    y[1] = evalsigne(s) | evallgefint(lx);
    while (--lx > 1) y[lx]=x[lx];
    xmpn_mirror(LIMBS(y),NLIMBS(y));
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
  xmpn_mirror(LIMBS(y),ly-2);
  y[1] = evalsigne(s)|evallgefint(ly);
  y[0] = evaltyp(t_INT)|evallg(ly); return y;
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
  long d,e,m,i,s;
  GEN y;

  if (typ(x)==t_INT) return icopy(x);
  if ((s=signe(x)) == 0 || (e=expo(x)) < 0) return gzero;
  d = (e>>TWOPOTBITS_IN_LONG) + 3;
  m = e & (BITS_IN_LONG-1);
  if (d > lg(x)) err(precer, "mptrunc (precision loss in truncation)");

  y=cgeti(d); y[1] = evalsigne(s) | evallgefint(d);
  if (++m == BITS_IN_LONG)
    for (i=2; i<d; i++) y[d-i+1]=x[i];
  else
  {
    GEN z=cgeti(d);
    for (i=2; i<d; i++) z[d-i+1]=x[i];
    mpn_rshift(LIMBS(y),LIMBS(z),d-2,BITS_IN_LONG-m);
    avma=(pari_sp)y;
  }
  return y;
}

/* integral part */
GEN
mpent(GEN x)
{
  GEN y;
  long d,e,m,i,lx;
  if (typ(x)==t_INT) return icopy(x);
  if (signe(x) >= 0) return mptrunc(x);
  if ((e=expo(x)) < 0) return stoi(-1);
  d = (e>>TWOPOTBITS_IN_LONG) + 3;
  m = e & (BITS_IN_LONG-1);
  lx=lg(x); if (d>lx) err(precer, "mpent (precision loss in trucation)");
  y = cgeti(d+1);
  if (++m == BITS_IN_LONG)
  {
    for (i=2; i<d; i++) y[d-i+1]=x[i];
    i=d; while (i<lx && !x[i]) i++;
    if (i==lx) goto END;
  }
  else
  {
    GEN z=cgeti(d);
    for (i=2; i<d; i++) z[d-i+1]=x[i];
    mpn_rshift(LIMBS(y),LIMBS(z),d-2,BITS_IN_LONG-m);
    if (x[d-1]<<m == 0)
    {
      i=d; while (i<lx && !x[i]) i++;
      if (i==lx) goto END;
    }
  }
  if (mpn_add_1(LIMBS(y),LIMBS(y),d,1))
    y[d++]=1; 
END:
  y[1] = evalsigne(-1) | evallgefint(d);
  return y;
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
  long lx,ly;

  if (sx<sy) return -1;
  if (sx>sy) return 1;
  if (!sx) return 0;

  lx=lgefint(x); ly=lgefint(y);
  if (lx>ly) return sx;
  if (lx<ly) return -sx;
  if (sx>0)
    return mpn_cmp(LIMBS(x),LIMBS(y),NLIMBS(x));
  else
    return -mpn_cmp(LIMBS(x),LIMBS(y),NLIMBS(x));
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

#define _sqri_l -1
#define _muli_l -1
#define _mulr_l 72

#if 1 /* for tunings */
long KARATSUBA_SQRI_LIMIT = _sqri_l;
long KARATSUBA_MULI_LIMIT = _muli_l;
long KARATSUBA_MULR_LIMIT = _mulr_l;

void setsqri(long a) {} /*NOOP*/ 
void setmuli(long a) {} /*NOOP*/
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
    z[3]=hiremainder; z[2]=p1; return z;
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
    z[3]=hiremainder; z[2]=p1; return z;
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
  long lz = ny+3;
  GEN z=cgeti(lz);
  ulong hi = mpn_mul_1 (LIMBS(z), (mp_limb_t *)y, ny, x);
  if (hi) { z[lz - 1] = hi; } else lz--;
  z[1] = evalsigne(1) | evallgefint(lz);
  return z;
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

/* a + b*Y, assume y >= 0, 0 <= a,b <= VERYBIGINT */
GEN
addsmulsi(long a, long b, GEN y)
{
  GEN z;
  long i, lz;
  ulong hi;
  if (!signe(y)) return stoi(a);
  lz = lgefint(y)+1;
  z = cgeti(lz);
  z[2]=a;
  for(i=3;i<lz;i++) z[i]=0;
  hi=mpn_addmul_1(LIMBS(z), LIMBS(y), NLIMBS(y), b);
  if (hi) z[lz-1]=hi; else lz--;
  z[1] = evalsigne(1) | evallgefint(lz);
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

#ifdef INLINE
INLINE
#endif
GEN
muliispec(GEN x, GEN y, long nx, long ny);

#ifdef INLINE
INLINE
#endif
GEN
quickmulii(GEN x, GEN y, long nx, long ny)
{
  GEN z;
  xmpn_mirror((mp_limb_t *)x,nx);
  if (x!=y) xmpn_mirror((mp_limb_t *)y,ny);
  z=muliispec(x, y, nx, ny);
  xmpn_mirror(LIMBS(z),NLIMBS(z));
  xmpn_mirror((mp_limb_t *)x,nx);
  if (x!=y) xmpn_mirror((mp_limb_t *)y,ny);
  return z;
}

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
#ifdef INLINE
INLINE
#endif
void
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
  long sy=signe(y);
  long hi;
  if (!x) err(diver4);
  if (!sy) return 0;
  hi = mpn_mod_1(LIMBS(y),NLIMBS(y),x);
  if (!hi) return 0;
  return (sy > 0)? hi: x - hi;
}

GEN
modiu(GEN y, ulong x) { return utoi(umodiu(y,x)); }

/* return |y| \/ x */
GEN
diviu(GEN y, ulong x)
{
  long sy=signe(y),ly;
  GEN z;
  LOCAL_HIREMAINDER;

  if (!x) err(diver4);
  if (!sy) { hiremainder=0; SAVE_HIREMAINDER; return gzero; }

  ly = lgefint(y);
  if (ly == 3 && (ulong)x > (ulong)y[2])
    { hiremainder = itou(y); SAVE_HIREMAINDER; return gzero; }

  z = cgeti(ly); 
  hiremainder = mpn_divrem_1(LIMBS(z), 0, LIMBS(y), NLIMBS(y), x);
  if (z [ly - 1] == 0) ly--;
  z[1] = evallgefint(ly) | evalsigne(1);
  SAVE_HIREMAINDER; return z;
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
divis(GEN y, long x)
{
  long sy=signe(y),ly,s;
  GEN z;
  LOCAL_HIREMAINDER;

  if (!x) err(diver4);
  if (!sy) { hiremainder=0; SAVE_HIREMAINDER; return gzero; }
  if (x<0) { s = -sy; x = -x; } else s=sy;

  ly = lgefint(y);
  if (ly == 3 && (ulong)x > (ulong)y[2])
  { hiremainder = itos(y); SAVE_HIREMAINDER; return gzero; }

  z = cgeti(ly); 
  hiremainder = mpn_divrem_1(LIMBS(z), 0, LIMBS(y), NLIMBS(y), x);
  if (sy<0) hiremainder = - ((long)hiremainder);
  if (z[ly - 1] == 0) ly--;
  z[1] = evallgefint(ly) | evalsigne(s);
  SAVE_HIREMAINDER; return z;
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
  if (x1[1] > si>>1)
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
  long lx, ly, lq;
  pari_sp av;
  GEN r,q;

  if (!sy) err(dvmer1);
  if (!sx)
  {
    if (!z || z == ONLY_REM) return gzero;
    *z=gzero; return gzero;
  }
  lx=lgefint(x);
  ly=lgefint(y); lq=lx-ly;
  if (lq <= 0)
  {
    if (lq == 0)
    {
      long s=mpn_cmp(LIMBS(x),LIMBS(y),NLIMBS(x));
      if (s>0) goto DIVIDE;
      if (s==0) 
      {
        if (z == ONLY_REM) return gzero;
        if (z) *z = gzero;
        if (sx < 0) sy = -sy;
        return stoi(sy);
      }
    }
    if (z == ONLY_REM) return icopy(x);
    if (z) *z = icopy(x);
    return gzero;
  }
DIVIDE: /* quotient is non-zero */
  av=avma; if (sx<0) sy = -sy;
  if (ly==3)
  {
    ulong lq = lx;
    ulong si;
    q  = cgeti(lq);
    si = mpn_divrem_1(LIMBS(q), 0, LIMBS(x), NLIMBS(x), y[2]);
    if (q[lq - 1] == 0) lq--;
    if (z == ONLY_REM)
    {
      avma=av; if (!si) return gzero;
      r=cgeti(3);
      r[1] = evalsigne(sx) | evallgefint(3);
      r[2] = si; return r;
    }
    q[1] = evalsigne(sy) | evallgefint(lq);
    if (!z) return q;
    if (!si) { *z=gzero; return q; }
    r=cgeti(3);
    r[1] = evalsigne(sx) | evallgefint(3);
    r[2] = si; *z=r; return q;
  }
  if (z == ONLY_REM)
  {
    ulong lr = lgefint(y);
    ulong lq = lgefint(x)-lgefint(y)+3;
    GEN r = cgeti(lr);
    GEN q = cgeti(lq);
    mpn_tdiv_qr(LIMBS(q), LIMBS(r),0, LIMBS(x), NLIMBS(x), LIMBS(y), NLIMBS(y));
    if (!r[lr - 1])
    {
      while(lr>2 && !r[lr - 1]) lr--;
      if (lr == 2) {avma=av; return gzero;} /* exact division */
    }
    r[1] = evalsigne(sx) | evallgefint(lr);
    avma = (pari_sp) r; return r; 
  }
  else
  {
    ulong lq = lgefint(x)-lgefint(y)+3;
    ulong lr = lgefint(y);
    GEN q = cgeti(lq);
    GEN r = cgeti(lr);
    mpn_tdiv_qr(LIMBS(q), LIMBS(r),0, LIMBS(x), NLIMBS(x), LIMBS(y), NLIMBS(y));
    if (q[lq - 1] == 0) lq--;
    q[1] = evalsigne(sy) | evallgefint(lq);
    if (!z) { avma = (pari_sp)q; return q; }
    if (!r[lr - 1])
    {
      while(lr>2 && !r[lr - 1]) lr--;
      if (lr == 2) {avma=(pari_sp) q; *z=gzero; return q;} /* exact division */
    }
    r[1] = evalsigne(sx) | evallgefint(lr);
    avma = (pari_sp) r; *z = r; return q; 
  }
}

/* assume y > x > 0. return y mod x */

static ulong
resiu(GEN y, ulong x)
{
  return mpn_mod_1(LIMBS(y), NLIMBS(y), x);
}

/***********************************************************************/
/**								      **/
/**		          GCD                            	      **/
/**                                                                   **/
/***********************************************************************/

/* Ultra-fast private ulong gcd for trial divisions.  Called with y odd;
   x can be arbitrary (but will most of the time be smaller than y).
   Will also be used from inside ifactor2.c, so it's `semi-private' really.
   --GN */

/* Gotos are Harmful, and Programming is a Science.  E.W.Dijkstra. */
ulong
ugcd(ulong x, ulong y)         /* assume y&1==1, y > 1 */
{
  if (!x) return y;
  /* fix up x */
  while (!(x&1)) x>>=1;
  if (x==1) return 1;
  if (x==y) return y;
  else if (x>y) goto xislarger;/* will be rare, given how we'll use this */
  /* loop invariants: x,y odd and distinct. */
 yislarger:
  if ((x^y)&2)                 /* ...01, ...11 or vice versa */
    y=(x>>2)+(y>>2)+1;         /* ==(x+y)>>2 except it can't overflow */
  else                         /* ...01,...01 or ...11,...11 */
    y=(y-x)>>2;                /* now y!=0 in either case */
  while (!(y&1)) y>>=1;        /* kill any windfall-gained powers of 2 */
  if (y==1) return 1;          /* comparand == return value... */
  if (x==y) return y;          /* this and the next is just one comparison */
  else if (x<y) goto yislarger;/* else fall through to xislarger */

 xislarger:                    /* same as above, seen through a mirror */
  if ((x^y)&2)
    x=(x>>2)+(y>>2)+1;
  else
    x=(x-y)>>2;                /* x!=0 */
  while (!(x&1)) x>>=1;
  if (x==1) return 1;
  if (x==y) return y;
  else if (x>y) goto xislarger;/* again, a decent [g]cc should notice that
                                  it can re-use the comparison */
  goto yislarger;
}
/* Gotos are useful, and Programming is an Art.  D.E.Knuth. */
/* PS: Of course written with Dijkstra's lessons firmly in mind... --GN */

/* modified right shift binary algorithm with at most one division */
long
cgcd(long a,long b)
{
  long v;
  a=labs(a); if (!b) return a;
  b=labs(b); if (!a) return b;
  if (a>b) { a %= b; if (!a) return b; }
  else { b %= a; if (!b) return a; }
  v=vals(a|b); a>>=v; b>>=v;
  if (a==1 || b==1) return 1L<<v;
  if (b&1)
    return ((long)ugcd((ulong)a, (ulong)b)) << v;
  else
    return ((long)ugcd((ulong)b, (ulong)a)) << v;
}

long
clcm(long a,long b)
{
  long d;
  if(!a) return 0;
  d=cgcd(a,b);
  if(d!=1) return a*(b/d);
  return a*b;
}

/* assume a>b>0, return gcd(a,b) as a GEN (for gcdii) */
static GEN
gcduu(ulong a, ulong b)
{
  GEN r = cgeti(3);
  long v;

  r[1] = evalsigne(1)|evallgefint(3);
  a %= b; if (!a) { r[2]=(long)b; return r; }
  v=vals(a|b); a>>=v; b>>=v;
  if (a==1 || b==1) { r[2]=(long)(1UL<<v); return r; }
  if (b&1)
    r[2] = (long)(ugcd((ulong)a, (ulong)b) << v);
  else
    r[2] = (long)(ugcd((ulong)b, (ulong)a) << v);
  return r;
}

/* uses modified right-shift binary algorithm now --GN 1998Jul23 */
GEN
gcdii(GEN a, GEN b)
{
  long v, w;
  pari_sp av;
  GEN t, p1;

  switch (absi_cmp(a,b))
  {
    case 0: return absi(a);
    case -1: t=b; b=a; a=t;
  }
  if (!signe(b)) return absi(a);
  /* here |a|>|b|>0. Try single precision first */
  if (lgefint(a)==3)
    return gcduu((ulong)a[2], (ulong)b[2]);
  if (lgefint(b)==3)
  {
    ulong u = resiu(a,(ulong)b[2]);
    if (!u) return absi(b);
    return gcduu((ulong)b[2], u);
  }
  /* larger than gcd: "avma=av" gerepile (erasing t) is valid */
  av = avma; (void)new_chunk(lgefint(b)+1); /* HACK */
  t = resii(a,b);
  if (!signe(t)) { avma=av; return absi(b); }

  a = b; b = t;
  v = vali(a); a = shifti(a,-v); setsigne(a,1);
  w = vali(b); b = shifti(b,-w); setsigne(b,1);
  if (w < v) v = w;
  switch(absi_cmp(a,b))
  {
    case  0: avma=av; a=shifti(a,v); return a;
    case -1: p1=b; b=a; a=p1;
  }
  if (is_pm1(b)) { avma=av; return shifti(gun,v); }
 {
  /* general case */
  /*This serve two purposes: 1) mpn_gcd destroy its input and need an extra
   * limb 2) this allows us to use icopy instead of gerepile later.  NOTE: we
   * must put u before d else the final icopy could fail.
   */
  GEN res= cgeti(lgefint(a)+1);
  GEN ca = icopy_ef(a,lgefint(a)+1);
  GEN cb = icopy_ef(b,lgefint(b)+1);
  long l = mpn_gcd(LIMBS(res), LIMBS(ca), NLIMBS(ca), LIMBS(cb), NLIMBS(cb));
  res[1] = evalsigne(1)|evallgefint(l+2);
  avma=av;
  return shifti(res,v);
  }
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

/* convert integer --> base 10^9 */
GEN
convi(GEN x)
{
  pari_sp av = avma, lim;
  long lz;
  GEN z,p1;

  lz = 3 + ((lgefint(x)-2)*15)/DIVCONVI;
  z = new_chunk(lz); z[1] = -1; p1 = z+2;
  lim = stack_lim(av,1);
  for(;;)
  {
    x = diviu(x,1000000000); *p1++ = hiremainder;
    if (!signe(x)) { avma = av; return p1; }
    if (low_stack(lim, stack_lim(av,1))) x = gerepileuptoint((pari_sp)z,x);
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
  GEN Te,Td,Ne,Nd, scratch;
  ulong m,t,d,k = lgefint(N)-2;
  int carry;
  long i,j;
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

/* Find c such that 1=c*b mod 2^BITS_IN_LONG, assuming b odd (unchecked) */
ulong
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

/* Find z such that x=y*z, knowing that y | x (unchecked)
 * Method: y0 z0 = x0 mod B = 2^BITS_IN_LONG ==> z0 = 1/y0 mod B.
 *    Set x := (x - z0 y) / B, updating only relevant words, and repeat */
GEN
diviiexact(GEN x, GEN y)
{
  /*TODO: use mpn_bdivmod instead*/
  return divii(x,y);
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
  long lx;

  if (!signe(x)) return !signe(y);
  if (!signe(y)) return 0;

  lx=lgefint(x); if (lx != lgefint(y)) return 0;
  return !mpn_cmp(LIMBS(x),LIMBS(y),NLIMBS(x));
}

/* x and y are integers. Return sign(|x| - |y|) */
int
absi_cmp(GEN x, GEN y)
{
  long lx,ly;

  if (!signe(x)) return signe(y)? -1: 0;
  if (!signe(y)) return 1;

  lx=lgefint(x); ly=lgefint(y);
  if (lx>ly) return 1;
  if (lx<ly) return -1;
  return mpn_cmp(LIMBS(x),LIMBS(y),NLIMBS(x));
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
/**               INTEGER MULTIPLICATION                           **/
/**                                                                **/
/********************************************************************/

/* nx >= ny = num. of digits of x, y (not GEN, see mulii) */
#ifdef INLINE
INLINE
#endif
GEN
muliispec(GEN x, GEN y, long nx, long ny)
{
  GEN zd;
  long lz;
  ulong hi;

  if (nx < ny) swapspec(x,y, nx,ny);
  if (!ny) return gzero;
  if (ny == 1)
    return mulsispec(*y, x, nx);
    
  lz = nx+ny+2;
  zd = cgeti(lz);
  hi = mpn_mul(LIMBS(zd), (mp_limb_t *)x, nx, (mp_limb_t *)y, ny);
  if (!hi) lz--;
  /*else zd[lz-1]=hi; GH tell me it is not neccessary.*/

  zd[1] = evalsigne(1) | evallgefint(lz);
  return zd;
}

#ifdef INLINE
INLINE
#endif
GEN
sqrispec(GEN x, long nx)
{
  GEN zd;
  long lz;

  if (!nx) return gzero;
  if (nx==1) return muluu(*x,*x);
    
  lz = (nx<<1)+2;
  zd = cgeti(lz);
  mpn_mul_n(LIMBS(zd), (mp_limb_t *)x, (mp_limb_t *)x, nx);
  if (zd[lz-1]==0) lz--;

  zd[1] = evalsigne(1) | evallgefint(lz);
  return zd;
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
  z = muliispec(a+2,b+2, lgefint(a)-2,lgefint(b)-2);
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
  ulong hi;
  long l,k,lx,ly;
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

GEN
sqri(GEN a) { return sqrispec(a+2, lgefint(a)-2); }

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
  pari_sp av;
  long s;
  ulong g;
  ulong xv,xv1;		/* Lehmer stage recurrence matrix */

  if (typ(a) != t_INT || typ(b) != t_INT) err(arither1);
  if (!signe(b)) { *res=absi(a); return 0; }
  av = avma;
  if (lgefint(b) == 3) /* single-word affair */
  {
    GEN d1 = modiu(a, (ulong)(b[2]));
    if (d1 == gzero)
    {
      if (b[2] == 1L)
        { *res = gzero; return 1; }
      else
        { *res = absi(b); return 0; }
    }
    g = xgcduu((ulong)(b[2]), (ulong)(d1[2]), 1, &xv, &xv1, &s);
    avma = av;
    if (g != 1UL) { *res = utoi(g); return 0; }
    xv = xv1 % (ulong)(b[2]); if (s < 0) xv = ((ulong)(b[2])) - xv;
    *res = utoi(xv); return 1;
  }
  else
  {
    /* general case */
    /*This serve two purposes:
     * 1) mpn_gcdext destroy its input and need an extra limb
     * 2) this allows us to use icopy instead of gerepile later.
     * NOTE: we must put u before d else the final icopy could fail.
     */
    GEN  ca, cb, u, v, d;
    long lu, l, su;
    GEN na = modii(a,b);
    if (!signe(na)) {avma=av; *res=icopy(b); return 0;}
    ca = icopy_ef(na,lgefint(na)+1);
    cb = icopy_ef(b,lgefint(b)+1);
    u = cgeti(lgefint(b)+1);
    d = cgeti(lgefint(b)+1);
    l = mpn_gcdext(LIMBS(d), LIMBS(u), &lu, LIMBS(cb), NLIMBS(cb), LIMBS(ca), NLIMBS(ca));
    d[1] = evalsigne(1)|evallgefint(l+2);
    if (lu<=0)
    {
      if (lu==0) su=0;
      else {su=-1;lu=-lu;}
    }
    else
      su=1;
    u[1] = evalsigne(su)|evallgefint(lu+2);
    if (!is_pm1(d)) {avma=av; *res=icopy(d); return 0;}
    if (signe(b)<0) b=negi(b); 
    v=diviiexact(subii(d,mulii(u,b)),na);
    if (signe(v)<0) v=addii(v,b);
    avma=av; *res=icopy(v); return 1;
  }
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
  GEN t,r;
  GEN *pt;
  long s;
  int sa, sb;
  ulong g;
  ulong xu,xu1,xv,xv1;		/* Lehmer stage recurrence matrix */

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
  else
  {
    /* general case */
    pari_sp av = avma;
    /*This serve two purposes:
     * 1) mpn_gcdext destroy its input and need an extra limb
     * 2) this allows us to use icopy instead of gerepile later.
     * NOTE: we must put u before d else the final icopy could fail.
     */
    GEN ca = icopy_ef(a,lgefint(a)+1);
    GEN cb = icopy_ef(b,lgefint(b)+1);
    GEN u = cgeti(lgefint(a)+1), v;
    GEN d = cgeti(lgefint(a)+1);
    long su,l,lu;
    l = mpn_gcdext(LIMBS(d), LIMBS(u), &lu, LIMBS(ca), NLIMBS(ca), LIMBS(cb), NLIMBS(cb));
    if (lu<=0)
    {
      if (lu==0) su=0;
      else {su=-1;lu=-lu;}
    }
    else
      su=1;
    if (sa<0) su=-su;
    d[1] = evalsigne(1)|evallgefint(l+2);
    u[1] = evalsigne(su)|evallgefint(lu+2);
    if (pv != NULL) v=diviiexact(subii(d,mulii(u,a)),b);
    avma = av;
    if (pu != NULL) *pu=icopy(u);
    if (pv != NULL) *pv=icopy(v);
    return icopy(d);
  }
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

  d = int_MSW(d); d1 = int_MSW(d1);		/* point at the leading `digits' */
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
        dd1 += (d1[-1] >> shc);
        if (ld1 > 4)
          dd1lo = (d1[-1] << sh) + (d1[-2] >> shc);
        else
          dd1lo = (d1[-1] << sh);
      }
    }
    /* following lines assume d to have 2 or more significant words */
    dd = (*d << sh) + (d[-1] >> shc);
    if (ld > 4)
      ddlo = (d[-1] << sh) + (d[-2] >> shc);
    else
      ddlo = (d[-1] << sh);
  }
  else
  {				/* no shift needed */
    if (lz) return 0;		/* div'd longer than div'r: o'flow automatic */
    dd1 = *d1;
    if (!(HIGHMASK & dd1)) return 0;
    if(ld1 > 3) dd1lo = d1[-1];
    /* assume again that d has another significant word */
    dd = *d; ddlo = d[-1];
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
     VOLUME = {20},
       YEAR = {1995},
     NUMBER = {3},
      PAGES = {287--297},
 }
 * Preprint available from:
 * ftp://ftp.risc.uni-linz.ac.at/pub/techreports/1994/94-64.ps.gz
 */

/* #define DEBUG_RATLIFT */

int
ratlift(GEN x, GEN m, GEN *a, GEN *b, GEN amax, GEN bmax)
{
  GEN d,d1,v,v1,q,r;
  pari_sp av = avma, av1, lim;
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
  lbb = bfffo(*int_MSW(bmax));
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
    lbr = bfffo(*int_MSW(r));
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
    /* do a Lehmer-Jebelean round*/
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
    lbr = bfffo(*int_MSW(r));
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
    (void)rgcduu((ulong)*int_MSW(d), (ulong)*int_MSW(d1), vmax, &xu, &xu1, &xv, &xv1, &s0);
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

/* Return trunc(sqrt(abs(a)))). a must be an integer*/
GEN
isqrti(GEN a)
{
  long l;
  GEN res;
  if (!signe(a)) return gzero;
  l=(NLIMBS(a)+5)>>1;/* 2+ceil(na/2)*/
  res= cgeti(l);
  res[1] = evalsigne(1) | evallgefint(l);
  mpn_sqrtrem(LIMBS(res),NULL,LIMBS(a),NLIMBS(a));
  return res;
}

/********************************************************************/
/**                                                                **/
/**                             SHIFT                              **/
/**                                                                **/
/********************************************************************/

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
  err(warner,"GMP: shift_r is not tested");
  if (sh)
  {
    register ulong sh_complement = BITS_IN_LONG - sh;
    register ulong _k,_l = *source--;
    *target-- = (_l>>(ulong)sh) | ((ulong)prepend<<(ulong)sh_complement);
    while (source > source_end)
    {
      _k = _l<<(ulong)sh_complement; _l = *source--;
      *target-- = (_l>>(ulong)sh) | _k;
    }
  } else {
    int i;

    for (i=0; i < source_end - source; i++)
      target[i] = source[i];
  }
}

 
 /********************************************************************/
 /**                                                                **/
 /**                         RANDOM INTEGERS                        **/
 /**                                                                **/
 /********************************************************************/
 
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
  long lx,i,nz;
  GEN x, p1;

  lx = lgefint(N); x = cgeti(lx);
  nz = 2; while (!N[nz]) nz++; /* nz = index of last non-zero word */
  for (i=lx-1; i>1; i--)
  {
    ulong n = N[i], r;
    if (n == 0) r = 0;
    else
    {
      pari_sp av = avma;
      if (i > nz) n++; /* allow for equality if we can go down later */
      p1 = muluu(n, pari_rand()); /* < n * 2^32, so 0 <= first word < n */
      r = (lgefint(p1)<=3)? 0: p1[3]; avma = av;
    }
    x[i] = r;
    if (r < (ulong)N[i]) break;
  }
  for (i--; i>1; i--) x[i] = pari_rand();
  while (!x[lx-1]) lx--;
  x[1] = evalsigne(lx>2) | evallgefint(lx);
  avma = (pari_sp)x; return x;
}
/* Normalize a non-negative integer.  */
void
int_normalize(GEN x, long known_zero_words)
{
  long xl = lgefint(x);
  /* Normalize */
  long i = xl - 1 - known_zero_words;
  while (i > 1) {
    if (x[i])
      break;
    i--;
  }
  setlgefint(x, i+1);
  if (i == 1)
    setsigne(x,0);
}
