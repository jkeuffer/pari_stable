#line 2 "../src/kernel/gmp/mp.c"
/* $Id$

Copyright (C) 2002-2003  The PARI group.

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
/** BA2002Sep24                                                       **/
/***********************************************************************/
/* GMP t_INT as just like normal t_INT, just the mantissa is the other way
 * round
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

/*We need PARI invmod renamed to invmod_pari*/
#define INVMOD_PARI

void setmontgomerylimit(long n); 
int pari_kernel_init(void)
{
  /*Montgomery mult is not supported*/
  setmontgomerylimit(0);
  /*setresiilimit(50);*/
  /* Use gpmalloc instead of malloc */
  mp_set_memory_functions((void *(*)(size_t)) gpmalloc
		  	,(void *(*)(void *, size_t, size_t)) gprealloc
		        ,NULL);
  return 0;
}

#define LIMBS(x)  ((mp_limb_t *)((x)+2))
#define NLIMBS(x) (lgefint(x)-2)
/*This one is for t_REAL to emphasize there are not t_INT*/
#define RLIMBS(x)  ((mp_limb_t *)((x)+2))
#define RNLIMBS(x) (lg(x)-2)

INLINE void
xmpn_copy(mp_limb_t *x, mp_limb_t *y, long n)
{
  while (--n >= 0) x[n]=y[n];
}

INLINE void
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

INLINE void
xmpn_mirrorcopy(mp_limb_t *z, mp_limb_t *x, long n)
{
  long i;
  for(i=0;i<n;i++)
    z[i]=x[n-1-i];
}

INLINE void
xmpn_zero(mp_ptr x, mp_size_t n)
{
  while (--n >= 0) x[n]=0;
}

INLINE GEN
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

INLINE GEN
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

INLINE GEN
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
INLINE GEN
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
INLINE GEN
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
INLINE GEN
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

INLINE GEN
muliispec(GEN x, GEN y, long nx, long ny);

/* We must have nx>=ny. This lets garbage on the stack.
   This handle squares correctly (mpn_mul is optimized
   for squares).
*/

INLINE GEN
quickmulii(GEN x, GEN y, long nx, long ny)
{
  GEN cx=new_chunk(nx),cy;
  GEN z;
  xmpn_mirrorcopy((mp_limb_t *)cx,(mp_limb_t *)x,nx);
  if (x==y) cy=cx; /*If nx<ny cy will be too short*/
  else
  {
    cy=new_chunk(ny);
    xmpn_mirrorcopy((mp_limb_t *)cy,(mp_limb_t *)y,ny);
  }
  z=muliispec(cx, cy, nx, ny);
  xmpn_mirror(LIMBS(z), NLIMBS(z));
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
diviu_rem(GEN y, ulong x, ulong *rem)
{
  long ly;
  GEN z;

  if (!x) err(diver4);
  if (!signe(y)) { *rem = 0; return gzero; }

  ly = lgefint(y);
  if (ly == 3 && (ulong)x > (ulong)y[2]) { *rem = (ulong)y[2]; return gzero; }

  z = cgeti(ly); 
  *rem = mpn_divrem_1(LIMBS(z), 0, LIMBS(y), NLIMBS(y), x);
  if (z [ly - 1] == 0) ly--;
  z[1] = evallgefint(ly) | evalsigne(1);
  return z;
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
  long sy=signe(y),ly,s;
  GEN z;

  if (!x) err(diver4);
  if (!sy) { *rem = 0; return gzero; }
  if (x<0) { s = -sy; x = -x; } else s = sy;

  ly = lgefint(y);
  if (ly == 3 && (ulong)x > (ulong)y[2]) { *rem = itos(y); return gzero; }

  z = cgeti(ly); 
  *rem = mpn_divrem_1(LIMBS(z), 0, LIMBS(y), NLIMBS(y), x);
  if (sy<0) *rem = - ((long)*rem);
  if (z[ly - 1] == 0) ly--;
  z[1] = evallgefint(ly) | evalsigne(s);
  return z;
}

GEN
divis(GEN y, long x)
{
  long sy=signe(y),ly,s;
  GEN z;

  if (!x) err(diver4);
  if (!sy) return gzero;
  if (x<0) { s = -sy; x = -x; } else s=sy;

  ly = lgefint(y);
  if (ly == 3 && (ulong)x > (ulong)y[2]) return gzero;

  z = cgeti(ly); 
  (void)mpn_divrem_1(LIMBS(z), 0, LIMBS(y), NLIMBS(y), x);
  if (z[ly - 1] == 0) ly--;
  z[1] = evallgefint(ly) | evalsigne(s);
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

/* We keep llx bits of x and lly bits of y*/
GEN
divrr_with_gmp(GEN x, GEN y)
{
  long lx=RNLIMBS(x),ly=RNLIMBS(y);
  long lw=min(lx,ly);
  long lly=min(lw+1,ly);
  GEN  w=cgetr(lw+2);
  pari_sp av=avma;
  long lu=lw+lly;
  long llx=min(lu,lx);
  mp_limb_t *u=(mp_limb_t *)new_chunk(lu);
  mp_limb_t *z=(mp_limb_t *)new_chunk(lly);
  mp_limb_t *q,*r;
  long e=expo(x)-expo(y);
  long sx=signe(x),sy=signe(y);
  xmpn_mirrorcopy(z,RLIMBS(y),lly);
  xmpn_mirrorcopy(u+lu-llx,RLIMBS(x),llx);
  xmpn_zero(u,lu-llx);
  q = (mp_limb_t *)new_chunk(lw+1);
  r = (mp_limb_t *)new_chunk(lly);

  mpn_tdiv_qr(q,r,0,u,lu,z,lly);
  
  /*Round up: This is not exactly correct we should test 2*r>z*/
  if ((ulong)r[lly-1] > ((ulong)z[lly-1]>>1))
    mpn_add_1(q,q,lw+1,1);
  
  xmpn_mirrorcopy(RLIMBS(w),q,lw);
  /*If q[lw] then q[lw]=1. We just need to right shift to 
   * renormalize, but then we do not need e-- */
  if (q[lw]) 
    shift_right(w,w, 2,lw+2, 1,1)
  else e--;
  avma=av;
  if (sy < 0) sx = -sx;
  w[1] = evalsigne(sx) | evalexpo(e);
  return w;
}

static long DIVRR_GMP_LIMIT = 502;

GEN
divrr(GEN x, GEN y)
{
  long sx=signe(x), sy=signe(y), lx,ly,lr,e,i,j;
  ulong si,saux;
  GEN r,r1;

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
    r = cgetr(3); r[1] = evalsigne(sx) | evalexpo(e);
    hiremainder=k; r[2]=divll(l,y[2]); return r;
  }

  if (ly>=DIVRR_GMP_LIMIT)
    return divrr_with_gmp(x,y);

  lr = min(lx,ly); r = new_chunk(lr);
  r1 = r-1;
  r1[1] = 0; for (i=2; i<lr; i++) r1[i]=x[i];
  r1[lr] = (lx>lr)? x[lr]: 0;
  si=y[2]; saux=y[3];
  for (i=0; i<lr-1; i++)
  { /* r1 = r + (i-1) */
    ulong k,qp;
    LOCAL_HIREMAINDER;
    LOCAL_OVERFLOW;
    
    if ((ulong)r1[1] == si)
    {
      qp = MAXULONG; k=addll(si,r1[2]);
    }
    else
    {
      if ((ulong)r1[1] > si) /* can't happen if i=0 */
      {
        GEN y1 = y+1;
	overflow=0;
	for (j=lr-i; j>0; j--) r1[j] = subllx(r1[j],y1[j]);
	j=i; do r[--j]++; while (j && !r[j]);
      }
      hiremainder=r1[1]; overflow=0;
      qp=divll(r1[2],si); k=hiremainder;
    }
    if (!overflow)
    {
      long k3 = subll(mulll(qp,saux), r1[3]);
      long k4 = subllx(hiremainder,k);
      while (!overflow && k4) { qp--; k3=subll(k3,saux); k4=subllx(k4,si); }
    }
    j = lr-i+1;
    if (j<ly) (void)mulll(qp,y[j]); else { hiremainder=0 ; j=ly; } 
    for (j--; j>1; j--)
    {
      r1[j] = subll(r1[j], addmul(qp,y[j]));
      hiremainder += overflow;
    }
    if ((ulong)r1[1] != hiremainder)
    {
      if ((ulong)r1[1] < hiremainder)
      {
        qp--;
        overflow=0; for (j=lr-i-(lr-i>=ly); j>1; j--) r1[j]=addllx(r1[j], y[j]);
      }
      else
      {
	r1[1] -= hiremainder;
	while (r1[1])
	{
	  qp++; if (!qp) { j=i; do r[--j]++; while (j && !r[j]); }
          overflow=0; for (j=lr-i-(lr-i>=ly); j>1; j--) r1[j]=subllx(r1[j],y[j]);
	  r1[1] -= overflow;
	}
      }
    }
    r1[1]=qp; r1++;
  }
  /* i = lr-1 */
  /* round correctly */
  if ((ulong)r1[1] > (si>>1))
  {
    j=i; do r[--j]++; while (j && !r[j]);
  }
  r1 = r-1; for (j=i; j>=2; j--) r[j]=r1[j];
  if (r[0] == 0) e--;
  else if (r[0] == 1) { shift_right(r,r, 2,lr, 1,1); }
  else { /* possible only when rounding up to 0x2 0x0 ... */
    r[2] = HIGHBIT; e++; 
  }
  r[0] = evaltyp(t_REAL)|evallg(lr);
  r[1] = evalsigne(sx) | evalexpo(e);
  return r;
}

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

/* Find z such that x=y*z, knowing that y | x (unchecked)
 * Method: y0 z0 = x0 mod B = 2^BITS_IN_LONG ==> z0 = 1/y0 mod B.
 *    Set x := (x - z0 y) / B, updating only relevant words, and repeat */
GEN
diviiexact(GEN x, GEN y)
{
  /*TODO: use mpn_bdivmod instead*/
  return divii(x,y);
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
INLINE GEN
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

INLINE GEN
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

/* Normalize a non-negative integer.  */
GEN
int_normalize(GEN x, long known_zero_words)
{
  long i =  lgefint(x) - 1 - known_zero_words;
  for ( ; i > 1; i--)
    if (x[i]) { setlgefint(x, i+1); return x; }
  x[1] = evalsigne(0) | evallgefint(2); return x;
}

