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
/**                                                                   **/
/**               ARITHMETIC OPERATIONS ON POLYNOMIALS                **/
/**                         (third part)                              **/
/**                                                                   **/
/***********************************************************************/
#include "pari.h"

#define lswap(x,y) {long _z=x; x=y; y=_z;}
#define pswap(x,y) {GEN *_z=x; x=y; y=_z;}
#define swap(x,y)  {GEN  _z=x; x=y; y=_z;}
#define swapspec(x,y, nx,ny) {swap(x,y); lswap(nx,ny);}
/* 2p^2 < 2^BITS_IN_LONG */
#ifdef LONG_IS_64BIT
#  define u_OK_ULONG(p) ((ulong)p <= 3037000493UL)
#else
#  define u_OK_ULONG(p) ((ulong)p <= 46337UL)
#endif
#define OK_ULONG(p) (lgefint(p) == 3 && u_OK_ULONG(p[2]))

/*******************************************************************/
/*                                                                 */
/*                  KARATSUBA (for polynomials)                    */
/*                                                                 */
/*******************************************************************/

#if 1 /* for tunings */
long SQR_LIMIT = 6;
long MUL_LIMIT = 10;
long u_SQR_LIMIT = 6;
long u_MUL_LIMIT = 10;

void
setsqpol(long a) { SQR_LIMIT=a; u_SQR_LIMIT=a; }
void
setmulpol(long a) { MUL_LIMIT=a; u_MUL_LIMIT=a; }

GEN
u_specpol(GEN x, long nx)
{
  GEN z = cgetg(nx+2,t_POL);
  long i;
  for (i=0; i<nx; i++) z[i+2] = lstoi(x[i]);
  z[1]=evalsigne(1)|evallgef(nx+2);
  return z;
}

GEN
specpol(GEN x, long nx)
{
  GEN z = cgetg(nx+2,t_POL);
  long i;
  for (i=0; i<nx; i++) z[i+2] = x[i];
  z[1]=evalsigne(1)|evallgef(nx+2);
  return z;
}
#else
#  define SQR_LIMIT 6
#  define MUL_LIMIT 10
#endif

#ifndef HIGHWORD
#  define HIGHWORD(a) ((a) >> BITS_IN_HALFULONG)
#endif

/* multiplication in Fp[X], p small */

static GEN
u_normalizepol(GEN x, long lx)
{
  long i;
  for (i=lx-1; i>1; i--)
    if (x[i]) break;
  setlgef(x,i+1);
  setsigne(x, (i > 1)); return x;
}

GEN
u_FpX_deriv(GEN z, ulong p)
{
  long i,l = lgef(z)-1;
  GEN x;
  if (l < 2) l = 2;
  x = cgetg(l,t_VECSMALL); x[1] = z[1]; z++;
  if (HIGHWORD(l | p))
    for (i=2; i<l; i++) x[i] = mulssmod(i-1, z[i], p);
  else
    for (i=2; i<l; i++) x[i] = ((i-1) * z[i]) % p;
  return u_normalizepol(x,l);
}

static GEN
u_FpX_gcd_i(GEN a, GEN b, ulong p)
{
  GEN c;
  if (lgef(b) > lgef(a)) swap(a, b);
  while (signe(b))
  {
    c = u_FpX_rem(a,b,p);
    a = b; b = c;
  }
  return a;
}

GEN
u_FpX_gcd(GEN a, GEN b, ulong p)
{
  ulong av = avma;
  return gerepileupto(av, u_FpX_gcd_i(a,b,p));
}

int
u_FpX_is_squarefree(GEN z, ulong p)
{
  ulong av = avma;
  GEN d = u_FpX_gcd_i(z, u_FpX_deriv(z,p) , p);
  avma = av; return (degpol(d) == 0);
}

static GEN
u_FpX_addspec(GEN x, GEN y, long p, long lx, long ly)
{
  long i,lz;
  GEN z;

  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx+2; z = cgetg(lz,t_VECSMALL) + 2;
  for (i=0; i<ly; i++) z[i] = addssmod(x[i],y[i],p);
  for (   ; i<lx; i++) z[i] = x[i];
  z -= 2; z[1]=0; return u_normalizepol(z, lz);
}

#ifdef INLINE
INLINE
#endif
ulong
u_FpX_mullimb(GEN x, GEN y, ulong p, long a, long b)
{
  ulong p1 = 0;
  long i;
  for (i=a; i<b; i++)
    if (y[i])
    {
      p1 += y[i] * x[-i];
      if (p1 & HIGHBIT) p1 %= p;
    }
  return p1 % p;
}

ulong
u_FpX_mullimb_safe(GEN x, GEN y, ulong p, long a, long b)
{
  ulong p1 = 0;
  long i;
  for (i=a; i<b; i++)
    if (y[i])
      p1 = addssmod(p1, mulssmod(y[i],x[-i],p), p);
  return p1;
}

/* assume nx >= ny > 0 */
static GEN
s_FpX_mulspec(GEN x, GEN y, ulong p, long nx, long ny)
{
  long i,lz,nz;
  GEN z;

  lz = nx+ny+1; nz = lz-2;
  z = cgetg(lz, t_VECSMALL) + 2; /* x:y:z [i] = term of degree i */
  if (u_OK_ULONG(p))
  {
    for (i=0; i<ny; i++)z[i] = (long)u_FpX_mullimb(x+i,y,p,0,i+1);
    for (  ; i<nx; i++) z[i] = (long)u_FpX_mullimb(x+i,y,p,0,ny);
    for (  ; i<nz; i++) z[i] = (long)u_FpX_mullimb(x+i,y,p,i-nx+1,ny);
  }
  else
  {
    for (i=0; i<ny; i++)z[i] = (long)u_FpX_mullimb_safe(x+i,y,p,0,i+1);
    for (  ; i<nx; i++) z[i] = (long)u_FpX_mullimb_safe(x+i,y,p,0,ny);
    for (  ; i<nz; i++) z[i] = (long)u_FpX_mullimb_safe(x+i,y,p,i-nx+1,ny);
  }
  z -= 2; z[1]=0; return u_normalizepol(z, lz);
}

/* return (x * X^d) + y. Assume d > 0, x > 0 and y >= 0 */
GEN
u_FpX_addshift(GEN x, GEN y, ulong p, long d)
{
  GEN xd,yd,zd = (GEN)avma;
  long a,lz,ny = lgef(y)-2, nx = lgef(x)-2;

  x += 2; y += 2; a = ny-d;
  if (a <= 0)
  {
    lz = (a>nx)? ny+2: nx+d+2;
    (void)new_chunk(lz); xd = x+nx; yd = y+ny;
    while (xd > x) *--zd = *--xd;
    x = zd + a;
    while (zd > x) *--zd = 0;
  }
  else
  {
    xd = new_chunk(d); yd = y+d;
    x = u_FpX_addspec(x,yd,p, nx,a);
    lz = (a>nx)? ny+2: lgef(x)+d;
    x += 2; while (xd > x) *--zd = *--xd;
  }
  while (yd > y) *--zd = *--yd;
  *--zd = evalsigne(1) | evallgef(lz);
  *--zd = evaltyp(t_VECSMALL) | evallg(lz); return zd;
}

#define u_zeropol(malloc) u_allocpol(-1,malloc)
#define u_FpX_mul(x,y, p) u_FpX_Kmul(x+2,y+2,p, lgef(x)-2,lgef(y)-2)
#define u_FpX_sqr(x, p) u_FpX_Ksqr(x+2,p, lgef(x)-2)
#define u_FpX_add(x,y, p) u_FpX_addspec(x+2,y+2,p, lgef(x)-2,lgef(y)-2)

static GEN
u_allocpol(long d, int malloc)
{
  GEN z = malloc? (GEN)gpmalloc((d+3) * sizeof(long)): new_chunk(d+3);
  z[0] = evaltyp(t_VECSMALL) | evallg(d+3);
  z[1] = evalsigne((d >= 0)) | evallgef(d+3) | evalvarn(0);
  return z;
}

static GEN
u_scalarpol(ulong x, int malloc)
{
  GEN z = u_allocpol(0,malloc);
  z[2] = x; return z;
}

static GEN
u_FpX_neg_i(GEN x, ulong p)
{
  long i, l = lgef(x);
  for (i=2; i<l; i++)
    if (x[i]) x[i] = p - x[i];
  return x;
}

/* shift polynomial + gerepile */
static GEN
u_FpX_shiftip(long av, GEN x, long v)
{
  long i, lx = lgef(x), ly;
  GEN y;
  if (v <= 0 || !signe(x)) return gerepileupto(av, x);
  avma = av; ly = lx + v;
  x += lx; y = new_chunk(ly) + ly;
  for (i = 2; i<lx; i++) *--y = *--x;
  for (i = 0; i< v; i++) *--y = 0;
  *--y = evalsigne(1) | evallgef(ly);
  *--y = evaltyp(t_VECSMALL) | evallg(ly); return y;
}

/* fast product (Karatsuba) of polynomials a,b. These are not real GENs, a+2,
 * b+2 were sent instead. na, nb = number of terms of a, b.
 * Only c, c0, c1, c2 are genuine GEN.
 */
GEN
u_FpX_Kmul(GEN a, GEN b, ulong p, long na, long nb)
{
  GEN a0,c,c0;
  long av,n0,n0a,i, v = 0;

  while (na && !a[0]) { a++; na--; v++; }
  while (nb && !b[0]) { b++; nb--; v++; }
  if (na < nb) swapspec(a,b, na,nb);
  if (!nb) return u_zeropol(0);

  av = avma;
  if (nb < u_MUL_LIMIT)
    return u_FpX_shiftip(av,s_FpX_mulspec(a,b,p,na,nb), v);
  i=(na>>1); n0=na-i; na=i;
  a0=a+n0; n0a=n0;
  while (n0a && !a[n0a-1]) n0a--;

  if (nb > n0)
  {
    GEN b0,c1,c2;
    long n0b;

    nb -= n0; b0 = b+n0; n0b = n0;
    while (n0b && !b[n0b-1]) n0b--;
    c =  u_FpX_Kmul(a,b,p,n0a,n0b);
    c0 = u_FpX_Kmul(a0,b0,p,na,nb);

    c2 = u_FpX_addspec(a0,a,p,na,n0a);
    c1 = u_FpX_addspec(b0,b,p,nb,n0b);

    c1 = u_FpX_mul(c1,c2,p);
    c2 = u_FpX_add(c0,c,p);

    c2 = u_FpX_neg_i(c2,p);
    c2 = u_FpX_add(c1,c2,p);
    c0 = u_FpX_addshift(c0,c2 ,p, n0);
  }
  else
  {
    c  = u_FpX_Kmul(a,b,p,n0a,nb);
    c0 = u_FpX_Kmul(a0,b,p,na,nb);
  }
  c0 = u_FpX_addshift(c0,c,p,n0);
  return u_FpX_shiftip(av,c0, v);
}

GEN
u_FpX_sqrpol(GEN x, ulong p, long nx)
{
  long i,j,l,lz,nz;
  ulong p1;
  GEN z;

  if (!nx) return u_zeropol(0);
  lz = (nx << 1) + 1, nz = lz-2;
  z = cgetg(lz,t_VECSMALL) + 2;
  for (i=0; i<nx; i++)
  {
    p1 = 0; l = (i+1)>>1;
    for (j=0; j<l; j++)
    {
      p1 += x[j] * x[i-j];
      if (p1 & HIGHBIT) p1 %= p;
    }
    p1 <<= 1; if (p1 & HIGHBIT) p1 %= p;
    if ((i&1) == 0)
      p1 += x[i>>1] * x[i>>1];
    z[i] = p1 % p;
  }
  for (  ; i<nz; i++)
  {
    p1 = 0; l = (i+1)>>1;
    for (j=i-nx+1; j<l; j++)
    {
      p1 += x[j] * x[i-j];
      if (p1 & HIGHBIT) p1 %= p;
    }
    p1 <<= 1; if (p1 & HIGHBIT) p1 %= p;
    if ((i&1) == 0)
      p1 += x[i>>1] * x[i>>1];
    z[i] = p1 % p;
  }
  z -= 2; z[1]=0; return u_normalizepol(z,lz);
}

static GEN
u_Fp_gmul2_1(GEN x, ulong p)
{
  long i, l = lgef(x);
  GEN z = cgetg(l, t_VECSMALL);
  for (i=2; i<l; i++)
  {
    ulong p1 = x[i]<<1;
    if (p1 > p) p1 -= p;
    z[i] = p1;
  }
  z[1] = x[1]; return z;
}

GEN
u_FpX_Ksqr(GEN a, ulong p, long na)
{
  GEN a0,c,c0,c1;
  long av,n0,n0a,i, v = 0;

  while (na && !a[0]) { a++; na--; v += 2; }
  av = avma;
  if (na < u_SQR_LIMIT) return u_FpX_shiftip(av, u_FpX_sqrpol(a,p,na), v);
  i=(na>>1); n0=na-i; na=i;
  a0=a+n0; n0a=n0;
  while (n0a && !a[n0a-1]) n0a--;

  c = u_FpX_Ksqr(a,p,n0a);
  c0= u_FpX_Ksqr(a0,p,na);
  if (p == 2) n0 *= 2;
  else
  {
    c1 = u_Fp_gmul2_1(u_FpX_Kmul(a0,a,p, na,n0a), p);
    c0 = u_FpX_addshift(c0,c1,p,n0);
  }
  c0 = u_FpX_addshift(c0,c,p,n0);
  return u_FpX_shiftip(av,c0,v);
}

/* generic multiplication */

static GEN
addpol(GEN x, GEN y, long lx, long ly)
{
  long i,lz;
  GEN z;

  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx+2; z = cgetg(lz,t_POL) + 2;
  for (i=0; i<ly; i++) z[i]=ladd((GEN)x[i],(GEN)y[i]);
  for (   ; i<lx; i++) z[i]=x[i];
  z -= 2; z[1]=0; return normalizepol_i(z, lz);
}

static GEN
addpolcopy(GEN x, GEN y, long lx, long ly)
{
  long i,lz;
  GEN z;

  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx+2; z = cgetg(lz,t_POL) + 2;
  for (i=0; i<ly; i++) z[i]=ladd((GEN)x[i],(GEN)y[i]);
  for (   ; i<lx; i++) z[i]=lcopy((GEN)x[i]);
  z -= 2; z[1]=0; return normalizepol_i(z, lz);
}

#ifdef INLINE
INLINE
#endif
GEN
mulpol_limb(GEN x, GEN y, char *ynonzero, long a, long b)
{
  GEN p1 = NULL;
  long i,av = avma;
  for (i=a; i<b; i++)
    if (ynonzero[i])
    {
      GEN p2 = gmul((GEN)y[i],(GEN)x[-i]);
      p1 = p1 ? gadd(p1, p2): p2;
    }
  return p1 ? gerepileupto(av, p1): gzero;
}

/* assume nx >= ny > 0 */
static GEN
mulpol(GEN x, GEN y, long nx, long ny)
{
  long i,lz,nz;
  GEN z;
  char *p1;

  lz = nx+ny+1; nz = lz-2;
  z = cgetg(lz, t_POL) + 2; /* x:y:z [i] = term of degree i */
  p1 = gpmalloc(ny);
  for (i=0; i<ny; i++)
  {
    p1[i] = !isexactzero((GEN)y[i]);
    z[i] = (long)mulpol_limb(x+i,y,p1,0,i+1);
  }
  for (  ; i<nx; i++) z[i] = (long)mulpol_limb(x+i,y,p1,0,ny);
  for (  ; i<nz; i++) z[i] = (long)mulpol_limb(x+i,y,p1,i-nx+1,ny);
  free(p1); z -= 2; z[1]=0; return normalizepol_i(z, lz);
}

/* return (x * X^d) + y. Assume d > 0, x > 0 and y >= 0 */
GEN
addshiftw(GEN x, GEN y, long d)
{
  GEN xd,yd,zd = (GEN)avma;
  long a,lz,ny = lgef(y)-2, nx = lgef(x)-2;

  x += 2; y += 2; a = ny-d;
  if (a <= 0)
  {
    lz = (a>nx)? ny+2: nx+d+2;
    (void)new_chunk(lz); xd = x+nx; yd = y+ny;
    while (xd > x) *--zd = *--xd;
    x = zd + a;
    while (zd > x) *--zd = zero;
  }
  else
  {
    xd = new_chunk(d); yd = y+d;
    x = addpol(x,yd, nx,a);
    lz = (a>nx)? ny+2: lgef(x)+d;
    x += 2; while (xd > x) *--zd = *--xd;
  }
  while (yd > y) *--zd = *--yd;
  *--zd = evalsigne(1) | evallgef(lz);
  *--zd = evaltyp(t_POL) | evallg(lz); return zd;
}

GEN
addshiftpol(GEN x, GEN y, long d)
{
  long v = varn(x);
  if (!signe(x)) return y;
  x = addshiftw(x,y,d);
  setvarn(x,v); return x;
}

/* as above, producing a clean malloc */
static GEN
addshiftwcopy(GEN x, GEN y, long d)
{
  GEN xd,yd,zd = (GEN)avma;
  long a,lz,ny = lgef(y)-2, nx = lgef(x)-2;

  x += 2; y += 2; a = ny-d;
  if (a <= 0)
  {
    lz = nx+d+2;
    (void)new_chunk(lz); xd = x+nx; yd = y+ny;
    while (xd > x) *--zd = lcopy((GEN)*--xd);
    x = zd + a;
    while (zd > x) *--zd = zero;
  }
  else
  {
    xd = new_chunk(d); yd = y+d;
    x = addpolcopy(x,yd, nx,a);
    lz = (a>nx)? ny+2: lgef(x)+d;
    x += 2; while (xd > x) *--zd = *--xd;
  }
  while (yd > y) *--zd = lcopy((GEN)*--yd);
  *--zd = evalsigne(1) | evallgef(lz);
  *--zd = evaltyp(t_POL) | evallg(lz); return zd;
}

/* shift polynomial in place. assume v free cells have been left before x */
static GEN
shiftpol_ip(GEN x, long v)
{
  long i, lx;
  GEN y;
  if (v <= 0 || !signe(x)) return x;
  lx = lgef(x);
  x += 2; y = x + v;
  for (i = lx-3; i>=0; i--) y[i] = x[i];
  for (i = 0   ; i< v; i++) x[i] = zero;
  lx += v;
  *--x = evalsigne(1) | evallgef(lx);
  *--x = evaltyp(t_POL) | evallg(lx); return x;
}

/* fast product (Karatsuba) of polynomials a,b. These are not real GENs, a+2,
 * b+2 were sent instead. na, nb = number of terms of a, b.
 * Only c, c0, c1, c2 are genuine GEN.
 */
GEN
quickmul(GEN a, GEN b, long na, long nb)
{
  GEN a0,c,c0;
  long av,n0,n0a,i, v = 0;

  while (na && isexactzero((GEN)a[0])) { a++; na--; v++; }
  while (nb && isexactzero((GEN)b[0])) { b++; nb--; v++; }
  if (na < nb) swapspec(a,b, na,nb);
  if (!nb) return zeropol(0);

  if (v) (void)cgetg(v,t_STR); /* v gerepile-safe cells for shiftpol_ip */
  if (nb < MUL_LIMIT)
    return shiftpol_ip(mulpol(a,b,na,nb), v);
  i=(na>>1); n0=na-i; na=i;
  av=avma; a0=a+n0; n0a=n0;
  while (n0a && isexactzero((GEN)a[n0a-1])) n0a--;

  if (nb > n0)
  {
    GEN b0,c1,c2;
    long n0b;

    nb -= n0; b0 = b+n0; n0b = n0;
    while (n0b && isexactzero((GEN)b[n0b-1])) n0b--;
    c = quickmul(a,b,n0a,n0b);
    c0 = quickmul(a0,b0, na,nb);

    c2 = addpol(a0,a, na,n0a);
    c1 = addpol(b0,b, nb,n0b);

    c1 = quickmul(c1+2,c2+2, lgef(c1)-2,lgef(c2)-2);
    c2 = gneg_i(gadd(c0,c));
    c0 = addshiftw(c0, gadd(c1,c2), n0);
  }
  else
  {
    c = quickmul(a,b,n0a,nb);
    c0 = quickmul(a0,b,na,nb);
  }
  c0 = addshiftwcopy(c0,c,n0);
  return shiftpol_ip(gerepileupto(av,c0), v);
}

GEN
sqrpol(GEN x, long nx)
{
  long av,i,j,l,lz,nz;
  GEN p1,z;
  char *p2;

  if (!nx) return zeropol(0);
  lz = (nx << 1) + 1, nz = lz-2;
  z = cgetg(lz,t_POL) + 2;
  p2 = gpmalloc(nx);
  for (i=0; i<nx; i++)
  {
    p2[i] = !isexactzero((GEN)x[i]);
    p1=gzero; av=avma; l=(i+1)>>1;
    for (j=0; j<l; j++)
      if (p2[j] && p2[i-j])
        p1 = gadd(p1, gmul((GEN)x[j],(GEN)x[i-j]));
    p1 = gshift(p1,1);
    if ((i&1) == 0 && p2[i>>1])
      p1 = gadd(p1, gsqr((GEN)x[i>>1]));
    z[i] = lpileupto(av,p1);
  }
  for (  ; i<nz; i++)
  {
    p1=gzero; av=avma; l=(i+1)>>1;
    for (j=i-nx+1; j<l; j++)
      if (p2[j] && p2[i-j])
        p1 = gadd(p1, gmul((GEN)x[j],(GEN)x[i-j]));
    p1 = gshift(p1,1);
    if ((i&1) == 0 && p2[i>>1])
      p1 = gadd(p1, gsqr((GEN)x[i>>1]));
    z[i] = lpileupto(av,p1);
  }
  free(p2); z -= 2; z[1]=0; return normalizepol_i(z,lz);
}

GEN
quicksqr(GEN a, long na)
{
  GEN a0,c,c0,c1;
  long av,n0,n0a,i, v = 0;

  while (na && isexactzero((GEN)a[0])) { a++; na--; v += 2; }
  if (v) (void)new_chunk(v);
  if (na<SQR_LIMIT) return shiftpol_ip(sqrpol(a,na), v);
  i=(na>>1); n0=na-i; na=i;
  av=avma; a0=a+n0; n0a=n0;
  while (n0a && isexactzero((GEN)a[n0a-1])) n0a--;

  c = quicksqr(a,n0a);
  c0 = quicksqr(a0,na);
  c1 = gmul2n(quickmul(a0,a, na,n0a), 1);
  c0 = addshiftw(c0,c1, n0);
  c0 = addshiftwcopy(c0,c,n0);
  return shiftpol_ip(gerepileupto(av,c0), v);
}
/*****************************************
 * Arithmetic in Z/pZ[X]                 *
 *****************************************/

/*********************************************************************
This functions supposes polynomials already reduced.
There are clean and memory efficient.
**********************************************************************/

GEN
FpX_center(GEN T,GEN mod)
{/*OK centermod exists, but is not so clean*/
  ulong av;
  long i, l=lg(T);
  GEN P,mod2;
  P=cgetg(l,t_POL);
  P[1]=T[1];
  av=avma;
  mod2=gclone(shifti(mod,-1));/*clone*/
  avma=av;
  for(i=2;i<l;i++)
    P[i]=cmpii((GEN)T[i],mod2)<0?licopy((GEN)T[i]):lsubii((GEN)T[i],mod);
  gunclone(mod2);/*unclone*/
  return P;
}

GEN
FpX_neg(GEN x,GEN p)
{
  long i,d=lgef(x);
  GEN y;
  y=cgetg(d,t_POL); y[1]=x[1];
  for(i=2;i<d;i++)
    if (signe(x[i])) y[i]=lsubii(p,(GEN)x[i]);
    else y[i]=zero;
  return y;
}
/**********************************************************************
Unclean functions, do not garbage collect.
This is a feature: The malloc is corrupted only by the call to FpX_red
so garbage collecting so often is not desirable.
FpX_red can sometime be avoided by passing NULL for p.
In this case the function is usually clean (see below for detail)
Added to help not using POLMOD of INTMOD which are deadly slow.
gerepileupto of the result is legible.   Bill.
I don't like C++.  I am wrong.
**********************************************************************/
/*
 *If p is NULL no reduction is performed and the function is clean.
 * for FpX_add,FpX_mul,FpX_sqr,FpX_Fp_mul
 */
GEN
FpX_add(GEN x,GEN y,GEN p)
{
  long lx,ly,i;
  GEN z;
  lx = lgef(x); ly = lgef(y); if (lx < ly) swapspec(x,y, lx,ly);
  z = cgetg(lx,t_POL); z[1] = x[1];
  for (i=2; i<ly; i++) z[i]=laddii((GEN)x[i],(GEN)y[i]);
  for (   ; i<lx; i++) z[i]=licopy((GEN)x[i]);
  (void)normalizepol_i(z, lx);
  if (lgef(z) == 2) { avma = (long)(z + lx); z = zeropol(varn(x)); }
  if (p) z= FpX_red(z, p);
  return z;
}
GEN
FpX_sub(GEN x,GEN y,GEN p)
{
  long lx,ly,i,lz;
  GEN z;
  lx = lgef(x); ly = lgef(y);
  lz=max(lx,ly);
  z = cgetg(lz,t_POL);
  if (lx >= ly)
  {
    z[1] = x[1];
    for (i=2; i<ly; i++) z[i]=lsubii((GEN)x[i],(GEN)y[i]);
    for (   ; i<lx; i++) z[i]=licopy((GEN)x[i]);
    (void)normalizepol_i(z, lz);
  }
  else
  {
    z[1] = y[1];
    for (i=2; i<lx; i++) z[i]=lsubii((GEN)x[i],(GEN)y[i]);
    for (   ; i<ly; i++) z[i]=lnegi((GEN)y[i]);
    /*polynomial is always normalized*/
  }
  if (lgef(z) == 2) { avma = (long)(z + lz); z = zeropol(varn(x)); }
  if (p) z= FpX_red(z, p);
  return z;
}
GEN
FpX_mul(GEN x,GEN y,GEN p)
{
  GEN z = quickmul(y+2, x+2, lgef(y)-2, lgef(x)-2);
  setvarn(z,varn(x));
  if (!p) return z;
  return FpX_red(z, p);
}
GEN
FpX_sqr(GEN x,GEN p)
{
  GEN z = quicksqr(x+2, lgef(x)-2);
  setvarn(z,varn(x));
  if (!p) return z;
  return FpX_red(z, p);
}
#define u_FpX_div(x,y,p) u_FpX_divrem((x),(y),(p),(0),NULL)

/* Product of y and x in Z/pZ[X]/(pol), as t_VECSMALL. Assume OK_ULONG(p) */
static GEN
u_FpXQ_mul(GEN y,GEN x,GEN pol,ulong p)
{
  GEN z = u_FpX_mul(y,x,p);
  return u_FpX_rem(z,pol,p);
}
/* Square of y in Z/pZ[X]/(pol), as t_VECSMALL. Assume OK_ULONG(p) */
static GEN
u_FpXQ_sqr(GEN y,GEN pol,ulong p)
{
  GEN z = u_FpX_sqr(y,p);
  return u_FpX_rem(z,pol,p);
}

/* Inverse of x in Z/pZ[X]/(pol) or NULL if inverse doesn't exist
 * return lift(1 / (x mod (p,pol))) */
GEN
FpXQ_invsafe(GEN x, GEN T, GEN p)
{
  GEN z, U, V;

  if (typ(x) != t_POL) return mpinvmod(x, p);
  z = FpX_extgcd(x, T, p, &U, &V);
  if (lgef(z) != 3) return NULL;
  z = mpinvmod((GEN)z[2], p);
  return FpX_Fp_mul(U, z, p);
}

/* Product of y and x in Z/pZ[X]/(T)
 * return lift(lift(Mod(x*y*Mod(1,p),T*Mod(1,p)))) */
GEN
FpXQ_mul(GEN y,GEN x,GEN T,GEN p)
{
  GEN z;
  if (typ(x) == t_INT)
  {
    if (typ(y) == t_INT) return modii(mulii(x,y), p);
    return FpX_Fp_mul(y, x, p);
  }
  if (typ(y) == t_INT) return FpX_Fp_mul(x, y, p);
  z = quickmul(y+2, x+2, lgef(y)-2, lgef(x)-2); setvarn(z,varn(y));
  z = FpX_red(z, p); return FpX_res(z,T, p);
}

/* Square of y in Z/pZ[X]/(pol)
 * return lift(lift(Mod(y^2*Mod(1,p),pol*Mod(1,p)))) */
GEN
FpXQ_sqr(GEN y,GEN pol,GEN p)
{
  GEN z = quicksqr(y+2,lgef(y)-2); setvarn(z,varn(y));
  z = FpX_red(z, p); return FpX_res(z,pol, p);
}
/*Modify y[2].
 *No reduction if p is NULL
 */
GEN
FpX_Fp_add(GEN y,GEN x,GEN p)
{
  if (!signe(x)) return y;
  if (!signe(y))
    return scalarpol(x,varn(y));
  y[2]=laddii((GEN)y[2],x);
  if (p) y[2]=lmodii((GEN)y[2],p);
  if (!signe(y[2]) && degpol(y) == 0) return zeropol(varn(y));
  return y;
}
GEN
ZX_s_add(GEN y,long x)
{
  if (!x) return y;
  if (!signe(y))
    return scalarpol(stoi(x),varn(y));
  y[2] = laddis((GEN)y[2],x);
  if (!signe(y[2]) && degpol(y) == 0) return zeropol(varn(y));
  return y;
}
/* y is a polynomial in ZZ[X] and x an integer.
 * If p is NULL, no reduction is perfomed and return x*y
 *
 * else the result is lift(y*x*Mod(1,p))
 */
GEN
FpX_Fp_mul(GEN y,GEN x,GEN p)
{
  GEN z;
  int i;
  if (!signe(x))
    return zeropol(varn(y));
  z=cgetg(lg(y),t_POL);
  z[1]=y[1];
  for(i=2;i<lgef(y);i++)
    z[i]=lmulii((GEN)y[i],x);
  if(!p) return z;
  return FpX_red(z,p);
}
/*****************************************************************
 *                 End of unclean functions.                     *
 *                                                               *
 *****************************************************************/
/*****************************************************************
 Clean and with no reduced hypothesis.  Beware that some operations
 will be much slower with big unreduced coefficient
*****************************************************************/
/* Inverse of x in Z[X] / (p,T)
 * return lift(lift(Mod(x*Mod(1,p), T*Mod(1,p))^-1)); */
GEN
FpXQ_inv(GEN x,GEN T,GEN p)
{
  ulong av;
  GEN U;

  if (!T) return mpinvmod(x,p);
  av = avma;
  U = FpXQ_invsafe(x, T, p);
  if (!U) err(talker,"non invertible polynomial in FpXQ_inv");
  return gerepileupto(av, U);
}

GEN
FpXV_FpV_innerprod(GEN V, GEN W, GEN p)
{
  long ltop=avma;
  long i;
  GEN z = FpX_Fp_mul((GEN)V[1],(GEN)W[1],NULL);
  for(i=2;i<lg(V);i++)
    z=FpX_add(z,FpX_Fp_mul((GEN)V[i],(GEN)W[i],NULL),NULL);
  return gerepileupto(ltop,FpX_red(z,p));
}

/* generates the list of powers of x of degree 0,1,2,...,l*/
GEN
FpXQ_powers(GEN x, long l, GEN T, GEN p)
{
  GEN V=cgetg(l+2,t_VEC);
  long i;
  V[1] = (long) scalarpol(gun,varn(T));
  if (l==0) return V;
  V[2] = lcopy(x);
  if (l==1) return V;
  V[3] = (long) FpXQ_sqr(x,T,p);
  for(i=4;i<l+2;i++)
    V[i] = (long) FpXQ_mul((GEN) V[i-1],x,T,p);
#if 0
  TODO: Karim proposes to use squaring:
  V[i] = (long) ((i&1)?FpXQ_sqr((GEN) V[(i+1)>>1],T,p)
                       :FpXQ_mul((GEN) V[i-1],x,T,p));
  Please profile it.
#endif
  return V;
}
#if 0
static long brent_kung_nbmul(long d, long n, long p)
{
  return p+n*((d+p-1)/p);
}
  TODO: This the the optimal parameter for the purpose of reducing
  multiplications, but profiling need to be done to ensure it is not slower 
  than the other option in practice
/*Return optimal parameter l for the evaluation of n polynomials of degree d*/
long brent_kung_optpow(long d, long n)
{
  double r;
  long f,c,pr;
  if (n>=d ) return d;
  pr=n*d;
  if (pr<=1) return 1;
  r=d/sqrt(pr);
  c=(long)ceil(d/ceil(r));
  f=(long)floor(d/floor(r));
  return (brent_kung_nbmul(d, n, c) <= brent_kung_nbmul(d, n, f))?c:f;
}
#endif 
/*Return optimal parameter l for the evaluation of n polynomials of degree d*/
long brent_kung_optpow(long d, long n)
{
  double r;
  long l,pr;
  if (n>=d ) return d;
  pr=n*d;
  if (pr<=1) return 1;
  r=d/sqrt(pr);
  l=(long)r;
  return (d+l-1)/l;
}

/*Close to FpXV_FpV_innerprod*/

static GEN
spec_compo_powers(GEN P, GEN V, long a, long n)
{
  long i;
  GEN z;
  z = scalarpol((GEN)P[2+a],varn(P));
  for(i=1;i<=n;i++)
    z=FpX_add(z,FpX_Fp_mul((GEN)V[i+1],(GEN)P[2+a+i],NULL),NULL);
  return z;
}
/*Try to implement algorithm in Brent & Kung (Fast algorithms for
 *manipulating formal power series, JACM 25:581-595, 1978)
 
 V must be as output by FpXQ_powers.
 For optimal performance, l (of FpXQ_powers) must be as output by
 brent_kung_optpow
 */

GEN
FpX_FpXQV_compo(GEN P, GEN V, GEN T, GEN p)
{
  ulong ltop=avma;
  long l=lg(V)-1;
  GEN z,u;
  long d=degpol(P),cnt=0;
  if (d==-1) return zeropol(varn(T));
  if (d<l)
  {
    z=spec_compo_powers(P,V,0,d);
    return gerepileupto(ltop,FpX_red(z,p));
  }
  if (l<=1)
    err(talker,"powers is only [] or [1] in FpX_FpXQV_compo");
  z=spec_compo_powers(P,V,d-l+1,l-1);
  d-=l;
  while(d>=l-1)
  {
    u=spec_compo_powers(P,V,d-l+2,l-2);
    z=FpX_add(u,FpXQ_mul(z,(GEN)V[l],T,p),NULL);
    d-=l-1;
    cnt++;
  }
  u=spec_compo_powers(P,V,0,d);
  z=FpX_add(u,FpXQ_mul(z,(GEN)V[d+2],T,p),NULL);
  cnt++;
  if (DEBUGLEVEL>=8) fprintferr("FpX_FpXQV_compo: %d FpXQ_mul [%d]\n",cnt,l-1);
  return gerepileupto(ltop,FpX_red(z,p));
}

/* T in Z[X] and  x in Z/pZ[X]/(pol)
 * return lift(lift(subst(T,variable(T),Mod(x*Mod(1,p),pol*Mod(1,p)))));
 */
GEN
FpX_FpXQ_compo(GEN T,GEN x,GEN pol,GEN p)
{
  ulong ltop=avma;
  GEN z;
  long d=degpol(T),rtd;
  if (!signe(T)) return zeropol(varn(T));
  rtd = (long) sqrt((double)d);
  z = FpX_FpXQV_compo(T,FpXQ_powers(x,rtd,pol,p),pol,p);
  return gerepileupto(ltop,z);
}

/* Evaluation in Fp
 * x in Z[X] and y in Z return x(y) mod p
 *
 * If p is very large (several longs) and x has small coefficients(<<p),
 * then Brent & Kung algorithm is faster. */
GEN
FpX_eval(GEN x,GEN y,GEN p)
{
  ulong av;
  GEN p1,r,res;
  long i,j;
  i=lgef(x)-1;
  if (i<=2)
    return (i==2)? modii((GEN)x[2],p): gzero;
  res=cgetg(lgefint(p),t_INT);
  av=avma; p1=(GEN)x[i];
  /* specific attention to sparse polynomials (see poleval)*/
  /*You've guess it! It's a copy-paste(tm)*/
  for (i--; i>=2; i=j-1)
  {
    for (j=i; !signe((GEN)x[j]); j--)
      if (j==2)
      {
	if (i!=j) y = powmodulo(y,stoi(i-j+1),p);
	p1=mulii(p1,y);
	goto fppoleval;/*sorry break(2) no implemented*/
      }
    r = (i==j)? y: powmodulo(y,stoi(i-j+1),p);
    p1 = modii(addii(mulii(p1,r), (GEN)x[j]),p);
  }
 fppoleval:
  modiiz(p1,p,res);
  avma=av;
  return res;
}
/* Tz=Tx*Ty where Tx and Ty coprime
 * return lift(chinese(Mod(x*Mod(1,p),Tx*Mod(1,p)),Mod(y*Mod(1,p),Ty*Mod(1,p))))
 * if Tz is NULL it is computed
 * As we do not return it, and the caller will frequently need it,
 * it must compute it and pass it.
 */
GEN
FpX_chinese_coprime(GEN x,GEN y,GEN Tx,GEN Ty,GEN Tz,GEN p)
{
  long av = avma;
  GEN ax,p1;
  ax = FpX_mul(FpXQ_inv(Tx,Ty,p), Tx,p);
  p1=FpX_mul(ax, FpX_sub(y,x,p),p);
  p1 = FpX_add(x,p1,p);
  if (!Tz) Tz=FpX_mul(Tx,Ty,p);
  p1 = FpX_res(p1,Tz,p);
  return gerepileupto(av,p1);
}

/* assume n > 0 */
GEN
u_FpXQ_pow(GEN x, GEN n, GEN pol, ulong p)
{
  ulong av = avma;
  GEN p1 = n+2, y = x;
  long m,i,j;
  m = *p1;
  j = 1+bfffo(m); m <<= j; j = BITS_IN_LONG-j;
  for (i=lgefint(n)-2;;)
  {
    for (; j; m<<=1,j--)
    {
      y = u_FpXQ_sqr(y,pol,p);
      if (m<0)
        y = u_FpXQ_mul(y,x,pol,p);
    }
    if (--i == 0) break;
    m = *++p1, j = BITS_IN_LONG;
  }
  return gerepileupto(av, y);
}

/* x,pol in Z[X], p in Z, n in Z, compute lift(x^n mod (p, pol)) */
GEN
FpXQ_pow(GEN x, GEN n, GEN pol, GEN p)
{
  ulong av, ltop = avma, lim=stack_lim(avma,1);
  long m,i,j, vx = varn(x);
  GEN p1 = n+2, y;
  if (!signe(n)) return polun[vx];
  if (signe(n) < 0)
  {
    x=FpXQ_inv(x,pol,p);
    if (is_pm1(n)) return x; /* n = -1*/
  }
  else
    if (is_pm1(n)) return gcopy(x); /* n = 1 */
  if (OK_ULONG(p))
  {
    ulong pp = p[2];
    pol = u_Fp_FpX(pol,0, pp);
    x = u_Fp_FpX(x,0, pp);
    y = u_FpXQ_pow(x, n, pol, pp);
    y = small_to_pol(y,vx);
  }
  else
  {
    av = avma;
    m = *p1; y = x;
    j = 1+bfffo(m); m <<= j; j = BITS_IN_LONG-j;
    for (i=lgefint(n)-2;;)
    {
      for (; j; m<<=1,j--)
      {
        y = FpXQ_sqr(y,pol,p);
        if (low_stack(lim, stack_lim(av,1)))
        {
          if(DEBUGMEM>1) err(warnmem,"[1]: FpXQ_pow");
          y = gerepileupto(av, y);
        }
        if (m<0)
          y = FpXQ_mul(y,x,pol,p);
        if (low_stack(lim, stack_lim(av,1)))
        {
          if(DEBUGMEM>1) err(warnmem,"[2]: FpXQ_pow");
          y = gerepileupto(av, y);
        }
      }
      if (--i == 0) break;
      m = *++p1, j = BITS_IN_LONG;
    }
  }
  return gerepileupto(ltop,y);
}

/*******************************************************************/
/*                                                                 */
/*                             Fp[X][Y]                            */
/*                                                                 */
/*******************************************************************/
/*Polynomials whose coefficients are either polynomials or integers*/

GEN
FpXX_red(GEN z, GEN p)
{
    GEN res;
    int i;
    res=cgetg(lgef(z),t_POL);
    res[1] = evalsigne(1) | evalvarn(varn(z)) | evallgef(lgef(z));
    for(i=2;i<lgef(res);i++)
      if (typ(z[i])!=t_INT)
      {
	ulong av=avma;
        res[i]=(long)FpX_red((GEN)z[i],p);
	if (lgef(res[i])<=3)
	{
	  if (lgef(res[i])==2) {avma=av;res[i]=zero;}
	  else res[i]=lpilecopy(av,gmael(res,i,2));
	}
      }
      else
        res[i]=lmodii((GEN)z[i],p);
    res=normalizepol_i(res,lgef(res));
    return res;
}

/*******************************************************************/
/*                                                                 */
/*                             (Fp[X]/(Q))[Y]                      */
/*                                                                 */
/*******************************************************************/

extern GEN to_Kronecker(GEN P, GEN Q);
GEN /*Somewhat copy-pasted...*/
/*Not malloc nor warn-clean.*/
FpXQX_from_Kronecker(GEN z, GEN pol, GEN p)
{
  long i,j,lx,l = lgef(z), N = (degpol(pol)<<1) + 1;
  GEN x, t = cgetg(N,t_POL);
  t[1] = pol[1] & VARNBITS;
  lx = (l-2) / (N-2); x = cgetg(lx+3,t_POL);
  if (isonstack(pol)) pol = gcopy(pol);
  for (i=2; i<lx+2; i++)
  {
    for (j=2; j<N; j++) t[j] = z[j];
    z += (N-2);
    x[i] = (long)FpX_res(normalizepol_i(t,N), pol, p);
  }
  N = (l-2) % (N-2) + 2;
  for (j=2; j<N; j++) t[j] = z[j];
  x[i] = (long)FpX_res(normalizepol_i(t,N), pol, p);
  return normalizepol_i(x, i+1);
}
/*Unused/untested*/
GEN
FpXQX_red(GEN z, GEN T, GEN p)
{
  GEN res;
  int i;
  res=cgetg(lgef(z),t_POL);
  res[1] = evalsigne(1) | evalvarn(varn(z)) | evallgef(lgef(z));
  for(i=2;i<lgef(res);i++)
    if (typ(z[i])!=t_INT)
    {
      if (T)
        res[i]=(long)FpX_res((GEN)z[i],T,p);
      else
        res[i]=(long)FpX_red((GEN)z[i],p);
    }
    else
      res[i]=lmodii((GEN)z[i],p);
  res=normalizepol_i(res,lgef(res));
  return res;
}
/* if T = NULL, call FpX_mul */
GEN
FpXQX_mul(GEN x, GEN y, GEN T, GEN p)
{
  ulong ltop;
  GEN z,kx,ky;
  long vx;
  if (!T) return FpX_mul(x,y,p);
  ltop = avma;
  vx = min(varn(x),varn(y));
  kx= to_Kronecker(x,T);
  ky= to_Kronecker(y,T);
  z = quickmul(ky+2, kx+2, lgef(ky)-2, lgef(kx)-2);
  z = FpX_red(z,p);
  z = FpXQX_from_Kronecker(z,T,p);
  setvarn(z,vx);/*quickmul and Fq_from_Kronecker are not varn-clean*/
  return gerepileupto(ltop,z);
}
GEN/*Unused/untested*/
FpXQX_sqr(GEN x, GEN T, GEN p)
{
  ulong ltop=avma;
  GEN z,kx;
  long vx=varn(x);
  kx= to_Kronecker(x,T);
  z = quicksqr(kx+2, lgef(kx)-2);
  z = FpX_red(z,p);
  z = FpXQX_from_Kronecker(z,T,p);
  setvarn(z,vx);/*quickmul and Fq_from_Kronecker are nor varn-clean*/
  return gerepileupto(ltop,z);
}
GEN
FpXQX_FpXQ_mul(GEN P, GEN U, GEN T, GEN p)
{
  int i, lP = lgef(P);
  GEN res = cgetg(lP,t_POL);
  res[1] = evalsigne(1) | evalvarn(varn(P)) | evallgef(lP);
  for(i=2; i<lP; i++)
    res[i] = (long)FpXQ_mul(U,(GEN)P[i], T,p);
  return normalizepol_i(res,lgef(res));
}

/* a X^degpol, assume degpol >= 0 */
static GEN
monomial(GEN a, int degpol, int v)
{
  long i, lP = degpol+3;
  GEN P = cgetg(lP, t_POL);
  P[1] = evalsigne(1) | evalvarn(v) | evallgef(lP);
  lP--; P[lP] = (long)a;
  for (i=2; i<lP; i++) P[i] = zero;
  return P;
}

/* return NULL if Euclidean remainder sequence fails (==> T reducible mod p)
 * last non-zero remainder otherwise */
GEN
FpXQX_safegcd(GEN P, GEN Q, GEN T, GEN p)
{
  ulong ltop = avma, btop, st_lim;
  long dg, vx = varn(P);
  GEN U, q;
  P = FpXX_red(P, p);
  Q = FpXX_red(Q, p);
  if (!signe(P)) return gerepileupto(ltop, Q);
  if (!signe(Q)) { avma = (ulong)P; return P; }
  T = FpX_red(T, p);

  btop = avma; st_lim = stack_lim(btop, 1);
  dg = lgef(P)-lgef(Q);
  if (dg < 0) { swap(P, Q); dg = -dg; }
  for(;;)
  {
    U = FpXQ_invsafe(leading_term(Q), T, p);
    if (!U) { avma = ltop; return NULL; }
    do /* set P := P % Q */
    {
      q = FpXQ_mul(U, gneg(leading_term(P)), T, p);
      P = gadd(P, FpXQX_mul(monomial(q, dg, vx), Q, T, p));
      P = FpXQX_red(P, T, p); /* wasteful, but negligible */
      dg = lgef(P)-lgef(Q);
    } while (dg >= 0);
    if (!signe(P)) break;

    if (low_stack(st_lim, stack_lim(btop, 1)))
    {
      GEN *bptr[2]; bptr[0]=&P; bptr[1]=&Q;
      if (DEBUGLEVEL>1) err(warnmem,"FpXQX_safegcd");
      gerepilemany(btop, bptr, 2);
    }
    swap(P, Q); dg = -dg;
  }
  Q = FpXQX_FpXQ_mul(Q, U, T, p); /* normalize GCD */
  return gerepileupto(ltop, Q);
}

/*******************************************************************/
/*                                                                 */
/*                             Fq[X]                               */
/*                                                                 */
/*******************************************************************/

/*Well nothing, for now. So we reuse FpXQX*/
#define FqX_mul FpXQX_mul
#define FqX_sqr FpXQX_sqr
#define FqX_red FpXQX_red
static GEN
Fq_neg(GEN x, GEN T, GEN p)/*T is not used but it is for consistency*/
{
  switch(typ(x)==t_POL)
  {
    case 0: return signe(x)?subii(p,x):gzero;
    case 1: return FpX_neg(x,p);
  }
  return NULL;
}
static GEN modulo,Tmodulo;
static GEN fgmul(GEN a,GEN b){return FqX_mul(a,b,Tmodulo,modulo);}
GEN
FqV_roots_to_pol(GEN V, GEN Tp, GEN p, long v)
{
  ulong ltop=avma;
  long k;
  GEN W=cgetg(lg(V),t_VEC);
  for(k=1;k<lg(V);k++)
    W[k]=(long)deg1pol(gun,Fq_neg((GEN)V[k],Tp,p),v);
  modulo=p;Tmodulo=Tp;
  W=divide_conquer_prod(W,&fgmul);
  return gerepileupto(ltop,W);
}

/*******************************************************************/
/*                                                                 */
/*                       n-th ROOT in Fq                           */
/*                                                                 */
/*******************************************************************/
/*NO clean malloc*/
static GEN fflgen(GEN l, long e, GEN r, GEN T ,GEN p, GEN *zeta)
{
  ulong av1;
  GEN z,m,m1;
  long x=varn(T),k,u,v,pp,i;
  if (is_bigint(p))
    pp=VERYBIGINT;
  else
    pp=itos(p);
  z=(lgef(T)==4)?polun[x]:polx[x];

  av1 = avma;
  for (k=1; ; k++)
  {
    u=k;v=0;
    while (u%pp==0){u/=pp;v++;}
    if(!v)
      z=gadd(z,gun);
    else
    {
      z=gadd(z,gpowgs(polx[x],v));
      if (DEBUGLEVEL>=6)
	fprintferr("FF l-Gen:next %Z",z);
    }
    m1 = m = FpXQ_pow(z,r,T,p);
    for (i=1; i<e; i++)
      if (gcmp1(m=FpXQ_pow(m,l,T,p))) break;
    if (i==e) break;
    avma = av1;
  }
  *zeta=m;
  return m1;
}
/* resoud x^l=a mod (p,T)
 * l doit etre premier
 * q=p^degpol(T)-1
 * q=(l^e)*r
 * e>=1
 * pgcd(r,l)=1
 * m=y^(q/l)
 * y n'est pas une puissance l-ieme
 * m!=1
 * ouf!
 */
GEN
ffsqrtlmod(GEN a, GEN l, GEN T ,GEN p , GEN q, long e, GEN r, GEN y, GEN m)
{
  ulong av = avma,lim;
  long i,k;
  GEN p1,p2,u1,u2,v,w,z;

  bezout(r,l,&u1,&u2);
  v=FpXQ_pow(a,u2,T,p);
  w=FpXQ_pow(a,modii(mulii(negi(u1),r),q),T,p);
  lim = stack_lim(av,1);
  while (!gcmp1(w))
  {
    /* if p is not prime, next loop will not end */
    k=0;
    p1=w;
    do
    {
      z=p1;
      p1=FpXQ_pow(p1,l,T,p);
      k++;
    }while(!gcmp1(p1));
    if (k==e) { avma=av; return NULL; }
    p2 = FpXQ_mul(z,m,T,p);
    for(i=1; !gcmp1(p2); i++) p2 = FpXQ_mul(p2,m,T,p);/*should be a baby step
							      giant step instead*/
    p1= FpXQ_pow(y,modii(mulsi(i,gpowgs(l,e-k-1)),q),T,p);
    m = FpXQ_pow(m,stoi(i),T,p);
    e = k;
    v = FpXQ_mul(p1,v,T,p);
    y = FpXQ_pow(p1,l,T,p);
    w = FpXQ_mul(y,w,T,p);
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[4];
      if(DEBUGMEM>1) err(warnmem,"ffsqrtlmod");
      gptr[0]=&y; gptr[1]=&v; gptr[2]=&w; gptr[3]=&m;
      gerepilemany(av,gptr,4);
    }
  }
  return gerepilecopy(av,v);
}
/*  n is an integer, a is in Fp[X]/(T), p is prime, T is irreducible mod p

return a solution of

x^n=a mod p

1)If there is no solution return NULL and if zetan is not NULL set zetan to gzero.

2) If there is solution there are exactly  m=gcd(p-1,n) of them.

If zetan is not NULL, zetan is set to a primitive mth root of unity so that
the set of solutions is {x*zetan^k;k=0 to m-1}

If a=0 ,return 0 and if zetan is not NULL zetan is set to gun
*/
GEN ffsqrtnmod(GEN a, GEN n, GEN T, GEN p, GEN *zetan)
{
  ulong ltop=avma,lbot=0,av1,lim;
  long i,j,e;
  GEN m,u1,u2;
  GEN q,r,zeta,y,l,z;
  GEN *gptr[2];
  if (typ(a) != t_POL || typ(n) != t_INT || typ(T) != t_POL || typ(p)!=t_INT)
    err(typeer,"ffsqrtnmod");
  if (lgef(T)==3)
    err(constpoler,"ffsqrtnmod");
  if(!signe(n))
    err(talker,"1/0 exponent in ffsqrtnmod");
  if(gcmp1(n)) {if (zetan) *zetan=gun;return gcopy(a);}
  if(gcmp0(a)) {if (zetan) *zetan=gun;return gzero;}
  q=addsi(-1,gpowgs(p,degpol(T)));
  m=bezout(n,q,&u1,&u2);
  if (gcmp(m,n))
  {
    GEN b=modii(u1,q);
    lbot=avma;
    a=FpXQ_pow(a,b,T,p);
  }
  if (zetan) z=polun[varn(T)];
  lim=stack_lim(ltop,1);
  if (!gcmp1(m))
  {
    m=decomp(m);
    av1=avma;
    for (i = lg(m[1])-1; i; i--)
    {
      l=gcoeff(m,i,1); j=itos(gcoeff(m,i,2));
      e=pvaluation(q,l,&r);
      y=fflgen(l,e,r,T,p,&zeta);
      if (zetan) z=FpXQ_mul(z,FpXQ_pow(y,gpowgs(l,e-j),T,p),T,p);
      do
      {
	lbot=avma;
	a=ffsqrtlmod(a,l,T,p,q,e,r,y,zeta);
	if (!a){avma=ltop;return NULL;}
	j--;
      }while (j);
      if (low_stack(lim, stack_lim(ltop,1)))
	  /* n can have lots of prime factors*/
      {
	if(DEBUGMEM>1) err(warnmem,"ffsqrtnmod");
	if (zetan)
	{
	  z=gcopy(z);
	  gptr[0]=&a;gptr[1]=&z;
	  gerepilemanysp(av1,lbot,gptr,2);
	}
	else
	  a=gerepileupto(av1,a);
	lbot=av1;
      }
    }
  }
  if (zetan)
  {
    *zetan=gcopy(z);
    gptr[0]=&a;gptr[1]=zetan;
    gerepilemanysp(ltop,lbot,gptr,2);
  }
  else
    a=gerepileupto(ltop,a);
  return a;
}
/*******************************************************************/
/*  Isomorphisms between finite fields                             */
/*                                                                 */
/*******************************************************************/
GEN
matrixpow(long n, long m, GEN y, GEN P,GEN l)
{
  return vecpol_to_mat(FpXQ_powers(y,m-1,P,l),n);
}
/* compute the reciprocical isomorphism of S mod T,p, i.e. V such that
   V(S)=X  mod T,p*/
GEN
Fp_inv_isom(GEN S,GEN T, GEN p)
{
  ulong   ltop = avma, lbot;
  GEN     M, V;
  int     n, i;
  long    x;
  x = varn(T);
  n = degpol(T);
  M = matrixpow(n,n,S,T,p);
  V = cgetg(n + 1, t_COL);
  for (i = 1; i <= n; i++)
    V[i] = zero;
  V[2] = un;
  V = FpM_invimage(M,V,p);
  lbot = avma;
  V = gtopolyrev(V, x);
  return gerepile(ltop, lbot, V);
}
#if 0
/*Old, trivial, implementation*/
GEN
intersect_ker(GEN P, GEN MA, GEN l, GEN U, GEN lU) 
{
  ulong ltop=avma;
  long vp=varn(P), np=degpol(P);
  GEN A;
  A=FqM_ker(gaddmat(gneg(polx[MAXVARN]), *MA),lU,l);
  if (lg(A)!=2)
    err(talker,"ZZ_%Z[%Z]/(%Z) is not a field in Fp_intersect"
	,l,polx[vp],P);
  A=gmul((GEN)A[1],gmodulcp(gmodulcp(gun,l),U));
  return gerepileupto(ltop,gtopolyrev(A,vp));
}
#endif
/* Let P a polynomial != 0 and M the matrix of the x^p Frobenius automorphism in
 * FFp[X]/T. Compute P(M)
 * not stack clean
 */
static GEN
polfrobenius(GEN M, GEN p, long r, long v)
{
  GEN V,W;
  long i;
  V = cgetg(r+2,t_VEC);
  V[1] = (long) polx[v];
  if (r == 0) return V;
  V[2] = (long) gtopolyrev((GEN)M[2],v);
  W = (GEN) M[2];
  for (i = 3; i <= r+1; ++i)
  {
    W = FpM_FpV_mul(M,W,p);
    V[i] = (long) gtopolyrev(W,v);
  }
  return V;
}

static GEN
matpolfrobenius(GEN V, GEN P, GEN T, GEN p)
{
  long i;
  long l=degpol(T);
  long v=varn(T);
  GEN M,W;
  GEN PV=gtovec(P);
  PV=cgetg(degpol(P)+2,t_VEC);
  for(i=1;i<lg(PV);i++)
    PV[i]=P[1+i];
  M=cgetg(l+1,t_VEC);
  M[1]=(long)scalarpol(poleval(P,gun),v);
  M[2]=(long)FpXV_FpV_innerprod(V,PV,p);
  W=cgetg(lg(V),t_VEC);
  for(i=1;i<lg(W);i++)
     W[i]=V[i];
  for(i=3;i<=l;i++)
  {
    long j;
    for(j=1;j<lg(W);j++)
      W[j]=(long)FpXQ_mul((GEN)W[j],(GEN)V[j],T,p);
    M[i]=(long)FpXV_FpV_innerprod(W,PV,p);
  }
  return vecpol_to_mat(M,l);
}

/* Essentially we want to compute
 * FqM_ker(MA-polx[MAXVARN],lU,l)
 * To avoid use of matrix in Fq we procede as follows:
 * We compute FpM_ker(U(MA)) and then we recover
 * the eigen value by Galois action, see formula.
 */
static GEN
intersect_ker(GEN P, GEN MA, GEN l, GEN U, GEN lU) 
{
  ulong ltop=avma;
  long vp=varn(P);
  long vu=varn(lU), r=degpol(lU);
  long i;
  GEN A, R, M, ib0, V;
  if (DEBUGLEVEL>=4) timer2();
  V=polfrobenius(MA,l,r,varn(U));
  if (DEBUGLEVEL>=4) msgtimer("pol[frobenius]");
  M=matpolfrobenius(V,lU,P,l);
  if (DEBUGLEVEL>=4) msgtimer("matrix cyclo");
  A=FpM_ker(M,l);
  if (DEBUGLEVEL>=4) msgtimer("kernel");
  A=gerepileupto(ltop,A);
  if (lg(A)!=r+1)
    err(talker,"ZZ_%Z[%Z]/(%Z) is not a field in Fp_intersect"
	,l,polx[vp],P);
  /*The formula is 
   * a_{r-1}=-\phi(a_0)/b_0
   * a_{i-1}=\phi(a_i)+b_ia_{r-1}  i=r-1 to 1
   * Where a_0=A[1] and b_i=U[i+2]
   */
  ib0=negi(mpinvmod((GEN)lU[2],l));
  R=cgetg(r+1,t_MAT);
  R[1]=A[1];
  R[r]=(long)FpM_FpV_mul(MA,gmul((GEN)A[1],ib0),l);
  for(i=r-1;i>1;i--)
    R[i]=(long)FpV_red(gadd(FpM_FpV_mul(MA,(GEN)R[i+1],l),
	  gmul((GEN)lU[i+2],(GEN)R[r])),l);
  R=gtrans_i(R);
  for(i=1;i<lg(R);i++)
    R[i]=(long)gtopolyrev((GEN)R[i],vu);
  A=gtopolyrev(R,vp);
  A=gmul(A,gmodulcp(gmodulcp(gun,l),U));
  return gerepileupto(ltop,A);
}

/* n must divide both the degree of P and Q.  Compute SP and SQ such
  that the subfield of FF_l[X]/(P) generated by SP and the subfield of
  FF_l[X]/(Q) generated by SQ are isomorphic of degree n.  P and Q do
  not need to be of the same variable.  if MA (resp. MB) is not NULL,
  must be the matrix of the frobenius map in FF_l[X]/(P) (resp.
  FF_l[X]/(Q) ).  */
/* Note on the implementation choice:
 * We assume the prime p is very large
 * so we handle Frobenius as matrices.
 */
void
Fp_intersect(long n, GEN P, GEN Q, GEN l,GEN *SP, GEN *SQ, GEN MA, GEN MB)
{
  ulong ltop=avma,lbot;
  long vp,vq,np,nq,e,pg;
  GEN q;
  GEN A,B,Ap,Bp;
  GEN *gptr[2];
  vp=varn(P);vq=varn(Q);
  np=degpol(P);nq=degpol(Q);
  if (np<=0 || nq<=0 || n<=0 || np%n!=0 || nq%n!=0)
    err(talker,"bad degrees in Fp_intersect: %d,%d,%d",n,degpol(P),degpol(Q));
  e=pvaluation(stoi(n),l,&q);
  pg=itos(q);
  avma=ltop;
  if (DEBUGLEVEL>=4) timer2();
  if(!MA) MA=matrixpow(np,np,FpXQ_pow(polx[vp],l,P,l),P,l);
  if(!MB) MB=matrixpow(nq,nq,FpXQ_pow(polx[vq],l,Q,l),Q,l);
  if (DEBUGLEVEL>=4) msgtimer("matrixpow");
  A=Ap=zeropol(vp);
  B=Bp=zeropol(vq);
  if (pg>1)
  {
    if (gcmp0(modis(addis(l,-1),pg)))
      /*We do not need to use relative extension in this setting, so
        we don't. (Well,now that we don't in the other case also, it is more
       dubious to treat cases apart...)*/
    {
      GEN L,An,Bn,ipg,z;
      z=rootmod(cyclo(pg,-1),l);
      if (lg(z)<2) err(talker,"%Z is not a prime in Fp_intersect",l);
      z=negi(lift((GEN)z[1]));
      ipg=stoi(pg);
      if (DEBUGLEVEL>=4) timer2();
      A=FpM_ker(gaddmat(z, MA),l);
      if (lg(A)!=2)
	err(talker,"ZZ_%Z[%Z]/(%Z) is not a field in Fp_intersect"
	    ,l,polx[vp],P);
      A=gtopolyrev((GEN)A[1],vp);
      B=FpM_ker(gaddmat(z, MB),l);
      if (lg(B)!=2)
	err(talker,"ZZ_%Z[%Z]/(%Z) is not a field in Fp_intersect"
	    ,l,polx[vq],Q);
      B=gtopolyrev((GEN)B[1],vq);
      if (DEBUGLEVEL>=4) msgtimer("FpM_ker");
      An=(GEN) FpXQ_pow(A,ipg,P,l)[2];
      Bn=(GEN) FpXQ_pow(B,ipg,Q,l)[2];
      z=modii(mulii(An,mpinvmod(Bn,l)),l);
      L=mpsqrtnmod(z,ipg,l,NULL);
      if ( !L )
        err(talker,"Polynomials not irreducible in Fp_intersect");
      if (DEBUGLEVEL>=4) msgtimer("mpsqrtnmod");
      B=FpX_Fp_mul(B,L,l);
    }
    else
    {
      GEN L,An,Bn,ipg,U,lU,z;
      U=gmael(factmod(cyclo(pg,MAXVARN),l),1,1);
      lU=lift(U);
      ipg=stoi(pg);
      A=intersect_ker(P, MA, l, U, lU); 
      B=intersect_ker(Q, MB, l, U, lU);
      /*Somewhat ugly, but it is a proof that POLYMOD are useful and
        powerful.*/
      if (DEBUGLEVEL>=4) timer2();
      An=lift(lift((GEN)lift(gpowgs(gmodulcp(A,P),pg))[2]));
      Bn=lift(lift((GEN)lift(gpowgs(gmodulcp(B,Q),pg))[2]));
      if (DEBUGLEVEL>=4) msgtimer("pows [P,Q]");
      z=FpXQ_inv(Bn,lU,l);
      z=FpXQ_mul(An,z,lU,l);
      L=ffsqrtnmod(z,ipg,lU,l,NULL);
      if (DEBUGLEVEL>=4) msgtimer("ffsqrtn");
      if ( !L )
        err(talker,"Polynomials not irreducible in Fp_intersect");
      B=gsubst(lift(lift(gmul(B,L))),MAXVARN,gzero);
      A=gsubst(lift(lift(A)),MAXVARN,gzero);
    }
  }
  if (e!=0)
  {
    GEN VP,VQ,moinsun,Ay,By,lmun;
    int i,j;
    moinsun=stoi(-1);
    lmun=addis(l,-1);
    MA=gaddmat(moinsun,MA);
    MB=gaddmat(moinsun,MB);
    Ay=polun[vp];
    By=polun[vq];
    VP=cgetg(np+1,t_COL);
    VP[1]=un;
    for(i=2;i<=np;i++) VP[i]=zero;
    if (np==nq) VQ=VP;/*save memory*/
    else
    {
      VQ=cgetg(nq+1,t_COL);
      VQ[1]=un;
      for(i=2;i<=nq;i++) VQ[i]=zero;
    }
    for(j=0;j<e;j++)
    {
      if (j)
      {
	Ay=FpXQ_mul(Ay,FpXQ_pow(Ap,lmun,P,l),P,l);
	for(i=1;i<lgef(Ay)-1;i++) VP[i]=Ay[i+1];
	for(;i<=np;i++) VP[i]=zero;
      }
      Ap=FpM_invimage(MA,VP,l);
      Ap=gtopolyrev(Ap,vp);
      if (j)
      {
	By=FpXQ_mul(By,FpXQ_pow(Bp,lmun,Q,l),Q,l);
	for(i=1;i<lgef(By)-1;i++) VQ[i]=By[i+1];
	for(;i<=nq;i++) VQ[i]=zero;
      }
      Bp=FpM_invimage(MB,VQ,l);
      Bp=gtopolyrev(Bp,vq);
      if (DEBUGLEVEL>=4) msgtimer("FpM_invimage");
    }
  }/*FpX_add is not clean, so we must do it *before* lbot=avma*/
  A=FpX_add(A,Ap,NULL);
  B=FpX_add(B,Bp,NULL);
  lbot=avma;
  *SP=FpX_red(A,l);
  *SQ=FpX_red(B,l);
  gptr[0]=SP;gptr[1]=SQ;
  gerepilemanysp(ltop,lbot,gptr,2);
}
/* Let l be a prime number, P, Q in ZZ[X].  P and Q are both
 * irreducible modulo l and degree(P) divides degree(Q).  Output a
 * monomorphism between FF_l[X]/(P) and FF_l[X]/(Q) as a polynomial R such
 * that Q | P(R) mod l.  If P and Q have the same degree, it is of course an
 * isomorphism.  */
GEN Fp_isom(GEN P,GEN Q,GEN l)
{
  ulong ltop=avma;
  GEN SP,SQ,R;
  Fp_intersect(degpol(P),P,Q,l,&SP,&SQ,NULL,NULL);
  R=Fp_inv_isom(SP,P,l);
  R=FpX_FpXQ_compo(R,SQ,Q,l);
  return gerepileupto(ltop,R);
}
GEN
Fp_factorgalois(GEN P,GEN l, long d, long w)
{
  ulong ltop=avma;
  GEN R,V,ld,Tl;
  long n,k,m;
  long v;
  v=varn(P);
  n=degpol(P);
  m=n/d;
  ld=gpowgs(l,d);
  Tl=gcopy(P); setvarn(Tl,w);
  V=cgetg(m+1,t_VEC);
  V[1]=lpolx[w];
  for(k=2;k<=m;k++)
    V[k]=(long)FpXQ_pow((GEN)V[k-1],ld,Tl,l);
  R=FqV_roots_to_pol(V,Tl,l,v);
  return gerepileupto(ltop,R);
}
extern GEN mat_to_polpol(GEN x, long v,long w);
extern GEN polpol_to_mat(GEN v, long n);
/* P,Q irreducible over F_l. Factor P over FF_l[X] / Q  [factors are ordered as
 * a Frobenius cycle] */
GEN
Fp_factor_irred(GEN P,GEN l, GEN Q)
{
  ulong ltop=avma,av;
  GEN SP,SQ,MP,MQ,M,MF,E,V,IR,res;
  long np=degpol(P),nq=degpol(Q);
  long i,d=cgcd(np,nq);
  long vp=varn(P),vq=varn(Q);
  if (d==1)
  {	
    res=cgetg(2,t_COL);
    res[1]=lcopy(P);
    return res;
  }
  MF=matrixpow(nq,nq,FpXQ_pow(polx[vq],l,Q,l),Q,l);
  Fp_intersect(d,P,Q,l,&SP,&SQ,NULL,MF);
  av=avma;
  E=Fp_factorgalois(P,l,d,vq);
  E=polpol_to_mat(E,np);
  MP = matrixpow(np,d,SP,P,l);
  IR = (GEN)FpM_sindexrank(MP,l)[1];
  E = rowextract_p(E, IR);
  M = rowextract_p(MP,IR);
  M = FpM_inv(M,l);
  MQ = matrixpow(nq,d,SQ,Q,l);
  M = FpM_mul(MQ,M,l);
  M = FpM_mul(M,E,l);
  M = gerepileupto(av,M);
  V = cgetg(d+1,t_VEC);
  V[1]=(long)M;
  for(i=2;i<=d;i++)
    V[i]=(long)FpM_mul(MF,(GEN)V[i-1],l);
  res=cgetg(d+1,t_COL);
  for(i=1;i<=d;i++)
    res[i]=(long)mat_to_polpol((GEN)V[i],vp,vq);
  return gerepilecopy(ltop,res);
}
GEN Fp_factor_rel0(GEN P,GEN l, GEN Q)
{
  ulong ltop=avma,tetpil;
  GEN V,ex,F,y,R;
  long n,nbfact=0,nmax=lgef(P)-2;
  long i;
  F=factmod0(P,l);
  n=lg((GEN)F[1]);
  V=cgetg(nmax,t_VEC);
  ex=cgetg(nmax,t_VECSMALL);
  for(i=1;i<n;i++)
  {
    int j,r;
    R=Fp_factor_irred(gmael(F,1,i),l,Q);
    r=lg(R);
    for (j=1;j<r;j++)
    {
      V[++nbfact]=R[j];
      ex[nbfact]=mael(F,2,i);
    }
  }
  setlg(V,nbfact+1);
  setlg(ex,nbfact+1);
  tetpil=avma; y=cgetg(3,t_VEC);
  y[1]=lcopy(V);
  y[2]=lcopy(ex);
  (void)sort_factor(y,cmp_pol);
  return gerepile(ltop,tetpil,y);
}
GEN Fp_factor_rel(GEN P, GEN l, GEN Q)
{
  long tetpil,av=avma;
  long nbfact;
  long j;
  GEN y,u,v;
  GEN z=Fp_factor_rel0(P,l,Q),t = (GEN) z[1],ex = (GEN) z[2];
  nbfact=lg(t);
  tetpil=avma; y=cgetg(3,t_MAT);
  u=cgetg(nbfact,t_COL); y[1]=(long)u;
  v=cgetg(nbfact,t_COL); y[2]=(long)v;
  for (j=1; j<nbfact; j++)
  {
    u[j] = lcopy((GEN)t[j]);
    v[j] = lstoi(ex[j]);
  }
  return gerepile(av,tetpil,y);
}

/*******************************************************************/
extern int ff_poltype(GEN *x, GEN *p, GEN *pol);

static GEN
to_intmod(GEN x, GEN p)
{
  GEN a = cgetg(3,t_INTMOD);
  a[1] = (long)p;
  a[2] = lmodii(x,p); return a;
}

/* z in Z[X], return z * Mod(1,p), normalized*/
GEN
FpX(GEN z, GEN p)
{
  long i,l = lgef(z);
  GEN x = cgetg(l,t_POL);
  if (isonstack(p)) p = icopy(p);
  for (i=2; i<l; i++) x[i] = (long)to_intmod((GEN)z[i], p);
  x[1] = z[1]; return normalizepol_i(x,l);
}

/* z in Z^n, return z * Mod(1,p), normalized*/
GEN
FpV(GEN z, GEN p)
{
  long i,l = lg(z);
  GEN x = cgetg(l,typ(z));
  if (isonstack(p)) p = icopy(p);
  for (i=1; i<l; i++) x[i] = (long)to_intmod((GEN)z[i], p);
  return x;
}
/* z in Mat m,n(Z), return z * Mod(1,p), normalized*/
GEN
FpM(GEN z, GEN p)
{
  long i,j,l = lg(z), m = lg((GEN)z[1]);
  GEN x,y,zi;
  if (isonstack(p)) p = icopy(p);
  x = cgetg(l,t_MAT);
  for (i=1; i<l; i++)
  {
    x[i] = lgetg(m,t_COL);
    y = (GEN)x[i];
    zi= (GEN)z[i];
    for (j=1; j<m; j++) y[j] = (long)to_intmod((GEN)zi[j], p);
  }
  return x;
}
/* z in Z[X] or Z, return lift(z * Mod(1,p)), normalized*/
GEN
FpX_red(GEN z, GEN p)
{
  long i,l;
  GEN x;
  if (typ(z) == t_INT) return modii(z,p);
  l = lgef(z);
  x = cgetg(l,t_POL);
  for (i=2; i<l; i++) x[i] = lmodii((GEN)z[i],p);
  x[1] = z[1]; return normalizepol_i(x,l);
}

GEN
FpXV_red(GEN z, GEN p)
{
  long i,l = lg(z);
  GEN x = cgetg(l, t_VEC);
  for (i=1; i<l; i++) x[i] = (long)FpX_red((GEN)z[i], p);
  return x;
}

/* z in Z^n, return lift(z * Mod(1,p)) */
GEN
FpV_red(GEN z, GEN p)
{
  long i,l = lg(z);
  GEN x = cgetg(l,typ(z));
  for (i=1; i<l; i++) x[i] = lmodii((GEN)z[i],p);
  return x;
}

/* z in Mat m,n(Z), return lift(z * Mod(1,p)) */
GEN
FpM_red(GEN z, GEN p)
{
  long i,j,l = lg(z), m = lg((GEN)z[1]);
  GEN x,y;
  x = cgetg(l,t_MAT);
  for (i=1; i<l; i++)
  {
    x[i]=lgetg(m,t_MAT);y=(GEN)x[i];
    for(j=1; j<m ; j++)
      y[j] = lmodii(gmael(z,i,j),p);
  }
  return x;
}

/* no garbage collection, divide by leading coeff, mod p */
GEN
FpX_normalize(GEN z, GEN p)
{
  GEN p1 = leading_term(z);
  if (gcmp1(p1)) return z;
  return FpX_Fp_mul(z, mpinvmod(p1,p), p);
}

GEN
FpXQX_normalize(GEN z, GEN T, GEN p)
{
  GEN p1 = leading_term(z);
  if (gcmp1(p1)) return z;
  if (!T) return FpX_normalize(z,p);
  return FpXQX_FpXQ_mul(z, FpXQ_inv(p1,T,p), T,p);
}

GEN
small_to_mat(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_MAT);
  for (i=1; i<l; i++) { x[i] = (long)gtovec((GEN)z[i]); settyp(x[i], t_COL); }
  return x;
}

GEN
small_to_pol_i(GEN z, long l)
{
  long i;
  GEN x = cgetg(l,t_POL);
  for (i=2; i<l; i++) x[i] = lstoi(z[i]);
  x[1] = z[1]; return x;
}

/* assume z[i] % p has been done */
GEN
small_to_pol(GEN z, long v)
{
  GEN x = small_to_pol_i(z, lgef(z));
  setvarn(x,v); return x;
}

GEN
pol_to_small(GEN x)
{
  long i, lx = lgef(x);
  GEN a = u_allocpol(lx-3, 0);
  for (i=2; i<lx; i++) a[i] = itos((GEN)x[i]);
  return a;
}

/* z in Z[X,Y] representing an elt in F_p[X,Y] mod pol(Y) i.e F_q[X])
 * in Kronecker form. Recover the "real" z, normalized
 * If p = NULL, use generic functions and the coeff. ring implied by the
 * coefficients of z */
GEN
FqX_from_Kronecker(GEN z, GEN pol, GEN p)
{
  long i,j,lx,l = lgef(z), N = (degpol(pol)<<1) + 1;
  GEN a,x, t = cgetg(N,t_POL);
  t[1] = pol[1] & VARNBITS;
  lx = (l-2) / (N-2); x = cgetg(lx+3,t_POL);
  if (isonstack(pol)) pol = gcopy(pol);
  for (i=2; i<lx+2; i++)
  {
    a = cgetg(3,t_POLMOD); x[i] = (long)a;
    a[1] = (long)pol;
    for (j=2; j<N; j++) t[j] = z[j];
    z += (N-2);
    a[2] = (long)FpX_res(normalizepol_i(t,N), pol,p);
  }
  a = cgetg(3,t_POLMOD); x[i] = (long)a;
  a[1] = (long)pol;
  N = (l-2) % (N-2) + 2;
  for (j=2; j<N; j++) t[j] = z[j];
  a[2] = (long)FpX_res(normalizepol_i(t,N), pol,p);
  return normalizepol_i(x, i+1);
}

/* z in ?[X,Y] mod Q(Y) in Kronecker form ((subst(lift(z), x, y^(2deg(z)-1)))
 * Recover the "real" z, normalized */
GEN
from_Kronecker(GEN z, GEN pol)
{
  return FqX_from_Kronecker(z,pol,NULL);
}

/*******************************************************************/
/*                                                                 */
/*                          MODULAR GCD                            */
/*                                                                 */
/*******************************************************************/
ulong xgcduu(ulong d, ulong d1, int f, ulong* v, ulong* v1, long *s);
/* 1 / Mod(x,p) , or 0 if inverse doesn't exist */
ulong
u_invmod(ulong x, ulong p)
{
  long s;
  ulong xv, xv1, g = xgcduu(p, x, 1, &xv, &xv1, &s);
  if (g != 1UL) return 0UL;
  xv = xv1 % p; if (s < 0) xv = p - xv;
  return xv;
}

#if 0
static ulong
umodratu(GEN a, ulong p)
{
  if (typ(a) == t_INT)
    return umodiu(a,p);
  else { /* assume a a t_FRAC */
    ulong num = umodiu((GEN)a[1],p);
    ulong den = umodiu((GEN)a[2],p);
    return (ulong)mulssmod(num, u_invmod(den,p), p);
  }
}
#endif

/* return x[0 .. dx] mod p as t_VECSMALL. Assume x a t_POL/VECSMALL/INT */
GEN
u_Fp_FpX(GEN x, int malloc, ulong p)
{
  long i, lx;
  GEN a;

  switch (typ(x))
  {
    case t_VECSMALL: return x;
    case t_INT: a = u_allocpol(0, malloc);
      a[2] = umodiu(x, p); return a;
  }
  lx = lgef(x); a = u_allocpol(lx-3, malloc);
  for (i=2; i<lx; i++) a[i] = (long)umodiu((GEN)x[i], p);
  return u_normalizepol(a,lx);
}

GEN
u_Fp_FpM(GEN x, ulong p)
{
  long i,j,m,n = lg(x);
  GEN y = cgetg(n,t_MAT);
  if (n == 1) return y;
  m = lg(x[1]);
  for (j=1; j<n; j++)
  {
    y[j] = (long)cgetg(m,t_VECSMALL);
    for (i=1; i<m; i++) coeff(y,i,j) = (long)umodiu(gcoeff(x,i,j), p);
  }
  return y;
}

static GEN
u_FpX_Fp_mul(GEN y, ulong x,ulong p, int malloc)
{
  GEN z;
  int i, l;
  if (!x) return u_zeropol(malloc);
  l = lgef(y); z = u_allocpol(l-3, malloc);
  if (HIGHWORD(x | p))
    for(i=2; i<l; i++) z[i] = mulssmod(y[i], x, p);
  else
    for(i=2; i<l; i++) z[i] = (y[i] * x) % p;
  return z;
}

GEN
u_FpX_normalize(GEN z, ulong p)
{
  long l = lgef(z)-1;
  ulong p1 = z[l]; /* leading term */
  if (p1 == 1) return z;
  return u_FpX_Fp_mul(z, u_invmod(p1,p), p, 0);
}

static GEN
u_copy(GEN x, int malloc)
{
  long i, l = lgef(x);
  GEN z = u_allocpol(l-3, malloc);
  for (i=2; i<l; i++) z[i] = x[i];
  return z;
}

/* as FpX_divres but working only on ulong types. ASSUME pr != ONLY_DIVIDES */
GEN
u_FpX_divrem(GEN x, GEN y, ulong p, int malloc, GEN *pr)
{
  GEN z,q,c;
  long dx,dy,dz,i,j;
  ulong p1,inv;

  dy = degpol(y);
  if (!dy)
  {
    if (pr)
    {
      if (pr == ONLY_REM) return u_zeropol(malloc);
      *pr = u_zeropol(malloc);
    }
    if (y[2] == 1UL) return u_copy(x,malloc);
    return u_FpX_Fp_mul(x, u_invmod(y[2], p), p, malloc);
  }
  dx = degpol(x);
  dz = dx-dy;
  if (dz < 0)
  {
    if (pr)
    {
      c = u_copy(x, malloc);
      if (pr == ONLY_REM) return c;
      *pr = c;
    }
    return u_zeropol(malloc);
  }
  x += 2;
  y += 2;
  z = u_allocpol(dz, malloc || (pr == ONLY_REM)) + 2;
  inv = y[dy];
  if (inv != 1UL) inv = u_invmod(inv,p);

  if (u_OK_ULONG(p))
  {
    z[dz] = (inv*x[dx]) % p;
    for (i=dx-1; i>=dy; --i)
    {
      p1 = p - x[i]; /* compute -p1 instead of p1 (pb with ulongs otherwise) */
      for (j=i-dy+1; j<=i && j<=dz; j++)
      {
        p1 += z[j]*y[i-j];
        if (p1 & HIGHBIT) p1 = p1 % p;
      }
      p1 %= p;
      z[i-dy] = p1? ((p - p1)*inv) % p: 0;
    }
  }
  else
  {
    z[dz] = mulssmod(inv, x[dx], p);
    for (i=dx-1; i>=dy; --i)
    {
      p1 = p - x[i]; /* compute -p1 instead of p1 (pb with ulongs otherwise) */
      for (j=i-dy+1; j<=i && j<=dz; j++)
        p1 = addssmod(p1, mulssmod(z[j],y[i-j],p), p);
      z[i-dy] = p1? mulssmod(p - p1, inv, p): 0;
    }
  }
  q = u_normalizepol(z-2, dz+3);
  if (!pr) return q;

  c = u_allocpol(dy,malloc) + 2;
  if (u_OK_ULONG(p))
  {
    for (i=0; i<dy; i++)
    {
      p1 = z[0]*y[i];
      for (j=1; j<=i && j<=dz; j++)
      {
        p1 += z[j]*y[i-j];
        if (p1 & HIGHBIT) p1 = p1 % p;
      }
      c[i] = subssmod(x[i], p1%p, p);
    }
  }
  else
  {
    for (i=0; i<dy; i++)
    {
      p1 = mulssmod(z[0],y[i],p);
      for (j=1; j<=i && j<=dz; j++)
        p1 = addssmod(p1, mulssmod(z[j],y[i-j],p), p);
      c[i] = subssmod(x[i], p1, p);
    }
  }
  i=dy-1; while (i>=0 && !c[i]) i--;
  c = u_normalizepol(c-2, i+3);
  if (pr == ONLY_REM) { free(q); return c; }
  *pr = c; return q;
}

/* x and y in Z[X]. Possibly x in Z */
GEN
FpX_divres(GEN x, GEN y, GEN p, GEN *pr)
{
  long vx,dx,dy,dz,i,j,av0,av,tetpil,sx,lrem;
  GEN z,p1,rem,lead;

  if (!p) return poldivres(x,y,pr);
  if (!signe(y)) err(talker,"division by zero in FpX_divres");
  vx=varn(x); dy=degpol(y); dx=(typ(x)==t_INT)? 0: degpol(x);
  if (dx < dy)
  {
    if (pr)
    {
      av0 = avma; x = FpX_red(x, p);
      if (pr == ONLY_DIVIDES) { avma=av0; return signe(x)? NULL: gzero; }
      if (pr == ONLY_REM) return x;
      *pr = x;
    }
    return zeropol(vx);
  }
  lead = leading_term(y);
  if (!dy) /* y is constant */
  {
    if (pr && pr != ONLY_DIVIDES)
    {
      if (pr == ONLY_REM) return zeropol(vx);
      *pr = zeropol(vx);
    }
    if (gcmp1(lead)) return gcopy(x);
    av0 = avma; x = gmul(x, mpinvmod(lead,p)); tetpil = avma;
    return gerepile(av0,tetpil,FpX_red(x,p));
  }
  av0 = avma; dz = dx-dy;
  if (OK_ULONG(p))
  { /* assume ab != 0 mod p */
    ulong pp = (ulong)p[2];
    GEN a = u_Fp_FpX(x,1, pp);
    GEN b = u_Fp_FpX(y,1, pp);
    GEN zz= u_FpX_divrem(a,b,pp,1, pr);
    if (pr && pr != ONLY_DIVIDES && pr != ONLY_REM)
    {
      rem = small_to_pol(*pr,vx);
      free(*pr); *pr = rem;
    }
    z = small_to_pol(zz,vx);
    free(zz); free(a); free(b); return z;
  }
  lead = gcmp1(lead)? NULL: gclone(mpinvmod(lead,p));
  avma = av0;
  z=cgetg(dz+3,t_POL);
  z[1]=evalsigne(1) | evallgef(dz+3) | evalvarn(vx);
  x += 2; y += 2; z += 2;

  p1 = (GEN)x[dx]; av = avma;
  z[dz] = lead? lpileupto(av, modii(mulii(p1,lead), p)): licopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av=avma; p1=(GEN)x[i];
    for (j=i-dy+1; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii((GEN)z[j],(GEN)y[i-j]));
    if (lead) p1 = mulii(p1,lead);
    tetpil=avma; z[i-dy] = lpile(av,tetpil,modii(p1, p));
  }
  if (!pr) { if (lead) gunclone(lead); return z-2; }

  rem = (GEN)avma; av = (long)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = (GEN)x[i];
    for (j=0; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii((GEN)z[j],(GEN)y[i-j]));
    tetpil=avma; p1 = modii(p1,p); if (signe(p1)) { sx = 1; break; }
    if (!i) break;
    avma=av;
  }
  if (pr == ONLY_DIVIDES)
  {
    if (lead) gunclone(lead);
    if (sx) { avma=av0; return NULL; }
    avma = (long)rem; return z-2;
  }
  lrem=i+3; rem -= lrem;
  rem[0]=evaltyp(t_POL) | evallg(lrem);
  rem[1]=evalsigne(1) | evalvarn(vx) | evallgef(lrem);
  p1 = gerepile((long)rem,tetpil,p1);
  rem += 2; rem[i]=(long)p1;
  for (i--; i>=0; i--)
  {
    av=avma; p1 = (GEN)x[i];
    for (j=0; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii((GEN)z[j],(GEN)y[i-j]));
    tetpil=avma; rem[i]=lpile(av,tetpil, modii(p1,p));
  }
  rem -= 2;
  if (lead) gunclone(lead);
  if (!sx) normalizepol_i(rem, lrem);
  if (pr == ONLY_REM) return gerepileupto(av0,rem);
  *pr = rem; return z-2;
}

/* x and y in Z[Y][X]. Assume T irreducible mod p */
GEN
FpXQX_divres(GEN x, GEN y, GEN T, GEN p, GEN *pr)
{
  long vx,dx,dy,dz,i,j,av0,av,tetpil,sx,lrem;
  GEN z,p1,rem,lead;

  if (!p) return poldivres(x,y,pr);
  if (!T) return FpX_divres(x,y,p,pr);
  if (!signe(y)) err(talker,"division by zero in FpX_divres");
  vx=varn(x); dy=degpol(y); dx=degpol(x);
  if (dx < dy)
  {
    if (pr)
    {
      av0 = avma; x = FpXQX_red(x, T, p);
      if (pr == ONLY_DIVIDES) { avma=av0; return signe(x)? NULL: gzero; }
      if (pr == ONLY_REM) return x;
      *pr = x;
    }
    return zeropol(vx);
  }
  lead = leading_term(y);
  if (!dy) /* y is constant */
  {
    if (pr && pr != ONLY_DIVIDES)
    {
      if (pr == ONLY_REM) return zeropol(vx);
      *pr = zeropol(vx);
    }
    if (gcmp1(lead)) return gcopy(x);
    av0 = avma; x = gmul(x, FpXQ_inv(lead,T,p)); tetpil = avma;
    return gerepile(av0,tetpil,FpXQX_red(x,T,p));
  }
  av0 = avma; dz = dx-dy;
#if 0 /* FIXME: to be done */
  if (OK_ULONG(p))
  { /* assume ab != 0 mod p */
    ulong pp = (ulong)p[2];
    GEN a = u_Fp_FpX(x,1, pp);
    GEN b = u_Fp_FpX(y,1, pp);
    GEN zz= u_FpX_divrem(a,b,pp,1, pr);
    if (pr && pr != ONLY_DIVIDES && pr != ONLY_REM)
    {
      rem = small_to_pol(*pr,vx);
      free(*pr); *pr = rem;
    }
    z = small_to_pol(zz,vx);
    free(zz); free(a); free(b); return z;
  }
#endif
  lead = gcmp1(lead)? NULL: gclone(FpXQ_inv(lead,T,p));
  avma = av0;
  z=cgetg(dz+3,t_POL);
  z[1]=evalsigne(1) | evallgef(dz+3) | evalvarn(vx);
  x += 2; y += 2; z += 2;

  p1 = (GEN)x[dx]; av = avma;
  z[dz] = lead? lpileupto(av, FpX_res(gmul(p1,lead), T, p)): lcopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av=avma; p1=(GEN)x[i];
    for (j=i-dy+1; j<=i && j<=dz; j++)
      p1 = gsub(p1, gmul((GEN)z[j],(GEN)y[i-j]));
    if (lead) p1 = gmul(FpX_res(p1, T, p), lead);
    tetpil=avma; z[i-dy] = lpile(av,tetpil,FpX_res(p1, T, p));
  }
  if (!pr) { if (lead) gunclone(lead); return z-2; }

  rem = (GEN)avma; av = (long)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = (GEN)x[i];
    for (j=0; j<=i && j<=dz; j++)
      p1 = gsub(p1, gmul((GEN)z[j],(GEN)y[i-j]));
    tetpil=avma; p1 = FpX_res(p1, T, p); if (signe(p1)) { sx = 1; break; }
    if (!i) break;
    avma=av;
  }
  if (pr == ONLY_DIVIDES)
  {
    if (lead) gunclone(lead);
    if (sx) { avma=av0; return NULL; }
    avma = (long)rem; return z-2;
  }
  lrem=i+3; rem -= lrem;
  rem[0]=evaltyp(t_POL) | evallg(lrem);
  rem[1]=evalsigne(1) | evalvarn(vx) | evallgef(lrem);
  p1 = gerepile((long)rem,tetpil,p1);
  rem += 2; rem[i]=(long)p1;
  for (i--; i>=0; i--)
  {
    av=avma; p1 = (GEN)x[i];
    for (j=0; j<=i && j<=dz; j++)
      p1 = gsub(p1, gmul((GEN)z[j],(GEN)y[i-j]));
    tetpil=avma; rem[i]=lpile(av,tetpil, FpX_res(p1, T, p));
  }
  rem -= 2;
  if (lead) gunclone(lead);
  if (!sx) normalizepol_i(rem, lrem);
  if (pr == ONLY_REM) return gerepileupto(av0,rem);
  *pr = rem; return z-2;
}

static GEN
FpX_gcd_long(GEN x, GEN y, GEN p)
{
  ulong pp = (ulong)p[2], av = avma;
  GEN a,b;

  (void)new_chunk((lgef(x) + lgef(y)) << 2); /* scratch space */
  a = u_Fp_FpX(x,0, pp);
  if (!signe(a)) { avma = av; return FpX_red(y,p); }
  b = u_Fp_FpX(y,0, pp);
  a = u_FpX_gcd_i(a,b, pp);
  avma = av; return small_to_pol(a, varn(x));
}

/* x and y in Z[X], return lift(gcd(x mod p, y mod p)) */
GEN
FpX_gcd(GEN x, GEN y, GEN p)
{
  GEN a,b,c;
  long av0,av;

  if (OK_ULONG(p)) return FpX_gcd_long(x,y,p);
  av0=avma;
  a = FpX_red(x, p); av = avma;
  b = FpX_red(y, p);
  while (signe(b))
  {
    av = avma; c = FpX_res(a,b,p); a=b; b=c;
  }
  avma = av; return gerepileupto(av0, a);
}

GEN
u_FpX_sub(GEN x, GEN y, ulong p)
{
  long i,lz,lx = lgef(x), ly = lgef(y);
  GEN z;

  if (ly <= lx)
  {
    lz = lx; z = cgetg(lz,t_VECSMALL);
    for (i=2; i<ly; i++) z[i] = subssmod(x[i],y[i],p);
    for (   ; i<lx; i++) z[i] = x[i];
  }
  else
  {
    lz = ly; z = cgetg(lz,t_VECSMALL);
    for (i=2; i<lx; i++) z[i] = subssmod(x[i],y[i],p);
    for (   ; i<ly; i++) z[i] = y[i]? p - y[i]: y[i];
  }
  z[1]=0; return u_normalizepol(z, lz);
}

/* list of u_FpX in gptr, return then as GEN */
static void
u_gerepilemany(long av, GEN* gptr[], long n, long v)
{
  GEN *l = (GEN*)gpmalloc(n*sizeof(GEN));
  long i;

  /* copy objects */
  for (i=0; i<n; i++) l[i] = gclone(*(gptr[i]));
  avma = av;
  /* copy them back, kill clones */
  for (--i; i>=0; i--)
  {
    *(gptr[i]) = small_to_pol(l[i],v);
    gunclone(l[i]);
  }
  free(l);
}

static GEN
u_FpX_extgcd(GEN a, GEN b, ulong p, GEN *ptu, GEN *ptv)
{
  GEN q,z,u,v, x = a, y = b;

  u = u_zeropol(0);
  v= u_scalarpol(1, 0); /* v = 1 */
  while (signe(y))
  {
    q = u_FpX_divrem(x,y,p, 0,&z);
    x = y; y = z; /* (x,y) = (y, x - q y) */
    z = u_FpX_sub(u, u_FpX_mul(q,v, p), p);
    u = v; v = z; /* (u,v) = (v, u - q v) */
  }
  z = u_FpX_sub(x, u_FpX_mul(b,u,p), p);
  z = u_FpX_div(z,a,p);
  *ptu = z;
  *ptv = u; return x;
}

static GEN
FpX_extgcd_long(GEN x, GEN y, GEN p, GEN *ptu, GEN *ptv)
{
  ulong pp = (ulong)p[2];
  long av = avma;
  GEN a, b, d;

  a = u_Fp_FpX(x,0, pp);
  b = u_Fp_FpX(y,0, pp);
  d = u_FpX_extgcd(a,b, pp, ptu,ptv);
  {
    GEN *gptr[3]; gptr[0] = &d; gptr[1] = ptu; gptr[2] = ptv;
    u_gerepilemany(av, gptr, 3, varn(x));
  }
  return d;
}

/* x and y in Z[X], return lift(gcd(x mod p, y mod p)). Set u and v st
 * ux + vy = gcd (mod p) */
GEN
FpX_extgcd(GEN x, GEN y, GEN p, GEN *ptu, GEN *ptv)
{
  GEN a,b,q,r,u,v,d,d1,v1;
  long ltop,lbot;

  if (OK_ULONG(p)) return FpX_extgcd_long(x,y,p,ptu,ptv);
  ltop=avma;
  a = FpX_red(x, p);
  b = FpX_red(y, p);
  d = a; d1 = b; v = gzero; v1 = gun;
  while (signe(d1))
  {
    q = FpX_divres(d,d1,p, &r);
    v = gadd(v, gneg_i(gmul(q,v1)));
    v = FpX_red(v,p);
    u=v; v=v1; v1=u;
    u=r; d=d1; d1=u;
  }
  u = gadd(d, gneg_i(gmul(b,v)));
  u = FpX_red(u, p);
  lbot = avma;
  u = FpX_div(u,a,p);
  d = gcopy(d);
  v = gcopy(v);
  {
    GEN *gptr[3]; gptr[0] = &d; gptr[1] = &u; gptr[2] = &v;
    gerepilemanysp(ltop,lbot,gptr,3);
  }
  *ptu = u; *ptv = v; return d;
}

/* x and y in Z[Y][X], return lift(gcd(x mod T,p, y mod T,p)). Set u and v st
 * ux + vy = gcd (mod T,p) */
GEN
FpXQX_extgcd(GEN x, GEN y, GEN T, GEN p, GEN *ptu, GEN *ptv)
{
  GEN a,b,q,r,u,v,d,d1,v1;
  long ltop,lbot;

#if 0 /* FIXME To be done...*/ 
  if (OK_ULONG(p)) return FpXQX_extgcd_long(x,y,T,p,ptu,ptv);
#endif
  if (!T) return FpX_extgcd(x,y,p,ptu,ptv);
  ltop=avma;
  a = FpXQX_red(x, T, p);
  b = FpXQX_red(y, T, p);
  d = a; d1 = b; v = gzero; v1 = gun;
  while (signe(d1))
  {
    q = FpXQX_divres(d,d1,T,p, &r);
    v = gadd(v, gneg_i(gmul(q,v1)));
    v = FpXQX_red(v,T,p);
    u=v; v=v1; v1=u;
    u=r; d=d1; d1=u;
  }
  u = gadd(d, gneg_i(gmul(b,v)));
  u = FpXQX_red(u,T, p);
  lbot = avma;
  u = FpXQX_divres(u,a,T,p,NULL);
  d = gcopy(d);
  v = gcopy(v);
  {
    GEN *gptr[3]; gptr[0] = &d; gptr[1] = &u; gptr[2] = &v;
    gerepilemanysp(ltop,lbot,gptr,3);
  }
  *ptu = u; *ptv = v; return d;
}

extern GEN caractducos(GEN p, GEN x, int v);

GEN
FpXQ_charpoly(GEN x, GEN T, GEN p)
{
  ulong ltop=avma;
  GEN R=lift(caractducos(FpX(T,p),FpX(x,p),varn(T)));
  return gerepileupto(ltop,R);
}

GEN 
FpXQ_minpoly(GEN x, GEN T, GEN p)
{
  ulong ltop=avma;
  GEN R=FpXQ_charpoly(x, T, p);
  GEN G=FpX_gcd(R,derivpol(R),p);
  G=FpX_normalize(G,p);
  G=FpX_div(R,G,p);
  return gerepileupto(ltop,G);
}

/* return z = a mod q, b mod p (p,q) = 1. qinv = 1/q mod p */
static GEN
u_chrem_coprime(GEN a, ulong b, GEN q, ulong p, ulong qinv, GEN pq)
{
  ulong av = avma, d, amod = umodiu(a,p);
  GEN ax;

  if (b == amod) return NULL;
  d = (b > amod)? b - amod: p - (amod - b); /* (b - a) mod p */
  (void)new_chunk(lgefint(pq)<<1); /* HACK */
  ax = mului(mulssmod(d,qinv,p), q); /* d mod p, 0 mod q */
  avma = av; return addii(a, ax); /* in ]-q, pq[ assuming a in -]-q,q[ */
}

/* centerlift(u mod p) */
GEN
u_center(ulong u, ulong p, ulong ps2)
{
  return stoi((long) (u > ps2)? u - p: u);
}

GEN
ZX_init_CRT(GEN Hp, ulong p, long v)
{
  long i, l = lgef(Hp), lim = (long)(p>>1);
  GEN H = cgetg(l, t_POL);
  H[1] = evalsigne(1)|evallgef(l)|evalvarn(v);
  for (i=2; i<l; i++)
    H[i] = (long)u_center(Hp[i], p, lim);
  return H;
}

/* assume lg(Hp) > 1 */
GEN 
ZM_init_CRT(GEN Hp, ulong p)
{
  long i,j, m = lg(Hp[1]), l = lg(Hp), lim = (long)(p>>1);
  GEN c,cp,H = cgetg(l, t_MAT);
  for (j=1; j<l; j++)
  {
    cp = (GEN)Hp[j];
    c = cgetg(m, t_COL);
    H[j] = (long)c;
    for (i=1; i<l; i++) c[i] = (long)u_center(cp[i],p, lim);
  }   
  return H;
}

int
Z_incremental_CRT(GEN *H, ulong Hp, GEN q, GEN qp, ulong p)
{
  GEN h, lim = shifti(qp,-1);
  ulong qinv = u_invmod(umodiu(q,p), p);
  int stable = 1;
  h = u_chrem_coprime(*H,Hp,q,p,qinv,qp);
  if (h)
  {
    if (cmpii(h,lim) > 0) h = subii(h,qp);
    *H = h; stable = 0;
  }
  return stable;
}

int
ZX_incremental_CRT(GEN H, GEN Hp, GEN q, GEN qp, ulong p)
{
  GEN h, lim = shifti(qp,-1);
  ulong qinv = u_invmod(umodiu(q,p), p);
  long i, l = lgef(H), lp = lgef(Hp);
  int stable = 1;
  for (i=2; i<lp; i++)
  {
    h = u_chrem_coprime((GEN)H[i],Hp[i],q,p,qinv,qp);
    if (h)
    {
      if (cmpii(h,lim) > 0) h = subii(h,qp);
      H[i] = (long)h; stable = 0;
    }
  }
  for (   ; i<l; i++)
  {
    h = u_chrem_coprime((GEN)H[i],   0,q,p,qinv,qp);
    if (h)
    {
      if (cmpii(h,lim) > 0) h = subii(h,qp);
      H[i] = (long)h; stable = 0;
    }
  }
  return stable;
}

int
ZM_incremental_CRT(GEN H, GEN Hp, GEN q, GEN qp, ulong p)
{
  GEN h, lim = shifti(qp,-1);
  ulong qinv = u_invmod(umodiu(q,p), p);
  long i,j, l = lg(H), m = lg(H[1]);
  int stable = 1;
  for (j=1; j<l; j++)
    for (i=1; i<m; i++)
    {
      h = u_chrem_coprime(gcoeff(H,i,j), coeff(Hp,i,j),q,p,qinv,qp);
      if (h)
      {
        if (cmpii(h,lim) > 0) h = subii(h,qp);
        coeff(H,i,j) = (long)h; stable = 0;
      }
    }
  return stable;
}

/* returns a polynomial in variable v, whose coeffs correspond to the digits
 * of m (in base p) */
GEN
stopoly(long m, long p, long v)
{
  GEN y = cgetg(BITS_IN_LONG + 2, t_POL);
  long l=2;

  do { y[l++] = lstoi(m%p); m=m/p; } while (m);
  y[1] = evalsigne(1)|evallgef(l)|evalvarn(v);
  return y;
}

GEN
stopoly_gen(GEN m, GEN p, long v)
{
  GEN y = cgetg(bit_accuracy(lgefint(m))+2, t_POL);
  long l=2;

  do { y[l++] = lmodii(m,p); m=divii(m,p); } while (signe(m));
  y[1] = evalsigne(1)|evallgef(l)|evalvarn(v);
  return y;
}

/* modular power */
ulong
powuumod(ulong x, ulong n0, ulong p)
{
  ulong y, z, n;
  if (n0 <= 2)
  { /* frequent special cases */
    if (n0 == 2) return mulssmod(x,x,p);
    if (n0 == 1) return x;
    if (n0 == 0) return 1;
  }
  y = 1; z = x; n = n0;
  for(;;)
  {
    if (n&1) y = mulssmod(y,z,p);
    n>>=1; if (!n) return y;
    z = mulssmod(z,z,p);
  }
}

/* separate from u_FpX_divrem for maximal speed. Implicitly malloc = 0  */
GEN
u_FpX_rem(GEN x, GEN y, ulong p)
{
  GEN z, c;
  long dx,dy,dz,i,j;
  ulong p1,inv;

  dy = degpol(y); if (!dy) return u_zeropol(0);
  dx = degpol(x);
  dz = dx-dy; if (dz < 0) return u_copy(x, 0);
  x += 2;
  y += 2;
  z = u_allocpol(dz, 1) + 2;
  inv = y[dy];
  if (inv != 1UL) inv = u_invmod(inv,p);

  c = u_allocpol(dy,0) + 2;
  if (u_OK_ULONG(p))
  {
    z[dz] = (inv*x[dx]) % p;
    for (i=dx-1; i>=dy; --i)
    {
      p1 = p - x[i]; /* compute -p1 instead of p1 (pb with ulongs otherwise) */
      for (j=i-dy+1; j<=i && j<=dz; j++)
      {
        p1 += z[j]*y[i-j];
        if (p1 & HIGHBIT) p1 = p1 % p;
      }
      p1 %= p;
      z[i-dy] = p1? ((p - p1)*inv) % p: 0;
    }
    for (i=0; i<dy; i++)
    {
      p1 = z[0]*y[i];
      for (j=1; j<=i && j<=dz; j++)
      {
        p1 += z[j]*y[i-j];
        if (p1 & HIGHBIT) p1 = p1 % p;
      }
      c[i] = subssmod(x[i], p1%p, p);
    }
  }
  else
  {
    z[dz] = mulssmod(inv, x[dx], p);
    for (i=dx-1; i>=dy; --i)
    {
      p1 = p - x[i]; /* compute -p1 instead of p1 (pb with ulongs otherwise) */
      for (j=i-dy+1; j<=i && j<=dz; j++)
        p1 = addssmod(p1, mulssmod(z[j],y[i-j],p), p);
      z[i-dy] = p1? mulssmod(p - p1, inv, p): 0;
    }
    for (i=0; i<dy; i++)
    {
      p1 = mulssmod(z[0],y[i],p);
      for (j=1; j<=i && j<=dz; j++)
        p1 = addssmod(p1, mulssmod(z[j],y[i-j],p), p);
      c[i] = subssmod(x[i], p1, p);
    }
  }
  i = dy-1; while (i>=0 && !c[i]) i--;
  free(z-2); return u_normalizepol(c-2, i+3);
}

ulong
u_FpX_resultant(GEN a, GEN b, ulong p)
{
  long da,db,dc,cnt;
  ulong lb,av, res = 1UL;
  GEN c;

  if (!signe(a) || !signe(b)) return 0;
  da = degpol(a);
  db = degpol(b);
  if (db > da)
  {
    swapspec(a,b, da,db);
    if (da & db & 1) res = p-res;
  }
  if (!da) return 1; /* = res * a[2] ^ db, since 0 <= db <= da = 0 */
  cnt = 0; av = avma;
  while (db)
  {
    lb = b[db+2];
    c = u_FpX_rem(a,b, p);
    a = b; b = c; dc = degpol(c);
    if (dc < 0) { avma = av; return 0; }

    if (da & db & 1) res = p - res;
    if (lb != 1) res = mulssmod(res, powuumod(lb, da - dc, p), p);
    if (++cnt == 4) { cnt = 0; avma = av; }
    da = db; /* = degpol(a) */
    db = dc; /* = degpol(b) */
  }
  avma = av; return mulssmod(res, powuumod(b[2], da, p), p);
}

/* If resultant is 0, *ptU and *ptU are not set */
ulong
u_FpX_extresultant(GEN a, GEN b, ulong p, GEN *ptU, GEN *ptV)
{
  GEN z,q,u,v, x = a, y = b;
  ulong lb, av = avma, res = 1UL;
  long dx,dy,dz;

  if (!signe(x) || !signe(y)) return 0;
  dx = degpol(x);
  dy = degpol(y);
  if (dy > dx)
  {
    swap(x,y); lswap(dx,dy); pswap(ptU, ptV);
    a = x; b = y;
    if (dx & dy & 1) res = p-res;
  }
  u = u_zeropol(0);
  v = u_scalarpol(1, 0); /* v = 1 */
  while (dy)
  { /* b u = x (a), b v = y (a) */
    lb = y[dy+2];
    q = u_FpX_divrem(x,y, p, 0, &z);
    x = y; y = z; /* (x,y) = (y, x - q y) */
    dz = degpol(z); if (dz < 0) { avma = av; return 0; }
    z = u_FpX_sub(u, u_FpX_mul(q,v, p), p);
    u = v; v = z; /* (u,v) = (v, u - q v) */

    if (dx & dy & 1) res = p - res;
    if (lb != 1) res = mulssmod(res, powuumod(lb, dx-dz, p), p);
    dx = dy; /* = degpol(x) */
    dy = dz; /* = degpol(y) */
  }
  res = mulssmod(res, powuumod(y[2], dx, p), p);
  lb = mulssmod(res, u_invmod(y[2],p), p);
  v = gerepileupto(av, u_FpX_Fp_mul(v, lb, p, 0));
  av = avma;
  u = u_FpX_sub(u_scalarpol(res,0), u_FpX_mul(b,v,p), p);
  u = gerepileupto(av, u_FpX_div(u,a,p)); /* = (res - b v) / a */
  *ptU = u;
  *ptV = v; return res;
}

/* assuming the PRS finishes on a degree 1 polynomial C0 + C1X, with "generic"
 * degree sequence as given by dglist, set *Ci and return resultant(a,b) */
ulong
u_FpX_resultant_all(GEN a, GEN b, long *C0, long *C1, GEN dglist, ulong p)
{
  long da,db,dc,cnt,ind;
  ulong lb,av,cx = 1, res = 1UL;
  GEN c;

  if (C0) { *C0 = 1; *C1 = 0; }
  if (!signe(a) || !signe(b)) return 0;
  da = degpol(a);
  db = degpol(b);
  if (db > da)
  {
    swapspec(a,b, da,db);
    if (da & db & 1) res = p-res;
  }
  /* = res * a[2] ^ db, since 0 <= db <= da = 0 */
  if (!da) return 1;
  cnt = ind = 0; av = avma;
  while (db)
  {
    lb = b[db+2];
    c = u_FpX_rem(a,b, p);
    a = b; b = c; dc = degpol(c);
    if (dc < 0) { avma = av; return 0; }

    ind++;
    if (C0)
    { /* check that Euclidean remainder sequence doesn't degenerate */
      if (dc != dglist[ind]) { avma = av; return 0; }
      /* update resultant */
      if (da & db & 1) res = p-res;
      if (lb != 1)
      {
        ulong t = powuumod(lb, da - dc, p);
        res = mulssmod(res, t, p);
        if (dc) cx = mulssmod(cx, t, p);
      }
    }
    else
    {
      if (dc > dglist[ind]) dglist[ind] = dc;
    }
    if (++cnt == 4) { cnt = 0; avma = av; }
    da = db; /* = degpol(a) */
    db = dc; /* = degpol(b) */
  }
  if (!C0)
  {
    if (ind+1 > lg(dglist)) setlg(dglist,ind+1);
    return 0;
  }

  if (da == 1) /* last non-constant polynomial has degree 1 */
  {
    *C0 = mulssmod(cx, a[2], p);
    *C1 = mulssmod(cx, a[3], p);
    lb = b[2];
  } else lb = powuumod(b[2], da, p);
  avma = av; return mulssmod(res, lb, p);
}

static ulong global_pp;
static GEN
_u_FpX_mul(GEN a, GEN b)
{
  return u_FpX_mul(a,b, global_pp);
}

/* compute prod (x - a[i]) */
GEN
u_FpV_roots_to_pol(GEN a, ulong p)
{
  long i,k,lx = lg(a);
  GEN p1,p2;
  if (lx == 1) return polun[0];
  p1 = cgetg(lx, t_VEC); global_pp = p;
  for (k=1,i=1; i<lx-1; i+=2)
  {
    p2 = cgetg(5,t_VECSMALL); p1[k++] = (long)p2;
    p2[2] = mulssmod(a[i], a[i+1], p);
    p2[3] = (p<<1) - (a[i] + a[i+1]);
    p2[4] = 1; p2[1] = evallgef(5);
  }
  if (i < lx)
  {
    p2 = cgetg(4,t_POL); p1[k++] = (long)p2;
    p2[1] = evallgef(4);
    p2[2] = p - a[i];
    p2[3] = 1;
  }
  setlg(p1, k); return divide_conquer_prod(p1, _u_FpX_mul);
}


/* u P(X) + v P(-X) */
static GEN
pol_comp(GEN P, GEN u, GEN v)
{
  long i, l = lgef(P);
  GEN y = cgetg(l, t_POL);
  for (i=2; i<l; i++)
  {
    GEN t = (GEN)P[i];
    y[i] = gcmp0(t)? zero:
                     (i&1)? lmul(t, gsub(u,v)) /*  odd degree */
                          : lmul(t, gadd(u,v));/* even degree */
  }
  y[1] = P[1]; return normalizepol_i(y,l);
}

static GEN
u_pol_comp(GEN P, ulong u, ulong v, ulong p)
{
  long i, l = lgef(P);
  GEN y = u_allocpol(l-3, 0);
  for (i=2; i<l; i++)
  {
    ulong t = P[i];
    y[i] = (t == 0)? 0:
                     (i&1)? mulssmod(t, u + (p - v), p)
                          : mulssmod(t, u + v, p);
  }
  return u_normalizepol(y,l);
}

GEN roots_to_pol(GEN a, long v);

GEN
polint_triv(GEN xa, GEN ya)
{
  GEN P = NULL, Q = roots_to_pol(xa,0);
  long i, n = lg(xa), av = avma, lim = stack_lim(av,2);
  for (i=1; i<n; i++)
  {
    GEN T,dP;
    if (gcmp0((GEN)ya[i])) continue;
    T = gdeuc(Q, gsub(polx[0], (GEN)xa[i]));
    if (i < n-1 && absi_equal((GEN)xa[i], (GEN)xa[i+1]))
    { /* x_i = -x_{i+1} */
      T = gdiv(T, poleval(T, (GEN)xa[i]));
      dP = pol_comp(T, (GEN)ya[i], (GEN)ya[i+1]);
      i++;
    }
    else
    {
      dP = gmul((GEN)ya[i], T);
      dP = gdiv(dP, poleval(T,(GEN)xa[i]));
    }
    P = P? gadd(P, dP): dP;
    if (low_stack(lim,stack_lim(av,2)))
    {
      if (DEBUGMEM>1) err(warnmem,"polint_triv2 (i = %ld)",i);
      P = gerepileupto(av, P);
    }
  }
  return P? P: zeropol(0);
}

ulong
u_FpX_eval(GEN x, ulong y, ulong p)
{
  ulong p1,r;
  long i,j;
  i=lgef(x)-1;
  if (i<=2)
    return (i==2)? x[2]: 0;
  p1 = x[i];
  /* specific attention to sparse polynomials (see poleval)*/
  if (u_OK_ULONG(p))
  {
    for (i--; i>=2; i=j-1)
    {
      for (j=i; !x[j]; j--)
        if (j==2)
        {
          if (i != j) y = powuumod(y, i-j+1, p);
          return (p1 * y) % p;
        }
      r = (i==j)? y: powuumod(y, i-j+1, p);
      p1 = ((p1*r) + x[j]) % p;
    }
  }
  else
  {
    for (i--; i>=2; i=j-1)
    {
      for (j=i; !x[j]; j--)
        if (j==2)
        {
          if (i != j) y = powuumod(y, i-j+1, p);
          return mulssmod(p1, y, p);
        }
      r = (i==j)? y: powuumod(y, i-j+1, p);
      p1 = addssmod(x[j], mulssmod(p1,r,p), p);
    }
  }
  return p1;
}

static GEN
u_FpX_div_by_X_x(GEN a, ulong x, ulong p)
{
  long l = lgef(a), i;
  GEN z = u_allocpol(l-4, 0), a0, z0;
  a0 = a + l-1;
  z0 = z + l-2; *z0 = *a0--;
  if (u_OK_ULONG(p))
  {
    for (i=l-3; i>1; i--) /* z[i] = (a[i+1] + x*z[i+1]) % p */
    {
      ulong t = (*a0-- + x *  *z0--) % p;
      *z0 = t;
    }
  }
  else
  {
    for (i=l-3; i>1; i--)
    {
      ulong t = addssmod(*a0--, mulssmod(x, *z0--, p), p);
      *z0 = t;
    }
  }
  return z;
}

/* xa, ya = t_VECSMALL */
GEN
u_FpV_polint(GEN xa, GEN ya, ulong p)
{
  GEN T,dP, P = NULL, Q = u_FpV_roots_to_pol(xa, p);
  long i, n = lg(xa);
  ulong av, inv;
  av = avma; (void)new_chunk(n+3); /* storage space for P */
  for (i=1; i<n; i++)
  {
    if (!ya[i]) continue;
    T = u_FpX_div_by_X_x(Q, xa[i], p);
    inv = u_invmod(u_FpX_eval(T,xa[i], p), p);
    if (i < n-1 && (ulong)(xa[i] + xa[i+1]) == p)
    {
      dP = u_pol_comp(T, mulssmod(ya[i],inv,p), mulssmod(ya[i+1],inv,p), p);
      i++; /* x_i = -x_{i+1} */
    }
    else
      dP = u_FpX_Fp_mul(T, mulssmod(ya[i],inv,p), p, 0);
    if (P) avma = av;
    P = P? u_FpX_add(P, dP, p): dP;
  }
  return P? P: u_zeropol(0);
}

static void
u_FpV_polint_all(GEN xa, GEN ya, GEN C0, GEN C1, ulong p)
{
  GEN T,Q = u_FpV_roots_to_pol(xa, p);
  GEN dP  = NULL,  P = NULL;
  GEN dP0 = NULL, P0= NULL;
  GEN dP1 = NULL, P1= NULL;
  long i, n = lg(xa);
  ulong inv;
  for (i=1; i<n; i++)
  {
    T = u_FpX_div_by_X_x(Q, xa[i], p);
    inv = u_invmod(u_FpX_eval(T,xa[i], p), p);

#if 0
    if (i < n-1 && (ulong)(xa[i] + xa[i+1]) == p)
    {
      if (ya[i])
        dP = u_pol_comp(T, mulssmod(ya[i],inv,p), mulssmod(ya[i+1],inv,p), p);
      if (C0[i])
        dP0= u_pol_comp(T, mulssmod(C0[i],inv,p), mulssmod(C0[i+1],inv,p), p);
      if (C1[i])
        dP1= u_pol_comp(T, mulssmod(C1[i],inv,p), mulssmod(C1[i+1],inv,p), p);
      i++; /* x_i = -x_{i+1} */
    }
    else
#endif
    {
      if (ya[i])
      {
        dP = u_FpX_Fp_mul(T, mulssmod(ya[i],inv,p), p, 0);
        P = P ? u_FpX_add(P , dP , p): dP;
      }
      if (C0[i])
      {
        dP0= u_FpX_Fp_mul(T, mulssmod(C0[i],inv,p), p, 0);
        P0= P0? u_FpX_add(P0, dP0, p): dP0;
      }
      if (C1[i])
      {
        dP1= u_FpX_Fp_mul(T, mulssmod(C1[i],inv,p), p, 0);
        P1= P1? u_FpX_add(P1, dP1, p): dP1;
      }
    }
  }
  ya[1] = (long) (P ? P : u_zeropol(0));
  C0[1] = (long) (P0? P0: u_zeropol(0));
  C1[1] = (long) (P1? P1: u_zeropol(0));
}

/* b a vector of polynomials representing B in Fp[X][Y], evaluate at X = x,
 * Return 0 in case of degree drop. */
static GEN
vec_u_FpX_eval(GEN b, ulong x, ulong p)
{
  GEN z;
  long i, lb = lgef(b);
  ulong leadz = u_FpX_eval((GEN)b[lb-1], x, p);
  if (!leadz) return u_zeropol(0);

  z = u_allocpol(lb-3, 0);
  for (i=2; i<lb-1; i++)
    z[i] = u_FpX_eval((GEN)b[i], x, p);
  z[i] = leadz; return z;
}

/* as above, but don't care about degree drop */
static GEN
vec_u_FpX_eval_gen(GEN b, ulong x, ulong p, int *drop)
{
  GEN z;
  long i, lb = lgef(b);
  z = u_allocpol(lb-3, 0);
  for (i=2; i<lb; i++)
    z[i] = u_FpX_eval((GEN)b[i], x, p);
  z = u_normalizepol(z, lb);
  *drop = lb - lgef(z);
  return z;
}

/* Interpolate at roots of 1 and use Hadamard bound for univariate resultant:
 *   bound = N_2(A)^degpol B N_2(B)^degpol(A),  where  N_2(A) = sqrt(sum (N_1(Ai))^2)
 * Return B such that bound < 2^B */
ulong
ZY_ZXY_ResBound(GEN A, GEN B)
{
  ulong av = avma;
  GEN a = gzero, b = gzero, run = realun(DEFAULTPREC);
  long i , lA = lgef(A), lB = lgef(B);
  for (i=2; i<lA; i++) a = addii(a, sqri((GEN)A[i]));
  for (i=2; i<lB; i++)
  {
    GEN t = (GEN)B[i];
    if (typ(t) == t_POL) t = gnorml1(t, 0);
    b = addii(b, sqri(t));
  }
  b = gmul(gpowgs(mulir(a,run), degpol(B)), gpowgs(mulir(b,run), degpol(A)));
  avma = av; return 1 + (gexpo(b)>>1);
}

/* 0, 1, -1, 2, -2, ... */
#define next_lambda(a) (a>0 ? -a : 1-a)

/* If lambda = NULL, assume A in Z[Y], B in Q[Y][X], return Res_Y(A,B)
 * Otherwise, find a small lambda (start from *lambda, use the sequence above)
 * such that R(X) = Res_Y(A, B(X + lambda Y)) is squarefree, reset *lambda to
 * the chosen value and return R
 *
 * If LERS is non-NULL, set it to the last non-constant polynomial in the PRS */
GEN
ZY_ZXY_resultant_all(GEN A, GEN B0, long *lambda, GEN *LERS)
{
  int checksqfree = lambda? 1: 0, delete = 0, first = 1, stable;
  ulong av = avma, av2, lim, bound;
  long i,n, lb, dres = degpol(A)*degpol(B0), nmax = (dres+1)>>1;
  long vX = varn(B0), vY = varn(A); /* assume vX < vY */
  GEN x,y,dglist,cB,B,q,a,b,ev,H,H0,H1,Hp,H0p,H1p,C0,C1;
  byteptr d = diffptr + 3000;
  ulong p = 27449; /* p = prime(3000) */

  dglist = Hp = H0p = H1p = C0 = C1 = NULL; /* gcc -Wall */
  if (LERS)
  {
    if (!lambda) err(talker,"ZY_ZXY_resultant_all: LERS needs lambda");
    C0 = cgetg(dres+2, t_VECSMALL);
    C1 = cgetg(dres+2, t_VECSMALL);
    dglist = cgetg(dres+1, t_VECSMALL);
  }
  x = cgetg(dres+2, t_VECSMALL);
  y = cgetg(dres+2, t_VECSMALL);
  if (vY == MAXVARN)
  {
    vY = fetch_var(); delete = 1;
    B0 = gsubst(B0, MAXVARN, polx[vY]);
    A = dummycopy(A); setvarn(A, vY);
  }
  cB = content(B0);
  if (typ(cB) == t_POL) cB = content(cB);
  if (gcmp1(cB)) cB = NULL; else B0 = gdiv(B0, cB);

  if (lambda)
    B = poleval(B0, gadd(polx[MAXVARN], gmulsg(*lambda, polx[vY])));
  else
    B = poleval(B0, polx[MAXVARN]);
  av2 = avma; lim = stack_lim(av,2);

INIT:
  if (first) first = 0;
  else
  { /* lambda != NULL */
    avma = av2; *lambda = next_lambda(*lambda);
    if (DEBUGLEVEL>4) fprintferr("Starting with lambda = %ld\n",*lambda);
    B = poleval(B0, gadd(polx[MAXVARN], gmulsg(*lambda, polx[vY])));
    av2 = avma;
  }

  if (degpol(A) <= 3)
  { /* sub-resultant faster for small degrees */
    if (LERS)
    {
      H = subresall(A,B,&q);
      if (typ(q) != t_POL || degpol(q)!=1 || !ZX_is_squarefree(H)) goto INIT;
      H0 = (GEN)q[2]; if (typ(H0) == t_POL) setvarn(H0,vX);
      H1 = (GEN)q[3]; if (typ(H1) == t_POL) setvarn(H1,vX);
    }
    else
    {
      H = subres(A,B);
      if (checksqfree && !ZX_is_squarefree(H)) goto INIT;
    }
    goto END;
  }

  H = H0 = H1 = NULL;
  lb = lgef(B); b = u_allocpol(degpol(B), 0);
  bound = ZY_ZXY_ResBound(A,B);
  if (DEBUGLEVEL>4) fprintferr("bound for resultant coeffs: 2^%ld\n",bound);

  for(;;)
  {
    p += *d++; if (!*d) err(primer1);

    a = u_Fp_FpX(A, 0, p);
    for (i=2; i<lb; i++)
      b[i] = (long)u_Fp_FpX((GEN)B[i], 0, p);
    if (LERS)
    {
      if (!b[lb-1] || degpol(a) < degpol(A)) continue; /* p | lc(A)lc(B) */
      if (checksqfree)
      { /* find degree list for generic Euclidean Remainder Sequence */
        int goal = min(degpol(a), degpol(b)); /* longest possible */
        for (n=1; n <= goal; n++) dglist[n] = 0;
        setlg(dglist, 1);
        for (n=0; n <= dres; n++)
        {
          ev = vec_u_FpX_eval(b, n, p);
          (void)u_FpX_resultant_all(a, ev, NULL, NULL, dglist, p);
          if (lg(dglist)-1 == goal) break;
        }
        /* last pol in ERS has degree > 1 ? */
        goal = lg(dglist)-1;
        if (degpol(B) == 1) { if (!goal) goto INIT; }
        else
        {
          if (goal <= 1) goto INIT;
          if (dglist[goal] != 0 || dglist[goal-1] != 1) goto INIT;
        }
        if (DEBUGLEVEL>4)
          fprintferr("Degree list for ERS (trials: %ld) = %Z\n",n+1,dglist);
      }

      for (i=0,n = 0; i <= dres; n++)
      {
        i++; ev = vec_u_FpX_eval(b, n, p);
        x[i] = n;
        y[i] = u_FpX_resultant_all(a, ev, C0+i, C1+i, dglist, p);
        if (!C1[i]) i--; /* C1(i) = 0. No way to recover C0(i) */
      }
      u_FpV_polint_all(x,y,C0,C1, p);
      Hp = (GEN)y[1];
      H0p= (GEN)C0[1];
      H1p= (GEN)C1[1];
    }
    else
    {
      ulong la = (ulong)leading_term(a);
      int drop;
     /* Evaluate at 0 (if dres even) and +/- n, so that P_n(X) = P_{-n}(-X),
      * where P_i is Lagrange polynomial: P_i(j) = 1 if i=j, 0 otherwise */
      for (i=0,n = 1; n <= nmax; n++)
      {
        ev = vec_u_FpX_eval_gen(b, n, p, &drop);
        i++; x[i] = n;   y[i] = u_FpX_resultant(a, ev, p);
        if (drop && la != 1) y[i] = mulssmod(y[i], powuumod(la, drop,p),p);
        ev = vec_u_FpX_eval_gen(b, p-n, p, &drop);
        i++; x[i] = p-n; y[i] = u_FpX_resultant(a, ev, p);
        if (drop && la != 1) y[i] = mulssmod(y[i], powuumod(la, drop,p),p);
      }
      if (i == dres)
      {
        ev = vec_u_FpX_eval_gen(b, 0, p, &drop);
        i++; x[i] = 0;   y[i] = u_FpX_resultant(a, ev, p);
        if (drop && la != 1) y[i] = mulssmod(y[i], powuumod(la, drop,p),p);
      }
      Hp = u_FpV_polint(x,y, p);
    }
    if (!H && degpol(Hp) != dres) continue;
    if (checksqfree) {
      if (!u_FpX_is_squarefree(Hp, p)) goto INIT;
      if (DEBUGLEVEL>4) fprintferr("Final lambda = %ld\n",*lambda);
      checksqfree = 0;
    }

    if (!H)
    { /* initialize */
      q = utoi(p); stable = 0;
      H = ZX_init_CRT(Hp, p,vX);
      if (LERS) {
        H0= ZX_init_CRT(H0p, p,vX);
        H1= ZX_init_CRT(H1p, p,vX);
      }
    }
    else
    {
      GEN qp = muliu(q,p);
      stable = ZX_incremental_CRT(H, Hp, q,qp, p);
      if (LERS) {
        stable &= ZX_incremental_CRT(H0,H0p, q,qp, p);
        stable &= ZX_incremental_CRT(H1,H1p, q,qp, p);
      }
      q = qp;
    }
    /* could make it probabilistic for H ? [e.g if stable twice, etc]
     * Probabilistic anyway for H0, H1 */
    if (DEBUGLEVEL>5)
      msgtimer("resultant mod %ld (bound 2^%ld, stable=%ld)", p,expi(q),stable);
    if (stable && (ulong)expi(q) >= bound) break; /* DONE */
    if (low_stack(lim, stack_lim(av,2)))
    {
      GEN *gptr[4]; gptr[0] = &H; gptr[1] = &q; gptr[2] = &H0; gptr[3] = &H1;
      if (DEBUGMEM>1) err(warnmem,"ZY_ZXY_resultant");
      gerepilemany(av2,gptr,LERS? 4: 2); b = u_allocpol(degpol(B), 0);
    }
  }
END:
  setvarn(H, vX); if (delete) delete_var();
  if (cB) H = gmul(H, gpowgs(cB, degpol(A)));
  if (LERS)
  {
    GEN *gptr[2];
    GEN z = cgetg(3, t_VEC);
    z[1] = (long)H0;
    z[2] = (long)H1; *LERS = z;
    gptr[0]=&H; gptr[1]=LERS;
    gerepilemany(av, gptr, 2);
    return H;
  }
  if (!cB) H = gcopy(H);
  return gerepileupto(av, H);
}

GEN
ZY_ZXY_resultant(GEN A, GEN B0, long *lambda)
{
  return ZY_ZXY_resultant_all(A, B0, lambda, NULL);
}

/* If lambda = NULL, return caract(Mod(B, A)), A,B in Z[X].
 * Otherwise find a small lambda such that caract (Mod(B + lambda X, A)) is
 * squarefree */
GEN
ZX_caract_sqf(GEN A, GEN B, long *lambda, long v)
{
  ulong av = avma;
  GEN B0, R, a;
  long dB;
  int delete;

  if (v < 0) v = 0;
  switch (typ(B))
  {
    case t_POL: dB = degpol(B); if (dB > 0) break;
      B = dB? (GEN)B[2]: gzero; /* fall through */
    default:
      if (lambda) { B = scalarpol(B,varn(A)); dB = 0; break;}
      return gerepileupto(av, gpowgs(gsub(polx[v], B), degpol(A)));
  }
  delete = 0;
  if (varn(A) == 0)
  {
    long v0 = fetch_var(); delete = 1;
    A = dummycopy(A); setvarn(A,v0);
    B = dummycopy(B); setvarn(B,v0);
  }
  B0 = cgetg(4, t_POL); B0[1] = evalsigne(1)|evalvarn(0)|evallgef(4);
  B0[2] = (long)gneg_i(B);
  B0[3] = un;
  R = ZY_ZXY_resultant(A, B0, lambda);
  if (delete) delete_var();
  setvarn(R, v); a = leading_term(A);
  if (!gcmp1(a)) R = gdiv(R, gpowgs(a, dB));
  return gerepileupto(av, R);
}

GEN
ZX_caract(GEN A, GEN B, long v)
{
  return (degpol(A) < 16) ? caractducos(A,B,v): ZX_caract_sqf(A,B, NULL, v);
}

static GEN
trivial_case(GEN A, GEN B)
{
  if (typ(A) == t_INT) return gpowgs(A, degpol(B));
  if (degpol(A) == 0) return trivial_case((GEN)A[2],B);
  return NULL;
}

GEN
ZX_resultant_all(GEN A, GEN B, ulong bound)
{
  ulong av = avma, av2, lim, Hp;
  int stable;
  GEN q, a, b, H;
  byteptr d = diffptr + 3000;
  ulong p = 27449; /* p = prime(3000) */

  if ((H = trivial_case(A,B)) || (H = trivial_case(B,A))) return H;
  q = H = NULL;
  av2 = avma; lim = stack_lim(av,2);
  if (!bound) bound = ZY_ZXY_ResBound(A,B);
  if (DEBUGLEVEL>4) fprintferr("bound for resultant: 2^%ld\n",bound);

  for(;;)
  {
    p += *d++; if (!*d) err(primer1);
    a = u_Fp_FpX(A, 0, p);
    b = u_Fp_FpX(B, 0, p);
    Hp= u_FpX_resultant(a, b, p);
    if (!H)
    {
      stable = 0; q = utoi(p);
      H = u_center(Hp, p, p>>1);
    }
    else /* could make it probabilistic ??? [e.g if stable twice, etc] */
    {
      GEN qp = muliu(q,p);
      stable = Z_incremental_CRT(&H, Hp, q,qp, p);
      q = qp;
    }
    if (DEBUGLEVEL>5)
      msgtimer("resultant mod %ld (bound 2^%ld, stable = %d)",p,expi(q),stable);
    if (stable && (ulong)expi(q) >= bound) break; /* DONE */
    if (low_stack(lim, stack_lim(av,2)))
    {
      GEN *gptr[2]; gptr[0] = &H; gptr[1] = &q;
      if (DEBUGMEM>1) err(warnmem,"ZX_resultant");
      gerepilemany(av2,gptr, 2);
    }
  }
  return gerepileuptoint(av, icopy(H));
}

GEN
ZX_resultant(GEN A, GEN B) { return ZX_resultant_all(A,B,0); }

/* assume x has integral coefficients */
GEN
ZX_disc_all(GEN x, ulong bound)
{
  ulong av = avma;
  GEN l, d = ZX_resultant_all(x, derivpol(x), bound);
  l = leading_term(x); if (!gcmp1(l)) d = divii(d,l);
  if (degpol(x) & 2) d = negi(d);
  return gerepileuptoint(av,d);
}
GEN ZX_disc(GEN x) { return ZX_disc_all(x,0); }

int
ZX_is_squarefree(GEN x)
{
  ulong av = avma;
  int d = (lgef(modulargcd(x,derivpol(x))) == 3);
  avma = av; return d;
}

/* A0 and B0 in Q[X] */
GEN
modulargcd(GEN A0, GEN B0)
{
  GEN a,b,Hp,D,A,B,q,qp,H,g,p1;
  long m,n;
  ulong p, av2, av = avma, avlim = stack_lim(av,1);
  byteptr d = diffptr;

  if ((typ(A0) | typ(B0)) !=t_POL) err(notpoler,"modulargcd");
  if (!signe(A0)) return gcopy(B0);
  if (!signe(B0)) return gcopy(A0);
  A = content(A0);
  B = content(B0); D = ggcd(A,B);
  A = gcmp1(A)? A0: gdiv(A0,A);
  B = gcmp1(B)? B0: gdiv(B0,B);
  /* A, B in Z[X] */
  g = mppgcd(leading_term(A), leading_term(B)); /* multiple of lead(gcd) */
  if (degpol(A) < degpol(B)) swap(A, B);
  n = 1 + degpol(B); /* > degree(gcd) */

  av2 = avma; H = NULL;
  d += 3000; /* 27449 = prime(3000) */
  for(p = 27449; ; p+= *d++)
  {
    if (!*d) err(primer1);
    if (!umodiu(g,p)) continue;

    a = u_Fp_FpX(A, 0, p);
    b = u_Fp_FpX(B, 0, p); Hp = u_FpX_gcd_i(a,b, p);
    m = degpol(Hp);
    if (m == 0) { H = polun[varn(A0)]; break; } /* coprime. DONE */
    if (m > n) continue; /* p | Res(A/G, B/G). Discard */

    if (is_pm1(g)) /* make sure lead(H) = g mod p */
      Hp = u_FpX_normalize(Hp, p);
    else
    {
      ulong t = mulssmod(umodiu(g, p), u_invmod(Hp[m+2],p), p);
      Hp = u_FpX_Fp_mul(Hp, t, p, 0);
    }
    if (m < n)
    { /* First time or degree drop [all previous p were as above; restart]. */
      H = ZX_init_CRT(Hp,p,varn(A0));
      q = utoi(p); n = m; continue;
    }

    qp = muliu(q,p);
    if (ZX_incremental_CRT(H, Hp, q, qp, p))
    { /* H stable: check divisibility */
      if (!is_pm1(g)) { p1 = content(H); if (!is_pm1(p1)) H = gdiv(H,p1); }
      if (!signe(gres(A,H)) && !signe(gres(B,H))) break; /* DONE */

      if (DEBUGLEVEL) fprintferr("modulargcd: trial division failed");
    }
    q = qp;
    if (low_stack(avlim, stack_lim(av,1)))
    {
      GEN *gptr[2]; gptr[0]=&H; gptr[1]=&q;
      if (DEBUGMEM>1) err(warnmem,"modulargcd");
      gerepilemany(av2,gptr,2);
    }
  }
  return gerepileupto(av, gmul(D,H));
}

/* lift(1 / Mod(A,B)). B0 a t_POL, A0 a scalar or a t_POL. Rational coeffs */
GEN
QX_invmod(GEN A0, GEN B0)
{
  GEN a,b,D,A,B,q,qp,Up,Vp,U,V,res;
  long stable;
  ulong p, av2, av = avma, avlim = stack_lim(av,1);
  byteptr d = diffptr;

  if (typ(B0) != t_POL) err(notpoler,"QX_invmod");
  if (typ(A0) != t_POL)
  {
    if (is_scalar_t(typ(A0))) return ginv(A0);
    err(notpoler,"QX_invmod");
  }
  if (degpol(A0) < 15) return ginvmod(A0,B0);
  A = primitive_part(A0, &D);
  B = primitive_part(B0, NULL);
  /* A, B in Z[X] */
  av2 = avma; U = NULL;
  d += 3000; /* 27449 = prime(3000) */
  for(p = 27449; ; p+= *d++)
  {
    if (!*d) err(primer1);
    a = u_Fp_FpX(A, 0, p);
    b = u_Fp_FpX(B, 0, p);
    /* if p | Res(A/G, B/G), discard */
    if (!u_FpX_extresultant(b,a,p, &Vp,&Up)) continue;

    if (!U)
    { /* First time */
      U = ZX_init_CRT(Up,p,varn(A0));
      V = ZX_init_CRT(Vp,p,varn(A0));
      q = utoi(p); continue;
    }
    if (DEBUGLEVEL>5) msgtimer("QX_invmod: mod %ld (bound 2^%ld)", p,expi(q));
    qp = muliu(q,p);
    stable  = ZX_incremental_CRT(U, Up, q,qp, p);
    stable &= ZX_incremental_CRT(V, Vp, q,qp, p);
    if (stable)
    { /* all stable: check divisibility */
      res = gadd(gmul(A,U), gmul(B,V));
      if (degpol(res) == 0) break; /* DONE */
      if (DEBUGLEVEL) fprintferr("QX_invmod: char 0 check failed");
    }
    q = qp;
    if (low_stack(avlim, stack_lim(av,1)))
    {
      GEN *gptr[3]; gptr[0]=&q; gptr[1]=&U; gptr[2]=&V;
      if (DEBUGMEM>1) err(warnmem,"QX_invmod");
      gerepilemany(av2,gptr,3);
    }
  }
  D = D? gmul(D,res): res;
  return gerepileupto(av, gdiv(U,D));
}

