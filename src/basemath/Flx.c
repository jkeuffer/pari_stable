/* $Id$

Copyright (C) 2004  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

#include "pari.h"

/* Not so fast arithmetic with polynomials with small coefficients. */

/***********************************************************************/
/**                                                                   **/
/**               Flx                                                 **/
/**                                                                   **/
/***********************************************************************/
/* Flx objects are defined as follows:
   Let l an ulong. An Flx is a t_VECSMALL:
   x[0] = codeword
   x[1] = evalvarn(variable number)  (signe is not stored).
   x[2] = a_0 x[3] = a_1, etc.
   With 0 <= a_i < l
   
   signe(x) is not valid. Use degpol(x)>=0 instead.
*/

#define lswap(x,y) {long _z=x; x=y; y=_z;}
#define pswap(x,y) {GEN *_z=x; x=y; y=_z;}
#define swap(x,y)  {GEN  _z=x; x=y; y=_z;}
#define swapspec(x,y, nx,ny) {swap(x,y); lswap(nx,ny);}

long Flx_SQR_LIMIT = 6;
long Flx_MUL_LIMIT = 10;

#define both_odd(x,y) ((x)&(y)&1)

/***********************************************************************/
/**                                                                   **/
/**          Conversion from Flx                                      **/
/**                                                                   **/
/***********************************************************************/

/* Flx_ZX=zx_ZX*/
GEN
Flx_ZX(GEN z)
{
  long i;
  long l=lg(z);
  GEN x = cgetg(l,t_POL);
  if (typ(z) != t_VECSMALL) err(bugparier,"Flx_ZX, not a VECSMALL");
  for (i=2; i<l; i++) x[i] = lutoi((ulong)z[i]);
  x[1] = evalsigne(l-2!=0)| z[1]; return x;
}

/* Flx_ZX_inplace=zx_ZX_inplace*/
/* same. In place */
GEN
Flx_ZX_inplace(GEN z)
{
  long i, l = lg(z);
  for (i=2; i<l; i++) z[i] = lutoi((ulong)z[i]);
  settyp(z, t_POL); z[1]=evalsigne(l-2!=0)|z[1]; return z;
}

/*FIXME: should be zx_zv_lg*/
GEN
Flx_Flv_lg(GEN x, long N)
{
  long i, l;
  GEN z = cgetg(N+1,t_VECSMALL);
  if (typ(x) != t_VECSMALL) err(typeer,"Flx_Flv_lg");
  l = lg(x)-1; x++;
  for (i=1; i<l ; i++) z[i]=x[i];
  for (   ; i<=N; i++) z[i]=0;
  return z;
}

/*FIXME: should be zv_zx*/
GEN
Flv_Flx(GEN x, long vs)
{
  long i, l=lg(x)+1;
  GEN z = cgetg(l,t_VECSMALL); z[1]=vs;
  x--; 
  for (i=2; i<l ; i++) z[i]=x[i];
  return z;
}

/*FIXME: should be zm_zxV*/
GEN
Flm_FlxV(GEN x, long sv)
{
  long j, lx = lg(x);
  GEN y = cgetg(lx, t_VEC);
  for (j=1; j<lx; j++) y[j] = (long)Flv_Flx((GEN)x[j], sv);
  return y;
}

/***********************************************************************/
/**                                                                   **/
/**          Conversion to Flx                                        **/
/**                                                                   **/
/***********************************************************************/

/*sv is a evalvarn()*/
/*FIXME: should be zero_Flx or something*/
/*Flx_zero=zx_zero*/
GEN
Flx_zero(long sv)
{
  GEN x = cgetg(2, t_VECSMALL);
  x[1] = sv; return x;
}

/* FIXME: should be polx_zx or something
 * since it does not take a Flx as input.
 *
 * Flx_polx=zx_polx*/

GEN
Flx_polx(long sv)
{
  GEN z = cgetg(4, t_VECSMALL);
  z[1] = sv;
  z[2] = 0;
  z[3] = 1;
  return z;
}


/*FIXME: Should be z_zx_zero since modular reduction is not performed*/
GEN
Fl_Flx(ulong x, long sv)
{
  GEN z;
  if (!x) return Flx_zero(sv);
  z = cgetg(3, t_VECSMALL);
  z[1] = sv;
  z[2] = (long)x; return z;
}

/* Take an integer and return a scalar polynomial mod p,
 * with evalvarn=vs */

GEN
Z_Flx(GEN x, ulong p, long vs)
{
  GEN a = cgetg(3, t_VECSMALL);
  a[1] = vs;
  a[2] = (long)umodiu(x, p); 
  return a;
}

/* return x[0 .. dx] mod p as t_VECSMALL. Assume x a t_POL*/
GEN
ZX_Flx(GEN x, ulong p)
{
  long i;
  long lx = lg(x); 
  GEN a = cgetg(lx, t_VECSMALL);
  a[1]=((ulong)x[1])&VARNBITS;
  for (i=2; i<lx; i++) a[i] = (long)umodiu((GEN)x[i], p);
  return Flx_renormalize(a,lx);
}

GEN
ZV_Flv(GEN x, ulong p)
{
  long i, n = lg(x);
  GEN y = cgetg(n,t_VECSMALL);
  for (i=1; i<n; i++) y[i] = (long)umodiu((GEN)x[i], p);
  return y;
}

GEN
ZM_Flm(GEN x, ulong p)
{
  long j,n = lg(x);
  GEN y = cgetg(n,t_MAT);
  if (n == 1) return y;
  for (j=1; j<n; j++) y[j] = (long)ZV_Flv((GEN)x[j], p);
  return y;
}

/***********************************************************************/
/**                                                                   **/
/**          Basic operation on Flx                                   **/
/**                                                                   **/
/***********************************************************************/


/*Similar to normalizepol, in place*/
/*FIXME: should be zx_renormalize*/
GEN
Flx_renormalize(GEN /*in place*/ x, long lx)
{
  long i;
  for (i = lx-1; i>1; i--)
    if (x[i]) break;
  stackdummy(x + (i+1), lg(x) - (i+1));
  setlg(x, i+1);
  return x;
}

GEN
Flx_red(GEN z, ulong p)
{
  long i,l;
  GEN x;
  l = lg(z); x = cgetg(l, t_VECSMALL);
  for (i=2; i<l; i++)
    x[i] = z[i]%p;
  x[1] = z[1]; return Flx_renormalize(x,l);
}

GEN
Flx_addspec(GEN x, GEN y, ulong p, long lx, long ly)
{
  long i,lz;
  GEN z;

  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx+2; z = cgetg(lz, t_VECSMALL) + 2;
  for (i=0; i<ly; i++) z[i] = (long)adduumod((ulong)x[i], (ulong)y[i], p);
  for (   ; i<lx; i++) z[i] = x[i];
  z -= 2; return Flx_renormalize(z, lz);
}

GEN
Flx_add(GEN x, GEN y, ulong p)
{
  long i,lz;
  GEN z; 
  long lx=lg(x);
  long ly=lg(y);
  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx; z = cgetg(lz, t_VECSMALL); z[1]=x[1];
  for (i=2; i<ly; i++) z[i] = (long)adduumod((ulong)x[i], (ulong)y[i], p);
  for (   ; i<lx; i++) z[i] = x[i];
  return Flx_renormalize(z, lz);
}

GEN
Flx_sub(GEN x, GEN y, ulong p)
{
  long i,lz,lx = lg(x), ly = lg(y);
  GEN z;

  if (ly <= lx)
  {
    lz = lx; z = cgetg(lz, t_VECSMALL);
    for (i=2; i<ly; i++) z[i] = (long)subuumod((ulong)x[i],(ulong)y[i],p);
    for (   ; i<lx; i++) z[i] = x[i];
  }
  else
  {
    lz = ly; z = cgetg(lz, t_VECSMALL);
    for (i=2; i<lx; i++) z[i] = (long)subuumod((ulong)x[i],(ulong)y[i],p);
    for (   ; i<ly; i++) z[i] = y[i]? (long)(p - y[i]): y[i];
  }
  z[1]=x[1]; return Flx_renormalize(z, lz);
}

GEN
Flx_neg(GEN x, ulong p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_VECSMALL);
  z[1] = x[1];
  for (i=2; i<l; i++) z[i] = x[i]? (long)p - x[i]: 0;
  return z;
}

GEN
Flx_neg_inplace(GEN x, ulong p)
{
  long i, l = lg(x);
  for (i=2; i<l; i++)
    if (x[i]) x[i] = (long)p - x[i];
  return x;
}

GEN
Flx_Fl_mul(GEN y, ulong x, ulong p)
{
  GEN z;
  int i, l;
  if (!x) return Flx_zero(y[1]);
  l = lg(y); z = cgetg(l, t_VECSMALL); z[1]=y[1]; 
  if (HIGHWORD(x | p))
    for(i=2; i<l; i++) z[i] = (long)muluumod(y[i], x, p);
  else
    for(i=2; i<l; i++) z[i] = (y[i] * x) % p;
  return z;
}

GEN
Flx_normalize(GEN z, ulong p)
{
  long l = lg(z)-1;
  ulong p1 = z[l]; /* leading term */
  if (p1 == 1) return z;
  return Flx_Fl_mul(z, invumod(p1,p), p);
}

/* return (x * X^d) + y. Assume d > 0, x > 0 and y >= 0 */
GEN
Flx_addshift(GEN x, GEN y, ulong p, long d)
{
  GEN xd,yd,zd = (GEN)avma;
  long a,lz,ny = lgpol(y), nx = lgpol(x);
  long vs = x[1];

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
    x = Flx_addspec(x,yd,p, nx,a);
    lz = (a>nx)? ny+2: lg(x)+d;
    x += 2; while (xd > x) *--zd = *--xd;
  }
  while (yd > y) *--zd = *--yd;
  *--zd = vs;
  *--zd = evaltyp(t_VECSMALL) | evallg(lz); return zd;
}

/* shift polynomial + gerepile */
/* Do not set evalvarn*/
static GEN
Flx_shiftip(pari_sp av, GEN x, long v)
{
  long i, lx = lg(x), ly;
  GEN y;
  if (v <= 0 || lx==2) return gerepileupto(av, x);
  avma = av; ly = lx + v;
  x += lx; y = new_chunk(ly) + ly; /*cgetg could overwrite x!*/
  for (i = 2; i<lx; i++) *--y = *--x;
  for (i = 0; i< v; i++) *--y = 0;
  y -= 2; y[0] = evaltyp(t_VECSMALL) | evallg(ly);
  return y;
}

INLINE ulong
Flx_mullimb_ok(GEN x, GEN y, ulong p, long a, long b)
{ /* Assume OK_ULONG*/
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

INLINE ulong
Flx_mullimb(GEN x, GEN y, ulong p, long a, long b)
{
  ulong p1 = 0;
  long i;
  for (i=a; i<b; i++)
    if (y[i])
      p1 = adduumod(p1, muluumod(y[i],x[-i],p), p);
  return p1;
}

/* assume nx >= ny > 0 */
GEN
Flx_mulspec_basecase(GEN x, GEN y, ulong p, long nx, long ny)
{
  long i,lz,nz;
  GEN z;

  lz = nx+ny+1; nz = lz-2;
  z = cgetg(lz, t_VECSMALL) + 2; /* x:y:z [i] = term of degree i */
  if (u_OK_ULONG(p))
  {
    for (i=0; i<ny; i++)z[i] = (long)Flx_mullimb_ok(x+i,y,p,0,i+1);
    for (  ; i<nx; i++) z[i] = (long)Flx_mullimb_ok(x+i,y,p,0,ny);
    for (  ; i<nz; i++) z[i] = (long)Flx_mullimb_ok(x+i,y,p,i-nx+1,ny);
  }
  else
  {
    for (i=0; i<ny; i++)z[i] = (long)Flx_mullimb(x+i,y,p,0,i+1);
    for (  ; i<nx; i++) z[i] = (long)Flx_mullimb(x+i,y,p,0,ny);
    for (  ; i<nz; i++) z[i] = (long)Flx_mullimb(x+i,y,p,i-nx+1,ny);
  }
  z -= 2; return Flx_renormalize(z, lz);
}

/* fast product (Karatsuba) of polynomials a,b. These are not real GENs, a+2,
 * b+2 were sent instead. na, nb = number of terms of a, b.
 * Only c, c0, c1, c2 are genuine GEN.
 */
GEN
Flx_mulspec(GEN a, GEN b, ulong p, long na, long nb)
{
  GEN a0,c,c0;
  long n0, n0a, i, v = 0;
  pari_sp av;

  while (na && !a[0]) { a++; na--; v++; }
  while (nb && !b[0]) { b++; nb--; v++; }
  if (na < nb) swapspec(a,b, na,nb);
  if (!nb) return Flx_zero(0);

  av = avma;
  if (nb < Flx_MUL_LIMIT)
    return Flx_shiftip(av,Flx_mulspec_basecase(a,b,p,na,nb), v);
  i=(na>>1); n0=na-i; na=i;
  a0=a+n0; n0a=n0;
  while (n0a && !a[n0a-1]) n0a--;

  if (nb > n0)
  {
    GEN b0,c1,c2;
    long n0b;

    nb -= n0; b0 = b+n0; n0b = n0;
    while (n0b && !b[n0b-1]) n0b--;
    c =  Flx_mulspec(a,b,p,n0a,n0b);
    c0 = Flx_mulspec(a0,b0,p,na,nb);

    c2 = Flx_addspec(a0,a,p,na,n0a);
    c1 = Flx_addspec(b0,b,p,nb,n0b);

    c1 = Flx_mul(c1,c2,p);
    c2 = Flx_add(c0,c,p);

    c2 = Flx_neg_inplace(c2,p);
    c2 = Flx_add(c1,c2,p);
    c0 = Flx_addshift(c0,c2 ,p, n0);
  }
  else
  {
    c  = Flx_mulspec(a,b,p,n0a,nb);
    c0 = Flx_mulspec(a0,b,p,na,nb);
  }
  c0 = Flx_addshift(c0,c,p,n0);
  return Flx_shiftip(av,c0, v);
}

GEN
Flx_mul(GEN x, GEN y, ulong p)
{
 GEN z = Flx_mulspec(x+2,y+2,p, lgpol(x),lgpol(y));
 z[1] = x[1]; return z;
}

GEN
Flx_sqrspec_basecase(GEN x, ulong p, long nx)
{
  long i, lz, nz;
  ulong p1;
  GEN z;

  if (!nx) return Flx_zero(0);
  lz = (nx << 1) + 1, nz = lz-2;
  z = cgetg(lz, t_VECSMALL) + 2;
  if (u_OK_ULONG(p))
  {
    for (i=0; i<nx; i++)
    {
      p1 = Flx_mullimb_ok(x+i,x,p,0, (i+1)>>1);
      p1 <<= 1; if (p1 & HIGHBIT) p1 %= p;
      if ((i&1) == 0) p1 += x[i>>1] * x[i>>1];
      z[i] = (long) (p1 % p);
    }
    for (  ; i<nz; i++)
    {
      p1 = Flx_mullimb_ok(x+i,x,p,i-nx+1, (i+1)>>1);
      p1 <<= 1; if (p1 & HIGHBIT) p1 %= p;
      if ((i&1) == 0) p1 += x[i>>1] * x[i>>1];
      z[i] = (long) (p1 % p);
    }
  }
  else
  {
    for (i=0; i<nx; i++)
    {
      p1 = Flx_mullimb(x+i,x,p,0, (i+1)>>1);
      p1 = adduumod(p1, p1, p);
      if ((i&1) == 0) p1 = adduumod(p1, muluumod(x[i>>1], x[i>>1], p), p);
      z[i] = (long)p1;
    }
    for (  ; i<nz; i++)
    {
      p1 = Flx_mullimb(x+i,x,p,i-nx+1, (i+1)>>1);
      p1 = adduumod(p1, p1, p);
      if ((i&1) == 0) p1 = adduumod(p1, muluumod(x[i>>1], x[i>>1], p), p);
      z[i] = (long)p1;
    }
  }
  z -= 2; return Flx_renormalize(z,lz);
}

GEN
Flx_2_mul(GEN x, ulong p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_VECSMALL);
  for (i=2; i<l; i++) z[i] = (long)adduumod(x[i], x[i], p);
  z[1] = x[1]; return z;
}

GEN
Flx_sqrspec(GEN a, ulong p, long na)
{
  GEN a0,c,c0,c1;
  long n0, n0a, i, v = 0;
  pari_sp av;

  while (na && !a[0]) { a++; na--; v += 2; }
  av = avma;
  if (na < Flx_SQR_LIMIT) 
    return Flx_shiftip(av, Flx_sqrspec_basecase(a,p,na), v);
  i=(na>>1); n0=na-i; na=i;
  a0=a+n0; n0a=n0;
  while (n0a && !a[n0a-1]) n0a--;

  c = Flx_sqrspec(a,p,n0a);
  c0= Flx_sqrspec(a0,p,na);
  if (p == 2) n0 *= 2;
  else
  {
    c1 = Flx_2_mul(Flx_mulspec(a0,a,p, na,n0a), p);
    c0 = Flx_addshift(c0,c1,p,n0);
  }
  c0 = Flx_addshift(c0,c,p,n0);
  return Flx_shiftip(av,c0,v);
}

GEN
Flx_sqr(GEN x, ulong p)
{
  GEN z = Flx_sqrspec(x+2,p, lgpol(x));
  z[1] = x[1]; return z;
}

GEN
Flx_pow(GEN x, long n, ulong p)
{
  GEN y = Fl_Flx(1,x[1]), z;
  long m;
  if (n == 0) return y;
  m = n; z = x;
  for (;;)
  {
    if (m&1) y = Flx_mul(y,z, p);
    m >>= 1; if (!m) return y;
    z = Flx_sqr(z, p);
  }
}

/* separate from Flx_divrem for maximal speed. */
GEN
Flx_rem(GEN x, GEN y, ulong p)
{ 
  pari_sp av;
  GEN z, c;
  long dx,dy,dz,i,j;
  ulong p1,inv;
  long vs=x[1];

  dy = degpol(y); if (!dy) return Flx_zero(x[1]);
  dx = degpol(x);
  dz = dx-dy; if (dz < 0) return Flx_copy(x);
  x += 2; y += 2;
  inv = y[dy];
  if (inv != 1UL) inv = invumod(inv,p);

  c = cgetg(dy+3, t_VECSMALL); c[1]=vs; c += 2; av=avma;
  z = cgetg(dz+3, t_VECSMALL); z[1]=vs; z += 2;

  if (u_OK_ULONG(p))
  {
    z[dz] = (inv*x[dx]) % p;
    for (i=dx-1; i>=dy; --i)
    {
      p1 = p - x[i]; /* compute -p1 instead of p1 (pb with ulongs otherwise) */
      for (j=i-dy+1; j<=i && j<=dz; j++)
      {
        p1 += z[j]*y[i-j];
        if (p1 & HIGHBIT) p1 %= p;
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
        if (p1 & HIGHBIT) p1 %= p;
      }
      c[i] = (long)subuumod((ulong)x[i], p1%p, p);
    }
  }
  else
  {
    z[dz] = muluumod(inv, x[dx], p);
    for (i=dx-1; i>=dy; --i)
    {
      p1 = p - x[i]; /* compute -p1 instead of p1 (pb with ulongs otherwise) */
      for (j=i-dy+1; j<=i && j<=dz; j++)
        p1 = adduumod(p1, muluumod(z[j],y[i-j],p), p);
      z[i-dy] = p1? muluumod(p - p1, inv, p): 0;
    }
    for (i=0; i<dy; i++)
    {
      p1 = muluumod(z[0],y[i],p);
      for (j=1; j<=i && j<=dz; j++)
        p1 = adduumod(p1, muluumod(z[j],y[i-j],p), p);
      c[i] = (long)subuumod((ulong)x[i], p1, p);
    }
  }
  i = dy-1; while (i>=0 && !c[i]) i--;
  avma=av;
  return Flx_renormalize(c-2, i+3);
}

/* as FpX_divrem but working only on ulong types. ASSUME pr != ONLY_DIVIDES
 * if relevant, *pr is the last object on stack */
GEN
Flx_divrem(GEN x, GEN y, ulong p, GEN *pr)
{
  GEN z,q,c;
  long dx,dy,dz,i,j;
  ulong p1,inv;
  long sv=x[1];

  if (pr == ONLY_REM) return Flx_rem(x, y, p);
  dy = degpol(y);
  if (!dy)
  {
    if (y[2] == 1UL)
      q = Flx_copy(x);
    else
      q = Flx_Fl_mul(x, invumod(y[2], p), p);
    if (pr) *pr = Flx_zero(sv);
    return q;
  }
  dx = degpol(x);
  dz = dx-dy;
  if (dz < 0)
  {
    q = Flx_zero(sv);
    if (pr) *pr = Flx_copy(x);
    return q;
  }
  x += 2;
  y += 2;
  z = cgetg(dz + 3, t_VECSMALL); z[1] = sv; z += 2;
  inv = (ulong)y[dy];
  if (inv != 1UL) inv = invumod(inv,p);

  if (u_OK_ULONG(p))
  {
    z[dz] = (long) (inv*x[dx]) % p;
    for (i=dx-1; i>=dy; --i)
    {
      p1 = p - x[i]; /* compute -p1 instead of p1 (pb with ulongs otherwise) */
      for (j=i-dy+1; j<=i && j<=dz; j++)
      {
        p1 += z[j]*y[i-j];
        if (p1 & HIGHBIT) p1 %= p;
      }
      p1 %= p;
      z[i-dy] = p1? (long) ((p - p1)*inv) % p: 0;
    }
  }
  else
  {
    z[dz] = (long)muluumod(inv, x[dx], p);
    for (i=dx-1; i>=dy; --i)
    { /* compute -p1 instead of p1 (pb with ulongs otherwise) */
      p1 = p - (ulong)x[i];
      for (j=i-dy+1; j<=i && j<=dz; j++)
        p1 = adduumod(p1, muluumod(z[j],y[i-j],p), p);
      z[i-dy] = p1? (long)muluumod(p - p1, inv, p): 0;
    }
  }
  q = Flx_renormalize(z-2, dz+3);
  if (!pr) return q;

  c = cgetg(dy + 3, t_VECSMALL); c[1] = sv; c += 2;
  if (u_OK_ULONG(p))
  {
    for (i=0; i<dy; i++)
    {
      p1 = (ulong)z[0]*y[i];
      for (j=1; j<=i && j<=dz; j++)
      {
        p1 += (ulong)z[j]*y[i-j];
        if (p1 & HIGHBIT) p1 %= p;
      }
      c[i] = (long)subuumod((ulong)x[i], p1%p, p);
    }
  }
  else
  {
    for (i=0; i<dy; i++)
    {
      p1 = muluumod(z[0],y[i],p);
      for (j=1; j<=i && j<=dz; j++)
        p1 = adduumod(p1, muluumod(z[j],y[i-j],p), p);
      c[i] = (long)subuumod((ulong)x[i], p1, p);
    }
  }
  i=dy-1; while (i>=0 && !c[i]) i--;
  c = Flx_renormalize(c-2, i+3);
  *pr = c; return q;
}

GEN
Flx_deriv(GEN z, ulong p)
{
  long i,l = lg(z)-1;
  GEN x;
  if (l < 2) l = 2;
  x = cgetg(l, t_VECSMALL); x[1] = z[1]; z++;
  if (HIGHWORD(l | p))
    for (i=2; i<l; i++) x[i] = (long)muluumod((ulong)i-1, (ulong)z[i], p);
  else
    for (i=2; i<l; i++) x[i] = ((i-1) * z[i]) % p;
  return Flx_renormalize(x,l);
}

/*Do not garbage collect*/

GEN
Flx_gcd_i(GEN a, GEN b, ulong p)
{
  GEN c;
  if (lg(b) > lg(a)) swap(a, b);
  while (lgpol(b))
  {
    c = Flx_rem(a,b,p);
    a = b; b = c;
  }
  return a;
}

GEN
Flx_gcd(GEN a, GEN b, ulong p)
{
  pari_sp av = avma;
  return gerepileupto(av, Flx_gcd_i(a,b,p));
}

int
Flx_is_squarefree(GEN z, ulong p)
{
  pari_sp av = avma;
  GEN d = Flx_gcd_i(z, Flx_deriv(z,p) , p);
  long res= (degpol(d) == 0);
  avma = av;
  return res;
}

GEN
Flx_extgcd(GEN a, GEN b, ulong p, GEN *ptu, GEN *ptv)
{
  GEN q,z,u,v, x = a, y = b;

  u = Flx_zero(a[1]);
  v = Fl_Flx(1,a[1]); /* v = 1 */
  while (lgpol(y))
  {
    q = Flx_divrem(x,y,p,&z);
    x = y; y = z; /* (x,y) = (y, x - q y) */
    z = Flx_sub(u, Flx_mul(q,v, p), p);
    u = v; v = z; /* (u,v) = (v, u - q v) */
  }
  z = Flx_sub(x, Flx_mul(b,u,p), p);
  z = Flx_div(z,a,p);
  *ptu = z;
  *ptv = u; return x;
}

ulong
Flx_resultant(GEN a, GEN b, ulong p)
{
  long da,db,dc,cnt;
  ulong lb, res = 1UL;
  pari_sp av;
  GEN c;

  if (lgpol(a)==0 || lgpol(b)==0) return 0;
  da = degpol(a);
  db = degpol(b);
  if (db > da)
  {
    swapspec(a,b, da,db);
    if (both_odd(da,db)) res = p-res;
  }
  if (!da) return 1; /* = res * a[2] ^ db, since 0 <= db <= da = 0 */
  cnt = 0; av = avma;
  while (db)
  {
    lb = b[db+2];
    c = Flx_rem(a,b, p);
    a = b; b = c; dc = degpol(c);
    if (dc < 0) { avma = av; return 0; }

    if (both_odd(da,db)) res = p - res;
    if (lb != 1) res = muluumod(res, powuumod(lb, da - dc, p), p);
    if (++cnt == 4) { cnt = 0; avma = av; }
    da = db; /* = degpol(a) */
    db = dc; /* = degpol(b) */
  }
  avma = av; return muluumod(res, powuumod(b[2], da, p), p);
}

/* If resultant is 0, *ptU and *ptU are not set */
ulong
Flx_extresultant(GEN a, GEN b, ulong p, GEN *ptU, GEN *ptV)
{
  GEN z,q,u,v, x = a, y = b;
  ulong lb, res = 1UL;
  pari_sp av = avma;
  long dx, dy, dz;
  long vs=a[1];

  dx = degpol(x);
  dy = degpol(y);
  if (dy > dx)
  {
    swap(x,y); lswap(dx,dy); pswap(ptU, ptV);
    a = x; b = y;
    if (both_odd(dx,dy)) res = p-res;
  }
  /* dx <= dy */
  if (dx < 0) return 0;

  u = Flx_zero(vs);
  v = Fl_Flx(1,vs); /* v = 1 */
  while (dy)
  { /* b u = x (a), b v = y (a) */
    lb = y[dy+2];
    q = Flx_divrem(x,y, p, &z);
    x = y; y = z; /* (x,y) = (y, x - q y) */
    dz = degpol(z); if (dz < 0) { avma = av; return 0; }
    z = Flx_sub(u, Flx_mul(q,v, p), p);
    u = v; v = z; /* (u,v) = (v, u - q v) */

    if (both_odd(dx,dy)) res = p - res;
    if (lb != 1) res = muluumod(res, powuumod(lb, dx-dz, p), p);
    dx = dy; /* = degpol(x) */
    dy = dz; /* = degpol(y) */
  }
  res = muluumod(res, powuumod(y[2], dx, p), p);
  lb = muluumod(res, invumod(y[2],p), p);
  v = gerepileupto(av, Flx_Fl_mul(v, lb, p));
  av = avma;
  u = Flx_sub(Fl_Flx(res,vs), Flx_mul(b,v,p), p);
  u = gerepileupto(av, Flx_div(u,a,p)); /* = (res - b v) / a */
  *ptU = u;
  *ptV = v; return res;
}

ulong
Flx_eval(GEN x, ulong y, ulong p)
{
  ulong p1,r;
  long j, i=lg(x)-1;
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
          return muluumod(p1, y, p);
        }
      r = (i==j)? y: powuumod(y, i-j+1, p);
      p1 = adduumod((ulong)x[j], muluumod(p1,r,p), p);
    }
  }
  return p1;
}

static ulong global_pp;
static GEN
_Flx_mul(GEN a, GEN b)
{
  return Flx_mul(a,b, global_pp);
}

/* compute prod (x - a[i]) */
GEN
Flv_roots_to_pol(GEN a, ulong p, long vs)
{
  long i,k,lx = lg(a);
  GEN p1,p2;
  if (lx == 1) return polun[0];
  p1 = cgetg(lx, t_VEC); global_pp = p;
  for (k=1,i=1; i<lx-1; i+=2)
  {
    p2 = cgetg(5,t_VECSMALL); p1[k++] = (long)p2;
    p2[1] = vs;
    p2[2] = muluumod(a[i], a[i+1], p);
    p2[3] = a[i] + a[i+1];
    if ((ulong)p2[3] >= p) p2[3] -= p;
    if (p2[3]) p2[3] = p - p2[3]; /* - (a[i] + a[i+1]) mod p */
    p2[4] = 1; p2[1] = 0;
  }
  if (i < lx)
  {
    p2 = cgetg(4,t_POL); p1[k++] = (long)p2;
    p2[1] = 0;
    p2[2] = p - a[i];
    p2[3] = 1;
  }
  setlg(p1, k); return divide_conquer_prod(p1, _Flx_mul);
}

GEN
Flx_div_by_X_x(GEN a, ulong x, ulong p)
{
  long l = lg(a), i;
  GEN a0, z0;
  GEN z = cgetg(l-1,t_POL);
  z[1]=a[1];
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
      ulong t = adduumod((ulong)*a0--, muluumod(x, *z0--, p), p);
      *z0 = (long)t;
    }
  }
  return z;
}

/* u P(X) + v P(-X) */
GEN
Flx_even_odd_comb(GEN P, ulong u, ulong v, ulong p)
{
  long i, l = lg(P);
  GEN y = cgetg(l,t_VECSMALL);
  y[1]=P[1];
  for (i=2; i<l; i++)
  {
    ulong t = P[i];
    y[i] = (t == 0)? 0:
                     (i&1)? muluumod(t, u + (p - v), p)
                          : muluumod(t, u + v, p);
  }
  return Flx_renormalize(y,l);
}

/* xa, ya = t_VECSMALL */
GEN
Flv_polint(GEN xa, GEN ya, ulong p, long vs)
{
  GEN T,dP, P = NULL, Q = Flv_roots_to_pol(xa, p, vs);
  long i, n = lg(xa);
  ulong inv;
  pari_sp av = avma;
  for (i=1; i<n; i++)
  {
    if (!ya[i]) continue;
    T = Flx_div_by_X_x(Q, xa[i], p);
    inv = invumod(Flx_eval(T,xa[i], p), p);
    if (i < n-1 && (ulong)(xa[i] + xa[i+1]) == p)
    {
      dP = Flx_even_odd_comb(T, muluumod(ya[i],inv,p), muluumod(ya[i+1],inv,p), p);
      i++; /* x_i = -x_{i+1} */
    }
    else
      dP = Flx_Fl_mul(T, muluumod(ya[i],inv,p), p);
    P = P? Flx_add(P, dP, p): dP;
  }
  return P? gerepileupto(av, P): Flx_zero(vs);
}

/***********************************************************************/
/**                                                                   **/
/**               Flxq                                                **/
/**                                                                   **/
/***********************************************************************/
/* Flxq objects are defined as follows:
   They are Flx modulo another Flx called q.
*/

/* Product of y and x in Z/pZ[X]/(pol), as t_VECSMALL. */
GEN
Flxq_mul(GEN y,GEN x,GEN pol,ulong p)
{
  GEN z = Flx_mul(y,x,p);
  return Flx_rem(z,pol,p);
}

/* Square of y in Z/pZ[X]/(pol), as t_VECSMALL. */
GEN
Flxq_sqr(GEN y,GEN pol,ulong p)
{
  GEN z = Flx_sqr(y,p);
  return Flx_rem(z,pol,p);
}

typedef struct {
  GEN pol;
  ulong p;
} Flxq_muldata;


static GEN
_u_sqr(void *data, GEN x)
{
  Flxq_muldata *D = (Flxq_muldata*)data;
  return Flxq_sqr(x, D->pol, D->p);
}
static GEN
_u_mul(void *data, GEN x, GEN y)
{
  Flxq_muldata *D = (Flxq_muldata*)data;
  return Flxq_mul(x,y, D->pol, D->p);
}

/* n-Power of x in Z/pZ[X]/(pol), as t_VECSMALL. */
/* FIXME: assume n > 0 */
GEN
Flxq_pow(GEN x, GEN n, GEN pol, ulong p)
{
  pari_sp av = avma;
  Flxq_muldata D;
  GEN y;
  D.pol = pol;
  D.p   = p;
  y = leftright_pow(x, n, (void*)&D, &_u_sqr, &_u_mul);
  return gerepileupto(av, y);
}

/* Inverse of x in Z/pZ[X]/(pol) or NULL if inverse doesn't exist
 * return lift(1 / (x mod (p,pol)))
 * not stack clean.
 * */
GEN
Flxq_invsafe(GEN x, GEN T, ulong p)
{
  GEN U, V;
  GEN z = Flx_extgcd(x, T, p, &U, &V);
  ulong iz;
  if (degpol(z)) return NULL;
  iz = invumod ((ulong)z[2], p);
  return Flx_Fl_mul(U, iz, p);
}

GEN
Flxq_inv(GEN x,GEN T,ulong p)
{
  pari_sp av=avma;
  GEN U = Flxq_invsafe(x, T, p);
  if (!U) err(talker,"non invertible polynomial in FpXQ_inv");
  return gerepileupto(av, U);
}
