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
GEN muliispec(GEN x, GEN y, long nx, long ny);
GEN sqrispec(GEN x, long nx);

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

long Flx_SQR_LIMIT = 200;
long Flx_MUL_LIMIT = 100;
long Flx_INVMONTGOMERY_LIMIT = 6000;
long Flx_POW_MONTGOMERY_LIMIT = 1000;

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
  long i, l = lg(z);
  GEN x = cgetg(l,t_POL);
  for (i=2; i<l; i++) x[i] = lutoi((ulong)z[i]);
  x[1] = evalsigne(l-2!=0)| z[1]; return x;
}
GEN
Flv_ZV(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l, t_VEC);
  for (i=1; i<l; i++) x[i] = lutoi((ulong)z[i]);
  return x;
}
GEN
Flv_ZC(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_COL);
  for (i=1; i<l; i++) x[i] = lutoi((ulong)z[i]);
  return x;
}
GEN
Flm_ZM(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_MAT);
  for (i=1; i<l; i++) x[i] = (long)Flv_ZC((GEN)z[i]);
  return x;
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
  return Flx_renormalize(z,l);
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

/*FIXME: Should be z_zx since modular reduction is not performed*/
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

/*Do not renormalize. Must not use z[0],z[1]*/
static GEN
Flx_red_lg_i(GEN z, long l, ulong p)
{
  long i;
  ulong *y=(ulong *)z;
  GEN x = cgetg(l, t_VECSMALL);
  for (i=2; i<l; i++)
    x[i] = (long) y[i]%p;
  return x; 
}

GEN
Flx_red(GEN z, ulong p)
{
  long l = lg(z);
  GEN x = Flx_red_lg_i(z,l,p); 
  x[1] = z[1]; 
  return Flx_renormalize(x,l);
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
Flx_subspec(GEN x, GEN y, ulong p, long lx, long ly)
{
  long i,lz;
  GEN z;

  if (ly <= lx)
  {
    lz = lx+2; z = cgetg(lz, t_VECSMALL)+2;
    for (i=0; i<ly; i++) z[i] = (long)subuumod((ulong)x[i],(ulong)y[i],p);
    for (   ; i<lx; i++) z[i] = x[i];
  }
  else
  {
    lz = ly+2; z = cgetg(lz, t_VECSMALL)+2;
    for (i=0; i<lx; i++) z[i] = (long)subuumod((ulong)x[i],(ulong)y[i],p);
    for (   ; i<ly; i++) z[i] = y[i]? (long)(p - y[i]): y[i];
  }
 return Flx_renormalize(z-2, lz);
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
Flx_negspec(GEN x, ulong p, long l)
{
  long i;
  GEN z = cgetg(l+2, t_VECSMALL) + 2;
  for (i=0; i<l; i++) 
    z[i] = x[i]? (long)p - x[i]: 0;
  return z-2;
}


GEN
Flx_neg(GEN x, ulong p)
{
  GEN z = Flx_negspec(x+2, p, lgpol(x));
  z[1] = x[1];
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

INLINE long
maxlenghtcoeffpol (ulong p, long n)
{
  pari_sp ltop=avma;
  long l;
  GEN z=muluu(p-1,p-1);
  z=mulis(z,n);
  l=lgefint(z)-2;
  avma=ltop;
  return l;
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
static GEN
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
  z -= 2; return z; 
}

INLINE GEN
Flx_mulspec_mulii(GEN a, GEN b, ulong p, long na, long nb)
{
  GEN z=muliispec(a,b,na,nb);
  return Flx_red_lg_i(z,lgefint(z),p);
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
  if (na>30 && maxlenghtcoeffpol(p,nb)==1)
    return Flx_shiftip(av,Flx_mulspec_mulii(a,b,p,na,nb), v);
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

static GEN
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
      p1 <<= 1; 
      if ((i&1) == 0) p1 += x[i>>1] * x[i>>1];
      z[i] = (long) (p1 % p);
    }
    for (  ; i<nz; i++)
    {
      p1 = Flx_mullimb_ok(x+i,x,p,i-nx+1, (i+1)>>1);
      p1 <<= 1; 
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
  z -= 2; return z;
}

#if 0
/* used only by Flx_sqrspec #if 0 code.*/
static GEN
Flx_2_mul(GEN x, ulong p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_VECSMALL);
  for (i=2; i<l; i++) z[i] = (long)adduumod(x[i], x[i], p);
  z[1] = x[1]; return z;
}
#endif

static GEN
Flx_sqrspec_sqri(GEN a, ulong p, long na)
{
  GEN z=sqrispec(a,na);
  return Flx_red_lg_i(z,lgefint(z),p);
}

GEN
Flx_sqrspec(GEN a, ulong p, long na)
{
  GEN a0,c,c0,c1;
  long n0, n0a, i, v = 0;
  pari_sp av;

  while (na && !a[0]) { a++; na--; v += 2; }
  av = avma;
  if (na > 30 && maxlenghtcoeffpol(p,na)==1)
    return Flx_shiftip(av, Flx_sqrspec_sqri(a,p,na), v);
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
#if 0
    c1 = Flx_2_mul(Flx_mulspec(a0,a,p, na,n0a), p);
#else
    GEN  t = Flx_addspec(a0,a,p,na,n0a);
    t = Flx_sqr(t,p);
    c1= Flx_add(c0,c, p);
    c1= Flx_sub(t, c1, p);
#endif
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

long 
Flx_valuation(GEN x)
{
  long i, l=lg(x);
  if (l==2)  return VERYBIGINT;
  for (i=2; i<l && x[i]==0; i++);
  return i-2;
}

GEN
Flx_recipspec(GEN x, long l, long n)
{
  long i;
  GEN z=cgetg(n+2,t_VECSMALL)+2;
  for(i=0; i<l; i++)
    z[n-i-1] = x[i];
  for(   ; i<n; i++)
    z[n-i-1] = 0;
  return Flx_renormalize(z-2,n+2);
}

GEN
Flx_recip(GEN x)
{
  GEN z=Flx_recipspec(x+2,lgpol(x),lgpol(x));
  z[1]=x[1];
  return z;
}

/*
 * x/polrecip(P)+O(x^n)
 */
static GEN 
Flx_invmontgomery_basecase(GEN T, ulong p)
{
  long i, l=lg(T)-1, k;
  GEN r=cgetg(l,t_VECSMALL); r[1]=T[1];
  r[2]=0; r[3]=1;
  for (i=4;i<l;i++)
  {
    r[i] = 0;
    for (k=3;k<i;k++)
      r[i]= (long) subuumod((ulong)r[i],muluumod((ulong)T[l-i+k],(ulong)r[k],p),p);
  }
  r = Flx_renormalize(r,l);
  return r;
}

/*Use newton style inversion.
 * Use log2(n) sqr +log2(n) mul*/
static GEN 
Flx_invmontgomery_newton(GEN T, ulong p)
{
  long i, l=lgpol(T), ll=l+2;
  GEN x, q, z;
  long v=T[1];
  pari_sp av, av2;
  x = Flx_recipspec(T+2,l-1,l);
  x[1] = v;
  x = Flx_neg(x,p);
  q = Flx_copy(x); q[2]=1;
  i = Flx_valuation(x);
  av=avma;
  new_chunk(ll<<1);
  av2=avma;
  for (  ; i<l; i<<=1)
  {
    x=Flx_sqr(x,p);
    x=Flx_renormalize(x,min(lg(x),ll));
    z=Flx_mul(q,x,p);
    z=Flx_renormalize(z,min(lg(z),ll));
    q=Flx_add(q,z,p);
    avma=av;
    q=Flx_copy(q);
    x=Flx_copy(x);
    avma=av2;
  }
  q=Flx_mul(q,Flx_polx(v),p);
  return q;
}

/*
 * x/polrecip(P)+O(x^n)
 */
GEN
Flx_invmontgomery(GEN T, ulong p)
{
  pari_sp ltop=avma;
  long l=lg(T);
  GEN r;
  ulong c=T[l-1], ci=1;
  if (l<5) return Flx_zero(T[1]);
  if (c!=1)
  {
    ci=invumod(c,p);
    T=Flx_Fl_mul(T, ci, p);
  }
  if (l<Flx_INVMONTGOMERY_LIMIT)
    r=Flx_invmontgomery_basecase(T,p);
  else
    r=Flx_invmontgomery_newton(T,p);
  if (c!=1)  r=Flx_Fl_mul(r,ci,p);
  return gerepileupto(ltop, r);
}

/* Compute x mod T where lg(x)<=2*lg(T)-2
 * and mg is the Montgomery inverse of T. 
 */
GEN
Flx_redmontgomery(GEN x, GEN mg, GEN T, ulong p)
{
  pari_sp ltop=avma;
  GEN z;
  long l=lgpol(x);
  long lt=degpol(T); /*We discard the leading term*/
  long lead=lt-1;
  long ld=l-lt+1;
  long lm=min(ld,lgpol(mg));
  if (l<=lt)
    return Flx_copy(x);
  new_chunk(lt);
  z=Flx_recipspec(x+2+lead,ld,ld);              /* z = rec(x)*/
  z=Flx_mulspec(z+2,mg+2,p,min(ld,lgpol(z)),lm);/* z = rec(x) * mg */
  z=Flx_recipspec(z+2,lgpol(z),ld);             /* z = rec (rec(x) * mg) */
  z=Flx_mulspec(z+2,T+2,p,min(ld,lgpol(z)),lt); /* z *= pol */
  avma=ltop;
  z=Flx_subspec(x+2,z+2,p,lt,min(lt,lgpol(z))); /* z = x - z */
  z[1]=T[1];
  return z;
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
  if (lx == 1) return Fl_Flx(1,vs);
  p1 = cgetg(lx, t_VEC); global_pp = p;
  for (k=1,i=1; i<lx-1; i+=2)
  {
    p2 = cgetg(5,t_VECSMALL); p1[k++] = (long)p2;
    p2[1] = vs;
    p2[2] = muluumod(a[i], a[i+1], p);
    p2[3] = a[i] + a[i+1];
    if ((ulong)p2[3] >= p) p2[3] -= p;
    if (p2[3]) p2[3] = p - p2[3]; /* - (a[i] + a[i+1]) mod p */
    p2[4] = 1; 
  }
  if (i < lx)
  {
    p2 = cgetg(4,t_VECSMALL); p1[k++] = (long)p2;
    p2[1] = vs;
    p2[2] = a[i]?p - a[i]:0;
    p2[3] = 1;
  }
  setlg(p1, k); return divide_conquer_prod(p1, _Flx_mul);
}

GEN
Flx_div_by_X_x(GEN a, ulong x, ulong p, ulong *rem)
{
  long l = lg(a), i;
  GEN a0, z0;
  GEN z = cgetg(l-1,t_VECSMALL);
  z[1] = a[1];
  a0 = a + l-1;
  z0 = z + l-2; *z0 = *a0--;
  if (u_OK_ULONG(p))
  {
    for (i=l-3; i>1; i--) /* z[i] = (a[i+1] + x*z[i+1]) % p */
    {
      ulong t = (*a0-- + x *  *z0--) % p;
      *z0 = (long)t;
    }
    if (rem) *rem = (*a0 + x *  *z0) % p;
  }
  else
  {
    for (i=l-3; i>1; i--)
    {
      ulong t = adduumod((ulong)*a0--, muluumod(x, *z0--, p), p);
      *z0 = (long)t;
    }
    if (rem) *rem = adduumod((ulong)*a0, muluumod(x, *z0, p), p);
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
    T = Flx_div_by_X_x(Q, xa[i], p, NULL);
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
  GEN mg;
  ulong p;
} Flxq_muldata;


static GEN
_sqr_montgomery(void *data, GEN x)
{
  Flxq_muldata *D = (Flxq_muldata*)data;
  return Flx_redmontgomery(Flx_sqr(x,D->p),D->mg, D->pol, D->p);
}
static GEN
_mul_montgomery(void *data, GEN x, GEN y)
{
  Flxq_muldata *D = (Flxq_muldata*)data;
  return Flx_redmontgomery(Flx_mul(x,y,D->p),D->mg, D->pol, D->p);
}

static GEN
_Flxq_sqr(void *data, GEN x)
{
  Flxq_muldata *D = (Flxq_muldata*)data;
  return Flxq_sqr(x, D->pol, D->p);
}
static GEN
_Flxq_mul(void *data, GEN x, GEN y)
{
  Flxq_muldata *D = (Flxq_muldata*)data;
  return Flxq_mul(x,y, D->pol, D->p);
}

/* n-Power of x in Z/pZ[X]/(pol), as t_VECSMALL. */
GEN
Flxq_pow(GEN x, GEN n, GEN pol, ulong p)
{
  pari_sp av = avma;
  Flxq_muldata D;
  GEN y;
  if (!signe(n)) return Fl_Flx(1,varn(pol));
  if (signe(n) < 0)
    x=Flxq_inv(x,pol,p);
  else
    x=Flx_rem(x, pol, p);
  if (is_pm1(n)) return x;
  D.pol = pol;
  D.p   = p;
  /* not tuned*/
  if (pol[2] && degpol(pol) >= Flx_POW_MONTGOMERY_LIMIT)
  {
    /* We do not handle polynomials multiple of x yet */
    D.mg  = Flx_invmontgomery(pol,p);
    y = leftright_pow(x, n, (void*)&D, &_sqr_montgomery, &_mul_montgomery);
  }
  else
    y = leftright_pow(x, n, (void*)&D, &_Flxq_sqr, &_Flxq_mul);
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
  if (!U) err(talker,"non invertible polynomial in Flxq_inv");
  return gerepileupto(av, U);
}

/* generates the list of powers of x of degree 0,1,2,...,l*/
GEN
Flxq_powers(GEN x, long l, GEN T, ulong p)
{
  GEN V=cgetg(l+2,t_VEC);
  long i;
  long v=T[1];
  V[1] = (long) Fl_Flx(1, v);
  if (l==0) return V;
  V[2] = (long) Flx_copy(x);
  if (l==1) return V;
  V[3] = (long) Flxq_sqr(x,T,p);
  for(i=4;i<l+2;i++)
    V[i] = (long) Flxq_mul((GEN) V[i-1],x,T,p);
#if 0
  TODO: Karim proposes to use squaring:
  V[i] = (long) ((i&1)?Flxq_sqr((GEN) V[(i+1)>>1],T,p)
                       :Flxq_mul((GEN) V[i-1],x,T,p));
  Please profile it.
#endif
  return V;
}

GEN
FlxV_Flv_innerprod(GEN V, GEN W, ulong p)
{
  pari_sp ltop=avma;
  long i;
  GEN z = Flx_Fl_mul((GEN)V[1],W[1],p);
  for(i=2;i<lg(V);i++)
    z=Flx_add(z,Flx_Fl_mul((GEN)V[i],W[i],p),p);
  return gerepileupto(ltop,z);
}

GEN
ZXV_FlxV(GEN v, ulong p)
{
  long j, N = lg(v);
  GEN y = cgetg(N, t_VEC);
  for (j=1; j<N; j++) y[j] = (long)ZX_Flx((GEN)v[j], p);
  return y;
}

GEN
FlxV_Flm(GEN v, long n)
{
  long j, N = lg(v);
  GEN y = cgetg(N, t_MAT);
  for (j=1; j<N; j++) y[j] = (long)Flx_Flv_lg((GEN)v[j], n);
  return y;
}


/**************************************************************
 **                 FlxX                                    **
 **                                                          **
 **************************************************************/

/* FlxX are t_POL with Flx coefficients.
 * Normally the variable ordering should be respected.*/

GEN 
FlxX_ZXX(GEN B)
{
  long lb=lg(B);
  long i;
  GEN b=cgetg(lb,t_POL);
  for (i=2; i<lb; i++) 
    if (lgpol(B[i]))
      b[i] = (long) Flx_ZX((GEN)B[i]);
    else
      b[i] = zero;
  b[1] = B[1]; return b;
}

/* Note: v is used _only_ for the t_INT. It must match
 * the variable of any t_POL coefficients.
 */

GEN 
ZXX_FlxX(GEN B, ulong p, long v)
{
  long lb=lg(B);
  long i;
  GEN b=cgetg(lb,t_POL);
  long vs = evalvarn(v);
  b[1]=evalsigne(1)|(((ulong)B[1])&VARNBITS);
  for (i=2; i<lb; i++) 
    switch (typ(B[i]))
    {
    case t_INT:  
      b[i] = (long)Fl_Flx(umodiu((GEN)B[i], p), vs);
      break;
    case t_POL:
      b[i] = (long)ZX_Flx((GEN)B[i], p);
      break;
    }
  return b;
}

/*Similar to normalizepol, in place*/
/*FIXME: should be zxX_renormalize*/
GEN
FlxX_renormalize(GEN /*in place*/ x, long lx)
{
  long i;
  for (i = lx-1; i>1; i--)
    if (lgpol(x[i])) break;
  stackdummy(x + (i+1), lg(x) - (i+1));
  setlg(x, i+1); setsigne(x, i!=1); return x;
}

/* matrix whose entries are given by the coeffs of the polynomial v in
 * two variables (considered as degree n polynomials) */
GEN
FlxX_Flm(GEN v, long n)
{
  long j, N = lg(v)-1;
  GEN y = cgetg(N, t_MAT);
  v++;
  for (j=1; j<N; j++) y[j] = (long)Flx_Flv_lg((GEN)v[j], n);
  return y;
}

GEN
Flm_FlxX(GEN x, long v,long w)
{
  long j, lx = lg(x);
  GEN y = cgetg(lx+1, t_POL);
  y[1]=evalsigne(1) | v;
  y++;
  for (j=1; j<lx; j++) y[j] = (long)Flv_Flx((GEN)x[j], w);
  return FlxX_renormalize(--y, lx+1);
}

/* P(X,Y) --> P(Y,X), n-1 is the degree in Y */
GEN
FlxX_swap(GEN x, long n, long ws)
{
  long j, lx = lg(x), ly = n+3;
  GEN y = cgetg(ly, t_POL);
  y[1] = x[1];
  for (j=2; j<ly; j++)
  {
    long k;
    GEN p1 = cgetg(lx, t_VECSMALL);
    p1[1] = ws;
    for (k=2; k<lx; k++)
      if( j<lg(x[k]))
        p1[k] = mael(x,k,j);
      else
        p1[k] = 0;
    y[j] = (long)Flx_renormalize(p1,lx);
  }
  return FlxX_renormalize(y,ly);
}

/*Fix me should be  zxX_to_Kronecker since it does not use l*/
GEN
FlxX_to_Kronecker(GEN P, GEN Q)
{
  /* P(X) = sum Mod(.,Q(Y)) * X^i, lift then set X := Y^(2n-1) */
  long i,j,k,l;
  long lx = lg(P), N = (degpol(Q)<<1) + 1;
  GEN p1;
  GEN y = cgetg((N-2)*(lx-2) + 2, t_VECSMALL);
  y[1] = P[1];
  for (k=i=2; i<lx; i++)
  {
    p1 = (GEN)P[i];
    l = lg(p1);
    for (j=2; j < l; j++) y[k++] = p1[j];
    if (i == lx-1) break;
    for (   ; j < N; j++) y[k++] = 0;
  }
  setlg(y, k); return y;
}

/**************************************************************
 **                 FlxqX                                    **
 **                                                          **
 **************************************************************/

/* FlxqX are t_POL with Flxq coefficients.
 * Normally the variable ordering should be respected.*/

/*Not stack clean.*/
GEN
FlxqX_from_Kronecker(GEN z, GEN T, ulong p)
{
  long i,j,lx,l, N = (degpol(T)<<1) + 1;
  GEN x, t = cgetg(N,t_VECSMALL);
  t[1] = T[1];
  l = lg(z); lx = (l-2) / (N-2);
  x = cgetg(lx+3,t_POL); x[1]=z[1];
  for (i=2; i<lx+2; i++)
  {
    for (j=2; j<N; j++) t[j] = z[j];
    z += (N-2);
    x[i] = (long)Flx_rem(Flx_renormalize(t,N), T,p);
  }
  N = (l-2) % (N-2) + 2;
  for (j=2; j<N; j++) t[j] = z[j];
  x[i] = (long)Flx_rem(Flx_renormalize(t,N), T,p);
  return Flx_renormalize(x, i+1);
}

GEN
FlxqX_red(GEN z, GEN T, ulong p)
{
  GEN res;
  int i, l = lg(z);
  res = cgetg(l,t_POL); res[1] = z[1];
  for(i=2;i<l;i++)
    res[i] = (long)Flx_rem((GEN)z[i],T,p);
  return FlxX_renormalize(res,lg(res));
}

GEN
FlxqX_mul(GEN x, GEN y, GEN T, ulong p)
{
  pari_sp ltop=avma;
  GEN z,kx,ky;
  kx= FlxX_to_Kronecker(x,T);
  ky= FlxX_to_Kronecker(y,T);
  z = Flx_mul(ky, kx, p);
  z = FlxqX_from_Kronecker(z,T,p);
  return gerepileupto(ltop,z);
}

GEN
FlxqX_sqr(GEN x, GEN T, ulong p)
{
  pari_sp ltop=avma;
  GEN z,kx;
  kx= FlxX_to_Kronecker(x,T);
  z = Flx_sqr(kx, p); 
  z = FlxqX_from_Kronecker(z,T,p);
  return gerepileupto(ltop,z);
}

GEN
FlxqX_Flxq_mul(GEN P, GEN U, GEN T, ulong p)
{
  int i, lP = lg(P);
  GEN res = cgetg(lP,t_POL);
  res[1] = P[1];
  for(i=2; i<lP; i++)
    res[i] = (long)Flxq_mul(U,(GEN)P[i], T,p);
  return Flx_renormalize(res,lg(res));
}

GEN
FlxqX_normalize(GEN z, GEN T, ulong p)
{
  GEN p1 = leading_term(z);
  if (!lgpol(z) || (!degpol(p1) && p1[1] == 1)) return z;
  return FlxqX_Flxq_mul(z, Flxq_inv(p1,T,p), T,p);
}

/* x and y in Z[Y][X]. Assume T irreducible mod p */
GEN
FlxqX_divrem(GEN x, GEN y, GEN T, ulong p, GEN *pr)
{
  long vx, dx, dy, dz, i, j, sx, lrem;
  pari_sp av0, av, tetpil;
  GEN z,p1,rem,lead;

  if (!signe(y)) err(gdiver);
  vx=varn(x); dy=degpol(y); dx=degpol(x);
  if (dx < dy)
  {
    if (pr)
    {
      av0 = avma; x = FlxqX_red(x, T, p);
      if (pr == ONLY_DIVIDES) 
      { 
        avma=av0; 
        return signe(x)? NULL: zeropol(vx); 
      }
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
    av0 = avma; x = FlxqX_normalize(x,T,p); tetpil = avma;
    return gerepile(av0,tetpil,FlxqX_red(x,T,p));
  }
  av0 = avma; dz = dx-dy;
  lead = (!degpol(lead) && lead[2]==1)? NULL: gclone(Flxq_inv(lead,T,p));
  avma = av0;
  z = cgetg(dz+3,t_POL); z[1] = x[1];
  x += 2; y += 2; z += 2;

  p1 = (GEN)x[dx]; av = avma;
  z[dz] = lead? lpileupto(av, Flxq_mul(p1,lead, T, p)): lcopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av=avma; p1=(GEN)x[i];
    for (j=i-dy+1; j<=i && j<=dz; j++)
      p1 = Flx_sub(p1, Flx_mul((GEN)z[j],(GEN)y[i-j],p),p);
    if (lead) p1 = Flx_mul(p1, lead,p);
    tetpil=avma; z[i-dy] = lpile(av,tetpil,Flx_rem(p1,T,p));
  }
  if (!pr) { if (lead) gunclone(lead); return z-2; }

  rem = (GEN)avma; av = (pari_sp)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = (GEN)x[i];
    for (j=0; j<=i && j<=dz; j++)
      p1 = Flx_sub(p1, Flx_mul((GEN)z[j],(GEN)y[i-j],p),p);
    tetpil=avma; p1 = Flx_rem(p1, T, p); if (lgpol(p1)) { sx = 1; break; }
    if (!i) break;
    avma=av;
  }
  if (pr == ONLY_DIVIDES)
  {
    if (lead) gunclone(lead);
    if (sx) { avma=av0; return NULL; }
    avma = (pari_sp)rem; return z-2;
  }
  lrem=i+3; rem -= lrem;
  rem[0] = evaltyp(t_POL) | evallg(lrem);
  rem[1] = z[-1];
  p1 = gerepile((pari_sp)rem,tetpil,p1);
  rem += 2; rem[i]=(long)p1;
  for (i--; i>=0; i--)
  {
    av=avma; p1 = (GEN)x[i];
    for (j=0; j<=i && j<=dz; j++)
      p1 = Flx_sub(p1, Flx_mul((GEN)z[j],(GEN)y[i-j],p), p);
    tetpil=avma; rem[i]=lpile(av,tetpil, Flx_rem(p1, T, p));
  }
  rem -= 2;
  if (lead) gunclone(lead);
  if (!sx) (void)FlxX_renormalize(rem, lrem);
  if (pr == ONLY_REM) return gerepileupto(av0,rem);
  *pr = rem; return z-2;
}

/*******************************************************************/
/*                                                                 */
/*                       (Fl[X]/T(X))[Y] / S(Y)                    */
/*                                                                 */
/*******************************************************************/

/*Preliminary implementation to speed up Fp_isom*/
typedef struct {
  GEN S, T, mg;
  ulong p;
} FlxYqQ_muldata;

/* reduce x in Fl[X, Y] in the algebra Fl[X, Y]/ (P(X),Q(Y)) */
static GEN
FlxYqQ_redswap(GEN x, GEN S, GEN mg, GEN T, ulong p)
{
  pari_sp ltop=avma;
  long n=degpol(S);
  long m=degpol(T);
  long w = S[1];
  GEN V = FlxX_swap(x,n,w);
  V = FlxqX_red(V,T,p);
  V = FlxX_swap(V,m,w);
  return gerepilecopy(ltop,V); 
}
static GEN
FlxYqQ_sqr(void *data, GEN x)
{
  FlxYqQ_muldata *D = (FlxYqQ_muldata*)data;
  return FlxYqQ_redswap(FlxqX_sqr(x, D->S, D->p),D->S,D->mg,D->T,D->p);
}

static GEN
FlxYqQ_mul(void *data, GEN x, GEN y)
{
  FlxYqQ_muldata *D = (FlxYqQ_muldata*)data;
  return FlxYqQ_redswap(FlxqX_mul(x,y, D->S, D->p),D->S,D->mg,D->T,D->p);
}

/* x in Z[X,Y], S in Z[X] over Fq = Z[Y]/(p,T); compute lift(x^n mod (S,T,p)) */
GEN
FlxYqQ_pow(GEN x, GEN n, GEN S, GEN T, ulong p)
{
  pari_sp av = avma;
  FlxYqQ_muldata D;
  GEN y;
  D.S = S;
  D.T = T;
  D.p = p;
  y = leftright_pow(x, n, (void*)&D, &FlxYqQ_sqr, &FlxYqQ_mul);
  return gerepileupto(av, y);
}

typedef struct {
  GEN T, S;
  ulong p;
} kronecker_muldata;

static GEN
FlxqXQ_red(void *data, GEN x)
{
  kronecker_muldata *D = (kronecker_muldata*)data;
  GEN t = FlxqX_from_Kronecker(x, D->T,D->p);
  t = FlxqX_divrem(t, D->S,D->T,D->p, ONLY_REM);
  return FlxX_to_Kronecker(t,D->T);
}
static GEN
FlxqXQ_mul(void *data, GEN x, GEN y) {
  return FlxqXQ_red(data, Flx_mul(x,y,((kronecker_muldata*) data)->p));
}
static GEN
FlxqXQ_sqr(void *data, GEN x) {
  return FlxqXQ_red(data, Flx_sqr(x,((kronecker_muldata*) data)->p));
}

/* x over Fq, return lift(x^n) mod S */
GEN
FlxqXQ_pow(GEN x, GEN n, GEN S, GEN T, ulong p)
{
  pari_sp av0 = avma;
  GEN y;
  kronecker_muldata D;

  D.S = S;
  D.T = T;
  D.p = p;
  y = leftright_pow(FlxX_to_Kronecker(x,T), n, 
      (void*)&D, &FlxqXQ_sqr, &FlxqXQ_mul);
  y = FlxqX_from_Kronecker(y, T,p);
  return gerepileupto(av0, y);
}

