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

#include "pari.h"
#include "paripriv.h"

/********************************************************************/
/**                                                                **/
/**                   GENERIC LINEAR ALGEBRA                       **/
/**                                                                **/
/********************************************************************/
/*           GENERIC  MULTIPLICATION involving zc/zm                */
/* x non-empty t_MAT, y a compatible zc (dimension > 0). */
static GEN
RgM_zc_mul_i(GEN x, GEN y, long c, long l)
{
  long i, j;
  pari_sp av;
  GEN z = cgetg(l,t_COL), s;

  for (i=1; i<l; i++)
  {
    av = avma; s = gmulgs(gcoeff(x,i,1),y[1]);
    for (j=2; j<c; j++)
    {
      long t = y[j];
      switch(t)
      {
        case  0: break;
        case  1: s = gadd(s, gcoeff(x,i,j)); break;
        case -1: s = gsub(s, gcoeff(x,i,j)); break;
        default: s = gadd(s, gmulgs(gcoeff(x,i,j), t)); break;
      }
    }
    gel(z,i) = gerepileupto(av,s);
  }
  return z;
}
GEN
RgM_zc_mul(GEN x, GEN y) { return RgM_zc_mul_i(x,y, lg(x), lg(x[1])); }
/* x t_MAT, y a compatible zm (dimension > 0). */
GEN
RgM_zm_mul(GEN x, GEN y)
{
  long j, c, l = lg(x), ly = lg(y);
  GEN z = cgetg(ly, t_MAT);
  if (l == 1) return z;
  c = lg(x[1]);
  for (j = 1; j < ly; j++) gel(z,j) = RgM_zc_mul_i(x, gel(y,j), l,c);
  return z;
}

static GEN
RgV_zc_mul_i(GEN x, GEN y, long l)
{
  long i;
  GEN z = gen_0;
  pari_sp av = avma;
  for (i = 1; i < l; i++) z = gadd(z, gmulgs(gel(x,i), y[i]));
  return gerepileupto(av, z);
}
GEN
RgV_zc_mul(GEN x, GEN y) { return RgV_zc_mul_i(x, y, lg(x)); }

GEN
RgV_zm_mul(GEN x, GEN y)
{
  long j, l = lg(x), ly = lg(y);
  GEN z = cgetg(ly, t_VEC);
  for (j = 1; j < ly; j++) gel(z,j) = RgV_zc_mul_i(x, gel(y,j), l);
  return z;
}

/* scalar product x.x */
GEN
RgV_dotsquare(GEN x)
{
  long i, lx = lg(x);
  pari_sp av;
  GEN z;
  if (lx == 1) return gen_0;
  av = avma;
  z = gsqr(gel(x,1));
  for (i=2; i<lx; i++) z = gadd(z, gsqr(gel(x,i)));
  return gerepileupto(av,z);
}

/* scalar product x.y, lx = lg(x) = lg(y) */
static GEN
RgV_dotproduct_i(GEN x, GEN y, long lx)
{
  pari_sp av;
  long i;
  GEN z;
  if (lx == 1) return gen_0;
  av = avma;
  z = gmul(gel(x,1),gel(y,1));
  for (i=2; i<lx; i++) z = gadd(z, gmul(gel(x,i), gel(y,i)));
  return gerepileupto(av,z);
}
GEN
RgV_dotproduct(GEN x,GEN y)
{
  if (x == y) return RgV_dotsquare(x);
  return RgV_dotproduct_i(x, y, lg(x));
}
/* v[1] + ... + v[lg(v)-1] */
GEN
RgV_sum(GEN v)
{
  GEN p;
  long i, l = lg(v);
  if (l == 1) return gen_0;
  p = gel(v,1); for (i=2; i<l; i++) p = gadd(p, gel(v,i));
  return p;
}
/* v[1] + ... + v[n]. Assume lg(v) > n. */
GEN
RgV_sumpart(GEN v, long n)
{
  GEN p;
  long i;
  if (!n) return gen_0;
  p = gel(v,1); for (i=2; i<=n; i++) p = gadd(p, gel(v,i));
  return p;
}
/* v[m] + ... + v[n]. Assume lg(v) > n, m > 0. */
GEN
RgV_sumpart2(GEN v, long m, long n)
{
  GEN p;
  long i;
  if (n < m) return gen_0;
  p = gel(v,m); for (i=m+1; i<=n; i++) p = gadd(p, gel(v,i));
  return p;
}

/*                    ADDITION SCALAR + MATRIX                     */
/* x square matrix, y scalar; create the square matrix x + y*Id */
GEN
RgM_Rg_add(GEN x, GEN y)
{
  long l = lg(x), i, j;
  GEN z = cgetg(l,t_MAT);

  if (l==1) return z;
  if (typ(x) != t_MAT || l != lg(x[1])) pari_err(consister,"RgM_Rg_add");
  z = cgetg(l,t_MAT);
  for (i=1; i<l; i++)
  {
    GEN zi = cgetg(l,t_COL), xi = gel(x,i);
    gel(z,i) = zi;
    for (j=1; j<l; j++)
      gel(zi,j) = i==j? gadd(y,gel(xi,j)): gcopy(gel(xi,j));
  }
  return z;
}
GEN
RgM_Rg_add_shallow(GEN x, GEN y)
{
  long l = lg(x), i, j;
  GEN z = cgetg(l,t_MAT);

  if (l==1) return z;
  if (typ(x) != t_MAT || l != lg(x[1])) pari_err(consister,"RgM_Rg_add");
  for (i=1; i<l; i++)
  {
    GEN zi = cgetg(l,t_COL), xi = gel(x,i);
    gel(z,i) = zi;
    for (j=1; j<l; j++) gel(zi,j) = gel(xi,j);
    gel(zi,i) = gadd(gel(zi,i), y);
  }
  return z;
}

GEN
RgC_Rg_add(GEN x, GEN y)
{
  long k, lx = lg(x);
  GEN z = cgetg(lx, t_COL);
  if (lx == 1) pari_err(operf,"+",x,y);
  gel(z,1) = gadd(y,gel(x,1));
  for (k = 2; k < lx; k++) gel(z,k) = gcopy(gel(x,k));
  return z;
}

static GEN
RgC_add_i(GEN x, GEN y, long lx)
{
  GEN A = cgetg(lx, t_COL);
  long i;
  for (i=1; i<lx; i++) gel(A,i) = gadd(gel(x,i), gel(y,i));
  return A;
}
GEN
RgC_add(GEN x, GEN y) { return RgC_add_i(x, y, lg(x)); }
GEN
RgV_add(GEN x, GEN y)
{
  long i, lx = lg(x);
  GEN A = cgetg(lx, t_VEC);
  for (i=1; i<lx; i++) gel(A,i) = gadd(gel(x,i), gel(y,i));
  return A;
}

static GEN
RgC_sub_i(GEN x, GEN y, long lx)
{
  long i;
  GEN A = cgetg(lx, t_COL);
  for (i=1; i<lx; i++) gel(A,i) = gsub(gel(x,i), gel(y,i));
  return A;
}
GEN
RgC_sub(GEN x, GEN y) { return RgC_sub_i(x, y, lg(x)); }
GEN
RgV_sub(GEN x, GEN y)
{
  long i, lx = lg(x);
  GEN A = cgetg(lx, t_VEC);
  for (i=1; i<lx; i++) gel(A,i) = gsub(gel(x,i), gel(y,i));
  return A;
}

GEN
RgM_add(GEN x, GEN y)
{
  long lx = lg(x), l, j;
  GEN z;
  if (lx == 1) return cgetg(1, t_MAT);
  z = cgetg(lx, t_MAT); l = lg(x[1]);
  for (j = 1; j < lx; j++) gel(z,j) = RgC_add_i(gel(x,j), gel(y,j), l);
  return z;
}
GEN
RgM_sub(GEN x, GEN y)
{
  long lx = lg(x), l, j;
  GEN z;
  if (lx == 1) return cgetg(1, t_MAT);
  z = cgetg(lx, t_MAT); l = lg(x[1]);
  for (j = 1; j < lx; j++) gel(z,j) = RgC_sub_i(gel(x,j), gel(y,j), l);
  return z;
}

static GEN
RgC_neg_i(GEN x, long lx)
{
  long i;
  GEN y = cgetg(lx, t_COL);
  for (i=1; i<lx; i++) gel(y,i) = gneg(gel(x,i));
  return y;
}
GEN
RgC_neg(GEN x) { return RgC_neg_i(x, lg(x)); }
GEN
RgV_neg(GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx, t_VEC);
  for (i=1; i<lx; i++) gel(y,i) = gneg(gel(x,i));
  return y;
}
GEN
RgM_neg(GEN x)
{
  long i, hx, lx = lg(x);
  GEN y = cgetg(lx, t_MAT);
  if (lx == 1) return y;
  hx = lg(x[1]);
  for (i=1; i<lx; i++) gel(y,i) = RgC_neg_i(gel(x,i), hx);
  return y;
}

GEN
RgV_RgC_mul(GEN x, GEN y)
{
  long lx = lg(x);
  if (lx != lg(y)) pari_err(operi,"*",x,y);
  return RgV_dotproduct_i(x, y, lx);
}
GEN
RgC_RgV_mul(GEN x, GEN y)
{
  long i, ly = lg(y);
  GEN z = cgetg(ly,t_MAT);
  for (i=1; i<ly; i++) gel(z,i) = RgC_Rg_mul(x, gel(y,i));
  return z;
}
GEN
RgC_RgM_mul(GEN x, GEN y)
{
  long i, ly = lg(y);
  GEN z = cgetg(ly,t_MAT);
  if (ly != 1 && lg(y[1]) != 2) pari_err(operi,"*",x,y);
  for (i=1; i<ly; i++) gel(z,i) = RgC_Rg_mul(x, gcoeff(y,1,i));
  return z;
}
GEN
RgM_RgV_mul(GEN x, GEN y)
{
  if (lg(x) != 2) pari_err(operi,"*",x,y);
  return RgC_RgV_mul(gel(x,1), y);
}

/* compatible t_MAT * t_COL, l = lg(x) = lg(y), lz = l>1? lg(x[1]): 1 */
static GEN
RgM_RgC_mul_i(GEN x, GEN y, long l, long lz)
{
  GEN z = cgetg(lz,t_COL);
  long i, j;
  for (i=1; i<lz; i++)
  {
    pari_sp av = avma;
    GEN t = gmul(gcoeff(x,i,1), gel(y,1)); /* l > 1 ! */
    for (j=2; j<l; j++) t = gadd(t, gmul(gcoeff(x,i,j), gel(y,j)));
    gel(z,i) = gerepileupto(av,t);
  }
  return z;
}
GEN
RgM_RgC_mul(GEN x, GEN y)
{
  long lx = lg(x);
  if (lx != lg(y)) pari_err(operi,"*",x,y);
  return RgM_RgC_mul_i(x, y, lx, (lx == 1)? 1: lg(x[1]));
}
GEN
RgV_RgM_mul(GEN x, GEN y)
{
  long i, lx, ly = lg(y);
  GEN z;
  if (ly == 1) return cgetg(1,t_VEC);
  lx = lg(x);
  if (lx != lg(y[1])) pari_err(operi,"*",x,y);
  z = cgetg(ly, t_VEC);
  for (i=1; i<ly; i++) gel(z,i) = RgV_dotproduct_i(x, gel(y,i), lx);
  return z;
}
GEN
RgM_mul(GEN x, GEN y)
{
  long j, l, lx, ly = lg(y);
  GEN z;
  if (ly == 1) return cgetg(1,t_MAT);
  lx = lg(x);
  if (lx != lg(y[1])) pari_err(operi,"*",x,y);
  z = cgetg(ly, t_MAT);
  l = (lx == 1)? 1: lg(x[1]);
  for (j=1; j<ly; j++) gel(z,j) = RgM_RgC_mul_i(x, gel(y,j), lx, l);
  return z;
}
GEN
RgM_sqr(GEN x)
{
  long j, lx = lg(x);
  GEN z;
  if (lx == 1) return cgetg(1, t_MAT);
  if (lx != lg(x[1])) pari_err(operi,"*",x,x);
  z = cgetg(lx, t_MAT);
  for (j=1; j<lx; j++) gel(z,j) = RgM_RgC_mul_i(x, gel(x,j), lx, lx);
  return z;
}
/* generates the list of powers of x of degree 0,1,2,...,l*/
GEN
RgM_powers(GEN x, long l)
{
  GEN V=cgetg(l+2,t_VEC);
  long i;
  gel(V,1) = matid(lg(x)-1); if (l==0) return V;
  gel(V,2) = gcopy(x);       if (l==1) return V;
  gel(V,3) = RgM_sqr(x);
  for(i = 4; i < l+2; i++)
    gel(V,i) = (i&1)? RgM_sqr(gel(V, (i+1)>>1))
                    : RgM_mul(gel(V, i-1), x);
  return V;
}

GEN
RgC_Rg_div(GEN x, GEN y) {
  long i, lx = lg(x);
  GEN z = cgetg(lx, t_COL);
  for (i=1; i<lx; i++) gel(z,i) = gdiv(gel(x,i),y);
  return z;
}
GEN
RgC_Rg_mul(GEN x, GEN y) {
  long i, lx = lg(x);
  GEN z = cgetg(lx, t_COL);
  for (i=1; i<lx; i++) gel(z,i) = gmul(gel(x,i),y);
  return z;
}
GEN
RgV_Rg_mul(GEN x, GEN y) {
  long i, lx = lg(x);
  GEN z = cgetg(lx, t_VEC);
  for (i=1; i<lx; i++) gel(z,i) = gmul(gel(x,i),y);
  return z;
}
GEN
RgM_Rg_div(GEN X, GEN c) {
  long i, j, h, l = lg(X);
  GEN A = cgetg(l, t_MAT);
  if (l == 1) return A;
  h = lg(X[1]);
  for (j=1; j<l; j++)
  {
    GEN a = cgetg(h, t_COL), x = gel(X, j);
    for (i = 1; i < h; i++) gel(a,i) = gdiv(gel(x,i), c);
    gel(A,j) = a;
  }
  return A;
}
GEN
RgM_Rg_mul(GEN X, GEN c) {
  long i, j, h, l = lg(X);
  GEN A = cgetg(l, t_MAT);
  if (l == 1) return A;
  h = lg(X[1]);
  for (j=1; j<l; j++)
  {
    GEN a = cgetg(h, t_COL), x = gel(X, j);
    for (i = 1; i < h; i++) gel(a,i) = gmul(gel(x,i), c);
    gel(A,j) = a;
  }
  return A;
}

/********************************************************************/
/*                                                                  */
/*                    SCALAR TO MATRIX/VECTOR                       */
/*                                                                  */
/********************************************************************/
/* fill the square nxn matrix equal to t*Id */
static void
fill_scalmat(GEN y, GEN t, GEN _0, long n)
{
  long i;
  if (n < 0) pari_err(talker,"negative size in fill_scalmat");
  for (i = 1; i <= n; i++)
  {
    gel(y,i) = const_col(n, _0);
    gcoeff(y,i,i) = t;
  }
}

GEN
scalarmat(GEN x, long n) {
  GEN y = cgetg(n+1, t_MAT);
  fill_scalmat(y, gcopy(x), gen_0, n); return y;
}
GEN
scalarmat_shallow(GEN x, long n) {
  GEN y = cgetg(n+1, t_MAT);
  fill_scalmat(y, x, gen_0, n); return y;
}
GEN
scalarmat_s(long x, long n) {
  GEN y = cgetg(n+1, t_MAT);
  fill_scalmat(y, stoi(x), gen_0, n); return y;
}
GEN
matid(long n) {
  GEN y = cgetg(n+1, t_MAT);
  fill_scalmat(y, gen_1, gen_0, n); return y;
}
static void
fill_scalcol(GEN y, GEN t, long n)
{
  long i;
  if (n < 0) pari_err(talker,"negative size in fill_scalcol");
  if (n) {
    gel(y,1) = t;
    for (i=2; i<=n; i++) gel(y,i) = gen_0;
  }
}
GEN
scalarcol(GEN x, long n) {
  GEN y = cgetg(n+1,t_COL);
  fill_scalcol(y, gcopy(x), n); return y;
}
GEN
scalarcol_shallow(GEN x, long n) {
  GEN y = cgetg(n+1,t_COL);
  fill_scalcol(y, x, n); return y;
}

int
RgM_isscalar(GEN x, GEN s)
{
  long i, j, lx = lg(x);

  if (lx == 1) return 1;
  if (lx != lg(x[1])) return 0;
  if (!s) s = gcoeff(x,1,1);

  for (j=1; j<lx; j++)
  {
    GEN c = gel(x,j);
    for (i=1; i<j; )
      if (!gequal0(gel(c,i++))) return 0;
    /* i = j */
      if (!gequal(gel(c,i++),s)) return 0;
    for (   ; i<lx; )
      if (!gequal0(gel(c,i++))) return 0;
  }
  return 1;
}

int
RgM_isidentity(GEN x)
{
  long i,j, lx = lg(x);

  if (lx == 1) return 1;
  if (lx != lg(x[1])) return 0;
  for (j=1; j<lx; j++)
  {
    GEN c = gel(x,j);
    for (i=1; i<j; )
      if (!gequal0(gel(c,i++))) return 0;
    /* i = j */
      if (!gequal1(gel(c,i++))) return 0;
    for (   ; i<lx; )
      if (!gequal0(gel(c,i++))) return 0;
  }
  return 1;
}

int
RgM_isdiagonal(GEN x)
{
  long i,j, lx = lg(x);
  if (lx == 1) return 1;
  if (lx != lg(x[1])) return 0;

  for (j=1; j<lx; j++)
  {
    GEN c = gel(x,j);
    for (i=1; i<j; i++)
      if (!gequal0(gel(c,i))) return 0;
    for (i++; i<lx; i++)
      if (!gequal0(gel(c,i))) return 0;
  }
  return 1;
}
int
isdiagonal(GEN x)
{
  return (typ(x)==t_MAT) && RgM_isdiagonal(x);
}

/* returns the first index i<=n such that x=v[i] if it exists, 0 otherwise */
long
RgV_isin(GEN v, GEN x)
{
  long i, l = lg(v);
  for (i = 1; i < l; i++)
    if (gequal(gel(v,i), x)) return i;
  return 0;
}

GEN
RgM_det_triangular(GEN mat)
{
  long i,l = lg(mat);
  pari_sp av;
  GEN s;

  if (l<3) return l<2? gen_1: gcopy(gcoeff(mat,1,1));
  av = avma; s = gcoeff(mat,1,1);
  for (i=2; i<l; i++) s = gmul(s,gcoeff(mat,i,i));
  return av==avma? gcopy(s): gerepileupto(av,s);
}

