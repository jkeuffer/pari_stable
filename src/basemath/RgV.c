/* $Id: alglin1.c 9633 2008-02-12 10:23:12Z kb $

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
       if (y[j]) s = gadd(s, gmulgs(gcoeff(x,i,j),y[j]));
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
  long i, lx;
  pari_sp av;
  GEN z;
  lx = lg(x);
  if (lx == 1) return gen_0;
  av = avma;
  z = gsqr(gel(x,1));
  for (i=2; i<lx; i++)
    z = gadd(z, gsqr(gel(x,i)));
  return gerepileupto(av,z);
}

/* scalar product x.y */
GEN
RgV_dotproduct(GEN x,GEN y)
{
  long i, lx;
  pari_sp av;
  GEN z;
  if (x == y) return RgV_dotsquare(x);
  lx = lg(x);
  if (lx == 1) return gen_0;
  av = avma;
  z = gmul(gel(x,1),gel(y,1));
  for (i=2; i<lx; i++)
    z = gadd(z, gmul(gel(x,i),gel(y,i)));
  return gerepileupto(av,z);
}

/*                    ADDITION SCALAR + MATRIX                     */
/* x square matrix, y scalar; create the square matrix x + y*Id */
GEN
RgM_Rg_add(GEN x, GEN y)
{
  long l = lg(x), i, j;
  GEN z = cgetg(l,t_MAT);

  if (l==1) return z;
  if (typ(x) != t_MAT || l != lg(x[1])) pari_err(mattype1,"RgM_Rg_add");
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
  if (typ(x) != t_MAT || l != lg(x[1])) pari_err(mattype1,"RgM_Rg_add");
  for (i=1; i<l; i++)
  {
    GEN zi = cgetg(l,t_COL), xi = gel(x,i);
    gel(z,i) = zi;
    for (j=1; j<l; j++) gel(zi,j) = gel(xi,j);
    gel(zi,i) = gadd(gel(zi,i), y);
  }
  return z;
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
matid_intern(long n, GEN _1, GEN _0) {
  GEN y = cgetg(n+1, t_MAT);
  fill_scalmat(y, _1, _0, n); return y;
}
GEN
matid(long n) { return matid_intern(n, gen_1, gen_0); }

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

long
RgV_isscalar(GEN x)
{
  long lx = lg(x),i;
  for (i=2; i<lx; i++)
    if (!gcmp0(gel(x, i))) return 0;
  return 1;
}
long
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
      if (!gcmp0(gel(c,i++))) return 0;
    /* i = j */
      if (!gequal(gel(c,i++),s)) return 0;
    for (   ; i<lx; )
      if (!gcmp0(gel(c,i++))) return 0;
  }
  return 1;
}

long
RgM_isidentity(GEN x)
{
  long i,j, lx = lg(x);

  if (lx == 1) return 1;
  if (lx != lg(x[1])) return 0;
  for (j=1; j<lx; j++)
  {
    GEN c = gel(x,j);
    for (i=1; i<j; )
      if (!gcmp0(gel(c,i++))) return 0;
    /* i = j */
      if (!gcmp1(gel(c,i++))) return 0;
    for (   ; i<lx; )
      if (!gcmp0(gel(c,i++))) return 0;
  }
  return 1;
}

long
RgM_isdiagonal(GEN x)
{
  long i,j, lx = lg(x);
  if (lx == 1) return 1;
  if (lx != lg(x[1])) return 0;

  for (j=1; j<lx; j++)
  {
    GEN c = gel(x,j);
    for (i=1; i<j; i++)
      if (!gcmp0(gel(c,i))) return 0;
    for (i++; i<lx; i++)
      if (!gcmp0(gel(c,i))) return 0;
  }
  return 1;
}
long
isdiagonal(GEN x)
{
  if (typ(x)!=t_MAT) pari_err(typeer,"isdiagonal");
  return RgM_isdiagonal(x);
}

/* check whether x is upper trinagular with positive diagonal coeffs */
int
RgM_ishnf(GEN x)
{
  long i,j, lx = lg(x);
  for (i=2; i<lx; i++)
  {
    if (gsigne(gcoeff(x,i,i)) <= 0) return 0;
    for (j=1; j<i; j++)
      if (!gcmp0(gcoeff(x,i,j))) return 0;
  }
  return (gsigne(gcoeff(x,1,1)) > 0);
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

