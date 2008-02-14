/* $Id: ZV.c 9633 2008-02-12 10:23:12Z kb $

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
/**                           MULTIPLICATION                       **/
/**                                                                **/
/********************************************************************/
/* x non-empty ZM, y a compatible zc (dimension > 0). */
static GEN
ZM_zc_mul_i(GEN x, GEN y, long c, long l)
{
  long i, j;
  pari_sp av;
  GEN z = cgetg(l,t_COL), s;

  for (i=1; i<l; i++)
  {
    av = avma; s = mulis(gcoeff(x,i,1),y[1]);
    for (j=2; j<c; j++)
      if (y[j]) s = addii(s, mulis(gcoeff(x,i,j),y[j]));
    gel(z,i) = gerepileuptoint(av,s);
  }
  return z;
}
GEN
ZM_zc_mul(GEN x, GEN y) {
  long l = lg(x);
  if (l == 1) return cgetg(1, t_COL);
  return ZM_zc_mul_i(x,y, l, lg(x[1]));
}

/* x ZM, y a compatible zm (dimension > 0). */
GEN
ZM_zm_mul(GEN x, GEN y)
{
  long j, c, l = lg(x), ly = lg(y);
  GEN z = cgetg(ly, t_MAT);
  if (l == 1) return z;
  c = lg(x[1]);
  for (j = 1; j < ly; j++) gel(z,j) = ZM_zc_mul_i(x, gel(y,j), l,c);
  return z;
}

/* return x * y, 1 < lx = lg(x), l = lg(x[1]) */
static GEN
ZM_ZC_mul_i(GEN x, GEN y, long lx, long l)
{
  GEN z = cgetg(l,t_COL), ZERO = gen_0;
  long i, k;
  for (i = 1; i < l; i++)
  {
    pari_sp av = avma;
    GEN c = mulii(gcoeff(x,i,1), gel(y,1)); /* cf. ZMrow_ZC_mul */
    for (k = 2; k < lx; k++)
    {
      GEN t = mulii(gcoeff(x,i,k), gel(y,k));
      if (t != ZERO) c = addii(c, t);
    }
    gel(z,i) = gerepileuptoint(av, c);
  }
  return z;
}
GEN
ZM_mul(GEN x, GEN y)
{
  long j, l, lx=lg(x), ly=lg(y);
  GEN z;
  if (ly==1) return cgetg(1,t_MAT);
  /* if (lx != lg(y[1])) pari_err(operi,"*",x,y); */
  if (lx==1) return zeromat(0, ly-1);
  l = lg(x[1]); z = cgetg(ly,t_MAT);
  for (j=1; j<ly; j++) gel(z,j) = ZM_ZC_mul_i(x, gel(y,j), lx, l);
  return z;
}
GEN
ZM_ZC_mul(GEN x, GEN y)
{
  long lx = lg(x);
  /* if (lx != lg(y)) pari_err(operi,"*",x,y); */
  return lx==1? cgetg(1,t_COL): ZM_ZC_mul_i(x, y, lx, lg(x[1]));
}

GEN
ZC_ZV_mul(GEN x, GEN y)
{
  long i,j, lx=lg(x), ly=lg(y);
  GEN z;
  if (ly==1) return cgetg(1,t_MAT);
  z = cgetg(ly,t_MAT);
  for (j=1; j < ly; j++)
  {
    gel(z,j) = cgetg(lx,t_COL);
    for (i=1; i<lx; i++) gcoeff(z,i,j) = mulii(gel(x,i),gel(y,j));
  }
  return z;
}

GEN
ZV_dotsquare(GEN x)
{
  long i, lx;
  pari_sp av;
  GEN z;
  lx = lg(x);
  if (lx == 1) return gen_0;
  av = avma; z = sqri(gel(x,1));
  for (i=2; i<lx; i++) z = addii(z, sqri(gel(x,i)));
  return gerepileuptoint(av,z);
}

GEN
ZV_dotproduct(GEN x,GEN y)
{
  long i, lx;
  pari_sp av;
  GEN z;
  if (x == y) return ZV_dotsquare(x);
  lx = lg(x);
  if (lx == 1) return gen_0;
  av = avma; z = mulii(gel(x,1),gel(y,1));
  for (i=2; i<lx; i++) z = addii(z, mulii(gel(x,i),gel(y,i)));
  return gerepileuptoint(av,z);
}

static GEN
_ZM_mul(void *data /*ignored*/, GEN x, GEN y)
{ (void)data; return ZM_mul(x,y); }
static GEN
_ZM_sqr(void *data /*ignored*/, GEN x)
{ (void)data; return ZM_mul(x,x); }
GEN
ZM_pow(GEN x, GEN n)
{
  pari_sp av = avma;
  if (!signe(n)) return matid(lg(x)-1);
  return gerepileupto(av, leftright_pow(x, n, NULL, &_ZM_sqr, &_ZM_mul));
}
/********************************************************************/
/**                                                                **/
/**                           ADD, SUB                             **/
/**                                                                **/
/********************************************************************/
static GEN
ZV_add_i(GEN x, GEN y, long lx)
{
  GEN A = cgetg(lx, t_COL);
  long i;
  for (i=1; i<lx; i++) gel(A,i) = addii(gel(x,i), gel(y,i));
  return A;
}
GEN
ZV_add(GEN x, GEN y) { return ZV_add_i(x, y, lg(x)); }

static GEN
ZV_sub_i(GEN x, GEN y, long lx)
{
  long i;
  GEN A = cgetg(lx, t_COL);
  for (i=1; i<lx; i++) gel(A,i) = subii(gel(x,i), gel(y,i));
  return A;
}
GEN
ZV_sub(GEN x, GEN y) { return ZV_sub_i(x, y, lg(x)); }

GEN
ZM_add(GEN x, GEN y)
{
  long lx = lg(x), l, j;
  GEN z;
  if (lx == 1) return cgetg(1, t_MAT);
  z = cgetg(lx, t_MAT); l = lg(x[1]);
  for (j = 1; j < lx; j++) gel(z,j) = ZV_add_i(gel(x,j), gel(y,j), l);
  return z;
}
GEN
ZM_sub(GEN x, GEN y)
{
  long lx = lg(x), l, j;
  GEN z;
  if (lx == 1) return cgetg(1, t_MAT);
  z = cgetg(lx, t_MAT); l = lg(x[1]);
  for (j = 1; j < lx; j++) gel(z,j) = ZV_sub_i(gel(x,j), gel(y,j), l);
  return z;
}
/********************************************************************/
/**                                                                **/
/**                         LINEAR COMBINATION                     **/
/**                                                                **/
/********************************************************************/
/* Return c * X */
GEN
ZV_Z_mul(GEN X, GEN c)
{
  long i, l;
  GEN A;
  if (!signe(c)) return typ(X) == t_VEC? zerovec(lg(X)-1): zerocol(lg(X)-1);
  if (is_pm1(c)) return (signe(c) > 0)? ZV_copy(X): ZV_neg(X);
  l = lg(X); A = cgetg_copy(l, X);
  for (i=1; i<l; i++) gel(A,i) = mulii(c,gel(X,i));
  return A;
}
GEN
ZM_Z_mul(GEN X, GEN c)
{
  long i, j, h, l = lg(X);
  GEN A;
  if (l == 1) return cgetg(1, t_MAT);
  h = lg(X[1]);
  if (!signe(c)) return zeromat(h-1, l-1);
  if (is_pm1(c)) return (signe(c) > 0)? ZM_copy(X): ZM_neg(X);
  A = cgetg_copy(l, X);
  for (j = 1; j < l; j++)
  {
    GEN a = cgetg(h, t_COL), x = gel(X, j);
    for (i = 1; i < h; i++) gel(a,i) = mulii(c, gel(x,i));
    gel(A,j) = a;
  }
  return A;
}

/* X + v Y */
static GEN
ZV_lincomb1(GEN v, GEN X, GEN Y)
{
  long i, lx = lg(X);
  GEN p1, p2, A = cgetg(lx,t_COL);
  if (is_bigint(v))
  {
    long m = lgefint(v);
    for (i=1; i<lx; i++)
    {
      p1=gel(X,i); p2=gel(Y,i);
      if      (!signe(p1)) gel(A,i) = mulii(v,p2);
      else if (!signe(p2)) gel(A,i) = icopy(p1);
      else
      {
	pari_sp av = avma; (void)new_chunk(m+lgefint(p1)+lgefint(p2)); /*HACK*/
	p2 = mulii(v,p2);
	avma = av; gel(A,i) = addii(p1,p2);
      }
    }
  }
  else
  {
    long w = itos(v);
    for (i=1; i<lx; i++)
    {
      p1=gel(X,i); p2=gel(Y,i);
      if      (!signe(p1)) gel(A,i) = mulsi(w,p2);
      else if (!signe(p2)) gel(A,i) = icopy(p1);
      else
      {
	pari_sp av = avma; (void)new_chunk(1+lgefint(p1)+lgefint(p2)); /*HACK*/
	p2 = mulsi(w,p2);
	avma = av; gel(A,i) = addii(p1,p2);
      }
    }
  }
  return A;
}
/* -X + vY */
static GEN
ZV_lincomb_1(GEN v, GEN X, GEN Y)
{
  long i, m, lx = lg(X);
  GEN p1, p2, A = cgetg(lx,t_COL);
  m = lgefint(v);
  for (i=1; i<lx; i++)
  {
    p1=gel(X,i); p2=gel(Y,i);
    if      (!signe(p1)) gel(A,i) = mulii(v,p2);
    else if (!signe(p2)) gel(A,i) = negi(p1);
    else
    {
      pari_sp av = avma; (void)new_chunk(m+lgefint(p1)+lgefint(p2)); /* HACK */
      p2 = mulii(v,p2);
      avma = av; gel(A,i) = subii(p2,p1);
    }
  }
  return A;
}
/* X,Y compatible ZV; u,v in Z. Returns A = u*X + v*Y */
GEN
ZV_lincomb(GEN u, GEN v, GEN X, GEN Y)
{
  pari_sp av;
  long i, lx, m, su, sv;
  GEN p1, p2, A;

  su = signe(u); if (!su) return ZV_Z_mul(Y, v);
  sv = signe(v); if (!sv) return ZV_Z_mul(X, u);
  if (is_pm1(v))
  {
    if (is_pm1(u))
    {
      if (su != sv) A = ZV_sub(X, Y);
      else          A = ZV_add(X, Y);
      if (su < 0) ZV_togglesign(A); /* in place but was created above */
    }
    else
    {
      if (sv > 0) A = ZV_lincomb1 (u, Y, X);
      else        A = ZV_lincomb_1(u, Y, X);
    }
  }
  else if (is_pm1(u))
  {
    if (su > 0) A = ZV_lincomb1 (v, X, Y);
    else        A = ZV_lincomb_1(v, X, Y);
  }
  else
  {
    lx = lg(X); A = cgetg(lx,t_COL); m = lgefint(u)+lgefint(v);
    for (i=1; i<lx; i++)
    {
      p1=gel(X,i); p2=gel(Y,i);
      if      (!signe(p1)) gel(A,i) = mulii(v,p2);
      else if (!signe(p2)) gel(A,i) = mulii(u,p1);
      else
      {
	av = avma; (void)new_chunk(m+lgefint(p1)+lgefint(p2)); /* HACK */
	p1 = mulii(u,p1);
	p2 = mulii(v,p2);
	avma = av; gel(A,i) = addii(p1,p2);
      }
    }
  }
  return A;
}

/********************************************************************/
/**                                                                **/
/**                           CONVERSIONS                          **/
/**                                                                **/
/********************************************************************/
GEN
ZV_to_nv(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l, t_VECSMALL);
  for (i=1; i<l; i++) x[i] = itou(gel(z,i));
  return x;
}

GEN
zm_to_ZM(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_MAT);
  for (i=1; i<l; i++) gel(x,i) = zc_to_ZC(gel(z,i));
  return x;
}

/* same as Flv_to_ZV, Flc_to_ZC, Flm_to_ZM but do not assume positivity */
GEN
ZM_to_zm(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_MAT);
  for (i=1; i<l; i++) gel(x,i) = ZV_to_zv(gel(z,i));
  return x;
}

/********************************************************************/
/**                                                                **/
/**                         COPY, NEGATION                         **/
/**                                                                **/
/********************************************************************/
GEN
ZV_copy(GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx, t_COL);
  for (i=1; i<lx; i++)
  {
    GEN c = gel(x,i);
    gel(y,i) = lgefint(c) == 2? gen_0: icopy(c);
  }
  return y;
}
GEN
Flv_copy(GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx, t_VECSMALL);
  for (i=1; i<lx; i++) y[i] = x[i];
  return y;
}

GEN
ZM_copy(GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx, t_MAT);
  for (i=1; i<lx; i++) gel(y,i) = ZV_copy(gel(x,i));
  return y;
}
GEN
Flm_copy(GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx, t_MAT);
  for (i=1; i<lx; i++) gel(y,i) = Flv_copy(gel(x,i));
  return y;
}

void
ZV_neg_inplace(GEN M)
{
  long i;
  for (i = lg(M)-1; i; i--) gel(M,i) = negi(gel(M,i));
}
GEN
ZV_neg(GEN M)
{
  long i, l = lg(M);
  GEN N = cgetg_copy(l, M);
  for (i = l-1; i ; i--) gel(N,i) = negi(gel(M,i));
  return N;
}
GEN
zv_neg(GEN M)
{
  long i, l = lg(M);
  GEN N = cgetg_copy(l, M);
  for (i=l-1; i; i--) N[i] = -M[i];
  return N;
}
GEN
ZM_neg(GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx, t_MAT);
  for (i=1; i<lx; i++) gel(y,i) = ZV_neg(gel(x,i));
  return y;
}

/********************************************************************/
/**                                                                **/
/**                               TESTS                            **/
/**                                                                **/
/********************************************************************/
int
zv_cmp0(GEN V)
{
  long i, l = lg(V);
  for (i = 1; i < l; i++)
    if (V[i]) return 0;
  return 1;
}

long
ZV_isscalar(GEN x)
{
  long lx = lg(x),i;
  for (i=2; i<lx; i++)
    if (signe(gel(x, i))) return 0;
  return 1;
}

/* check whether x is upper trinagular with positive diagonal coeffs */
int
ZM_ishnf(GEN x)
{
  long i,j, lx = lg(x);
  for (i=2; i<lx; i++)
  {
    if (signe(gcoeff(x,i,i)) <= 0) return 0;
    for (j=1; j<i; j++)
      if (signe(gcoeff(x,i,j))) return 0;
  }
  return (signe(gcoeff(x,1,1)) > 0);
}

/********************************************************************/
/**                                                                **/
/**                       MISCELLANEOUS                            **/
/**                                                                **/
/********************************************************************/
long
zv_content(GEN x)
{
  long i, l = lg(x), s = labs(x[1]);
  for (i=2; i<l && s!=1; i++) s = cgcd(x[i],s);
  return s;
}
