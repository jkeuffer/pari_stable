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
/**              Flm, FpM, ZM MULTIPLICATION                       **/
/**                                                                **/
/********************************************************************/
/* == zm_transpose */
GEN
Flm_transpose(GEN x)
{
  long i, dx, lx = lg(x);
  GEN y;
  if (lx == 1) return cgetg(1,t_MAT);
  dx = lg(x[1]); y = cgetg(dx,t_MAT);
  for (i=1; i<dx; i++) gel(y,i) = row_Flm(x,i);
  return y;
}

GEN
FpC_Fp_mul(GEN x, GEN y, GEN p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_COL);
  for (i=1;i<l;i++) gel(z,i) = Fp_mul(gel(x,i),y,p);
  return z;
}
GEN
Flc_Fl_mul(GEN x, ulong y, ulong p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_VECSMALL);
  for (i=1;i<l;i++) z[i] = Fl_mul(x[i], y, p);
  return z;
}
GEN
Flc_Fl_div(GEN x, ulong y, ulong p)
{
  return Flc_Fl_mul(x, Fl_inv(y, p), p);
}
void
Flc_Fl_div_inplace(GEN x, ulong y, ulong p)
{
  return Flc_Fl_mul_inplace(x, Fl_inv(y, p), p);
}

/* x *= y */
void
Flc_Fl_mul_inplace(GEN x, ulong y, ulong p)
{
  long i, l = lg(x);
  for (i=1;i<l;i++) x[i] = Fl_mul(x[i], y, p);
}

/* set y *= x */
void
Flm_Fl_mul_inplace(GEN y, ulong x, ulong p)
{
  long i, j, m = lg(y[1]), l = lg(y);
  if (HIGHWORD(x | p))
    for(j=1; j<l; j++)
      for(i=1; i<m; i++) ucoeff(y,i,j) = Fl_mul(ucoeff(y,i,j), x, p);
  else
    for(j=1; j<l; j++)
      for(i=1; i<m; i++) ucoeff(y,i,j) = (ucoeff(y,i,j) * x) % p;
}
/* set y = x * y */
GEN
Flm_Fl_mul(GEN y, ulong x, ulong p)
{
  long i, j, m = lg(y[1]), l = lg(y);
  GEN z = cgetg(l, t_MAT);
  if (HIGHWORD(x | p))
    for(j=1; j<l; j++) {
      GEN c = cgetg(m, t_VECSMALL); gel(z,j) = c;
      for(i=1; i<m; i++) c[i] = Fl_mul(ucoeff(y,i,j), x, p);
    }
  else
    for(j=1; j<l; j++) {
      GEN c = cgetg(m, t_VECSMALL); gel(z,j) = c;
      for(i=1; i<m; i++) c[i] = (ucoeff(y,i,j) * x) % p;
    }
  return y;
}

/* x[i,]*y. Assume lx > 1 and 0 < i < lg(x[1]) */
static GEN
ZMrow_ZC_mul(GEN x, GEN y, long lx, long i)
{
  GEN c = mulii(gcoeff(x,i,1), gel(y,1)), ZERO = gen_0;
  long k;
  for (k = 2; k < lx; k++)
  {
    GEN t = mulii(gcoeff(x,i,k), gel(y,k));
    if (t != ZERO) c = addii(c, t);
  }
  return c;
}
static ulong
Flmrow_Flc_mul_SMALL(GEN x, GEN y, ulong p, long lx, long i)
{
  ulong c = ucoeff(x,i,1) * y[1];
  long k;
  for (k = 2; k < lx; k++) {
    c += ucoeff(x,i,k) * y[k];
    if (c & HIGHBIT) c %= p;
  }
  return c % p;
}
static ulong
Flmrow_Flc_mul(GEN x, GEN y, ulong p, long lx, long i)
{
  ulong c = Fl_mul(ucoeff(x,i,1), y[1], p);
  long k;
  for (k = 2; k < lx; k++)
    c = Fl_add(c, Fl_mul(ucoeff(x,i,k), y[k], p), p);
  return c;
}

/* return x * y, 1 < lx = lg(x), l = lg(x[1]) */
static GEN
ZM_ZC_mul_i(GEN x, GEN y, long lx, long l)
{
  GEN z = cgetg(l,t_COL);
  long i;
  for (i = 1; i < l; i++)
  {
    pari_sp av = avma;
    GEN c = ZMrow_ZC_mul(x, y, lx, i);
    gel(z,i) = gerepileuptoint(av, c);
  }
  return z;
}
static GEN
FpM_FpC_mul_i(GEN x, GEN y, long lx, long l, GEN p)
{
  GEN z = cgetg(l,t_COL);
  long i;
  for (i = 1; i < l; i++)
  {
    pari_sp av = avma;
    GEN c = ZMrow_ZC_mul(x, y, lx, i);
    gel(z,i) = gerepileuptoint(av, modii(c,p));
  }
  return z;
}
static GEN
Flm_Flc_mul_i_SMALL(GEN x, GEN y, long lx, long l, ulong p)
{
  GEN z = cgetg(l,t_VECSMALL);
  long i;
  for (i = 1; i < l; i++) z[i] = Flmrow_Flc_mul_SMALL(x, y, p, lx, i);
  return z;
}
static GEN
Flm_Flc_mul_i(GEN x, GEN y, long lx, long l, ulong p)
{
  GEN z = cgetg(l,t_VECSMALL);
  long i;
  for (i=1; i<l; i++) z[i] = Flmrow_Flc_mul(x, y, p, lx, i);
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
FpM_mul(GEN x, GEN y, GEN p)
{
  long j, l, lx=lg(x), ly=lg(y);
  GEN z;
  if (ly==1) return cgetg(1,t_MAT);
  /* if (lx != lg(y[1])) pari_err(operi,"*",x,y); */
  if (lx==1) return zeromat(0, ly-1);
  l = lg(x[1]); z = cgetg(ly,t_MAT);
  for (j=1; j<ly; j++) gel(z,j) = FpM_FpC_mul_i(x, gel(y,j), lx, l, p);
  return z;
}
GEN
Flm_mul(GEN x, GEN y, ulong p)
{
  long i,j,l,lx=lg(x), ly=lg(y);
  GEN z;
  if (ly==1) return cgetg(1,t_MAT);
  /* if (lx != lg(y[1])) pari_err(operi,"*",x,y); */
  z = cgetg(ly,t_MAT);
  if (lx==1)
  {
    for (i=1; i<ly; i++) gel(z,i) = cgetg(1,t_VECSMALL);
    return z;
  }
  l = lg(x[1]);
  if (SMALL_ULONG(p)) {
    for (j=1; j<ly; j++)
      gel(z,j) = Flm_Flc_mul_i_SMALL(x, gel(y,j), lx, l, p);
  } else {
    for (j=1; j<ly; j++)
      gel(z,j) = Flm_Flc_mul_i(x, gel(y,j), lx, l, p);
  }
  return z;
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

GEN
Flv_add(GEN x, GEN y, ulong p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_VECSMALL);
  for (i = 1; i < l; i++) z[i] = Fl_add(x[i], y[i], p);
  return z;
}
GEN
Flv_sub(GEN x, GEN y, ulong p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_VECSMALL);
  for (i = 1; i < l; i++) z[i] = Fl_sub(x[i], y[i], p);
  return z;
}
void
Flv_add_inplace(GEN x, GEN y, ulong p)
{
  long i, l = lg(x);
  for (i = 1; i < l; i++) x[i] = Fl_add(x[i], y[i], p);
}
void
Flv_sub_inplace(GEN x, GEN y, ulong p)
{
  long i, l = lg(x);
  for (i = 1; i < l; i++) x[i] = Fl_sub(x[i], y[i], p);
}

/*Multiple a column vector by a line vector to make a matrix*/
GEN
FpC_FpV_mul(GEN x, GEN y, GEN p)
{
  long i,j, lx=lg(x), ly=lg(y);
  GEN z;
  if (ly==1) return cgetg(1,t_MAT);
  z = cgetg(ly,t_MAT);
  for (j=1; j < ly; j++)
  {
    gel(z,j) = cgetg(lx,t_COL);
    for (i=1; i<lx; i++) gcoeff(z,i,j) = Fp_mul(gel(x,i),gel(y,j), p);
  }
  return z;
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

/* Multiply a line vector by a column and return a scalar (t_INT) */
GEN
FpV_dotproduct(GEN x, GEN y, GEN p)
{
  long i, lx = lg(x);
  pari_sp av;
  GEN c;
  /* if (lx != lg(y)) pari_err(operi,"*",x,y); */
  if (lx == 1) return gen_0;
  av = avma; c = mulii(gel(x,1),gel(y,1));
  for (i=2; i<lx; i++) c = addii(c, mulii(gel(x,i),gel(y,i)));
  return gerepileuptoint(av, modii(c,p));
}
GEN
FpV_dotsquare(GEN x, GEN p)
{
  long i, lx = lg(x);
  pari_sp av;
  GEN c;
  if (lx == 1) return gen_0;
  av = avma; c = sqri(gel(x,1));
  for (i=2; i<lx; i++) c = addii(c, sqri(gel(x,i)));
  return gerepileuptoint(av, modii(c,p));
}
ulong
Flv_dotproduct(GEN x, GEN y, ulong p)
{
  long i, lx = lg(x);
  ulong c;
  if (lx == 1) return 0;
  c = Fl_mul(x[1], y[1], p);
  for (i=2; i<lx; i++) c = Fl_add(c, Fl_mul(x[i], y[i], p), p);
  return c;
}

GEN
ZM_ZC_mul(GEN x, GEN y)
{
  long lx = lg(x);
  /* if (lx != lg(y)) pari_err(operi,"*",x,y); */
  return lx==1? cgetg(1,t_COL): ZM_ZC_mul_i(x, y, lx, lg(x[1]));
}
GEN
FpM_FpC_mul(GEN x, GEN y, GEN p)
{
  long lx = lg(x);
  /* if (lx != lg(y)) pari_err(operi,"*",x,y); */
  return lx==1? cgetg(1,t_COL): FpM_FpC_mul_i(x, y, lx, lg(x[1]), p);
}
GEN
Flm_Flc_mul(GEN x, GEN y, ulong p)
{
  long l, lx = lg(x);
  /* if (lx != lg(y)) pari_err(operi,"*",x,y); */
  if (lx==1) return cgetg(1,t_VECSMALL);
  l = lg(x[1]);
  if (SMALL_ULONG(p))
    return Flm_Flc_mul_i_SMALL(x, y, lx, l, p);
  else
    return Flm_Flc_mul_i(x, y, lx, l, p);
}
/* RgV_to_RgX(FpM_FpC_mul(x,y,p), v), p != NULL, memory clean */
GEN
FpM_FpC_mul_FpX(GEN x, GEN y, GEN p, long v)
{
  long i, l, lx = lg(x);
  GEN z;
  /* if (lx != lg(y)) pari_err(operi,"*",x,y); */
  if (lx==1) return zeropol(v);
  l = lg(x[1]);
  z = new_chunk(l+1);
  for (i=l-1; i; i--)
  {
    pari_sp av = avma;
    GEN p1 = ZMrow_ZC_mul(x,y,lx,i);
    p1 = modii(p1, p);
    if (signe(p1))
    {
      if (i != l-1) stackdummy((pari_sp)(z + l+1), (pari_sp)(z + i+2));
      gel(z,i+1) = gerepileuptoint(av, p1);
      break;
    }
    avma = av;
  }
  if (!i) { avma = (pari_sp)(z + l+1); return zeropol(v); }
  z[0] = evaltyp(t_POL) | evallg(i+2);
  z[1] = evalsigne(1) | evalvarn(v);
  for (; i; i--)
  {
    pari_sp av = avma;
    GEN p1 = ZMrow_ZC_mul(x,y,lx,i);
    gel(z,i+1) = gerepileuptoint(av, modii(p1,p));
  }
  return z;
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

GEN
FpC_add(GEN x, GEN y, GEN p)
{
  long i, lx = lg(x);
  GEN z = cgetg(lx, t_COL);
  for (i = 1; i < lx; i++) gel(z, i) = Fp_add(gel(x, i), gel(y, i), p);
  return z;
}
GEN
FpV_add(GEN x, GEN y, GEN p)
{
  long i, lx = lg(x);
  GEN z = cgetg(lx, t_VEC);
  for (i = 1; i < lx; i++) gel(z, i) = Fp_add(gel(x, i), gel(y, i), p);
  return z;
}

GEN
FpC_sub(GEN x, GEN y, GEN p)
{
  long i, lx = lg(x);
  GEN z = cgetg(lx, t_COL);
  for (i = 1; i < lx; i++) gel(z, i) = Fp_sub(gel(x, i), gel(y, i), p);
  return z;
}
GEN
FpV_sub(GEN x, GEN y, GEN p)
{
  long i, lx = lg(x);
  GEN z = cgetg(lx, t_VEC);
  for (i = 1; i < lx; i++) gel(z, i) = Fp_sub(gel(x, i), gel(y, i), p);
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

/*                          TO INTMOD                        */
static GEN
to_intmod(GEN x, GEN p) { return mkintmod(modii(x, p), p); }

/* z in Z[X], return z * Mod(1,p), normalized*/
GEN
FpX_to_mod(GEN z, GEN p)
{
  long i,l = lg(z);
  GEN x = cgetg(l,t_POL); p = icopy(p);
  for (i=2; i<l; i++) gel(x,i) = to_intmod(gel(z,i), p);
  x[1] = z[1]; return normalizepol_i(x,l);
}

/* z in Z^n, return z * Mod(1,p), normalized*/
GEN
FpV_to_mod(GEN z, GEN p)
{
  long i,l = lg(z);
  GEN x = cgetg(l, t_VEC); p = icopy(p);
  for (i=1; i<l; i++) gel(x,i) = to_intmod(gel(z,i), p);
  return x;
}
/* z in Z^n, return z * Mod(1,p), normalized*/
GEN
FpC_to_mod(GEN z, GEN p)
{
  long i,l = lg(z);
  GEN x = cgetg(l, t_COL); p = icopy(p);
  for (i=1; i<l; i++) gel(x,i) = to_intmod(gel(z,i), p);
  return x;
}
/* z in Mat m,n(Z), return z * Mod(1,p), normalized*/
GEN
FpM_to_mod(GEN z, GEN p)
{
  long i,j,l = lg(z), m = lg(gel(z,1));
  GEN  x = cgetg(l,t_MAT), y, zi;
  p = icopy(p);
  for (i=1; i<l; i++)
  {
    gel(x,i) = cgetg(m,t_COL);
    y = gel(x,i); zi= gel(z,i);
    for (j=1; j<m; j++) gel(y,j) = to_intmod(gel(zi,j), p);
  }
  return x;
}

/********************************************************************/
/**                                                                **/
/**                           REDUCTION                            **/
/**                                                                **/
/********************************************************************/
/* z in Z^n, return lift(Col(z) * Mod(1,p)) */
GEN
FpC_red(GEN z, GEN p)
{
  long i,l = lg(z);
  GEN x = cgetg(l, t_COL);
  for (i=1; i<l; i++) gel(x,i) = modii(gel(z,i),p);
  return x;
}

/* z in Z^n, return lift(Vec(z) * Mod(1,p)) */
GEN
FpV_red(GEN z, GEN p)
{
  long i,l = lg(z);
  GEN x = cgetg(l, t_VEC);
  for (i=1; i<l; i++) gel(x,i) = modii(gel(z,i),p);
  return x;
}
GEN
FpV_center(GEN z, GEN p, GEN pov2)
{
  long i,l = lg(z);
  GEN x = cgetg_copy(l, z);
  for (i=1; i<l; i++) gel(x,i) = Fp_center(gel(z,i),p, pov2);
  return x;
}

/* z in Mat m,n(Z), return lift(z * Mod(1,p)) */
GEN
FpM_red(GEN z, GEN p)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_MAT);
  for (i=1; i<l; i++) gel(x,i) = FpC_red(gel(z,i), p);
  return x;
}
GEN
FpM_center(GEN z, GEN p, GEN pov2)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_MAT);
  for (i=1; i<l; i++) gel(x,i) = FpV_center(gel(z,i), p, pov2);
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
RgV_isscalar(GEN x)
{
  long lx = lg(x),i;
  for (i=2; i<lx; i++)
    if (!gcmp0(gel(x, i))) return 0;
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
