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
FpC_center(GEN z, GEN p, GEN pov2)
{
  long i,l = lg(z);
  GEN x = cgetg(l, t_COL);
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
  for (i=1; i<l; i++) gel(x,i) = FpC_center(gel(z,i), p, pov2);
  return x;
}

/********************************************************************/
/**                                                                **/
/**                           ADD, SUB                             **/
/**                                                                **/
/********************************************************************/
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
Flv_add(GEN x, GEN y, ulong p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_VECSMALL);
  if (p==2)
    for (i = 1; i < l; i++) z[i] = x[i]^y[i];
  else
    for (i = 1; i < l; i++) z[i] = Fl_add(x[i], y[i], p);
  return z;
}

void
Flv_add_inplace(GEN x, GEN y, ulong p)
{
  long i, l = lg(x);
  if (p==2)
    for (i = 1; i < l; i++) x[i] ^= y[i];
  else
    for (i = 1; i < l; i++) x[i] = Fl_add(x[i], y[i], p);
}

ulong
Flv_sum(GEN x, ulong p)
{
  long i, l = lg(x);
  ulong s = 0;
  if (p==2)
    for (i = 1; i < l; i++) s ^= x[i];
  else
    for (i = 1; i < l; i++) s = Fl_add(s, x[i], p);
  return s;
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

GEN
Flv_sub(GEN x, GEN y, ulong p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_VECSMALL);
  for (i = 1; i < l; i++) z[i] = Fl_sub(x[i], y[i], p);
  return z;
}

void
Flv_sub_inplace(GEN x, GEN y, ulong p)
{
  long i, l = lg(x);
  for (i = 1; i < l; i++) x[i] = Fl_sub(x[i], y[i], p);
}

/********************************************************************/
/**                                                                **/
/**                           MULTIPLICATION                       **/
/**                                                                **/
/********************************************************************/
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
  Flc_Fl_mul_inplace(x, Fl_inv(y, p), p);
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
ZMrow_ZC_mul_i(GEN x, GEN y, long lx, long i)
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

static GEN
Flm_Flc_mul_i_2(GEN x, GEN y, long lx, long l)
{
  long i,j;
  GEN z = NULL;

  for (j=1; j<lx; j++)
  {
    if (!y[j]) continue;
    if (!z) z = Flv_copy(gel(x,j));
    else for (i = 1; i < l; i++) z[i] ^= coeff(x,i,j);
  }
  if (!z) z = const_vecsmall(l-1, 0);
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
    GEN c = ZMrow_ZC_mul_i(x, y, lx, i);
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
INLINE GEN
F2m_F2c_mul_i(GEN x, GEN y, long lx, long l)
{
  long j;
  GEN z = NULL;

  for (j=1; j<lx; j++)
  {
    if (!F2v_coeff(y,j)) continue;
    if (!z) z = vecsmall_copy(gel(x,j));
    else F2v_add_inplace(z,gel(x,j));
  }
  if (!z) z = zero_F2v(l);
  return z;
}

GEN
FpM_mul(GEN x, GEN y, GEN p)
{
  long j, l, lx=lg(x), ly=lg(y);
  GEN z;
  if (ly==1) return cgetg(1,t_MAT);
  if (lx==1) return zeromat(0, ly-1);
  if (lgefint(p) == 3)
  {
    pari_sp av = avma;
    ulong pp = (ulong)p[2];
    if (pp == 2)
    {
      x = ZM_to_F2m(x);
      y = ZM_to_F2m(y);
      z = F2m_to_ZM(F2m_mul(x,y));
    }
    else
    {
      x = ZM_to_Flm(x, pp);
      y = ZM_to_Flm(y, pp);
      z = Flm_to_ZM(Flm_mul(x,y, pp));
    }
    return gerepileupto(av, z);
  }
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
GEN
F2m_mul(GEN x, GEN y)
{
  long i,j,l,lx=lg(x), ly=lg(y);
  GEN z;
  if (ly==1) return cgetg(1,t_MAT);
  z = cgetg(ly,t_MAT);
  if (lx==1)
  {
    for (i=1; i<ly; i++) gel(z,i) = const_vecsmall(1,0);
    return z;
  }
  l = coeff(x,1,1);
  for (j=1; j<ly; j++) gel(z,j) = F2m_F2c_mul_i(x, gel(y,j), lx, l);
  return z;
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

/* Multiply a line vector by a column and return a scalar (t_INT) */
GEN
FpV_dotproduct(GEN x, GEN y, GEN p)
{
  long i, lx = lg(x);
  pari_sp av;
  GEN c;
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
ulong
F2v_dotproduct(GEN x0, GEN y0)
{
  uGEN x = (uGEN)x0, y = (uGEN)y0;
  long i, lx = lg(x);
  ulong c;
  if (lx == 2) return 0;
  c = x[2] & y[2];
  for (i=3; i<lx; i++) c ^= x[i] & y[i];
  if (BITS_IN_LONG == 64) c ^= c >> 32;
  c ^= c >> 16;
  c ^= c >>  8;
  c ^= c >>  4;
  c ^= c >>  2;
  c ^= c >>  1;
  return c & 1;
}

GEN
FpM_FpC_mul(GEN x, GEN y, GEN p)
{
  long lx = lg(x);
  return lx==1? cgetg(1,t_COL): FpM_FpC_mul_i(x, y, lx, lg(x[1]), p);
}
GEN
Flm_Flc_mul(GEN x, GEN y, ulong p)
{
  long l, lx = lg(x);
  if (lx==1) return cgetg(1,t_VECSMALL);
  l = lg(x[1]);
  if (p==2)
    return Flm_Flc_mul_i_2(x, y, lx, l);
  else if (SMALL_ULONG(p))
    return Flm_Flc_mul_i_SMALL(x, y, lx, l, p);
  else
    return Flm_Flc_mul_i(x, y, lx, l, p);
}
GEN
F2m_F2c_mul(GEN x, GEN y)
{
  long l, lx = lg(x);
  if (lx==1) return cgetg(1,t_VECSMALL);
  l = coeff(x,1,1);
  return F2m_F2c_mul_i(x, y, lx, l);
}
/* RgV_to_RgX(FpM_FpC_mul(x,y,p), v), p != NULL, memory clean */
GEN
FpM_FpC_mul_FpX(GEN x, GEN y, GEN p, long v)
{
  long i, l, lx = lg(x);
  GEN z;
  if (lx==1) return pol_0(v);
  l = lg(x[1]);
  z = new_chunk(l+1);
  for (i=l-1; i; i--)
  {
    pari_sp av = avma;
    GEN p1 = ZMrow_ZC_mul_i(x,y,lx,i);
    p1 = modii(p1, p);
    if (signe(p1))
    {
      if (i != l-1) stackdummy((pari_sp)(z + l+1), (pari_sp)(z + i+2));
      gel(z,i+1) = gerepileuptoint(av, p1);
      break;
    }
    avma = av;
  }
  if (!i) { avma = (pari_sp)(z + l+1); return pol_0(v); }
  z[0] = evaltyp(t_POL) | evallg(i+2);
  z[1] = evalsigne(1) | evalvarn(v);
  for (; i; i--)
  {
    pari_sp av = avma;
    GEN p1 = ZMrow_ZC_mul_i(x,y,lx,i);
    gel(z,i+1) = gerepileuptoint(av, modii(p1,p));
  }
  return z;
}

/********************************************************************/
/**                                                                **/
/**                           TRANSPOSITION                        **/
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

/********************************************************************/
/**                                                                **/
/**                           CONVERSIONS                          **/
/**                                                                **/
/********************************************************************/
GEN
ZV_to_Flv(GEN x, ulong p)
{
  long i, n = lg(x);
  GEN y = cgetg(n,t_VECSMALL);
  for (i=1; i<n; i++) y[i] = umodiu(gel(x,i), p);
  return y;
}
GEN
ZM_to_Flm(GEN x, ulong p)
{
  long j,n = lg(x);
  GEN y = cgetg(n,t_MAT);
  if (n == 1) return y;
  for (j=1; j<n; j++) gel(y,j) = ZV_to_Flv(gel(x,j), p);
  return y;
}

/*                          TO INTMOD                        */
static GEN
to_intmod(GEN x, GEN p) { return mkintmod(modii(x, p), p); }

GEN
Fp_to_mod(GEN z, GEN p)
{
  return mkintmod(modii(z, p), icopy(p));
}

/* z in Z[X], return z * Mod(1,p), normalized*/
GEN
FpX_to_mod(GEN z, GEN p)
{
  long i,l = lg(z);
  GEN x = cgetg(l,t_POL);
  if (l >2) p = icopy(p);
  for (i=2; i<l; i++) gel(x,i) = to_intmod(gel(z,i), p);
  x[1] = z[1]; return normalizepol_lg(x,l);
}

/* z in Z^n, return z * Mod(1,p), normalized*/
GEN
FpV_to_mod(GEN z, GEN p)
{
  long i,l = lg(z);
  GEN x = cgetg(l, t_VEC);
  if (l == 1) return x;
  p = icopy(p);
  for (i=1; i<l; i++) gel(x,i) = to_intmod(gel(z,i), p);
  return x;
}
/* z in Z^n, return z * Mod(1,p), normalized*/
GEN
FpC_to_mod(GEN z, GEN p)
{
  long i, l = lg(z);
  GEN x = cgetg(l, t_COL);
  if (l == 1) return x;
  p = icopy(p);
  for (i=1; i<l; i++) gel(x,i) = to_intmod(gel(z,i), p);
  return x;
}
/* z in Mat m,n(Z), return z * Mod(1,p), normalized*/
GEN
FpM_to_mod(GEN z, GEN p)
{
  long i, j, m, l = lg(z);
  GEN  x = cgetg(l,t_MAT), y, zi;
  if (l == 1) return x;
  m = lg(gel(z,1));
  p = icopy(p);
  for (i=1; i<l; i++)
  {
    gel(x,i) = cgetg(m,t_COL);
    y = gel(x,i); zi= gel(z,i);
    for (j=1; j<m; j++) gel(y,j) = to_intmod(gel(zi,j), p);
  }
  return x;
}

/* z in Z^n, return z * Mod(1,p), normalized*/
GEN
FpXQC_to_mod(GEN z, GEN T, GEN p)
{
  long i,l = lg(z);
  GEN x = cgetg(l, t_COL); T = FpX_to_mod(T, p);
  for (i=1; i<l; i++)
    gel(x,i) = mkpolmod(FpX_to_mod(gel(z,i), p), T);
  return x;
}

/********************************************************************/
/*                                                                  */
/*                     Blackbox linear algebra                      */
/*                                                                  */
/********************************************************************/

/* A sparse column (zCs) v is a t_COL with two components C and E which are
 * t_VECSMALL of the same length, representing sum_i E[i]*e_{C[i]}, where
 * (e_j) is the canonical basis.
 * A sparse matrix (zMs) is a t_VEC of zCs */

/* FpCs and FpMs are identical but E[i] is interpreted as a _signed_ C long
 * integer representing an element of Fp. This is important since p can be
 * large and p+E[i] would not fit in a C long.  */

/* RgCs and RgMs are similar, except that the type of the component is
 * unspecified. Functions handling RgCs/RgMs must be independent of the type
 * of E. */

/* Most functions take an argument nbrow which is the number of lines of the
 * column/matrix, which cannot be derived from the data. */

GEN
zCs_to_ZC(GEN R, long nbrow)
{
  GEN C = gel(R,1), E = gel(R,2), c = zerocol(nbrow);
  long j, l = lg(C);
  for (j = 1; j < l; ++j) gel(c, C[j]) = stoi(E[j]);
  return c;
}

GEN
zMs_to_ZM(GEN M, long nbrow)
{
  long i, l = lg(M);
  GEN m = cgetg(l, t_MAT);
  for (i = 1; i < l; ++i) gel(m,i) = zCs_to_ZC(gel(M,i), nbrow);
  return m;
}

/* Solve equation f(X) = B (mod p) where B is a FpV, and f is an endomorphism.
 * Return either a solution as a t_COL, or a kernel vector as a t_VEC. */
GEN
gen_FpM_Wiedemann(void *E, GEN (*f)(void*, GEN), GEN B, GEN p)
{
  long col = 0, n = lg(B)-1, m = 2*n+1;
  if (ZV_equal0(B)) return zerocol(n);
  while (++col <= n)
  {
    pari_sp ltop = avma, av, lim;
    long i, lQ;
    GEN V, Q, M, W = B;
    GEN b = cgetg(m+2, t_POL);
    b[1] = evalsigne(1)|evalvarn(0);
    gel(b, 2) = gel(W, col);
    for (i = 3; i<m+2; i++)
      gel(b, i) = cgeti(lgefint(p));
    av = avma; lim = stack_lim(av,1);
    for (i = 3; i<m+2; i++)
    {
      W = f(E, W);
      affii(gel(W, col),gel(b, i));
      if (low_stack(lim, stack_lim(av,2)))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"Wiedemann: first loop, %ld",i);
        W = gerepileupto(av, W);
      }
    }
    b = FpX_renormalize(b, m+2);
    if (lgpol(b)==0) {avma = ltop; continue; }
    M = FpX_halfgcd(b, monomial(gen_1, m, 0), p);
    Q = FpX_neg(FpX_normalize(gcoeff(M, 2, 1),p),p);
    W = B; lQ =lg(Q);
    if (DEBUGLEVEL) err_printf("Wiedemann: deg. minpoly: %ld\n",lQ-3);
    V = FpC_Fp_mul(W, gel(Q, lQ-2), p);
    av = avma; lim = stack_lim(av,1);
    for (i = lQ-3; i > 1; i--)
    {
      W = f(E, W);
      V = ZC_lincomb(gen_1, gel(Q,i), V, W);
      if (low_stack(lim, stack_lim(av,2)))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"Wiedemann: second loop, %ld",i);
        gerepileall(av, 2, &V, &W);
      }
    }
    V = FpC_red(V, p);
    W = FpC_sub(f(E,V), B, p);
    if (ZV_equal0(W)) return V;
    av = avma;
    for (i = 1; i <= n; ++i)
    {
      V = W;
      W = f(E, V);
      if (ZV_equal0(W))
        return shallowtrans(V);
      gerepileall(av, 2, &V, &W);
    }
    avma = ltop;
  }
  return NULL;
}

GEN
FpMs_FpC_mul(GEN M, GEN B, GEN p)
{
  long i, j;
  long n = lg(B)-1;
  GEN V = zerocol(n);
  for (i = 1; i <= n; ++i)
    if (signe(gel(B, i)))
    {
      GEN R = gel(M, i), C = gel(R, 1), E = gel(R, 2);
      long l = lg(C);
      for (j = 1; j < l; ++j)
      {
        long k = C[j];
        switch(E[j])
        {
        case 1:
          gel(V, k) = gel(V,k)==gen_0 ? gel(B,i) : addii(gel(V, k), gel(B,i));
          break;
        case -1:
          gel(V, k) = gel(V,k)==gen_0 ? negi(gel(B,i)) : subii(gel(V, k), gel(B,i));
          break;
        default:
          gel(V, k) = gel(V,k)==gen_0 ? mulis(gel(B, i), E[j]) : addii(gel(V, k), mulis(gel(B, i), E[j]));
          break;
        }
      }
    }
  return FpC_red(V,p);
}

struct relcomb_s
{
  GEN M, p;
};

static GEN
wrap_relcomb(void*E, GEN x)
{
  struct relcomb_s *s = (struct relcomb_s *) E;
  return FpMs_FpC_mul(s->M, x, s->p);
}

static GEN
vecprow(GEN A, GEN prow)
{
  return mkvec2(vecpermute(prow,gel(A,1)), gel(A,2));
}

/* Solve the equation MX = A. Return either a solution as a t_COL,
 * or the index of a column which is linearly dependent from the others as a
 * t_VECSMALL with a single component. */
GEN
FpMs_FpCs_solve(GEN M, GEN A, long nbrow, GEN p)
{
  pari_sp av = avma;
  struct relcomb_s s;
  GEN pcol, prow;
  long nbi=lg(M)-1, lR;
  long i, n;
  GEN Mp, Ap, Rp;
  pari_timer ti;
  RgMs_structelim(M, nbrow, gel(A, 1), &pcol, &prow);
  if (DEBUGLEVEL)
    err_printf("Structured elimination: %ld -> %ld\n",nbi,lg(pcol)-1);
  n = lg(pcol)-1;
  Mp = cgetg(n+1, t_MAT);
  for(i=1; i<=n; i++)
    gel(Mp, i) = vecprow(gel(M,pcol[i]), prow);
  Ap = zCs_to_ZC(vecprow(A, prow), n);
  s.M = Mp; s.p = p;
  timer_start(&ti);
  Rp = gen_FpM_Wiedemann((void*)&s,wrap_relcomb, Ap, p);
  if (DEBUGLEVEL) timer_printf(&ti,"linear algebra");
  if (!Rp) { avma = av; return NULL; }
  lR = lg(Rp)-1;
  if (typ(Rp) == t_COL)
  {
    GEN R = zerocol(nbi+1);
    for (i=1; i<=lR; i++)
       gel(R,pcol[i]) = gel(Rp,i);
    return R;
  }
  for (i = 1; i <= lR; ++i)
    if (signe(gel(Rp, i)))
      return mkvecsmall(pcol[i]);
  return NULL; /* NOT REACHED */
}
