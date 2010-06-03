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
  if (p==2)
    return Flm_Flc_mul_i_2(x, y, lx, l);
  else if (SMALL_ULONG(p))
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
  if (!i) { avma = (pari_sp)(z + l+1); return zeropol(v); }
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
