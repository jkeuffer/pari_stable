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

long
RgX_equal(GEN x, GEN y)
{
  long i = lg(x);

  if (i != lg(y)) return 0;
  for (i--; i > 1; i--)
    if (!gequal(gel(x,i),gel(y,i))) return 0;
  return 1;
}
long
RgX_equal_var(GEN x, GEN y) { return varn(x) == varn(y) && RgX_equal(x,y); }


/* Returns 1 in the base ring over which x is defined */
/* HACK: this also works for t_SER */
GEN
RgX_get_1(GEN x)
{
  pari_sp av = avma;
  GEN p, T;
  long i, lx, vx = varn(x), tx = RgX_type(x, &p, &T, &lx);
  if (RgX_type_is_composite(tx))
    RgX_type_decode(tx, &i /*junk*/, &tx);
  switch(tx)
  {
    case t_INTMOD: x = mkintmod(gen_1,p); break;
    case t_PADIC: x = cvtop(gen_1, p, lx); break;
    case t_FFELT: x = FF_1(T); break;
    default: x = gen_1; break;
  }
  return gerepileupto(av, scalarpol(x, vx));
}
/* Returns 0 in the base ring over which x is defined */
/* HACK: this also works for t_SER */
GEN
RgX_get_0(GEN x)
{
  pari_sp av = avma;
  GEN p, T;
  long i, lx, vx = varn(x), tx = RgX_type(x, &p, &T, &lx);
  if (RgX_type_is_composite(tx))
    RgX_type_decode(tx, &i /*junk*/, &tx);
  switch(tx)
  {
    case t_INTMOD: x = mkintmod(gen_0,p); break;
    case t_PADIC: x = cvtop(gen_0, p, lx); break;
    case t_FFELT: x = FF_zero(T); break;
    default: x = gen_0; break;
  }
  return gerepileupto(av, scalarpol(x, vx));
}

/********************************************************************/
/**                                                                **/
/**                         COMPOSITION                            **/
/**                                                                **/
/********************************************************************/

static GEN
RgXQ_eval_powers(GEN P, GEN V, long a, long n)
{
  GEN z = scalarpol(gel(P,2+a), varn(P)); /* V[1] = 1 */
  long i;
  for (i=1; i<=n; i++) z = RgX_add(z, RgX_Rg_mul(gel(V,i+1), gel(P,2+a+i)));
  return z;
}

/* Brent & Kung
 * (Fast algorithms for manipulating formal power series, JACM 25:581-595, 1978)
 *
 * V as output by RgXQ_powers(x,l,T,p). For optimal performance, l is as given
 * by brent_kung_optpow */
GEN
RgX_RgXQV_eval(GEN P, GEN V, GEN T)
{
  pari_sp av = avma, btop;
  long l = lg(V)-1, d = degpol(P);
  GEN z, u;

  if (d < 0) return zeropol(varn(T));
  if (d < l)
  {
    z = RgXQ_eval_powers(P,V,0,d);
    return gerepileupto(av, z);
  }
  if (l<=1) pari_err(talker,"powers is only [] or [1] in RgX_RgXQV_eval");
  d -= l;
  btop = avma;
  z = RgXQ_eval_powers(P,V,d+1,l-1);
  while (d >= l-1)
  {
    d -= l-1;
    u = RgXQ_eval_powers(P,V,d+1,l-2);
    z = RgX_add(u, RgXQ_mul(z, gel(V,l), T));
    z = gerepileupto(btop, z);
  }
  u = RgXQ_eval_powers(P,V,0,d);
  z = RgX_add(u, RgXQ_mul(z, gel(V,d+2), T));
  if (DEBUGLEVEL>=8)
  {
    long cnt = 1 + (degpol(P) - l) / (l-1);
    fprintferr("RgX_RgXQV_eval: %ld RgXQ_mul [%ld]\n", cnt, l-1);
  }
  return gerepileupto(av, z);
}

/* Q in Z[X] and x in Rg[X]/(T). Return a lift of Q(x) */
GEN
RgX_RgXQ_eval(GEN Q, GEN x, GEN T)
{
  pari_sp av = avma;
  GEN z;
  long d = degpol(Q), rtd;
  if (typ(Q)!=t_POL || typ(x)!=t_POL) pari_err(typeer,"RgX_RgXQ_eval");
  if (d < 0) return zeropol(varn(Q));
  rtd = (long) sqrt((double)d);
  z = RgX_RgXQV_eval(Q, RgXQ_powers(x, rtd, T), T);
  return gerepileupto(av, z);
}

GEN
QX_ZXQV_eval(GEN P, GEN V, GEN dV)
{
  long i, n = degpol(P);
  GEN z, dz, dP;
  if (n < 0) return gen_0;
  P = Q_remove_denom(P, &dP);
  z = gel(P,2); if (n == 0) return icopy(z);
  if (dV) z = mulii(dV, z); /* V[1] = dV */
  z = ZX_Z_add(ZX_Z_mul(gel(V,2),gel(P,3)), z);
  for (i=2; i<=n; i++) z = ZX_add(ZX_Z_mul(gel(V,i+1),gel(P,2+i)), z);
  dz = mul_denom(dP, dV);
  return dz? RgX_Rg_div(z, dz): z;
}

/* Return P(h * x), not memory clean */
GEN
RgX_unscale(GEN P, GEN h)
{
  long i, l = lg(P);
  GEN hi = gen_1, Q = cgetg(l, t_POL);
  Q[1] = P[1];
  if (l == 2) return Q;
  gel(Q,2) = gcopy(gel(P,2));
  for (i=3; i<l; i++)
  {
    hi = gmul(hi,h);
    gel(Q,i) = gmul(gel(P,i), hi);
  }
  return Q;
}

GEN
RgXV_unscale(GEN v, GEN h)
{
  long i, l;
  GEN w;
  if (!h) return v;
  w = cgetg_copy(v, &l);
  for (i=1; i<l; i++) gel(w,i) = RgX_unscale(gel(v,i), h);
  return w;
}

/* Return h^degpol(P) P(x / h), not memory clean */
GEN
RgX_rescale(GEN P, GEN h)
{
  long i, l = lg(P);
  GEN Q = cgetg(l,t_POL), hi = h;
  Q[l-1] = P[l-1];
  for (i=l-2; i>=2; i--)
  {
    gel(Q,i) = gmul(gel(P,i), hi);
    if (i == 2) break;
    hi = gmul(hi,h);
  }
  Q[1] = P[1]; return Q;
}

/* A(X^d) --> A(X) */
GEN
RgX_deflate(GEN x0, long d)
{
  GEN z, y, x;
  long i,id, dy, dx = degpol(x0);
  if (d <= 1) return x0;
  if (dx < 0) return zeropol(varn(x0));
  dy = dx/d;
  y = cgetg(dy+3, t_POL); y[1] = x0[1];
  z = y + 2;
  x = x0+ 2;
  for (i=id=0; i<=dy; i++,id+=d) z[i] = x[id];
  return y;
}

/* return x0(X^d) */
GEN
RgX_inflate(GEN x0, long d)
{
  long i, id, dy, dx = degpol(x0);
  GEN x = x0 + 2, z, y;
  dy = dx*d;
  y = cgetg(dy+3, t_POL); y[1] = x0[1];
  z = y + 2;
  for (i=0; i<=dy; i++) gel(z,i) = gen_0;
  for (i=id=0; i<=dx; i++,id+=d) z[id] = x[i];
  return y;
}

/* return P(X + c) using destructive Horner, optimize for c = 1,-1 */
GEN
RgX_translate(GEN P, GEN c)
{
  pari_sp av = avma, lim;
  GEN Q, *R;
  long i, k, n;

  if (!signe(P) || gequal0(c)) return gcopy(P);
  Q = leafcopy(P);
  R = (GEN*)(Q+2); n = degpol(P);
  lim = stack_lim(av, 2);
  if (gequal1(c))
  {
    for (i=1; i<=n; i++)
    {
      for (k=n-i; k<n; k++) R[k] = gadd(R[k], R[k+1]);
      if (low_stack(lim, stack_lim(av,2)))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"TR_POL(1), i = %ld/%ld", i,n);
        Q = gerepilecopy(av, Q); R = (GEN*)Q+2;
      }
    }
  }
  else if (gequalm1(c))
  {
    for (i=1; i<=n; i++)
    {
      for (k=n-i; k<n; k++) R[k] = gsub(R[k], R[k+1]);
      if (low_stack(lim, stack_lim(av,2)))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"TR_POL(-1), i = %ld/%ld", i,n);
        Q = gerepilecopy(av, Q); R = (GEN*)Q+2;
      }
    }
  }
  else
  {
    for (i=1; i<=n; i++)
    {
      for (k=n-i; k<n; k++) R[k] = gadd(R[k], gmul(c, R[k+1]));
      if (low_stack(lim, stack_lim(av,2)))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"TR_POL, i = %ld/%ld", i,n);
        Q = gerepilecopy(av, Q); R = (GEN*)Q+2;
      }
    }
  }
  return gerepilecopy(av, Q);
}
/* return lift( P(X + c) ) using Horner, c in R[y]/(T) */
GEN
RgXQX_translate(GEN P, GEN c, GEN T)
{
  pari_sp av = avma, lim;
  GEN Q, *R;
  long i, k, n;

  if (!signe(P) || gequal0(c)) return gcopy(P);
  Q = leafcopy(P);
  R = (GEN*)(Q+2); n = degpol(P);
  lim = stack_lim(av, 2);
  for (i=1; i<=n; i++)
  {
    for (k=n-i; k<n; k++)
    {
      pari_sp av2 = avma;
      R[k] = gerepileupto(av2, RgX_rem(gadd(R[k], gmul(c, R[k+1])), T));
    }
    if (low_stack(lim, stack_lim(av,2)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"RgXQX_translate, i = %ld/%ld", i,n);
      Q = gerepilecopy(av, Q); R = (GEN*)Q+2;
    }
  }
  return gerepilecopy(av, Q);
}

/********************************************************************/
/**                                                                **/
/**                          CONVERSIONS                           **/
/**                       (not memory clean)                       **/
/**                                                                **/
/********************************************************************/
/* to INT / FRAC / (POLMOD mod T), not memory clean because T not copied */
static GEN
RgXQ_to_mod(GEN x, GEN T)
{
  long d;
  switch(typ(x))
  {
    case t_INT: case t_FRAC:
      return gcopy(x);

    default:
      d = degpol(x);
      if (d < 0) return gen_0;
      if (d == 0) return gcopy(gel(x,2));
      return mkpolmod(gcopy(x), T);
  }
}
/* T a ZX, z lifted from (Q[Y]/(T(Y)))[X], apply RgXQ_to_mod to all coeffs.
 * Not memory clean because T not copied */
static GEN
RgXQX_to_mod(GEN z, GEN T)
{
  long i,l = lg(z);
  GEN x = cgetg(l,t_POL);
  for (i=2; i<l; i++) gel(x,i) = RgXQ_to_mod(gel(z,i), T);
  x[1] = z[1]; return normalizepol_lg(x,l);
}
/* Apply RgXQX_to_mod to all entries. Memory-clean ! */
GEN
QXQXV_to_mod(GEN V, GEN T)
{
  long i, l = lg(V);
  GEN z = cgetg(l, t_VEC); T = ZX_copy(T);
  for (i=1;i<l; i++) gel(z,i) = RgXQX_to_mod(gel(V,i), T);
  return z;
}
/* Apply RgXQ_to_mod to all entries. Memory-clean ! */
GEN
QXQV_to_mod(GEN V, GEN T)
{
  long i, l = lg(V);
  GEN z = cgetg(l, t_VEC); T = ZX_copy(T);
  for (i=1;i<l; i++) gel(z,i) = RgXQ_to_mod(gel(V,i), T);
  return z;
}

GEN
RgX_renormalize(GEN x)
{
  long i, lx = lg(x);
  for (i = lx-1; i>1; i--)
    if (! gequal0(gel(x,i))) break; /* _not_ isexactzero */
  stackdummy((pari_sp)(x + lg(x)), (pari_sp)(x + i+1));
  setlg(x, i+1); setsigne(x, i != 1); return x;
}

GEN
RgV_to_RgX(GEN x, long v)
{
  long i, k = lg(x);
  GEN p;

  while (--k && gequal0(gel(x,k)));
  if (!k) return zeropol(v);
  i = k+2; p = cgetg(i,t_POL);
  p[1] = evalsigne(1) | evalvarn(v);
  x--; for (k=2; k<i; k++) p[k] = x[k];
  return p;
}

/* return the (N-dimensional) vector of coeffs of p */
GEN
RgX_to_RgV(GEN x, long N)
{
  long i, l;
  GEN z = cgetg(N+1,t_COL);
  if (typ(x) != t_POL)
  {
    gel(z,1) = x;
    for (i=2; i<=N; i++) gel(z,i) = gen_0;
    return z;
  }
  l = lg(x)-1; x++;
  for (i=1; i<l ; i++) z[i]=x[i];
  for (   ; i<=N; i++) gel(z,i) = gen_0;
  return z;
}

/* vector of polynomials (in v) whose coeffs are given by the columns of x */
GEN
RgM_to_RgXV(GEN x, long v)
{
  long j, lx = lg(x);
  GEN y = cgetg(lx, t_VEC);
  for (j=1; j<lx; j++) gel(y,j) = RgV_to_RgX(gel(x,j), v);
  return y;
}

/* matrix whose entries are given by the coeffs of the polynomials in
 * vector v (considered as degree n-1 polynomials) */
GEN
RgXV_to_RgM(GEN v, long n)
{
  long j, N = lg(v);
  GEN y = cgetg(N, t_MAT);
  for (j=1; j<N; j++) gel(y,j) = RgX_to_RgV(gel(v,j), n);
  return y;
}

/* polynomial (in v) of polynomials (in w) whose coeffs are given by the columns of x */
GEN
RgM_to_RgXX(GEN x, long v,long w)
{
  long j, lx = lg(x);
  GEN y = cgetg(lx+1, t_POL);
  y[1] = evalsigne(1) | evalvarn(v);
  y++;
  for (j=1; j<lx; j++) gel(y,j) = RgV_to_RgX(gel(x,j), w);
  return normalizepol_lg(--y, lx+1);
}

/* matrix whose entries are given by the coeffs of the polynomial v in
 * two variables (considered as degree n polynomials) */
GEN
RgXX_to_RgM(GEN v, long n)
{
  long j, N = lg(v)-1;
  GEN y = cgetg(N, t_MAT);
  v++;
  for (j=1; j<N; j++) gel(y,j) = RgX_to_RgV(gel(v,j), n);
  return y;
}

/* P(X,Y) --> P(Y,X), n is an upper bound for deg_Y(P) */
GEN
RgXY_swap(GEN x, long n, long w)
{
  long j, lx = lg(x), ly = n+3, v = varn(x);
  GEN y = cgetg(ly, t_POL);
  y[1] = evalsigne(1) | evalvarn(v);
  for (j=2; j<ly; j++)
  {
    long k;
    GEN a = cgetg(lx,t_POL);
    a[1] = evalsigne(1) | evalvarn(w);
    for (k=2; k<lx; k++)
    {
      GEN xk = gel(x,k);
      if (j < lg(xk))
        gel(a,k) = gel(xk,j);
      else
        gel(a,k) = gen_0;
    }
    gel(y,j) = normalizepol_lg(a,lx);
  }
  return normalizepol_lg(y,ly);
}

/* return (x % X^n). Shallow */
GEN
RgX_modXn_shallow(GEN a, long n)
{
  long i, L, l = lg(a);
  GEN  b;
  if (l == 2 || !n) return zeropol(varn(a));
  if (n < 0) pari_err(talker,"n < 0 in RgX_modXn");
  L = n+2; if (L > l) L = l;
  b = cgetg(L, t_POL); b[1] = a[1];
  for (i=2; i<L; i++) gel(b,i) = gel(a,i);
  return b;
}

/* return (x * X^n). Shallow */
GEN
RgX_shift_shallow(GEN a, long n)
{
  long i, l = lg(a);
  GEN  b;
  if (l == 2 || !n) return a;
  l += n;
  if (n < 0)
  {
    if (l <= 2) return zeropol(varn(a));
    b = cgetg(l, t_POL); b[1] = a[1];
    a -= n;
    for (i=2; i<l; i++) gel(b,i) = gel(a,i);
  } else {
    b = cgetg(l, t_POL); b[1] = a[1];
    a -= n; n += 2;
    for (i=2; i<n; i++) gel(b,i) = gen_0;
    for (   ; i<l; i++) gel(b,i) = gel(a,i);
  }
  return b;
}
/* return (x * X^n). */
GEN
RgX_shift(GEN a, long n)
{
  long i, l = lg(a);
  GEN  b;
  if (l == 2 || !n) return gcopy(a);
  l += n;
  if (n < 0)
  {
    if (l <= 2) return zeropol(varn(a));
    b = cgetg(l, t_POL); b[1] = a[1];
    a -= n;
    for (i=2; i<l; i++) gel(b,i) = gcopy(gel(a,i));
  } else {
    b = cgetg(l, t_POL); b[1] = a[1];
    a -= n; n += 2;
    for (i=2; i<n; i++) gel(b,i) = gen_0;
    for (   ; i<l; i++) gel(b,i) = gcopy(gel(a,i));
  }
  return b;
}
GEN
RgX_mulXn(GEN x, long d)
{
  pari_sp av;
  GEN z;
  long v;
  if (d >= 0) return RgX_shift(x, d);
  d = -d;
  v = RgX_val(x);
  if (v >= d) return RgX_shift(x, -d);
  av = avma;
  z = gred_rfrac_simple( RgX_shift(x, -v),
                         monomial(gen_1, d - v, varn(x)));
  return gerepileupto(av, z);
}

long
RgX_val(GEN x)
{
  long i, lx = lg(x);
  if (lx == 2) return LONG_MAX;
  for (i = 2; i < lx; i++)
    if (!isexactzero(gel(x,i))) break;
  if (i == lx) i--; /* possible with non-rational zeros */
  return i - 2;
}
long
RgX_valrem(GEN x, GEN *Z)
{
  long v, i, lx = lg(x);
  if (lx == 2) { *Z = zeropol(varn(x)); return LONG_MAX; }
  for (i = 2; i < lx; i++)
    if (!isexactzero(gel(x,i))) break;
  if (i == lx) i--; /* possible with non-rational zeros */
  v = i - 2;
  *Z = RgX_shift_shallow(x, -v);
  return v;
}
long
RgX_valrem_inexact(GEN x, GEN *Z)
{
  long v;
  if (!signe(x)) { if (Z) *Z = zeropol(varn(x)); return LONG_MAX; }
  for (v = 0;; v++)
    if (!gequal0(gel(x,2+v))) break;
  if (Z) *Z = RgX_shift_shallow(x, -v);
  return v;
}

GEN
RgXQC_red(GEN P, GEN T)
{
  long i, l = lg(P);
  GEN Q = cgetg(l, t_COL);
  for (i=1; i<l; i++) gel(Q,i) = grem(gel(P,i), T);
  return Q;
}

GEN
RgXQV_red(GEN P, GEN T)
{
  long i, l = lg(P);
  GEN Q = cgetg(l, t_VEC);
  for (i=1; i<l; i++) gel(Q,i) = grem(gel(P,i), T);
  return Q;
}

GEN
RgXQX_red(GEN P, GEN T)
{
  long i, l = lg(P);
  GEN Q = cgetg(l, t_POL);
  Q[1] = P[1];
  for (i=2; i<l; i++) gel(Q,i) = grem(gel(P,i), T);
  return normalizepol_lg(Q, l);
}

GEN
RgX_deriv(GEN x)
{
  long i,lx = lg(x)-1;
  GEN y;

  if (lx<3) return zeropol(varn(x));
  y = cgetg(lx,t_POL); gel(y,2) = gcopy(gel(x,3));
  for (i=3; i<lx ; i++) gel(y,i) = gmulsg(i-1,gel(x,i+1));
  y[1] = x[1]; return normalizepol_lg(y,i);
}

/* return coefficients s.t x = x_0 X^n + ... + x_n */
GEN
RgX_recip(GEN x)
{
  long lx, i, j;
  GEN y = cgetg_copy(x, &lx);
  y[1] = x[1]; for (i=2,j=lx-1; i<lx; i++,j--) gel(y,i) = gcopy(gel(x,j));
  return normalizepol_lg(y,lx);
}
/* shallow version */
GEN
RgX_recip_shallow(GEN x)
{
  long lx, i, j;
  GEN y = cgetg_copy(x, &lx);
  y[1] = x[1]; for (i=2,j=lx-1; i<lx; i++,j--) y[i] = x[j];
  return y;
}
/*******************************************************************/
/*                                                                 */
/*                      ADDITION / SUBTRACTION                     */
/*                                                                 */
/*******************************************************************/
/* same variable */
GEN
RgX_add(GEN x, GEN y)
{
  long i, lx = lg(x), ly = lg(y);
  GEN z;
  if (lx == ly) {
    z = cgetg(lx, t_POL); z[1] = x[1];
    for (i=2; i < lx; i++) gel(z,i) = gadd(gel(x,i),gel(y,i));
    return normalizepol_lg(z, lx);
  }
  if (ly < lx) {
    z = cgetg(lx,t_POL); z[1] = x[1];
    for (i=2; i < ly; i++) gel(z,i) = gadd(gel(x,i),gel(y,i));
    for (   ; i < lx; i++) gel(z,i) = gcopy(gel(x,i));
    if (!signe(x)) z = normalizepol_lg(z, lx);
  } else {
    z = cgetg(ly,t_POL); z[1] = y[1];
    for (i=2; i < lx; i++) gel(z,i) = gadd(gel(x,i),gel(y,i));
    for (   ; i < ly; i++) gel(z,i) = gcopy(gel(y,i));
    if (!signe(y)) z = normalizepol_lg(z, ly);
  }
  return z;
}
GEN
RgX_sub(GEN x, GEN y)
{
  long i, lx = lg(x), ly = lg(y);
  GEN z;
  if (lx == ly) {
    z = cgetg(lx, t_POL); z[1] = x[1];
    for (i=2; i < lx; i++) gel(z,i) = gsub(gel(x,i),gel(y,i));
    return normalizepol_lg(z, lx);
  }
  if (ly < lx) {
    z = cgetg(lx,t_POL); z[1] = x[1];
    for (i=2; i < ly; i++) gel(z,i) = gsub(gel(x,i),gel(y,i));
    for (   ; i < lx; i++) gel(z,i) = gcopy(gel(x,i));
    if (!signe(x)) z = normalizepol_lg(z, lx);
  } else {
    z = cgetg(ly,t_POL); z[1] = y[1];
    for (i=2; i < lx; i++) gel(z,i) = gsub(gel(x,i),gel(y,i));
    for (   ; i < ly; i++) gel(z,i) = gneg(gel(y,i));
    if (!signe(y)) z = normalizepol_lg(z, ly);
  }
  return z;
}
GEN
RgX_neg(GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx, t_POL); y[1] = x[1];
  for (i=2; i<lx; i++) gel(y,i) = gneg(gel(x,i));
  return y;
}

GEN
RgX_Rg_add(GEN y, GEN x)
{
  GEN z;
  long lz = lg(y), i;
  if (lz == 2) return scalarpol(x,varn(y));
  z = cgetg(lz,t_POL); z[1] = y[1];
  gel(z,2) = gadd(gel(y,2),x);
  for(i=3; i<lz; i++) gel(z,i) = gcopy(gel(y,i));
  if (lz==3) z = normalizepol_lg(z,lz);
  return z;
}
GEN
RgX_Rg_add_shallow(GEN y, GEN x)
{
  GEN z;
  long lz = lg(y), i;
  if (lz == 2) return scalarpol(x,varn(y));
  z = cgetg(lz,t_POL); z[1] = y[1];
  gel(z,2) = gadd(gel(y,2),x);
  for(i=3; i<lz; i++) gel(z,i) = gel(y,i);
  if (lz==3) z = normalizepol_lg(z,lz);
  return z;
}
GEN
RgX_Rg_sub(GEN y, GEN x)
{
  GEN z;
  long lz = lg(y), i;
  if (lz == 2)
  { /* scalarpol(gneg(x),varn(y)) optimized */
    long v = varn(y);
    if (isrationalzero(x)) return zeropol(v);
    z = cgetg(3,t_POL);
    z[1] = gequal0(x)? evalvarn(v)
                   : evalvarn(v) | evalsigne(1);
    gel(z,2) = gneg(x); return z;
  }
  z = cgetg(lz,t_POL); z[1] = y[1];
  gel(z,2) = gsub(gel(y,2),x);
  for(i=3; i<lz; i++) gel(z,i) = gcopy(gel(y,i));
  if (lz==3) z = normalizepol_lg(z,lz);
  return z;
}
GEN
Rg_RgX_sub(GEN x, GEN y)
{
  GEN z;
  long lz = lg(y), i;
  if (lz == 2) return scalarpol(x,varn(y));
  z = cgetg(lz,t_POL); z[1] = y[1];
  gel(z,2) = gsub(x, gel(y,2));
  for(i=3; i<lz; i++) gel(z,i) = gneg(gel(y,i));
  if (lz==3) z = normalizepol_lg(z,lz);
  return z;
}
/*******************************************************************/
/*                                                                 */
/*                  KARATSUBA MULTIPLICATION                       */
/*                                                                 */
/*******************************************************************/
#if 0
/* to debug Karatsuba-like routines */
GEN
zx_debug_spec(GEN x, long nx)
{
  GEN z = cgetg(nx+2,t_POL);
  long i;
  for (i=0; i<nx; i++) gel(z,i+2) = stoi(x[i]);
  z[1] = evalsigne(1); return z;
}

GEN
RgX_debug_spec(GEN x, long nx)
{
  GEN z = cgetg(nx+2,t_POL);
  long i;
  for (i=0; i<nx; i++) z[i+2] = x[i];
  z[1] = evalsigne(1); return z;
}
#endif

/* generic multiplication */

static GEN
addpol(GEN x, GEN y, long lx, long ly)
{
  long i,lz;
  GEN z;

  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx+2; z = cgetg(lz,t_POL) + 2;
  for (i=0; i<ly; i++) gel(z,i) = gadd(gel(x,i),gel(y,i));
  for (   ; i<lx; i++) z[i]=x[i];
  z -= 2; z[1]=0; return normalizepol_lg(z, lz);
}

static GEN
addpolcopy(GEN x, GEN y, long lx, long ly)
{
  long i,lz;
  GEN z;

  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx+2; z = cgetg(lz,t_POL) + 2;
  for (i=0; i<ly; i++) gel(z,i) = gadd(gel(x,i),gel(y,i));
  for (   ; i<lx; i++) gel(z,i) = gcopy(gel(x,i));
  z -= 2; z[1]=0; return normalizepol_lg(z, lz);
}

INLINE GEN
RgX_mulspec_basecase_limb(GEN x, GEN y, long a, long b)
{
  pari_sp av = avma;
  GEN s = NULL;
  long i;

  for (i=a; i<b; i++)
  {
    GEN t = gmul(gel(y,i), gel(x,-i));
    s = s? gadd(s, t): t;
  }
  return s? gerepileupto(av, s): gen_0;
}

/* assume nx >= ny > 0, return x * y * t^v */
static GEN
RgX_mulspec_basecase(GEN x, GEN y, long nx, long ny, long v)
{
  long i, lz, nz;
  GEN z;

  lz = nx + ny + 1; nz = lz-2;
  lz += v;
  z = cgetg(lz, t_POL) + 2; /* x:y:z [i] = term of degree i */
  for (i=0; i<v; i++) gel(z++, 0) = gen_0;
  for (i=0; i<ny; i++)gel(z,i) = RgX_mulspec_basecase_limb(x+i,y, 0, i+1);
  for (  ; i<nx; i++) gel(z,i) = RgX_mulspec_basecase_limb(x+i,y, 0,ny);
  for (  ; i<nz; i++) gel(z,i) = RgX_mulspec_basecase_limb(x+i,y, i-nx+1,ny);
  z -= v+2; z[1] = 0; return normalizepol_lg(z, lz);
}

/* return (x * X^d) + y. Assume d > 0, y != 0 */
GEN
addmulXn(GEN x, GEN y, long d)
{
  GEN xd, yd, zd;
  long a, lz, nx, ny;

  if (!signe(x)) return y;
  ny = lgpol(y);
  nx = lgpol(x);
  zd = (GEN)avma;
  x += 2; y += 2; a = ny-d;
  if (a <= 0)
  {
    lz = (a>nx)? ny+2: nx+d+2;
    (void)new_chunk(lz); xd = x+nx; yd = y+ny;
    while (xd > x) gel(--zd,0) = gel(--xd,0);
    x = zd + a;
    while (zd > x) gel(--zd,0) = gen_0;
  }
  else
  {
    xd = new_chunk(d); yd = y+d;
    x = addpol(x,yd, nx,a);
    lz = (a>nx)? ny+2: lg(x)+d;
    x += 2; while (xd > x) *--zd = *--xd;
  }
  while (yd > y) *--zd = *--yd;
  *--zd = evalsigne(1);
  *--zd = evaltyp(t_POL) | evallg(lz); return zd;
}

GEN
addshiftpol(GEN x, GEN y, long d)
{
  long v = varn(x);
  x = addmulXn(x,y,d);
  setvarn(x,v); return x;
}

/* as above, producing a clean malloc */
static GEN
addmulXncopy(GEN x, GEN y, long d)
{
  GEN xd, yd, zd;
  long a, lz, nx, ny;

  if (!signe(x)) return gcopy(y);
  nx = lgpol(x);
  ny = lgpol(y);
  zd = (GEN)avma;
  x += 2; y += 2; a = ny-d;
  if (a <= 0)
  {
    lz = nx+d+2;
    (void)new_chunk(lz); xd = x+nx; yd = y+ny;
    while (xd > x) gel(--zd,0) = gcopy(gel(--xd,0));
    x = zd + a;
    while (zd > x) gel(--zd,0) = gen_0;
  }
  else
  {
    xd = new_chunk(d); yd = y+d;
    x = addpolcopy(x,yd, nx,a);
    lz = (a>nx)? ny+2: lg(x)+d;
    x += 2; while (xd > x) *--zd = *--xd;
  }
  while (yd > y) gel(--zd,0) = gcopy(gel(--yd,0));
  *--zd = evalsigne(1);
  *--zd = evaltyp(t_POL) | evallg(lz); return zd;
}

/* fast product (Karatsuba) of polynomials a,b. These are not real GENs, a+2,
 * b+2 were sent instead. na, nb = number of terms of a, b.
 * Only c, c0, c1, c2 are genuine GEN.
 */
GEN
RgX_mulspec(GEN a, GEN b, long na, long nb)
{
  GEN a0, c, c0;
  long n0, n0a, i, v = 0;
  pari_sp av;

  while (na && isrationalzero(gel(a,0))) { a++; na--; v++; }
  while (nb && isrationalzero(gel(b,0))) { b++; nb--; v++; }
  if (na < nb) swapspec(a,b, na,nb);
  if (!nb) return zeropol(0);

  if (nb < RgX_MUL_LIMIT) return RgX_mulspec_basecase(a,b,na,nb, v);
  RgX_shift_inplace_init(v);
  i = (na>>1); n0 = na-i; na = i;
  av = avma; a0 = a+n0; n0a = n0;
  while (n0a && isrationalzero(gel(a,n0a-1))) n0a--;

  if (nb > n0)
  {
    GEN b0,c1,c2;
    long n0b;

    nb -= n0; b0 = b+n0; n0b = n0;
    while (n0b && isrationalzero(gel(b,n0b-1))) n0b--;
    c = RgX_mulspec(a,b,n0a,n0b);
    c0 = RgX_mulspec(a0,b0, na,nb);

    c2 = addpol(a0,a, na,n0a);
    c1 = addpol(b0,b, nb,n0b);

    c1 = RgX_mulspec(c1+2,c2+2, lgpol(c1),lgpol(c2));
    c2 = RgX_sub(c1, RgX_add(c0,c));
    c0 = addmulXn(c0, c2, n0);
  }
  else
  {
    c = RgX_mulspec(a,b,n0a,nb);
    c0 = RgX_mulspec(a0,b,na,nb);
  }
  c0 = addmulXncopy(c0,c,n0);
  return RgX_shift_inplace(gerepileupto(av,c0), v);
}

INLINE GEN
RgX_sqrspec_basecase_limb(GEN x, long a, long i)
{
  pari_sp av = avma;
  GEN s = NULL;
  long j, l = (i+1)>>1;
  for (j=a; j<l; j++)
  {
    GEN xj = gel(x,j), xx = gel(x,i-j);
    if (xj && xx)
    {
      GEN t = gmul(xj, xx);
      s = s? gadd(s, t): t;
    }
  }
  if (s) s = gshift(s,1);
  if ((i&1) == 0)
  {
    GEN t = gel(x, i>>1);
    if (t) {
      t = gsqr(t);
      s = s? gadd(s, t): t;
    }
  }
  return s? gerepileupto(av,s): gen_0;
}
static GEN
RgX_sqrspec_basecase(GEN x, long nx, long v)
{
  long i, lz, nz;
  GEN z;

  if (!nx) return zeropol(0);
  lz = (nx << 1) + 1, nz = lz-2;
  lz += v;
  z = cgetg(lz,t_POL) + 2;
  for (i=0; i<v; i++) gel(z++, 0) = gen_0;
  for (i=0; i<nx; i++)gel(z,i) = RgX_sqrspec_basecase_limb(x, 0, i);
  for (  ; i<nz; i++) gel(z,i) = RgX_sqrspec_basecase_limb(x, i-nx+1, i);
  z -= v+2; z[1] = 0; return normalizepol_lg(z, lz);
}

GEN
RgX_sqrspec(GEN a, long na)
{
  GEN a0, c, c0, c1;
  long n0, n0a, i, v = 0;
  pari_sp av;

  while (na && isrationalzero(gel(a,0))) { a++; na--; v += 2; }
  if (na<RgX_SQR_LIMIT) return RgX_sqrspec_basecase(a, na, v);
  RgX_shift_inplace_init(v);
  i = (na>>1); n0 = na-i; na = i;
  av = avma; a0 = a+n0; n0a = n0;
  while (n0a && isrationalzero(gel(a,n0a-1))) n0a--;

  c = RgX_sqrspec(a,n0a);
  c0 = RgX_sqrspec(a0,na);
  c1 = gmul2n(RgX_mulspec(a0,a, na,n0a), 1);
  c0 = addmulXn(c0,c1, n0);
  c0 = addmulXncopy(c0,c,n0);
  return RgX_shift_inplace(gerepileupto(av,c0), v);
}

GEN
RgX_mul(GEN x, GEN y)
{
  GEN z = RgX_mulspec(y+2, x+2, lgpol(y), lgpol(x));
  setvarn(z,varn(x)); return z;
}

GEN
RgX_sqr(GEN x)
{
  GEN z = RgX_sqrspec(x+2, lgpol(x));
  setvarn(z,varn(x)); return z;
}

/*******************************************************************/
/*                                                                 */
/*                               DIVISION                          */
/*                                                                 */
/*******************************************************************/
GEN
RgX_Rg_divexact(GEN x, GEN y) {
  long i, lx;
  GEN z;
  if (typ(y) == t_INT && is_pm1(y))
    return signe(y) < 0 ? RgX_neg(x): gcopy(x);
  z = cgetg_copy(x, &lx); z[1] = x[1];
  for (i=2; i<lx; i++) gel(z,i) = gdivexact(gel(x,i),y);
  return z;
}
GEN
RgX_Rg_div(GEN x, GEN y) {
  long i, lx;
  GEN z = cgetg_copy(x, &lx); z[1] = x[1];
  for (i=2; i<lx; i++) gel(z,i) = gdiv(gel(x,i),y);
  return normalizepol_lg(z, lx);
}
GEN
RgX_divs(GEN x, long y) {
  long i, lx;
  GEN z = cgetg_copy(x, &lx); z[1] = x[1];
  for (i=2; i<lx; i++) gel(z,i) = gdivgs(gel(x,i),y);
  return normalizepol_lg(z, lx);
}
GEN
RgX_div_by_X_x(GEN a, GEN x, GEN *r)
{
  long l = lg(a), i;
  GEN a0, z0, z = cgetg(l-1, t_POL);
  z[1] = a[1];
  a0 = a + l-1;
  z0 = z + l-2; *z0 = *a0--;
  for (i=l-3; i>1; i--) /* z[i] = a[i+1] + x*z[i+1] */
  {
    GEN t = gadd(gel(a0--,0), gmul(x, gel(z0--,0)));
    gel(z0,0) = t;
  }
  if (r) *r = gadd(gel(a0,0), gmul(x, gel(z0,0)));
  return z;
}
/* Polynomial division x / y:
 *   if z = ONLY_REM  return remainder, otherwise return quotient
 *   if z != NULL set *z to remainder
 *   *z is the last object on stack (and thus can be disposed of with cgiv
 *   instead of gerepile) */
/* assume, typ(x) = typ(y) = t_POL, same variable */
GEN
RgX_divrem(GEN x, GEN y, GEN *pr)
{
  pari_sp avy, av, av1;
  long dx,dy,dz,i,j,sx,lr;
  GEN z,p1,p2,rem,y_lead,mod;
  GEN (*f)(GEN,GEN);

  if (!signe(y)) pari_err(gdiver);

  dy = degpol(y);
  y_lead = gel(y,dy+2);
  if (gequal0(y_lead)) /* normalize denominator if leading term is 0 */
  {
    pari_warn(warner,"normalizing a polynomial with 0 leading term");
    for (dy--; dy>=0; dy--)
    {
      y_lead = gel(y,dy+2);
      if (!gequal0(y_lead)) break;
    }
  }
  if (!dy) /* y is constant */
  {
    if (pr && pr != ONLY_DIVIDES)
    {
      if (pr == ONLY_REM) return zeropol(varn(x));
      *pr = zeropol(varn(x));
    }
    return RgX_Rg_div(x, y_lead);
  }
  dx = degpol(x);
  if (dx < dy)
  {
    if (pr)
    {
      if (pr == ONLY_DIVIDES) return gequal0(x)? gen_0: NULL;
      if (pr == ONLY_REM) return gcopy(x);
      *pr = gcopy(x);
    }
    return zeropol(varn(x));
  }

  /* x,y in R[X], y non constant */
  av = avma;
  switch(typ(y_lead))
  {
    case t_REAL:
      y_lead = ginv(y_lead);
      f = gmul; mod = NULL;
      break;
    case t_INTMOD:
    case t_POLMOD: y_lead = ginv(y_lead);
      f = gmul; mod = gmodulo(gen_1, gel(y_lead,1));
      break;
    default: if (gequal1(y_lead)) y_lead = NULL;
      f = gdiv; mod = NULL;
  }

  if (y_lead == NULL)
    p2 = gel(x,dx+2);
  else {
    for(;;) {
      p2 = f(gel(x,dx+2),y_lead);
      if (!isexactzero(p2) || (--dx < 0)) break;
    }
    if (dx < 0) /* x was in fact zero */
    {
      if (pr == ONLY_DIVIDES) return gen_0;
      x = gerepileupto(av, p2);
      if (pr)
      {
        if (pr == ONLY_REM) return x;
        *pr = x;
      }
      return x;
    }
  }
  avy = avma;
  dz = dx-dy;
  z = cgetg(dz+3,t_POL); z[1] = x[1];
  x += 2;
  z += 2;
  y += 2;
  gel(z,dz) = gcopy(p2);

  for (i=dx-1; i>=dy; i--)
  {
    av1=avma; p1=gel(x,i);
    for (j=i-dy+1; j<=i && j<=dz; j++) p1 = gsub(p1, gmul(gel(z,j),gel(y,i-j)));
    if (y_lead) p1 = f(p1,y_lead);

    if (isrationalzero(p1)) { avma=av1; p1 = gen_0; }
    else
      p1 = avma==av1? gcopy(p1): gerepileupto(av1,p1);
    gel(z,i-dy) = p1;
  }
  if (!pr) return gerepileupto(av,z-2);

  rem = (GEN)avma; av1 = (pari_sp)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = gel(x,i);
    /* we always enter this loop at least once */
    for (j=0; j<=i && j<=dz; j++) p1 = gsub(p1, gmul(gel(z,j),gel(y,i-j)));
    if (mod && avma==av1) p1 = gmul(p1,mod);
    if (!gequal0(p1)) { sx = 1; break; } /* remainder is non-zero */
    if (!isexactzero(p1)) break;
    if (!i) break;
    avma=av1;
  }
  if (pr == ONLY_DIVIDES)
  {
    if (sx) { avma=av; return NULL; }
    avma = (pari_sp)rem;
    return gerepileupto(av,z-2);
  }
  lr=i+3; rem -= lr;
  if (avma==av1) { avma = (pari_sp)rem; p1 = gcopy(p1); }
  else p1 = gerepileupto((pari_sp)rem,p1);
  rem[0] = evaltyp(t_POL) | evallg(lr);
  rem[1] = z[-1];
  rem += 2;
  gel(rem,i) = p1;
  for (i--; i>=0; i--)
  {
    av1=avma; p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++) p1 = gsub(p1, gmul(gel(z,j),gel(y,i-j)));
    if (mod && avma==av1) p1 = gmul(p1,mod);
    gel(rem,i) = avma==av1? gcopy(p1):gerepileupto(av1,p1);
  }
  rem -= 2;
  if (!sx) (void)normalizepol_lg(rem, lr);
  if (pr == ONLY_REM) return gerepileupto(av,rem);
  z -= 2;
  {
    GEN *gptr[2]; gptr[0]=&z; gptr[1]=&rem;
    gerepilemanysp(av,avy,gptr,2); *pr = rem; return z;
  }
}

/* x and y in (R[Y]/T)[X]  (lifted), T in R[Y]. y preferably monic */
GEN
RgXQX_divrem(GEN x, GEN y, GEN T, GEN *pr)
{
  long vx, dx, dy, dz, i, j, sx, lr;
  pari_sp av0, av, tetpil;
  GEN z,p1,rem,lead;

  if (!signe(y)) pari_err(gdiver);
  vx = varn(x);
  dx = degpol(x);
  dy = degpol(y);
  if (dx < dy)
  {
    if (pr)
    {
      av0 = avma; x = RgXQX_red(x, T);
      if (pr == ONLY_DIVIDES) { avma=av0; return signe(x)? NULL: gen_0; }
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
    if (gequal1(lead)) return gcopy(x);
    av0 = avma; x = gmul(x, ginvmod(lead,T)); tetpil = avma;
    return gerepile(av0,tetpil,RgXQX_red(x,T));
  }
  av0 = avma; dz = dx-dy;
  lead = gequal1(lead)? NULL: gclone(ginvmod(lead,T));
  avma = av0;
  z = cgetg(dz+3,t_POL); z[1] = x[1];
  x += 2; y += 2; z += 2;

  p1 = gel(x,dx); av = avma;
  gel(z,dz) = lead? gerepileupto(av, grem(gmul(p1,lead), T)): gcopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av=avma; p1=gel(x,i);
    for (j=i-dy+1; j<=i && j<=dz; j++) p1 = gsub(p1, gmul(gel(z,j),gel(y,i-j)));
    if (lead) p1 = gmul(grem(p1, T), lead);
    tetpil=avma; gel(z,i-dy) = gerepile(av,tetpil, grem(p1, T));
  }
  if (!pr) { if (lead) gunclone(lead); return z-2; }

  rem = (GEN)avma; av = (pari_sp)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++) p1 = gsub(p1, gmul(gel(z,j),gel(y,i-j)));
    tetpil=avma; p1 = grem(p1, T); if (!gequal0(p1)) { sx = 1; break; }
    if (!i) break;
    avma=av;
  }
  if (pr == ONLY_DIVIDES)
  {
    if (lead) gunclone(lead);
    if (sx) { avma=av0; return NULL; }
    avma = (pari_sp)rem; return z-2;
  }
  lr=i+3; rem -= lr;
  rem[0] = evaltyp(t_POL) | evallg(lr);
  rem[1] = z[-1];
  p1 = gerepile((pari_sp)rem,tetpil,p1);
  rem += 2; gel(rem,i) = p1;
  for (i--; i>=0; i--)
  {
    av=avma; p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++)
      p1 = gsub(p1, gmul(gel(z,j),gel(y,i-j)));
    tetpil=avma; gel(rem,i) = gerepile(av,tetpil, grem(p1, T));
  }
  rem -= 2;
  if (lead) gunclone(lead);
  if (!sx) (void)normalizepol_lg(rem, lr);
  if (pr == ONLY_REM) return gerepileupto(av0,rem);
  *pr = rem; return z-2;
}

/*******************************************************************/
/*                                                                 */
/*                        PSEUDO-DIVISION                          */
/*                                                                 */
/*******************************************************************/
INLINE GEN
rem(GEN c, GEN T)
{
  if (T && typ(c) == t_POL && varn(c) == varn(T)) c = RgX_rem(c, T);
  return c;
}

/* assume dx >= dy, y non constant, T either NULL or a t_POL. */
GEN
RgXQX_pseudorem(GEN x, GEN y, GEN T)
{
  long vx = varn(x), dx, dy, dz, i, lx, p;
  pari_sp av = avma, av2, lim;
  GEN y_lead;

  if (!signe(y)) pari_err(gdiver);
  dy = degpol(y); y_lead = gel(y,dy+2);
  /* if monic, no point in using pseudo-division */
  if (gequal1(y_lead)) return T? RgXQX_rem(x, y, T): RgX_rem(x, y);
  (void)new_chunk(2);
  dx = degpol(x);
  x = RgX_recip_shallow(x)+2;
  y = RgX_recip_shallow(y)+2;
  /* pay attention to sparse divisors */
  for (i = 1; i <= dy; i++)
    if (isexactzero(gel(y,i))) gel(y,i) = NULL;
  dz = dx-dy; p = dz+1;
  av2 = avma; lim = stack_lim(av2,1);
  for (;;)
  {
    gel(x,0) = gneg(gel(x,0)); p--;
    for (i=1; i<=dy; i++)
    {
      GEN c = gmul(y_lead, gel(x,i));
      if (gel(y,i)) c = gadd(c, gmul(gel(x,0),gel(y,i)));
      gel(x,i) = rem(c, T);
    }
    for (   ; i<=dx; i++)
    {
      GEN c = gmul(y_lead, gel(x,i));
      gel(x,i) = rem(c, T);
    }
    do { x++; dx--; } while (dx >= 0 && gequal0(gel(x,0)));
    if (dx < dy) break;
    if (low_stack(lim,stack_lim(av2,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"RgX_pseudorem dx = %ld >= %ld",dx,dy);
      gerepilecoeffs(av2,x,dx+1);
    }
  }
  if (dx < 0) return zeropol(vx);
  lx = dx+3; x -= 2;
  x[0] = evaltyp(t_POL) | evallg(lx);
  x[1] = evalsigne(1) | evalvarn(vx);
  x = RgX_recip_shallow(x);
  if (p)
  { /* multiply by y[0]^p   [beware dummy vars from FpX_FpXY_resultant] */
    GEN t = y_lead;
    if (T && typ(t) == t_POL && varn(t) == varn(T))
      t = RgXQ_powu(t, p, T);
    else
      t = gpowgs(t, p);
    for (i=2; i<lx; i++)
    {
      GEN c = gmul(gel(x,i), t);
      gel(x,i) = rem(c,T);
    }
    if (!T) return gerepileupto(av, x);
  }
  return gerepilecopy(av, x);
}

GEN
RgX_pseudorem(GEN x, GEN y) { return RgXQX_pseudorem(x,y, NULL); }

/* assume dx >= dy, y non constant
 * Compute z,r s.t lc(y)^(dx-dy+1) x = z y + r */
GEN
RgXQX_pseudodivrem(GEN x, GEN y, GEN T, GEN *ptr)
{
  long vx = varn(x), dx, dy, dz, i, iz, lx, lz, p;
  pari_sp av = avma, av2, lim;
  GEN z, r, ypow, y_lead;

  if (!signe(y)) pari_err(gdiver);
  dy = degpol(y); y_lead = gel(y,dy+2);
  if (gequal1(y_lead)) return T? RgXQX_divrem(x,y, T, ptr): RgX_divrem(x,y, ptr);
  (void)new_chunk(2);
  dx = degpol(x);
  x = RgX_recip_shallow(x)+2;
  y = RgX_recip_shallow(y)+2;
  /* pay attention to sparse divisors */
  for (i = 1; i <= dy; i++)
    if (isexactzero(gel(y,i))) gel(y,i) = NULL;
  dz = dx-dy; p = dz+1;
  lz = dz+3; z = cgetg(lz, t_POL) + 2;
  ypow = new_chunk(dz+1);
  gel(ypow,0) = gen_1;
  gel(ypow,1) = y_lead;
  for (i=2; i<=dz; i++)
  {
    GEN c = gmul(gel(ypow,i-1), y_lead);
    gel(ypow,i) = rem(c,T);
  }
  av2 = avma; lim = stack_lim(av2,1);
  for (iz=0;;)
  {
    p--;
    gel(z,iz++) = rem(gmul(gel(x,0), gel(ypow,p)), T);
    for (i=1; i<=dy; i++)
    {
      GEN c = gmul(y_lead, gel(x,i));
      if (gel(y,i)) c = gsub(c, gmul(gel(x,0),gel(y,i)));
      gel(x,i) = rem(c, T);
    }
    for (   ; i<=dx; i++)
    {
      GEN c = gmul(y_lead, gel(x,i));
      gel(x,i) = rem(c,T);
    }
    x++; dx--;
    while (dx >= dy && gequal0(gel(x,0))) { x++; dx--; gel(z,iz++) = gen_0; }
    if (dx < dy) break;
    if (low_stack(lim,stack_lim(av2,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"RgX_pseudodivrem dx = %ld >= %ld",dx,dy);
      gerepilecoeffs2(av2,x,dx+1, z,iz);
    }
  }
  while (dx >= 0 && gequal0(gel(x,0))) { x++; dx--; }
  if (dx < 0)
    x = zeropol(vx);
  else
  {
    lx = dx+3; x -= 2;
    x[0] = evaltyp(t_POL) | evallg(lx);
    x[1] = evalsigne(1) | evalvarn(vx);
    x = RgX_recip_shallow(x);
  }

  z -= 2;
  z[0] = evaltyp(t_POL) | evallg(lz);
  z[1] = evalsigne(1) | evalvarn(vx);
  z = RgX_recip_shallow(z);
  r = x;
  if (p)
  {
    GEN c = gel(ypow,p); r = RgX_Rg_mul(r, c);
    if (T && typ(c) == t_POL && varn(c) == varn(T)) r = RgXQX_red(r, T);
  }
  gerepileall(av, 2, &z, &r);
  *ptr = r; return z;
}
GEN
RgX_pseudodivrem(GEN x, GEN y, GEN *ptr)
{ return RgXQX_pseudodivrem(x,y,NULL,ptr); }

GEN
RgXQX_mul(GEN x, GEN y, GEN T)
{
  return RgXQX_red(RgX_mul(x,y), T);
}
GEN
RgX_Rg_mul(GEN y, GEN x) {
  long i, ly;
  GEN z;
  if (isrationalzero(x)) return zeropol(varn(y));
  z = cgetg_copy(y, &ly); z[1] = y[1];
  if (ly == 2) return z;
  for (i = 2; i < ly; i++) gel(z,i) = gmul(x,gel(y,i));
  return normalizepol_lg(z,ly);
}
GEN
RgX_muls(GEN y, long x) {
  long i, ly;
  GEN z;
  if (!x) return zeropol(varn(y));
  z = cgetg_copy(y, &ly); z[1] = y[1];
  if (ly == 2) return z;
  for (i = 2; i < ly; i++) gel(z,i) = gmulsg(x,gel(y,i));
  return normalizepol_lg(z,ly);
}
GEN
RgXQX_RgXQ_mul(GEN x, GEN y, GEN T)
{
  return RgXQX_red(RgX_Rg_mul(x,y), T);
}
GEN
RgXQX_sqr(GEN x, GEN T)
{
  return RgXQX_red(RgX_sqr(x), T);
}

static GEN
_sqr(void *data, GEN x) { return RgXQ_sqr(x, (GEN)data); }
static GEN
_mul(void *data, GEN x, GEN y) { return RgXQ_mul(x,y, (GEN)data); }

/* x,T in Rg[X], n in N, compute lift(x^n mod T)) */
GEN
RgXQ_powu(GEN x, ulong n, GEN T)
{
  pari_sp av;
  GEN y;

  if (!n) return pol_1(varn(x));
  if (n == 1) return gcopy(x);
  av = avma;
  y = gen_powu(x, n, (void*)T, &_sqr, &_mul);
  return gerepileupto(av, y);
}
/* x,T in Rg[X], n in N, compute lift(x^n mod T)) */
GEN
RgXQ_pow(GEN x, GEN n, GEN T)
{
  pari_sp av;
  long s = signe(n);
  GEN y;

  if (!s) return pol_1(varn(x));
  if (is_pm1(n) == 1)
    return (s < 0)? RgXQ_inv(x, T): gcopy(x);
  av = avma;
  if (s < 0) x = RgXQ_inv(x, T);
  y = gen_pow(x, n, (void*)T, &_sqr, &_mul);
  return gerepileupto(av, y);
}

/* generates the list of powers of x of degree 0,1,2,...,l*/
GEN
RgXQ_powers(GEN x, long l, GEN T)
{
  GEN V=cgetg(l+2,t_VEC);
  long i;
  gel(V,1) = pol_1(varn(T)); if (l==0) return V;
  gel(V,2) = gcopy(x);       if (l==1) return V;
  gel(V,3) = RgXQ_sqr(x,T);
  if ((degpol(x)<<1) < degpol(T)) {
    for(i = 4; i < l+2; i++)
      gel(V,i) = RgXQ_mul(gel(V,i-1),x,T);
  } else { /* use squarings if degree(x) is large */
    for(i = 4; i < l+2; i++)
      gel(V,i) = (i&1)? RgXQ_sqr(gel(V, (i+1)>>1),T)
                      : RgXQ_mul(gel(V, i-1),x,T);
  }
  return V;
}

/* a in K = Q[X]/(T), returns [a^0, ..., a^n] */
GEN
QXQ_powers(GEN a, long n, GEN T)
{
  GEN den, v = RgXQ_powers(Q_remove_denom(a, &den), n, T);
  /* den*a integral; v[i+1] = (den*a)^i in K */
  if (den)
  { /* restore denominators */
    GEN d = den;
    long i;
    gel(v,2) = a;
    for (i=3; i<=n+1; i++) {
      d = mulii(d,den);
      gel(v,i) = RgX_Rg_div(gel(v,i), d);
    }
  }
  return v;
}

GEN
RgXQ_matrix_pow(GEN y, long n, long m, GEN P)
{
  return RgXV_to_RgM(RgXQ_powers(y,m-1,P),n);
}

GEN
RgXQ_minpoly_naive(GEN y, GEN P)
{
  pari_sp ltop=avma;
  long n=lgpol(P);
  GEN M=ker(RgXQ_matrix_pow(y,n,n,P));
  M=content(RgM_to_RgXV(M,varn(P)));
  return gerepileupto(ltop,M);
}

GEN
RgXQ_norm(GEN x, GEN T)
{
  pari_sp av;
  long dx = degpol(x);
  GEN L, y;

  av = avma; y = resultant(T, x);
  L = leading_term(T);
  if (gequal1(L) || dx < 0) return y;
  return gerepileupto(av, gdiv(y, gpowgs(L, dx)));
}
