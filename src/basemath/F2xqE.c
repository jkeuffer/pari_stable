/* $Id$

Copyright (C) 2012  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#include "pari.h"
#include "paripriv.h"

/* Not so fast arithmetic with points over elliptic curves over F_2^n */

/***********************************************************************/
/**                                                                   **/
/**                              F2xqE                                **/
/**                                                                   **/
/***********************************************************************/

/* Theses functions deal with point over elliptic curves over F_2^n defined
 * by an equation of the form:
 ** y^2+x*y=x^3+a_2*x^2+a_6 if the curve is ordinary.
 ** y^2+a_3*y=x^3+a_4*x+a_6 if the curve is supersingular.
 * Most of the time a6 is omitted since it can be recovered from any point
 * on the curve.
 * For supersingular curves, the parameter a2 is replaced by [a3,a4,a3^-1].
 */

GEN
RgE_to_F2xqE(GEN x, GEN T)
{
  if (ell_is_inf(x)) return x;
  retmkvec2(Rg_to_F2xq(gel(x,1),T),Rg_to_F2xq(gel(x,2),T));
}

GEN
F2xqE_changepoint(GEN x, GEN ch, GEN T)
{
  pari_sp av = avma;
  GEN p1,z,u,r,s,t,v,v2,v3;
  if (ell_is_inf(x)) return x;
  u = gel(ch,1); r = gel(ch,2);
  s = gel(ch,3); t = gel(ch,4);
  v = F2xq_inv(u, T); v2 = F2xq_sqr(v, T); v3 = F2xq_mul(v,v2, T);
  p1 = F2x_add(gel(x,1),r);
  z = cgetg(3,t_VEC);
  gel(z,1) = F2xq_mul(v2, p1, T);
  gel(z,2) = F2xq_mul(v3, F2x_add(gel(x,2), F2x_add(F2xq_mul(s, p1, T),t)), T);
  return gerepileupto(av, z);
}

GEN
F2xqE_changepointinv(GEN x, GEN ch, GEN T)
{
  GEN u, r, s, t, X, Y, u2, u3, u2X, z;
  if (ell_is_inf(x)) return x;
  X = gel(x,1); Y = gel(x,2);
  u = gel(ch,1); r = gel(ch,2);
  s = gel(ch,3); t = gel(ch,4);
  u2 = F2xq_sqr(u, T); u3 = F2xq_mul(u,u2, T);
  u2X = F2xq_mul(u2,X, T);
  z = cgetg(3, t_VEC);
  gel(z,1) = F2x_add(u2X,r);
  gel(z,2) = F2x_add(F2xq_mul(u3,Y, T), F2x_add(F2xq_mul(s,u2X, T), t));
  return z;
}

static GEN
F2xqE_dbl_slope(GEN P, GEN a, GEN T, GEN *slope)
{
  GEN x, y, Q;
  if (ell_is_inf(P)) return ellinf();
  x = gel(P,1); y = gel(P,2);
  if (typ(a)==t_VECSMALL)
  {
    GEN a2 = a;
    if (!lgpol(gel(P,1))) return ellinf();
    *slope = F2x_add(x, F2xq_div(y, x, T));
    Q = cgetg(3,t_VEC);
    gel(Q, 1) = F2x_add(F2xq_sqr(*slope, T), F2x_add(*slope, a2));
    gel(Q, 2) = F2x_add(F2xq_mul(*slope, F2x_add(x, gel(Q, 1)), T), F2x_add(y, gel(Q, 1)));
  }
  else
  {
    GEN a3 = gel(a,1), a4 = gel(a,2), a3i = gel(a,3);
    *slope = F2xq_mul(F2x_add(a4, F2xq_sqr(x, T)), a3i, T);
    Q = cgetg(3,t_VEC);
    gel(Q, 1) = F2xq_sqr(*slope, T);
    gel(Q, 2) = F2x_add(F2xq_mul(*slope, F2x_add(x, gel(Q, 1)), T), F2x_add(y, a3));
  }
  return Q;
}

GEN
F2xqE_dbl(GEN P, GEN a, GEN T)
{
  pari_sp av = avma;
  GEN slope;
  return gerepileupto(av, F2xqE_dbl_slope(P, a, T,&slope));
}

static GEN
F2xqE_add_slope(GEN P, GEN Q, GEN a, GEN T, GEN *slope)
{
  GEN Px, Py, Qx, Qy, R;
  if (ell_is_inf(P)) return Q;
  if (ell_is_inf(Q)) return P;
  Px = gel(P,1); Py = gel(P,2);
  Qx = gel(Q,1); Qy = gel(Q,2);
  if (zv_equal(Px, Qx))
  {
    if (zv_equal(Py, Qy))
      return F2xqE_dbl_slope(P, a, T, slope);
    else
      return ellinf();
  }
  *slope = F2xq_div(F2x_add(Py, Qy), F2x_add(Px, Qx), T);
  R = cgetg(3,t_VEC);
  if (typ(a)==t_VECSMALL)
  {
    GEN a2 = a;
    gel(R, 1) = F2x_add(F2x_add(F2x_add(F2x_add(F2xq_sqr(*slope, T), *slope), Px), Qx), a2);
    gel(R, 2) = F2x_add(F2xq_mul(*slope, F2x_add(Px, gel(R, 1)), T), F2x_add(Py, gel(R, 1)));
  }
  else
  {
    GEN a3 = gel(a,1);
    gel(R, 1) = F2x_add(F2x_add(F2xq_sqr(*slope, T), Px), Qx);
    gel(R, 2) = F2x_add(F2xq_mul(*slope, F2x_add(Px, gel(R, 1)), T), F2x_add(Py, a3));
  }
  return R;
}

GEN
F2xqE_add(GEN P, GEN Q, GEN a, GEN T)
{
  pari_sp av = avma;
  GEN slope;
  return gerepileupto(av, F2xqE_add_slope(P, Q, a, T, &slope));
}

static GEN
F2xqE_neg_i(GEN P, GEN a, GEN T)
{
  GEN LHS;
  if (ell_is_inf(P)) return P;
  LHS = typ(a)==t_VECSMALL ? gel(P,1): gel(a,1);
  return mkvec2(gel(P,1), F2x_add(LHS, gel(P,2)));
}

GEN
F2xqE_neg(GEN P, GEN a, GEN T)
{
  GEN LHS;
  if (ell_is_inf(P)) return ellinf();
  LHS = typ(a)==t_VECSMALL ? gel(P,1): gel(a,1);
  return mkvec2(gcopy(gel(P,1)), F2x_add(LHS, gel(P,2)));
}

GEN
F2xqE_sub(GEN P, GEN Q, GEN a2, GEN T)
{
  pari_sp av = avma;
  GEN slope;
  return gerepileupto(av, F2xqE_add_slope(P, F2xqE_neg_i(Q, a2, T), a2, T, &slope));
}

struct _F2xqE
{
  GEN a2, a6;
  GEN T;
};

static GEN
_F2xqE_dbl(void *E, GEN P)
{
  struct _F2xqE *ell = (struct _F2xqE *) E;
  return F2xqE_dbl(P, ell->a2, ell->T);
}

static GEN
_F2xqE_add(void *E, GEN P, GEN Q)
{
  struct _F2xqE *ell=(struct _F2xqE *) E;
  return F2xqE_add(P, Q, ell->a2, ell->T);
}

static GEN
_F2xqE_mul(void *E, GEN P, GEN n)
{
  pari_sp av = avma;
  struct _F2xqE *e=(struct _F2xqE *) E;
  long s = signe(n);
  if (!s || ell_is_inf(P)) return ellinf();
  if (s<0) P = F2xqE_neg(P, e->a2, e->T);
  if (is_pm1(n)) return s>0? gcopy(P): P;
  return gerepileupto(av, gen_pow(P, n, e, &_F2xqE_dbl, &_F2xqE_add));
}

GEN
F2xqE_mul(GEN P, GEN n, GEN a2, GEN T)
{
  struct _F2xqE E;
  E.a2 = a2; E.T = T;
  return _F2xqE_mul(&E, P, n);
}

/* Finds a random non-singular point on E */
GEN
random_F2xqE(GEN a, GEN a6, GEN T)
{
  pari_sp ltop = avma;
  GEN x, y, rhs, u;
  do
  {
    avma= ltop;
    x   = random_F2x(F2x_degree(T),T[1]);
    if (typ(a) == t_VECSMALL)
    {
      GEN a2 = a, x2;
      if (!lgpol(x))
        { avma=ltop; retmkvec2(pol0_Flx(T[1]), F2xq_sqrt(a6,T)); }
      u = x; x2  = F2xq_sqr(x, T);
      rhs = F2x_add(F2xq_mul(x2,F2x_add(x,a2),T),a6);
      rhs = F2xq_div(rhs,x2,T);
    }
    else
    {
      GEN a3 = gel(a,1), a4 = gel(a,2), a3i = gel(a,3), u2i;
      u = a3; u2i = F2xq_sqr(a3i,T);
      rhs = F2x_add(F2xq_mul(x,F2x_add(F2xq_sqr(x,T),a4),T),a6);
      rhs = F2xq_mul(rhs,u2i,T);
    }
  } while (F2xq_trace(rhs,T));
  y = F2xq_mul(F2xq_Artin_Schreier(rhs, T), u, T);
  return gerepilecopy(ltop, mkvec2(x, y));
}

static GEN
_F2xqE_rand(void *E)
{
  struct _F2xqE *ell=(struct _F2xqE *) E;
  return random_F2xqE(ell->a2, ell->a6, ell->T);
}

static const struct bb_group F2xqE_group={_F2xqE_add,_F2xqE_mul,_F2xqE_rand,hash_GEN,zvV_equal,ell_is_inf, NULL};

const struct bb_group *
get_F2xqE_group(void ** pt_E, GEN a2, GEN a6, GEN T)
{
  struct _F2xqE *e = (struct _F2xqE *) stack_malloc(sizeof(struct _F2xqE));
  e->a2 = a2; e->a6 = a6; e->T = T;
  *pt_E = (void *) e;
  return &F2xqE_group;
}

GEN
F2xqE_order(GEN z, GEN o, GEN a2, GEN T)
{
  pari_sp av = avma;
  struct _F2xqE e;
  e.a2=a2; e.T=T;
  return gerepileuptoint(av, gen_order(z, o, (void*)&e, &F2xqE_group));
}

GEN
F2xqE_log(GEN a, GEN b, GEN o, GEN a2, GEN T)
{
  pari_sp av = avma;
  struct _F2xqE e;
  e.a2=a2; e.T=T;
  return gerepileuptoint(av, gen_PH_log(a, b, o, (void*)&e, &F2xqE_group));
}

/***********************************************************************/
/**                                                                   **/
/**                            Pairings                               **/
/**                                                                   **/
/***********************************************************************/

/* Derived from APIP from and by Jerome Milan, 2012 */

static GEN
F2xqE_vert(GEN P, GEN Q, GEN T)
{
  if (ell_is_inf(P))
    return pol1_F2x(T[1]);
  return F2x_add(gel(Q, 1), gel(P, 1));
}

/* Computes the equation of the line tangent to R and returns its
   evaluation at the point Q. Also doubles the point R.
 */

static GEN
F2xqE_tangent_update(GEN R, GEN Q, GEN a2, GEN T, GEN *pt_R)
{
  if (ell_is_inf(R))
  {
    *pt_R = ellinf();
    return pol1_F2x(T[1]);
  }
  else if (!lgpol(gel(R,1)))
  {
    *pt_R = ellinf();
    return F2xqE_vert(R, Q, T);
  } else {
    GEN slope, tmp1, tmp2;
    *pt_R = F2xqE_dbl_slope(R, a2, T, &slope);
    tmp1 = F2x_add(gel(Q, 1), gel(R, 1));
    tmp2 = F2x_add(F2xq_mul(tmp1, slope, T), gel(R,2));
    return F2x_add(gel(Q, 2), tmp2);
  }
}

/* Computes the equation of the line through R and P, and returns its
   evaluation at the point Q. Also adds P to the point R.
 */

static GEN
F2xqE_chord_update(GEN R, GEN P, GEN Q, GEN a2, GEN T, GEN *pt_R)
{
  if (ell_is_inf(R))
  {
    *pt_R = gcopy(P);
    return F2xqE_vert(P, Q, T);
  }
  else if (ell_is_inf(P))
  {
    *pt_R = gcopy(R);
    return F2xqE_vert(R, Q, T);
  }
  else if (zv_equal(gel(P, 1), gel(R, 1)))
  {
    if (zv_equal(gel(P, 2), gel(R, 2)))
      return F2xqE_tangent_update(R, Q, a2, T, pt_R);
    else
    {
      *pt_R = ellinf();
      return F2xqE_vert(R, Q, T);
    }
  } else {
    GEN slope, tmp1, tmp2;
    *pt_R = F2xqE_add_slope(P, R, a2, T, &slope);
    tmp1  = F2xq_mul(F2x_add(gel(Q, 1), gel(R, 1)), slope, T);
    tmp2  = F2x_add(tmp1, gel(R, 2));
    return F2x_add(gel(Q, 2), tmp2);
  }
}

/* Returns the Miller function f_{m, Q} evaluated at the point P using
   the standard Miller algorithm.
 */

struct _F2xqE_miller
{
  GEN T, a2, P;
};

static GEN
F2xqE_Miller_dbl(void* E, GEN d)
{
  struct _F2xqE_miller *m = (struct _F2xqE_miller *)E;
  GEN T = m->T, a2 = m->a2, P = m->P;
  GEN v, line;
  GEN num = F2xq_sqr(gel(d,1), T);
  GEN denom = F2xq_sqr(gel(d,2), T);
  GEN point = gel(d,3);
  line = F2xqE_tangent_update(point, P, a2, T, &point);
  num  = F2xq_mul(num, line, T);
  v = F2xqE_vert(point, P, T);
  denom = F2xq_mul(denom, v, T);
  return mkvec3(num, denom, point);
}

static GEN
F2xqE_Miller_add(void* E, GEN va, GEN vb)
{
  struct _F2xqE_miller *m = (struct _F2xqE_miller *)E;
  GEN T = m->T, a2 = m->a2, P = m->P;
  GEN v, line, point;
  GEN na = gel(va,1), da = gel(va,2), pa = gel(va,3);
  GEN nb = gel(vb,1), db = gel(vb,2), pb = gel(vb,3);
  GEN num   = F2xq_mul(na, nb, T);
  GEN denom = F2xq_mul(da, db, T);
  line = F2xqE_chord_update(pa, pb, P, a2, T, &point);
  num  = F2xq_mul(num, line, T);
  v = F2xqE_vert(point, P, T);
  denom = F2xq_mul(denom, v, T);
  return mkvec3(num, denom, point);
}

static GEN
F2xqE_Miller(GEN Q, GEN P, GEN m, GEN a2, GEN T)
{
  pari_sp ltop = avma;
  struct _F2xqE_miller d;
  GEN v, num, denom, g1;

  d.a2 = a2; d.T = T; d.P = P;
  g1 = pol1_F2x(T[1]);
  v = gen_pow(mkvec3(g1,g1,Q), m, (void*)&d, F2xqE_Miller_dbl, F2xqE_Miller_add);
  num = gel(v,1); denom = gel(v,2);
  if (!lgpol(num) || !lgpol(denom)) { avma = ltop; return NULL; }
  return gerepileupto(ltop, F2xq_div(num, denom, T));
}

GEN
F2xqE_weilpairing(GEN P, GEN Q, GEN m, GEN a2, GEN T)
{
  pari_sp ltop = avma;
  GEN num, denom, result;
  if (ell_is_inf(P) || ell_is_inf(Q) || zv_equal(P,Q))
    return pol1_F2x(T[1]);
  num    = F2xqE_Miller(P, Q, m, a2, T);
  if (!num) return pol1_F2x(T[1]);
  denom  = F2xqE_Miller(Q, P, m, a2, T);
  if (!denom) { avma=ltop; return pol1_F2x(T[1]); }
  result = F2xq_div(num, denom, T);
  return gerepileupto(ltop, result);
}

GEN
F2xqE_tatepairing(GEN P, GEN Q, GEN m, GEN a2, GEN T)
{
  GEN num;
  if (ell_is_inf(P) || ell_is_inf(Q))
    return pol1_F2x(T[1]);
  num = F2xqE_Miller(P, Q, m, a2, T);
  return num? num: pol1_F2x(T[1]);
}

/***********************************************************************/
/**                                                                   **/
/**                          Point counting                           **/
/**                                                                   **/
/***********************************************************************/

/* Solve the linear equation approximation in the Newton algorithm */

static GEN
Z2X_canonlift_aux(GEN f0, GEN f1, GEN V, long N)
{
  pari_sp av = avma;
  long N2, M;
  GEN q, d0, d1, d2, d3, V2, bil;
  V = ZX_remi2n(V, N);
  if (N == 1) return V;
  N2 = (N + 1)>>1; M = N - N2;
  q = int2n(N);
  f0 = ZX_remi2n(f0, N); f1 = ZX_remi2n(f1, N);
  d2 = Z2X_canonlift_aux(f0, f1, V, N2);
  RgX_even_odd(d2, &d0, &d1);
  bil = ZX_sub(FpX_mul(f0, d0, q), RgX_shift(FpX_mul(f1, d1, q), 1));
  V2 = ZX_shifti(ZX_sub(ZX_add(V, d2), ZX_shifti(bil, 1)), -N2);
  d3 = Z2X_canonlift_aux(f0, f1, V2, M);
  return gerepileupto(av, FpX_add(d2, ZX_shifti(d3, N2), q));
}

/* Lift P to Q such that Q(x^2)=Q(x)*Q(-x) mod 2^n */

static GEN
F2x_canonlift(GEN P, long n)
{
  pari_sp ltop = avma, st_lim = stack_lim(ltop, 1);
  long N = 1, N2;
  GEN f2 = F2x_to_ZX(P);
  long mask = quadratic_prec_mask(n);
  while (mask > 1)
  {
    GEN f0, f1, V, d, q;
    N2 = N; N <<= 1;
    if (mask&1UL) N--;
    mask >>= 1; q = int2n(N);
    RgX_even_odd(f2, &f0, &f1);
    V = ZX_shifti(ZX_add(ZX_sub(f2, FpX_sqr(f0, q)), RgX_shift(FpX_sqr(f1, q), 1)), -N2);
    d = Z2X_canonlift_aux(f0, f1, V, N2);
    f2 = FpX_add(f2, ZX_shifti(d, N2), q);
    if (low_stack(st_lim, stack_lim(ltop, 1)))
      f2 = gerepileupto(ltop, f2);
  }
  if (odd(degpol(f2))) f2 = FpX_neg(f2,int2n(n));
  return gerepileupto(ltop, f2);
}

static GEN
Z2XQ_frob(GEN x, GEN B, GEN T, GEN q)
{
  return FpX_rem_Barrett(RgX_inflate(x, 2), B, T, q);
}

static GEN
F2xq_fastsqrt(GEN c, GEN sqx, GEN T)
{
  GEN c0, c1;
  F2x_even_odd(c, &c0, &c1);
  return F2x_add(c0, F2xq_mul(c1, sqx, T));
}

/* Solve a*S(x)+b*x+c=0 mod 2^N where 2|b, a=1 [2] */

GEN
solve_frobeqn(GEN a, GEN b, GEN c, long N, GEN B, GEN T, GEN sqx)
{
  pari_sp ltop = avma;
  GEN q, x2, y2, c2, D2, lin;
  long N2, M;
  if (N == 1) return F2x_to_ZX(F2xq_fastsqrt(ZX_to_F2x(c), gel(sqx,1), gel(sqx,2)));
  N2 = (N + 1)>>1; M = N - N2;
  q = int2n(N);
  a = ZX_remi2n(a, N); b = ZX_remi2n(b, N); c = ZX_remi2n(c, N);
  B = ZX_remi2n(B, N); T = ZX_remi2n(T, N);
  x2 = solve_frobeqn(a, b, c, N2, B, T, sqx);
  y2 = Z2XQ_frob(x2, B, T, q);
  lin = ZX_add(ZX_add(ZX_mul(a, y2), ZX_mul(b, x2)), c);
  c2 = ZX_shifti(FpX_rem_Barrett(ZX_remi2n(lin, N), B, T, q), -N2);
  D2 = solve_frobeqn(a, b, c2, M, B, T, sqx);
  return gerepileupto(ltop, FpX_add(x2, ZX_shifti(D2, N2), q));
}

/*
  Let P(X,Y)=(X+2*Y+8*X*Y)^2+Y+4*X*Y
  Solve   P(x,S(x))=0 [mod 2^n]
  assuming  x = x0    [mod 2]

  we set s = X+2*Y+8*X*Y, P = s^2+Y+4*X*Y
  Dx = dP/dx = (16*s+4)*x+(4*s+1)
  Dy = dP/dy = (16*y+2)*s+4*y
*/

static GEN
solve_AGM_eqn(GEN x0, long n, GEN B, GEN T, GEN sqx)
{
  pari_sp ltop = avma, st_lim = stack_lim(ltop, 1);
  long mask, N = 1;
  GEN x2 = x0;
  mask = quadratic_prec_mask(n);
  while (mask > 1)
  {
    GEN q, BN, TN;
    GEN qM, BM, TM;
    long M, N2;
    GEN y2, x2y2, s, Dx, Dy, D2, V;
    N2 = N; N <<= 1;
    if (mask&1UL) N--;
    mask >>= 1; M = N - N2;
    BN = ZX_remi2n(B, N); TN = ZX_remi2n(T, N); q = int2n(N);
    y2 = Z2XQ_frob(x2, BN, TN, q);
    x2y2 = FpX_rem_Barrett(ZX_remi2n(ZX_mul(x2, y2), N), BN, TN, q);
    s = ZX_add(ZX_add(x2, ZX_shifti(y2, 1)), ZX_shifti(x2y2, 3));
    V = ZX_add(ZX_add(ZX_sqr(s), y2), ZX_shifti(x2y2, 2));
    V = FpX_rem_Barrett(ZX_remi2n(V, N), BN, TN, q);
    V = ZX_shifti(V, -N2);
    BM = ZX_remi2n(B, M); TM = ZX_remi2n(T, M); qM = int2n(M);
    Dx = ZX_add(ZX_mul(ZX_Z_add(ZX_shifti(y2, 4), gen_2), s), ZX_shifti(y2, 2));
    Dx = FpX_rem_Barrett(ZX_remi2n(Dx, M), BM, TM, qM);
    Dy = ZX_add(ZX_Z_add(ZX_mul(ZX_Z_add(ZX_shifti(x2, 4), utoi(4)), s), gen_1), ZX_shifti(x2, 2));
    Dy = FpX_rem_Barrett(ZX_remi2n(Dy, M), BM, TM, qM);
    D2 = solve_frobeqn(Dy, Dx, V, M, BM, TM, sqx);
    x2 = FpX_add(x2, ZX_shifti(D2, N2), q);
    if (low_stack(st_lim, stack_lim(ltop, 1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"solve_AGM_eqn");
      x2 = gerepileupto(ltop, x2);
    }
  }
  return gerepileupto(ltop, x2);
}

/* Assume a = 1 [4], return log(a) */
static GEN
Z2XQ_log(GEN a, GEN T, long e)
{
  pari_sp av = avma;
  long i,k= (long) pow((double)(e>>1),1./3);
  GEN pe = int2n(e+k);
  GEN ak = FpXQ_pow(a, int2n(k), T, pe);
  GEN bn = ZX_shifti(Fp_FpX_sub(gen_1, ak, pe),-1);
  GEN bd = ZX_shifti(FpX_Fp_add(ak, gen_1, pe),-1);
  GEN bdi = ZpXQ_invlift(bd,pol_1(varn(T)),T,gen_2,e);
  GEN b = FpXQ_mul(bn,bdi,T,pe), s;
  long l = (e>>1)/k;
  GEN pol = cgetg(l+3,t_POL);
  for(i=0; i<=l; i++)
    gel(pol,i+2) = Fp_inv(utoi(2*i+1),pe);
  s = FpXQ_mul(b,FpX_FpXQ_eval(pol,FpXQ_sqr(b,T,pe),T,pe),T,pe);
  return gerepileupto(av, FpX_neg(ZX_shifti(s,1-k), int2n(e)));
}

/* Assume a = 1 [4] */
static GEN
Z2XQ_invnorm(GEN a, GEN T, long e)
{
  GEN pe = int2n(e), s;
  if (degpol(a)==0) return Fp_inv(Fp_powu(gel(a,2),degpol(T),pe),pe);
  s = Fp_neg(FpXQ_trace(Z2XQ_log(a, T, e), T, pe), pe);
  return modii(gel(Qp_exp(cvtop(s, gen_2, e-2)),4),pe);
}

/* Assume a2==0, so 4|E(F_p): if t^4 = a6 then (t,t^2) is of order 4
   8|E(F_p) <=> trace(a6)==0
 */

static GEN
F2xq_elltrace_Harley(GEN a6, GEN T2)
{
  pari_sp ltop = avma;
  pari_timer ti;
  GEN B, T, sqx;
  GEN x, t;
  long n = F2x_degree(T2), N = ((n + 1)>>1) + 2;
  if (n==1) return gen_m1;
  if (n==2) return F2x_degree(a6) ? gen_1 : stoi(-3);
  if (n==3) return F2x_degree(a6) ? (F2xq_trace(a6,T2) ?  stoi(-3): gen_1) : stoi(5);
  timer_start(&ti);
  sqx = mkvec2(F2xq_sqrt(polx_F2x(T2[1]), T2), T2);
  if (DEBUGLEVEL>1) timer_printf(&ti,"Sqrtx");
  T = F2x_canonlift(T2, N-2);
  if (DEBUGLEVEL>1) timer_printf(&ti,"Teich");
  B = FpX_invBarrett(T, int2n(N));
  if (DEBUGLEVEL>1) timer_printf(&ti,"Barrett");
  x = solve_AGM_eqn(F2x_to_ZX(a6), N-2, B, T, sqx);
  if (DEBUGLEVEL>1) timer_printf(&ti,"Lift");
  t = Z2XQ_invnorm(ZX_Z_add_shallow(ZX_shifti(x,2), gen_1), T, N);
  if (DEBUGLEVEL>1) timer_printf(&ti,"Norm");
  if (cmpii(sqri(t), int2n(n + 2)) > 0)
    t = subii(t, int2n(N));
  return gerepileuptoint(ltop, t);
}

GEN
F2xq_ellcard(GEN a, GEN a6, GEN T)
{
  pari_sp av = avma;
  long n = F2x_degree(T);
  GEN q = int2u(n), c;
  if (typ(a)==t_VECSMALL)
  {
    GEN t = F2xq_elltrace_Harley(a6, T);
    c = addii(q, F2xq_trace(a,T) ? addui(1,t): subui(1,t));
  } else if (n==1)
  {
    long a4i = lgpol(gel(a,2)), a6i = lgpol(a6);
    return utoi(a4i? (a6i? 1: 5): 3);
  }
  else if (n==2)
  {
    GEN a3 = gel(a,1), a4 = gel(a,2), x = polx_F2x(T[1]), x1 = pol1_F2x(T[1]);
    GEN a613 = F2xq_mul(F2x_add(x1, a6),a3,T), a43= F2xq_mul(a4,a3,T);
    long f0= F2xq_trace(F2xq_mul(a6,a3,T),T);
    long f1= F2xq_trace(F2x_add(a43,a613),T);
    long f2= F2xq_trace(F2x_add(F2xq_mul(a43,x,T),a613),T);
    long f3= F2xq_trace(F2x_add(F2xq_mul(a43,F2x_add(x,x1),T),a613),T);
    c = utoi(9-2*(f0+f1+f2+f3));
  }
  else
  {
    struct _F2xqE e;
    long m = (n+1)>>1;
    GEN q1 = addis(q, 1);
    GEN v = n==4 ? mkvec4s(13,17,21,25)
                 : odd(n) ? mkvec3(subii(q1,int2u(m)),q1,addii(q1,int2u(m))):
                            mkvec5(subii(q1,int2u(m+1)),subii(q1,int2u(m)),q1,
                                   addii(q1,int2u(m)),addii(q1,int2u(m+1)));
    e.a2=a; e.a6=a6; e.T=T;
    c = gen_select_order(v,(void*)&e, &F2xqE_group);
    if (n==4 && equaliu(c, 21)) /* Ambiguous case */
    {
      GEN d = F2xq_pow(polx_F2x(T[1]),utoi(3),T), a3 = gel(a,1);
      e.a6 = F2x_add(a6,F2xq_mul(d,F2xq_sqr(a3,T),T)); /* twist */
      c = subui(34, gen_select_order(mkvec2s(13,25),(void*)&e, &F2xqE_group));
    }
  }
  return gerepileuptoint(av, c);
}

/***********************************************************************/
/**                                                                   **/
/**                          Group structure                          **/
/**                                                                   **/
/***********************************************************************/

static GEN
_F2xqE_pairorder(void *E, GEN P, GEN Q, GEN m, GEN F)
{
  struct _F2xqE *e = (struct _F2xqE *) E;
  return  F2xq_order(F2xqE_weilpairing(P,Q,m,e->a2,e->T), F, e->T);
}

GEN
F2xq_ellgroup(GEN a2, GEN a6, GEN N, GEN T, GEN *pt_m)
{
  struct _F2xqE e;
  GEN q = int2u(F2x_degree(T));
  e.a2=a2; e.a6=a6; e.T=T;
  return gen_ellgroup(N, subis(q,1), pt_m, (void*)&e, &F2xqE_group, _F2xqE_pairorder);
}

GEN
F2xq_ellgens(GEN a2, GEN a6, GEN ch, GEN D, GEN m, GEN T)
{
  GEN P;
  pari_sp av = avma;
  struct _F2xqE e;
  e.a2=a2; e.a6=a6; e.T=T;
  switch(lg(D)-1)
  {
  case 0:
    return cgetg(1,t_VEC);
  case 1:
    P = gen_gener(gel(D,1), (void*)&e, &F2xqE_group);
    P = mkvec(F2xqE_changepoint(P, ch, T));
    break;
  default:
    P = gen_ellgens(gel(D,1), gel(D,2), m, (void*)&e, &F2xqE_group, _F2xqE_pairorder);
    gel(P,1) = F2xqE_changepoint(gel(P,1), ch, T);
    gel(P,2) = F2xqE_changepoint(gel(P,2), ch, T);
    break;
  }
  return gerepilecopy(av, P);
}
