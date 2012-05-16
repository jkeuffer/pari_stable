/* $Id$

Copyright (C) 2009  The PARI group.

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

/* Not so fast arithmetic with points over elliptic curves over Fp */

/***********************************************************************/
/**                                                                   **/
/**                              FpE                                  **/
/**                                                                   **/
/***********************************************************************/

/* Theses functions deal with point over elliptic curves over Fp defined
 * by an equation of the form y^2=x^3+a4*x+a6.
 * Most of the time a6 is omitted since it can be recovered from any point
 * on the curve.
 */

GEN
FpE_changepoint(GEN x, GEN ch, GEN p)
{
  pari_sp av = avma;
  GEN p1,z,u,r,s,t,v,v2,v3;
  if (ell_is_inf(x)) return x;
  u = gel(ch,1); r = gel(ch,2);
  s = gel(ch,3); t = gel(ch,4);
  v = Fp_inv(u, p); v2 = Fp_sqr(v,p); v3 = Fp_mul(v,v2,p);
  p1 = Fp_sub(gel(x,1),r,p);
  z = cgetg(3,t_VEC);
  gel(z,1) = Fp_mul(v2, p1, p);
  gel(z,2) = Fp_mul(v3, Fp_sub(gel(x,2), Fp_add(Fp_mul(s,p1, p),t, p),p),p);
  return gerepileupto(av, z);
}

GEN
FpE_changepointinv(GEN x, GEN ch, GEN p)
{
  GEN u, r, s, t, X, Y, u2, u3, u2X, z;
  if (ell_is_inf(x)) return x;
  X = gel(x,1); Y = gel(x,2);
  u = gel(ch,1); r = gel(ch,2);
  s = gel(ch,3); t = gel(ch,4);
  u2 = Fp_sqr(u, p); u3 = Fp_mul(u,u2,p);
  u2X = Fp_mul(u2,X, p);
  z = cgetg(3, t_VEC);
  gel(z,1) = Fp_add(u2X,r,p);
  gel(z,2) = Fp_add(Fp_mul(u3,Y,p), Fp_add(Fp_mul(s,u2X,p), t, p), p);
  return z;
}

static GEN
FpE_dbl_slope(GEN P, GEN a4, GEN p, GEN *slope)
{
  GEN x, y, Q;
  if (ell_is_inf(P) || !signe(gel(P,2))) return ellinf();
  x = gel(P,1); y = gel(P,2);
  *slope = Fp_div(Fp_add(Fp_mulu(Fp_sqr(x,p), 3, p), a4, p),
                  Fp_mulu(y, 2, p), p);
  Q = cgetg(3,t_VEC);
  gel(Q, 1) = Fp_sub(Fp_sqr(*slope, p), Fp_mulu(x, 2, p), p),
  gel(Q, 2) = Fp_sub(Fp_mul(*slope, Fp_sub(x, gel(Q, 1), p), p), y, p);
  return Q;
}

GEN
FpE_dbl(GEN P, GEN a4, GEN p)
{
  pari_sp av = avma;
  GEN slope;
  return gerepileupto(av, FpE_dbl_slope(P,a4,p,&slope));
}

static GEN
FpE_add_slope(GEN P, GEN Q, GEN a4, GEN p, GEN *slope)
{
  GEN Px, Py, Qx, Qy, R;
  if (ell_is_inf(P)) return Q;
  if (ell_is_inf(Q)) return P;
  Px = gel(P,1); Py = gel(P,2);
  Qx = gel(Q,1); Qy = gel(Q,2);
  if (equalii(Px, Qx))
  {
    if (equalii(Py, Qy))
      return FpE_dbl_slope(P, a4, p, slope);
    else
      return mkvec(gen_0);
  }
  *slope = Fp_div(Fp_sub(Py, Qy, p), Fp_sub(Px, Qx, p), p);
  R = cgetg(3,t_VEC);
  gel(R, 1) = Fp_sub(Fp_sub(Fp_sqr(*slope, p), Px, p), Qx, p);
  gel(R, 2) = Fp_sub(Fp_mul(*slope, Fp_sub(Px, gel(R, 1), p), p), Py, p);
  return R;
}

GEN
FpE_add(GEN P, GEN Q, GEN a4, GEN p)
{
  pari_sp av = avma;
  GEN slope;
  return gerepileupto(av, FpE_add_slope(P,Q,a4,p,&slope));
}

static GEN
FpE_neg_i(GEN P, GEN p)
{
  if (ell_is_inf(P)) return P;
  return mkvec2(gel(P,1), Fp_neg(gel(P,2), p));
}

GEN
FpE_neg(GEN P, GEN p)
{
  if (ell_is_inf(P)) return ellinf();
  return mkvec2(gcopy(gel(P,1)), Fp_neg(gel(P,2), p));
}

GEN
FpE_sub(GEN P, GEN Q, GEN a4, GEN p)
{
  pari_sp av = avma;
  GEN slope;
  return gerepileupto(av, FpE_add_slope(P, FpE_neg_i(Q, p), a4, p, &slope));
}

struct _FpE
{
  GEN a4,a6;
  GEN p;
};

static GEN
_FpE_dbl(void *E, GEN P)
{
  struct _FpE *ell = (struct _FpE *) E;
  return FpE_dbl(P, ell->a4, ell->p);
}

static GEN
_FpE_add(void *E, GEN P, GEN Q)
{
  struct _FpE *ell=(struct _FpE *) E;
  return FpE_add(P, Q, ell->a4, ell->p);
}

static GEN
_FpE_mul(void *E, GEN P, GEN n)
{
  pari_sp av = avma;
  struct _FpE *e=(struct _FpE *) E;
  long s = signe(n);
  if (!s || ell_is_inf(P)) return ellinf();
  if (s<0) P = FpE_neg(P, e->p);
  if (is_pm1(n)) return s>0? gcopy(P): P;
  return gerepileupto(av, gen_pow(P, n, e, &_FpE_dbl, &_FpE_add));
}

GEN
FpE_mul(GEN P, GEN n, GEN a4, GEN p)
{
  struct _FpE E;
  E.a4= a4; E.p = p;
  return _FpE_mul(&E, P, n);
}

/* Finds a random non-singular point on E */

GEN
random_FpE(GEN a4, GEN a6, GEN p)
{
  pari_sp ltop = avma;
  GEN x, x2, y, rhs;
  do
  {
    avma= ltop;
    x   = randomi(p); /*  x^3+a4*x+a6 = x*(x^2+a4)+a6  */
    x2  = Fp_sqr(x, p);
    rhs = Fp_add(Fp_mul(x, Fp_add(x2, a4, p), p), a6, p);
    if (!signe(rhs) && !signe(Fp_add(mului(3,x2),a4,p)))
      continue;
  } while (kronecker(rhs, p) < 0);
  y = Fp_sqrt(rhs, p);
  if (!y) pari_err_PRIME("random_FpE", p);
  return gerepilecopy(ltop, mkvec2(x, y));
}

static GEN
_FpE_rand(void *E)
{
  struct _FpE *e=(struct _FpE *) E;
  return random_FpE(e->a4, e->a6, e->p);
}

static int
FpE_cmp(GEN x, GEN y)
{
  if (ell_is_inf(x)) return !ell_is_inf(y);
  if (ell_is_inf(y)) return -1;
  return lexcmp(x,y);
}

static ulong
FpE_hash(GEN P)
{
  return signe(gel(P,1))?mod2BIL(gel(P,1)):0;
}

static const struct bb_group FpE_group={_FpE_add,_FpE_mul,_FpE_rand,FpE_hash,FpE_cmp,ell_is_inf};

GEN
FpE_order(GEN z, GEN o, GEN a4, GEN p)
{
  pari_sp av = avma;
  struct _FpE e;
  e.a4=a4;
  e.p=p;
  return gerepileuptoint(av, gen_order(z, o, (void*)&e, &FpE_group));
}

GEN
FpE_log(GEN a, GEN b, GEN o, GEN a4, GEN p)
{
  pari_sp av = avma;
  struct _FpE e;
  e.a4=a4;
  e.p=p;
  return gerepileuptoint(av, gen_PH_log(a, b, o, (void*)&e, &FpE_group, NULL));
}

/***********************************************************************/
/**                                                                   **/
/**                            Pairings                               **/
/**                                                                   **/
/***********************************************************************/

/* Derived from APIP from and by Jerome Milan, 2012 */

static GEN
FpE_vert(GEN P, GEN Q, GEN p)
{
  if (ell_is_inf(P))
    return gen_1;
  return Fp_sub(gel(Q, 1), gel(P, 1), p);
}

/* Computes the equation of the line tangent to R and returns its
   evaluation at the point Q. Also doubles the point R.
 */

static GEN
FpE_tangent_update(GEN R, GEN Q, GEN a4, GEN p, GEN *pt_R)
{
  if (ell_is_inf(R))
  {
    *pt_R = ellinf();
    return gen_1;
  }
  else if (signe(gel(R,2)) == 0)
  {
    *pt_R = ellinf();
    return FpE_vert(R, Q, p);
  } else {
    GEN slope, tmp1, tmp2;
    *pt_R = FpE_dbl_slope(R, a4, p, &slope);
    tmp1 = Fp_add(gel(Q, 1), Fp_neg(gel(R, 1), p), p);
    tmp2 = Fp_add(Fp_mul(tmp1, slope, p), gel(R,2), p);
    return Fp_sub(gel(Q, 2), tmp2, p);
  }
}

/* Computes the equation of the line through R and P, and returns its
   evaluation at the point Q. Also adds Q to the point R.
 */

static GEN
FpE_chord_update(GEN R, GEN P, GEN Q, GEN a4, GEN p, GEN *pt_R)
{
  if (ell_is_inf(R))
  {
    *pt_R = ellinf();
    return gen_1;
  }
  else if (equalii(gel(P, 1), gel(R, 1)))
  {
    if (equalii(gel(P, 2), gel(R, 2)))
      return FpE_tangent_update(R, Q, a4, p, pt_R);
    else {
      *pt_R = ellinf();
      return FpE_vert(R, Q, p);
    }
  } else {
    GEN slope, tmp1, tmp2;
    *pt_R = FpE_add_slope(P, R, a4, p, &slope);
    tmp1  = Fp_mul(Fp_add(gel(Q, 1), Fp_neg(gel(R, 1), p), p), slope, p);
    tmp2  = Fp_add(tmp1, gel(R, 2), p);
    return Fp_sub(gel(Q, 2), tmp2, p);
  }
}

/* Returns the Miller function f_{m, Q} evaluated at the point P using
   the standard Miller algorithm.
 */

struct _FpE_miller
{
  GEN p, a4, P;
};

static GEN
FpE_Miller_dbl(void* E, GEN d)
{
  struct _FpE_miller *m = (struct _FpE_miller *)E;
  GEN p = m->p, a4 = m->a4, P = m->P;
  GEN v, line;
  GEN num = Fp_sqr(gel(d,1), p);
  GEN denom = Fp_sqr(gel(d,2), p);
  GEN point = gel(d,3);
  line = FpE_tangent_update(point, P, a4, p, &point);
  num  = Fp_mul(num, line, p);
  v = FpE_vert(point, P, p);
  denom = Fp_mul(denom, v, p);
  return mkvec3(num, denom, point);
}

static GEN
FpE_Miller_add(void* E, GEN va, GEN vb)
{
  struct _FpE_miller *m = (struct _FpE_miller *)E;
  GEN p = m->p, a4= m->a4, P = m->P;
  GEN v, line, point;
  GEN na = gel(va,1), da = gel(va,2), pa = gel(va,3);
  GEN nb = gel(vb,1), db = gel(vb,2), pb = gel(vb,3);
  GEN num   = Fp_mul(na, nb, p);
  GEN denom = Fp_mul(da, db, p);
  line = FpE_chord_update(pa, pb, P, a4, p, &point);
  num  = Fp_mul(num, line, p);
  v = FpE_vert(point, P, p);
  denom = Fp_mul(denom, v, p);
  return mkvec3(num, denom, point);
}

static GEN
FpE_Miller(GEN Q, GEN P, GEN m, GEN a4, GEN p)
{
  pari_sp ltop = avma;
  struct _FpE_miller d;
  GEN v, result, num, denom;

  d.a4 = a4; d.p = p; d.P = P;
  v = gen_pow(mkvec3(gen_1,gen_1,Q), m, (void*)&d, FpE_Miller_dbl, FpE_Miller_add);
  num = gel(v,1); denom = gel(v,2);
  result = signe(denom) ? Fp_div(num, denom, p): gen_1;
  return gerepileupto(ltop, signe(result) ? result: gen_1);
}

GEN
FpE_weilpairing(GEN P, GEN Q, GEN m, GEN a4, GEN p)
{
  pari_sp ltop = avma;
  GEN num, denom, result;
  if (ell_is_inf(P) || ell_is_inf(Q) || ZV_equal(P,Q))
    return gen_1;
  num    = FpE_Miller(P, Q, m, a4, p);
  denom  = FpE_Miller(Q, P, m, a4, p);
  result = Fp_div(num, denom, p);
  if (mpodd(m))
    result  = Fp_neg(result, p);
  return gerepileupto(ltop, result);
}

GEN
FpE_tatepairing(GEN P, GEN Q, GEN m, GEN a4, GEN p)
{
  if (ell_is_inf(P) || ell_is_inf(Q))
    return gen_1;
  return FpE_Miller(P, Q, m, a4, p);
}

static GEN
_FpE_pairorder(void *E, GEN P, GEN Q, GEN m, GEN F)
{
  struct _FpE *e = (struct _FpE *) E;
  return  Fp_order(FpE_weilpairing(P,Q,m,e->a4,e->p), F, e->p);
}

GEN
Fp_ellgroup(GEN a4, GEN a6, GEN N, GEN p, GEN *pt_m)
{
  struct _FpE e;
  e.a4=a4; e.a6=a6; e.p=p;
  return gen_ellgroup(N, subis(p, 1), pt_m, (void*)&e, &FpE_group, _FpE_pairorder);
}

GEN
Fp_ellgens(GEN a4, GEN a6, GEN ch, GEN D, GEN m, GEN p)
{
  GEN P;
  pari_sp av = avma;
  struct _FpE e;
  e.a4=a4; e.a6=a6; e.p=p;
  switch(lg(D)-1)
  {
  case 1:
    P = gen_gener(gel(D,1), (void*)&e, &FpE_group);
    P = mkvec(FpE_changepoint(P, ch, p));
    break;
  default:
    P = gen_ellgens(gel(D,1), gel(D,2), m, (void*)&e, &FpE_group, _FpE_pairorder);
    gel(P,1) = FpE_changepoint(gel(P,1), ch, p);
    gel(P,2) = FpE_changepoint(gel(P,2), ch, p);
    break;
  }
  return gerepilecopy(av, P);
}
