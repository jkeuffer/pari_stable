/* $Id$

Copyright (C) 2009  The PARI group.

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
FpE_dbl(GEN P, GEN a4, GEN p)
{
  pari_sp ltop = avma;
  GEN lambda, C, D, x = gel(P,1), y = gel(P,2);
  if (ell_is_inf(P) || !signe(y)) return ellinf();
  lambda = Fp_div(Fp_add(Fp_mulu(Fp_sqr(x,p), 3, p), a4, p),
                  Fp_mulu(y, 2, p), p);
  C = Fp_sub(Fp_sqr(lambda, p), Fp_mulu(x, 2, p), p);
  D = Fp_sub(Fp_mul(lambda, Fp_sub(x, C, p), p), y, p);
  return gerepilecopy(ltop, mkvec2(C,D));
}

static GEN
FpE_add_i(GEN P, GEN Q, GEN a4, GEN p)
{
  GEN Px = gel(P,1), Py = gel(P,2);
  GEN Qx = gel(Q,1), Qy = gel(Q,2), lambda, C, D;
  if (ell_is_inf(P)) return Q;
  if (ell_is_inf(Q)) return P;
  if (equalii(Px, Qx))
  {
    if (equalii(Py, Qy))
      return FpE_dbl(P, a4, p);
    else
      return mkvec(gen_0);
  }
  lambda = Fp_div(Fp_sub(Py, Qy, p), Fp_sub(Px, Qx, p), p);
  C = Fp_sub(Fp_sub(Fp_sqr(lambda, p), Px, p), Qx, p);
  D = Fp_sub(Fp_mul(lambda, Fp_sub(Px, C, p), p), Py, p);
  return mkvec2(C,D);
}

GEN
FpE_add(GEN P, GEN Q, GEN a4, GEN p)
{
  pari_sp av = avma;
  return gerepilecopy(av, FpE_add_i(P,Q,a4,p));
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
  GEN z  = FpE_add_i(P, FpE_neg_i(Q, p), a4, p);
  return gerepilecopy(av, z);
}

struct _FpE
{
  GEN a4;
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

/* Finds a random point on E */
GEN
random_FpE(GEN a4, GEN a6, GEN p)
{
  pari_sp ltop = avma;
  GEN x, y, rhs;
  do
  {
    avma= ltop;
    x   = randomi(p); /*  x^3+a4*x+a6 = x*(x^2+a4)+a6  */
    rhs = Fp_add(Fp_mul(x, Fp_add(Fp_sqr(x, p), a4, p), p), a6, p);
  } while (kronecker(rhs, p) < 0);
  y = Fp_sqrt(rhs, p);
  if (!y) pari_err_PRIME("random_FpE", p);
  return gerepilecopy(ltop, mkvec2(x, y));
}

static int
FpE_cmp(GEN x, GEN y)
{
  if (ell_is_inf(x)) return !ell_is_inf(y);
  if (ell_is_inf(y)) return -1;
  return lexcmp(x,y);
}

static const struct bb_group FpE_group={_FpE_add,_FpE_mul,NULL,NULL,FpE_cmp,ell_is_inf};

GEN
FpE_order(GEN z, GEN o, GEN a4, GEN p)
{
  pari_sp av = avma;
  struct _FpE e;
  e.a4=a4;
  e.p=p;
  return gerepileuptoint(av, gen_order(z, o, (void*)&e, &FpE_group));
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
  GEN x1, y1;
  if (ell_is_inf(R)) return gen_1;

  x1 = gel(R, 1);
  y1 = gel(R, 2);

  if (signe(y1) == 0)
  {
    GEN v = FpE_vert(R, Q, p);
    *pt_R = ellinf();
    return v;
  } else {
    GEN _2_x1    = mului(2, x1);
    GEN _2_y1    = mului(2, y1);
    GEN _sqrx1   = Fp_sqr(x1,p);
    GEN _3_sqrx1 = mului(3, _sqrx1);
    GEN slope = Fp_div(addii(_3_sqrx1, a4), _2_y1, p);
    GEN x3 = Fp_sub(sqri(slope), _2_x1, p);
    GEN y3 = Fp_neg(addii(y1, mulii(slope, subii(x3, x1))), p);
    GEN tmp1 = Fp_add(gel(Q, 1), Fp_neg(x1, p), p);
    GEN tmp2 = Fp_add(Fp_mul(tmp1, slope, p), y1, p);
    GEN line = Fp_sub(gel(Q, 2), tmp2, p);

    *pt_R = mkvec2(x3, y3);
    return line;
  }
}

/* Computes the equation of the line through R and P, and returns its
   evaluation at the point Q. Also adds Q to the point R.
 */

static GEN
FpE_chord_update(GEN R, GEN P, GEN Q, GEN a4, GEN p, GEN *pt_R)
{
  if (ell_is_inf(R))
    return gen_1;
  if (equalii(gel(P, 1), gel(R, 1)))
  {
    if (equalii(gel(P, 2), subii(p, gel(R, 2))))
    {
      GEN v = FpE_vert(R, Q, p);
      *pt_R = ellinf();
      return v;
    } else
      return FpE_tangent_update(R, Q, a4, p, pt_R);
  } else {
    GEN x1 = gel(R, 1), y1 = gel(R, 2);
    GEN x2 = gel(P, 1), y2 = gel(P, 2);
    GEN slope = Fp_div(subii(y2, y1), subii(x2, x1), p);
    GEN x3 = Fp_sub(subii(gsqr(slope), x1), x2, p);
    GEN y3 = Fp_neg(addii(y1, mulii(slope, subii(x3, x1))), p);
    GEN tmp1 = Fp_mul(Fp_add(gel(Q, 1), Fp_neg(x1, p), p), slope, p);
    GEN tmp2 = Fp_add(tmp1, y1, p);
    GEN line = Fp_sub(gel(Q, 2), tmp2, p);
    *pt_R = mkvec2(x3, y3);
    return line;
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
