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
  return gerepileupto(av, leftright_pow(P, n, e, &_FpE_dbl, &_FpE_add));
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
    rhs = Fp_add(Fp_mul(x, Fp_add(Fp_sqr(x,p), a4, p), p), a6, p);
  } while (kronecker(rhs, p) < 0);
  y = Fp_sqrt(rhs, p);
  if (!y) pari_err(talker,"not a prime number");
  return gerepilecopy(ltop, mkvec2(x,y));
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
  return gerepileuptoint(av, gen_eltorder(z, o, (void*)&e, &FpE_group));
}

