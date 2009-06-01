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
    rhs = Fp_add(Fp_mul(x, Fp_add(Fp_sqr(x, p), a4, p), p), a6, p);
  } while (kronecker(rhs, p) < 0);
  y = Fp_sqrt(rhs, p);
  if (!y) pari_err(talker,"not a prime number");
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
  return gerepileuptoint(av, gen_eltorder(z, o, (void*)&e, &FpE_group));
}

/***********************************************************************/
/**                                                                   **/
/**                            Pairings                               **/
/**                                                                   **/
/***********************************************************************/
/* Formulae from a GP script by J.E.Cremona */

static GEN
FpE_ffvert(GEN t, GEN pt, GEN p)
{
  return ell_is_inf(t)?gen_1:Fp_sub(gel(pt, 1), gel(t, 1), p);
}

static GEN
FpE_fftang(GEN t, GEN pt, GEN a4, GEN p)
{
  GEN dyf, dxf;
  if (ell_is_inf(t)) return gen_1;
  if (signe(gel(t, 2))==0)
    return Fp_sub(gel(pt, 1), gel(t, 1), p);
  dxf = Fp_neg(Fp_add(Fp_mulu(Fp_sqr(gel(t, 1), p), 3, p), a4, p), p);
  dyf = Fp_mulu(gel(t, 2), 2, p);
  return Fp_add(Fp_sub(gel(pt, 2), gel(t, 2), p), Fp_mul(Fp_div(dxf, dyf, p),
                Fp_sub(gel(pt, 1), gel(t, 1), p), p), p);
}

static GEN
FpE_ffchord(GEN t, GEN s, GEN pt, GEN a4, GEN p)
{
  if (ell_is_inf(s)) return FpE_ffvert(t, pt, p);
  if (ell_is_inf(t)) return FpE_ffvert(s, pt, p);
  if (equalii(gel(s, 1), gel(t, 1)))
  {
    if (equalii(gel(s, 2), gel(t, 2))) return FpE_fftang(t, pt, a4, p);
    else return FpE_ffvert(t, pt, p);
  }
  return Fp_sub(Fp_sub(gel(pt, 2), gel(t, 2),p),
                Fp_mul(Fp_div(Fp_sub(gel(t, 2), gel(s, 2), p),
                              Fp_sub(gel(t, 1), gel(s, 1),p), p),
                       Fp_sub(gel(pt, 1), gel(t, 1), p), p), p);
}

struct FpE_ff
{
  GEN pt1, pt2, a4, p;
};

static GEN
FpE_ffadd(GEN S, GEN T, GEN pt1, GEN pt2, GEN a4, GEN p)
{
  GEN s=gel(S,1), t=gel(T,1);
  GEN a, b, h;
  GEN ST = cgetg(3, t_VEC);
  GEN st = FpE_add(s, t, a4, p);
  pari_sp av=avma;
  gel(ST, 1) = st;
  a  = Fp_mul(FpE_ffchord(s, t, pt1, a4, p), FpE_ffvert(st, pt2, p), p);
  if (signe(a)==0) return gen_0;
  b  = Fp_mul(FpE_ffchord(s, t, pt2, a4, p), FpE_ffvert(st, pt1, p), p);
  if (signe(b)==0) return gen_0;
  h = Fp_mul(Fp_mul(gel(S,2), gel(T,2), p), Fp_div(a, b, p), p);
  gel(ST, 2) = gerepileupto(av, h);
  return ST;
}
static GEN
_FpE_ffadd(void *data, GEN s, GEN t)
{
  struct FpE_ff* ff=(struct FpE_ff*) data;
  if (s==gen_0 || t==gen_0) return gen_0;
  return FpE_ffadd(s,t,ff->pt1,ff->pt2,ff->a4,ff->p);
}

static GEN
FpE_ffdbl(GEN S, GEN pt1, GEN pt2, GEN a4, GEN p)
{
  GEN s=gel(S,1);
  GEN a, b, h;
  GEN S2 = cgetg(3, t_VEC);
  GEN s2 = FpE_dbl(s, a4, p);
  pari_sp av=avma;
  gel(S2, 1) = s2;
  a = Fp_mul(FpE_fftang(s, pt1, a4, p), FpE_ffvert(s2, pt2, p), p);
  if (signe(a)==0) return gen_0;
  b = Fp_mul(FpE_fftang(s, pt2, a4, p), FpE_ffvert(s2, pt1, p), p);
  if (signe(b)==0) return gen_0;
  h = Fp_mul(Fp_sqr(gel(S, 2), p), Fp_div(a, b, p), p);
  gel(S2, 2) = gerepileupto(av, h);
  return S2;
}

static GEN
_FpE_ffdbl(void *data, GEN s)
{
  struct FpE_ff* ff=(struct FpE_ff*) data;
  if (s==gen_0) return gen_0;
  return FpE_ffdbl(s,ff->pt1,ff->pt2,ff->a4,ff->p);
}

static GEN
FpE_ffmul(GEN t, GEN m, GEN pt1, GEN pt2, GEN a4, GEN p)
{
  struct FpE_ff ff;
  ff.pt1=pt1; ff.pt2=pt2; ff.a4=a4; ff.p=p;
  return leftright_pow(t, m, (void*)&ff, _FpE_ffdbl, _FpE_ffadd);
}

static GEN
FpE_ffmul1(GEN t, GEN m, GEN pt1, GEN pt2, GEN a4, GEN p)
{
  return gel(FpE_ffmul(mkvec2(t, gen_1), m, pt1, pt2, a4, p), 2);
}
static GEN
FpE_get_a6(GEN P, GEN a4, GEN p)
{
  GEN x=gel(P,1), y=gel(P,2);
  GEN RHS = Fp_mul(x, Fp_add(Fp_sqr(x, p), a4, p), p);
  return Fp_sub(Fp_sqr(y, p), RHS, p);
}

static GEN
FpE_weilpairing2(GEN t, GEN s, GEN p)
{
 return gequal(s, t)? gen_1: subis(p, 1);
}

static GEN
FpE_weilpairing3(GEN t, GEN s, GEN a4, GEN p)
{
  pari_sp ltop = avma;
  GEN t2, s2, a, b;
  if (gequal(s, t)) return gen_1;
  t2 = FpE_dbl(t, a4, p);
  if (gequal(s, t2)) return gen_1;
  s2 = FpE_dbl(s, a4, p);
  a  = Fp_mul(FpE_fftang(s, t,  a4, p), FpE_fftang(t, s2, a4 ,p), p);
  b  = Fp_mul(FpE_fftang(s, t2, a4, p), FpE_fftang(t, s,  a4, p), p);
  return gerepileuptoint(ltop, Fp_sqr(Fp_div(a, b, p), p));
}

static GEN
FpE_weilpairing4(GEN t, GEN s, GEN m, GEN a4, GEN p)
{
  pari_sp ltop = avma;
  GEN s2, t2, t3;
  GEN w;
  if (gequal(s, t)) return gen_1;
  s2 = FpE_dbl(s, a4, p);
  t2 = FpE_dbl(t, a4, p);
  if (ell_is_inf(s2)) return FpE_weilpairing2(s, t2, p);
  if (ell_is_inf(t2)) return FpE_weilpairing2(s2, t, p);
  if (gequal(s2, t2)) return FpE_weilpairing2(s2, FpE_sub(s, t, a4, p), p);
  t3 = FpE_add(t2, t, a4, p);
  if (gequal(s, t3)) return gen_1;
  w = Fp_mul(Fp_mul(FpE_ffmul1(s, m, t, t2, a4, p),
                    FpE_ffmul1(s2,m, t2, t, a4, p), p),
             Fp_mul(FpE_ffmul1(t, m, s2, s, a4, p),
                    FpE_ffmul1(t2,m, s, s2, a4, p), p), p);
  return gerepileuptoint(ltop, w);
}

GEN
FpE_weilpairing(GEN t, GEN s, GEN m, GEN a4, GEN p)
{
  pari_sp ltop=avma, av;
  GEN w, a6;
  if (ell_is_inf(s) || ell_is_inf(t)) return gen_1;
  switch(itou_or_0(m))
  {
    case 2: return FpE_weilpairing2(s, t, p);
    case 3: return FpE_weilpairing3(s, t, a4, p);
    case 4: return FpE_weilpairing4(s, t, m, a4, p);
  }
  a6 = FpE_get_a6(t, a4, p);
  av = avma;
  while(1)
  {
    GEN r, rs, tr, a, b;
    avma = av;
    r  = random_FpE(a4, a6, p);
    rs = FpE_add(r, s, a4, p);
    tr = FpE_sub(t, r, a4, p);
    if (ell_is_inf(rs) || ell_is_inf(tr) || ell_is_inf(r) || gequal(rs, t))
      continue;
    a = FpE_ffmul(mkvec2(t, gen_1), m, rs, r, a4, p);
    if (a==gen_0) continue;
    b = FpE_ffmul(mkvec2(s, gen_1), m, tr, FpE_neg_i(r, p), a4, p);
    if (b==gen_0) continue;
    w = Fp_div(gel(a, 2), gel(b, 2), p);
    return gerepileuptoint(ltop, w);
  }
}

GEN
FpE_tatepairing(GEN t, GEN s, GEN m, GEN a4, GEN p)
{
  pari_sp ltop=avma, av;
  GEN w, a6;
  if (ell_is_inf(s) || ell_is_inf(t)) return gen_1;
  a6 = FpE_get_a6(t, a4, p);
  av = avma;
  while(1)
  {
    GEN r, rs, tr, a;
    avma = av;
    r  = random_FpE(a4, a6, p);
    rs = FpE_add(r, s, a4, p);
    tr = FpE_sub(t, r, a4, p);
    if (ell_is_inf(rs) || ell_is_inf(tr) || ell_is_inf(r) || gequal(rs, t))
      continue;
    a = FpE_ffmul(mkvec2(t, gen_1), m, rs, r, a4, p);
    if (a==gen_0) continue;
    w = Fp_pow(gel(a, 2), diviiexact(subis(p,1), m), p);
    return gerepileuptoint(ltop, w);
  }
}
