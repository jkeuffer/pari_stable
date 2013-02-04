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

/* Not so fast arithmetic with points over elliptic curves over Fq,
small characteristic. */

/***********************************************************************/
/**                                                                   **/
/**                              FlxqE                                **/
/**                                                                   **/
/***********************************************************************/

/* Theses functions deal with point over elliptic curves over Fq defined
 * by an equation of the form y^2=x^3+a4*x+a6.
 * Most of the time a6 is omitted since it can be recovered from any point
 * on the curve.
 */

GEN
RgE_to_FlxqE(GEN x, GEN T, ulong p)
{
  if (ell_is_inf(x)) return x;
  retmkvec2(Rg_to_Flxq(gel(x,1),T,p),Rg_to_Flxq(gel(x,2),T,p));
}

GEN
FlxqE_changepoint(GEN x, GEN ch, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN p1,z,u,r,s,t,v,v2,v3;
  if (ell_is_inf(x)) return x;
  u = gel(ch,1); r = gel(ch,2);
  s = gel(ch,3); t = gel(ch,4);
  v = Flxq_inv(u, T, p); v2 = Flxq_sqr(v, T, p); v3 = Flxq_mul(v,v2, T, p);
  p1 = Flx_sub(gel(x,1),r, p);
  z = cgetg(3,t_VEC);
  gel(z,1) = Flxq_mul(v2, p1, T, p);
  gel(z,2) = Flxq_mul(v3, Flx_sub(gel(x,2), Flx_add(Flxq_mul(s, p1, T, p),t, p), p), T, p);
  return gerepileupto(av, z);
}

GEN
FlxqE_changepointinv(GEN x, GEN ch, GEN T, ulong p)
{
  GEN u, r, s, t, X, Y, u2, u3, u2X, z;
  if (ell_is_inf(x)) return x;
  X = gel(x,1); Y = gel(x,2);
  u = gel(ch,1); r = gel(ch,2);
  s = gel(ch,3); t = gel(ch,4);
  u2 = Flxq_sqr(u, T, p); u3 = Flxq_mul(u,u2, T, p);
  u2X = Flxq_mul(u2,X, T, p);
  z = cgetg(3, t_VEC);
  gel(z,1) = Flx_add(u2X,r, p);
  gel(z,2) = Flx_add(Flxq_mul(u3,Y, T, p), Flx_add(Flxq_mul(s,u2X, T, p), t, p), p);
  return z;
}

static GEN
FlxqE_dbl_slope(GEN P, GEN a4, GEN T, ulong p, GEN *slope)
{
  GEN x, y, Q;
  if (ell_is_inf(P) || !lgpol(gel(P,2))) return ellinf();
  x = gel(P,1); y = gel(P,2);
  if (p==3UL)
    *slope = typ(a4)==t_VEC ? Flxq_div(Flxq_mul(x, gel(a4, 1), T, p), y, T, p)
                            : Flxq_div(a4, Flx_neg(y, p), T, p);
  else
  {
    GEN sx = Flx_add(Flx_Fl_mul(Flxq_sqr(x, T, p), 3, p), a4, p);
    *slope = Flxq_div(sx, Flx_Fl_mul(y, 2, p), T, p);
  }
  Q = cgetg(3,t_VEC);
  gel(Q, 1) = Flx_sub(Flxq_sqr(*slope, T, p), Flx_Fl_mul(x, 2, p), p);
  if (typ(a4)==t_VEC) gel(Q, 1) = Flx_sub(gel(Q, 1), gel(a4, 1), p);
  gel(Q, 2) = Flx_sub(Flxq_mul(*slope, Flx_sub(x, gel(Q, 1), p), T, p), y, p);
  return Q;
}

GEN
FlxqE_dbl(GEN P, GEN a4, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN slope;
  return gerepileupto(av, FlxqE_dbl_slope(P,a4, T, p,&slope));
}

static GEN
FlxqE_add_slope(GEN P, GEN Q, GEN a4, GEN T, ulong p, GEN *slope)
{
  GEN Px, Py, Qx, Qy, R;
  if (ell_is_inf(P)) return Q;
  if (ell_is_inf(Q)) return P;
  Px = gel(P,1); Py = gel(P,2);
  Qx = gel(Q,1); Qy = gel(Q,2);
  if (zv_equal(Px, Qx))
  {
    if (zv_equal(Py, Qy))
      return FlxqE_dbl_slope(P, a4, T, p, slope);
    else
      return ellinf();
  }
  *slope = Flxq_div(Flx_sub(Py, Qy, p), Flx_sub(Px, Qx, p), T, p);
  R = cgetg(3,t_VEC);
  gel(R, 1) = Flx_sub(Flx_sub(Flxq_sqr(*slope, T, p), Px, p), Qx, p);
  if (typ(a4)==t_VEC) gel(R, 1) = Flx_sub(gel(R, 1),gel(a4, 1), p);
  gel(R, 2) = Flx_sub(Flxq_mul(*slope, Flx_sub(Px, gel(R, 1), p), T, p), Py, p);
  return R;
}

GEN
FlxqE_add(GEN P, GEN Q, GEN a4, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN slope;
  return gerepileupto(av, FlxqE_add_slope(P,Q,a4, T, p,&slope));
}

static GEN
FlxqE_neg_i(GEN P, ulong p)
{
  if (ell_is_inf(P)) return P;
  return mkvec2(gel(P,1), Flx_neg(gel(P,2), p));
}

GEN
FlxqE_neg(GEN P, GEN T, ulong p)
{
  (void) T;
  if (ell_is_inf(P)) return ellinf();
  return mkvec2(gcopy(gel(P,1)), Flx_neg(gel(P,2), p));
}

GEN
FlxqE_sub(GEN P, GEN Q, GEN a4, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN slope;
  return gerepileupto(av, FlxqE_add_slope(P, FlxqE_neg_i(Q, p), a4, T, p, &slope));
}

struct _FlxqE
{
  GEN a4, a6;
  GEN T;
  ulong p;
};

static GEN
_FlxqE_dbl(void *E, GEN P)
{
  struct _FlxqE *ell = (struct _FlxqE *) E;
  return FlxqE_dbl(P, ell->a4, ell->T, ell->p);
}

static GEN
_FlxqE_add(void *E, GEN P, GEN Q)
{
  struct _FlxqE *ell=(struct _FlxqE *) E;
  return FlxqE_add(P, Q, ell->a4, ell->T, ell->p);
}

static GEN
_FlxqE_mul(void *E, GEN P, GEN n)
{
  pari_sp av = avma;
  struct _FlxqE *e=(struct _FlxqE *) E;
  long s = signe(n);
  if (!s || ell_is_inf(P)) return ellinf();
  if (s<0) P = FlxqE_neg(P, e->T, e->p);
  if (is_pm1(n)) return s>0? gcopy(P): P;
  return gerepileupto(av, gen_pow(P, n, e, &_FlxqE_dbl, &_FlxqE_add));
}

GEN
FlxqE_mul(GEN P, GEN n, GEN a4, GEN T, ulong p)
{
  struct _FlxqE E;
  E.a4= a4; E.T = T; E.p = p;
  return _FlxqE_mul(&E, P, n);
}

/* 3*x^2+2*a2*x = -a2*x, and a2!=0 */

/* Finds a random non-singular point on E */
static GEN
random_F3xqE(GEN a2, GEN a6, GEN T)
{
  pari_sp ltop = avma;
  GEN x, y, rhs;
  const ulong p=3;
  do
  {
    avma= ltop;
    x   = random_Flx(get_Flx_degree(T),get_Flx_var(T),p);
    rhs = Flx_add(Flxq_mul(Flxq_sqr(x, T, p), Flx_add(x, a2, p), T, p), a6, p);
  } while ((!lgpol(rhs) && !lgpol(x)) || !Flxq_issquare(rhs, T, p));
  y = Flxq_sqrt(rhs, T, p);
  if (!y) pari_err_PRIME("random_F3xqE", T);
  return gerepilecopy(ltop, mkvec2(x, y));
}

/* Finds a random non-singular point on E */
GEN
random_FlxqE(GEN a4, GEN a6, GEN T, ulong p)
{
  pari_sp ltop = avma;
  GEN x, x2, y, rhs;
  if (typ(a4)==t_VEC)
    return random_F3xqE(gel(a4,1), a6, T);
  do
  {
    avma= ltop;
    x   = random_Flx(get_Flx_degree(T),get_Flx_var(T),p);
    x2  = Flxq_sqr(x, T, p); /*  x^3+a4*x+a6 = x*(x^2+a4)+a6  */
    rhs = Flx_add(Flxq_mul(x, Flx_add(x2, a4, p), T, p), a6, p);
  } while ((!lgpol(rhs) && !lgpol(Flx_add(Flx_Fl_mul(x2, 3, p), a4, p)))
          || !Flxq_issquare(rhs, T, p));
  y = Flxq_sqrt(rhs, T, p);
  if (!y) pari_err_PRIME("random_FlxqE", T);
  return gerepilecopy(ltop, mkvec2(x, y));
}

static GEN
_FlxqE_rand(void *E)
{
  struct _FlxqE *ell=(struct _FlxqE *) E;
  return random_FlxqE(ell->a4, ell->a6, ell->T, ell->p);
}

static const struct bb_group FlxqE_group={_FlxqE_add,_FlxqE_mul,_FlxqE_rand,hash_GEN,zvV_equal,ell_is_inf, NULL};

const struct bb_group *
get_FlxqE_group(void ** pt_E, GEN a4, GEN a6, GEN T, ulong p)
{
  struct _FlxqE *e = (struct _FlxqE *) stack_malloc(sizeof(struct _FlxqE));
  e->a4 = a4; e->a6 = a6; e->T = Flx_get_red(T, p); e->p = p;
  *pt_E = (void *) e;
  return &FlxqE_group;
}

GEN
FlxqE_order(GEN z, GEN o, GEN a4, GEN T, ulong p)
{
  pari_sp av = avma;
  struct _FlxqE e;
  e.a4=a4; e.T=T; e.p=p;
  return gerepileuptoint(av, gen_order(z, o, (void*)&e, &FlxqE_group));
}

GEN
FlxqE_log(GEN a, GEN b, GEN o, GEN a4, GEN T, ulong p)
{
  pari_sp av = avma;
  struct _FlxqE e;
  e.a4=a4; e.T=T; e.p=p;
  return gerepileuptoint(av, gen_PH_log(a, b, o, (void*)&e, &FlxqE_group));
}

/***********************************************************************/
/**                                                                   **/
/**                            Pairings                               **/
/**                                                                   **/
/***********************************************************************/

/* Derived from APIP from and by Jerome Milan, 2012 */

static GEN
FlxqE_vert(GEN P, GEN Q, GEN T, ulong p)
{
  if (ell_is_inf(P))
    return pol1_Flx(get_Flx_var(T));
  return Flx_sub(gel(Q, 1), gel(P, 1), p);
}

/* Computes the equation of the line tangent to R and returns its
   evaluation at the point Q. Also doubles the point R.
 */

static GEN
FlxqE_tangent_update(GEN R, GEN Q, GEN a4, GEN T, ulong p, GEN *pt_R)
{
  if (ell_is_inf(R))
  {
    *pt_R = ellinf();
    return pol1_Flx(get_Flx_var(T));
  }
  else if (!lgpol(gel(R,2)))
  {
    *pt_R = ellinf();
    return FlxqE_vert(R, Q, T, p);
  } else {
    GEN slope, tmp1, tmp2;
    *pt_R = FlxqE_dbl_slope(R, a4, T, p, &slope);
    tmp1 = Flx_sub(gel(Q, 1), gel(R, 1), p);
    tmp2 = Flx_add(Flxq_mul(tmp1, slope, T, p), gel(R,2), p);
    return Flx_sub(gel(Q, 2), tmp2, p);
  }
}

/* Computes the equation of the line through R and P, and returns its
   evaluation at the point Q. Also adds P to the point R.
 */

static GEN
FlxqE_chord_update(GEN R, GEN P, GEN Q, GEN a4, GEN T, ulong p, GEN *pt_R)
{
  if (ell_is_inf(R))
  {
    *pt_R = gcopy(P);
    return FlxqE_vert(P, Q, T, p);
  }
  else if (ell_is_inf(P))
  {
    *pt_R = gcopy(R);
    return FlxqE_vert(R, Q, T, p);
  }
  else if (zv_equal(gel(P, 1), gel(R, 1)))
  {
    if (zv_equal(gel(P, 2), gel(R, 2)))
      return FlxqE_tangent_update(R, Q, a4, T, p, pt_R);
    else
    {
      *pt_R = ellinf();
      return FlxqE_vert(R, Q, T, p);
    }
  } else {
    GEN slope, tmp1, tmp2;
    *pt_R = FlxqE_add_slope(P, R, a4, T, p, &slope);
    tmp1  = Flxq_mul(Flx_sub(gel(Q, 1), gel(R, 1), p), slope, T, p);
    tmp2  = Flx_add(tmp1, gel(R, 2), p);
    return Flx_sub(gel(Q, 2), tmp2, p);
  }
}

/* Returns the Miller function f_{m, Q} evaluated at the point P using
   the standard Miller algorithm.
 */

struct _FlxqE_miller
{
  ulong p;
  GEN T, a4, P;
};

static GEN
FlxqE_Miller_dbl(void* E, GEN d)
{
  struct _FlxqE_miller *m = (struct _FlxqE_miller *)E;
  ulong p  = m->p;
  GEN T = m->T, a4 = m->a4, P = m->P;
  GEN v, line;
  GEN num = Flxq_sqr(gel(d,1), T, p);
  GEN denom = Flxq_sqr(gel(d,2), T, p);
  GEN point = gel(d,3);
  line = FlxqE_tangent_update(point, P, a4, T, p, &point);
  num  = Flxq_mul(num, line, T, p);
  v = FlxqE_vert(point, P, T, p);
  denom = Flxq_mul(denom, v, T, p);
  return mkvec3(num, denom, point);
}

static GEN
FlxqE_Miller_add(void* E, GEN va, GEN vb)
{
  struct _FlxqE_miller *m = (struct _FlxqE_miller *)E;
  ulong p = m->p;
  GEN T = m->T, a4 = m->a4, P = m->P;
  GEN v, line, point;
  GEN na = gel(va,1), da = gel(va,2), pa = gel(va,3);
  GEN nb = gel(vb,1), db = gel(vb,2), pb = gel(vb,3);
  GEN num   = Flxq_mul(na, nb, T, p);
  GEN denom = Flxq_mul(da, db, T, p);
  line = FlxqE_chord_update(pa, pb, P, a4, T, p, &point);
  num  = Flxq_mul(num, line, T, p);
  v = FlxqE_vert(point, P, T, p);
  denom = Flxq_mul(denom, v, T, p);
  return mkvec3(num, denom, point);
}

static GEN
FlxqE_Miller(GEN Q, GEN P, GEN m, GEN a4, GEN T, ulong p)
{
  pari_sp ltop = avma;
  struct _FlxqE_miller d;
  GEN v, num, denom, g1;

  d.a4 = a4; d.T = T; d.p = p; d.P = P;
  g1 = pol1_Flx(get_Flx_var(T));
  v = gen_pow(mkvec3(g1,g1,Q), m, (void*)&d, FlxqE_Miller_dbl, FlxqE_Miller_add);
  num = gel(v,1); denom = gel(v,2);
  if (!lgpol(num) || !lgpol(denom)) { avma = ltop; return NULL; }
  return gerepileupto(ltop, Flxq_div(num, denom, T, p));
}

GEN
FlxqE_weilpairing(GEN P, GEN Q, GEN m, GEN a4, GEN T, ulong p)
{
  pari_sp ltop = avma;
  GEN num, denom, result;
  if (ell_is_inf(P) || ell_is_inf(Q) || zv_equal(P,Q))
    return pol1_Flx(get_Flx_var(T));
  num    = FlxqE_Miller(P, Q, m, a4, T, p);
  if (!num) return pol1_Flx(get_Flx_var(T));
  denom  = FlxqE_Miller(Q, P, m, a4, T, p);
  if (!denom) {avma = ltop; return pol1_Flx(get_Flx_var(T)); }
  result = Flxq_div(num, denom, T, p);
  if (mpodd(m))
    result  = Flx_neg(result, p);
  return gerepileupto(ltop, result);
}

GEN
FlxqE_tatepairing(GEN P, GEN Q, GEN m, GEN a4, GEN T, ulong p)
{
  GEN num;
  if (ell_is_inf(P) || ell_is_inf(Q))
    return pol1_Flx(get_Flx_var(T));
  num = FlxqE_Miller(P, Q, m, a4, T, p);
  return num? num: pol1_Flx(get_Flx_var(T));
}

static GEN
_FlxqE_pairorder(void *E, GEN P, GEN Q, GEN m, GEN F)
{
  struct _FlxqE *e = (struct _FlxqE *) E;
  return  Flxq_order(FlxqE_weilpairing(P,Q,m,e->a4,e->T,e->p), F, e->T, e->p);
}

GEN
Flxq_ellgroup(GEN a4, GEN a6, GEN N, GEN T, ulong p, GEN *pt_m)
{
  struct _FlxqE e;
  GEN q = powuu(p, get_Flx_degree(T));
  e.a4=a4; e.a6=a6; e.T=T; e.p=p;
  return gen_ellgroup(N, subis(q,1), pt_m, (void*)&e, &FlxqE_group, _FlxqE_pairorder);
}

GEN
Flxq_ellgens(GEN a4, GEN a6, GEN ch, GEN D, GEN m, GEN T, ulong p)
{
  GEN P;
  pari_sp av = avma;
  struct _FlxqE e;
  e.a4=a4; e.a6=a6; e.T=T; e.p=p;
  switch(lg(D)-1)
  {
  case 1:
    P = gen_gener(gel(D,1), (void*)&e, &FlxqE_group);
    P = mkvec(FlxqE_changepoint(P, ch, T, p));
    break;
  default:
    P = gen_ellgens(gel(D,1), gel(D,2), m, (void*)&e, &FlxqE_group, _FlxqE_pairorder);
    gel(P,1) = FlxqE_changepoint(gel(P,1), ch, T, p);
    gel(P,2) = FlxqE_changepoint(gel(P,2), ch, T, p);
    break;
  }
  return gerepilecopy(av, P);
}
/***********************************************************************/
/**                                                                   **/
/**                          Point counting                           **/
/**                                                                   **/
/***********************************************************************/

static GEN _can_invl(void *E, GEN V) {(void) E; return V; }

static GEN _can_lin(void *E, GEN F, GEN V, GEN q)
{
  GEN v = RgX_splitting(V, 3);
  (void) E;
  return FpX_sub(V,ZXV_dotproduct(v, F), q);
}

static GEN
_can_iter(void *E, GEN f, GEN q)
{
  GEN h = RgX_splitting(f,3);
  GEN h1s = ZX_sqr(gel(h,1)), h2s = ZX_sqr(gel(h,2)), h3s = ZX_sqr(gel(h,3));
  GEN h12 = ZX_mul(gel(h,1), gel(h,2));
  GEN h13 = ZX_mul(gel(h,1), gel(h,3));
  GEN h23 = ZX_mul(gel(h,2), gel(h,3));
  GEN h1c = ZX_mul(gel(h,1), h1s);
  GEN h3c = ZX_mul(gel(h,3), h3s);
  GEN th = ZX_mul(ZX_sub(h2s,ZX_mulu(h13,3)),gel(h,2));
  GEN y = FpX_sub(f,ZX_add(RgX_shift(h3c,2),ZX_add(RgX_shift(th,1),h1c)),q);
  (void) E;
  return mkvecn(7,y,h1s,h2s,h3s,h12,h13,h23);
}

static GEN
_can_invd(void *E, GEN V, GEN v, GEN qM, long M)
{
  GEN h1s=gel(v,2), h2s=gel(v,3), h3s=gel(v,4);
  GEN h12=gel(v,5), h13=gel(v,6), h23=gel(v,7);
  GEN F = mkvec3(ZX_sub(h1s,RgX_shift(h23,1)),RgX_shift(ZX_sub(h2s,h13),1),
                 ZX_sub(RgX_shift(h3s,2),RgX_shift(h12,1)));
  (void)E;
  return gen_ZpX_Dixon(ZXV_Z_mul(F, utoi(3)), V, qM, utoi(3), M, NULL,
                                                 _can_lin, _can_invl);
}

static GEN
F3x_canonlift(GEN P, long n)
{ return gen_ZpX_Newton(Flx_to_ZX(P),utoi(3), n, NULL, _can_iter, _can_invd); }

static GEN
ZpXQ_frob(GEN x, GEN Xm, GEN T, GEN q, ulong p)
{
  long n = get_FpX_degree(T);
  GEN V = RgX_blocks(RgX_inflate(x, p), n, p);
  GEN W = ZXV_dotproduct(V, Xm);
  return FpX_rem(W, T, q);
}

struct _lift_lin
{
  ulong p;
  GEN sqx, Tp;
  GEN ai, Xm;
};

static GEN _lift_invl(void *E, GEN x)
{
  struct _lift_lin *d = (struct _lift_lin *) E;
  GEN T = d->Tp;
  ulong p = d->p;
  GEN xai = Flxq_mul(ZX_to_Flx(x, p), d->ai, T, p);
  return Flx_to_ZX(Flxq_lroot_fast(xai, d->sqx, T, p));
}

static GEN _lift_lin(void *E, GEN F, GEN x2, GEN q)
{
  struct _lift_lin *d = (struct _lift_lin *) E;
  pari_sp av = avma;
  GEN T = gel(F,3), Xm = gel(F,4);
  GEN y2  = ZpXQ_frob(x2, Xm, T, q, d->p);
  GEN lin = FpX_add(ZX_mul(gel(F,1), y2), ZX_mul(gel(F,2), x2), q);
  return gerepileupto(av, FpX_rem(lin, T, q));
}

static GEN
FpM_FpXV_bilinear(GEN P, GEN X, GEN Y, GEN p)
{
   pari_sp av = avma;
   GEN s =  ZX_mul(FpXV_FpC_mul(X,gel(P,1),p),gel(Y,1));
   long i, l = lg(P);
   for(i=2; i<l; i++)
     s = ZX_add(s, ZX_mul(FpXV_FpC_mul(X,gel(P,i),p),gel(Y,i)));
   return gerepileupto(av, FpX_red(s, p));
}

static GEN
FpM_FpXQV_bilinear(GEN P, GEN X, GEN Y, GEN T, GEN p)
{
  return FpX_rem(FpM_FpXV_bilinear(P,X,Y,p),T,p);
}

static GEN
FpXC_powderiv(GEN M, GEN p)
{
  long i, l;
  long v = varn(gel(M,2));
  GEN m = cgetg_copy(M, &l);
  gel(m,1) = pol_0(v);
  gel(m,2) = pol_1(v);
  for(i=2; i<l-1; i++)
    gel(m,i+1) = FpX_Fp_mul(gel(M,i),utoi(i), p);
  return m;
}

struct _lift_iso
{
  GEN phi;
  GEN Xm,T;
  GEN sqx, Tp;
  ulong p;
};

static GEN
_lift_iter(void *E, GEN x2, GEN q)
{
  struct _lift_iso *d = (struct _lift_iso *) E;
  ulong p = d->p;
  GEN TN = FpXT_red(d->T, q), XN = FpXV_red(d->Xm, q);
  GEN y2 = ZpXQ_frob(x2, XN, TN, q, p);
  GEN xp = FpXQ_powers(x2, p, TN, q);
  GEN yp = FpXQ_powers(y2, p, TN, q);
  GEN V  = FpM_FpXV_bilinear(d->phi,xp,yp,q);
  V = FpX_rem(V,TN,q);
  return mkvec3(V,xp,yp);
}

static GEN
_lift_invd(void *E, GEN V, GEN v, GEN qM, long M)
{
  struct _lift_iso *d = (struct _lift_iso *) E;
  struct _lift_lin e;
  ulong p = d->p;
  GEN TM = FpXT_red(d->T, qM), XM = FpXV_red(d->Xm, qM);
  GEN xp = FpXV_red(gel(v,2), qM);
  GEN yp = FpXV_red(gel(v,3), qM);
  GEN Dx = FpM_FpXQV_bilinear(d->phi, FpXC_powderiv(xp, qM), yp, TM, qM);
  GEN Dy = FpM_FpXQV_bilinear(d->phi, xp, FpXC_powderiv(yp, qM), TM, qM);
  GEN F = mkvec4(Dy, Dx, TM, XM);
  e.ai = Flxq_inv(ZX_to_Flx(Dy,p),d->Tp,p);
  e.sqx = d->sqx; e.Tp = d->Tp; e.p=p; e.Xm = XM;
  return gen_ZpX_Dixon(F,V,qM,utoi(p),M,(void*) &e, _lift_lin, _lift_invl);
}

static GEN
lift_isogeny(GEN phi, GEN x0, long n, GEN Xm, GEN T, GEN sqx, GEN Tp, ulong p)
{
  struct _lift_iso d;
  d.phi=phi;
  d.Xm=Xm; d.T=T;
  d.sqx=sqx; d.Tp=Tp; d.p=p;
  return gen_ZpX_Newton(x0, utoi(p), n,(void*)&d, _lift_iter, _lift_invd);
}

static GEN
getc2(GEN act, GEN X, GEN T, GEN q, long N)
{
  GEN A1 = RgV_to_RgX(gel(act,1),0), A2 =  RgV_to_RgX(gel(act,2),0);
  long n = brent_kung_optpow(maxss(degpol(A1),degpol(A2)),2,1);
  GEN xp = FpXQ_powers(X,n,T,q);
  GEN P  = FpX_FpXQV_eval(A1, xp, T, q);
  GEN Q  = FpX_FpXQV_eval(A2, xp, T, q);
  return FpXQ_mul(P,ZpXQ_inv(Q,T,utoi(3),N),T,q);
}

/* Assume a = 1 [p], return the square root of the norm */
static GEN
ZpXQ_sqrtnorm(GEN a, GEN T, GEN p, long e)
{
  GEN pe = powiu(p,e);
  GEN s = Fp_div(FpXQ_trace(ZpXQ_log(a, T, p, e), T, pe), gen_2, pe);
  return modii(gel(Qp_exp(cvtop(s, p, e-1)),4),pe);
}

/*
  These polynomials were extracted from the ECHIDNA databases
  available at <http://echidna.maths.usyd.edu.au/echidna/>
  and computed by David R. Kohel.
*/

static GEN
get_Kohel_polynomial(ulong p, GEN *act)
{
  switch(p)
  {
  case 3:
    *act = mkvec2(mkcol4s(1, -483,-21141,-59049),
        mkcol4s(1, 261, 4347, -6561));
    return mkvec4( mkcol4s(0,0,0,1),
        mkcol4s(-1,-36,-270,0),
        mkcol4s(0,-729, -26244,0),
        mkcol4s(0,0,-531441,0));
  }
  *act = NULL;
  return NULL;
}

static GEN
F3xq_elltrace_Harley(GEN a6, GEN T)
{
  pari_sp av = avma, av2;
  pari_timer ti;
  long n = get_Flx_degree(T), N = (n+4)/2;
  GEN q = powuu(3, N), p = utoi(3);
  GEN T2, Xm, s1, c2, t, lr;
  GEN S1, sqx;
  GEN act, phi = get_Kohel_polynomial(3, &act);
  timer_start(&ti);
  T2 = F3x_canonlift(get_Flx_mod(T),N);
  if (DEBUGLEVEL) timer_printf(&ti,"Teich");
  T2 = FpX_get_red(T2, q); T = ZXT_to_FlxT(T2, 3);
  av2 = avma;
  if (DEBUGLEVEL) timer_printf(&ti,"Barrett");
  Xm = FpXQ_powers(monomial(gen_1,n,get_FpX_var(T2)),2,T2,q);
  if (DEBUGLEVEL) timer_printf(&ti,"Xm");
  s1 = Flx_neg(a6,3);
  lr = Flxq_lroot(polx_Flx( get_Flx_var(T)), T, 3);
  sqx = Flxq_powers(lr, 2, T, 3);
  S1 = lift_isogeny(phi, Flx_to_ZX(s1), N, Xm, T2, sqx, T, 3);
  if (DEBUGLEVEL) timer_printf(&ti,"Lift invariant");
  c2 = gerepileupto(av2, getc2(act,S1,T2,q,N));
  if (DEBUGLEVEL) timer_printf(&ti,"c2");
  t = Fp_center(ZpXQ_sqrtnorm(c2,T2,p,N),q,shifti(q,-1));
  if (DEBUGLEVEL) timer_printf(&ti,"Norm");
  return gerepileupto(av, umodiu(t,3)==1 ? t: negi(t));
}

/***************************************************************************/
/*                                                                         */
/*                          Shanks Mestre                                  */
/*                                                                         */
/***************************************************************************/

/* Return the lift of a (mod b), which is closest to h */
static GEN
closest_lift(GEN a, GEN b, GEN h)
{
  return addii(a, mulii(b, diviiround(subii(h,a), b)));
}

static GEN
FlxqE_find_order(GEN f, GEN h, GEN bound, GEN B, GEN a4, GEN T, ulong p)
{
  pari_sp av = avma, av1, lim;
  pari_timer Ti;
  long s = itos( gceil(gsqrt(gdiv(bound,B),DEFAULTPREC)) ) >> 1;
  GEN tx, ti;
  GEN fh = FlxqE_mul(f, h, a4, T, p);
  GEN F, P = fh, fg;
  long i;
  if (DEBUGLEVEL) timer_start(&Ti);
  if (ell_is_inf(fh)) return h;
  F = FlxqE_mul(f, B, a4, T, p);
  if (s < 3)
  { /* we're nearly done: naive search */
    GEN Q = P;
    for (i=1;; i++)
    {
      P = FlxqE_add(P, F, a4, T, p); /* h.f + i.F */
      if (ell_is_inf(P)) return gerepileupto(av, addii(h, mului(i,B)));
      Q = FlxqE_sub(Q, F, a4, T, p); /* h.f - i.F */
      if (ell_is_inf(Q)) return gerepileupto(av, subii(h, mului(i,B)));
    }
  }
  tx = cgetg(s+1,t_VECSMALL);
  /* Baby Step/Giant Step */
  av1 = avma; lim = stack_lim(av1,3);
  for (i=1; i<=s; i++)
  { /* baby steps */
    tx[i] = hash_GEN(gel(P, 1));
    P = FlxqE_add(P, F, a4, T, p); /* h.f + i.F */
    if (ell_is_inf(P)) return gerepileupto(av, addii(h, mului(i,B)));
    if (low_stack(lim, stack_lim(av1,3)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"[ellap3] baby steps, i=%ld",i);
      P = gerepileupto(av1,P);
    }
  }
  if (DEBUGLEVEL) timer_printf(&Ti, "[ellap3] baby steps, s = %ld",s);
  /* giant steps: fg = s.F */
  fg = gerepileupto(av1, FlxqE_sub(P, fh, a4, T, p));
  if (ell_is_inf(fg)) return gerepileupto(av,mului(s,B));
  ti = vecsmall_indexsort(tx); /* = permutation sorting tx */
  tx = perm_mul(tx,ti);
  if (DEBUGLEVEL) timer_printf(&Ti, "[ellap3] sorting");
  av1 = avma; lim = stack_lim(av1,3);
  for (P=fg, i=1; ; i++)
  {
    long k = hash_GEN(gel(P,1));
    long r = zv_search(tx, k);
    if (r)
    {
      while (tx[r] == k && r) r--;
      for (r++; tx[r] == k && r <= s; r++)
      {
        long j = ti[r]-1;
        GEN Q = FlxqE_add(FlxqE_mul(F, stoi(j), a4, T, p), fh, a4, T, p);
        if (DEBUGLEVEL) timer_printf(&Ti, "[ellap3] giant steps, i = %ld",i);
        if (zv_equal(gel(P,1), gel(Q,1)))
        {
          if (zv_equal(gel(P,2), gel(Q,2))) i = -i;
          return gerepileupto(av,addii(h, mulii(addis(mulss(s,i), j), B)));
        }
      }
    }
    P = FlxqE_add(P,fg,a4,T,p);
    if (low_stack(lim, stack_lim(av1,3)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"[ellap3] giants steps, i=%ld",i);
      P = gerepileupto(av1,P);
    }
  }
}

static void
Flx_next(GEN t, ulong p)
{
  long i;
  for(i=2;;i++)
    if ((ulong)t[i]==p-1)
      t[i]=0;
    else
    {
      t[i]++;
      break;
    }
}

static void
Flx_renormalize_ip(GEN x, long lx)
{
  long i;
  for (i = lx-1; i>=2; i--)
    if (x[i]) break;
  setlg(x, i+1);
}

static ulong
F3xq_ellcard_naive(GEN a2, GEN a6, GEN T)
{
  pari_sp av = avma;
  long i, d = get_Flx_degree(T), lx = d+2;
  long q = upowuu(3, d), a;
  GEN x = const_vecsmall(lx,0); x[1] = get_Flx_var(T);
  for(a=1, i=0; i<q; i++)
  {
    GEN rhs;
    Flx_renormalize_ip(x, lx);
    rhs = Flx_add(Flxq_mul(Flxq_sqr(x, T, 3), Flx_add(x, a2, 3), T, 3), a6, 3);
    if (!lgpol(rhs)) a++; else if (Flxq_issquare(rhs, T, 3)) a+=2;
    Flx_next(x, 3);
  }
  avma = av;
  return a;
}

static ulong
Flxq_ellcard_naive(GEN a4, GEN a6, GEN T, ulong p)
{
  pari_sp av = avma;
  long i, d = get_Flx_degree(T), lx = d+2;
  long q = upowuu(p, d), a;
  GEN x = const_vecsmall(lx,0); x[1] = get_Flx_var(T);
  for(a=1, i=0; i<q; i++)
  {
    GEN x2, rhs;
    Flx_renormalize_ip(x, lx);
    x2  = Flxq_sqr(x, T, p);
    rhs = Flx_add(Flxq_mul(x, Flx_add(x2, a4, p), T, p), a6, p);
    if (!lgpol(rhs)) a++; else if (Flxq_issquare(rhs,T,p)) a+=2;
    Flx_next(x,p);
  }
  avma = av;
  return a;
}

static GEN
Flxq_ellcard_Shanks(GEN a4, GEN a6, GEN q, GEN T, ulong p)
{
  pari_sp av = avma;
  long vn = get_Flx_var(T);
  long i, twistp, twistpold=0;
  GEN h,f, ta4, u, x, A, B;
  long n = get_Flx_degree(T);
  GEN q1p = addsi(1, q), q2p = shifti(q1p, 1);
  GEN bound = addis(sqrti(gmul2n(q,4)), 1); /* ceil( 4sqrt(q) ) */
  /* once #E(Flxq) is know mod B >= bound, it is completely determined */
  /* how many 2-torsion points ? */
  switch(FlxqX_nbroots(mkpoln(4, pol1_Flx(vn), pol0_Flx(vn), a4, a6), T, p))
  {
  case 3:  A = gen_0; B = utoipos(4); break;
  case 1:  A = gen_0; B = gen_2; break;
  default: A = gen_1; B = gen_2; break; /* 0 */
  }
  h = closest_lift(A, B, q1p);
  for(;;)
  {
    do
    { /* look for points alternatively on E and its quadratic twist E' */
      x = random_Flx(n,vn,p);
      u = Flx_add(a6, Flxq_mul(Flx_add(a4, Flxq_sqr(x, T, p), p), x , T, p), p);
      twistp = Flxq_issquare(u, T, p);
    } while (twistp == twistpold);
    twistpold = twistp;
    /* [ux, u^2] is on E_u: y^2 = x^3 + c4 u^2 x + c6 u^3
     * E_u isomorphic to E (resp. E') iff twistp = 1 (resp. -1)
     * #E(F_p) = p+1 - a_p, #E'(F_p) = p+1 + a_p
     *
     * #E_u(Flxq) = A (mod B),  h is close to #E_u(Flxq) */

    f = mkvec2(Flxq_mul(u, x, T, p), Flxq_sqr(u, T, p));
    ta4 = Flxq_mul(a4, gel(f,2), T, p); /* a4 for E_u */
    h = FlxqE_find_order(f, h, bound, B, ta4,T,p);
    h = FlxqE_order(f, h, ta4, T, p);
    /* h | #E_u(Flxq) = A (mod B) */
    if (B == gen_1)
      B = h;
    else
      A = Z_chinese_all(A, gen_0, B, h, &B);

    i = (cmpii(B, bound) < 0);
    /* If we are not done, update A mod B for the _next_ curve, isomorphic to
     * the quadratic twist of this one */
    if (i) A = remii(subii(q2p,A), B); /* #E(Fq)+#E'(Fq) = 2q+2 */

    /* h = A mod B, closest lift to p+1 */
    h = closest_lift(A, B, q1p);
    if (!i) break;
  }
  return gerepileuptoint(av, twistp? h: subii(shifti(q1p,1),h));
}

static GEN
F3xq_ellcard(GEN a2, GEN a6, GEN T)
{
  long n = get_Flx_degree(T);
  if (n <= 2)
    return utoi(F3xq_ellcard_naive(a2, a6, T));
  else
  {
    GEN q1 = addis(powuu(3, get_Flx_degree(T)), 1), t;
    GEN a = Flxq_div(a6,Flxq_powu(a2,3,T,3),T,3);
    if (Flx_equal1(Flxq_powu(a, 8, T, 3)))
    {
      GEN P = Flxq_minpoly(a,T,3);
      long dP = degpol(P); /* dP <= 2 */
      ulong q = upowuu(3,dP);
      GEN A2 = pol1_Flx(P[1]), A6 = Flx_rem(polx_Flx(P[1]), P, 3);
      long tP = q + 1 - F3xq_ellcard_naive(A2, A6, P);
      t = elltrace_extension(stoi(tP), n/dP, utoi(q));
      if (umodiu(t, 3)!=1) t = negi(t);
    }
    else t = F3xq_elltrace_Harley(a, T);
    return Flx_equal1(a2) || Flxq_issquare(a2,T,3) ? subii(q1,t): addii(q1,t);
  }
}

GEN
Flxq_ellj(GEN a4, GEN a6, GEN T, ulong p)
{
  pari_sp av=avma;
  if (p==3)
  {
    GEN J;
    if (typ(a4)!=t_VEC) return pol0_Flx(get_Flx_var(T));
    J = Flxq_div(Flxq_powu(gel(a4,1),3, T, p),Flx_neg(a6,p), T, p);
    return gerepileuptoleaf(av, J);
  }
  else
  {
    pari_sp av=avma;
    GEN a43 = Flxq_mul(a4,Flxq_sqr(a4,T,p),T,p);
    GEN a62 = Flxq_sqr(a6,T,p);
    GEN num = Flx_mulu(a43,6912,p);
    GEN den = Flx_add(Flx_mulu(a43,4,p),Flx_mulu(a62,27,p),p);
    return gerepileuptoleaf(av, Flxq_div(num, den, T, p));
  }
}

static GEN
Flxq_ellcardj(GEN a4, GEN a6, ulong j, GEN T, GEN q, ulong p, long n)
{
  GEN q1 = addis(q,1);
  if (j==0 && p!=3)
  {
    ulong w;
    GEN W, t, N;
    if (umodiu(q,6)!=1) return q1;
    N = Fp_ffellcard(gen_0,gen_1,q,n,utoi(p));
    t = subii(q1, N);
    W = Flxq_pow(a6,diviuexact(shifti(q,-1), 3),T,p);
    if (degpol(W)>0) /*p=5 mod 6*/
      return Flx_equal1(Flxq_powu(W,3,T,p)) ? addii(q1,shifti(t,-1)):
                                              subii(q1,shifti(t,-1));
    w = W[2];
    if (w==1)   return N;
    if (w==p-1) return addii(q1,t);
    else /*p=1 mod 6*/
    {
      GEN u = shifti(t,-1), v = sqrtint(diviuexact(subii(q,sqri(u)),3));
      GEN a = addii(u,v), b = shifti(v,1);
      if (Fl_powu(w,3,p)==1)
      {
        if (Fl_add(umodiu(a,p),Fl_mul(w,umodiu(b,p),p),p)==0)
          return subii(q1,subii(shifti(b,1),a));
        else
          return addii(q1,addii(a,b));
      }
      else
      {
        if (Fl_sub(umodiu(a,p),Fl_mul(w,umodiu(b,p),p),p)==0)
          return subii(q1,subii(a,shifti(b,1)));
        else
          return subii(q1,addii(a,b));
      }
    }
  } else if (j==1728%p)
  {
    ulong w;
    GEN W, N, t;
    if (mod4(q)==3) return q1;
    W = Flxq_pow(a4,shifti(q,-2),T,p);
    if (degpol(W)>0) return q1; /*p=3 mod 4*/
    w = W[2];
    N = Fp_ffellcard(gen_1,gen_0,q,n,utoi(p));
    if(w==1) return N;
    t = subii(q1, N);
    if(w==p-1) return addii(q1, t);
    else /*p=1 mod 4*/
    {
      GEN u = shifti(t,-1), v = sqrtint(subii(q,sqri(u)));
      if (Fl_add(umodiu(u,p),Fl_mul(w,umodiu(v,p),p),p)==0)
        return subii(q1,shifti(v,1));
      else
        return addii(q1,shifti(v,1));
    }
  } else
  {
    ulong g = Fl_div(j, Fl_sub(1728%p, j, p), p);
    GEN l = Flxq_div(Flx_Fl_mul(a6,3,p),Flx_Fl_mul(a4,2,p),T,p);
    GEN N = Fp_ffellcard(utoi(Fl_mul(g,3,p)),utoi(Fl_mul(g,2,p)),q,n,utoi(p));
    if (Flxq_issquare(l,T,p)) return N;
    return subii(shifti(q1,1),N);
  }
}

GEN
Flxq_ellcard(GEN a4, GEN a6, GEN T, ulong p)
{
  pari_sp av = avma;
  long n = get_Flx_degree(T);
  GEN J, r, q = powuu(p,  n);
  if (typ(a4)==t_VEC)
    r = F3xq_ellcard(gel(a4,1), a6, T);
  else if (degpol(a4)<=0 && degpol(a6)<=0)
    r = Fp_ffellcard(utoi(Flx_eval(a4,0,p)),utoi(Flx_eval(a6,0,p)),q,n,utoi(p));
  else if (degpol(J=Flxq_ellj(a4,a6,T,p))<=0)
    r = Flxq_ellcardj(a4,a6,lgpol(J)?J[2]:0,T,q,p,n);
  else if (cmpis(q,100)<0)
    r = utoi(Flxq_ellcard_naive(a4, a6, T, p));
  else if (expi(q)<=62)
    r = Flxq_ellcard_Shanks(a4, a6, q, T, p);
  else
  {
    r = Fq_ellcard_SEA(Flx_to_ZX(a4),Flx_to_ZX(a6),q,Flx_to_ZX(T),utoi(p),0);
    if (!r) pari_err_PACKAGE("seadata");
  }
  return gerepileuptoint(av, r);
}
