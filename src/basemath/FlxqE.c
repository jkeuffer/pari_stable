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
/**                              FlxqE                                  **/
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
  *slope = Flxq_div(Flx_add(Flx_Fl_mul(Flxq_sqr(x, T, p), 3, p), a4, p),
                  Flx_Fl_mul(y, 2, p), T, p);
  Q = cgetg(3,t_VEC);
  gel(Q, 1) = Flx_sub(Flxq_sqr(*slope, T, p), Flx_Fl_mul(x, 2, p), p),
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
FlxqE_neg_i(GEN P, GEN T, ulong p)
{
  if (ell_is_inf(P)) return P;
  return mkvec2(gel(P,1), Flx_neg(gel(P,2), p));
}

GEN
FlxqE_neg(GEN P, GEN T, ulong p)
{
  if (ell_is_inf(P)) return ellinf();
  return mkvec2(gcopy(gel(P,1)), Flx_neg(gel(P,2), p));
}

GEN
FlxqE_sub(GEN P, GEN Q, GEN a4, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN slope;
  return gerepileupto(av, FlxqE_add_slope(P, FlxqE_neg_i(Q, T, p), a4, T, p, &slope));
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

/* Finds a random non-singular point on E */
GEN
random_FlxqE(GEN a4, GEN a6, GEN T, ulong p)
{
  pari_sp ltop = avma;
  GEN x, x2, y, rhs;
  do
  {
    avma= ltop;
    x   = random_Flx(degpol(T),T[1],p); /*  x^3+a4*x+a6 = x*(x^2+a4)+a6  */
    x2  = Flxq_sqr(x, T, p);
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
  e->a4 = a4; e->a6 = a6; e->T = T; e->p = p;
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
    return pol1_Flx(T[1]);
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
    return pol1_Flx(T[1]);
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
  g1 = pol1_Flx(T[1]);
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
    return pol1_Flx(T[1]);
  num    = FlxqE_Miller(P, Q, m, a4, T, p);
  if (!num) return pol1_Flx(T[1]);
  denom  = FlxqE_Miller(Q, P, m, a4, T, p);
  if (!denom) {avma = ltop; return pol1_Flx(T[1]); }
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
    return pol1_Flx(T[1]);
  num = FlxqE_Miller(P, Q, m, a4, T, p);
  return num? num: pol1_Flx(T[1]);
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
  GEN q = powuu(p, degpol(T));
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
Flxq_ellcard_naive(GEN a4, GEN a6, GEN T, ulong p)
{
  pari_sp av = avma;
  long i, d = degpol(T), lx = d+2;
  long q = upowuu(p, d), a;
  GEN x = const_vecsmall(lx,0); x[1] = T[1];
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
  long vn = T[1];
  long i, twistp, twistpold=0;
  GEN h,f, ta4, u, x, A, B;
  long n = degpol(T);
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

GEN
Flxq_ellcard(GEN a4, GEN a6, GEN T, ulong p)
{
  pari_sp av = avma;
  long n = degpol(T);
  GEN r, q = powuu(p,  n);
  if (degpol(a4)<=0 && degpol(a6)<=0)
    r = Fp_ffellcard(utoi(Flx_eval(a4,0,p)),utoi(Flx_eval(a6,0,p)),q,n,utoi(p));
  else if (cmpis(q,100)<0)
    r = utoi(Flxq_ellcard_naive(a4, a6, T, p));
  else if (expi(q)<=62)
    r = Flxq_ellcard_Shanks(a4, a6, q, T, p);
  else
    r = Fq_ellcard_SEA(Flx_to_ZX(a4),Flx_to_ZX(a6),q,Flx_to_ZX(T),utoi(p),0);
  return gerepileuptoint(av, r);
}
