/* $Id: polarit2.c 10436 2008-07-11 14:08:05Z kb $

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

/***********************************************************************/
/**                                                                   **/
/**       QUADRATIC HENSEL LIFT (adapted from V. Shoup's NTL)         **/
/**                                                                   **/
/***********************************************************************/
/* Setup for divide/conquer quadratic Hensel lift
 *  a = set of k t_POL in Z[X] = factors over Fp (T=NULL) or Fp[Y]/(T)
 *  V = set of products of factors built as follows
 *  1) V[1..k] = initial a
 *  2) iterate:
 *      append to V the two smallest factors (minimal degree) in a, remove them
 *      from a and replace them by their product [net loss for a = 1 factor]
 *
 * W = bezout coeffs W[i]V[i] + W[i+1]V[i+1] = 1
 *
 * link[i] = -j if V[i] = a[j]
 *            j if V[i] = V[j] * V[j+1]
 * Arrays (link, V, W) pre-allocated for 2k - 2 elements */
static void
BuildTree(GEN link, GEN V, GEN W, GEN a, GEN T, GEN p)
{
  long k = lg(a)-1;
  long i, j, s, minp, mind;

  for (i=1; i<=k; i++) { V[i] = a[i]; link[i] = -i; }

  for (j=1; j <= 2*k-5; j+=2,i++)
  {
    minp = j;
    mind = degpol(V[j]);
    for (s=j+1; s<i; s++)
      if (degpol(V[s]) < mind) { minp = s; mind = degpol(V[s]); }

    swap(gel(V,j), gel(V,minp));
    lswap(link[j], link[minp]);

    minp = j+1;
    mind = degpol(V[j+1]);
    for (s=j+2; s<i; s++)
      if (degpol(V[s]) < mind) { minp = s; mind = degpol(V[s]); }

    swap(gel(V,j+1), gel(V,minp));
    lswap(link[j+1], link[minp]);

    if (T)
      gel(V,i) = FpXQX_mul(gel(V,j), gel(V,j+1), T, p);
    else
      gel(V,i) = FpX_mul(gel(V,j), gel(V,j+1), p);
    link[i] = j;
  }

  for (j=1; j <= 2*k-3; j+=2)
  {
    GEN d, u, v;
    if (T)
      d = FpXQX_extgcd(gel(V,j), gel(V,j+1), T, p, &u, &v);
    else
      d = FpX_extgcd(gel(V,j), gel(V,j+1), p, &u, &v);
    if (degpol(d) > 0) pari_err(talker, "relatively prime polynomials expected");
    d = gel(d,2);
    if (!gcmp1(d))
    {
      if (typ(d)==t_POL)
      {
	d = FpXQ_inv(d, T, p);
	u = FqX_Fq_mul(u, d, T, p);
	v = FqX_Fq_mul(v, d, T, p);
      }
      else
      {
	d = Fp_inv(d, p);
	u = FpX_Fp_mul(u, d, p);
	v = FpX_Fp_mul(v, d, p);
      }
    }
    gel(W,j) = u;
    gel(W,j+1) = v;
  }
}

/* au + bv = 1 (p0), ab = f (p0). Lift mod p1 = p0 pd (<= p0^2).
 * If noinv is set, don't lift the inverses u and v */
static void
HenselLift(GEN V, GEN W, long j, GEN f, GEN T, GEN pd, GEN p0, int noinv)
{
  pari_sp av = avma;
  long space = lg(f) * (lgefint(pd) + lgefint(p0));
  GEN a2,b2,g,z,s,t;
  GEN a = gel(V,j), b = gel(V,j+1);
  GEN u = gel(W,j), v = gel(W,j+1);

  if (T) space *= lg(T);

  (void)new_chunk(space); /* HACK */
  g = RgX_sub(f, RgX_mul(a,b));
  if (T) g = FpXQX_red(g, T, mulii(p0,pd));
  g = RgX_Rg_divexact(g, p0);
  if (T)
  {
    z = FpXQX_mul(v,g, T,pd);
    t = FpXQX_divrem(z,a, T,pd, &s);
  }
  else
  {
    g = FpX_red(g, pd);
    z = FpX_mul(v,g, pd);
    t = FpX_divrem(z,a, pd, &s);
  }
  t = RgX_add(RgX_mul(u,g), RgX_mul(t,b));
  t = T? FpXQX_red(t, T, pd): FpX_red(t, pd);
  t = RgX_Rg_mul(t,p0);
  s = RgX_Rg_mul(s,p0);
  avma = av;

  /* already reduced mod p1 = pd p0 */
  a2 = RgX_add(a,s); gel(V,j) = a2;
  b2 = RgX_add(b,t); gel(V,j+1) = b2;
  if (noinv) return;

  av = avma;
  (void)new_chunk(space); /* HACK */
  g = RgX_add(RgX_mul(u,a2), RgX_mul(v,b2));
  g = Rg_RgX_sub(gen_1, g);

  if (T) g = FpXQX_red(g, T, mulii(p0,pd));
  g = RgX_Rg_divexact(g, p0);
  if (T)
  {
    z = FpXQX_mul(v,g, T,pd);
    t = FpXQX_divrem(z,a, T,pd, &s);
  }
  else
  {
    g = FpX_red(g, pd);
    z = FpX_mul(v,g, pd);
    t = FpX_divrem(z,a, pd, &s);
  }
  t = RgX_add(RgX_mul(u,g), RgX_mul(t,b));
  t = T? FpXQX_red(t, T, pd): FpX_red(t, pd);
  t = RgX_Rg_mul(t,p0);
  s = RgX_Rg_mul(s,p0);
  avma = av;

  u = RgX_add(u,t); gel(W,j) = u;
  v = RgX_add(v,s); gel(W,j+1) = v;
}

/* v list of factors, w list of inverses.  f = v[j] v[j+1]
 * Lift v[j] and v[j+1] mod p0 pd (possibly mod T), then all their divisors */
static void
RecTreeLift(GEN link, GEN v, GEN w, GEN T, GEN pd, GEN p0, GEN f, long j, int noinv)
{
  if (j < 0) return;

  HenselLift(v, w, j, f, T, pd, p0, noinv);
  RecTreeLift(link, v, w, T, pd, p0, gel(v,j)  , link[j  ], noinv);
  RecTreeLift(link, v, w, T, pd, p0, gel(v,j+1), link[j+1], noinv);
}

/* lift from p^{e0} to p^{e1} */
static void
TreeLift(GEN link, GEN v, GEN w, GEN T, GEN p, long e0, long e1, GEN f, int noinv)
{
  GEN p0 = powiu(p, e0);
  GEN pd = powiu(p, e1-e0);
  RecTreeLift(link, v, w, T, pd, p0, f, lgpol(v), noinv);
}

/* Successive accuracies for a quadratic lift.
 * Eg 9 --> 9,5,3,2,1 instead of 9,8,4,2,1 */
GEN
Newton_exponents(long e)
{
  GEN E = cgetg(BITS_IN_LONG, t_VECSMALL);
  long l = 1; E[l++] = e;
  while (e > 1) { e = (e+1)>>1; E[l++] = e; }
  setlg(E, l); return E;
}

/* lift accelerator */
long
hensel_lift_accel(long n, long *pmask)
{
  long a, j, mask = 0;
  for(j=BITS_IN_LONG-1, a=n ;; j--)
  {
    mask |= (a&1)<<j;
    a = (a+1)>>1;
    if (a==1) break;
  }
  *pmask = mask>>j;
  return BITS_IN_LONG-j;
}

/* a = modular factors of f mod (p,T) [possibly T=NULL], lift to precision p^e0
 * flag = 0: standard.
 * flag = 1: return TreeLift structure
 * flag = 2: a = TreeLift structure, go on lifting, as flag = 1 otherwise */
static GEN
MultiLift(GEN f, GEN a, GEN T, GEN p, long e0, long flag)
{
  long l, i, e = e0, k = lg(a) - 1;
  GEN E, v, w, link;
  pari_timer Ti;

  if (k < 2 || e < 1) pari_err(talker, "MultiLift: bad args");
  if (e == 1) return a;
  if (typ(a[1]) == t_INT) flag = 2;
  else if (flag == 2) flag = 1;

  E = Newton_exponents(e);
  e = 1;
  l = lg(E)-1;

  if (DEBUGLEVEL > 3) TIMERstart(&Ti);

  if (flag != 2)
  {
    v = cgetg(2*k - 2 + 1, t_VEC);
    w = cgetg(2*k - 2 + 1, t_VEC);
    link=cgetg(2*k - 2 + 1, t_VECSMALL);
    BuildTree(link, v, w, a, T, p);
    if (DEBUGLEVEL > 3) msgTIMER(&Ti, "building tree");
  }
  else
  {
    e = itos(gel(a,1));
    link = gel(a,2);
    v    = gel(a,3);
    w    = gel(a,4);
  }

  for (i = l; i > 1; i--) {
    if (E[i-1] < e) continue;
    TreeLift(link, v, w, T, p, E[i], E[i-1], f, (flag == 0) && (i == 2));
    if (DEBUGLEVEL > 3) msgTIMER(&Ti, "lifting to prec %ld", E[i-1]);
  }

  if (flag)
    E = mkvec4(stoi(e0), link, v, w);
  else
  {
    E = cgetg(k+1, t_VEC);
    for (i = 1; i <= 2*k-2; i++)
    {
      long t = link[i];
      if (t < 0) E[-t] = v[i];
    }
  }
  return E;
}

/* Q list of (coprime, monic) factors of pol mod (T,p). Lift mod p^e = pe.
 * T may be NULL */
GEN
ZpX_liftfact(GEN pol, GEN Q, GEN T, GEN p, long e, GEN pe)
{
  pari_sp av = avma;
  if (lg(Q) == 2) return mkvec(pol);
  pol = FqX_normalize(pol, T, pe);
  return gerepilecopy(av, MultiLift(pol, Q, T, p, e, 0));
}

/* U = NULL treated as 1 */
static void
BezoutPropagate(GEN link, GEN v, GEN w, GEN pe, GEN U, GEN f, long j)
{
  GEN Q, R;
  if (j < 0) return;

  Q = FpX_mul(gel(v,j), gel(w,j), pe);
  if (U)
  {
    Q = FpXQ_mul(Q, U, f, pe);
    R = FpX_sub(U, Q, pe);
  }
  else
    R = FpX_Fp_add_shallow(FpX_neg(Q, pe), gen_1, pe);
  gel(w,j+1) = Q; /*  0 mod U v[j],  1 mod (1-U) v[j+1] */
  gel(w,j) = R; /*  1 mod U v[j],  0 mod (1-U) v[j+1] */
  BezoutPropagate(link, v, w, pe, R, f, link[j  ]);
  BezoutPropagate(link, v, w, pe, Q, f, link[j+1]);
}

/* as above, but return the Bezout coefficients for the lifted modular factors
 *   U[i] = 1 mod Qlift[i]
 *          0 mod Qlift[j], j != i */
GEN
bezout_lift_fact(GEN pol, GEN Q, GEN p, long e)
{
  pari_sp av = avma;
  GEN E, link, v, w, pe;
  long i, k = lg(Q)-1;
  if (k == 1) return mkvec(pol);
  pe = powiu(p, e);
  pol = FpX_normalize(pol, pe);
  E = MultiLift(pol, Q, NULL, p, e, 1);
  link = gel(E,2);
  v    = gel(E,3);
  w    = gel(E,4);
  BezoutPropagate(link, v, w, pe, NULL, pol, lgpol(v));
  E = cgetg(k+1, t_VEC);
  for (i = 1; i <= 2*k-2; i++)
  {
    long t = link[i];
    if (t < 0) E[-t] = w[i];
  }
  return gerepilecopy(av, E);
}

/* Front-end for ZpX_liftfact:
   lift the factorization of pol mod p given by L to p^N (if possible) */
GEN
polhensellift(GEN pol, GEN L, GEN p, long N)
{
  GEN T = NULL;
  long i, l, t;
  pari_sp av = avma;

  if (typ(pol) != t_POL) pari_err(talker, "not a polynomial in polhensellift");
  RgX_check_ZXY(pol, "polhensellift");
  t = typ(L);
  if (!is_vec_t(t) || lg(L) < 3)
    pari_err(talker, "not a factorization in polhensellift");
  t = typ(p);
  if (t == t_VEC) /* [p, T] */
  {
    T = gel(p,2);
    if (typ(T) != t_POL) pari_err(talker, "incorrect T in polhensellift");
    RgX_check_ZX(T, "polhensellift");
    p = gel(p,1); t = typ(p);
  }
  if (t != t_INT) pari_err(talker, "incorrect p in polhensellift");
  if (N < 1) pari_err(talker, "not a positive exponent in polhensellift");

  l = lg(L); L = shallowcopy(L);
  for (i = 1; i < l; i++)
  {
    if (typ(gel(L,i)) != t_POL)
      gel(L,i) = scalar_ZX_shallow(gel(L,i), varn(pol));
    RgX_check_ZXY(gel(L,i), "polhensellift");
  }
  return gerepilecopy(av, ZpX_liftfact(pol, L, T, p, N, powiu(p,N)));
}

/*************************************************************************/
/*                             rootpadicfast                             */
/*************************************************************************/
/* SPEC:
 * p is a t_INT > 1, e >= 0
 * f is a ZX with leading term prime to p.
 * a is a simple root mod l for all l|p.
 * Return roots of f mod p^e, as integers (implicitly mod p^e)
 * STANDARD USE: p is a prime power */
GEN
ZpX_liftroot(GEN f, GEN a, GEN p, long e)
{
  pari_sp ltop=avma;
  GEN     qold, q, qm1;
  GEN     W, fr, Wr = gen_0;
  long    i, nb, mask;
  qold = q = p; qm1 = gen_1;
  nb = hensel_lift_accel(e, &mask);
  fr = FpX_red(f,q);
  a = modii(a,q);
  W = FpX_eval(ZX_deriv(fr), a, q);
  W = Fp_inv(W,q);
  for(i=0;i<nb;i++)
  {
    qm1 = (mask&(1<<i))?sqri(qm1):mulii(qm1, q);
    q   =  mulii(qm1, p);
    fr = FpX_red(f,q);
    if (i)
    {
      W = Fp_mul(Wr, FpX_eval(ZX_deriv(fr),a,qold), qold);
      W = Fp_mul(Wr, subsi(2,W), qold);
    }
    Wr = W;
    a = subii(a, mulii(Wr, FpX_eval(fr, a,q)));
    a = modii(a,q);
    qold = q;
  }
  return gerepileupto(ltop,a);
}
GEN
ZpXQX_liftroot(GEN f, GEN a, GEN T, GEN p, long e)
{
  pari_sp ltop=avma;
  GEN     qold, q, qm1;
  GEN     W, fr, Wr = gen_0;
  long    i, nb, mask;
  qold = p ;  q = p; qm1 = gen_1;
  nb=hensel_lift_accel(e, &mask);
  fr = FpXQX_red(f, T, q);
  a = Fq_red(a, T, q);
  W = FqX_eval(RgX_deriv(fr), a, T, q);
  W = Fq_inv(W,T,q);
  for(i=0;i<nb;i++)
  {
    qm1 = (mask&(1<<i))?sqri(qm1):mulii(qm1, q);
    q   =  mulii(qm1, p);
    fr = FpXQX_red(f,T,q);
    if (i)
    {
      W = Fq_red(gmul(Wr,FqX_eval(RgX_deriv(fr),a,T,qold)), T, qold);
      W = Fq_red(gmul(Wr, gadd(gen_2, gneg(W))), T, qold);
    }
    Wr = W;
    a = gsub(a, gmul(Wr, FqX_eval(fr, a, T, q)));
    a = Fq_red(a, T, q);
    qold = q;
  }
  return gerepileupto(ltop,a);
}
/* Apply ZpX_liftroot to all roots in S and trace trick.
 * Elements of S must be distinct simple roots mod p for all p|q. */
GEN
ZpX_liftroots(GEN f, GEN S, GEN q, long e)
{
  long i, d, l = lg(S), n = l-1;
  GEN y = cgetg(l, typ(S));
  if (!n) return y;
  for (i=1; i<n; i++)
    gel(y,i) = ZpX_liftroot(f, gel(S,i), q, e);
  d = degpol(f);
  if (n != d) /* not totally split*/
    gel(y,n) = ZpX_liftroot(f, gel(S,n), q, e);
  else
  { /* totally split: use trace trick */
    pari_sp av = avma;
    GEN z = gel(f, d+1);/* -trace(roots) */
    for(i=1; i<n;i++) z = addii(z, gel(y,i));
    z = modii(negi(z), powiu(q,e));
    gel(y,n) = gerepileuptoint(av,z);
  }
  return y;
}

/* Same as ZpX_liftroot for the polynomial X^2-T */
GEN
padicsqrtlift(GEN T, GEN a, GEN p, long e)
{
  pari_sp ltop=avma;
  GEN q, W;
  long i, nb, mask;

  if (e == 1) return icopy(a);
  nb = hensel_lift_accel(e, &mask);
  W = Fp_inv(modii(shifti(a,1), p), p);
  q = p;
  for(i=0;;i++)
  {
    q = sqri(q);
    if (mask & (1<<i)) q = diviiexact(q, p);
    if (lgefint(q) == 3)
    {
      ulong Q = (ulong)q[2];
      ulong A = umodiu(a, Q);
      ulong t = umodiu(T, Q);
      ulong w = umodiu(W, Q);
      A = Fl_sub(A, Fl_mul(w, Fl_sub(Fl_sqr(A,Q), t, Q), Q), Q);
      a = utoi(A);
      if (i == nb-1) break;
      w = Fl_sub(Fl_add(w,w,Q), Fl_mul(Fl_sqr(w,Q), Fl_add(A,A,Q),Q), Q);
      W = utoi(w);
    }
    else
    {
      a = modii(subii(a, mulii(W, subii(Fp_sqr(a,q),T))), q);
      if (i == nb-1) break;
      W = subii(shifti(W,1), Fp_mul(Fp_sqr(W,q), shifti(a,1),q));
    }
  }
  return gerepileuptoint(ltop,a);
}
/* Same as ZpX_liftroot for the polynomial X^n-T
 * TODO: generalize to sparse polynomials. */
GEN
padicsqrtnlift(GEN T, GEN n, GEN a, GEN p, long e)
{
  pari_sp ltop=avma;
  GEN q, W;
  long i, nb, mask;

  if (equalii(n, gen_2)) return padicsqrtlift(T,a,p,e);
  nb = hensel_lift_accel(e, &mask);
  W = Fp_inv(Fp_mul(n,Fp_pow(a,subis(n,1),p), p), p);
  q = p;
  for(i=0;;i++)
  {
    q = sqri(q);
    if (mask & (1<<i)) q = diviiexact(q, p);
    a = modii(subii(a, mulii(W, subii(Fp_pow(a,n,q),T))), q);
    if (i == nb-1) break;

    W = subii(shifti(W,1),
	      Fp_mul(Fp_sqr(W,q), mulii(n,Fp_pow(a,subis(n,1),q)), q));
  }
  return gerepileuptoint(ltop,a);
}
