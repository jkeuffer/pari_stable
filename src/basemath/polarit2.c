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

/***********************************************************************/
/**                                                                   **/
/**               ARITHMETIC OPERATIONS ON POLYNOMIALS                **/
/**                         (second part)                             **/
/**                                                                   **/
/***********************************************************************/
#include "pari.h"

#define swap(a,b) { GEN _x = a; a = b; b = _x; }
#define lswap(a,b) { long _x = a; a = b; b = _x; }
#define pswap(a,b) { GEN *_x = a; a = b; b = _x; }
#define both_odd(a,b) ((a)&(b)&1)

extern GEN gassoc_proto(GEN f(GEN,GEN),GEN,GEN);

GEN
polsym(GEN x, long n)
{
  long dx=degpol(x), i, k;
  gpmem_t av1, av2;
  GEN s,y,x_lead;

  if (n<0) err(impl,"polsym of a negative n");
  if (typ(x) != t_POL) err(typeer,"polsym");
  if (!signe(x)) err(zeropoler,"polsym");
  y=cgetg(n+2,t_COL); y[1]=lstoi(dx);
  x_lead=(GEN)x[dx+2]; if (gcmp1(x_lead)) x_lead=NULL;
  for (k=1; k<=n; k++)
  {
    av1=avma; s = (dx>=k)? gmulsg(k,(GEN)x[dx+2-k]): gzero;
    for (i=1; i<k && i<=dx; i++)
      s = gadd(s,gmul((GEN)y[k-i+1],(GEN)x[dx+2-i]));
    if (x_lead) s = gdiv(s,x_lead);
    av2=avma; y[k+1]=lpile(av1,av2,gneg(s));
  }
  return y;
}

extern GEN Fq_mul(GEN x, GEN y, GEN T, GEN p);
/* compute Newton sums S_1(P), ... , S_n(P). S_k(P) = sum a_j^k, a_j root of P
 * If N != NULL, assume p-adic roots and compute mod N [assume integer coeffs]
 * If T != NULL, compute mod (T,N) [assume integer coeffs and N != NULL]
 * If y0!= NULL, precomputed i-th powers, i=1..m, m = length(y0) */
GEN
polsym_gen(GEN P, GEN y0, long n, GEN T, GEN N)
{
  long dP=degpol(P), i, k, m;
  gpmem_t av1, av2;
  GEN s,y,P_lead;

  if (n<0) err(impl,"polsym of a negative n");
  if (typ(P) != t_POL) err(typeer,"polsym");
  if (!signe(P)) err(zeropoler,"polsym");
  y = cgetg(n+2,t_COL);
  if (y0)
  {
    if (typ(y0) != t_COL) err(typeer,"polsym_gen");
    m = lg(y0)-1;
    for (i=1; i<=m; i++) y[i] = lcopy((GEN)y0[i]);
  }
  else
  {
    m = 1;
    y[1] = lstoi(dP);
  }
  P += 2; /* strip codewords */

  P_lead=(GEN)P[dP]; if (gcmp1(P_lead)) P_lead=NULL;
  if (N && P_lead) P_lead = FpXQ_inv(P_lead,T,N);
  for (k=m; k<=n; k++)
  {
    av1=avma; s = (dP>=k)? gmulsg(k,(GEN)P[dP-k]): gzero;
    for (i=1; i<k && i<=dP; i++)
      s = gadd(s, gmul((GEN)y[k-i+1],(GEN)P[dP-i]));
    if (N)
    {
      if (T)
        s = FpX_res(FpX_red(s,N), T, N);
      else
        s = modii(s, N);
      if (P_lead) s = Fq_mul(s, P_lead, T, N);
    }
    else
      if (P_lead) s = gdiv(s,P_lead);
    av2=avma; y[k+1]=lpile(av1,av2,gneg(s));
  }
  return y;
}

static int (*polcmp_coeff_cmp)(GEN,GEN);

/* assume x and y are polynomials in the same variable whose coeffs can be
 * compared (used to sort polynomial factorizations)
 */
static int
polcmp(GEN x, GEN y)
{
  long i, lx = lgef(x), ly = lgef(y);
  int fl;
#if 0 /* for efficiency */
  if (typ(x) != t_POL || typ(y) != t_POL)
    err(talker,"not a polynomial in polcmp");
#endif
  if (lx > ly) return  1;
  if (lx < ly) return -1;
  for (i=lx-1; i>1; i--)
    if ((fl = polcmp_coeff_cmp((GEN)x[i], (GEN)y[i]))) return fl;
  return 0;
}

/* sort polynomial factorization so that factors appear by decreasing
 * degree, sorting coefficients according to cmp. In place */
GEN
sort_factor(GEN y, int (*cmp)(GEN,GEN))
{
  int (*old)(GEN,GEN) = polcmp_coeff_cmp;
  polcmp_coeff_cmp = cmp;
  (void)sort_factor_gen(y,polcmp);
  polcmp_coeff_cmp = old; return y;
}

/* sort generic factorisation */
GEN
sort_factor_gen(GEN y, int (*cmp)(GEN,GEN))
{
  long n, i;
  gpmem_t av = avma;
  GEN a,b,A,B,w;
  a = (GEN)y[1]; n = lg(a); A = new_chunk(n);
  b = (GEN)y[2];            B = new_chunk(n);
  w = gen_sort(a, cmp_IND | cmp_C, cmp);
  for (i=1; i<n; i++) { A[i] = a[w[i]]; B[i] = b[w[i]]; }
  for (i=1; i<n; i++) { a[i] = A[i]; b[i] = B[i]; }
  avma = av; return y;
}

/* for internal use */
GEN
centermod_i(GEN x, GEN p, GEN ps2)
{
  long i, j, lx, hx;
  gpmem_t av;
  GEN y,p1;

  if (!ps2) ps2 = shifti(p,-1);
  switch(typ(x))
  {
    case t_INT:
      y=modii(x,p);
      if (cmpii(y,ps2)>0) return subii(y,p);
      return y;

    case t_POL: lx=lgef(x);
      y=cgetg(lx,t_POL); y[1]=x[1];
      for (i=2; i<lx; i++)
      {
	av=avma; p1=modii((GEN)x[i],p);
	if (cmpii(p1,ps2)>0) p1=subii(p1,p);
	y[i]=lpileupto(av,p1);
      }
      return normalizepol_i(y, lx);

    case t_COL: lx=lg(x);
      y=cgetg(lx,t_COL);
      for (i=1; i<lx; i++)
      {
	p1=modii((GEN)x[i],p);
	if (cmpii(p1,ps2)>0) p1=subii(p1,p);
	y[i]=(long)p1;
      }
      return y;

    case t_MAT: lx=lg(x);
      y=cgetg(lx,t_MAT);
      if (lx == 1) return y;
      hx = lg(x[1]);
      for (j=1; j<lx; j++)
      {
        GEN cx = (GEN)x[j], cy = cgetg(hx,t_COL);
        y[j] = (long)cy;
        for (i=1; i<hx; i++)
        {
          p1=modii((GEN)cx[i], p);
          if (cmpii(p1,ps2)>0) p1=subii(p1,p);
          cy[i]=(long)p1;
        }
      }
      return y;
  }
  return x;
}

GEN
centermod(GEN x, GEN p) { return centermod_i(x,p,NULL); }

/* assume same variables, y normalized, non constant */
static GEN
polidivis(GEN x, GEN y, GEN bound)
{
  long dx, dy, dz, i, j, vx = varn(x);
  gpmem_t av;
  GEN z,p1,y_lead;

  dy=degpol(y);
  dx=degpol(x);
  dz=dx-dy; if (dz<0) return NULL;
  z=cgetg(dz+3,t_POL);
  x += 2; y += 2; z += 2;
  y_lead = (GEN)y[dy];
  if (gcmp1(y_lead)) y_lead = NULL;

  p1 = (GEN)x[dx];
  z[dz]=y_lead? ldivii(p1,y_lead): licopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av=avma; p1=(GEN)x[i];
    for (j=i-dy+1; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii((GEN)z[j],(GEN)y[i-j]));
    if (y_lead) { p1 = gdiv(p1,y_lead); if (typ(p1)!=t_INT) return NULL; }
    if (absi_cmp(p1, bound) > 0) return NULL;
    p1 = gerepileupto(av,p1);
    z[i-dy] = (long)p1;
  }
  av = avma;
  for (;; i--)
  {
    p1 = (GEN)x[i];
    /* we always enter this loop at least once */
    for (j=0; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii((GEN)z[j],(GEN)y[i-j]));
    if (!gcmp0(p1)) return NULL;
    avma = av;
    if (!i) break;
  }
  z -= 2;
  z[1]=evalsigne(1) | evallgef(dz+3) | evalvarn(vx);
  return z;
}

static long
min_deg(long jmax,ulong tabbit[])
{
  long j, k = 1, j1 = 2;

  for (j=jmax; j>=0; j--)
  {
    for (  ; k<=15; k++)
    {
      if (tabbit[j]&j1) return ((jmax-j)<<4)+k;
      j1<<=1;
    }
    k = 0; j1 = 1;
  }
  return (jmax<<4)+15;
}

/* tabkbit is a bit vector (only lowest 32 bits of each word are used
 * on 64bit architecture): reading from right to left, bit i+1 is set iff
 * degree i is attainable from the factorisation mod p.
 *
 * record N modular factors of degree d. */
static void
record_factors(long N, long d, long jmax, ulong *tabkbit, ulong *tmp)
{
  long n,j, a = d>>4, b = d&15; /* d = 16 a + b */
  ulong *tmp2 = tmp - a;

  for (n = 1; n <= N; n++)
  {
    ulong pro, rem = 0;
    for (j=jmax; j>=a; j--)
    {
      pro = tabkbit[j] << b;
      tmp2[j] = (pro&0xffff) + rem; rem = pro >> 16;
    }
    for (j=jmax-a; j>=0; j--) tabkbit[j] |= tmp[j];
  }
}

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

    lswap(V[j], V[minp]);
    lswap(link[j], link[minp]);

    minp = j+1;
    mind = degpol(V[j+1]);
    for (s=j+2; s<i; s++)
      if (degpol(V[s]) < mind) { minp = s; mind = degpol(V[s]); }

    lswap(V[j+1], V[minp]);
    lswap(link[j+1], link[minp]);

    V[i] = (long)FpXQX_mul((GEN)V[j], (GEN)V[j+1], T, p);
    link[i] = j;
  }

  for (j=1; j <= 2*k-3; j+=2)
  {
    GEN d, u, v;
    d = FpXQX_extgcd((GEN)V[j], (GEN)V[j+1], T, p, &u, &v);
    if (degpol(d) > 0) err(talker, "relatively prime polynomials expected");
    d = (GEN)d[2];
    if (!gcmp1(d))
    {
      d = FpXQ_inv(d, T, p);
      u = FpXQX_FpXQ_mul(u, d, T, p);
      v = FpXQX_FpXQ_mul(v, d, T, p);
    }
    W[j]   = (long)u;
    W[j+1] = (long)v;
  }
}

/* au + bv = 1 (p0), ab = f (p0). Lift mod p1 = p0 pd (<= p0^2).
 * If noinv is set, don't lift the inverses u and v */
static void
HenselLift(GEN V, GEN W, long j, GEN f, GEN T, GEN pd, GEN p0, int noinv)
{
  gpmem_t av = avma;
  long space = lgef(f) * (lgefint(pd) + lgefint(p0) - 2);
  GEN a2,b2,g,z,s,t;
  GEN a = (GEN)V[j], b = (GEN)V[j+1];
  GEN u = (GEN)W[j], v = (GEN)W[j+1];

  if (T) space *= lgef(T);

  (void)new_chunk(space); /* HACK */
  g = gadd(f, gneg_i(gmul(a,b)));
  if (T) g = FpXQX_red(g, T, mulii(p0,pd));
  g = gdivexact(g, p0); if (!T) g = FpXQX_red(g, NULL, pd);
  z = FpXQX_mul(v,g, T,pd);
  t = FpXQX_divres(z,a, T,pd, &s);
  t = gadd(gmul(u,g), gmul(t,b)); t = FpXQX_red(t, T, pd);
  t = gmul(t,p0);
  s = gmul(s,p0);
  avma = av;

  /* already reduced mod p1 = pd p0 */
  a2 = gadd(a,s); V[j]   = (long)a2;
  b2 = gadd(b,t); V[j+1] = (long)b2;
  if (noinv) return;

  av = avma;
  (void)new_chunk(space); /* HACK */
  g = gadd(gmul(u,a2), gmul(v,b2));
  g = gadd(gneg_i(g), gun);

  if (T) g = FpXQX_red(g, T, mulii(p0,pd));
  g = gdivexact(g, p0); if (!T) g = FpXQX_red(g, NULL, pd);
  z = FpXQX_mul(v,g, T,pd);
  t = FpXQX_divres(z,a, T,pd, &s);
  t = gadd(gmul(u,g), gmul(t,b)); t = FpXQX_red(t, T, pd);
  t = gmul(t,p0);
  s = gmul(s,p0);
  avma = av;

  u = gadd(u,t); W[j]   = (long)u;
  v = gadd(v,s); W[j+1] = (long)v;
}

/* v list of factors, w list of inverses.  f = v[j] v[j+1]
 * Lift v[j] and v[j+1] mod p0 pd (possibly mod T), then all their divisors */
static void
RecTreeLift(GEN link, GEN v, GEN w, GEN T, GEN pd, GEN p0, GEN f, long j, int noinv)
{
  if (j < 0) return;

  HenselLift(v, w, j, f, T, pd, p0, noinv);
  RecTreeLift(link, v, w, T, pd, p0, (GEN)v[j]  , link[j  ], noinv);
  RecTreeLift(link, v, w, T, pd, p0, (GEN)v[j+1], link[j+1], noinv);
}

/* lift from p^{e0} to p^{e1} */
static void
TreeLift(GEN link, GEN v, GEN w, GEN T, GEN p, long e0, long e1, GEN f, int noinv)
{
  GEN p0 = gpowgs(p, e0);
  GEN pd = gpowgs(p, e1-e0);
  RecTreeLift(link, v, w, T, pd, p0, f, lg(v)-2, noinv);
}

/* a = modular factors of f mod (p,T) [possibly T=NULL], lift to precision p^e0
 * flag = 0: standard.
 * flag = 1: return TreeLift structure
 * flag = 2: a = TreeLift structure, go on lifting, as flag = 1 otherwise */
static GEN
MultiLift(GEN f, GEN a, GEN T, GEN p, long e0, int flag)
{
  long l, i, e = e0, k = lg(a) - 1;
  GEN E, v, w, link;

  if (k < 2 || e < 1) err(talker, "MultiLift: bad args");
  if (e == 1) return a;
  if (typ(a[1]) == t_INT) flag = 2;
  else if (flag == 2) flag = 1;

  E = cgetg(BITS_IN_LONG, t_VECSMALL);
  l = 0; E[++l] = e;
  while (e > 1) { e = (e+1)/2; E[++l] = e; }

  if (DEBUGLEVEL > 3) timer2();

  if (flag != 2)
  {
    v = cgetg(2*k - 2 + 1, t_VEC);
    w = cgetg(2*k - 2 + 1, t_VEC);
    link=cgetg(2*k - 2 + 1, t_VECSMALL);
    BuildTree(link, v, w, a, T, p);
    if (DEBUGLEVEL > 3) msgtimer("building tree");
  }
  else
  {
    e = itos((GEN)a[1]);
    link = (GEN)a[2];
    v    = (GEN)a[3];
    w    = (GEN)a[4];
  }

  for (i = l; i > 1; i--) {
    if (E[i-1] < e) continue;
    TreeLift(link, v, w, T, p, E[i], E[i-1], f, (flag == 0) && (i == 2));
    if (DEBUGLEVEL > 3) msgtimer("lifting to prec %ld", E[i-1]);
  }

  if (flag)
  {
    E = cgetg(4, t_VEC);
    E[1] = lstoi(e0);
    E[2] = (long)link;
    E[3] = (long)v;
    E[4] = (long)w;
  }
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
hensel_lift_fact(GEN pol, GEN Q, GEN T, GEN p, GEN pe, long e)
{
  if (lg(Q) == 2) { GEN d = cgetg(2, t_VEC); d[1] = (long)pol; return d; }
  pol = FpXQX_normalize(pol, T, pe);
  return MultiLift(pol, Q, T, p, e, 0);
}

/* U = NULL treated as 1 */
static void
BezoutPropagate(GEN link, GEN v, GEN w, GEN pe, GEN U, GEN f, long j)
{
  GEN Q, R;
  if (j < 0) return;

  Q = FpX_mul((GEN)v[j], (GEN)w[j], pe);
  if (U)
  {
    Q = FpXQ_mul(Q, U, f, pe);
    R = FpX_sub(U, Q, pe);
  }
  else
    R = FpX_Fp_add(FpX_neg(Q, pe), gun, pe);
  w[j+1] = (long)Q; /*  0 mod U v[j],  1 mod (1-U) v[j+1] */
  w[j  ] = (long)R; /*  1 mod U v[j],  0 mod (1-U) v[j+1] */
  BezoutPropagate(link, v, w, pe, R, f, link[j  ]);
  BezoutPropagate(link, v, w, pe, Q, f, link[j+1]);
}

/* as above, but return the Bezout coefficients for the lifted modular factors
 *   U[i] = 1 mod Qlift[i]
 *          0 mod Qlift[j], j != i */
GEN
bezout_lift_fact(GEN pol, GEN Q, GEN p, long e)
{
  GEN E, link, v, w, pe;
  long i, k = lg(Q)-1;
  if (k == 1) { GEN d = cgetg(2, t_VEC); d[1] = (long)pol; return d; }
  pe = gpowgs(p, e);
  pol = FpX_normalize(pol, pe);
  E = MultiLift(pol, Q, NULL, p, e, 1);
  link = (GEN) E[2];
  v    = (GEN) E[3];
  w    = (GEN) E[4];
  BezoutPropagate(link, v, w, pe, NULL, pol, lg(v) - 2);
  E = cgetg(k+1, t_VEC);
  for (i = 1; i <= 2*k-2; i++)
  {
    long t = link[i];
    if (t < 0) E[-t] = w[i];
  }
  return gcopy(E);
}

/* Front-end for hensel_lift_fact:
   lift the factorization of pol mod p given by fct to p^exp (if possible) */
GEN
polhensellift(GEN pol, GEN fct, GEN p, long exp)
{
  GEN p1, p2;
  long i, j, l;
  gpmem_t av = avma;

  /* we check the arguments */
  if (typ(pol) != t_POL)
    err(talker, "not a polynomial in polhensellift");
  if ((typ(fct) != t_COL && typ(fct) != t_VEC) || (lg(fct) < 3))
    err(talker, "not a factorization in polhensellift");
  if (typ(p) != t_INT || !BSW_psp(p))
    err(talker, "not a prime number in polhensellift");
  if (exp < 1)
    err(talker, "not a positive exponent in polhensellift");

  p1 = lift(fct); /* make sure the coeffs are integers and not intmods */
  l = lg(p1) - 1;
  for (i=1; i<=l; i++)
  {
    p2 = (GEN)p1[i];
    if (typ(p2) != t_POL)
    {
      if (typ(p2) != t_INT)
        err(talker, "not an integral factorization in polhensellift");
      p1[i] = (long)scalarpol(p2, varn(pol));
    }
  }

  /* then we check that pol \equiv \prod f ; f \in fct mod p */
  p2 = (GEN)p1[1];
  for (j = 2; j <= l; j++) p2 = FpX_mul(p2, (GEN)p1[j], p);
  if (!gcmp0(FpX_sub(pol, p2, p)))
    err(talker, "not a correct factorization in polhensellift");

  /* finally we check that the elements of fct are coprime mod p */
  if (!FpX_is_squarefree(pol, p))
  {
    for (i = 1; i <= l; i++)
      for (j = 1; j < i; j++)
        if (lgef(FpX_gcd((GEN)p1[i], (GEN)p1[j], p)) != 3)
          err(talker, "polhensellift: factors %Z and %Z are not coprime",
                     p1[i], p1[j]);
  }
  return gerepilecopy(av, hensel_lift_fact(pol,p1,NULL,p,gpowgs(p,exp),exp));
}

#if 0
/* cf Beauzamy et al: upper bound for
 *      lc(x) * [2^(5/8) / pi^(3/8)] e^(1/4n) 2^(n/2) sqrt([x]_2)/ n^(3/8)
 * where [x]_2 = sqrt(\sum_i=0^n x[i]^2 / binomial(n,i)). One factor has
 * all coeffs less than then bound */
static GEN
two_factor_bound(GEN x)
{
  long i, j, n = lgef(x) - 3;
  gpmem_t av = avma;
  GEN *invbin, c, r = cgetr(3), z;

  x += 2; invbin = (GEN*)new_chunk(n+1);
  z = realun(3); /* invbin[i] = 1 / binomial(n, i) */
  for (i=0,j=n; j >= i; i++,j--)
  {
    invbin[i] = invbin[j] = z;
    z = divrs(mulrs(z, i+1), n-i);
  }
  z = invbin[0]; /* = 1 */
  for (i=0; i<=n; i++)
  {
    c = (GEN)x[i]; if (!signe(c)) continue;
    affir(c, r);
    z = addrr(z, mulrr(gsqr(r), invbin[i]));
  }
  z = shiftr(mpsqrt(z), n);
  z = divrr(z, dbltor(pow((double)n, 0.75)));
  z = grndtoi(mpsqrt(z), &i);
  z = mulii(z, absi((GEN)x[n]));
  return gerepileuptoint(av, shifti(z, 1));
}
#endif

static GEN
uniform_Mignotte_bound(GEN x)
{
  long e, n = degpol(x);
  GEN p1, N2 = mpsqrt(QuickNormL2(x,DEFAULTPREC));

  p1 = grndtoi(gmul2n(N2, n), &e);
  if (e>=0) p1 = addii(p1, shifti(gun, e));
  return p1;
}

/* all factors have coeffs less than the bound */
static GEN
all_factor_bound(GEN x)
{
  long i, n = lgef(x) - 3;
  GEN t, z = gzero;
  for (i=2; i<=n+2; i++) z = addii(z,sqri((GEN)x[i]));
  t = absi((GEN)x[n+2]);
  z = addii(t, addsi(1, racine(z)));
  z = mulii(z, binome(stoi(n-1), n>>1));
  return shifti(mulii(t,z),1);
}

/* x defined mod p^a, return mods ( (x - mods(x, p^b)) / p^b , p^(b-a) )  */
static GEN
Truncate_p(GEN x, GEN pb, GEN pa_b, GEN pa_bs2, GEN pbs2)
{
  GEN r, q = dvmdii(x, pb, &r);
  if (cmpii(r,  pbs2) > 0) q = addis(q,1);
  if (pa_bs2 && cmpii(q,pa_bs2) > 0) q = subii(q,pa_b);
  return q;
}

/* in place */
GEN
MatTruncate_p(GEN T, GEN p, long a, long b)
{
  GEN pb = gpowgs(p, b);
  GEN pa_b = gpowgs(p, a-b);
  GEN pa_bs2 = shifti(pa_b,-1);
  GEN pbs2   = shifti(pb,-1);
  long i,j, r = lg(T)-1, s = lg(T[1])-1;
  for (i=1; i<=r; i++)
  {
    GEN c = (GEN)T[i];
    for (j=1; j<=s; j++)
      c[j] = (long)Truncate_p((GEN)c[j],pb,pa_b,pa_bs2,pbs2);
  }
  return T;
}

/* Naive recombination of modular factors: combine up to maxK modular
 * factors, degree <= klim and divisible by hint
 *
 * target = polynomial we want to factor
 * famod = array of modular factors.  Product should be congruent to
 * target/lc(target) modulo p^a
 * All rational factors are bounded by p^b, b <= a and p^(b-a) < 2^(BIL-1) */
static GEN
cmbf(GEN target, GEN famod, GEN p, long b, long a,
     long maxK, long klim,long hint)
{
  long K = 1, cnt = 1, i,j,k, curdeg, lfamod = lg(famod)-1;
  long spa_b, spa_bs2;
  GEN lc, lctarget, pa = gpowgs(p,a), pas2 = shifti(pa,-1);
  GEN trace    = cgetg(lfamod+1, t_VECSMALL);
  GEN ind      = cgetg(lfamod+1, t_VECSMALL);
  GEN degpol   = cgetg(lfamod+1, t_VECSMALL);
  GEN degsofar = cgetg(lfamod+1, t_VECSMALL);
  GEN listmod  = cgetg(lfamod+1, t_COL);
  GEN fa       = cgetg(lfamod+1, t_COL);
  GEN res = cgetg(3, t_VEC);
  GEN bound = all_factor_bound(target);

  if (maxK < 0) maxK = lfamod-1;

  lc = absi(leading_term(target));
  lctarget = gmul(lc,target);

  {
    GEN pa_b,pa_bs2,pb,pbs2;
    pa_b = gpowgs(p, a-b); /* make sure p^(a-b) < 2^(BIL-1) */
    while (is_bigint(pa_b)) { b++; pa_b = divii(pa_b, p); }
    pa_bs2 = shifti(pa_b,-1);
    pb= gpowgs(p, b); pbs2 = shifti(pb,-1);
    for (i=1; i <= lfamod; i++)
    {
      GEN T, p1 = (GEN)famod[i];
      degpol[i] = degpol(p1);
      if (!gcmp1(lc))
        T = modii(mulii(lc, (GEN)p1[degpol[i]+1]), pa);
      else
        T = (GEN)p1[degpol[i]+1]; /* d-1 term */
      trace[i] = itos( Truncate_p(T, pb,pa_b,NULL,pbs2) );
    }
    spa_b   =   pa_b[2]; /* < 2^(BIL-1) */
    spa_bs2 = pa_bs2[2]; /* < 2^(BIL-1) */
  }
  degsofar[0] = 0; /* sentinel */

  /* ind runs through strictly increasing sequences of length K,
   * 1 <= ind[i] <= lfamod */
nextK:
  if (K > maxK || 2*K > lfamod) goto END;
  if (DEBUGLEVEL > 4)
    fprintferr("\n### K = %d, %Z combinations\n", K,binome(stoi(lfamod), K));
  setlg(ind, K+1); ind[1] = 1;
  i = 1; curdeg = degpol[ind[1]];
  for(;;)
  { /* try all combinations of K factors */
    for (j = i; j < K; j++)
    {
      degsofar[j] = curdeg;
      ind[j+1] = ind[j]+1; curdeg += degpol[ind[j+1]];
    }
    if (curdeg <= klim && curdeg % hint == 0) /* trial divide */
    {
      GEN y, q, cont, list;
      gpmem_t av;
      long t;

      /* d - 1 test,  overflow is not a problem (correct mod 2^BIL) */
      for (t=trace[ind[1]],i=2; i<=K; i++)
        t = addssmod(t, trace[ind[i]], spa_b);
      if (t > spa_bs2) t -= spa_b;
      if (labs(t) > ((K+1)>>1))
      {
        if (DEBUGLEVEL>6) fprintferr(".");
        goto NEXT;
      }
      av = avma;

      /* check trailing coeff */
      y = lc;
      for (i=1; i<=K; i++)
        y = centermod_i(mulii(y, gmael(famod,ind[i],2)), pa, pas2);
      if (!signe(y) || resii((GEN)lctarget[2], y) != gzero)
      {
        if (DEBUGLEVEL>6) fprintferr("T");
        avma = av; goto NEXT;
      }
      y = lc; /* full computation */
      for (i=1; i<=K; i++)
        y = centermod_i(gmul(y, (GEN)famod[ind[i]]), pa, pas2);

      /* y is the candidate factor */
      if (! (q = polidivis(lctarget,y,bound)) )
      {
        if (DEBUGLEVEL>6) fprintferr("*");
        avma = av; goto NEXT;
      }
      /* found a factor */
      cont = content(y);
      if (signe(leading_term(y)) < 0) cont = negi(cont);
      y = gdiv(y, cont);

      list = cgetg(K+1, t_VEC);
      listmod[cnt] = (long)list;
      for (i=1; i<=K; i++) list[i] = famod[ind[i]];

      fa[cnt++] = (long)y;
      /* fix up target */
      target = gdiv(q, leading_term(y));
      for (i=j=k=1; i <= lfamod; i++)
      { /* remove used factors */
        if (j <= K && i == ind[j]) j++;
        else
        {
          famod[k] = famod[i];
          trace[k] = trace[i];
          degpol[k] = degpol[i]; k++;
        }
      }
      lfamod -= K;
      if (lfamod < 2*K) goto END;
      i = 1; curdeg = degpol[ind[1]];
      bound = all_factor_bound(target);
      lc = absi(leading_term(target));
      lctarget = gmul(lc,target);
      if (DEBUGLEVEL > 2)
      {
        fprintferr("\n"); msgtimer("to find factor %Z",y);
        fprintferr("remaining modular factor(s): %ld\n", lfamod);
      }
      continue;
    }

NEXT:
    for (i = K+1;;)
    {
      if (--i == 0) { K++; goto nextK; }
      if (++ind[i] <= lfamod - K + i)
      {
        curdeg = degsofar[i-1] + degpol[ind[i]];
        if (curdeg <= klim) break;
      }
    }
  }
END:
  if (degpol(target) > 0)
  { /* leftover factor */
    if (signe(leading_term(target)) < 0) target = gneg_i(target);

    setlg(famod, lfamod+1);
    listmod[cnt] = (long)dummycopy(famod);
    fa[cnt++] = (long)target;
  }
  if (DEBUGLEVEL>6) fprintferr("\n");
  setlg(listmod, cnt); setlg(fa, cnt);
  res[1] = (long)fa;
  res[2] = (long)listmod; return res;
}

void
factor_quad(GEN x, GEN res, long *ptcnt)
{
  GEN a = (GEN)x[4], b = (GEN)x[3], c = (GEN)x[2], d, u, z1, z2, t;
  GEN D = subii(sqri(b), shifti(mulii(a,c), 2));
  long v, cnt = *ptcnt;

  if (!carrecomplet(D, &d)) { res[cnt++] = (long)x; *ptcnt = cnt; return; }

  t = shifti(negi(addii(b, d)), -1);
  z1 = gdiv(t, a); u = denom(z1);
  z2 = gdiv(addii(t, d), a);
  v = varn(x);
  res[cnt++] = lmul(u, gsub(polx[v], z1)); u = divii(a, u);
  res[cnt++] = lmul(u, gsub(polx[v], z2)); *ptcnt = cnt;
}

/* y > 1 and B integers. Let n such that y^(n-1) <= B < y^n.
 * Return e = max(n,1), set *ptq = y^e if non-NULL */
long
logint(GEN B, GEN y, GEN *ptq)
{
  gpmem_t av = avma;
  long e,i,fl;
  GEN q,pow2, r = y;

  if (typ(B) != t_INT) B = ceil_safe(B);
  if (expi(B) <= (expi(y) << 6)) /* e small, be naive */
  {
    for (e=1; cmpii(r, B) < 0; e++) r = mulii(r,y);
    goto END;
  }
  /* binary splitting: compute bits of e one by one */
  /* compute pow2[i] = y^(2^i) [i < very crude upper bound for log_2(n)] */
  pow2 = new_chunk(bit_accuracy(lgefint(B)));
  pow2[0] = (long)y;
  for (i=0,q=r;; )
  {
    fl = cmpii(r,B); if (fl >= 0) break;
    q = r; r = sqri(q);
    i++; pow2[i] = (long)r;
  }
  if (i == 0) { e = 1; goto END; } /* y <= B */

  for (i--, e=1<<i;;)
  { /* y^e = q < B <= r = q * y^(2^i) */
    if (!fl) break; /* B = r */
    /* q < B < r */
    if (--i < 0) { if (fl > 0) e++; break; }
    r = mulii(q, (GEN)pow2[i]);
    fl = cmpii(r, B);
    if (fl <= 0) { e += (1<<i); q = r; }
  }
  if (fl <= 0) { e++; r = mulii(r,y); }
END:
  if (ptq) *ptq = gerepileuptoint(av, icopy(r)); else avma = av;
  return e;
}
    
/* recombination of modular factors: van Hoeij's algorithm */

/* return integer y such that all roots of P are less than y */
static GEN
root_bound(GEN P)
{
  GEN P0 = dummycopy(P), lP = absi(leading_term(P)), x,y,z;
  long k,d = degpol(P);

  setlgef(P0, d+2); /* P = lP x^d + P0 */
  P = P0+2; /* strip codewords */
  for (k=0; k<d; k++) P[k] = labsi((GEN)P[k]);

  x = y = gun;
  for (k=0; ; k++)
  {
    if (cmpii(poleval(P0,y), mulii(lP, gpowgs(y, d))) < 0) break;
    x = y; y = shifti(y,1);
  }
  for(;;)
  {
    z = shifti(addii(x,y), -1);
    if (egalii(x,z)) break;
    if (cmpii(poleval(P0,z), mulii(lP, gpowgs(z, d))) < 0)
      y = z;
    else
      x = z;
  }
  return y;
}

extern GEN gscal(GEN x,GEN y);
extern GEN sqscal(GEN x);

/* return Gram-Schmidt orthogonal basis (f) associated to (e), B is the
 * vector of the (f_i . f_i)*/
GEN
gram_schmidt(GEN e, GEN *ptB)
{
  long i,j,lx = lg(e);
  GEN f = dummycopy(e), B, iB;

  B = cgetg(lx, t_VEC);
  iB= cgetg(lx, t_VEC);

  for (i=1;i<lx;i++)
  {
    GEN p1 = NULL;
    gpmem_t av;
    B[i] = (long)sqscal((GEN)f[i]);
    iB[i]= linv((GEN)B[i]); av = avma;
    for (j=1; j<i; j++)
    {
      GEN mu = gmul(gscal((GEN)e[i],(GEN)f[j]), (GEN)iB[j]);
      GEN p2 = gmul(mu, (GEN)f[j]);
      p1 = p1? gadd(p1,p2): p2;
    }
    p1 = p1? gerepileupto(av, gsub((GEN)e[i], p1)): (GEN)e[i];
    f[i] = (long)p1;
  }
  *ptB = B; return f;
}

extern GEN hnfall_i(GEN A, GEN *ptB, long remove);

GEN
special_pivot(GEN x)
{
  GEN t, H = hnfall_i(x, NULL, 1);
  long i,j, l = lg(H), h = lg(H[1]);
  for (i=1; i<h; i++)
  {
    int fl = 0;
    for (j=1; j<l; j++)
    {
      t = gcoeff(H,i,j);
      if (signe(t))
      {
        if (!is_pm1(t) || fl) return NULL;
        fl = 1;
      }
    }
  }
  return H;
}

/* x matrix: compute a bound for | \sum e_i x_i | ^ 2, e_i = 0,1 */
GEN
norml2_spec(GEN x, long prec)
{
  long i,j, co = lg(x), li;
  GEN S = gzero;
  if (co == 1) return S;

  x = gmul(x, realun(prec));
  li = lg(x[1]);
  for (i=1; i<li; i++)
  {
    GEN p = gzero;
    GEN m = gzero;
    for (j=1; j<co; j++)
    {
      GEN u = gcoeff(x,i,j);
      long s = gsigne(u);
      if      (s < 0) m = gadd(m,u);
      else if (s > 0) p = gadd(p,u);
    }
    if (m != gzero) m = gneg(m);
    if (gcmp(p,m) > 0) m = p;

    S = gadd(S, gsqr(m));
  }
  return S;
}

/* each entry < 2^e */
long
init_padic_prec(long e, int BitPerFactor, long r, double LOGp2)
{
  long b, goodb = (long) (((e - BitPerFactor*r)) * LOGp2);
  b = (long) ((e - 32)*LOGp2); if (b < goodb) goodb = b;
  return goodb;
}

extern GEN sindexrank(GEN x);
extern GEN vconcat(GEN Q1, GEN Q2);
extern GEN gauss_intern(GEN a, GEN b);
extern GEN lllgramint_i(GEN x, long alpha, GEN *ptfl, GEN *ptB);

/* bound for q(vS) := || vS ||_2^2 */
double
bound_vS(long tmax, GEN *ptB)
{
  gpmem_t av = avma;
  double Nx;
  GEN z, B = *ptB;
  if (tmax > 0)
  { /* bound small vector in terms of a modified L2 norm of a
     * left inverse of BL */
    z = gauss_intern(B,NULL); /* 1/BL */
    if (!z) /* not maximal rank */
    {
      avma = av;
      B = hnfall_i(B,NULL,1);
      av = avma;
      z = invmat(B);
    }
    Nx = gtodouble(norml2_spec(z, DEFAULTPREC));
    avma = av;
  }
  else
  {
    long n0 = lg(B)-1;
    Nx = (double)n0; /* first time: BL = id */
  }
  *ptB = B; return Nx;
}

/* B grom lllgramint_i: return [ |b_i^*|^2, i ] */
GEN
GS_norms(GEN B, long prec)
{
  long i, l = lg(B);
  GEN v = gmul(B, realun(prec));
  l--; setlg(v, l);
  for (i=1; i<l; i++)
    v[i] = ldivrr((GEN)v[i+1], (GEN)v[i]);
  return v;
}

/* Recombination phase of Berlekamp-Zassenhaus algorithm using a variant of
 * van Hoeij's knapsack
 *
 * P = monic squarefree in Z[X].
 * famod = array of (lifted) modular factors mod p^a
 * bound = Mignotte bound for the size of divisors of P (for the sup norm)
 * previously recombined all set of factors with less than rec elts */
GEN
LLL_cmbf(GEN P, GEN famod, GEN p, GEN pa, GEN bound, long a, long rec)
{
  const long s = 2; /* # of traces added at each step */
  long BitPerFactor = 3; /* nb bits in p^(a-b) / modular factor */
  long i,j,C,r,S,tmax,n0,n,dP = degpol(P);
  double logp = log(gtodouble(p)), LOGp2 = LOG2/logp;
  double b0 = log((double)dP*2) / logp;
  double k = gtodouble(glog(root_bound(P), DEFAULTPREC)) / logp;
  GEN B, y, T, T2, TT, BL, m, u, norm, target, M, piv, list;
  gpmem_t av, av2, lim;
  int did_recompute_famod = 0;

  n0 = n = r = lg(famod) - 1;
  list = cgetg(n0+1, t_COL);

  av = avma; lim = stack_lim(av, 1);
  TT = cgetg(n0+1, t_VEC);
  T  = cgetg(n0+1, t_MAT);
  for (i=1; i<=n0; i++)
  {
    TT[i] = 0;
    T [i] = lgetg(s+1, t_COL);
  }
  BL = idmat(n0);
  /* tmax = current number of traces used (and computed so far)
   * S = number of traces used at the round's end = tmax + s */
  for(tmax = 0;; tmax = S)
  {
    GEN pas2, pa_b, BE;
    long b, goodb;
    double Nx;

    if (DEBUGLEVEL>2)
      fprintferr("LLL_cmbf: %ld potential factors (tmax = %ld)\n", r, tmax);
    Nx = bound_vS(tmax,&BL);
    r = lg(BL)-1;

    C = (long)sqrt(s*n0*n0/4. / Nx);
    if (C == 0) C = 1; /* frequent after a few iterations */
    M = dbltor((Nx * C*C + s*n0*n0/4.) * 1.00001);

    S = tmax + s;
    b = (long)ceil(b0 + S*k);
    if (a <= b)
    {
      a = (long)ceil(b + 3*s*k) + 1; /* enough for 3 more rounds */
      pa = gpowgs(p,a);
      famod = hensel_lift_fact(P,famod,NULL,p,pa,a);
      /* recompute old Newton sums to new precision */
      for (i=1; i<=n0; i++)
        TT[i] = (long)polsym_gen((GEN)famod[i], NULL, tmax, NULL, pa);
      did_recompute_famod = 1;
    }
    for (i=1; i<=n0; i++)
    {
      GEN p1 = (GEN)T[i];
      GEN p2 = polsym_gen((GEN)famod[i], (GEN)TT[i], S, NULL, pa);
      TT[i] = (long)p2;
      p2 += 1+tmax; /* ignore traces number 0...tmax */
      for (j=1; j<=s; j++) p1[j] = p2[j];
    }

    av2 = avma;
    T2 = gmod( gmul(T, BL), pa );
    goodb = init_padic_prec(gexpo(T2), BitPerFactor, r, LOGp2);
    if (goodb > b) b = goodb;
    if (DEBUGLEVEL>2)
      fprintferr("LLL_cmbf: (a, b) = (%ld, %ld), expo(T) = %ld\n",
                 a,b,gexpo(T2));
    T2 = MatTruncate_p(T2,p, a,b);
    if (gcmp0(T2)) { avma = av2; continue; }

    BE = cgetg(s+1, t_MAT);
    pa_b = gpowgs(p, a-b);
    for (i=1; i<=s; i++)
    {
      BE[i] = (long)zerocol(r+s);
      coeff(BE, i+r, i) = (long)pa_b;
    }
    m = concatsp( vconcat( gscalmat(stoi(C), r), T2 ), BE );
    /*     [  C        0      ]
     * m = [                  ]   square matrix
     *     [ T2   p^(a-b) I_s ]   T2 = T * BL  truncated
     */
    u = lllgramint_i(gram_matrix(m), 4, NULL, &B);
    norm = GS_norms(B, DEFAULTPREC);
    for (i=r+s; i>0; i--)
      if (cmprr((GEN)norm[i], M) < 0) break;
    if (i > r)
    { /* no progress. Note: even if i == r we may have made some progress */
      avma = av2; BitPerFactor += 2;
      if (DEBUGLEVEL>2)
        fprintferr("LLL_cmbf: increasing BitPerFactor = %ld\n", BitPerFactor);
      continue;
    }

    n = r; r = i;
    if (r <= 1)
    {
      if (r == 0) err(bugparier,"LLL_cmbf [no factor]");
      if (DEBUGLEVEL>2) fprintferr("LLL_cmbf: 1 factor\n");
      list[1] = (long)P; setlg(list,2); return list;
    }

    setlg(u, r+1);
    for (i=1; i<=r; i++) setlg(u[i], n+1);
    BL = gerepileupto(av2, gmul(BL, u));
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[4]; gptr[0]=&BL; gptr[1]=&TT; gptr[2]=&T; gptr[3]=&famod;
      if(DEBUGMEM>1) err(warnmem,"LLL_cmbf");
      gerepilemany(av, gptr, did_recompute_famod? 4: 3);
    }
    if (r*rec >= n0) continue;

    av2 = avma;
    piv = special_pivot(BL);
    if (!piv) { avma = av2; continue; }
    if (DEBUGLEVEL) fprintferr("special_pivot output:\n%Z\n",piv);

    pas2 = shifti(pa,-1); target = P;
    for (i=1; i<=r; i++)
    {
      GEN p1 = (GEN)piv[i];
      if (DEBUGLEVEL) fprintferr("LLL_cmbf: checking factor %ld\n",i);

      y = gun;
      for (j=1; j<=n0; j++)
        if (signe(p1[j]))
          y = centermod_i(gmul(y, (GEN)famod[j]), pa, pas2);

      /* y is the candidate factor */
      if (! (target = polidivis(target,y,bound)) ) break;
      list[i] = (long)y;
    }
    if (i > r)
    {
      if (DEBUGLEVEL>2) fprintferr("LLL_cmbf: %ld factors\n", r);
      setlg(list,r+1); return list;
    }
  }
}

extern GEN primitive_pol_to_monic(GEN pol, GEN *ptlead);

/* Return P(h * x) */
GEN
unscale_pol(GEN P, GEN h)
{
  long i, l = lgef(P);
  GEN hi = gun, Q = cgetg(l, t_POL);
  Q[1] = P[1];
  Q[2] = lcopy((GEN)P[2]);
  for (i=3; i<l; i++)
  {
    hi = gmul(hi,h);
    Q[i] = lmul((GEN)P[i], hi);
  }
  return Q;
}

/* Return h^degpol(P) P(x / h) */
GEN
rescale_pol(GEN P, GEN h)
{
  long i, l = lgef(P);
  GEN Q = cgetg(l,t_POL), hi = gun;
  Q[l-1] = P[l-1];
  for (i=l-2; i>=2; i--)
  {
    hi = gmul(hi,h);
    Q[i] = lmul((GEN)P[i], hi);
  }
  Q[1] = P[1]; return Q;
}

/* as above over Fp[X] */
GEN
FpX_rescale(GEN P, GEN h, GEN p)
{
  long i, l = lgef(P);
  GEN Q = cgetg(l,t_POL), hi = gun;
  Q[l-1] = P[l-1];
  for (i=l-2; i>=2; i--)
  {
    hi = modii(mulii(hi,h), p);
    Q[i] = lmodii(mulii((GEN)P[i], hi), p);
  }
  Q[1] = P[1]; return Q;
}

/* use van Hoeij's knapsack algorithm */
static GEN
combine_factors(GEN a, GEN famod, GEN p, long klim, long hint)
{
  GEN B = uniform_Mignotte_bound(a), res,lt,L,pe,pE,listmod;
  long i,E,e,l, maxK = 3, nft = lg(famod)-1;

  e = logint(B, p, &pe);
  if (DEBUGLEVEL > 4) fprintferr("Mignotte bound: %Z^%ld\n", p,e);

  { /* overlift for the d-1 test */
    int over = (int) (32 * LOG2 / log((double)itos(p)));
    pE = mulii(pe, gpowgs(p,over)); E = e + over;
  }
  famod = hensel_lift_fact(a,famod,NULL,p,pE,E);

  if (nft < 11) maxK = -1; /* few modular factors: try all posibilities */
  else
  {
    lt = leading_term(a);
    if (!is_pm1(lt) && nft < 13) maxK = -1;
  }
  L = cmbf(a, famod, p, e, E, maxK, klim, hint);

  res     = (GEN)L[1];
  listmod = (GEN)L[2]; l = lg(listmod);
  famod = (GEN)listmod[l-1];
  if (maxK >= 0 && lg(famod)-1 > 2*maxK)
  {
    a = (GEN)res[l-1];
    lt = leading_term(a);
    if (signe(lt) < 0) { a = gneg_i(a); lt = leading_term(a); }
    if (DEBUGLEVEL > 4) fprintferr("last factor still to be checked\n");
    if (gcmp1(lt)) lt = NULL;
    else
    {
      if (DEBUGLEVEL > 4) fprintferr("making it monic\n");
      a = primitive_pol_to_monic(a, &lt);
      B = uniform_Mignotte_bound(a);
      e = logint(B, p, &pe);
      /* renormalize modular factors */
      for (i = 1; i<lg(famod); i++)
        famod[i] = (long)FpX_rescale((GEN)famod[i], lt, p);
      famod = hensel_lift_fact(a,famod,NULL,p,pe,e);
    }
    setlg(res, l-1); /* remove last elt (possibly unfactored) */
    L = LLL_cmbf(a, famod, p, pe, B, e, maxK);
    if (lt)
      for (i=1; i<lg(L); i++)
        L[i] = (long)primpart( unscale_pol((GEN)L[i], lt) );
    res = concatsp(res, L);
  }
  return res;
}

extern long FpX_split_berlekamp(GEN *t, GEN pp);
#define u_FpX_div(x,y,p) u_FpX_divrem((x),(y),(p),(0),NULL)

/* Assume a squarefree, degree(a) > 0, a(0) != 0 */
static GEN
DDF(GEN a, long hint)
{
  GEN PolX,lead,res,prime,famod,y,g,z,w,*tabd,*tabdnew;
  long da = degpol(a), va = varn(a);
  long klim,chosenp,p,nfacp,lbit,j,d,e,np,nmax,nf,nft;
  ulong *tabbit, *tabkbit, *tmp;
  gpmem_t av = avma;
  byteptr pt=diffptr;
  const int MAXNP = max(5, (long)sqrt(da));

  if (hint <= 0) hint = 1;
  if (DEBUGLEVEL > 2) timer2();
  lbit = (da>>4)+1; nmax = da+1; klim = da>>1;
  chosenp = 0;
  tabd = NULL;
  tabdnew = (GEN*)new_chunk(nmax);
  tabbit  = (ulong*)new_chunk(lbit);
  tabkbit = (ulong*)new_chunk(lbit);
  tmp     = (ulong*)new_chunk(lbit);
  prime = icopy(gun);
  lead = (GEN)a[da+2]; PolX = u_Fp_FpX(polx[0],0, 2);
  for (p = np = 0; np < MAXNP; )
  {
    gpmem_t av0 = avma;
    p += *pt++; if (!*pt) err(primer1);
    if (!smodis(lead,p)) continue;
    z = u_Fp_FpX(a,0, p);
    if (!u_FpX_is_squarefree(z, p)) { avma = av0; continue ; }

    for (j=0; j<lbit-1; j++) tabkbit[j] = 0;
    tabkbit[j] = 1;
    d = 0; e = da; nfacp = 0;
    w = PolX; prime[2] = p;
    while (d < (e>>1))
    {
      long lgg;
      d++; w = u_FpXQ_pow(w, prime, z, p);
      g = u_FpX_gcd(z, u_FpX_sub(w, PolX, p), p);
      lgg = degpol(g);
      if (lgg == 0) g = NULL;
      else
      {
	z = u_FpX_div(z, g, p); e = degpol(z);
        w = u_FpX_rem(w, z, p);
        lgg /= d; nfacp += lgg;
        if (DEBUGLEVEL>5)
          fprintferr("   %3ld factor%s of degree %3ld\n", lgg, lgg==1?"":"s",d);
	record_factors(lgg, d, lbit-1, tabkbit, tmp);
      }
      tabdnew[d] = g;
    }
    if (e > 0)
    {
      if (DEBUGLEVEL>5) fprintferr("   %3ld factor of degree %3ld\n",1,e);
      tabdnew[e] = z; nfacp++;
      record_factors(1, e, lbit-1, tabkbit, tmp);
    }

    if (np)
      for (j=0; j<lbit; j++) tabbit[j] &= tabkbit[j];
    else
      for (j=0; j<lbit; j++) tabbit[j] = tabkbit[j];
    if (DEBUGLEVEL > 4)
      fprintferr("...tried prime %3ld (%-3ld factor%s). Time = %ld\n",
                  p, nfacp, nfacp==1?"": "s", timer2());
    if (min_deg(lbit-1,tabbit) > klim) { avma = av; return _col(a); }
    if (nfacp < nmax)
    {
      nmax = nfacp; tabd = tabdnew; chosenp = p;
      for (j=d+1; j<e; j++) tabd[j] = NULL;
      tabdnew = (GEN*)new_chunk(da);
    }
    else avma = av0;
    np++;
  }
  prime[2] = chosenp;
  nf = nmax; nft = 1;
  y = cgetg(nf+1,t_COL); famod = cgetg(nf+1,t_COL);
  for (d = 1; nft <= nf; d++)
  {
    g = tabd[d]; 
    if (g)
    {
      long n = degpol(g)/d;
      famod[nft] = (long)small_to_pol(u_FpX_normalize(g, chosenp),va);
      if (n > 1 && n != FpX_split_berlekamp((GEN*)(famod+nft),prime))
        err(bugparier,"DDF: wrong numbers of factors");
      nft += n;
    }
  }
  if (DEBUGLEVEL > 4) msgtimer("splitting mod p = %ld",chosenp);
  res = combine_factors(a, famod, prime, da-1, hint);
  return gerepilecopy(av, res);
}

/* A(X^d) --> A(X) */
GEN
poldeflate_i(GEN x0, long d)
{
  GEN z, y, x;
  long i,id, dy, dx = degpol(x0);
  if (d == 1) return x0;
  if (dx < 0) return zeropol(varn(x0));
  dy = dx/d;
  y = cgetg(dy+3, t_POL);
  y[1] = evalsigne(1)|evaldeg(dy)|evalvarn(varn(x0));
  z = y + 2;
  x = x0+ 2;
  for (i=id=0; i<=dy; i++,id+=d) z[i] = x[id];
  return y;
}

long
checkdeflate(GEN x)
{
  long d = 0, i, lx = lgef(x);
  for (i=3; i<lx; i++)
    if (!gcmp0((GEN)x[i])) { d = cgcd(d,i-2); if (d == 1) break; }
  return d;
}

GEN
gdeflate(GEN x, long v, long d)
{
  long i, lx, tx = typ(x);
  GEN z;
  if (is_scalar_t(tx)) return gcopy(x);
  if (d <= 0) err(talker,"need positive degree in gdeflate");
  if (tx == t_POL)
  {
    long vx = varn(x);
    gpmem_t av;
    if (vx < v)
    {
      lx = lgef(x);
      z = cgetg(lx,t_POL); z[1] = x[1];
      for (i=2; i<lx; i++) z[i] = (long)gdeflate((GEN)x[i],v,d);
      return z;
    }
    if (vx > v) return gcopy(x);
    av = avma;
    if (checkdeflate(x) % d != 0)
      err(talker,"impossible substitution in gdeflate");
    return gerepilecopy(av, poldeflate_i(x,d));
  }
  if (tx == t_RFRAC)
  {
    z = cgetg(3, t_RFRAC);
    z[1] = (long)gdeflate((GEN)x[1],v,d);
    z[2] = (long)gdeflate((GEN)x[2],v,d);
    return z;
  }
  if (is_matvec_t(tx))
  {
    lx = lg(x); z = cgetg(lx, tx);
    for (i=1; i<lx; i++) z[i] = (long)gdeflate((GEN)x[i],v,d);
    return z;
  }
  err(typeer,"gdeflate");
  return NULL; /* not reached */
}

/* set *m to the largest d such that x0 = A(X^d); return A */
GEN
poldeflate(GEN x, long *m)
{
  *m = checkdeflate(x);
  return poldeflate_i(x, *m);
}

/* return x0(X^d) */
GEN
polinflate(GEN x0, long d)
{
  long i, id, dy, dx = degpol(x0);
  GEN x = x0 + 2, z, y;
  dy = dx*d;
  y = cgetg(dy+3, t_POL);
  y[1] = evalsigne(1)|evaldeg(dy)|evalvarn(varn(x0));
  z = y + 2;
  for (i=0; i<=dy; i++) z[i] = zero;
  for (i=id=0; i<=dx; i++,id+=d) z[id] = x[i];
  return y;
}

/* Distinct Degree Factorization (deflating first)
 * Assume x squarefree, degree(x) > 0, x(0) != 0 */
GEN
DDF2(GEN x, long hint)
{
  GEN L;
  long m;
  x = poldeflate(x, &m);
  L = DDF(x, hint);
  if (m > 1)
  {
    GEN e, v, fa = decomp(stoi(m));
    long i,j,k, l;

    e = (GEN)fa[2]; k = 0;
    fa= (GEN)fa[1]; l = lg(fa);
    for (i=1; i<l; i++)
    {
      e[i] = itos((GEN)e[i]);
      k += e[i];
    }
    v = cgetg(k+1, t_VECSMALL); k = 1;
    for (i=1; i<l; i++)
      for (j=1; j<=e[i]; j++) v[k++] = itos((GEN)fa[i]);
    for (k--; k; k--)
    {
      GEN L2 = cgetg(1,t_VEC);
      for (i=1; i < lg(L); i++)
        L2 = concatsp(L2, DDF(polinflate((GEN)L[i], v[k]), hint));
      L = L2;
    }
  }
  return L;
}

/* SquareFree Factorization. f = prod P^e, all e distinct, in Z[X] (char 0
 * would be enough, if modulargcd --> ggcd). Return (P), set *ex = (e) */
GEN
ZX_squff(GEN f, GEN *ex)
{
  GEN T,V,W,P,e,cf;
  long i,k,dW,n,val;

  val = polvaluation(f, &f);
  n = 1 + degpol(f); if (val) n++;
  e = cgetg(n,t_VECSMALL);
  P = cgetg(n,t_COL);
 
  cf = content(f); if (gsigne(leading_term(f)) < 0) cf = gneg_i(cf);
  if (!gcmp1(cf)) f = gdiv(f,cf);
 
  T = modulargcd(derivpol(f), f);
  V = gdeuc(f,T);
  for (k=i=1;; k++)
  {
    W = modulargcd(T,V); T = gdeuc(T,W); dW = degpol(W);
    /* W = prod P^e, e > k; V = prod P^e, e >= k */
    if (dW != degpol(V)) { P[i] = ldeuc(V,W); e[i] = k; i++; }
    if (dW <= 0) break;
    V = W;
  }
  if (val) { P[i] = lpolx[varn(f)]; e[i] = val; i++;}
  setlg(P,i);
  setlg(e,i); *ex=e; return P;
}

GEN
fact_from_DDF(GEN fa, GEN e, long n)
{
  GEN v,w, y = cgetg(3, t_MAT);
  long i,j,k, l = lg(fa);
 
  v = cgetg(n+1,t_COL); y[1] = (long)v;
  w = cgetg(n+1,t_COL); y[2] = (long)w;
  for (k=i=1; i<l; i++)
  {
    GEN L = (GEN)fa[i], ex = stoi(e[i]);
    long J = lg(L);
    for (j=1; j<J; j++,k++)
    {
      v[k] = lcopy((GEN)L[j]);
      w[k] = (long)ex;
    }
  }
  return y;
}

/* Factor x in Z[t]. Assume all factors have degree divisible by hint */
GEN
factpol(GEN x, long hint)
{
  gpmem_t av = avma;
  GEN fa,ex,y;
  long n,i,l;

  if (typ(x)!=t_POL) err(notpoler,"factpol");
  if (!signe(x)) err(zeropoler,"factpol");

  fa = ZX_squff(x, &ex);
  l = lg(fa); n = 0;
  for (i=1; i<l; i++)
  {
    fa[i] = (long)DDF2((GEN)fa[i], hint);
    n += lg(fa[i])-1;
  }
  y = fact_from_DDF(fa,ex,n);
  return gerepileupto(av, sort_factor(y, cmpii));
}

/***********************************************************************/
/**                                                                   **/
/**                          FACTORIZATION                            **/
/**                                                                   **/
/***********************************************************************/
#define LT 17
#define assign_or_fail(x,y) {\
  if (y==NULL) y=x; else if (!gegal(x,y)) return 0;\
}
#define tsh 6
#define typs(x,y) ((x << tsh) | y)
#define typ1(x) (x >> tsh)
#define typ2(x) (x & ((1<<tsh)-1))

static long
poltype(GEN x, GEN *ptp, GEN *ptpol, long *ptpa)
{
  long t[LT]; /* code for 0,1,2,3,61,62,63,67,7,81,82,83,86,87,91,93,97 */
  long tx = typ(x),lx,i,j,s,pa=BIGINT;
  GEN pcx=NULL, p=NULL,pol=NULL,p1,p2;

  if (is_scalar_t(tx))
  {
    if (tx == t_POLMOD) return 0;
    x = scalarpol(x,0);
  }
  for (i=2; i<LT; i++) t[i]=0; /* t[0..1] unused */
  lx = lgef(x);
  for (i=2; i<lx; i++)
  {
    p1=(GEN)x[i];
    switch(typ(p1))
    {
      case t_INT: case t_FRAC: case t_FRACN:
        break;
      case t_REAL:
        s = precision(p1); if (s < pa) pa = s;
        t[2]=1; break;
      case t_INTMOD:
	assign_or_fail((GEN)p1[1],p);
        t[3]=1; break;
      case t_COMPLEX:
        if (!pcx) pcx = coefs_to_pol(3, gun,gzero,gun); /* x^2 + 1 */
	for (j=1; j<=2; j++)
	{
	  p2 = (GEN)p1[j];
	  switch(typ(p2))
	  {
	    case t_INT: case t_FRAC: case t_FRACN:
	      assign_or_fail(pcx,pol);
	      t[4]=1; break;
	    case t_REAL:
              s = precision(p2); if (s < pa) pa = s;
	      t[5]=1; break;
	    case t_INTMOD:
	      assign_or_fail((GEN)p2[1],p);
	      assign_or_fail(pcx,pol);
	      t[6]=1; break;
	    case t_PADIC:
	      s = precp(p2) + valp(p2); if (s < pa) pa = s;
	      assign_or_fail((GEN)p2[2],p);
	      assign_or_fail(pcx,pol);
	      t[7]=1; break;
	    default: return 0;
	  }
	}
	break;
      case t_PADIC:
        s = precp(p1) + valp(p1); if (s < pa) pa = s;
	assign_or_fail((GEN)p1[2],p);
        t[8]=1; break;
      case t_QUAD:
	for (j=2; j<=3; j++)
	{
	  p2 = (GEN)p1[j];
	  switch(typ(p2))
	  {
	    case t_INT: case t_FRAC: case t_FRACN:
	      assign_or_fail((GEN)p1[1],pol);
	      t[9]=1; break;
	    case t_REAL:
	      s = precision(p2); if (s < pa) pa = s;
	      if (gsigne(discsr((GEN)p1[1]))>0) t[10]=1; else t[12]=1;
	      break;
	    case t_INTMOD:
	      assign_or_fail((GEN)p2[1],p);
	      assign_or_fail((GEN)p1[1],pol);
	      t[11]=1; break;
	    case t_PADIC:
	      s = precp(p2) + valp(p2); if (s < pa) pa = s;
	      assign_or_fail((GEN)p2[2],p);
	      assign_or_fail((GEN)p1[1],pol);
	      t[13]=1; break;
	    default: return 0;
	  }
	}
	break;
      case t_POLMOD:
	assign_or_fail((GEN)p1[1],pol);
	for (j=1; j<=2; j++)
	{
	  GEN pbis = NULL, polbis = NULL;
	  long pabis;
	  switch(poltype((GEN)p1[j],&pbis,&polbis,&pabis))
	  {
	    case t_INT: t[14]=1; break;
	    case t_INTMOD: t[15]=1; break;
	    case t_PADIC: t[16]=1; if (pabis<pa) pa=pabis; break;
	    default: return 0;
	  }
	  if (pbis) assign_or_fail(pbis,p);
	  if (polbis) assign_or_fail(polbis,pol);
	}
	break;
      default: return 0;
    }
  }
  if (t[5]||t[12])
  {
    if (t[3]||t[6]||t[7]||t[8]||t[11]||t[13]||t[14]||t[15]||t[16]) return 0;
    *ptpa=pa; return t_COMPLEX;
  }
  if (t[2]||t[10])
  {
    if (t[3]||t[6]||t[7]||t[8]||t[11]||t[13]||t[14]||t[15]||t[16]) return 0;
    *ptpa=pa; return t[4]?t_COMPLEX:t_REAL;
  }
  if (t[6]||t[11]||t[15])
  {
    *ptpol=pol; *ptp=p;
    i = t[15]? t_POLMOD: (t[11]? t_QUAD: t_COMPLEX);
    return typs(i, t_INTMOD);
  }
  if (t[7]||t[13]||t[16])
  {
    *ptpol=pol; *ptp=p; *ptpa=pa;
    i = t[16]? t_POLMOD: (t[13]? t_QUAD: t_COMPLEX);
    return typs(i, t_PADIC);
  }
  if (t[4]||t[9]||t[14])
  {
    *ptpol=pol;
    i = t[14]? t_POLMOD: (t[9]? t_QUAD: t_COMPLEX);
    return typs(i, t_INT);
  }
  if (t[3]) { *ptp=p; return t_INTMOD; }
  if (t[8]) { *ptp=p; *ptpa=pa; return t_PADIC; }
  return t_INT;
}
#undef LT

GEN
factor0(GEN x,long flag)
{
  long tx=typ(x);

  if (flag<0) return factor(x);
  if (is_matvec_t(tx)) return gboundfact(x,flag);
  if (tx==t_INT || tx==t_FRAC || tx==t_FRACN) return boundfact(x,flag);
  err(talker,"partial factorization is not meaningful here");
  return NULL; /* not reached */
}

GEN
concat_factor(GEN f, GEN g)
{
  GEN h;
  if (lg(f) == 1) return g;
  if (lg(g) == 1) return f;
  h = cgetg(3,t_MAT);
  h[1] = (long)concatsp((GEN)f[1], (GEN)g[1]);
  h[2] = (long)concatsp((GEN)f[2], (GEN)g[2]);
  return h;
}

/* assume f and g coprime integer factorizations */
GEN
merge_factor_i(GEN f, GEN g)
{
  if (lg(f) == 1) return g;
  if (lg(g) == 1) return f;
  return sort_factor_gen(concat_factor(f,g), cmpii);
}

GEN
deg1_from_roots(GEN L, long v)
{
  long i, l = lg(L);
  GEN z = cgetg(l,t_COL);
  for (i=1; i<l; i++)
    z[i] = (long)deg1pol_i(gun, gneg((GEN)z[i]), v);
  return z;
}

GEN
factor(GEN x)
{
  long tx=typ(x), lx, i, j, pa, v, r1;
  gpmem_t av, tetpil;
  GEN  y,p,p1,p2,p3,p4,p5,pol;

  if (is_matvec_t(tx))
  {
    lx=lg(x); y=cgetg(lx,tx);
    for (i=1; i<lx; i++) y[i]=(long)factor((GEN)x[i]);
    return y;
  }
  if (gcmp0(x))
  {
    y=cgetg(3,t_MAT);
    p1=cgetg(2,t_COL); y[1]=(long)p1; p1[1]=lcopy(x);
    p2=cgetg(2,t_COL); y[2]=(long)p2; p2[1]=un;
    return y;
  }
  av = avma;
  switch(tx)
  {
    case t_INT: return decomp(x);

    case t_FRACN:
      return gerepileupto(av, factor(gred(x)));
    case t_FRAC:
      p1 = decomp((GEN)x[1]);
      p2 = decomp((GEN)x[2]); p2[2] = (long)gneg_i((GEN)p2[2]);
      return gerepilecopy(av, merge_factor_i(p1,p2));

    case t_POL:
      tx=poltype(x,&p,&pol,&pa);
      switch(tx)
      {
        case 0: err(impl,"factor for general polynomials");
	case t_INT: return factpol(x,1);
	case t_INTMOD: return factmod(x,p);

	case t_COMPLEX: y=cgetg(3,t_MAT); lx=lgef(x)-2; v=varn(x);
	  av = avma; p1 = roots(x,pa); tetpil = avma;
          p2 = deg1_from_roots(p1, v);
	  y[1]=lpile(av,tetpil,p2);
	  p3=cgetg(lx,t_COL); for (i=1; i<lx; i++) p3[i] = un;
          y[2]=(long)p3; return y;

	case t_REAL: y=cgetg(3,t_MAT); lx=lgef(x)-2; v=varn(x);
	  av=avma; p1=roots(x,pa); tetpil=avma;
	  for(r1=1; r1<lx; r1++)
            if (signe(gmael(p1,r1,2))) break;
	  lx=(r1+lx)>>1; p2=cgetg(lx,t_COL);
	  for(i=1; i<r1; i++)
            p2[i] = (long)deg1pol_i(gun, negr(gmael(p1,i,1)), v);
	  for(   ; i<lx; i++)
	  {
	    GEN a = (GEN) p1[2*i-r1];
	    p = cgetg(5, t_POL); p2[i] = (long)p;
	    p[1] = evalsigne(1) | evalvarn(v) | evallgef(5);
	    p[2] = lnorm(a);
	    p[3] = lmul2n((GEN)a[1],1); setsigne(p[3],-signe(p[3]));
	    p[4] = un;
	  }
	  y[1]=lpile(av,tetpil,p2);
	  p3=cgetg(lx,t_COL); for (i=1; i<lx; i++) p3[i] = un;
          y[2]=(long)p3; return y;

	case t_PADIC: return factorpadic4(x,p,pa);

        default:
        {
          long killv;
	  x = dummycopy(x); lx=lgef(x);
          pol = dummycopy(pol);
          v = manage_var(4,NULL);
          for(i=2; i<lx; i++)
          {
            p1=(GEN)x[i];
            switch(typ(p1))
            {
              case t_QUAD: p1++;
              case t_COMPLEX:
                p2 = cgetg(3, t_POLMOD); x[i] = (long) p2;
                p2[1] = (long)pol;
                p2[2] = (long)deg1pol_i((GEN)p1[2], (GEN)p1[1], v);
            }
          }
          killv = (avma != (gpmem_t)pol);
          if (killv) setvarn(pol, fetch_var());
          switch (typ2(tx))
          {
            case t_INT: p1 = polfnf(x,pol); break;
            case t_INTMOD: p1 = factmod9(x,p,pol); break;
	    default: err(impl,"factor of general polynomial");
              return NULL; /* not reached */
          }
          switch (typ1(tx))
          {
            case t_POLMOD:
              if (killv) delete_var();
              return gerepileupto(av,p1);
            case t_COMPLEX: p5 = gi; break;
            case t_QUAD: p5=cgetg(4,t_QUAD);
              p5[1]=(long)pol; p5[2]=zero; p5[3]=un;
              break;
	    default: err(impl,"factor of general polynomial");
              return NULL; /* not reached */
          }
          p2=(GEN)p1[1];
          for(i=1; i<lg(p2); i++)
          {
            p3=(GEN)p2[i];
            for(j=2; j<lgef(p3); j++)
            {
              p4=(GEN)p3[j];
              if(typ(p4)==t_POLMOD) p3[j]=lsubst((GEN)p4[2],v,p5);
            }
          }
          if (killv) delete_var();
          tetpil=avma; y=cgetg(3,t_MAT);
          y[1]=lcopy(p2);y[2]=lcopy((GEN)p1[2]);
          return gerepile(av,tetpil,y);
        }
      }

    case t_RFRACN:
      return gerepileupto(av, factor(gred_rfrac(x)));
    case t_RFRAC:
      p1=factor((GEN)x[1]);
      p2=factor((GEN)x[2]); p3=gneg_i((GEN)p2[2]);
      tetpil=avma; y=cgetg(3,t_MAT);
      y[1]=lconcat((GEN)p1[1],(GEN)p2[1]);
      y[2]=lconcat((GEN)p1[2],p3);
      return gerepile(av,tetpil,y);
  }
  err(talker,"can't factor %Z",x);
  return NULL; /* not reached */
}
#undef typ1
#undef typ2
#undef typs
#undef tsh

/* assume n != 0, t_INT. Compute x^|n| using left-right binary powering */
GEN
leftright_pow(GEN x, GEN n, void *data,
             GEN (*sqr)(void*,GEN), GEN (*mul)(void*,GEN,GEN))
{
  GEN nd = n+2, y = x;
  long i, m = *nd, j = 1+bfffo((ulong)m);
  gpmem_t av = avma, lim = stack_lim(av, 1);
 
  /* normalize, i.e set highest bit to 1 (we know m != 0) */
  m<<=j; j = BITS_IN_LONG-j;
  /* first bit is now implicit */
  for (i=lgefint(n)-2;;)
  {
    for (; j; m<<=1,j--)
    {
      y = sqr(data,y);
      if (m < 0) y = mul(data,y,x); /* first bit set: multiply by base */
      if (low_stack(lim, stack_lim(av,1)))
      {
        if (DEBUGMEM>1) err(warnmem,"leftright_pow");
        y = gerepilecopy(av, y);
      }
    }
    if (--i == 0) return avma==av? gcopy(y): y;
    m = *++nd; j = BITS_IN_LONG;
  }
}

GEN
divide_conquer_prod(GEN x, GEN (*mul)(GEN,GEN))
{
  long i,k,lx = lg(x);

  if (lx == 1) return gun;
  if (lx == 2) return gcopy((GEN)x[1]);
  x = dummycopy(x); k = lx;
  while (k > 2)
  {
    if (DEBUGLEVEL>7)
      fprintferr("prod: remaining objects %ld\n",k-1);
    lx = k; k = 1;
    for (i=1; i<lx-1; i+=2)
      x[k++] = (long)mul((GEN)x[i],(GEN)x[i+1]);
    if (i < lx) x[k++] = x[i];
  }
  return (GEN)x[1];
}

static GEN static_nf;

static GEN
myidealmulred(GEN x, GEN y) { return idealmulred(static_nf, x, y, 0); }

static GEN
myidealpowred(GEN x, GEN n) { return idealpowred(static_nf, x, n, 0); }

static GEN
myidealmul(GEN x, GEN y) { return idealmul(static_nf, x, y); }

static GEN
myidealpow(GEN x, GEN n) { return idealpow(static_nf, x, n); }

GEN
factorback_i(GEN fa, GEN e, GEN nf, int red)
{
  gpmem_t av = avma;
  long k,l,lx,t = typ(fa);
  GEN p,x;
  GEN (*_mul)(GEN,GEN);
  GEN (*_pow)(GEN,GEN);
  if (!nf && e && lg(e) > 1 && typ(e[1]) != t_INT) { nf = e; e = NULL; }
  if (nf)
  {
    static_nf = nf;
    if (red)
    {
      _mul = &myidealmulred;
      _pow = &myidealpowred;
    }
    else
    {
      _mul = &myidealmul;
      _pow = &myidealpow;
    }
  }
  else
  {
    _mul = &gmul;
    _pow = &powgi;
  }
 
  if (e) /* supplied vector of exponents */
    p = fa;
  else /* genuine factorization */
  {
    if (t != t_MAT)
    {
      if (!is_vec_t(t)) err(talker,"not a factorisation in factorback");
      return gerepileupto(av, divide_conquer_prod(fa, _mul));
    }
    p = (GEN)fa[1];
    e = (GEN)fa[2];
  }
  lx = lg(p);
  t = t_INT; /* dummy */
  /* check whether e is an integral vector of correct length */
  if (is_vec_t(typ(e)) && lx == lg(e))
  {
    for (k=1; k<lx; k++)
      if (typ(e[k]) != t_INT) break;
    if (k == lx) t = t_MAT;
  }
  if (t != t_MAT) err(talker,"not a factorisation in factorback");
  if (lx == 1) return gun;
  x = cgetg(lx,t_VEC);
  for (l=1,k=1; k<lx; k++)
    if (signe(e[k]))
      x[l++] = (long)_pow((GEN)p[k],(GEN)e[k]);
  setlg(x,l);
  return gerepileupto(av, divide_conquer_prod(x, _mul));
}

GEN
factorback0(GEN fa, GEN e, GEN nf)
{
  return factorback_i(fa,e,nf,0);
}

GEN
factorback(GEN fa, GEN nf)
{
  return factorback_i(fa,nf,NULL,0);
}

GEN
gisirreducible(GEN x)
{
  long tx = typ(x), l, i;
  gpmem_t av=avma;
  GEN y;

  if (is_matvec_t(tx))
  {
    l=lg(x); y=cgetg(l,tx);
    for (i=1; i<l; i++) y[i]=(long)gisirreducible((GEN)x[i]);
    return y;
  }
  if (is_intreal_t(tx) || is_frac_t(tx)) return gzero;
  if (tx!=t_POL) err(notpoler,"gisirreducible");
  l=lgef(x); if (l<=3) return gzero;
  y=factor(x); avma=av;
  return (lgef(gcoeff(y,1,1))==l)?gun:gzero;
}

/*******************************************************************/
/*                                                                 */
/*                         GENERIC GCD                             */
/*                                                                 */
/*******************************************************************/

GEN
gcd0(GEN x, GEN y, long flag)
{
  switch(flag)
  {
    case 0: return gassoc_proto(ggcd,x,y);
    case 1: return gassoc_proto(modulargcd,x,y);
    case 2: return gassoc_proto(srgcd,x,y);
    default: err(flagerr,"gcd");
  }
  return NULL; /* not reached */
}

/* x is a COMPLEX or a QUAD */
static GEN
triv_cont_gcd(GEN x, GEN y)
{
  gpmem_t av = avma, tetpil;
  GEN p1 = (typ(x)==t_COMPLEX)? ggcd((GEN)x[1],(GEN)x[2])
                              : ggcd((GEN)x[2],(GEN)x[3]);
  tetpil=avma; return gerepile(av,tetpil,ggcd(p1,y));
}

static GEN
cont_gcd(GEN x, GEN y)
{
  gpmem_t av = avma, tetpil;
  GEN p1 = content(x);

  tetpil=avma; return gerepile(av,tetpil,ggcd(p1,y));
}

/* y is a PADIC, x a rational number or an INTMOD */
static GEN
padic_gcd(GEN x, GEN y)
{
  long v = ggval(x,(GEN)y[2]), w = valp(y);
  if (w < v) v = w;
  return gpuigs((GEN)y[2], v);
}

/* x,y in Z[i], at least one of which is t_COMPLEX */
static GEN
gaussian_gcd(GEN x, GEN y)
{
  gpmem_t av = avma;
  GEN dx = denom(x);
  GEN dy = denom(y);
  GEN den = mpppcm(dx, dy);

  x = gmul(x, dx);
  y = gmul(y, dy);
  while (!gcmp0(y))
  {
    GEN z = gdiv(x,y);
    GEN r0 = greal(z), r = gfloor(r0);
    GEN i0 = gimag(z), i = gfloor(i0);
    if (gcmp(gsub(r0,r), ghalf) > 0) r = addis(r,1);
    if (gcmp(gsub(i0,i), ghalf) > 0) i = addis(i,1);
    if (gcmp0(i)) z = r;
    else
    {
      z = cgetg(3, t_COMPLEX);
      z[1] = (long)r;
      z[2] = (long)i;
    }
    z = gsub(x, gmul(z,y));
    x = y; y = z;
  }
  if (signe(greal(x)) < 0) x = gneg(x);
  if (signe(gimag(x)) < 0) x = gmul(x, gi);
  if (typ(x) == t_COMPLEX)
  {
    if      (gcmp0((GEN)x[2])) x = (GEN)x[1];
    else if (gcmp0((GEN)x[1])) x = (GEN)x[2];
  }
  return gerepileupto(av, gdiv(x, den));
}

#define fix_frac(z) if (signe(z[2])<0)\
{\
  setsigne(z[1],-signe(z[1]));\
  setsigne(z[2],1);\
}

int
isrational(GEN x)
{
  long i, t = typ(x);
  if (t != t_POL) return is_rational_t(t);
  for (i=lgef(x)-1; i>1; i--)
  {
    t = typ(x[i]);
    if (!is_rational_t(t)) return 0;
  }
  return 1;
}

static int
cx_isrational(GEN x)
{ 
  return (isrational((GEN)x[1]) && isrational((GEN)x[2]));
}

GEN
ggcd(GEN x, GEN y)
{
  long l, i, vx, vy, tx = typ(x), ty = typ(y);
  gpmem_t av, tetpil;
  GEN p1,z;

  if (tx>ty) { swap(x,y); lswap(tx,ty); }
  if (is_matvec_t(ty))
  {
    l=lg(y); z=cgetg(l,ty);
    for (i=1; i<l; i++) z[i]=lgcd(x,(GEN)y[i]);
    return z;
  }
  if (is_noncalc_t(tx) || is_noncalc_t(ty)) err(operf,"g",x,y);
  if (gcmp0(x)) return gcopy(y);
  if (gcmp0(y)) return gcopy(x);
  if (is_const_t(tx))
  {
    if (ty == t_FRACN)
    {
      if (tx==t_INTMOD)
      {
        av=avma; y = gred(y); tetpil=avma;
        return gerepile(av,tetpil,ggcd(x,y));
      }
      ty = t_FRAC;
    }
    if (tx == t_FRACN) tx = t_FRAC;
    if (ty == tx) switch(tx)
    {
      case t_INT:
        return mppgcd(x,y);

      case t_INTMOD: z=cgetg(3,t_INTMOD);
        if (egalii((GEN)x[1],(GEN)y[1]))
          { copyifstack(x[1],z[1]); }
        else
          z[1] = lmppgcd((GEN)x[1],(GEN)y[1]);
        if (gcmp1((GEN)z[1])) z[2] = zero;
        else
        {
          av = avma; p1 = mppgcd((GEN)z[1],(GEN)x[2]);
          if (!is_pm1(p1)) p1 = gerepileuptoint(av, mppgcd(p1,(GEN)y[2]));
          z[2] = (long)p1;
        }
        return z;

      case t_FRAC: z=cgetg(3,t_FRAC);
        z[1] = (long)mppgcd((GEN)x[1], (GEN)y[1]);
        z[2] = (long)mpppcm((GEN)x[2], (GEN)y[2]);
        return z;

      case t_COMPLEX:
        if (cx_isrational(x) && cx_isrational(y)) return gaussian_gcd(x,y);
        return triv_cont_gcd(y,x);

      case t_PADIC:
        if (!egalii((GEN)x[2],(GEN)y[2])) return gun;
        vx = valp(x);
        vy = valp(y); return gpuigs((GEN)y[2], min(vy,vx));

      case t_QUAD:
        av=avma; p1=gdiv(x,y);
        if (gcmp0((GEN)p1[3]))
        {
          p1=(GEN)p1[2];
          if (typ(p1)==t_INT) { avma=av; return gcopy(y); }
          tetpil=avma; return gerepile(av,tetpil, gdiv(y,(GEN)p1[2]));
        }
        if (typ(p1[2])==t_INT && typ(p1[3])==t_INT) {avma=av; return gcopy(y);}
        p1 = ginv(p1); avma=av;
        if (typ(p1[2])==t_INT && typ(p1[3])==t_INT) return gcopy(x);
        return triv_cont_gcd(y,x);

      default: return gun; /* t_REAL */
    }
    if (is_const_t(ty)) switch(tx)
    {
      case t_INT:
        switch(ty)
        {
          case t_INTMOD: z = cgetg(3,t_INTMOD);
            copyifstack(y[1],z[1]); av=avma;
            p1 = mppgcd((GEN)y[1],(GEN)y[2]);
            if (!is_pm1(p1)) p1 = gerepileuptoint(av, mppgcd(x,p1));
            z[2] = (long)p1; return z;

          case t_FRAC: z = cgetg(3,t_FRAC);
            z[1] = lmppgcd(x,(GEN)y[1]);
            z[2] = licopy((GEN)y[2]); return z;

          case t_COMPLEX:
            if (cx_isrational(y)) return gaussian_gcd(x,y);
          case t_QUAD:
            return triv_cont_gcd(y,x);

          case t_PADIC:
            return padic_gcd(x,y);

          default: return gun; /* t_REAL */
        }

      case t_INTMOD:
        switch(ty)
        {
          case t_FRAC:
            av = avma; p1=mppgcd((GEN)x[1],(GEN)y[2]); avma = av;
            if (!is_pm1(p1)) err(operi,"g",x,y);
            return ggcd((GEN)y[1], x);

          case t_COMPLEX: case t_QUAD:
            return triv_cont_gcd(y,x);

          case t_PADIC:
            return padic_gcd(x,y);
        }

      case t_FRAC:
        switch(ty)
        {
          case t_COMPLEX:
            if (cx_isrational(y)) return gaussian_gcd(x,y);
          case t_QUAD:
            return triv_cont_gcd(y,x);

          case t_PADIC:
            return padic_gcd(x,y);
        }

      case t_COMPLEX: /* ty = PADIC or QUAD */
        return triv_cont_gcd(x,y);

      case t_PADIC: /* ty = QUAD */
        return triv_cont_gcd(y,x);

      default: return gun; /* tx = t_REAL */
    }
    return cont_gcd(y,x);
  }

  vx = gvar9(x); vy = gvar9(y);
  if (vy<vx) return cont_gcd(y,x);
  if (vx<vy) return cont_gcd(x,y);
  switch(tx)
  {
    case t_POLMOD:
      switch(ty)
      {
	case t_POLMOD: z=cgetg(3,t_POLMOD);
          if (gegal((GEN)x[1],(GEN)y[1]))
	    { copyifstack(x[1],z[1]); }
          else
            z[1] = lgcd((GEN)x[1],(GEN)y[1]);
	  if (lgef(z[1])<=3) z[2]=zero;
	  else
	  {
	    av=avma; p1=ggcd((GEN)z[1],(GEN)x[2]);
	    if (lgef(p1)>3)
	    {
	      tetpil=avma;
              p1=gerepile(av,tetpil,ggcd(p1,(GEN)y[2]));
	    }
	    z[2]=(long)p1;
	  }
	  return z;

	case t_POL: z=cgetg(3,t_POLMOD);
          copyifstack(x[1],z[1]); av=avma;
          p1=ggcd((GEN)x[1],(GEN)x[2]);
	  if (lgef(p1)>3)
            { tetpil=avma; p1=gerepile(av,tetpil,ggcd(y,p1)); }
	  z[2]=(long)p1; return z;

	case t_RFRAC:
	  av = avma; p1=ggcd((GEN)x[1],(GEN)y[2]); avma = av;
          if (!gcmp1(p1)) err(operi,"g",x,y);
	  return ggcd((GEN)y[1],x);

	case t_RFRACN:
	  av=avma; p1=gred_rfrac(y); tetpil=avma;
	  return gerepile(av,tetpil,ggcd(p1,x));
      }
      break;

    case t_POL:
      switch(ty)
      {
	case t_POL:
	  return srgcd(x,y);

	case t_SER:
	  return gpuigs(polx[vx],min(valp(y),gval(x,vx)));

	case t_RFRAC: case t_RFRACN: av=avma; z=cgetg(3,ty);
          z[1]=lgcd(x,(GEN)y[1]);
          z[2]=lcopy((GEN)y[2]); return z;
      }
      break;

    case t_SER:
      switch(ty)
      {
	case t_SER:
	  return gpuigs(polx[vx],min(valp(x),valp(y)));

	case t_RFRAC: case t_RFRACN:
	  return gpuigs(polx[vx],min(valp(x),gval(y,vx)));
      }
      break;

    case t_RFRAC: case t_RFRACN: z=cgetg(3,ty);
      if (!is_rfrac_t(ty)) err(operf,"g",x,y);
      p1 = gdiv((GEN)y[2], ggcd((GEN)x[2], (GEN)y[2]));
      tetpil = avma;
      z[2] = lpile((gpmem_t)z,tetpil,gmul(p1, (GEN)x[2]));
      z[1] = lgcd((GEN)x[1], (GEN)y[1]); return z;
  }
  err(operf,"g",x,y);
  return NULL; /* not reached */
}

GEN glcm0(GEN x, GEN y)
{
  return gassoc_proto(glcm,x,y);
}

GEN
glcm(GEN x, GEN y)
{
  long tx, ty, i, l;
  gpmem_t av;
  GEN p1,p2,z;

  ty = typ(y);
  if (is_matvec_t(ty))
  {
    l=lg(y); z=cgetg(l,ty);
    for (i=1; i<l; i++) z[i]=(long)glcm(x,(GEN)y[i]);
    return z;
  }
  tx = typ(x);
  if (is_matvec_t(tx))
  {
    l=lg(x); z=cgetg(l,tx);
    for (i=1; i<l; i++) z[i]=(long)glcm((GEN)x[i],y);
    return z;
  }
  if (tx==t_INT && ty==t_INT) return mpppcm(x,y);
  if (gcmp0(x)) return gzero;

  av = avma;
  p1 = ggcd(x,y); if (!gcmp1(p1)) y = gdiv(y,p1);
  p2 = gmul(x,y);
  switch(typ(p2))
  {
    case t_INT: if (signe(p2)<0) setsigne(p2,1);
      break;
    case t_POL:
      if (lgef(p2) <= 2) break;
      p1=leading_term(p2);
      if (typ(p1)==t_INT && signe(p1)<0) p2=gneg(p2);
  }
  return gerepileupto(av,p2);
}

extern int approx_0(GEN x, GEN y);

/* x + r ~ x ? Assume x,r are t_POL, deg(r) <= deg(x) */
static int
pol_approx0(GEN r, GEN x, int exact)
{
  long i, lx,lr;
  if (exact) return gcmp0(r);
  lx = lgef(x);
  lr = lgef(r); if (lr < lx) lx = lr;
  for (i=2; i<lx; i++)
    if (!approx_0((GEN)r[i], (GEN)x[i])) return 0;
  return 1;
}

static GEN
polgcdnun(GEN x, GEN y)
{
  gpmem_t av1, av = avma, lim = stack_lim(av, 1);
  GEN r, yorig = y;
  int exact = !(isinexactreal(x) || isinexactreal(y));

  for(;;)
  {
    av1 = avma; r = gres(x,y);
    if (pol_approx0(r, x, exact))
    {
      avma = av1;
      if (lgef(y) == 3 && !exact) { avma = av; return gun; }
      return (y==yorig)? gcopy(y): gerepileupto(av,y);
    }
    x = y; y = r;
    if (low_stack(lim,stack_lim(av,1)))
    {
      GEN *gptr[2]; x = gcopy(x); gptr[0]=&x; gptr[1]=&y;
      if(DEBUGMEM>1) err(warnmem,"polgcdnun");
      gerepilemanysp(av,av1,gptr,2);
    }
  }
}

/* return 1 if coeff explosion is not possible */
static int
issimplefield(GEN x)
{
  long lx,i;
  switch(typ(x))
  {
    case t_REAL: case t_INTMOD: case t_PADIC: case t_SER:
      return 1;
    case t_POL:
      lx=lgef(x);
      for (i=2; i<lx; i++)
	if (issimplefield((GEN)x[i])) return 1;
      return 0;
    case t_COMPLEX: case t_POLMOD:
      return issimplefield((GEN)x[1]) || issimplefield((GEN)x[2]);
  }
  return 0;
}

static int
can_use_modular_gcd(GEN x, GEN *mod, long *v)
{
  GEN p1, p2;
  long i;
  for (i=lgef(x)-1; i>1; i--)
  {
    p1 = (GEN)x[i];
    switch(typ(p1))
    {
      case t_INT: case t_FRAC: break;
      case t_POLMOD:
        p2 = (GEN)p1[1];
        if (*mod)
        {
          if (!isrational((GEN)p1[2])) return 0;
          if (!gegal(*mod,p2)) return 0;
        } else
        {
          if (!isrational(p2)) return 0;
          *mod = p2; *v = varn(p2);
        }
        break;
      case t_POL:
        if (!isrational(p1)) return 0;
        if (*v >= 0) 
        {
          if (*v != varn(p1)) return 0;
        } else *v = varn(p1);
        break;
      default: return 0;
    }
  }
  return 1;
}

static int
isinexactfield(GEN x)
{
  long lx,i;
  switch(typ(x))
  {
    case t_REAL: case t_PADIC: case t_SER:
      return 1;
    case t_POL:
      lx=lgef(x); if (lx == 2) return 0;/*true 0 polynomial*/
      for (i=2; i<lx; i++)
	if (isinexactfield((GEN)x[i])) return 1;
      return 0;
    case t_COMPLEX: case t_POLMOD:
      return isinexactfield((GEN)x[1]) || isinexactfield((GEN)x[2]);
  }
  return 0;
}

static GEN
gcdmonome(GEN x, GEN y)
{
  long dx=degpol(x), v=varn(x), e=gval(y, v);
  gpmem_t tetpil, av=avma;
  GEN p1,p2;

  if (dx < e) e = dx;
  p1=ggcd(leading_term(x),content(y)); p2=gpuigs(polx[v],e);
  tetpil=avma; return gerepile(av,tetpil,gmul(p1,p2));
}

/***********************************************************************/
/**                                                                   **/
/**                        GENERIC EXTENDED GCD                       **/
/**                                                                   **/
/***********************************************************************/

static GEN
polinvinexact(GEN x, GEN y)
{
  gpmem_t av = avma;
  long i,dx=degpol(x),dy=degpol(y),lz=dx+dy;
  GEN v,z;

  if (dx < 0 || dy < 0) err(talker,"non-invertible polynomial in polinvmod");
  z=cgetg(dy+2,t_POL); z[1]=y[1];
  v=cgetg(lz+1,t_COL);
  for (i=1; i<lz; i++) v[i]=zero;
  v[lz]=un; v=gauss(sylvestermatrix(y,x),v);
  for (i=2; i<dy+2; i++) z[i]=v[lz-i+2];
  z = normalizepol_i(z, dy+2);
  return gerepilecopy(av,z);
}

static GEN
polinvmod(GEN x, GEN y)
{
  long tx, vx=varn(x), vy=varn(y);
  gpmem_t av, av1;
  GEN u,v,d,p1;

  while (vx!=vy)
  {
    if (vx > vy)
    {
      d=cgetg(3,t_RFRAC);
      d[1]=(long)polun[vx];
      d[2]=lcopy(x); return d;
    }
    if (lgef(x)!=3) err(talker,"non-invertible polynomial in polinvmod");
    x=(GEN)x[2]; vx=gvar(x);
  }
  tx=typ(x);
  if (tx==t_POL)
  {
    if (isinexactfield(x) || isinexactfield(y))
      return polinvinexact(x,y);

    av=avma; d=subresext(x,y,&u,&v);
    if (gcmp0(d)) err(talker,"non-invertible polynomial in polinvmod");
    if (typ(d)==t_POL && varn(d)==vx)
    {
      if (lgef(d)>3) err(talker,"non-invertible polynomial in polinvmod");
      d=(GEN)d[2];
    }
    av1=avma; return gerepile(av,av1,gdiv(u,d));
  }
  if (!is_rfrac_t(tx)) err(typeer,"polinvmod");
  av=avma; p1=gmul((GEN)x[1],polinvmod((GEN)x[2],y));
  av1=avma; return gerepile(av,av1,gmod(p1,y));
}

GEN
gbezout(GEN x, GEN y, GEN *u, GEN *v)
{
  long tx=typ(x),ty=typ(y);

  if (tx==t_INT && ty==t_INT) return bezout(x,y,u,v);
  if (!is_extscalar_t(tx) || !is_extscalar_t(ty)) err(typeer,"gbezout");
  return bezoutpol(x,y,u,v);
}

GEN
vecbezout(GEN x, GEN y)
{
  GEN z=cgetg(4,t_VEC);
  z[3]=(long)gbezout(x,y,(GEN*)(z+1),(GEN*)(z+2));
  return z;
}

GEN
vecbezoutres(GEN x, GEN y)
{
  GEN z=cgetg(4,t_VEC);
  z[3]=(long)subresext(x,y,(GEN*)(z+1),(GEN*)(z+2));
  return z;
}

/*******************************************************************/
/*                                                                 */
/*                    CONTENT / PRIMITIVE PART                     */
/*                                                                 */
/*******************************************************************/

GEN
content(GEN x)
{
  long lx,i,tx=typ(x);
  gpmem_t av, tetpil;
  GEN p1,p2;

  if (is_scalar_t(tx))
    return tx==t_POLMOD? content((GEN)x[2]): gcopy(x);
  av = avma;
  switch(tx)
  {
    case t_RFRAC: case t_RFRACN:
      p1=content((GEN)x[1]);
      p2=content((GEN)x[2]); tetpil=avma;
      return gerepile(av,tetpil,gdiv(p1,p2));

    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); if (lx==1) return gun;
      p1=content((GEN)x[1]);
      for (i=2; i<lx; i++) p1 = ggcd(p1,content((GEN)x[i]));
      return gerepileupto(av,p1);

    case t_POL:
      if (!signe(x)) return gzero;
      lx = lgef(x); break;
    case t_SER:
      if (!signe(x)) return gzero;
      lx = lg(x); break;
    case t_QFR: case t_QFI:
      lx = 4; break;

    default: err(typeer,"content");
      return NULL; /* not reached */
  }
  for (i=lontyp[tx]; i<lx; i++)
    if (typ(x[i]) != t_INT) break;
  lx--; p1=(GEN)x[lx];
  if (i > lx)
  { /* integer coeffs */
    while (lx>lontyp[tx])
    {
      lx--; p1=mppgcd(p1,(GEN)x[lx]);
      if (is_pm1(p1)) { avma=av; return gun; }
    }
  }
  else
  {
    while (lx>lontyp[tx])
    {
      lx--; p1=ggcd(p1,(GEN)x[lx]);
    }
    if (isinexactreal(p1)) { avma=av; return gun; }
  }
  return av==avma? gcopy(p1): gerepileupto(av,p1);
}

GEN
primitive_part(GEN x, GEN *ptc)
{
  GEN c = content(x);
  if (gcmp1(c)) c = NULL; else x = gdiv(x,c);
  if (ptc) *ptc = c;
  return x;
}

GEN
primpart(GEN x)
{
  return primitive_part(x, NULL);
}

/*******************************************************************/
/*                                                                 */
/*                           SUBRESULTANT                          */
/*                                                                 */
/*******************************************************************/
/* for internal use */
GEN
gdivexact(GEN x, GEN y)
{
  long i,lx;
  GEN z;
  if (gcmp1(y)) return x;
  switch(typ(x))
  {
    case t_INT:
      if (typ(y)==t_INT) return diviiexact(x,y);
      if (!signe(x)) return gzero;
      break;
    case t_INTMOD:
    case t_POLMOD: return gmul(x,ginv(y));
    case t_POL:
      switch(typ(y))
      {
        case t_INTMOD:
        case t_POLMOD: return gmul(x,ginv(y));
        case t_POL:
          if (varn(x)==varn(y)) return poldivres(x,y, ONLY_DIVIDES_EXACT);
      }
      lx = lgef(x); z = cgetg(lx,t_POL);
      for (i=2; i<lx; i++) z[i]=(long)gdivexact((GEN)x[i],y);
      z[1]=x[1]; return z;
    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); z = cgetg(lx, typ(x));
      for (i=1; i<lx; i++) z[i]=(long)gdivexact((GEN)x[i],y);
      return z;
  }
  if (DEBUGLEVEL) err(warner,"missing case in gdivexact");
  return gdiv(x,y);
}

static GEN
init_resultant(GEN x, GEN y)
{
  long tx,ty;
  if (gcmp0(x) || gcmp0(y)) return gzero;
  tx = typ(x); ty = typ(y);
  if (is_scalar_t(tx) || is_scalar_t(ty))
  {
    if (tx==t_POL) return gpuigs(y,degpol(x));
    if (ty==t_POL) return gpuigs(x,degpol(y));
    return gun;
  }
  if (tx!=t_POL || ty!=t_POL) err(typeer,"subresall");
  if (varn(x)==varn(y)) return NULL;
  return (varn(x)<varn(y))? gpuigs(y,degpol(x)): gpuigs(x,degpol(y));
}

/* return coefficients s.t x = x_0 X^n + ... + x_n */
static GEN
revpol(GEN x)
{
  long i,n = degpol(x);
  GEN y = cgetg(n+3,t_POL);
  y[1] = x[1]; x += 2; y += 2;
  for (i=0; i<=n; i++) y[i] = x[n-i];
  return y;
}

/* assume dx >= dy, y non constant */
static GEN
pseudorem_i(GEN x, GEN y, GEN mod)
{
  long vx = varn(x), dx, dy, dz, i, lx, p;
  gpmem_t av = avma, av2, lim;

  if (!signe(y)) err(talker,"euclidean division by zero (pseudorem)");
  (void)new_chunk(2);
  dx=degpol(x); x = revpol(x);
  dy=degpol(y); y = revpol(y); dz=dx-dy; p = dz+1;
  av2 = avma; lim = stack_lim(av2,1);
  for (;;)
  {
    x[0] = lneg((GEN)x[0]); p--;
    for (i=1; i<=dy; i++)
    {
      x[i] = ladd(gmul((GEN)y[0], (GEN)x[i]), gmul((GEN)x[0],(GEN)y[i]));
      if (mod) x[i] = lmod((GEN)x[i], mod);
    }
    for (   ; i<=dx; i++)
    {
      x[i] = lmul((GEN)y[0], (GEN)x[i]);
      if (mod) x[i] = lmod((GEN)x[i], mod);
    }
    do { x++; dx--; } while (dx >= 0 && gcmp0((GEN)x[0]));
    if (dx < dy) break;
    if (low_stack(lim,stack_lim(av2,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"pseudorem dx = %ld >= %ld",dx,dy);
      gerepilemanycoeffs(av2,x,dx+1);
    }
  }
  if (dx < 0) return zeropol(vx);
  lx = dx+3; x -= 2;
  x[0]=evaltyp(t_POL) | evallg(lx);
  x[1]=evalsigne(1) | evalvarn(vx) | evallgef(lx);
  x = revpol(x) - 2;
  if (mod) x = gmul(x, gmodulcp(gun, mod));
  if (p)
  { /* multiply by y[0]^p   [beware dummy vars from FpY_FpXY_resultant] */  
    GEN t = (GEN)y[0];
    if (mod) t = gmodulcp(t, mod);
    t = gpowgs(t, p);
    for (i=2; i<lx; i++) x[i] = lmul((GEN)x[i], t);
    return gerepileupto(av, x);
  }
  return gerepilecopy(av, x);
}

GEN
pseudorem(GEN x, GEN y) { return pseudorem_i(x,y, NULL); }

extern void gerepilemanycoeffs2(gpmem_t av, GEN x, long n, GEN y, long o);

/* assume dx >= dy, y non constant
 * Compute z,r s.t lc(y)^(dx-dy+1) x = z y + r */
GEN
pseudodiv(GEN x, GEN y, GEN *ptr)
{
  long vx = varn(x), dx, dy, dz, i, iz, lx, lz, p;
  gpmem_t av = avma, av2, lim;
  GEN z, r, ypow;

  if (!signe(y)) err(talker,"euclidean division by zero (pseudodiv)");
  (void)new_chunk(2);
  dx=degpol(x); x = revpol(x);
  dy=degpol(y); y = revpol(y); dz=dx-dy; p = dz+1;
  lz = dz+3; z = cgetg(lz, t_POL) + 2;
  ypow = new_chunk(dz+1);
  ypow[0] = un;
  for (i=1; i<=dz; i++) ypow[i] = lmul((GEN)ypow[i-1], (GEN)y[0]);
  av2 = avma; lim = stack_lim(av2,1);
  for (iz=0;;)
  {
    p--;
    z[iz++] = lmul((GEN)x[0], (GEN)ypow[p]);
    x[0] = lneg((GEN)x[0]);
    for (i=1; i<=dy; i++)
      x[i] = ladd(gmul((GEN)y[0], (GEN)x[i]), gmul((GEN)x[0],(GEN)y[i]));
    for (   ; i<=dx; i++)
      x[i] = lmul((GEN)y[0], (GEN)x[i]);
    x++; dx--; 
    while (dx >= dy && gcmp0((GEN)x[0])) { x++; dx--; z[iz++] = zero; }
    if (dx < dy) break;
    if (low_stack(lim,stack_lim(av2,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"pseudodiv dx = %ld >= %ld",dx,dy);
      gerepilemanycoeffs2(av2,x,dx+1, z,iz);
    }
  }
  while (dx >= 0 && gcmp0((GEN)x[0])) { x++; dx--; }
  if (dx < 0) 
    x = zeropol(vx);
  else
  {
    lx = dx+3; x -= 2;
    x[0] = evaltyp(t_POL) | evallg(lx);
    x[1] = evalsigne(1) | evalvarn(vx) | evallgef(lx);
    x = revpol(x) - 2;
  }

  z -= 2;
  z[0] = evaltyp(t_POL) | evallg(lz);
  z[1] = evalsigne(1) | evalvarn(vx) | evallgef(lz);
  z = revpol(z) - 2;
  r = gmul(x, (GEN)ypow[p]);
  {
    GEN *gptr[2]; gptr[0] = &z; gptr[1] = &r;
    gerepilemany(av,gptr,2);
  }
  *ptr = r; return z;
}

/* Return resultant(u,v). If sol != NULL: set *sol to the last non-zero
 * polynomial in the prs IF the sequence was computed, and gzero otherwise */
GEN
subresall(GEN u, GEN v, GEN *sol)
{
  gpmem_t av, av2, lim;
  long degq,dx,dy,du,dv,dr,signh;
  GEN z,g,h,r,p1,p2,cu,cv;

  if (sol) *sol=gzero;
  if ((r = init_resultant(u,v))) return r;

  if (isinexactfield(u) || isinexactfield(v)) return resultant2(u,v);
  dx=degpol(u); dy=degpol(v); signh=1;
  if (dx < dy)
  {
    swap(u,v); lswap(dx,dy);
    if (both_odd(dx, dy)) signh = -signh;
  }
  if (dy==0) return gpowgs((GEN)v[2],dx);
  av = avma;
  u = primitive_part(u, &cu);
  v = primitive_part(v, &cv);
  g = h = gun; av2 = avma; lim = stack_lim(av2,1);
  for(;;)
  {
    r = pseudorem(u,v); dr = lgef(r);
    if (dr == 2)
    {
      if (sol) { avma = (gpmem_t)(r+2); *sol=gerepileupto(av,v); } else avma = av;
      return gzero;
    }
    du = degpol(u); dv = degpol(v); degq = du-dv;
    u = v; p1 = g; g = leading_term(u);
    switch(degq)
    {
      case 0: break;
      case 1:
        p1 = gmul(h,p1); h = g; break;
      default:
        p1 = gmul(gpowgs(h,degq),p1);
        h = gdivexact(gpowgs(g,degq), gpowgs(h,degq-1));
    }
    if (both_odd(du,dv)) signh = -signh;
    v = gdivexact(r,p1);
    if (dr==3) break;
    if (low_stack(lim,stack_lim(av2,1)))
    {
      GEN *gptr[4]; gptr[0]=&u; gptr[1]=&v; gptr[2]=&g; gptr[3]=&h;
      if(DEBUGMEM>1) err(warnmem,"subresall, dr = %ld",dr);
      gerepilemany(av2,gptr,4);
    }
  }
  z = (GEN)v[2];
  if (dv > 1) z = gdivexact(gpowgs(z,dv), gpowgs(h,dv-1));
  if (signh < 0) z = gneg(z); /* z = resultant(ppart(x), ppart(y)) */
  p2 = gun;
  if (cu) p2 = gmul(p2, gpowgs(cu,dy));
  if (cv) p2 = gmul(p2, gpowgs(cv,dx));
  z = gmul(z, p2);

  if (sol) u = gclone(u);
  z = gerepileupto(av, z);
  if (sol) { *sol = forcecopy(u); gunclone(u); }
  return z;
}

static GEN
scalar_res(GEN x, GEN y, GEN *U, GEN *V)
{
  *V=gpuigs(y,degpol(x)-1); *U=gzero; return gmul(y,*V);
}

/* compute U, V s.t Ux + Vy = resultant(x,y) */
GEN
subresext(GEN x, GEN y, GEN *U, GEN *V)
{
  gpmem_t av, av2, tetpil, lim;
  long degq,tx,ty,dx,dy,du,dv,dr,signh;
  GEN q,z,g,h,r,p1,p2,cu,cv,u,v,um1,uze,vze,xprim,yprim;

  if (gcmp0(x) || gcmp0(y)) { *U = *V = gzero; return gzero; }
  tx=typ(x); ty=typ(y);
  if (is_scalar_t(tx) || is_scalar_t(ty))
  {
    if (tx==t_POL) return scalar_res(x,y,U,V);
    if (ty==t_POL) return scalar_res(y,x,V,U);
    *U = ginv(x); *V = gzero; return gun;
  }
  if (tx!=t_POL || ty!=t_POL) err(typeer,"subresext");
  if (varn(x) != varn(y))
    return (varn(x)<varn(y))? scalar_res(x,y,U,V)
                            : scalar_res(y,x,V,U);
  dx = degpol(x); dy = degpol(y); signh = 1;
  if (dx < dy)
  {
    pswap(U,V); lswap(dx,dy); swap(x,y);
    if (both_odd(dx, dy)) signh = -signh;
  }
  if (dy == 0)
  {
    *V = gpowgs((GEN)y[2],dx-1);
    *U = gzero; return gmul(*V,(GEN)y[2]);
  }
  av = avma;
  u = primitive_part(x, &cu); xprim = u;
  v = primitive_part(y, &cv); yprim = v;
  g = h = gun; av2 = avma; lim = stack_lim(av2,1);
  um1 = gun; uze = gzero;
  for(;;)
  {
    q = pseudodiv(u,v, &r); dr = lgef(r);
    if (dr == 2) { *U = *V = gzero; avma = av; return gzero; }

    du = degpol(u); dv = degpol(v); degq = du-dv;
    /* lead(v)^(degq + 1) * um1 - q * uze */
    p1 = gsub(gmul(gpowgs((GEN)v[dv+2],degq+1),um1), gmul(q,uze));
    um1 = uze; uze = p1;
    u = v; p1 = g; g = leading_term(u);
    switch(degq)
    {
      case 0: break;
      case 1: p1 = gmul(h,p1); h = g; break;
      default:
        p1 = gmul(gpowgs(h,degq),p1);
        h = gdivexact(gpowgs(g,degq), gpowgs(h,degq-1));
    }
    if (both_odd(du, dv)) signh = -signh;
    v  = gdivexact(r,p1);
    uze= gdivexact(uze,p1);
    if (dr==3) break;
    if (low_stack(lim,stack_lim(av2,1)))
    {
      GEN *gptr[6]; gptr[0]=&u; gptr[1]=&v; gptr[2]=&g; gptr[3]=&h;
      gptr[4]=&uze; gptr[5]=&um1;
      if(DEBUGMEM>1) err(warnmem,"subresext, dr = %ld",dr);
      gerepilemany(av2,gptr,6);
    }
  }
  z = (GEN)v[2];
  if (dv > 1) 
  {
    /* z = gdivexact(gpowgs(z,dv), gpowgs(h,dv-1)); */
    p1 = gpowgs(gdiv(z,h),dv-1);
    z = gmul(z,p1); uze = gmul(uze,p1);
  }
  if (signh < 0) { z = gneg_i(z); uze = gneg_i(uze); }
  p1 = gadd(z, gneg(gmul(uze,xprim)));
  if (!poldivis(p1,yprim,&vze)) err(bugparier,"subresext");
  /* uze ppart(x) + vze ppart(y) = z = resultant(ppart(x), ppart(y)), */
  p2 = gun;
  if (cu) p2 = gmul(p2, gpowgs(cu,dy));
  if (cv) p2 = gmul(p2, gpowgs(cv,dx));
  cu = cu? gdiv(p2,cu): p2;
  cv = cv? gdiv(p2,cv): p2;

  tetpil = avma;
  z = gmul(z,p2); uze = gmul(uze,cu); vze = gmul(vze,cv);
  {
    GEN *gptr[3]; gptr[0]=&z; gptr[1]=&uze; gptr[2]=&vze;
    gerepilemanysp(av,tetpil,gptr,3); 
  }
  *U = uze; *V = vze; return z;
}

static GEN
scalar_bezout(GEN x, GEN y, GEN *U, GEN *V)
{
  *U=gzero; *V=ginv(y); return polun[varn(x)];
}

static GEN
zero_bezout(GEN y, GEN *U, GEN *V)
{
  GEN x=content(y);
  *U=gzero; *V = ginv(x); return gmul(y,*V);
}

/* compute U, V s.t Ux + Vy = GCD(x,y) using subresultant */
GEN
bezoutpol(GEN x, GEN y, GEN *U, GEN *V)
{
  gpmem_t av, av2, tetpil, lim;
  long degq,tx,ty,dx,dy,du,dv,dr;
  GEN q,z,g,h,r,p1,cu,cv,u,v,um1,uze,vze,xprim,yprim, *gptr[3];

  if (gcmp0(x)) return zero_bezout(y,U,V);
  if (gcmp0(y)) return zero_bezout(x,V,U);
  tx=typ(x); ty=typ(y); av=avma;
  if (is_scalar_t(tx) || is_scalar_t(ty))
  {
    if (tx==t_POL) return scalar_bezout(x,y,U,V);
    if (ty==t_POL) return scalar_bezout(y,x,V,U);
    *U = ginv(x); *V = gzero; return polun[0];
  }
  if (tx!=t_POL || ty!=t_POL) err(typeer,"bezoutpol");
  if (varn(x)!=varn(y))
    return (varn(x)<varn(y))? scalar_bezout(x,y,U,V)
                            : scalar_bezout(y,x,V,U);
  dx = degpol(x); dy = degpol(y);
  if (dx < dy)
  {
    pswap(U,V); lswap(dx,dy); swap(x,y);
  }
  if (dy==0) return scalar_bezout(x,y,U,V);

  u = primitive_part(x, &cu); xprim = u;
  v = primitive_part(y, &cv); yprim = v;
  g = h = gun; av2 = avma; lim = stack_lim(av2,1);
  um1 = gun; uze = gzero;
  for(;;)
  {
    q = pseudodiv(u,v, &r); dr = lgef(r);
    if (dr == 2) break;

    du = degpol(u); dv = degpol(v); degq = du-dv;
    p1 = gsub(gmul(gpowgs((GEN)v[dv+2],degq+1),um1), gmul(q,uze));
    um1 = uze; uze = p1;
    u = v; p1 = g; g  = leading_term(u);
    switch(degq)
    {
      case 0: break;
      case 1:
        p1 = gmul(h,p1); h = g; break;
      default:
        p1 = gmul(gpowgs(h,degq), p1);
        h = gdiv(gpowgs(g,degq), gpowgs(h,degq-1));
    }
    v  = gdivexact(r,p1);
    uze= gdivexact(uze,p1);
    if (dr==3) break;
    if (low_stack(lim,stack_lim(av2,1)))
    {
      GEN *gptr[6]; gptr[0]=&u; gptr[1]=&v; gptr[2]=&g; gptr[3]=&h;
      gptr[4]=&uze; gptr[5]=&um1;
      if(DEBUGMEM>1) err(warnmem,"bezoutpol, dr = %ld",dr);
      gerepilemany(av2,gptr,6);
    }
  }
  if (!poldivis(gsub(v,gmul(uze,xprim)),yprim, &vze))
    err(warner,"inexact computation in bezoutpol");
  if (cu) uze = gdiv(uze,cu);
  if (cv) vze = gdiv(vze,cv);
  p1 = ginv(content(v)); tetpil = avma;

  uze = gmul(uze,p1);
  vze = gmul(vze,p1);
  z = gmul(v,p1);
  gptr[0]=&uze; gptr[1]=&vze; gptr[2]=&z;
  gerepilemanysp(av,tetpil,gptr,3);
  *U = uze; *V = vze; return z;
}

/*******************************************************************/
/*                                                                 */
/*                RESULTANT USING DUCOS VARIANT                    */
/*                                                                 */
/*******************************************************************/

static GEN
reductum(GEN P)
{
  if (signe(P)==0) return P;
  return normalizepol_i(dummycopy(P),lgef(P)-1);
}

static GEN
Lazard(GEN x, GEN y, long n)
{
  long a, b;
  GEN c;

  if (n<=1) return x;
  a=1; while (n >= (b=a+a)) a=b;
  c=x; n-=a;
  while (a>1)
  {
    a>>=1; c=gdivexact(gsqr(c),y);
    if (n>=a) { c=gdivexact(gmul(c,x),y); n -= a; }
  }
  return c;
}

static GEN
Lazard2(GEN F, GEN x, GEN y, long n)
{
  if (n<=1) return F;
  x = Lazard(x,y,n-1); return gdivexact(gmul(x,F),y);
}

extern GEN addshiftpol(GEN x, GEN y, long d);
#define addshift(x,y) addshiftpol((x),(y),1)

static GEN
nextSousResultant(GEN P, GEN Q, GEN Z, GEN s)
{
  GEN p0, q0, z0, H, A;
  long p, q, j, v = varn(P);
  gpmem_t av, lim;

  z0 = leading_term(Z);
  p = degpol(P); p0 = leading_term(P); P = reductum(P);
  q = degpol(Q); q0 = leading_term(Q); Q = reductum(Q);

  av = avma; lim = stack_lim(av,1);
  H = gneg(reductum(Z));
  A = gmul((GEN)P[q+2],H);
  for (j = q+1; j < p; j++)
  {
    H = (degpol(H) == q-1) ?
      addshift(reductum(H), gdivexact(gmul(gneg((GEN)H[q+1]),Q), q0)) :
      addshift(H, zeropol(v));
    A = gadd(A,gmul((GEN)P[j+2],H));
    if (low_stack(lim,stack_lim(av,1)))
    {
      GEN *gptr[2]; gptr[0]=&A; gptr[1]=&H;
      if(DEBUGMEM>1) err(warnmem,"nextSousResultant j = %ld/%ld",j,p);
      gerepilemany(av,gptr,2);
    }
  }
  P = normalizepol_i(P, q+2);
  A = gdivexact(gadd(A,gmul(z0,P)), p0);
  A = (degpol(H) == q-1) ?
    gadd(gmul(q0,addshift(reductum(H),A)), gmul(gneg((GEN)H[q+1]),Q)) :
    gmul(q0, addshift(H,A));
  return gdivexact(A, ((p-q)&1)? s: gneg(s));
}

GEN
resultantducos(GEN P, GEN Q)
{
  gpmem_t av = avma, av2, lim;
  long dP,dQ,delta;
  GEN cP,cQ,Z,s;

  if ((Z = init_resultant(P,Q))) return Z;
  dP = degpol(P);
  dQ = degpol(Q);
  P = primitive_part(P, &cP);
  Q = primitive_part(Q, &cQ);
  delta = dP - dQ;
  if (delta < 0)
  {
    Z = (dP & dQ & 1)? gneg(Q): Q;
    Q = P; P = Z; delta = -delta;
  }
  s = gun;
  if (degpol(Q) > 0)
  {
    av2 = avma; lim = stack_lim(av2,1);
    s = gpuigs(leading_term(Q),delta);
    Z = Q;
    Q = pseudorem(P, gneg(Q));
    P = Z;
    while(degpol(Q) > 0)
    {
      if (low_stack(lim,stack_lim(av,1)))
      {
        GEN *gptr[2]; gptr[0]=&P; gptr[1]=&Q;
        if(DEBUGMEM>1) err(warnmem,"resultantducos, degpol Q = %ld",degpol(Q));
        gerepilemany(av2,gptr,2); s = leading_term(P);
      }
      delta = degpol(P) - degpol(Q);
      Z = Lazard2(Q, leading_term(Q), s, delta);
      Q = nextSousResultant(P, Q, Z, s);
      P = Z;
      s = leading_term(P);
    }
  }
  if (!signe(Q)) { avma = av; return gzero; }
  if (!degpol(P)){ avma = av; return gun; }
  s = Lazard(leading_term(Q), s, degpol(P));
  if (cP) s = gmul(s, gpowgs(cP,dQ));
  if (cQ) s = gmul(s, gpowgs(cQ,dP)); else if (!cP) s = gcopy(s);
  return gerepileupto(av, s);
}

/*******************************************************************/
/*                                                                 */
/*               RESULTANT USING SYLVESTER MATRIX                  */
/*                                                                 */
/*******************************************************************/
static GEN
_zeropol(void)
{
  GEN x = cgetg(3,t_POL);
  x[1] = evallgef(3);
  x[2] = zero; return x;
}

static GEN
sylvester_col(GEN x, long j, long d, long D)
{
  GEN c = cgetg(d+1,t_COL);
  long i;
  for (i=1; i< j; i++) c[i]=zero;
  for (   ; i<=D; i++) c[i]=x[D-i+2];
  for (   ; i<=d; i++) c[i]=zero;
  return c;
}

GEN
sylvestermatrix_i(GEN x, GEN y)
{
  long j,d,dx,dy;
  GEN M;

  dx = degpol(x); if (dx < 0) { dx = 0; x = _zeropol(); }
  dy = degpol(y); if (dy < 0) { dy = 0; y = _zeropol(); }
  d = dx+dy; M = cgetg(d+1,t_MAT);
  for (j=1; j<=dy; j++) M[j]    = (long)sylvester_col(x,j,d,j+dx);
  for (j=1; j<=dx; j++) M[j+dy] = (long)sylvester_col(y,j,d,j+dy);
  return M;
}

GEN
sylvestermatrix(GEN x, GEN y)
{
  long i,j,lx;
  if (typ(x)!=t_POL || typ(y)!=t_POL) err(typeer,"sylvestermatrix");
  if (varn(x) != varn(y))
    err(talker,"not the same variables in sylvestermatrix");
  x = sylvestermatrix_i(x,y); lx = lg(x);
  for (i=1; i<lx; i++)
    for (j=1; j<lx; j++) coeff(x,i,j) = lcopy(gcoeff(x,i,j));
  return x;
}

GEN
resultant2(GEN x, GEN y)
{
  gpmem_t av;
  GEN r;
  if ((r = init_resultant(x,y))) return r;
  av = avma; return gerepileupto(av,det(sylvestermatrix_i(x,y)));
}

static GEN
fix_pol(GEN x, long v, long *mx)
{
  long vx;
  GEN p1;

  if (typ(x) == t_POL)
  {
    vx = varn(x);
    if (vx)
    {
      if (v>=vx) return gsubst(x,v,polx[0]);
      p1 = cgetg(3,t_POL);
      p1[1] = evalvarn(0)|evalsigne(signe(x))|evallgef(3);
      p1[2] = (long)x; return p1;
    }
    if (v)
    {
      *mx = 1;
      return gsubst(gsubst(x,0,polx[MAXVARN]),v,polx[0]);
    }
  }
  return x;
}

/* resultant of x and y with respect to variable v, or with respect to their
 * main variable if v < 0. */
GEN
polresultant0(GEN x, GEN y, long v, long flag)
{
  long m = 0;
  gpmem_t av = avma;

  if (v >= 0)
  {
    x = fix_pol(x,v, &m);
    y = fix_pol(y,v, &m);
  }
  switch(flag)
  {
    case 0: x=subresall(x,y,NULL); break;
    case 1: x=resultant2(x,y); break;
    case 2: x=resultantducos(x,y); break;
    default: err(flagerr,"polresultant");
  }
  if (m) x = gsubst(x,MAXVARN,polx[0]);
  return gerepileupto(av,x);
}

/*******************************************************************/
/*                                                                 */
/*                  GCD USING SUBRESULTANT                         */
/*                                                                 */
/*******************************************************************/
extern GEN nfgcd(GEN P, GEN Q, GEN nf, GEN den);
extern GEN to_polmod(GEN x, GEN mod);

GEN
srgcd(GEN x, GEN y)
{
  long tx=typ(x), ty=typ(y), dx, dy, vx, vmod;
  gpmem_t av, av1, tetpil, lim;
  GEN d,g,h,p1,p2,u,v,mod,cx,cy;

  if (!signe(y)) return gcopy(x);
  if (!signe(x)) return gcopy(y);
  if (is_scalar_t(tx) || is_scalar_t(ty)) return gun;
  if (tx!=t_POL || ty!=t_POL) err(typeer,"srgcd");
  vx=varn(x); if (vx!=varn(y)) return gun;
  if (ismonome(x)) return gcdmonome(x,y);
  if (ismonome(y)) return gcdmonome(y,x);
  av = avma;
  mod = NULL; vmod = -1;
  if (can_use_modular_gcd(x, &mod, &vmod) &&
      can_use_modular_gcd(y, &mod, &vmod))
  {
    if (mod)
    { /* (Q[Y]/mod)[X]*/
      x = primitive_part(lift(x), &cx);
      y = primitive_part(lift(y), &cy);
      if (cx)
        { if (cy) cx = ggcd(cx,cy); }
      else
        cx = cy;
      d = nfgcd(x,y,mod,NULL); if (cx) d = gmul(d,cx);
      return gerepileupto(av, gmul(d, to_polmod(gun,mod)));
    }
    if (vmod < 0) return modulargcd(x,y); /* Q[X] */
  }

  if (issimplefield(x) || issimplefield(y)) x = polgcdnun(x,y);
  else
  {
    dx=lgef(x); dy=lgef(y);
    if (dx<dy) { swap(x,y); lswap(dx,dy); }
    p1=content(x); p2=content(y); d=ggcd(p1,p2);

    tetpil=avma; d=gmul(d,polun[vx]);
    if (dy==3) return gerepile(av,tetpil,d);

    av1=avma; lim=stack_lim(av1,1);
    u=gdiv(x,p1); v=gdiv(y,p2); g=h=gun;
    for(;;)
    {
      GEN r = pseudorem(u,v);
      long degq, du, dv, dr=lgef(r);

      if (dr <= 3)
      {
        if (gcmp0(r)) break;
        avma=av1; return gerepile(av,tetpil,d);
      }
      if (DEBUGLEVEL > 9) fprintferr("srgcd: dr = %ld\n", dr);
      du=lgef(u); dv=lgef(v); degq=du-dv; u=v;
      switch(degq)
      {
        case 0:
          v = gdiv(r,g);
          g = leading_term(u);
          break;
        case 1:
          v = gdiv(r,gmul(h,g));
          h = g = leading_term(u);
          break;
        default:
          v = gdiv(r,gmul(gpuigs(h,degq),g));
          g = leading_term(u);
          h = gdiv(gpuigs(g,degq), gpuigs(h,degq-1));
      }
      if (low_stack(lim, stack_lim(av1,1)))
      {
        GEN *gptr[4]; gptr[0]=&u; gptr[1]=&v; gptr[2]=&g; gptr[3]=&h;
        if(DEBUGMEM>1) err(warnmem,"srgcd");
        gerepilemany(av1,gptr,4);
      }
    }
    p1 = content(v); if (!gcmp1(p1)) v = gdiv(v,p1);
    x = gmul(d,v);
  }

  if (typ(x)!=t_POL) x = gmul(polun[vx],x);
  else
  {
    p1=leading_term(x); ty=typ(p1);
    if ((is_frac_t(ty) || is_intreal_t(ty)) && gsigne(p1)<0) x = gneg(x);
  }
  return gerepileupto(av,x);
}

extern GEN qf_disc(GEN x, GEN y, GEN z);

GEN
poldisc0(GEN x, long v)
{
  long tx=typ(x), i;
  gpmem_t av;
  GEN z,p1,p2;

  switch(tx)
  {
    case t_POL:
      if (gcmp0(x)) return gzero;
      av = avma; i = 0;
      if (v >= 0 && v != varn(x)) x = fix_pol(x,v, &i);
      p1 = subres(x, derivpol(x));
      p2 = leading_term(x); if (!gcmp1(p2)) p1 = gdiv(p1,p2);
      if (degpol(x) & 2) p1 = gneg(p1);
      if (i) p1 = gsubst(p1, MAXVARN, polx[0]);
      return gerepileupto(av,p1);

    case t_COMPLEX:
      return stoi(-4);

    case t_QUAD: case t_POLMOD:
      return poldisc0((GEN)x[1], v);

    case t_QFR: case t_QFI:
      av = avma; return gerepileuptoint(av, qf_disc(x,NULL,NULL));

    case t_VEC: case t_COL: case t_MAT:
      i=lg(x); z=cgetg(i,tx);
      for (i--; i; i--) z[i]=(long)poldisc0((GEN)x[i], v);
      return z;
  }
  err(typeer,"discsr");
  return NULL; /* not reached */
}

GEN
discsr(GEN x)
{
  return poldisc0(x, -1);
}

GEN
reduceddiscsmith(GEN pol)
{
  long i, j, n;
  gpmem_t av=avma, tetpil;
  GEN polp,alpha,p1,m;

  if (typ(pol)!=t_POL) err(typeer,"reduceddiscsmith");
  n=degpol(pol);
  if (n<=0) err(constpoler,"reduceddiscsmith");
  check_pol_int(pol,"poldiscreduced");
  if (!gcmp1((GEN)pol[n+2]))
    err(talker,"non-monic polynomial in poldiscreduced");
  polp = derivpol(pol); alpha = polx[varn(pol)];
  m=cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++)
  {
    p1=cgetg(n+1,t_COL); m[j]=(long)p1;
    for (i=1; i<=n; i++) p1[i]=(long)truecoeff(polp,i-1);
    if (j<n) polp = gres(gmul(alpha,polp), pol);
  }
  tetpil=avma; return gerepile(av,tetpil,smith(m));
}

/***********************************************************************/
/**							              **/
/**	                  STURM ALGORITHM                             **/
/**	         (number of real roots of x in ]a,b])		      **/
/**								      **/
/***********************************************************************/

/* if a (resp. b) is NULL, set it to -oo (resp. +oo) */
long
sturmpart(GEN x, GEN a, GEN b)
{
  long sl, sr, s, t, r1;
  gpmem_t av = avma, lim = stack_lim(av, 1);
  GEN g,h,u,v;

  if (typ(x) != t_POL) err(typeer,"sturm");
  if (gcmp0(x)) err(zeropoler,"sturm");
  s=lgef(x); if (s==3) return 0;

  sl = gsigne(leading_term(x));
  if (s==4)
  {
    t = a? gsigne(poleval(x,a)): -sl;
    if (t == 0) { avma = av; return 0; }
    s = b? gsigne(poleval(x,b)):  sl;
    avma = av; return (s == t)? 0: 1;
  }
  u=gdiv(x,content(x)); v=derivpol(x);
  v=gdiv(v,content(v));
  g=gun; h=gun;
  s = b? gsigne(poleval(u,b)): sl;
  t = a? gsigne(poleval(u,a)): ((lgef(u)&1)? sl: -sl);
  r1=0;
  sr = b? gsigne(poleval(v,b)): s;
  if (sr)
  {
    if (!s) s=sr;
    else if (sr!=s) { s= -s; r1--; }
  }
  sr = a? gsigne(poleval(v,a)): -t;
  if (sr)
  {
    if (!t) t=sr;
    else if (sr!=t) { t= -t; r1++; }
  }
  for(;;)
  {
    GEN p1, r = pseudorem(u,v);
    long du=lgef(u), dv=lgef(v), dr=lgef(r), degq=du-dv;

    if (dr<=2) err(talker,"not a squarefree polynomial in sturm");
    if (gsigne(leading_term(v)) > 0 || degq&1) r=gneg_i(r);
    sl = gsigne((GEN) r[dr-1]);
    sr = b? gsigne(poleval(r,b)): sl;
    if (sr)
    {
      if (!s) s=sr;
      else if (sr!=s) { s= -s; r1--; }
    }
    sr = a? gsigne(poleval(r,a)): ((dr&1)? sl: -sl);
    if (sr)
    {
      if (!t) t=sr;
      else if (sr!=t) { t= -t; r1++; }
    }
    if (dr==3) { avma=av; return r1; }

    u=v; p1 = g; g = gabs(leading_term(u),DEFAULTPREC);
    switch(degq)
    {
      case 0: break;
      case 1:
        p1 = gmul(h,p1); h = g; break;
      default:
        p1 = gmul(gpuigs(h,degq),p1);
        h = gdivexact(gpuigs(g,degq), gpuigs(h,degq-1));
    }
    v = gdivexact(r,p1);
    if (low_stack(lim,stack_lim(av,1)))
    {
      GEN *gptr[4]; gptr[0]=&u; gptr[1]=&v; gptr[2]=&g; gptr[3]=&h;
      if(DEBUGMEM>1) err(warnmem,"polsturm, dr = %ld",dr);
      gerepilemany(av,gptr,4);
    }
  }
}

/*******************************************************************/
/*                                                                 */
/*         QUADRATIC POLYNOMIAL ASSOCIATED TO A DISCRIMINANT       */
/*                                                                 */
/*******************************************************************/

GEN
quadpoly0(GEN x, long v)
{
  long res, i, l, sx, tx = typ(x);
  gpmem_t av, tetpil;
  GEN y,p1;

  if (is_matvec_t(tx))
  {
    l=lg(x); y=cgetg(l,tx);
    for (i=1; i<l; i++) y[i]=(long)quadpoly0((GEN)x[i],v);
    return y;
  }
  if (tx!=t_INT) err(arither1);
  if (v < 0) v = 0;
  sx=signe(x);
  if (!sx) err(talker,"zero discriminant in quadpoly");
  y=cgetg(5,t_POL);
  y[1]=evalsigne(1) | evalvarn(v) | evallgef(5); y[4]=un;
  res=mod4(x); if (sx<0 && res) res=4-res;
  if (res>1) err(funder2,"quadpoly");

  av=avma; p1=shifti(x,-2); setsigne(p1,-signe(p1));
  y[2] = (long) p1;
  if (!res) y[3] = zero;
  else
  {
    if (sx<0) { tetpil=avma; y[2] = lpile(av,tetpil,addsi(1,p1)); }
    y[3] = lnegi(gun);
  }
  return y;
}

GEN
quadpoly(GEN x)
{
  return quadpoly0(x,-1);
}

GEN
quadgen(GEN x)
{
  GEN y=cgetg(4,t_QUAD);
  y[1]=lquadpoly(x); y[2]=zero; y[3]=un; return y;
}

/*******************************************************************/
/*                                                                 */
/*                    GENERIC (modular) INVERSE                    */
/*                                                                 */
/*******************************************************************/

GEN
ginvmod(GEN x, GEN y)
{
  long tx=typ(x);

  switch(typ(y))
  {
    case t_POL:
      if (tx==t_POL) return polinvmod(x,y);
      if (is_scalar_t(tx)) return ginv(x);
      break;
    case t_INT:
      if (tx==t_INT) return mpinvmod(x,y);
      if (tx==t_POL) return gzero;
  }
  err(typeer,"ginvmod");
  return NULL; /* not reached */
}

/***********************************************************************/
/**							              **/
/**		            NEWTON POLYGON                            **/
/**								      **/
/***********************************************************************/

/* assume leading coeff of x is non-zero */
GEN
newtonpoly(GEN x, GEN p)
{
  GEN y;
  long n,ind,a,b,c,u1,u2,r1,r2;
  long *vval, num[] = {evaltyp(t_INT) | _evallg(3), 0, 0};

  if (typ(x)!=t_POL) err(typeer,"newtonpoly");
  n=degpol(x); if (n<=0) { y=cgetg(1,t_VEC); return y; }
  y = cgetg(n+1,t_VEC); x += 2; /* now x[i] = term of degree i */
  vval = (long *) gpmalloc(sizeof(long)*(n+1));
  for (a=0; a<=n; a++) vval[a] = ggval((GEN)x[a],p);
  for (a=0, ind=1; a<n; a++)
  {
    if (vval[a] != VERYBIGINT) break;
    y[ind++] = lstoi(VERYBIGINT);
  }
  for (b=a+1; b<=n; a=b, b=a+1)
  {
    while (vval[b] == VERYBIGINT) b++;
    u1=vval[a]-vval[b]; u2=b-a;
    for (c=b+1; c<=n; c++)
    {
      if (vval[c] == VERYBIGINT) continue;
      r1=vval[a]-vval[c]; r2=c-a;
      if (u1*r2<=u2*r1) { u1=r1; u2=r2; b=c; }
    }
    while (ind<=b) { affsi(u1,num); y[ind++] = ldivgs(num,u2); }
  }
  free(vval); return y;
}

extern int cmp_pol(GEN x, GEN y);
extern GEN ZY_ZXY_resultant(GEN A, GEN B0, long *lambda);
extern GEN indexpartial(GEN P, GEN DP);
GEN matratlift(GEN M, GEN mod, GEN amax, GEN bmax, GEN denom);
GEN nfgcd(GEN P, GEN Q, GEN nf, GEN den);

/* Factor polynomial a on the number field defined by polynomial t */
GEN
polfnf(GEN a, GEN t)
{
  gpmem_t av = avma;
  GEN x0,y,p1,p2,u,G,fa,n,unt,dent,alift;
  long lx,i,k,e;
  int sqfree, tmonic;

  if (typ(a)!=t_POL || typ(t)!=t_POL) err(typeer,"polfnf");
  if (gcmp0(a)) return gcopy(a);
  a = fix_relative_pol(t,a,0);
  alift = lift(a);
  p1 = content(alift); if (!gcmp1(p1)) { a = gdiv(a, p1); alift = lift(a); }
  t = primpart(t);
  tmonic = is_pm1(leading_term(t));

  dent = indexpartial(t, NULL); unt = gmodulsg(1,t);
  G = nfgcd(alift,derivpol(alift), t, dent);
  sqfree = gcmp1(G);
  u = sqfree? alift: lift_intern(gdiv(a, gmul(unt,G)));
  k = 0; n = ZY_ZXY_resultant(t, u, &k);
  if (DEBUGLEVEL>4) fprintferr("polfnf: choosing k = %ld\n",k);
  if (!sqfree)
  {
    G = poleval(G, gadd(polx[varn(a)], gmulsg(k, polx[varn(t)])));
    G = ZY_ZXY_resultant(t, G, NULL);
  }

  /* n guaranteed to be squarefree */
  fa = DDF2(n,0); lx = lg(fa);
  y = cgetg(3,t_MAT);
  p1 = cgetg(lx,t_COL); y[1] = (long)p1;
  p2 = cgetg(lx,t_COL); y[2] = (long)p2;
  x0 = gadd(polx[varn(a)], gmulsg(-k, gmodulcp(polx[varn(t)], t)));
  for (i=lx-1; i>0; i--)
  {
    GEN f = (GEN)fa[i], F = lift_intern(poleval(f, x0));
    if (!tmonic) F = primpart(F);
    F = nfgcd(u, F, t, dent);
    if (typ(F) != t_POL || degpol(F) == 0)
      err(talker,"reducible modulus in factornf");
    e = 1;
    if (!sqfree)
    {
      while (poldivis(G,f, &G)) e++;
      if (degpol(G) == 0) sqfree = 1;
    }
    p1[i] = ldiv(gmul(unt,F), leading_term(F));
    p2[i] = lstoi(e);
  }
  return gerepilecopy(av, sort_factor(y, cmp_pol));
}

extern GEN FpXQX_safegcd(GEN P, GEN Q, GEN T, GEN p);
extern GEN FpM(GEN z, GEN p);
extern GEN polpol_to_mat(GEN v, long n);
extern GEN mat_to_polpol(GEN x, long v, long w);

static GEN
to_frac(GEN a, GEN b)
{
  GEN f = cgetg(3, t_FRAC);
  f[1] = (long)a;
  f[2] = (long)b; return f;
}

static GEN
lift_to_frac(GEN t, GEN mod, GEN amax, GEN bmax, GEN denom)
{
  GEN a, b;
  if (signe(t) < 0) t = addii(t, mod); /* in case t is a centerlift */
  if (!ratlift(t, mod, &a, &b, amax, bmax)
     || (denom && !divise(denom,b))
     || !gcmp1(mppgcd(a,b))) return NULL;
  if (!is_pm1(b)) a = to_frac(a, b);
  return a;
}

/* compute rational lifting for all the components of M modulo mod.
 * If one components fails, return NULL.
 * See ratlift.
 * If denom is not NULL, check that the denominators divide denom
 *
 * FIXME: NOT stack clean ! a & b stay on the stack.
 * If we suppose mod and denom coprime, then a and b are coprime
 * so we can do a cgetg(t_FRAC).
 */
GEN
matratlift(GEN M, GEN mod, GEN amax, GEN bmax, GEN denom)
{
  gpmem_t ltop = avma;
  GEN N, a;
  long l2, l3;
  long i, j;
  if (typ(M)!=t_MAT) err(typeer,"matratlift");
  l2 = lg(M); l3 = lg((GEN)M[1]);
  N = cgetg(l2, t_MAT);
  for (j = 1; j < l2; ++j)
  {
    N[j] = lgetg(l3, t_COL);
    for (i = 1; i < l3; ++i)
    {
      a = lift_to_frac(gcoeff(M,i,j), mod, amax,bmax,denom);
      if (!a) { avma = ltop; return NULL; }
      coeff(N, i, j) = (long)a;
    }
  }
  return N;
}

GEN
polratlift(GEN P, GEN mod, GEN amax, GEN bmax, GEN denom)
{
  gpmem_t ltop = avma;
  GEN Q,a;
  long l2, j;
  if (typ(P)!=t_POL) err(typeer,"polratlift");
  l2 = lg(P);
  Q = cgetg(l2, t_POL); Q[1] = P[1];
  for (j = 2; j < l2; ++j)
  {
    a = lift_to_frac((GEN)P[j], mod, amax,bmax,denom);
    if (!a) { avma = ltop; return NULL; }
    Q[j] = (long)a;
  }
  return Q;
}

/* P,Q in Z[X,Y], nf in Z[Y] irreducible. compute GCD in Q[Y]/(nf)[X].
 *
 * We essentially follow M. Encarnacion "On a modular Algorithm for computing
 * GCDs of polynomials over number fields" (ISSAC'94).
 *
 * We procede as follows
 *  1:compute the gcd modulo primes discarding bad primes as they are detected.
 *  2:reconstruct the result via matratlift, stoping as soon as we get weird
 *    denominators.
 *  3:if matratlift succeeds, try the full division.
 * Suppose we does not have sufficient accuracy to get the result right:
 * it is extremly rare that matratlift will succeed, and even if it does, the
 * polynomial we get has sensible coefficients, so the full division will
 * not be too costly.
 *
 * FIXME: Handle rational coefficient for P and Q.
 * If not NULL, den must a a multiple of the denominator of the gcd,
 * for example the discriminant of nf.
 *
 * NOTE: if nf is not irreducible, nfgcd may loop forever, esp. if gcd | nf */
GEN
nfgcd(GEN P, GEN Q, GEN nf, GEN den)
{
  gpmem_t ltop = avma;
  GEN sol, mod = NULL;
  long x = varn(P);
  long y = varn(nf);
  long d = degpol(nf);
  GEN lP, lQ;
  if (!signe(P) || !signe(Q))
    return zeropol(x);
  /*Compute denominators*/
  if (!den) den = indexpartial(nf, NULL);
  lP = leading_term(P);
  lQ = leading_term(Q);
  if ( !((typ(lP)==t_INT && is_pm1(lP)) || (typ(lQ)==t_INT && is_pm1(lQ))) )
    den = mulii(den, mppgcd(ZX_resultant(lP, nf), ZX_resultant(lQ, nf)));
  /*Modular GCD*/
  {
    gpmem_t btop = avma, st_lim = stack_lim(btop, 1);
    long p;
    long dM=0, dR;
    GEN M, dsol;
    GEN R, ax, bo;
    byteptr primepointer;
    for (p = 27449, primepointer = diffptr + 3000; ; p += *(primepointer++))
    {
      if (!*primepointer) err(primer1);
      if (!smodis(den, p))
        continue;/*Discard primes dividing disc(T) or leadingcoeff(PQ) */
      if (DEBUGLEVEL>5) fprintferr("nfgcd: p=%d\n",p);
      if ((R = FpXQX_safegcd(P, Q, nf, stoi(p))) == NULL)
        continue;/*Discard primes when modular gcd does not exist*/
      dR = degpol(R);
      if (dR == 0) return scalarpol(gun, x);
      if (mod && dR > dM) continue; /* p divides Res(P/gcd, Q/gcd). Discard. */

      R = polpol_to_mat(R, d);
      /* previous primes divided Res(P/gcd, Q/gcd)? Discard them. */
      if (!mod || dR < dM) { M = R; mod = stoi(p); dM = dR; continue; }
      if (low_stack(st_lim, stack_lim(btop, 1)))
      {
	GEN *bptr[2]; bptr[0]=&M; bptr[1]=&mod;
	if (DEBUGMEM>1) err(warnmem,"nfgcd");
	gerepilemany(btop, bptr, 2);
      }

      ax = gmulgs(mpinvmod(stoi(p), mod), p);
      M = gadd(R, gmul(ax, gsub(M, R)));
      mod = mulis(mod, p);
      M = lift(FpM(M, mod));
      /* I suspect it must be better to take amax > bmax*/
      bo = racine(shifti(mod, -1));
      if ((sol = matratlift(M, mod, bo, bo, den)) == NULL)
        continue;
      sol = mat_to_polpol(sol,x,y);
      dsol = primpart(sol);
      if (gcmp0(pseudorem_i(P, dsol, nf))
       && gcmp0(pseudorem_i(Q, dsol, nf))) break;
    }
  }
  return gerepilecopy(ltop, sol);
}
