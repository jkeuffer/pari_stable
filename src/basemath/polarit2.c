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

#define swap(a,b) { long _x = a; a = b; b = _x; }
#define deg(a) (lgef(a)-3)

GEN gassoc_proto(GEN f(GEN,GEN),GEN,GEN);

GEN
polsym(GEN x, long n)
{
  long av1,av2,dx=deg(x),i,k;
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
  long n,i, av = avma;
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
  long av,i,lx;
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
      return y;

    case t_COL: lx=lg(x);
      y=cgetg(lx,t_COL);
      for (i=1; i<lx; i++)
      {
	p1=modii((GEN)x[i],p);
	if (cmpii(p1,ps2)>0) p1=subii(p1,p);
	y[i]=(long)p1;
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
  long dx,dy,dz,i,j,av, vx = varn(x);
  GEN z,p1,y_lead;

  dy=deg(y);
  dx=deg(x);
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
 *  a = set of k modular factors
 *  V = set of products of factors built as follows
 *  1) V[1..k] = initial a
 *  2) iterate:
 *      append to V the two smallest factors (minimal degree) in a, remove them
 *      from a and replace them by their product [net loss for a: 1 factor]
 *
 * W = bezout coeffs W[i]V[i] + W[i+1]V[i+1] = 1
 *
 * link[i] = -j if V[i] = a[j]
 *            j if V[i] = V[j] * V[j+1]
 * Arrays (link, V, W) pre-allocated for 2k - 2 elements */
static void
BuildTree(GEN link, GEN V, GEN W, GEN a, GEN p)
{
  long k = lg(a)-1;
  long i, j, s, minp, mind;

  for (i=1; i<=k; i++) { V[i] = a[i]; link[i] = -i; }

  for (j=1; j <= 2*k-5; j+=2,i++)
  {
    minp = j;
    mind = deg(V[j]);
    for (s=j+1; s<i; s++)
      if (deg(V[s]) < mind) { minp = s; mind = deg(V[s]); }

    swap(V[j], V[minp]);
    swap(link[j], link[minp]);

    minp = j+1;
    mind = deg(V[j+1]);
    for (s=j+2; s<i; s++)
      if (deg(V[s]) < mind) { minp = s; mind = deg(V[s]); }

    swap(V[j+1], V[minp]);
    swap(link[j+1], link[minp]);

    V[i] = (long)FpX_mul((GEN)V[j], (GEN)V[j+1], p);
    link[i] = j;
  }

  for (j=1; j <= 2*k-3; j+=2)
  {
    GEN d, u, v;
    d = FpX_extgcd((GEN)V[j], (GEN)V[j+1], p, &u, &v);
    if (deg(d) > 0) err(talker, "relatively prime polynomials expected");
    d = (GEN)d[2];
    if (!gcmp1(d))
    {
      d = mpinvmod(d, p);
      u = FpX_Fp_mul(u, d, p);
      v = FpX_Fp_mul(v, d, p);
    }
    W[j]   = (long)u;
    W[j+1] = (long)v;
  }
}

#define ZX_add(a,b) FpX_add(a,b,NULL)
#define ZX_sub(a,b) FpX_sub(a,b,NULL)
#define ZX_mul(a,b) FpX_mul(a,b,NULL)
#define ZX_Z_mul(a,b) FpX_Fp_mul(a,b,NULL)
#define ZX_Z_add(a,b) FpX_Fp_add(a,b,NULL)

/* au + bv = 1 (p0), ab = f (p0). Lift mod p1 = p0 pd (<= p0^2).
 * If noinv is set, don't lift the inverses u and v */
static void
HenselLift(GEN V, GEN W, long j, GEN f, GEN pd, GEN p0, int noinv)
{
  const long space = lgef(f) * (lgefint(pd) + lgefint(p0) - 2);
  long av = avma;
  GEN a2,b2,g,z,s,t;
  GEN a = (GEN)V[j], b = (GEN)V[j+1];
  GEN u = (GEN)W[j], v = (GEN)W[j+1];

  (void)new_chunk(space);
  g = gadd(f, gneg_i(gmul(a,b)));

  g = gdivexact(g, p0); g = FpX_red(g, pd);
  z = FpX_mul(v,g, pd);
  t = FpX_divres(z,a,pd, &s);
  t = FpX_add(ZX_mul(u,g), ZX_mul(t,b), pd);
  t = ZX_Z_mul(t,p0);
  s = ZX_Z_mul(s,p0);
  avma = av;

  /* already reduced mod p1 = pd p0 */
  a2 = ZX_add(a,s); V[j]   = (long)a2;
  b2 = ZX_add(b,t); V[j+1] = (long)b2;
  if (noinv) return;

  av = avma;
  (void)new_chunk(space);
  g = ZX_add(ZX_mul(u,a2), ZX_mul(v,b2));
  g = ZX_Z_add(gneg_i(g), gun);

  g = gdivexact(g, p0); g = FpX_red(g, pd);
  z = FpX_mul(v,g, pd);
  t = FpX_divres(z,a,pd, &s);
  t = FpX_add(ZX_mul(u,g), ZX_mul(t,b), pd);
  t = ZX_Z_mul(t,p0);
  s = ZX_Z_mul(s,p0);
  avma = av;

  u = ZX_add(u,t); W[j]   = (long)u;
  v = ZX_add(v,s); W[j+1] = (long)v;
}

/* v list of factors, w list of inverses.  f = v[j] v[j+1]
 * Lift v[j] and v[j+1] mod p0 pd, then all their divisors */
static void
RecTreeLift(GEN link, GEN v, GEN w, GEN pd, GEN p0, GEN f, long j, int noinv)
{
  if (j < 0) return;

  HenselLift(v, w, j, f, pd, p0, noinv);

  RecTreeLift(link, v, w, pd, p0, (GEN)v[j]  , link[j  ], noinv);
  RecTreeLift(link, v, w, pd, p0, (GEN)v[j+1], link[j+1], noinv);
}

/* lift from p^{e0} to p^{e1} */
static void
TreeLift(GEN link, GEN v, GEN w, GEN p, long e0, long e1, GEN f, int noinv)
{
  GEN p0 = gpowgs(p, e0);
  GEN pd = gpowgs(p, e1-e0);
  RecTreeLift(link, v, w, pd, p0, f, lg(v)-2, noinv);
}

/* a = modular factors of f mod p, lift to precision e0
 * flag = 0: standard.
 * flag = 1: return TreeLift structure
 * flag = 2: a = TreeLift structure, go on lifting, as flag = 1 otherwise */
static GEN
MultiLift(GEN f, GEN a, GEN p, long e0, int flag)
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
    BuildTree(link, v, w, a, p);
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
    TreeLift(link, v, w, p, E[i], E[i-1], f, (flag == 0) && (i == 2));
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

/* Q list of (coprime, monic) factors of pol mod p. Lift mod p^e = pe */
GEN
hensel_lift_fact(GEN pol, GEN Q, GEN p, GEN pe, long e)
{
  if (lg(Q) == 2) { GEN d = cgetg(2, t_VEC); d[1] = (long)pol; return d; }
  pol = FpX_normalize(pol, pe);
  return MultiLift(pol, Q, p, e, 0);
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
  E = MultiLift(pol, Q, p, e, 1);
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
  long av = avma, i, j, l;

  /* we check the arguments */
  if (typ(pol) != t_POL)
    err(talker, "not a polynomial in polhensellift");
  if ((typ(fct) != t_COL && typ(fct) != t_VEC) || (lg(fct) < 3))
    err(talker, "not a factorization in polhensellift");
  if (typ(p) != t_INT || !isprime(p))
    err(talker, "not a prime number in polhensellift");
  if (exp < 1)
    err(talker, "not a positive exponent in polhensellift");

  p1 = lift(fct); /* make sure the coeffs are integers and not intmods */
  l = lg(p1) - 1;

  /* then we check that pol \equiv \prod f ; f \in fct mod p */
  p2 = (GEN)p1[1];
  for (j = 2; j <= l; j++) p2 = FpX_mul(p2, (GEN)p1[j], p);
  if (!gcmp0(FpX_sub(pol, p2, p)))
    err(talker, "not a correct factorization in polhensellift");

  /* finally we check that the elements of fct are coprime mod p */
  if (gcmp0(discsr(FpX(pol, p))))
  {
    for (i = 1; i <= l; i++)
      for (j = 1; j < i; j++)
        if (lgef(FpX_gcd((GEN)p1[i], (GEN)p1[j], p)) != 3)
          err(talker, "polhensellift: factors %Z and %Z are not coprime",
                     p1[i], p1[j]);
  }
  return gerepileupto(av, gcopy(hensel_lift_fact(pol, p1, p,
						 gpowgs(p, exp), exp)));
}

#if 0
/* cf Beauzamy et al: upper bound for
 *      lc(x) * [2^(5/8) / pi^(3/8)] e^(1/4n) 2^(n/2) sqrt([x]_2)/ n^(3/8)
 * where [x]_2 = sqrt(\sum_i=0^n x[i]^2 / binomial(n,i)). One factor has
 * all coeffs less than then bound */
static GEN
two_factor_bound(GEN x)
{
  long av = avma, i,j, n = lgef(x) - 3;
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
  long e, n = deg(x);
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
TruncTrace(GEN x, GEN pb, GEN pa_b, GEN pa_bs2, GEN pbs2)
{
  GEN r, q = dvmdii(x, pb, &r);
  if (cmpii(r,  pbs2) > 0) q = addis(q,1);
  if (pa_bs2 && cmpii(q,pa_bs2) > 0) q = subii(q,pa_b);
  return q;
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
  GEN deg      = cgetg(lfamod+1, t_VECSMALL);
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
      deg[i] = deg(p1);
      if (!gcmp1(lc))
        T = modii(mulii(lc, (GEN)p1[deg[i]+1]), pa);
      else
        T = (GEN)p1[deg[i]+1]; /* d-1 term */
      trace[i] = itos( TruncTrace(T, pb,pa_b,NULL,pbs2) );
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
  i = 1; curdeg = deg[ind[1]];
  for(;;)
  { /* try all combinations of K factors */
    for (j = i; j < K; j++)
    {
      degsofar[j] = curdeg;
      ind[j+1] = ind[j]+1; curdeg += deg[ind[j+1]];
    }
    if (curdeg <= klim && curdeg % hint == 0) /* trial divide */
    {
      GEN y, q, cont, list;
      ulong av;
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
          deg[k] = deg[i]; k++;
        }
      }
      lfamod -= K;
      if (lfamod < 2*K) goto END;
      i = 1; curdeg = deg[ind[1]];
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
        curdeg = degsofar[i-1] + deg[ind[i]];
        if (curdeg <= klim) break;
      }
    }
  }
END:
  if (deg(target) > 0)
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

static long
get_e(GEN B, GEN p, GEN *ptpe)
{
  GEN pe;
  long e;
  for (e=1,pe=p; cmpii(pe, B) < 0; e++) pe = mulii(pe,p);
  *ptpe =  pe; return e;
}

/* recombination of modular factors: van Hoeij's algorithm */

/* compute Newton sums of P (i-th powers of roots, i=1..n)
 * If N != NULL, assume p-adic roots and compute mod N [assume integer coeffs]
 * If y0!= NULL, precomputed i-th powers, i=1..m, m = length(y0) */
GEN
polsym_gen(GEN P, GEN y0, long n, GEN N)
{
  long av1,av2,dP=deg(P),i,k,m;
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
  if (N && P_lead)
    if (!invmod(P_lead,N,&P_lead))
      err(talker,"polsyn: non-invertible leading coeff: %Z", P_lead);
  for (k=m; k<=n; k++)
  {
    av1=avma; s = (dP>=k)? gmulsg(k,(GEN)P[dP-k]): gzero;
    for (i=1; i<k && i<=dP; i++)
      s = gadd(s, gmul((GEN)y[k-i+1],(GEN)P[dP-i]));
    if (N)
    {
      s = modii(s, N);
      if (P_lead) { s = mulii(s,P_lead); s = modii(s,N); }
    }
    else
      if (P_lead) s = gdiv(s,P_lead);
    av2=avma; y[k+1]=lpile(av1,av2,gneg(s));
  }
  return y;
}

/* return integer y such that all roots of P are less than y */
static GEN
root_bound(GEN P)
{
  GEN P0 = dummycopy(P), lP = absi(leading_term(P)), x,y,z;
  long k,d = deg(P);

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
    B[i] = (long)sqscal((GEN)f[i]);
    iB[i]= linv((GEN)B[i]);
    for (j=1; j<i; j++)
    {
      GEN mu = gmul(gscal((GEN)e[i],(GEN)f[j]), (GEN)iB[j]);
      GEN p2 = gmul(mu, (GEN)f[j]);
      p1 = p1? gadd(p1,p2): p2;
    }
    p1 = p1? gsub((GEN)e[i], p1): (GEN)e[i];
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
static GEN
my_norml2(GEN x)
{
  long i,j, co = lg(x), li;
  GEN S = gzero;
  if (co == 1) return S;
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
static long
init_padic_prec(long e, int BitPerFactor, long n0, double LOGp2)
{
/* long b, goodb = (long) ((e - 0.175 * n0 * n0)  * LOGp2); */
  long b, goodb = (long) (((e - BitPerFactor*n0)) * LOGp2);
  b = (long) ((e -     32)*LOGp2); if (b < goodb) goodb = b;
  /* b = (long) ((e - Max*32)*LOGp2); if (b > goodb) goodb = b; */
  return goodb;
}

extern GEN sindexrank(GEN x);
extern GEN vconcat(GEN Q1, GEN Q2);

/* Recombination phase of Berlekamp-Zassenhaus algorithm using a variant of
 * van Hoeij's knapsack
 *
 * P = monic squarefree in Z[X].
 * famod = array of (lifted) modular factors mod p^a
 * bound = Mignotte bound for the size of divisors of P (sor the sup norm)
 * previously recombined all set of factors with less than rec elts
 */
GEN
LLL_cmbf(GEN P, GEN famod, GEN p, GEN pa, GEN bound, long a, long rec)
{
  long s = 2; /* # of traces added at each step */
  long BitPerFactor = 3; /* nb bits in p^(a-b) / modular factor */
  long i,j,C,r,S,tmax,n0,n,dP = deg(P);
  double logp = log(gtodouble(p)), LOGp2 = LOG2/logp;
  double b0 = log((double)dP*2) / logp;
  double k = gtodouble(glog(root_bound(P), DEFAULTPREC)) / logp;
  GEN y, T, T2, TT, BL, m, u, norm, target, M, piv, list;
  GEN run = realun(DEFAULTPREC);
  ulong av,av2, lim;
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

    if (DEBUGLEVEL>3)
      fprintferr("LLL_cmbf: %ld potential factors (tmax = %ld)\n", r, tmax);
    av2 = avma;
    if (tmax > 0)
    { /* bound small vector in terms of a modified L2 norm of a
       * left inverse of BL */
      Nx = gtodouble(my_norml2(gmul(run, invmat(BL))));
      avma = av2;
    }
    else
      Nx = (double)n0; /* first time: BL = id */
    C = (long)sqrt(s*n0*n0/4. / Nx);
    if (C == 0) C = 1; /* frequent after a few iterations */
    M = dbltor((Nx * C*C + s*n0*n0/4.) * 1.00001);

    S = tmax + s;
    b = (long)ceil(b0 + S*k);
    if (a <= b)
    {
      a = (long)ceil(b + 3*s*k) + 1; /* enough for 3 more rounds */
      pa = gpowgs(p,a);
      famod = hensel_lift_fact(P,famod,p,pa,a);
      /* recompute old Newton sums to new precision */
      for (i=1; i<=n0; i++)
        TT[i] = (long)polsym_gen((GEN)famod[i], NULL, tmax, pa);
      did_recompute_famod = 1;
    }
    for (i=1; i<=n0; i++)
    {
      GEN p1 = (GEN)T[i];
      GEN p2 = polsym_gen((GEN)famod[i], (GEN)TT[i], S, pa);
      TT[i] = (long)p2;
      p2 += 1+tmax; /* ignore traces number 0...tmax */
      for (j=1; j<=s; j++) p1[j] = p2[j];
    }

    av2 = avma;
    T2 = gmod( gmul(T, BL), pa );
    goodb = init_padic_prec(gexpo(T2), BitPerFactor, n0, LOGp2);
    if (goodb > b) b = goodb;
    if (DEBUGLEVEL>2)
      fprintferr("LLL_cmbf: (a, b) = (%ld, %ld), expo(T) = %ld\n",
                 a,b,gexpo(T2));
    pa_b = gpowgs(p, a-b);
    {
      GEN pb = gpowgs(p, b);
      GEN pa_bs2 = shifti(pa_b,-1);
      GEN pbs2   = shifti(pb,-1);
      for (i=1; i<=r; i++)
      {
        GEN p1 = (GEN)T2[i];
        for (j=1; j<=s; j++)
          p1[j] = (long)TruncTrace((GEN)p1[j],pb,pa_b,pa_bs2,pbs2);
      }
    }
    if (gcmp0(T2)) { avma = av2; continue; }

    BE = cgetg(s+1, t_MAT);
    for (i=1; i<=s; i++)
    {
      BE[i] = (long)zerocol(r+s);
      coeff(BE, i+r, i) = (long)pa_b;
    }
    m = concatsp( vconcat( gscalmat(stoi(C), r), T2 ), BE );
    /*     [  C        0      ]
     * m = [                  ]   square matrix
     *     [ T2   p^(a-b) I_S ]   T2 = T * BL  truncated
     */
    u = lllgramintern(gram_matrix(m), 4, 0, 0);
    m = gmul(m,u);
    (void)gram_schmidt(gmul(run,m), &norm);
    for (i=r+s; i>0; i--)
      if (cmprr((GEN)norm[i], M) < 0) break;
    if (i > r)
    { /* no progress */
      avma = av2; BitPerFactor += 2;
      if (DEBUGLEVEL>2)
        fprintferr("LLL_cmbf: increasing BitPerFactor = %ld\n", BitPerFactor);
#if 0
      s++; for (i=1; i<=n; i++) T[i] = lgetg(s+1, t_COL);
      if (DEBUGLEVEL>2) fprintferr("LLL_cmbf: increasing s = %ld\n", s);
#endif
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
    if (DEBUGLEVEL) fprintferr("special_pivot output:\n%Z\n",piv);
    if (!piv) { avma = av2; continue; }

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

/* P(hx), in place. Assume P in Z[X], h in Z */
void
rescale_pol_i(GEN P, GEN h)
{
  GEN hi = gun;
  long i, l = lgef(P);
  for (i=3; i<l; i++)
  {
    hi = mulii(hi,h);
    P[i] = lmulii((GEN)P[i], hi);
  }
}

/* P(hx) in Fp[X], in place. Assume P in Z[X], h in Z */
void
FpX_rescale_i(GEN P, GEN h, GEN p)
{
  GEN hi = gun;
  long i, l = lgef(P);
  for (i=3; i<l; i++)
  {
    hi = modii(mulii(hi,h), p);
    P[i] = lmodii(mulii((GEN)P[i], hi), p);
  }
}

/* use van Hoeij's knapsack algorithm */
static GEN
combine_factors(GEN a, GEN famod, GEN p, long klim, long hint)
{
  GEN B = uniform_Mignotte_bound(a), res,y,lt,L,pe,pE,listmod,p1;
  long i,E,e,l, maxK = 3, nft = lg(famod)-1;

  e = get_e(B, p, &pe);
  if (DEBUGLEVEL > 4) fprintferr("Mignotte bound: %Z^%ld\n", p,e);

  { /* overlift for the d-1 test */
    int over = (int) (32 * LOG2 / log((double)itos(p)));
    pE = mulii(pe, gpowgs(p,over)); E = e + over;
  }
  famod = hensel_lift_fact(a,famod,p,pE,E);

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
    if (gcmp1(lt))
      lt = NULL;
    else
    {
      GEN invlt, invLT;
      if (DEBUGLEVEL > 4) fprintferr("making it monic\n");
      a = primitive_pol_to_monic(a, &lt);
      B = uniform_Mignotte_bound(a);
      e = get_e(B, p, &pe);

      invlt = mpinvmod(lt,p);
      for (i = 1; i<lg(famod); i++)
      { /* renormalize modular factors */
        p1 = (GEN)famod[i]; FpX_rescale_i(p1, invlt, p);
        invLT = powmodulo(lt, stoi(deg(p1)), p);
        famod[i] = (long)FpX_Fp_mul(p1, invLT, p);
      }
      famod = hensel_lift_fact(a,famod,p,pe,e);
    }
    setlg(res, l-1); /* remove last elt (possibly unfactored) */
    L = LLL_cmbf(a, famod, p, pe, B, e, maxK);
    if (lt)
    {
      for (i=1; i<lg(L); i++)
      {
        y = (GEN)L[i]; rescale_pol_i(y, lt);
        p1 = content(y); if (!is_pm1(p1)) y = gdiv(y, p1);
        L[i] = (long)y;
      }
    }
    res = concatsp(res, L);
  }
  return res;
}

extern long split_berlekamp(GEN Q, GEN *t, GEN pp, GEN pps2);

/* assume degree(a) > 0, a(0) != 0, and a squarefree */
static GEN
squff(GEN a, long hint)
{
  GEN res,Q,prime,primes2,famod,p1,y,g,z,w,*tabd,*tabdnew;
  long av=avma,va=varn(a),da=deg(a);
  long klim,chosenp,p,nfacp,lbit,i,j,d,e,np,nmax,lgg,nf,nft;
  ulong *tabbit, *tabkbit, *tmp;
  byteptr pt=diffptr;
  const int NOMBDEP = 5;

  if (hint <= 0) hint = 1;
  if (DEBUGLEVEL > 2) timer2();
  lbit=(da>>4)+1; nmax=da+1; klim=da>>1;
  chosenp = 0;
  tabd = NULL;
  tabdnew = (GEN*)new_chunk(nmax);
  tabbit  = (ulong*)new_chunk(lbit);
  tabkbit = (ulong*)new_chunk(lbit);
  tmp     = (ulong*)new_chunk(lbit);
  prime = icopy(gun);
  for (p = np = 0; np < NOMBDEP; )
  {
    GEN minuspolx;
    p += *pt++; if (!*pt) err(primer1);
    if (!smodis((GEN)a[da+2],p)) continue;
    prime[2] = p; z = FpX_red(a, prime);
    if (!FpX_is_squarefree(z, prime)) continue;

    for (j=0; j<lbit-1; j++) tabkbit[j] = 0;
    tabkbit[j] = 1;
    d=0; e=da; nfacp=0;
    w = polx[va]; minuspolx = gneg(w);
    while (d < (e>>1))
    {
      d++; w = FpXQ_pow(w, prime, z, prime);
      g = FpX_gcd(z, gadd(w, minuspolx), prime);
      tabdnew[d]=g; lgg=deg(g);
      if (lgg > 0)
      {
	z = FpX_div(z, g, prime); e = deg(z);
        w = FpX_res(w, z, prime);
        lgg /= d; nfacp += lgg;
        if (DEBUGLEVEL>5)
          fprintferr("   %3ld %s of degree %3ld\n",
                     lgg, lgg==1?"factor": "factors",d);
	record_factors(lgg, d, lbit-1, tabkbit, tmp);
      }
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
      fprintferr("...tried prime %3ld (%-3ld %s). Time = %ld\n",
                  p,nfacp,nfacp==1?"factor": "factors",timer2());
    if (min_deg(lbit-1,tabbit) > klim)
    {
      avma = av; y = cgetg(2,t_COL);
      y[1] = lcopy(a); return y;
    }
    if (nfacp < nmax)
    {
      nmax=nfacp; tabd=tabdnew; chosenp=p;
      for (j=d+1; j<e; j++) tabd[j]=polun[va];
      tabdnew = (GEN*)new_chunk(da);
    }
    np++;
  }
  prime[2]=chosenp; primes2 = shifti(prime, -1);
  nf=nmax; nft=1;
  y=cgetg(nf+1,t_COL); famod=cgetg(nf+1,t_COL);
  Q = cgetg(da+1,t_MAT);
  for (i=1; i<=da; i++) Q[i] = lgetg(da+1, t_COL);
  p1 = (GEN)Q[1]; for (i=1; i<=da; i++) p1[i] = zero;
  for (d=1; nft<=nf; d++)
  {
    g=tabd[d]; lgg=deg(g);
    if (lgg)
    {
      long n = lgg/d;
      famod[nft] = (long)FpX_normalize(g, prime);
      if (n > 1) (void)split_berlekamp(Q, (GEN*)(famod+nft),prime,primes2);
      nft += n;
    }
  }
  if (DEBUGLEVEL > 4) msgtimer("splitting mod p = %ld",chosenp);
  res = combine_factors(a, famod, prime, da-1, hint);
  return gerepileupto(av, gcopy(res));
}

GEN
poldeflate(GEN x0, long *m)
{
  long d = 0, i, id, lx = lgef(x0)-2;
  GEN x = x0 + 2;

  for (i=1; i<lx; i++)
    if (!gcmp0((GEN)x[i])) { d = cgcd(d,i); if (d == 1) break; }
  *m = d;
  if (d > 1)
  {
    GEN z, y;
    long ly = (lx-1)/d + 3;
    y = cgetg(ly, t_POL);
    y[1] = evalsigne(1)|evallgef(ly)|evalvarn(varn(x0));
    z = y + 2; ly -= 2;
    for (i=id=0; i<ly; i++,id+=d) z[i] = x[id];
    x0 = y;
  }
  return x0;
}

GEN
polinflate(GEN x0, long d)
{
  long i, id, ly, lx = lgef(x0)-2;
  GEN x = x0 + 2, z, y;
  ly = (lx-1)*d + 3;
  y = cgetg(ly, t_POL);
  y[1] = evalsigne(1)|evallgef(ly)|evalvarn(varn(x0));
  z = y + 2; ly -= 2;
  for (i=0; i<ly; i++) z[i] = zero;
  for (i=id=0; i<lx; i++,id+=d) z[id] = x[i];
  return y;
}

GEN
squff2(GEN x, long hint)
{
  GEN L;
  long m;
  x = poldeflate(x, &m);
  L = squff(x, hint);
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
        L2 = concatsp(L2, squff(polinflate((GEN)L[i], v[k]), hint));
      L = L2;
    }
  }
  return L;
}

/* Factor x in Z[t]. Assume all factors have degree divisible by hint */
GEN
factpol(GEN x, long hint)
{
  GEN fa,p1,d,t,v,w, y = cgetg(3,t_MAT);
  long av=avma,av2,lx,vx,i,j,k,ex,nbfac,zval;

  if (typ(x)!=t_POL) err(notpoler,"factpol");
  if (!signe(x)) err(zeropoler,"factpol");

  ex = nbfac = 0;
  p1 = x+2; while (gcmp0((GEN)*p1)) p1++;
  zval = p1 - (x + 2);
  lx = lgef(x) - zval;
  vx = varn(x);
  if (zval)
  {
    x = cgetg(lx, t_POL); p1 -= 2;
    for (i=2; i<lx; i++) x[i] = p1[i];
    x[1] = evalsigne(1)|evalvarn(vx)|evallgef(lx);
    nbfac++;
  }
  /* now x(0) != 0 */
  if (lx==3) { fa = NULL;/* for lint */ goto END; }
  p1 = cgetg(1,t_VEC); fa=cgetg(lx,t_VEC);
  for (i=1; i<lx; i++) fa[i] = (long)p1;
  d=content(x); if (gsigne(leading_term(x)) < 0) d = gneg_i(d);
  if (!gcmp1(d)) x=gdiv(x,d);
  if (lx==4) { nbfac++; ex++; fa[1] = (long)concatsp(p1,x); goto END; }

  w=derivpol(x); t=modulargcd(x,w);
  if (!gcmp1(t)) { x=gdeuc(x,t); w=gdeuc(w,t); }
  k=1;
  while (k)
  {
    ex++; w=gadd(w, gneg_i(derivpol(x))); k=signe(w);
    if (k) { t=modulargcd(x,w); x=gdeuc(x,t); w=gdeuc(w,t); } else t=x;
    if (deg(t) > 0)
    {
      fa[ex] = (long)squff2(t,hint);
      nbfac += lg(fa[ex])-1;
    }
  }
END: av2=avma;
  v=cgetg(nbfac+1,t_COL); y[1]=(long)v;
  w=cgetg(nbfac+1,t_COL); y[2]=(long)w;
  if (zval) { v[1]=lpolx[vx]; w[1]=lstoi(zval); k=1; } else k=0;
  for (i=1; i<=ex; i++)
    for (j=1; j<lg(fa[i]); j++)
    {
      k++; v[k]=lcopy(gmael(fa,i,j)); w[k]=lstoi(i);
    }
  gerepilemanyvec(av,av2,y+1,2);
  return sort_factor(y, cmpii);
}

/***********************************************************************/
/**                                                                   **/
/**                          FACTORISATION                            **/
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
  long t[LT]; /* code pour 0,1,2,3,61,62,63,67,7,81,82,83,86,87,91,93,97 */
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
        if (!pcx)
        {
          pcx = cgetg(5,t_POL); /* x^2 + 1 */
          pcx[1] = evalsigne(1)|evalvarn(0)|m_evallgef(5),
          pcx[2]=pcx[4]=un; pcx[3]=zero;
        }
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

/* assume f and g coprime integer factorizations */
GEN
merge_factor_i(GEN f, GEN g)
{
  GEN h;
  if (lg(f) == 1) return g;
  if (lg(g) == 1) return f;
  h = cgetg(3,t_MAT);
  h[1] = (long)concatsp((GEN)f[1], (GEN)g[1]);
  h[2] = (long)concatsp((GEN)f[2], (GEN)g[2]);
  return sort_factor_gen(h, cmpii);
}

GEN
factor(GEN x)
{
  long tx=typ(x),lx,av,tetpil,i,j,pa,v,r1;
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
      x = gred(x); /* fall through */
    case t_FRAC:
      p1 = decomp((GEN)x[1]);
      p2 = decomp((GEN)x[2]); p2[2] = (long)gneg_i((GEN)p2[2]);
      return gerepileupto(av, gcopy(merge_factor_i(p1,p2)));

    case t_POL:
      tx=poltype(x,&p,&pol,&pa);
      switch(tx)
      {
        case 0: err(impl,"factor for general polynomials");
	case t_INT: return factpol(x,1);
	case t_INTMOD: return factmod(x,p);

	case t_COMPLEX: y=cgetg(3,t_MAT); lx=lgef(x)-2; v=varn(x);
	  av = avma; p1 = roots(x,pa); tetpil = avma;
          p2=cgetg(lx,t_COL);
	  for (i=1; i<lx; i++)
            p2[i] = (long)deg1pol_i(gun, gneg((GEN)p1[i]), v);
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
          killv = (avma != (ulong)pol);
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
      x=gred_rfrac(x); /* fall through */
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
factorback_i(GEN fa, GEN nf, int red)
{
  long av=avma,k,l,lx;
  GEN ex, x;
  GEN (*_mul)(GEN,GEN);
  GEN (*_pow)(GEN,GEN);

  if (typ(fa)!=t_MAT || lg(fa)!=3)
    err(talker,"not a factorisation in factorback");
  ex=(GEN)fa[2]; fa=(GEN)fa[1];
  lx = lg(fa); if (lx == 1) return gun;
  x = cgetg(lx,t_VEC);
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
  for (l=1,k=1; k<lx; k++)
    if (signe(ex[k]))
      x[l++] = (long)_pow((GEN)fa[k],(GEN)ex[k]);
  setlg(x,l);
  return gerepileupto(av, divide_conquer_prod(x, _mul));
}

GEN
factorback(GEN fa, GEN nf)
{
  return factorback_i(fa,nf,0);
}

GEN
gisirreducible(GEN x)
{
  long av=avma, tx = typ(x),l,i;
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
/*                         PGCD GENERAL                            */
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
  long av = avma, tetpil;
  GEN p1 = (typ(x)==t_COMPLEX)? ggcd((GEN)x[1],(GEN)x[2])
                              : ggcd((GEN)x[2],(GEN)x[3]);
  tetpil=avma; return gerepile(av,tetpil,ggcd(p1,y));
}

static GEN
cont_gcd(GEN x, GEN y)
{
  long av = avma, tetpil;
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

#define fix_frac(z) if (signe(z[2])<0)\
{\
  setsigne(z[1],-signe(z[1]));\
  setsigne(z[2],1);\
}

GEN
ggcd(GEN x, GEN y)
{
  long l,av,tetpil,i,vx,vy, tx = typ(x), ty = typ(y);
  GEN p1,z;

  if (tx>ty) { p1=x; x=y; y=p1; l=tx; tx=ty; ty=l; }
  if (is_matvec_t(ty))
  {
    l=lg(y); z=cgetg(l,ty);
    for (i=1; i<l; i++) z[i]=lgcd(x,(GEN)y[i]);
    return z;
  }
  if (is_noncalc_t(tx) || is_noncalc_t(ty)) err(operf,"g",tx,ty);
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
          z[1]=lmppgcd((GEN)x[1],(GEN)y[1]);
        if (gcmp1((GEN)z[1])) z[2]=zero;
        else
        {
          av=avma; p1=mppgcd((GEN)z[1],(GEN)x[2]);
          if (!gcmp1(p1))
          {
            tetpil=avma;
            p1=gerepile(av,tetpil,mppgcd(p1,(GEN)y[2]));
          }
          z[2]=(long)p1;
        }
        return z;

      case t_FRAC: z=cgetg(3,t_FRAC);
        z[1] = (long)mppgcd((GEN)x[1], (GEN)y[1]);
        z[2] = (long)mpppcm((GEN)x[2], (GEN)y[2]);
        return z;

      case t_COMPLEX:
        av=avma; p1=gdiv(x,y);
        if (gcmp0((GEN)p1[2]))
        {
          p1=(GEN)p1[1];
          switch(typ(p1))
          {
            case t_INT:
              avma=av; return gcopy(y);
            case t_FRAC: case t_FRACN:
              tetpil=avma; return gerepile(av,tetpil,gdiv(y,(GEN)p1[2]));
            default: avma=av; return gun;
          }
        }
        avma=av;
        if (typ(p1[1])==t_INT && typ(p1[2])==t_INT) return gcopy(y);
        p1=gdiv(y,x); avma=av;
        if (typ(p1[1])==t_INT && typ(p1[2])==t_INT) return gcopy(x);
        return triv_cont_gcd(y,x);

      case t_PADIC:
        if (!egalii((GEN)x[2],(GEN)y[2])) return gun;
        return gpuigs((GEN)y[2],min(valp(y),valp(x)));

      case t_QUAD:
        av=avma; p1=gdiv(x,y);
        if (gcmp0((GEN)p1[3]))
        {
          p1=(GEN)p1[2];
          if (typ(p1)==t_INT) { avma=av; return gcopy(y); }
          tetpil=avma; return gerepile(av,tetpil, gdiv(y,(GEN)p1[2]));
        }
        avma=av;
        if (typ(p1[2])==t_INT && typ(p1[3])==t_INT) return gcopy(y);
        p1=gdiv(y,x); avma=av;
        if (typ(p1[2])==t_INT && typ(p1[3])==t_INT) return gcopy(x);
        return triv_cont_gcd(y,x);

      default: return gun; /* t_REAL */
    }
    if (is_const_t(ty)) switch(tx)
    {
      case t_INT:
        switch(ty)
        {
          case t_INTMOD: z=cgetg(3,t_INTMOD);
            copyifstack(y[1],z[1]); av=avma;
            p1=mppgcd((GEN)y[1],(GEN)y[2]);
            if (!gcmp1(p1))
              { tetpil=avma; p1=gerepile(av,tetpil,mppgcd(x,p1)); }
            z[2]=(long)p1; return z;

          case t_FRAC: z=cgetg(3,t_FRAC);
            z[1]=lmppgcd(x,(GEN)y[1]);
            z[2]=licopy((GEN)y[2]); return z;

          case t_COMPLEX: case t_QUAD:
            return triv_cont_gcd(y,x);

          case t_PADIC:
            return padic_gcd(x,y);

          default: /* t_REAL */
            return gun;
        }

      case t_INTMOD:
        switch(ty)
        {
          case t_FRAC:
            av=avma; p1=mppgcd((GEN)x[1],(GEN)y[2]); tetpil=avma;
            if (!gcmp1(p1)) err(operi,"g",tx,ty);
            return gerepile(av,tetpil, ggcd((GEN)y[1],x));

          case t_COMPLEX: case t_QUAD:
            return triv_cont_gcd(y,x);

          case t_PADIC:
            return padic_gcd(x,y);
        }

      case t_FRAC:
        switch(ty)
        {
          case t_COMPLEX: case t_QUAD:
            return triv_cont_gcd(y,x);

          case t_PADIC:
            return padic_gcd(x,y);
        }

      case t_COMPLEX: /* ty = PADIC or QUAD */
        return triv_cont_gcd(x,y);

      case t_PADIC: /* ty = QUAD */
        return triv_cont_gcd(y,x);

      default: /* tx = t_REAL */
        return gun;
    }
    return cont_gcd(y,x);
  }

  vx=gvar9(x); vy=gvar9(y);
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
	  av=avma; p1=ggcd((GEN)x[1],(GEN)y[2]); tetpil=avma;
          if (!gcmp1(p1)) err(operi,"g",tx,ty);
	  return gerepile(av,tetpil,ggcd((GEN)y[1],x));

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
      if (!is_rfrac_t(ty)) err(operf,"g",tx,ty);
      p1 = gdiv((GEN)y[2], ggcd((GEN)x[2], (GEN)y[2]));
      tetpil = avma;
      z[2] = lpile((long)z,tetpil,gmul(p1, (GEN)x[2]));
      z[1] = lgcd((GEN)x[1], (GEN)y[1]); return z;
  }
  err(operf,"g",tx,ty);
  return NULL; /* not reached */
}

GEN glcm0(GEN x, GEN y)
{
  return gassoc_proto(glcm,x,y);
}

GEN
glcm(GEN x, GEN y)
{
  long av,tx,ty,i,l;
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

static GEN
polgcdnun(GEN x, GEN y)
{
  long av1, av = avma, lim = stack_lim(av,1);
  GEN p1, yorig = y;

  for(;;)
  {
    av1 = avma; p1 = gres(x,y);
    if (gcmp0(p1))
    {
      avma = av1;
      if (lgef(y) == 3 && isinexactreal(y)) { avma = av; return gun; }
      return (y==yorig)? gcopy(y): gerepileupto(av,y);
    }
    x = y; y = p1;
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
isrational(GEN x)
{
  long i;
  for (i=lgef(x)-1; i>1; i--)
    switch(typ(x[i]))
    {
      case t_INT:
      case t_FRAC: break;
      default: return 0;
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
  long tetpil,av=avma, lx=lgef(x), v=varn(x), e=gval(y,v);
  GEN p1,p2;

  if (lx-3<e) e=lx-3;
  p1=ggcd(leading_term(x),content(y)); p2=gpuigs(polx[v],e);
  tetpil=avma; return gerepile(av,tetpil,gmul(p1,p2));
}

/***********************************************************************/
/**                                                                   **/
/**                         BEZOUT GENERAL                            **/
/**                                                                   **/
/***********************************************************************/

static GEN
polinvinexact(GEN x, GEN y)
{
  long i,dx=deg(x),dy=deg(y),lz=dx+dy, av=avma, tetpil;
  GEN v,z;

  if (dx < 0 || dy < 0) err(talker,"non-invertible polynomial in polinvmod");
  z=cgetg(dy+2,t_POL); z[1]=y[1];
  v=cgetg(lz+1,t_COL);
  for (i=1; i<lz; i++) v[i]=zero;
  v[lz]=un; v=gauss(sylvestermatrix(y,x),v);
  for (i=2; i<dy+2; i++) z[i]=v[lz-i+2];
  z = normalizepol_i(z, dy+2); tetpil = avma;
  return gerepile(av,tetpil,gcopy(z));
}

static GEN
polinvmod(GEN x, GEN y)
{
  long av,av1,tx,vx=varn(x),vy=varn(y);
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
/*                    CONTENU ET PARTIE PRIMITIVE                  */
/*                                                                 */
/*******************************************************************/

GEN
content(GEN x)
{
  long lx,i,tx=typ(x);
  ulong av,tetpil;
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

/*******************************************************************/
/*                                                                 */
/*                         SOUS RESULTANT                          */
/*                                                                 */
/*******************************************************************/
GEN diviiexact(GEN x, GEN y);
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
    if (tx==t_POL) return gpuigs(y,deg(x));
    if (ty==t_POL) return gpuigs(x,deg(y));
    return gun;
  }
  if (tx!=t_POL || ty!=t_POL) err(typeer,"subresall");
  if (varn(x)==varn(y)) return NULL;
  return (varn(x)<varn(y))? gpuigs(y,deg(x)): gpuigs(x,deg(y));
}

/* return coefficients s.t x = x_0 X^n + ... + x_n */
static GEN
revpol(GEN x)
{
  long i,n = deg(x);
  GEN y = cgetg(n+3,t_POL);
  y[1] = x[1]; x += 2; y += 2;
  for (i=0; i<=n; i++) y[i] = x[n-i];
  return y;
}

/* assume dx >= dy, y non constant */
GEN
pseudorem(GEN x, GEN y)
{
  long av = avma, av2,lim, vx = varn(x),dx,dy,dz,i,lx, p;

  if (!signe(y)) err(talker,"euclidean division by zero (pseudorem)");
  (void)new_chunk(2);
  dx=deg(x); x = revpol(x);
  dy=deg(y); y = revpol(y); dz=dx-dy; p = dz+1;
  av2 = avma; lim = stack_lim(av2,1);
  for (;;)
  {
    x[0] = lneg((GEN)x[0]); p--;
    for (i=1; i<=dy; i++)
      x[i] = ladd(gmul((GEN)y[0], (GEN)x[i]), gmul((GEN)x[0],(GEN)y[i]));
    for (   ; i<=dx; i++)
      x[i] = lmul((GEN)y[0], (GEN)x[i]);
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
  return gerepileupto(av, gmul(x, gpowgs((GEN)y[0], p)));
}

/* Si sol != NULL:
 *   met dans *sol le dernier polynome non nul de la polynomial remainder
 *   sequence si elle a ete effectuee, 0 sinon
 */
GEN
subresall(GEN u, GEN v, GEN *sol)
{
  long degq,av,av2,lim,tetpil,dx,dy,du,dv,dr,signh;
  GEN g,h,r,p1,p2,cu,cv;

  if (sol) *sol=gzero;
  if ((r = init_resultant(u,v))) return r;

  if (isinexactfield(u) || isinexactfield(v)) return resultant2(u,v);
  dx=lgef(u); dy=lgef(v); signh=1;
  if (dx<dy)
  {
    p1=u; u=v; v=p1; du=dx; dx=dy; dy=du;
    if ((dx&1) == 0 && (dy&1) == 0) signh = -signh;
  }
  if (dy==3) return gpowgs((GEN)v[2],dx-3);
  av=avma;
  cu=content(u); if (gcmp1(cu)) cu=NULL; else u=gdiv(u,cu);
  cv=content(v); if (gcmp1(cv)) cv=NULL; else v=gdiv(v,cv);
  g=gun; h=gun; av2 = avma; lim = stack_lim(av2,1);
  for(;;)
  {
    r = pseudorem(u,v); dr = lgef(r);
    if (dr==2)
    {
      if (sol) {avma = (long)(r+2); *sol=gerepileupto(av,v);} else avma = av;
      return gzero;
    }
    du=lgef(u); dv=lgef(v);
    degq=du-dv; u=v;
    p1 = g; g = leading_term(u);
    switch(degq)
    {
      case 0: break;
      case 1:
        p1 = gmul(h,p1); h = g; break;
      default:
        p1 = gmul(gpuigs(h,degq),p1);
        h = gdivexact(gpuigs(g,degq), gpuigs(h,degq-1));
    }
    if ((du&1) == 0 && (dv&1) == 0) signh = -signh;
    v = gdivexact(r,p1);
    if (dr==3) break;
    if (low_stack(lim,stack_lim(av2,1)))
    {
      GEN *gptr[4]; gptr[0]=&u; gptr[1]=&v; gptr[2]=&g; gptr[3]=&h;
      if(DEBUGMEM>1) err(warnmem,"subresall, dr = %ld",dr);
      gerepilemany(av2,gptr,4);
    }
  }
  if (dv==4) { tetpil=avma; p2=gcopy((GEN)v[2]); }
  else
  {
    if (dv == 3) err(bugparier,"subres");
    p1=gpuigs((GEN)v[2],dv-3); p2=gpuigs(h,dv-4);
    tetpil=avma; p2=gdiv(p1,p2);
  }
  if (cu) { p1=gpuigs(cu,dy-3); tetpil=avma; p2=gmul(p2,p1); }
  if (cv) { p1=gpuigs(cv,dx-3); tetpil=avma; p2=gmul(p2,p1); }
  if (signh<0) { tetpil=avma; p2=gneg(p2); }
  {
    GEN *gptr[2]; gptr[0]=&p2; if (sol) { *sol=gcopy(u); gptr[1]=sol; }
    gerepilemanysp(av,tetpil,gptr,sol?2:1);
    return p2;
  }
}

static GEN
scalar_res(GEN x, GEN y, GEN *U, GEN *V)
{
  long dx=lgef(x)-4;
  *V=gpuigs(y,dx); *U=gzero; return gmul(y,*V);
}

/* calcule U et V tel que Ux+By=resultant(x,y) */
GEN
subresext(GEN x, GEN y, GEN *U, GEN *V)
{
  long degq,av,tetpil,tx,ty,dx,dy,du,dv,dr,signh;
  GEN z,g,h,r,p1,p2,p3,p4,u,v,lpu,um1,uze, *gptr[2];

  if (gcmp0(x) || gcmp0(y)) { *U = *V = gzero; return gzero; }
  tx=typ(x); ty=typ(y);
  if (is_scalar_t(tx) || is_scalar_t(ty))
  {
    if (tx==t_POL) return scalar_res(x,y,U,V);
    if (ty==t_POL) return scalar_res(y,x,V,U);
    *U=ginv(x); *V=gzero; return gun;
  }
  if (tx!=t_POL || ty!=t_POL) err(typeer,"subresext");
  if (varn(x)!=varn(y))
    return (varn(x)<varn(y))? scalar_res(x,y,U,V)
                            : scalar_res(y,x,V,U);
  dx=lgef(x); dy=lgef(y); signh=1;
  if (dx<dy)
  {
    GEN *W = U; U=V; V=W;
    du=dx; dx=dy; dy=du; p1=x; x=y; y=p1;
    if ((dx&1) == 0 && (dy&1) == 0) signh = -signh;
  }
  if (dy==3)
  {
    *V=gpuigs((GEN)y[2],dx-4);
    *U=gzero; return gmul(*V,(GEN)y[2]);
  }
  av=avma;
  p3=content(x); if (gcmp1(p3)) {p3 = NULL; u=x; } else u=gdiv(x,p3);
  p4=content(y); if (gcmp1(p4)) {p4 = NULL; v=y; } else v=gdiv(y,p4);
  g=gun; h=gun; um1=gun; uze=gzero;
  for(;;)
  {
    du=lgef(u); dv=lgef(v); degq=du-dv;
    lpu=gpuigs((GEN)v[dv-1],degq+1);
    p1=gmul(lpu,u); p2=poldivres(p1,v,&r);
    dr=lgef(r); if (dr==2) { *U=gzero; *V=gzero; avma=av; return gzero; }

    p1=gsub(gmul(lpu,um1),gmul(p2,uze));
    um1=uze; uze=p1; u=v;
    p1 = g; g = leading_term(u);
    switch(degq)
    {
      case 0: break;
      case 1: p1 = gmul(h,p1); h = g; break;
      default:
        p1 = gmul(gpuigs(h,degq),p1);
        h = gdivexact(gpuigs(g,degq), gpuigs(h,degq-1));
    }
    if ((du & 1) == 0 && (dv & 1) == 0) signh= -signh;
    v=gdivexact(r,p1); uze=gdivexact(uze,p1);
    if (dr==3) break;
  }

  p2=(dv==4)?gun:gpuigs(gdiv((GEN)v[2],h),dv-4);
  if (p3) p2 = gmul(p2,gpuigs(p3,dy-3));
  if (p4) p2 = gmul(p2,gpuigs(p4,dx-3));
  if (signh<0) p2=gneg_i(p2);
  p3 = p3? gdiv(p2,p3): p2;

  tetpil=avma; z=gmul((GEN)v[2],p2); uze=gmul(uze,p3);
  gptr[0]=&z; gptr[1]=&uze; gerepilemanysp(av,tetpil,gptr,2);

  av=avma; p1 = gadd(z, gneg(gmul(uze,x))); tetpil = avma;
  if (!poldivis(p1,y,&p1)) err(bugparier,"subresext");
  *U=uze; *V=gerepile(av,tetpil,p1); return z;
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

/* calcule U et V tel que Ux+Vy=GCD(x,y) par le sous-resultant */
GEN
bezoutpol(GEN x, GEN y, GEN *U, GEN *V)
{
  long degq,av,tetpil,tx,ty,dx,dy,du,dv,dr;
  GEN g,h,r,p1,p2,p3,p4,u,v,lpu,um1,uze,vze,xprim,yprim;
  GEN *gptr[3];

  if (gcmp0(x)) return zero_bezout(y,U,V);
  if (gcmp0(y)) return zero_bezout(x,V,U);
  tx=typ(x); ty=typ(y); av=avma;
  if (is_scalar_t(tx) || is_scalar_t(ty))
  {
    if (tx==t_POL) return scalar_bezout(x,y,U,V);
    if (ty==t_POL) return scalar_bezout(y,x,V,U);
    *U=ginv(x); *V=gzero; return polun[0];
  }
  if (tx!=t_POL || ty!=t_POL) err(typeer,"bezoutpol");
  if (varn(x)!=varn(y))
    return (varn(x)<varn(y))? scalar_bezout(x,y,U,V)
                            : scalar_bezout(y,x,V,U);
  dx=lgef(x); dy=lgef(y);
  if (dx<dy)
  {
    GEN *W=U; U=V; V=W;
    p1=x; x=y; y=p1; du=dx; dx=dy; dy=du;
  }
  if (dy==3) return scalar_bezout(x,y,U,V);

  p3=content(x); u=gdiv(x,p3);
  p4=content(y); v=gdiv(y,p4);
  xprim=u; yprim=v; g=gun; h=gun; um1=gun; uze=gzero;
  for(;;)
  {
    du=lgef(u); dv=lgef(v); degq=du-dv;
    lpu=gpuigs((GEN)v[dv-1],degq+1);
    p1=gmul(lpu,u); p2=poldivres(p1,v,&r);
    dr=lgef(r); if (dr<=2) break;
    p1=gsub(gmul(lpu,um1),gmul(p2,uze)); um1=uze; uze=p1;

    u=v; p1 = g; g  = leading_term(u);
    switch(degq)
    {
      case 0: break;
      case 1:
        p1 = gmul(h,p1); h = g; break;
      default:
        p1 = gmul(gpuigs(h,degq), p1);
        h = gdiv(gpuigs(g,degq), gpuigs(h,degq-1));
    }
    v=gdiv(r,p1); uze=gdiv(uze,p1);
    if (dr==3) break;
  }
  if (!poldivis(gsub(v,gmul(uze,xprim)),yprim, &vze))
    err(warner,"non-exact computation in bezoutpol");
  uze=gdiv(uze,p3); vze=gdiv(vze,p4); p1=ginv(content(v));

  tetpil=avma; uze=gmul(uze,p1); vze=gmul(vze,p1); p1=gmul(v,p1);
  gptr[0]=&uze; gptr[1]=&vze; gptr[2]=&p1;
  gerepilemanysp(av,tetpil,gptr,3);
  *U=uze; *V=vze; return p1;
}



/*******************************************************************/
/*                                                                 */
/*               RESULTANT PAR L'ALGORITHME DE DUCOS               */
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
  long p, q, j, av, lim, v = varn(P);

  z0 = leading_term(Z);
  p = degree(P); p0 = leading_term(P); P = reductum(P);
  q = degree(Q); q0 = leading_term(Q); Q = reductum(Q);

  av = avma; lim = stack_lim(av,1);
  H = gneg(reductum(Z));
  A = gmul((GEN)P[q+2],H);
  for (j = q+1; j < p; j++)
  {
    H = (degree(H) == q-1) ?
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
  A = (degree(H) == q-1) ?
    gadd(gmul(q0,addshift(reductum(H),A)), gmul(gneg((GEN)H[q+1]),Q)) :
    gmul(q0, addshift(H,A));
  return gdivexact(A, ((p-q)&1)? s: gneg(s));
}

GEN
resultantducos(GEN P, GEN Q)
{
  ulong av = avma, lim = stack_lim(av,1);
  long dP,dQ,delta;
  GEN cP,cQ,Z,s;

  if ((Z = init_resultant(P,Q))) return Z;
  dP = degree(P);
  dQ = degree(Q);
  cP = content(P); if (gcmp1(cP)) cP = NULL; else P = gdiv(P,cP);
  cQ = content(Q); if (gcmp1(cQ)) cQ = NULL; else Q = gdiv(Q,cQ);
  delta = dP - dQ;
  if (delta < 0)
  {
    Z = (dP & dQ & 1)? gneg(Q): Q;
    Q = P; P = Z; delta = -delta;
  }
  s = gun;
  if (degree(Q) > 0)
  {
    s = gpuigs(leading_term(Q),delta);
    Z = Q;
    Q = pseudorem(P, gneg(Q));
    P = Z;
    while(degree(Q) > 0)
    {
      if (low_stack(lim,stack_lim(av,1)))
      {
        GEN *gptr[2]; gptr[0]=&P; gptr[1]=&Q;
        if(DEBUGMEM>1) err(warnmem,"resultantducos, deg Q = %ld",degree(Q));
        gerepilemany(av,gptr,2); s = leading_term(P);
      }
      delta = degree(P) - degree(Q);
      Z = Lazard2(Q, leading_term(Q), s, delta);
      Q = nextSousResultant(P, Q, Z, s);
      P = Z;
      s = leading_term(P);
    }
  }
  if (!signe(Q)) { avma = av; return gzero; }
  if (!degree(P)){ avma = av; return gun; }
  s = Lazard(leading_term(Q), s, degree(P));
  if (cP) s = gmul(s, gpowgs(cP,dQ));
  if (cQ) s = gmul(s, gpowgs(cQ,dP)); else if (!cP) s = gcopy(s);
  return gerepileupto(av, s);
}

/*******************************************************************/
/*                                                                 */
/*               RESULTANT PAR MATRICE DE SYLVESTER                */
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

  dx = deg(x); if (dx < 0) { dx = 0; x = _zeropol(); }
  dy = deg(y); if (dy < 0) { dy = 0; y = _zeropol(); }
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
  long av;
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
 * main variable if v < 0.
 */
GEN
polresultant0(GEN x, GEN y, long v, long flag)
{
  long av = avma, m = 0;

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
/*           P.G.C.D PAR L'ALGORITHME DU SOUS RESULTANT            */
/*                                                                 */
/*******************************************************************/

GEN
srgcd(GEN x, GEN y)
{
  long av,av1,tetpil,tx=typ(x),ty=typ(y),dx,dy,vx,lim;
  GEN d,g,h,p1,p2,u,v;

  if (!signe(y)) return gcopy(x);
  if (!signe(x)) return gcopy(y);
  if (is_scalar_t(tx) || is_scalar_t(ty)) return gun;
  if (tx!=t_POL || ty!=t_POL) err(typeer,"srgcd");
  vx=varn(x); if (vx!=varn(y)) return gun;
  if (ismonome(x)) return gcdmonome(x,y);
  if (ismonome(y)) return gcdmonome(y,x);
  if (isrational(x) && isrational(y)) return modulargcd(x,y);

  av=avma;
  if (issimplefield(x) || issimplefield(y)) x = polgcdnun(x,y);
  else
  {
    dx=lgef(x); dy=lgef(y);
    if (dx<dy) { p1=x; x=y; y=p1; tx=dx; dx=dy; dy=tx; }
    p1=content(x); p2=content(y); d=ggcd(p1,p2);

    tetpil=avma; d=gmul(d,polun[vx]);
    if (dy==3) return gerepile(av,tetpil,d);

    av1=avma; lim=stack_lim(av1,1);
    u=gdiv(x,p1); v=gdiv(y,p2); g=h=gun;
    for(;;)
    {
      GEN r = pseudorem(u,v);
      long degq, du, dv, dr=lgef(r);

      if (dr<=3)
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
  long av,tx=typ(x),i;
  GEN z,p1,p2;

  switch(tx)
  {
    case t_POL:
      if (gcmp0(x)) return gzero;
      av = avma; i = 0;
      if (v >= 0 && v != varn(x)) x = fix_pol(x,v, &i);
      p1 = subres(x, derivpol(x));
      p2 = leading_term(x); if (!gcmp1(p2)) p1 = gdiv(p1,p2);
      if (deg(x) & 2) p1 = gneg(p1);
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
  long av=avma,tetpil,i,j,n;
  GEN polp,alpha,p1,m;

  if (typ(pol)!=t_POL) err(typeer,"reduceddiscsmith");
  n=deg(pol);
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
/**	                 ALGORITHME DE STURM                          **/
/**	         (number of real roots of x in ]a,b])		      **/
/**								      **/
/***********************************************************************/

/* if a (resp. b) is NULL, set it to -oo (resp. +oo) */
long
sturmpart(GEN x, GEN a, GEN b)
{
  long av = avma, lim = stack_lim(av,1), sl,sr,s,t,r1;
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
        h = gdiv(gpuigs(g,degq), gpuigs(h,degq-1));
    }
    v = gdiv(r,p1);
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
/*         POLYNOME QUADRATIQUE ASSOCIE A UN DISCRIMINANT          */
/*                                                                 */
/*******************************************************************/

GEN
quadpoly0(GEN x, long v)
{
  long res,l,tetpil,i,sx, tx = typ(x);
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

  l=avma; p1=shifti(x,-2); setsigne(p1,-signe(p1));
  y[2] = (long) p1;
  if (!res) y[3] = zero;
  else
  {
    if (sx<0) { tetpil=avma; y[2] = lpile(l,tetpil,addsi(1,p1)); }
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
/*                    INVERSE MODULO GENERAL                       */
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
  long *vval, num[] = {evaltyp(t_INT) | m_evallg(3), 0, 0};

  if (typ(x)!=t_POL) err(typeer,"newtonpoly");
  n=deg(x); if (n<=0) { y=cgetg(1,t_VEC); return y; }
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
GEN matratlift(GEN M, GEN mod, GEN amax, GEN bmax, GEN denom);
GEN nfgcd(GEN P, GEN Q, GEN nf, GEN den);

/* Factor polynomial a on the number field defined by polynomial t */
GEN
polfnf(GEN a, GEN t)
{
  ulong av = avma;
  GEN x0,y,p1,p2,u,fa,n,unt,dent,alift;
  long lx,i,k,e;
  int sqfree, tmonic;

  if (typ(a)!=t_POL || typ(t)!=t_POL) err(typeer,"polfnf");
  if (gcmp0(a)) return gcopy(a);
  a = fix_relative_pol(t,a,0);
  alift = lift(a);
  p1 = content(alift); if (!gcmp1(p1)) { a = gdiv(a, p1); alift = lift(a); }
  p1 = content(t); if (!gcmp1(t)) t = gdiv(t, p1);
  tmonic = is_pm1(leading_term(t));

  dent = ZX_disc(t); unt = gmodulsg(1,t);
  u = nfgcd(alift,derivpol(alift), t, dent);
  sqfree = gcmp1(u);
  u = sqfree? alift: lift_intern(gdiv(a, gmul(unt,u)));
  k = 0; n = ZY_ZXY_resultant(t, u, &k);
  if (DEBUGLEVEL > 4) fprintferr("polfnf: choosing k = %ld\n",k);

  /* n guaranteed to be squarefree */
  fa = squff2(n,0); lx = lg(fa);
  y = cgetg(3,t_MAT);
  p1 = cgetg(lx,t_COL); y[1] = (long)p1;
  p2 = cgetg(lx,t_COL); y[2] = (long)p2;
  x0 = gadd(polx[varn(a)], gmulsg(-k, gmodulcp(polx[varn(t)], t)));
  for (i=lx-1; i>1; i--)
  {
    GEN b, F = lift_intern(poleval((GEN)fa[i], x0));
    if (!tmonic) F = gdiv(F, content(F));
    F = nfgcd(u, F, t, dent);
    if (typ(F) != t_POL || deg(F) == 0)
      err(talker,"reducible modulus in factornf");
    F = gmul(unt, F);
    F = gdiv(F, leading_term(F));
    u = lift_intern(gdeuc(u, F));
    u = gdiv(u, content(u));
    if (sqfree) e = 1;
    else
    {
      e = 0; while (poldivis(a,F, &b)) { a = b; e++; }
      if (deg(a) == deg(u)) sqfree = 1;
    }
    p1[i] = (long)F;
    p2[i] = lstoi(e);
  }
  u = gmul(unt, u);
  u = gdiv(u, leading_term(u));
  p1[1] = (long)u;
  e = sqfree? 1: deg(a)/deg(u);
  p2[1] = lstoi(e);
  (void)sort_factor(y, cmp_pol);
  return gerepileupto(av, gcopy(y));
}

GEN FpXQX_safegcd(GEN P, GEN Q, GEN T, GEN p);
GEN FpM(GEN z, GEN p);
GEN polpol_to_mat(GEN v, long n);
GEN mat_to_polpol(GEN x, long v, long w);

static GEN
to_frac(GEN a, GEN b)
{
  GEN f = cgetg(3, t_FRAC);
  f[1] = (long)a;
  f[2] = (long)b; return f;
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
  ulong ltop = avma;
  GEN N, a, b;
  long l2, l3;
  long i, j;
  if (typ(M)!=t_MAT) err(typeer,"matratlift");
  l2 = lg(M)-1; l3 = lg((GEN)M[1])-1;
  N = cgetg(l2 + 1, t_MAT);
  for (j = 1; j <= l2; ++j)
  {
    N[j] = lgetg(l3 + 1, t_COL);
    for (i = 1; i <= l3; ++i)
    {
      if (!ratlift(gcoeff(M,i,j), mod, &a, &b, amax, bmax)
	 || (denom && !divise(denom,b))
         || !gcmp1(mppgcd(a,b))) { avma = ltop; return NULL; }
      if (!is_pm1(b)) a = to_frac(a, b);
      coeff(N, i, j) = (long)a;
    }
  }
  return N;
}

GEN
polratlift(GEN P, GEN mod, GEN amax, GEN bmax, GEN denom)
{
  ulong ltop = avma;
  GEN Q,a,b,t;
  long l2, j;
  if (typ(P)!=t_POL) err(typeer,"polratlift");
  l2 = lg(P);
  Q = cgetg(l2, t_POL); Q[1] = P[1];
  for (j = 2; j < l2; ++j)
  {
    t = (GEN)P[j];
    if (signe(t) < 0) t = addii(t, mod);
    if (!ratlift(t, mod, &a, &b, amax, bmax)
        || (denom && !divise(denom,b))
        || !gcmp1(mppgcd(a,b))) { avma=ltop; return NULL; }
    if (!is_pm1(b)) a = to_frac(a, b);
    Q[j] = (long)a;
  }
  return Q;
}

/* P,Q in Z[X,Y], nf in Z[Y] irreducible. compute GCD in Q[Y]/(nf)[X].
 *
 * We essentially follows the paper of M. Encarnacion
 * "On a modular Algorithm for computing GCDs of polynomials over
 * number fields" in the proceeding of ISSAC'94.
 *
 * We procede as follows :
 * We compute the gcd modulo primes discarding bad primes as they are detected.
 * We try reconstruct the result with matratlift, stoping as soon as we get
 * weird denominators.
 *
 * If matratlift succeed, we then try the full division.
 * Suppose we does not have sufficient accuracy to get the result right:
 * It is extremly rare that matratlift will succeed, and even if it does, the
 * polynomial we get has reasonnable coefficients, so the full division will
 * not be too costly.
 *
 * FIXME: Handle rational coefficient for P and Q.
 * If not NULL, den must a a multiple of the denominator of the gcd,
 * for example the discriminant of nf.
 * Use resultantducos for now.(ref: polresultant0)
 *
 * NOTE: if nf is not irreducible, nfgcd may loop forever, especially if the
 * gcd divides nf !
 */
GEN nfgcd(GEN P, GEN Q, GEN nf, GEN den)
{
  ulong ltop = avma;
  GEN sol, mod = NULL;
  long x = varn(P);
  long y = varn(nf);
  long d = deg(nf);
  GEN lP, lQ;
  if (!signe(P) || !signe(Q))
    return zeropol(x);
  /*Compute denominators*/
  if (!den) den = ZX_disc(nf);
  lP = leading_term(P);
  lQ = leading_term(Q);
  if ( !((typ(lP)==t_INT && is_pm1(lP)) || (typ(lQ)==t_INT && is_pm1(lQ))) )
    den = mulii(den, mppgcd(resultantducos(lP, nf), resultantducos(lQ, nf)));
  /*Modular GCD*/
  {
    ulong btop = avma;
    ulong st_lim = stack_lim(btop, 1);
    long p;
    long dM=0, dR;
    GEN M, dsol, dens;
    GEN R, ax, bo;
    byteptr primepointer;
    for (p = 27449, primepointer = diffptr + 3000; ; p += *(primepointer++))
    {
      if (!*primepointer) err(primer1);
      if (!smodis(den, p))
        continue;/*Discard primes dividing the disc(T) or leadingcoeff(PQ) */
      if (DEBUGLEVEL>=5) fprintferr("nfgcd: p=%d\n",p);
      if ((R = FpXQX_safegcd(P, Q, nf, stoi(p))) == NULL)
        continue;/*Discard primes when modular gcd does not exist*/
      dR = deg(R);
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
      dens = denom(sol);
      sol = mat_to_polpol(sol,x,y);
      dsol = gmul(sol, gmodulcp(dens, nf));
      if (gdivise(P, dsol) && gdivise(Q, dsol))
        break;
    }
  }
  return gerepileupto(ltop, gcopy(sol));
}

