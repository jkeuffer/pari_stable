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

/*******************************************************************/
/*                                                                 */
/*            POLYNOMIAL FACTORIZATION IN A NUMBER FIELD           */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "parinf.h"

extern GEN GS_norms(GEN B, long prec);
extern GEN RXQX_divrem(GEN x, GEN y, GEN T, GEN *pr);
extern GEN RXQX_red(GEN P, GEN T);
extern GEN apply_kummer(GEN nf,GEN pol,GEN e,GEN p);
extern GEN centermod_i(GEN x, GEN p, GEN ps2);
extern GEN dim1proj(GEN prh);
extern GEN hensel_lift_fact(GEN pol, GEN fact, GEN T, GEN p, GEN pev, long e);
extern GEN initgaloisborne(GEN T, GEN dn, long prec, GEN *ptL, GEN *ptprep, GEN *ptdis);
extern GEN max_modulus(GEN p, double tau);
extern GEN mulmat_pol(GEN A, GEN x);
extern GEN nfgcd(GEN P, GEN Q, GEN nf, GEN den);
extern GEN polsym_gen(GEN P, GEN y0, long n, GEN T, GEN N);
extern GEN sort_factor(GEN y, int (*cmp)(GEN,GEN));
extern GEN special_pivot(GEN x);
extern GEN trivfact(void);
extern GEN vandermondeinverse(GEN L, GEN T, GEN den, GEN prep);
extern GEN vconcat(GEN A, GEN B);
extern int cmbf_precs(GEN q, GEN A, GEN B, long *a, long *b, GEN *qa, GEN *qb);
extern int isrational(GEN x);
extern GEN LLL_check_progress(GEN Bnorm, long n0, GEN m, int final, pari_timer *T, long *ti_LLL);
extern void remake_GM(GEN nf, nffp_t *F, long prec);
#define RXQX_div(x,y,T) RXQX_divrem((x),(y),(T),NULL)
#define RXQX_rem(x,y,T) RXQX_divrem((x),(y),(T),ONLY_REM)

static GEN nfsqff(GEN nf,GEN pol,long fl);

/* for nf_bestlift: reconstruction of algebraic integers known mod \wp^k */
/* FIXME: assume \wp has degree 1 for now */
typedef struct {
  long a;    /* input known mod \wp^a */
  GEN pa;    /* p^a = Norm(\wp^a)*/
  GEN den;   /* denom(prk^-1) = p^a */
  GEN prk;   /* |.|^2 LLL-reduced basis (b_i) of \wp^a  (NOT T2-reduced) */
  GEN iprk;  /* den * prk^-1 */
  GEN GSmin; /* min |b_i^*|^2 */
  GEN ZpProj;/* projector to Zp / \wp^k = Z/p^k  (\wp unramified, degree 1) */
  GEN tozk;
  GEN topow;
} nflift_t;

typedef struct /* for use in nfsqff */
{
  nflift_t *L;
  GEN nf, pol, fact, res, bound, pr, pa, Br, ZC, dn, polbase, BS_2;
  long hint;
} nfcmbf_t;

GEN
RXQX_mul(GEN x, GEN y, GEN T)
{
  return RXQX_red(gmul(x,y), T);
}

static GEN
unifpol0(GEN nf,GEN pol,long flag)
{
  static long n = 0;
  static GEN vun = NULL;
  GEN f = (GEN) nf[1];
  long i = degpol(f);
  gpmem_t av;

  if (i != n)
  {
    n=i; if (vun) free(vun);
    vun = (GEN) gpmalloc((n+1)*sizeof(long));
    vun[0] = evaltyp(t_COL) | evallg(n+1); vun[1]=un;
    for ( ; i>=2; i--) vun[i]=zero;
  }

  av = avma;
  switch(typ(pol))
  {
    case t_INT: case t_FRAC: case t_RFRAC:
      if (flag) return gcopy(pol);
      pol = gmul(pol,vun); break;

    case t_POL:
      if (flag && !degpol(pol)) return gcopy(constant_term(pol));
      pol = gmodulcp(pol,f); /* fall through */
    case t_POLMOD:
      pol = algtobasis(nf,pol);
  }
  if (flag) pol = basistoalg(nf, lift(pol));
  return gerepileupto(av,pol);
}

/* Let pol be a polynomial with coefficients in Z or nf (vectors or polymods)
 * return the same polynomial with coefficients expressed:
 *  if flag=0: as vectors (on the integral basis).
 *  if flag=1: as polymods.
 */
GEN
unifpol(GEN nf,GEN pol,long flag)
{
  if (typ(pol)==t_POL && varn(pol) < varn(nf[1]))
  {
    long i, d = lgef(pol);
    GEN p1 = pol;

    pol=cgetg(d,t_POL); pol[1]=p1[1];
    for (i=2; i<d; i++)
      pol[i] = (long) unifpol0(nf,(GEN) p1[i],flag);

    return pol;
  }
  return unifpol0(nf,(GEN) pol, flag);
}

/* factorization of x modulo pr. Assume x already reduced */
GEN
FqX_factor(GEN x, GEN T, GEN p)
{
  GEN rep;
  if (!T)
  {
    rep = factmod0(x, p);
    rep[2] = (long)small_to_vec((GEN)rep[2]);
  }
  else
  {
    rep = factmod9(x, p, T);
    rep = lift_intern(lift_intern(rep));
  }
  return rep;
}

GEN
nffactormod(GEN nf, GEN x, GEN pr)
{
  long j, l, vx = varn(x), vn;
  gpmem_t av = avma;
  GEN z, rep, xrd, modpr, T, p;

  nf = checknf(nf);
  vn = varn((GEN)nf[1]);
  if (typ(x)!=t_POL) err(typeer,"nffactormod");
  if (vx >= vn)
    err(talker,"polynomial variable must have highest priority in nffactormod");

  modpr = nf_to_ff_init(nf, &pr, &T, &p);
  xrd = modprX(x, nf, modpr);
  rep = FqX_factor(xrd,T,p);
  z = (GEN)rep[1]; l = lg(z);
  for (j = 1; j < l; j++) z[j] = (long)modprX_lift((GEN)z[j], modpr);
  return gerepilecopy(av, rep);
}

/* If p doesn't divide bad and has a divisor of degree 1, return the latter. */
static GEN
choose_prime(GEN nf, GEN bad, GEN *p, byteptr *PT)
{
  GEN  q = icopy(gun), r, x = (GEN)nf[1];
  ulong pp = *p? itou(*p): 0;
  byteptr pt = *PT;
  gpmem_t av = avma;
  for (;;)
  {
    pp += *pt++; if (!*pt) err(primer1);
    if (! smodis(bad,pp)) continue;
    affui(pp, q);
    r = rootmod(x, q); if (lg(r) > 1) break;
    avma = av;
  }
  r = gsub(polx[varn(x)], lift_intern((GEN)r[1]));
  *p = q;
  *PT = pt; return apply_kummer(nf,r,gun,q);
}

static GEN
QXQ_normalize(GEN P, GEN T)
{
  GEN t = leading_term(P);
  if (!gcmp1(t))
  {
    if (is_rational_t(typ(t)))
      P = gdiv(P, t);
    else
      P = RXQX_mul(QX_invmod(t,T), P, T);
  }
  return P;
}

/* return the roots of pol in nf */
GEN
nfroots(GEN nf,GEN pol)
{
  gpmem_t av = avma;
  int d = degpol(pol);
  GEN A,g, T;

  nf = checknf(nf); T = (GEN)nf[1];
  if (typ(pol) != t_POL) err(notpoler,"nfroots");
  if (varn(pol) >= varn(T))
    err(talker,"polynomial variable must have highest priority in nfroots");
  if (d == 0) return cgetg(1,t_VEC);
  if (d == 1)
  {
    A = gneg_i(gdiv((GEN)pol[2],(GEN)pol[3]));
    return gerepilecopy(av, _vec( basistoalg(nf,A) ));
  }
  A = fix_relative_pol(nf,pol,0);
  A = primpart( lift_intern(A) );
  if (DEBUGLEVEL>3) fprintferr("test if polynomial is square-free\n");
  g = nfgcd(A, derivpol(A), T, NULL);

  if (degpol(g))
  { /* not squarefree */
    g = QXQ_normalize(g, T);
    A = RXQX_div(A,g,T);
  }
  A = QXQ_normalize(A, T);
  A = primpart(A);
  A = nfsqff(nf,A,1);
  return gerepileupto(av, gen_sort(A, 0, cmp_pol));
}

/* return a minimal lift of elt modulo id */
static GEN
nf_bestlift(GEN elt, GEN bound, nflift_t *T)
{
  GEN u;
  long i,l = lg(T->prk), t = typ(elt);
  if (t != t_INT)
  {
    if (t == t_POL) elt = mulmat_pol(T->tozk, elt);
    u = gmul(T->iprk,elt);
    for (i=1; i<l; i++) u[i] = (long)diviiround((GEN)u[i], T->pa);
  }
  else
  {
    u = gmul(elt, (GEN)T->iprk[1]);
    for (i=1; i<l; i++) u[i] = (long)diviiround((GEN)u[i], T->pa);
    elt = gscalcol(elt, l-1);
  }
  u = gsub(elt, gmul(T->prk, u));
  if (bound && gcmp(QuickNormL2(u,DEFAULTPREC), bound) > 0) u = NULL;
  return u;
}

static GEN
nf_bestlift_to_pol(GEN elt, GEN bound, nflift_t *T)
{
  GEN u = nf_bestlift(elt,bound,T);
  if (u) u = gmul(T->topow, u);
  return u;
}

/* return the lift of pol with coefficients of T2-norm <= C (if possible) */
static GEN
nf_pol_lift(GEN pol, GEN bound, nfcmbf_t *T)
{
  long i, d = lgef(pol);
  GEN x = cgetg(d,t_POL);
  nflift_t *L = T->L;

  x[1] = pol[1];
  for (i=2; i<d; i++)
  {
    x[i] = (long)nf_bestlift_to_pol((GEN)pol[i], bound, L);
    if (!x[i]) return NULL;
  }
  return x;
}

/* return the factorization of x in nf */
GEN
nffactor(GEN nf,GEN pol)
{
  GEN A,g,y,p1,rep,T;
  long l, j, d = degpol(pol);
  gpmem_t av;
  if (DEBUGLEVEL>3) (void)timer2();

  nf = checknf(nf); T = (GEN)nf[1];
  if (typ(pol) != t_POL) err(notpoler,"nffactor");
  if (varn(pol) >= varn(T))
    err(talker,"polynomial variable must have highest priority in nffactor");

  if (d == 0) return trivfact();
  rep = cgetg(3, t_MAT); av = avma;
  if (d == 1)
  {
    rep[1] = (long)_col( gcopy(pol) );
    rep[2] = (long)_col( gun );
    return rep;
  }

  A = fix_relative_pol(nf,pol,0);
  A = primpart( lift_intern(A) );
  if (DEBUGLEVEL>3) fprintferr("test if polynomial is square-free\n");
  g = nfgcd(A, derivpol(A), T, NULL);

  A = QXQ_normalize(A, T);
  A = primpart(A);

  if (degpol(g))
  { /* not squarefree */
    gpmem_t av1;
    GEN ex;
    g = QXQ_normalize(g, T);
    A = RXQX_div(A,g, T);

    y = nfsqff(nf,A,0); av1 = avma;
    l = lg(y);
    ex=(GEN)gpmalloc(l * sizeof(long));
    for (j=l-1; j>=1; j--)
    {
      GEN fact = lift((GEN)y[j]), quo = g, q;
      long e = 0;
      for(e = 1;; e++)
      {
        q = RXQX_divrem(quo,fact,T, ONLY_DIVIDES);
        if (!q) break;
        quo = q;
      }
      ex[j] = e;
    }
    avma = av1; y = gerepileupto(av, y);
    p1 = cgetg(l, t_COL); for (j=l-1; j>=1; j--) p1[j] = lstoi(ex[j]);
    free(ex);
  }
  else
  {
    y = gerepileupto(av, nfsqff(nf,A,0));
    l = lg(y);
    p1 = cgetg(l, t_COL); for (j=l-1; j>=1; j--) p1[j] = un;
  }
  if (DEBUGLEVEL>3)
    fprintferr("number of factor(s) found: %ld\n", lg(y)-1);
  rep[1] = (long)y;
  rep[2] = (long)p1; return sort_factor(rep, cmp_pol);
}

/* Assume n >= 1, return bin, bin[k+1] = binomial(n, k) */
GEN
vecbinome(long n)
{
  long d = (n + 1)/2, k;
  GEN bin = cgetg(n+2, t_VEC), *C;
  C = (GEN*)(bin + 1); /* C[k] = binomial(n, k) */
  C[0] = gun;
  for (k=1; k <= d; k++)
  {
    gpmem_t av = avma;  
    C[k] = gerepileuptoint(av, diviiexact(mulsi(n-k+1, C[k-1]), stoi(k)));
  }
  for (   ; k <= n; k++) C[k] = C[n - k];
  return bin;
}

/* return a bound for T_2(P), P | polbase in C[X]
 * NB: Mignotte bound: A | S ==>
 *  |a_i| <= binom(d-1, i-1) || S ||_2 + binom(d-1, i) lc(S)
 *
 * Apply to sigma(S) for all embeddings sigma, then take the L_2 norm over
 * sigma, then take the sup over i.
 **/
static GEN
nf_factor_bound(GEN nf, GEN polbase)
{
  gpmem_t av = avma;
  GEN G = gmael(nf,5,2), lS = leading_term(polbase); /* t_INT */
  GEN p1, C, N2, matGS, binlS, bin;
  long prec, i, j, d = degpol(polbase), n = degpol(nf[1]), r1 = nf_get_r1(nf);

  if (typ(lS) == t_COL) lS = (GEN)lS[1];
  binlS = bin = vecbinome(d-1);
  if (!gcmp1(lS)) binlS = gmul(lS, bin);

  matGS = cgetg(d+2, t_MAT);
  N2 = cgetg(n+1, t_VEC);
  prec = gprecision(G);
  for (;;)
  {
    nffp_t F;

    for (j=0; j<=d; j++)
      matGS[j+1] = lmul(G, (GEN)polbase[j+2]);
    matGS = gtrans_i(matGS);
    for (j=1; j <= r1; j++) /* N2[j] = || sigma_j(S) ||_2 */
    {
      N2[j] = lsqrt( QuickNormL2((GEN)matGS[j], DEFAULTPREC), DEFAULTPREC );
      if (lg(N2[j]) < DEFAULTPREC) goto PRECPB;
    }
    for (   ; j <= n; j+=2)
    {
      GEN q1 = QuickNormL2((GEN)matGS[j  ], DEFAULTPREC);
      GEN q2 = QuickNormL2((GEN)matGS[j+1], DEFAULTPREC);
      p1 = gmul2n(mpadd(q1, q2), -1);
      N2[j] = N2[j+1] = lsqrt( p1, DEFAULTPREC );
      if (lg(N2[j]) < DEFAULTPREC) goto PRECPB;
    }
    if (j > n) break; /* done */
PRECPB:
    prec = (prec<<1)-2;
    remake_GM(nf, &F, prec); G = F.G;
    if (DEBUGLEVEL>1) err(warnprec, "nf_factor_bound", prec);
    matGS = gtrans_i(matGS);
  }

  /* Take sup over 0 <= i <= d of
   * sum_sigma | binom(d-1, i-1) ||sigma(S)||_2 + binom(d-1,i) lc(S) |^2 */

  /* i = 0: n lc(S)^2 */
  C = mulsi(n, sqri(lS));
  /* i = d: sum_sigma ||sigma(S)||_2^2 */
  p1 = gnorml2(N2); if (gcmp(C, p1) < 0) C = p1;
  for (i = 1; i <= d-1; i++ )
  {
    GEN s = gzero;
    for (j = 1; j <= n; j++)
    {
      p1 = mpadd( mpmul((GEN)bin[i], (GEN)N2[j]), (GEN)binlS[i+1] );
      s = mpadd(s, gsqr(p1));
    }
    if (gcmp(C, s) < 0) C = s;
  }
  return gerepileupto(av, C);
}

static long
ZXY_get_prec(GEN P)
{
  long i, j, z, prec = 0;
  for (i=2; i<lgef(P); i++)
  {
    GEN p = (GEN)P[i];
    if (typ(p) == t_INT)
    {
      z = lgefint(p);
      if (z > prec) prec = z;
    }
    else
    {
      for (j=2; j<lgef(p); j++)
      {
        z = lgefint(p[j]);
        if (z > prec) prec = z;
      }
    }
  }
  return prec + 1;
}

long
ZM_get_prec(GEN x)
{
  long i, j, l, k = 2, lx = lg(x);

  for (j=1; j<lx; j++)
  {
    GEN c = (GEN)x[j];
    for (i=1; i<lx; i++) { l = lgefint(c[i]); if (l > k) k = l; }
  }
  return k;
}
long
ZX_get_prec(GEN x)
{
  long j, l, k = 2, lx = lgef(x);

  for (j=2; j<lx; j++)
  {
    l = lgefint(x[j]); if (l > k) k = l;
  }
  return k;
}

static GEN
complex_bound(GEN P)
{
  return gmul(max_modulus(P, 0.01), dbltor(1.0101)); /* exp(0.01) = 1.0100 */
}

/* return Bs: if r a root of sigma_i(P), |r| < Bs[i] */
static GEN
nf_root_bounds(GEN P, GEN T)
{
  long lR, i, j, l, prec;
  GEN Ps, R, V, nf;

  if (isrational(P)) return complex_bound(P);

  T = get_nfpol(T, &nf);

  prec = ZXY_get_prec(P);
  l = lgef(P);
  if (nf && nfgetprec(nf) >= prec)
    R = (GEN)nf[6];
  else
    R = roots(T, prec);
  lR = lg(R);
  V = cgetg(lR, t_VEC);
  Ps = cgetg(l, t_POL); /* sigma (P) */
  Ps[1] = P[1];
  for (j=1; j<lg(R); j++)
  {
    GEN r = (GEN)R[j];
    for (i=2; i<l; i++) Ps[i] = (long)poleval((GEN)P[i], r);
    V[j] = (long)complex_bound(Ps);
  }
  return V;
}

/* return B such that if x in O_K, K = Z[X]/(T), then the L2-norm of the
 * coordinates of the numerator of x [on the power, resp. integral, basis if T
 * is a polynomial, resp. an nf] is  <= B T_2(x)
 * *ptden = multiplicative bound for denom(x) */
static GEN
L2_bound(GEN T, GEN tozk, GEN *ptden)
{
  GEN nf, M, L, prep, den, u;
  long prec;

  T = get_nfpol(T, &nf);
  u = NULL; /* gcc -Wall */

  prec = ZX_get_prec(T) + ZM_get_prec(tozk);
  den = nf? gun: NULL;
  den = initgaloisborne(T, den, prec, &L, &prep, NULL);
  M = vandermondeinverse(L, gmul(T, realun(prec)), den, prep);
  if (nf) M = gmul(tozk, M);
  if (gcmp1(den)) den = NULL;
  *ptden = den;
  return QuickNormL2(M, DEFAULTPREC);
}

/* || L ||_p^p in dimension n (L may be a scalar) */
static GEN
normlp(GEN L, long p, long n)
{
  long i,l, t = typ(L);
  GEN z;

  if (!is_vec_t(t)) return gmulsg(n, gpowgs(L, p));

  l = lg(L); z = gzero;
  /* assert(n == l-1); */
  for (i=1; i<l; i++)
    z = gadd(z, gpowgs((GEN)L[i], p));
  return z;
}

/* S = S0 + qS1, P = P0 + qP1 (Euclidean div. by q integer). For a true
 * factor (vS, vP), we have:
 *    | S vS + P vP |^2 < Btra
 * This implies | S1 vS + P1 vP |^2 < Blow, assuming q > sqrt(Btra).
 * d = dimension of low part (= [nf:Q])
 * BvS = bound for |vS|^2
 * */
static double
get_Blow(long BvS, long d)
{
  double sqrtBvS = sqrt((double)BvS);
  double t = 1. + 0.5*sqrtBvS + 0.5 * sqrt((double)d) * (sqrtBvS + 1);
  return t * t;
}

/* Naive recombination of modular factors: combine up to maxK modular
 * factors, degree <= klim and divisible by hint
 *
 * target = polynomial we want to factor
 * famod = array of modular factors.  Product should be congruent to
 * target/lc(target) modulo p^a
 * For true factors: S1,S2 <= p^b, with b <= a and p^(b-a) < 2^31 */
static GEN
nfcmbf(nfcmbf_t *T, GEN p, long a, long maxK, long klim)
{
  long Sbound;
  GEN pol = T->pol, nf = T->nf, famod = T->fact;
  GEN dn = T->dn, bound = T->bound;
  GEN den = T->L->den, deno2 = shifti(den, -1);
  GEN nfpol = (GEN)nf[1];
  long K = 1, cnt = 1, i,j,k, curdeg, lfamod = lg(famod)-1, dnf = degpol(nfpol);
  GEN lc, lcpol, h1 = NULL; /* gcc -Wall */
  GEN pa = gpowgs(p,a), pas2 = shifti(pa,-1);

  GEN hS1    = cgetg(lfamod+1, t_VEC);
  GEN hS2    = cgetg(lfamod+1, t_VEC);
  GEN trace1   = cgetg(lfamod+1, t_MAT);
  GEN trace2   = cgetg(lfamod+1, t_MAT);
  GEN ind      = cgetg(lfamod+1, t_VECSMALL);
  GEN degpol   = cgetg(lfamod+1, t_VECSMALL);
  GEN degsofar = cgetg(lfamod+1, t_VECSMALL);
  GEN listmod  = cgetg(lfamod+1, t_COL);
  GEN fa       = cgetg(lfamod+1, t_COL);
  GEN res = cgetg(3, t_VEC);
  const double Blow = get_Blow(lfamod, dnf);

  if (maxK < 0) maxK = lfamod-1;
  (void)dn;

  lc = absi(leading_term(pol));
  if (gcmp1(lc)) lc = NULL;
  lcpol = lc? gmul(lc,pol): pol;

  {
    GEN T1,T2, q, qgood, lc2 = lc? sqri(lc): NULL;
    long e, e1, e2;

    q = ceil_safe(mpsqrt(T->BS_2));
    for (i=1; i <= lfamod; i++)
    {
      GEN P = (GEN)famod[i];
      long d = degpol(P);

      degpol[i] = d; P += 2;
      T1 = (GEN)P[d-1];/* = - S_1 */
      T2 = sqri(T1);
      if (d > 1) T2 = subii(T2, shifti((GEN)P[d-2],1));
      T2 = modii(T2, pa); /* = S_2 Newton sum */
      if (lc)
      {
        T1 = modii(mulii(lc, T1), pa);
        T2 = modii(mulii(lc2,T2), pa);
      }
      trace1[i] = (long)nf_bestlift(T1, NULL, T->L);
      trace2[i] = (long)nf_bestlift(T2, NULL, T->L);
    }
    e1 = gexpo((GEN)trace1);
    e2 = gexpo((GEN)trace2); e = max(e1, e2);
    if (e < 0) /* trace1 = trace2 = 0 */
      trace1 = trace2 = NULL;
    else
    {
      qgood = shifti(gun, e2 - 32); /* single precision check */
      if (cmpii(qgood, q) > 0) q = qgood;
      T1 = trace1;
      T2 = trace2;
      trace1 = gdivround(T1, q); if (gcmp0(trace1)) trace1 = NULL;
      trace2 = gdivround(T2, q); if (gcmp0(trace2)) trace2 = NULL;
      if (trace1) hS1 = gsub(T1, gmul(T->L->prk, trace1));
      if (trace2) hS2 = gsub(T2, gmul(T->L->prk, trace2)); /* <= q/2 */
      h1 = gdivround(T->L->prk, q);
    }
  }
  degsofar[0] = 0; /* sentinel */

  /* ind runs through strictly increasing sequences of length K,
   * 1 <= ind[i] <= lfamod */
nextK:
  if (K > maxK || 2*K > lfamod) goto END;
  if (DEBUGLEVEL > 3)
    fprintferr("\n### K = %d, %Z combinations\n", K,binome(stoi(lfamod), K));
  setlg(ind, K+1); ind[1] = 1;
  Sbound = ((K+1)>>1);
  i = 1; curdeg = degpol[ind[1]];
  for(;;)
  { /* try all combinations of K factors */
    for (j = i; j < K; j++)
    {
      degsofar[j] = curdeg;
      ind[j+1] = ind[j]+1; curdeg += degpol[ind[j+1]];
    }
    if (curdeg <= klim && curdeg % T->hint == 0) /* trial divide */
    {
      GEN s, t, y, q, list;
      gpmem_t av;

      av = avma;
      /* d - 1 test */
      if (trace1)
      {
        s = (GEN)hS1[ind[1]];
        t = (GEN)trace1[ind[1]];
        for (i=2; i<=K; i++)
        {
          t = gadd(t, (GEN)trace1[ind[i]]);
          s = gadd(s, (GEN)hS1[ind[i]]);
          for (j=1; j<=dnf; j++)
            if (absi_cmp((GEN)s[j], deno2) > 0)
            {
              t = gsub(t, (GEN)h1[j]);
              s[j] = lsubii((GEN)s[j], den);
            }
        }
        if (rtodbl(QuickNormL2(t,DEFAULTPREC)) > Blow)
        {
          if (DEBUGLEVEL>6) fprintferr(".");
          avma = av; goto NEXT;
        }
      }
      /* d - 2 test */
      if (trace2)
      {
        s = (GEN)hS2[ind[1]];
        t = (GEN)trace2[ind[1]];
        for (i=2; i<=K; i++)
        {
          t = gadd(t, (GEN)trace2[ind[i]]);
          s = gadd(s, (GEN)hS2[ind[i]]);
          for (j=1; j<=dnf; j++)
            if (absi_cmp((GEN)s[j], deno2) > 0)
            {
              t = gsub(t, (GEN)h1[j]);
              s[j] = lsubii((GEN)s[j], den);
            }
        }
        if (rtodbl(QuickNormL2(t,DEFAULTPREC)) > Blow)
        {
          if (DEBUGLEVEL>3) fprintferr("|");
          avma = av; goto NEXT;
        }
      }
      avma = av;
      y = lc; /* full computation */
      for (i=1; i<=K; i++)
      {
        GEN q = (GEN)famod[ind[i]];
        if (y) q = gmul(y, q);
        y = centermod_i(q, pa, pas2);
      }
      y = nf_pol_lift(y, bound, T);
      if (!y)
      {
        if (DEBUGLEVEL>3) fprintferr("@");
        avma = av; goto NEXT;
      }
      /* try out the new combination: y is the candidate factor */
      q = RXQX_divrem(lcpol,y, nfpol, ONLY_DIVIDES);
      if (!q)
      {
        if (DEBUGLEVEL>3) fprintferr("*");
        avma = av; goto NEXT;
      }

      /* found a factor */
      list = cgetg(K+1, t_VEC);
      listmod[cnt] = (long)list;
      for (i=1; i<=K; i++) list[i] = famod[ind[i]];

      y = primpart(y);
      fa[cnt++] = (long)QXQ_normalize(y, nfpol);
      /* fix up pol */
      pol = q;
      if (lc) pol = primpart(pol);
      for (i=j=k=1; i <= lfamod; i++)
      { /* remove used factors */
        if (j <= K && i == ind[j]) j++;
        else
        {
          famod[k] = famod[i];
          if (trace1) { trace1[k] = trace1[i]; hS1[k] = hS2[i]; }
          if (trace2) { trace2[k] = trace2[i]; hS2[k] = hS2[i]; }
          degpol[k] = degpol[i]; k++;
        }
      }
      lfamod -= K;
      if (lfamod < 2*K) goto END;
      i = 1; curdeg = degpol[ind[1]];
      if (lc) lc = absi(leading_term(pol));
      lcpol = lc? gmul(lc,pol): pol;
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
  if (degpol(pol) > 0)
  { /* leftover factor */
    if (signe(leading_term(pol)) < 0) pol = gneg_i(pol);

    if (lc && lfamod < 2*K) pol = QXQ_normalize(primpart(pol), nfpol);
    setlg(famod, lfamod+1);
    listmod[cnt] = (long)dummycopy(famod);
    fa[cnt++] = (long)pol;
  }
  if (DEBUGLEVEL>6) fprintferr("\n");
  setlg(listmod, cnt); setlg(fa, cnt);
  res[1] = (long)fa;
  res[2] = (long)listmod; return res;
}

static GEN
nf_check_factors(nfcmbf_t *T, GEN P, GEN M_L, GEN famod, GEN pa)
{
  GEN nf = T->nf, bound = T->bound;
  GEN nfT = (GEN)nf[1];
  long i, j, r, n0;
  GEN pol = P, lcpol, lc, list, piv, y, pas2;

  piv = special_pivot(M_L);
  if (!piv) return NULL;
  if (DEBUGLEVEL>3) fprintferr("special_pivot output:\n%Z\n",piv);

  pas2 = shifti(pa,-1);
  r  = lg(piv)-1;
  n0 = lg(piv[1])-1;
  list = cgetg(r+1, t_COL);
  lc = absi(leading_term(pol));
  if (is_pm1(lc)) lc = NULL;
  lcpol = lc? gmul(lc, pol): pol;
  for (i=1; i<r; i++)
  {
    GEN c = (GEN)piv[i];
    if (DEBUGLEVEL) fprintferr("nf_LLL_cmbf: checking factor %ld\n",i);

    y = lc;
    for (j=1; j<=n0; j++)
      if (signe(c[j]))
      {
        GEN q = (GEN)famod[j];
        if (y) q = gmul(y, q);
        y = centermod_i(q, pa, pas2);
      }
    y = nf_pol_lift(y, bound, T);
    if (!y) return NULL;

    /* y is the candidate factor */
    pol = RXQX_divrem(lcpol,y,nfT, ONLY_DIVIDES);
    if (!pol) return NULL;

    y = primpart(y);
    if (lc)
    {
      pol = primpart(pol);
      lc = absi(leading_term(pol));
    }
    lcpol = lc? gmul(lc, pol): pol;
    list[i] = (long)QXQ_normalize(y, nfT);
  }
  y = primpart(pol);
  list[i] = (long)QXQ_normalize(y, nfT); return list;
}

static GEN
nf_to_Zp(GEN x, GEN pa, GEN pas2, GEN ffproj)
{
  return centermodii(gmul(ffproj, x), pa, pas2);
}

/* assume lc(pol) != 0 mod prh. Reduce P to Zp[X] mod p^a */
static GEN
ZpX(GEN P, GEN pa, GEN ffproj)
{
  long i, l;
  GEN z, pas2 = shifti(pa,-1);

  if (typ(P)!=t_POL) return nf_to_Zp(P,pa,pas2,ffproj);
  l = lgef(P);
  z = cgetg(l,t_POL); z[1] = P[1];
  for (i=2; i<l; i++) z[i] = (long)nf_to_Zp((GEN)P[i],pa,pas2,ffproj);
  return normalizepol(z);
}

/* We want to be able to reconstruct x, |x|^2 < C, from x mod pr^k
 * We want B := min B_i >= C. Let alpha the LLL parameter,
 * y = 1/(alpha-1/4) > 4/3, the theoretical guaranteed bound follows from
 *    (Npr)^(2k/n) = det(L)^(2/n) <= 1/n sum B_i
 *                                <= 1/n B sum y^i
 *                                <= 1/n B y^(n-1) / (y-1)
 *
 *  Hence log(B/n) >= 2k/n log(Npr) - (n-1)log(y) + log(y-1)
 *                 >= log(C/n), provided
 *   k >= [ log(C/n) + (n-1)log(y) - log(y-1) ] * n/(2log(Npr))
 */
static double
bestlift_bound(GEN C, long n, double alpha, GEN Npr)
{
  const double y = 1 / (alpha - 0.25); /* = 2 if alpha = 3/4 */
  double t;
  if (typ(C) != t_REAL) C = gmul(C, realun(DEFAULTPREC));
  setlg(C, DEFAULTPREC);
  t = rtodbl(mplog(divrs(C,n))) + (n-1) * log(y) - log(y-1);
  return ceil((t * n) / (2.* log(gtodouble(Npr))));
}

static void
bestlift_init(long a, GEN nf, GEN pr, GEN C, nflift_t *T)
{
  const int D = 4;
  const double alpha = ((double)D-1) / D; /* LLL parameter */
  gpmem_t av = avma;
  GEN prk, PRK, B, GSmin, pa;

  if (!a)  a = (long) bestlift_bound(C, degpol(nf[1]), alpha, idealnorm(nf,pr));

  for (;; avma = av, a<<=1)
  {
    if (DEBUGLEVEL>2) fprintferr("exponent: %ld\n",a);
    prk = idealpows(nf, pr, a);
    pa = gcoeff(prk,1,1);
    PRK = hnfmodid(prk, pa);

    PRK = lllint_i(PRK, D, 0, NULL, NULL, &B);
    GSmin = vecmin(GS_norms(B, DEFAULTPREC));
    if (gcmp(GSmin, C) >= 0) break;
  }
  if (DEBUGLEVEL>2) fprintferr("for this exponent, GSmin = %Z\n",GSmin);
  T->a = a;
  T->pa = T->den = pa;
  T->prk = PRK;
  T->iprk = ZM_inv(PRK, pa);
  T->GSmin= GSmin;
  T->ZpProj = dim1proj(prk); /* nf --> Zp */
}

/* assume pr has degree 1 */
static GEN
nf_LLL_cmbf(nfcmbf_t *T, GEN p, long a, long rec)
{
  nflift_t *L = T->L;
  GEN pa = L->pa, PRK = L->prk, PRKinv = L->iprk, GSmin = L->GSmin;

  GEN famod = T->fact, nf = T->nf, ZC = T->ZC, Br = T->Br;
  GEN Pbase = T->polbase, P = T->pol, dn = T->dn;
  GEN nfT = (GEN)nf[1];
  GEN Btra;
  long dnf = degpol(nfT), dP = degpol(P);

  double BitPerFactor = 0.5; /* nb bits / modular factor */
  long i, C, tmax, n0;
  GEN lP, Bnorm, Tra, T2, TT, CM_L, m, list, ZERO;
  double Blow;
  gpmem_t av, av2, lim;
  long ti_LLL = 0, ti_CF = 0;
  pari_timer ti;

  if (DEBUGLEVEL>2) (void)TIMER(&ti);

  lP = absi(leading_term(P));
  if (is_pm1(lP)) lP = NULL;

  n0 = lg(famod) - 1;
 /* Lattice: (S PRK), small vector (vS vP). To find a bound for the image,
  * write S = S1 q + S0, P = P1 q + P0
  * q(S1 vS + P1 vP) <= Blow for all (vS,vP) assoc. to true factors */
  Blow = get_Blow(n0, dnf);
  C = (long)ceil(sqrt(Blow/n0)) + 1; /* C^2 n0 ~ Blow */
  Bnorm = dbltor( n0 * C * C + Blow );
  ZERO = zeromat(n0, dnf);

  av = avma; lim = stack_lim(av, 1);
  TT = cgetg(n0+1, t_VEC);
  Tra  = cgetg(n0+1, t_MAT);
  for (i=1; i<=n0; i++) TT[i] = 0;
  CM_L = gscalsmat(C, n0);
  /* tmax = current number of traces used (and computed so far) */
  for(tmax = 0;; tmax++)
  {
    long b, bmin, bgood, delta, tnew = tmax + 1, r = lg(CM_L)-1;
    GEN M_L, q;
    pari_timer ti2;

    /* bound for f . S_k(genuine factor) = ZC * bound for T_2(S_tnew) */
    Btra = mulrr(ZC, mulsr(dP*dP, normlp(Br, 2*tnew, dnf)));
    bmin = logint(ceil_safe(mpsqrt(Btra)), gdeux, NULL);
    if (DEBUGLEVEL>2)
      fprintferr("LLL_cmbf: %ld potential factors (tmax = %ld, bmin = %ld)\n",
                 r, tmax, bmin);

    /* compute Newton sums (possibly relifting first) */
    if (gcmp(GSmin, Btra) < 0)
    {
      nflift_t L1;
      GEN polred;

      bestlift_init(a<<1, nf, T->pr, Btra, &L1);
      a      = L1.a;
      pa     = L1.pa;
      PRK    = L1.prk;
      PRKinv = L1.iprk;
      GSmin  = L1.GSmin;

      polred = ZpX(Pbase, pa, L1.ZpProj);
      famod = hensel_lift_fact(polred,famod,NULL,p,pa,a);
      for (i=1; i<=n0; i++) TT[i] = 0;
    }
    for (i=1; i<=n0; i++)
    {
      GEN p1, lPpow;
      GEN p2 = polsym_gen((GEN)famod[i], (GEN)TT[i], tnew, NULL, pa);
      TT[i] = (long)p2;
      p1 = (GEN)p2[tnew+1];
      /* make Newton sums integral */
      if (lP)
      {
        lPpow = gpowgs(lP, tnew);
        p1 = mulii(p1, lPpow); /* assume pr has degree 1 */
      }
      if (dn) p1 = mulii(p1,dn);
      if (dn || lP) p1 = modii(p1, pa);
      Tra[i] = (long)gscalcol(p1, dnf); /* S_tnew(famod) */
    }

    /* compute truncation parameter */
    if (DEBUGLEVEL>2) TIMERstart(&ti2);
    av2 = avma;
    delta = 0;
    b = 0; /* -Wall */
AGAIN:
    M_L = gdivexact(CM_L, stoi(C));
    T2 = centermod( gmul(Tra, M_L), pa );
    T2 = gsub(T2, gmul(PRK, gdivround(gmul(PRKinv, T2), pa)));

    if (!delta)
    { /* initialize lattice, using few p-adic digits for traces */
      bgood = (long)(gexpo(T2) - BitPerFactor * r);
      b = max(bmin, bgood);
      delta = a - b;
      q = shifti(gun, b);
      m = concatsp( vconcat( CM_L, gdivround(T2, q) ),
                    vconcat( ZERO, gdivround(PRK,q) ) );
      /*     [ C M_L   0  ]
       * m = [            ]   square matrix
       *     [  T2'   PRK ]   T2' = Tra * M_L  truncated
       */
    }
    else
    { /* add more p-adic digits and continue reduction */
      long b0 = gexpo(T2);
      if (b0 < b) b = b0;
      b = max(b-delta, bmin);
      if (b - delta/2 < bmin) b = bmin; /* near there. Go all the way */
      q = shifti(gun, b);
      m = vconcat( CM_L, gdivround(T2, q) );
    }
    if (DEBUGLEVEL>2)
      fprintferr("LLL_cmbf: b = %ld, r = %ld\n", b,lg(m)-1);
    CM_L = LLL_check_progress(Bnorm, n0, m, b == bmin, /*dbg:*/ &ti, &ti_LLL);
    if (!CM_L) { list = _col(P); break; }
    i = lg(CM_L) - 1;
    if (b > bmin) 
    {
      CM_L = gerepilecopy(av2, CM_L);
      goto AGAIN;
    }
    if (DEBUGLEVEL>2) msgTIMER(&ti2, "for this trace");

    if (i <= r && i*rec < n0)
    {
      if (DEBUGLEVEL>2) (void)TIMER(&ti);
      list = nf_check_factors(T, P, M_L, famod, pa);
      if (DEBUGLEVEL>2) ti_CF += TIMER(&ti);
      if (list) break;
      CM_L = gerepilecopy(av2, CM_L);
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"nf_LLL_cmbf");
      gerepileall(av, 8, &CM_L,&TT,&Tra,&famod,&pa,&GSmin,&PRK,&PRKinv);
    }
  }
  if (DEBUGLEVEL>2)
    fprintferr("* Time LLL: %ld\n* Time Check Factor: %ld\n",ti_LLL,ti_CF);
  return list;
}

static GEN
nf_combine_factors(nfcmbf_t *T, GEN polred, GEN p, long a, long klim)
{
  GEN z, res, L, listmod, famod = T->fact, nf = T->nf;
  long i, m, l, maxK = 3, nft = lg(famod)-1;

  T->fact = hensel_lift_fact(polred,famod,NULL,p,T->pa,a);
  if (nft < 11) maxK = -1; /* few modular factors: try all posibilities */
  if (DEBUGLEVEL>3) msgtimer("Hensel lift");

  /* FIXME: neither nfcmbf nor LLL_cmbf can handle the non-nf case */

  T->res      = cgetg(nft+1,t_VEC);
  L = nfcmbf(T, p, a, maxK, klim);

  res     = (GEN)L[1];
  listmod = (GEN)L[2]; l = lg(listmod)-1;
  famod = (GEN)listmod[l];
  if (maxK >= 0 && lg(famod)-1 > 2*maxK)
  {
    if (l > 1) T->polbase = unifpol(nf, (GEN)res[l], 0);
    L = nf_LLL_cmbf(T, p, a, maxK);
    /* remove last elt, possibly unfactored. Add all new ones. */
    setlg(res, l); res = concatsp(res, L);
  }
  if (DEBUGLEVEL>3) msgtimer("computation of the factors");

  m = lg(res); z = cgetg(m, t_VEC);
  for (i=1;i<m; i++) z[i] = (long)unifpol(nf,(GEN)res[i],1);
  return z;
}

/* return the factorization of the square-free polynomial x.
   The coeff of x are in Z_nf and its leading term is a rational integer.
   deg(x) > 1
   If fl = 1,return only the roots of x in nf */
static GEN
nfsqff(GEN nf, GEN pol, long fl)
{
  long i, a, m, n, nbf, ct, dpol = degpol(pol);
  gpmem_t av = avma;
  GEN pr, C0, C, dk, bad, polbase, pa;
  GEN N2, rep, p, ap, polmod, polred, lt, nfpol;
  byteptr pt=diffptr;
  nfcmbf_t T;
  nflift_t L;

  if (DEBUGLEVEL>3) msgtimer("square-free");
  nfpol = (GEN)nf[1];
  polbase = unifpol(nf,pol,0);
  polmod  = unifpol(nf,pol,1);
  pol = simplify_i(lift(polmod));
  lt  = (GEN)leading_term(polbase)[1]; /* t_INT */

  dk = absi((GEN)nf[3]);
  bad = mulii(mulii(dk,(GEN)nf[4]), lt);
  n = degpol(nfpol);

  p = polred = pr = NULL; /* gcc -Wall */
  nbf = 0; ap = NULL;
  for (ct = 5;;)
  {
    GEN apr = choose_prime(nf, bad, &ap, &pt);
    GEN modpr = zkmodprinit(nf, apr);
    long anbf;

    polred = modprX(polbase, nf, modpr);
    if (!FpX_is_squarefree(polred,ap)) continue;

    anbf = fl? FpX_nbroots(polred,ap): FpX_nbfact(polred,ap);
    if (!nbf || anbf < nbf)
    {
      nbf = anbf; pr = apr; p = ap;
      if (DEBUGLEVEL>3)
        fprintferr("%3ld %s at prime ideal above %Z\n",
                   nbf, fl?"roots": "factors", p);
      if (nbf <= 1)
      {
        if (!fl) return gerepilecopy(av, _vec(polmod)); /* irreducible */
        if (!nbf) return cgetg(1,t_VEC); /* no root */
      }
    }
    if (--ct <= 0) break;
  }
  if (DEBUGLEVEL>3) {
    msgtimer("choice of a prime ideal");
    fprintferr("Prime ideal chosen: %Z\n", pr);
  }

  L.tozk = (GEN)nf[8];
  L.topow= (GEN)nf[7];
  T.ZC = L2_bound(nf, L.tozk, &(T.dn));
  T.Br = gmul(lt, nf_root_bounds(pol, nf));

  if (fl) C0 = normlp(T.Br, 2, n);
  else    C0 = nf_factor_bound(nf, polbase); /* bound for T_2(Q_i), Q | P */
  C = mulrr(T.ZC, C0); /* bound for |Q_i|^2 in Z^n on chosen Z-basis */
  T.bound = C;

  N2 = mulsr(dpol*dpol, normlp(T.Br, 4, n)); /* bound for T_2(lt * S_2) */
  T.BS_2 = mulrr(T.ZC, N2); /* bound for |S_2|^2 on chosen Z-basis */

  if (DEBUGLEVEL>2) {
    msgtimer("bound computation");
    fprintferr("  1) T_2 bound for %s: %Z\n", fl?"root":"factor", C0);
    fprintferr("  2) Conversion from T_2 --> | |^2 bound : %Z\n", T.ZC);
    fprintferr("  3) Final bound: %Z\n", C);
  }

  if (fl)
    (void)logint(C, p, &pa);
  else
  { /* overlift needed for d-1/d-2 tests? */
    GEN pb; long b; /* junk */
    if (cmbf_precs(p, C, T.BS_2, &a, &b, &pa, &pb))
    { /* Rare */
      if (DEBUGLEVEL) err(warner,"nffactor: overlift for d-1/d-2 test");
      C = itor(pa, DEFAULTPREC);
    }
  }

  bestlift_init(0, nf, pr, C, &L);
  T.pr = pr;
  T.L  = &L;

  /* polred is monic */
  pa = L.pa;
  polred = ZpX(gmul(mpinvmod(lt,pa), polbase), pa, L.ZpProj);

  if (fl)
  { /* roots only */
    long x_r[] = { evaltyp(t_POL)|_evallg(4), 0,0,0 };
    rep = rootpadicfast(polred, p, L.a);
    x_r[1] = evalsigne(1) | evalvarn(varn(pol)) | evallgef(4);
    x_r[3] = un;
    for (m=1,i=1; i<lg(rep); i++)
    {
      GEN q, r = (GEN)rep[i];

      r = nf_bestlift_to_pol(gmul(lt,r), NULL, &L);
      r = gdiv(r,lt);
      x_r[2] = lneg(r); /* check P(r) == 0 */
      q = RXQX_divrem(pol, x_r, nfpol, ONLY_DIVIDES);
      if (q) { pol = q; rep[m++] = (long)r; }
    }
    rep[0] = evaltyp(t_VEC) | evallg(m);
    return gerepilecopy(av, rep);
  }

  T.polbase = polbase;
  T.pol   = pol;
  T.nf    = nf;
  T.fact  = (GEN)factmod0(polred,p)[1];
  T.hint  = 1; /* useless */

  rep = nf_combine_factors(&T, polred, p, L.a, dpol-1);
  return gerepileupto(av, rep);
}

/* return the characteristic polynomial of alpha over nf, where alpha
   is an element of the algebra nf[X]/(T) given as a polynomial in X */
GEN
rnfcharpoly(GEN nf,GEN T,GEN alpha,int v)
{
  long vnf, vT, lT;
  gpmem_t av = avma;
  GEN p1;

  nf=checknf(nf); vnf = varn(nf[1]);
  if (v<0) v = 0;
  T = fix_relative_pol(nf,T,1);
  if (typ(alpha) == t_POLMOD) alpha = lift_to_pol(alpha);
  lT = lgef(T);
  if (typ(alpha) != t_POL || varn(alpha) == vnf)
    return gerepileupto(av, gpowgs(gsub(polx[v], alpha), lT - 3));
  vT = varn(T);
  if (varn(alpha) != vT || v >= vnf)
    err(talker,"incorrect variables in rnfcharpoly");
  if (lgef(alpha) >= lT) alpha = gmod(alpha,T);
  if (lT <= 4)
    return gerepileupto(av, gsub(polx[v], alpha));
  p1 = caract2(unifpol(nf,T,1), unifpol(nf,alpha,1), v);
  return gerepileupto(av, unifpol(nf,p1,1));
}
