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

extern GEN lllint_fp_ip(GEN x, long D);
extern long FqX_split_deg1(GEN *pz, GEN u, GEN q, GEN T, GEN p);
extern GEN FqX_split_roots(GEN z, GEN T, GEN p, GEN pol);
extern GEN FqX_split_all(GEN z, GEN T, GEN p);
extern long FqX_split_by_degree(GEN *pz, GEN u, GEN q, GEN T, GEN p);
extern long FpX_split_berlekamp(GEN *t, GEN p);
extern GEN get_proj_modT(GEN basis, GEN T, GEN p);
extern void init_dalloc();
extern double *dalloc(size_t n);
extern GEN sqred1_from_QR(GEN x, long prec);
extern GEN gmul_mati_smallvec(GEN x, GEN y);
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
extern GEN LLL_check_progress(GEN Bnorm, long n0, GEN m, int final, long *ti_LLL);
extern void remake_GM(GEN nf, nffp_t *F, long prec);
#define RXQX_div(x,y,T) RXQX_divrem((x),(y),(T),NULL)
#define RXQX_rem(x,y,T) RXQX_divrem((x),(y),(T),ONLY_REM)
#define FpX_rem(x,y,p) FpX_divres((x),(y),(p),ONLY_REM)
#define FqX_div(x,y,T,p) FpXQX_divres((x),(y),(T),(p),NULL)

static GEN nfsqff(GEN nf,GEN pol,long fl);

/* FIXME: neither nfcmbf nor LLL_cmbf can handle the non-nf case */
/* for nf_bestlift: reconstruction of algebraic integers known mod \wp^k */
typedef struct {
  long k;    /* input known mod \wp^k */
  GEN p, pk;    /* p^k */
  GEN den;   /* denom(prk^-1) = p^k [ assume pr unramified ] */
  GEN prk;   /* |.|^2 LLL-reduced basis (b_i) of \wp^k  (NOT T2-reduced) */
  GEN prkHNF;/* HNF basis of \wp^k */
  GEN iprk;  /* den * prk^-1 */
  GEN GSmin; /* min |b_i^*|^2 */

  GEN Tp; /* Tpk mod p */
  GEN Tpk;
  GEN ZqProj;/* projector to Zp / \wp^k = Z/p^k[X] / Tpk */

  GEN tozk;
  GEN topow;
  GEN topowden; /* topow x / topowden = basistoalg(x) */
} nflift_t;

typedef struct /* for use in nfsqff */
{
  nflift_t *L;
  GEN nf;
  GEN pol, polbase; 
  GEN fact; 
  GEN pr; 
  GEN Br, bound, ZC, BS_2;
  GEN dn;
  long hint;
} nfcmbf_t;

GEN
RXQX_mul(GEN x, GEN y, GEN T)
{
  return RXQX_red(gmul(x,y), T);
}

static GEN
unifpol0(GEN nf,GEN x,long flag)
{
  switch(typ(x))
  {
    case t_INT: case t_FRAC: case t_FRACN:
      return gcopy(x);

    case t_POLMOD:
      x = (GEN)x[2]; /* fall through */
      if (typ(x) != t_POL) return gcopy(x); /* scalar */
    case t_POL:
      if (!degpol(x)) return gcopy(constant_term(x));
      return (flag == t_COL)? algtobasis(nf, x): gmodulcp(x, (GEN)nf[1]);

    default: /* t_COL */
      return (flag == t_COL)? gcopy(x): basistoalg(nf, x);
  }
}

/* Let x be a polynomial with coefficients in Z or nf (vectors or polymods)
 * return the same polynomial with coefficients expressed:
 *  if flag=0: as vectors (on the integral basis).
 *  if flag=1: as polymods.
 */
GEN
unifpol(GEN nf, GEN x, long flag)
{
  if (typ(x)==t_POL && varn(x) < varn(nf[1]))
  {
    long i, d = lgef(x);
    GEN y = cgetg(d,t_POL); y[1] = x[1];
    for (i=2; i<d; i++) y[i] = (long)unifpol0(nf, (GEN)x[i], flag);
    return y;
  }
  return unifpol0(nf, (GEN)x, flag);
}

/* factorization of x modulo (T,p). Assume x already reduced */
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
  pari_sp av = avma;
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

extern GEN nfrootsQ(GEN x);

/* return the roots of pol in nf */
GEN
nfroots(GEN nf,GEN pol)
{
  pari_sp av = avma;
  GEN A,g, T;
  int d;

  if (!nf) return nfrootsQ(pol);

  nf = checknf(nf); T = (GEN)nf[1];
  if (typ(pol) != t_POL) err(notpoler,"nfroots");
  if (varn(pol) >= varn(T))
    err(talker,"polynomial variable must have highest priority in nfroots");
  d = degpol(pol);
  if (d == 0) return cgetg(1,t_VEC);
  if (d == 1)
  {
    A = gneg_i(gdiv((GEN)pol[2],(GEN)pol[3]));
    return gerepilecopy(av, _vec( basistoalg(nf,A) ));
  }
  A = fix_relative_pol(nf,pol,0);
  A = Q_primpart( lift_intern(A) );
  if (DEBUGLEVEL>3) fprintferr("test if polynomial is square-free\n");
  g = nfgcd(A, derivpol(A), T, (GEN)nf[4]);

  if (degpol(g))
  { /* not squarefree */
    g = QXQ_normalize(g, T);
    A = RXQX_div(A,g,T);
  }
  A = QXQ_normalize(A, T);
  A = Q_primpart(A);
  A = nfsqff(nf,A,1);
  return gerepileupto(av, gen_sort(A, 0, cmp_pol));
}

int
nfissplit(GEN nf, GEN x)
{
  pari_sp av = avma;
  long l;
  if (typ(x) != t_POL) err(typeer, "nfissplit");
  l = lg(nfsqff(checknf(nf), x, 2));
  avma = av; return l != 1;
}

/* nf = K[y] / (P). Galois over K ? */
int
nfisgalois(GEN nf, GEN P)
{
  if (typ(P) != t_POL) err(typeer, "nfissplit");
  return degpol(P) <= 2 || nfissplit(nf, P);
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
    for (i=1; i<l; i++) u[i] = (long)diviiround((GEN)u[i], T->den);
  }
  else
  {
    u = gmul(elt, (GEN)T->iprk[1]);
    for (i=1; i<l; i++) u[i] = (long)diviiround((GEN)u[i], T->den);
    elt = gscalcol(elt, l-1);
  }
  u = gsub(elt, gmul(T->prk, u));
  if (bound && gcmp(QuickNormL2(u,DEFAULTPREC), bound) > 0) u = NULL;
  return u;
}

/* Warning: return T->topowden * (best lift) */
static GEN
nf_bestlift_to_pol(GEN elt, GEN bound, nflift_t *T)
{
  GEN u = nf_bestlift(elt,bound,T);
  if (!u) return NULL;
  return gmul(T->topow, u);
}

/* return the T->powden * (lift of pol with coefficients of T2-norm <= C)
 * if it exists */
static GEN
nf_pol_lift(GEN pol, GEN bound, nfcmbf_t *T)
{
  long i, l = lgef(pol);
  GEN x = cgetg(l,t_POL);

  x[1] = pol[1];
  for (i=2; i<l; i++)
  {
    x[i] = (long)nf_bestlift_to_pol((GEN)pol[i], bound, T->L);
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
  pari_sp av;
  pari_timer ti;

  if (DEBUGLEVEL>2) { TIMERstart(&ti); fprintferr("\nEntering nffactor:\n"); }
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
  if (degpol(nf[1]) == 1)
    return gerepileupto(av, factpol(simplify(pol), 0));

  A = Q_primpart( lift_intern(A) );
  g = nfgcd(A, derivpol(A), T, (GEN)nf[4]);

  A = QXQ_normalize(A, T);
  A = Q_primpart(A);
  if (DEBUGLEVEL>2) msgTIMER(&ti, "squarefree test");

  if (degpol(g))
  { /* not squarefree */
    pari_sp av1;
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

/* assume x scalar or t_COL */
static GEN
arch_for_T2(GEN G, GEN x)
{
  return (typ(x) == t_COL)? gmul(G,x): gmul((GEN)G[1],x);
}

/* return a bound for T_2(P), P | polbase in C[X]
 * NB: Mignotte bound: A | S ==>
 *  |a_i| <= binom(d-1, i-1) || S ||_2 + binom(d-1, i) lc(S)
 *
 * Apply to sigma(S) for all embeddings sigma, then take the L_2 norm over
 * sigma, then take the sup over i.
 **/
static GEN
nf_Mignotte_bound(GEN nf, GEN polbase)
{
  GEN G = gmael(nf,5,2), lS = leading_term(polbase); /* t_INT */
  GEN p1, C, N2, matGS, binlS, bin;
  long prec, i, j, d = degpol(polbase), n = degpol(nf[1]), r1 = nf_get_r1(nf);

  binlS = bin = vecbinome(d-1);
  if (!gcmp1(lS)) binlS = gmul(lS, bin);

  N2 = cgetg(n+1, t_VEC);
  prec = gprecision(G);
  for (;;)
  {
    nffp_t F;

    matGS = cgetg(d+2, t_MAT);
    for (j=0; j<=d; j++) matGS[j+1] = (long)arch_for_T2(G, (GEN)polbase[j+2]);
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
  }

  /* Take sup over 0 <= i <= d of
   * sum_sigma | binom(d-1, i-1) ||sigma(S)||_2 + binom(d-1,i) lc(S) |^2 */

  /* i = 0: n lc(S)^2 */
  C = mulsi(n, sqri(lS));
  /* i = d: sum_sigma ||sigma(S)||_2^2 */
  p1 = gnorml2(N2); if (gcmp(C, p1) < 0) C = p1;
  for (i = 1; i < d; i++)
  {
    GEN s = gzero;
    for (j = 1; j <= n; j++)
    {
      p1 = mpadd( mpmul((GEN)bin[i], (GEN)N2[j]), (GEN)binlS[i+1] );
      s = mpadd(s, gsqr(p1));
    }
    if (gcmp(C, s) < 0) C = s;
  }
  return C;
}

/* return a bound for T_2(P), P | polbase
 * max |b_i|^2 <= 3^{3/2 + d} / (4 \pi d) [P]_2,
 * where [P]_2 is Bombieri's 2-norm
 * Sum over conjugates
*/
static GEN
nf_Beauzamy_bound(GEN nf, GEN polbase)
{
  GEN lt,C,run,s, G = gmael(nf,5,2), POL, bin;
  long i,prec,precnf, d = degpol(polbase), n = degpol(nf[1]);

  precnf = gprecision(G);
  prec   = MEDDEFAULTPREC;
  bin = vecbinome(d);
  POL = polbase + 2;
  /* compute [POL]_2 */
  for (;;)
  {
    run= realun(prec);
    s = realzero(prec);
    for (i=0; i<=d; i++)
    {
      GEN p1 = gnorml2(arch_for_T2(G, gmul(run, (GEN)POL[i]))); /* T2(POL[i]) */
      if (!signe(p1)) continue;
      if (lg(p1) == 3) break;
      /* s += T2(POL[i]) / binomial(d,i) */
      s = addrr(s, gdiv(p1, (GEN)bin[i+1]));
    }
    if (i > d) break;

    prec = (prec<<1)-2;
    if (prec > precnf)
    {
      nffp_t F; remake_GM(nf, &F, prec); G = F.G;
      if (DEBUGLEVEL>1) err(warnprec, "nf_factor_bound", prec);
    }
  }
  lt = leading_term(polbase);
  s = gmul(s, mulis(sqri(lt), n));
  C = gpow(stoi(3), dbltor(1.5 + d), DEFAULTPREC); /* 3^{3/2 + d} */
  return gdiv(gmul(C, s), gmulsg(d, mppi(DEFAULTPREC)));
}

static GEN
nf_factor_bound(GEN nf, GEN polbase)
{
  pari_sp av = avma;
  GEN a = nf_Mignotte_bound(nf, polbase);
  GEN b = nf_Beauzamy_bound(nf, polbase);
  if (DEBUGLEVEL>2)
  {
    fprintferr("Mignotte bound: %Z\n",a);
    fprintferr("Beauzamy bound: %Z\n",b);
  }
  return gerepileupto(av, gmin(a, b));
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

/* S = S0 + tS1, P = P0 + tP1 (Euclidean div. by t integer). For a true
 * factor (vS, vP), we have:
 *    | S vS + P vP |^2 < Btra
 * This implies | S1 vS + P1 vP |^2 < Bhigh, assuming t > sqrt(Btra).
 * d = dimension of low part (= [nf:Q])
 * n0 = bound for |vS|^2
 * */
static double
get_Bhigh(long n0, long d)
{
  double sqrtd = sqrt((double)d);
  double z = n0*sqrtd + sqrtd/2 * (d * (n0+1));
  z = 1. + 0.5 * z; return z * z;
}

typedef struct {
  GEN d;
  GEN dPinvS;   /* d P^(-1) S   [ integral ] */
  double **PinvSdbl; /* P^(-1) S as double */
  GEN S1, P1;   /* S = S0 + S1 q, idem P */
} trace_data;

/* S1 * u - P1 * round(P^-1 S u). K non-zero coords in u given by ind */
static GEN
get_trace(GEN ind, trace_data *T)
{
  long i, j, l, K = lg(ind)-1;
  GEN z, s, v;

  s = (GEN)T->S1[ ind[1] ];
  if (K == 1) return s;

  /* compute s = S1 u */
  for (j=2; j<=K; j++) s = gadd(s, (GEN)T->S1[ ind[j] ]);

  /* compute v := - round(P^1 S u) */
  l = lg(s);
  v = cgetg(l, t_VECSMALL);
  for (i=1; i<l; i++)
  {
    double r, t = 0.;
    /* quick approximate computation */
    for (j=1; j<=K; j++) t += T->PinvSdbl[ ind[j] ][i];
    r = floor(t + 0.5);
    if (fabs(t + 0.5 - r) < 0.01)
    { /* dubious, compute exactly */
      z = gzero;
      for (j=1; j<=K; j++) z = addii(z, ((GEN**)T->dPinvS)[ ind[j] ][i]);
      v[i] = - itos( diviiround(z, T->d) );
    }
    else
      v[i] = - (long)r;
  }
  return gadd(s, gmul_mati_smallvec(T->P1, v));
} 

static trace_data *
init_trace(trace_data *T, GEN S, nflift_t *L, GEN q)
{
  long e = gexpo((GEN)S), i,j, l,h;
  GEN qgood, S1, invd;

  if (e < 0) return NULL; /* S = 0 */

  qgood = shifti(gun, e - 32); /* single precision check */
  if (cmpii(qgood, q) > 0) q = qgood;

  S1 = gdivround(S, q);
  if (gcmp0(S1)) return NULL;

  invd = ginv(itor(L->den, DEFAULTPREC));

  T->dPinvS = gmul(L->iprk, S);
  l = lg(S);
  h = lg(T->dPinvS[1]);
  T->PinvSdbl = (double**)cgetg(l, t_MAT);
  init_dalloc();
  for (j = 1; j < l; j++)
  {
    double *t = dalloc(h * sizeof(double));
    GEN c = (GEN)T->dPinvS[j];
    T->PinvSdbl[j] = t;
    for (i=1; i < h; i++) t[i] = rtodbl(mpmul(invd, (GEN)c[i]));
  }

  T->d  = L->den;
  T->P1 = gdivround(L->prk, q);
  T->S1 = S1; return T;
}

static void
update_trace(trace_data *T, long k, long i)
{
  if (!T) return;
  T->S1[k]       = T->S1[i];
  T->dPinvS[k]   = T->dPinvS[i];
  T->PinvSdbl[k] = T->PinvSdbl[i];
}

/* reduce coeffs mod (T,pk), then center mod pk */
static GEN
FqX_centermod(GEN z, GEN T, GEN pk, GEN pks2)
{
  long i, l;
  GEN y;
  if (!T) return centermod_i(z, pk, pks2);
  y = FpXQX_red(z, T, pk); l = lgef(y);
  for (i = 2; i < l; i++)
  {
    GEN c = (GEN)y[i];
    if (typ(c) == t_INT)
      c = centermodii(c, pk, pks2);
    else
      c = FpX_center(c, pk);
    y[i] = (long)c;
  }
  return y;
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
  GEN pol = T->pol, nf = T->nf, famod = T->fact, dn = T->dn;
  GEN bound = T->bound;
  GEN nfpol = (GEN)nf[1];
  long K = 1, cnt = 1, i,j,k, curdeg, lfamod = lg(famod)-1, dnf = degpol(nfpol);
  GEN res = cgetg(3, t_VEC);
  pari_sp av0 = avma;
  GEN pk = gpowgs(p,a), pks2 = shifti(pk,-1);

  GEN trace1   = cgetg(lfamod+1, t_MAT);
  GEN trace2   = cgetg(lfamod+1, t_MAT);
  GEN ind      = cgetg(lfamod+1, t_VECSMALL);
  GEN degpol   = cgetg(lfamod+1, t_VECSMALL);
  GEN degsofar = cgetg(lfamod+1, t_VECSMALL);
  GEN listmod  = cgetg(lfamod+1, t_COL);
  GEN fa       = cgetg(lfamod+1, t_COL);
  GEN q = ceil_safe(mpsqrt(T->BS_2));
  GEN lc = absi(leading_term(pol)), lt = is_pm1(lc)? NULL: lc;
  GEN C2ltpol, C = T->L->topowden, Tpk = T->L->Tpk;
  GEN Clt  = mul_content(C, lt);
  GEN C2lt = mul_content(C,Clt);
  const double Bhigh = get_Bhigh(lfamod, dnf);
  trace_data _T1, _T2, *T1, *T2;
  pari_timer ti;

  TIMERstart(&ti);

  if (maxK < 0) maxK = lfamod-1;

  C2ltpol = C2lt? gmul(C2lt,pol): pol;
  {
    GEN t1,t2, ltdn, lt2dn;

    ltdn = mul_content(lt, dn);
    lt2dn= mul_content(ltdn, lt);

    for (i=1; i <= lfamod; i++)
    {
      GEN P = (GEN)famod[i];
      long d = degpol(P);

      degpol[i] = d; P += 2;
      t1 = (GEN)P[d-1];/* = - S_1 */
      t2 = gsqr(t1);
      if (d > 1) t2 = gsub(t2, gmul2n((GEN)P[d-2], 1));
      t2 = Tpk? FpX_rem(t2, Tpk, pk): modii(t2, pk); /* = S_2 Newton sum */
      if (lt)
      {
        t1 = FpX_red(gmul(ltdn, t1), pk);
        t2 = FpX_red(gmul(lt2dn,t2), pk);
      }
      trace1[i] = (long)nf_bestlift(t1, NULL, T->L);
      trace2[i] = (long)nf_bestlift(t2, NULL, T->L);
    }

    T1 = init_trace(&_T1, trace1, T->L, q);
    T2 = init_trace(&_T2, trace2, T->L, q);
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
      GEN t, y, q, list;
      pari_sp av;

      av = avma;
      /* d - 1 test */
      if (T1)
      {
        t = get_trace(ind, T1);
        if (rtodbl(QuickNormL2(t,DEFAULTPREC)) > Bhigh)
        {
          if (DEBUGLEVEL>6) fprintferr(".");
          avma = av; goto NEXT;
        }
      }
      /* d - 2 test */
      if (T2)
      {
        t = get_trace(ind, T2);
        if (rtodbl(QuickNormL2(t,DEFAULTPREC)) > Bhigh)
        {
          if (DEBUGLEVEL>3) fprintferr("|");
          avma = av; goto NEXT;
        }
      }
      avma = av;
      y = lt; /* full computation */
      for (i=1; i<=K; i++)
      {
        GEN q = (GEN)famod[ind[i]];
        if (y) q = gmul(y, q);
        y = FqX_centermod(q, Tpk, pk, pks2);
      }
      y = nf_pol_lift(y, bound, T);
      if (!y)
      {
        if (DEBUGLEVEL>3) fprintferr("@");
        avma = av; goto NEXT;
      }
      /* try out the new combination: y is the candidate factor */
      q = RXQX_divrem(C2ltpol, y, nfpol, ONLY_DIVIDES);
      if (!q)
      {
        if (DEBUGLEVEL>3) fprintferr("*");
        avma = av; goto NEXT;
      }

      /* found a factor */
      list = cgetg(K+1, t_VEC);
      listmod[cnt] = (long)list;
      for (i=1; i<=K; i++) list[i] = famod[ind[i]];

      y = Q_primpart(y);
      fa[cnt++] = (long)QXQ_normalize(y, nfpol);
      /* fix up pol */
      pol = q;
      for (i=j=k=1; i <= lfamod; i++)
      { /* remove used factors */
        if (j <= K && i == ind[j]) j++;
        else
        {
          famod[k] = famod[i];
          update_trace(T1, k, i);
          update_trace(T2, k, i);
          degpol[k] = degpol[i]; k++;
        }
      }
      lfamod -= K;
      if (lfamod < 2*K) goto END;
      i = 1; curdeg = degpol[ind[1]];

      if (C2lt) pol = Q_primpart(pol);
      if (lt) lt = absi(leading_term(pol));
      Clt  = mul_content(C, lt);
      C2lt = mul_content(C,Clt);
      C2ltpol = C2lt? gmul(C2lt,pol): pol;
      if (DEBUGLEVEL > 2)
      {
        fprintferr("\n"); msgTIMER(&ti, "to find factor %Z",y);
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

    if (C2lt && lfamod < 2*K) pol = QXQ_normalize(Q_primpart(pol), nfpol);
    setlg(famod, lfamod+1);
    listmod[cnt] = (long)dummycopy(famod);
    fa[cnt++] = (long)pol;
  }
  if (DEBUGLEVEL>6) fprintferr("\n");
  if (cnt == 2) { 
    avma = av0; 
    res[1] = (long)_vec(T->pol);
    res[2] = (long)_vec(T->fact);
  }
  else
  {
    setlg(listmod, cnt); setlg(fa, cnt);
    res[1] = (long)fa;
    res[2] = (long)listmod;
    gerepilecopy(av0, res);
  }
  return res;
}

static GEN
nf_check_factors(nfcmbf_t *T, GEN P, GEN M_L, GEN famod, GEN pk)
{
  GEN nf = T->nf, bound = T->bound;
  GEN nfT = (GEN)nf[1];
  long i, j, r, n0;
  GEN pol = P, list, piv, y, pks2;
  GEN C2ltpol, C = T->L->topowden, Tpk = T->L->Tpk;
  GEN lc = absi(leading_term(pol)), lt = is_pm1(lc)? NULL: lc;
  GEN Clt  = mul_content(C, lt);
  GEN C2lt = mul_content(C,Clt);

  piv = special_pivot(M_L);
  if (!piv) return NULL;
  if (DEBUGLEVEL>3) fprintferr("special_pivot output:\n%Z\n",piv);

  pks2 = shifti(pk,-1);
  r  = lg(piv)-1;
  n0 = lg(piv[1])-1;
  list = cgetg(r+1, t_COL);
  C2ltpol = C2lt? gmul(C2lt,pol): pol;
  for (i = 1;;)
  {
    GEN c = (GEN)piv[i];
    pari_sp av = avma, lim = stack_lim(av, 2);
    if (DEBUGLEVEL) fprintferr("nf_LLL_cmbf: checking factor %ld\n",i);

    y = lt;
    for (j=1; j<=n0; j++)
      if (signe(c[j]))
      {
        GEN q = (GEN)famod[j];
        if (y) q = gmul(y, q);
        y = FqX_centermod(q, Tpk, pk, pks2);
        if (low_stack(lim, stack_lim(av,2)))
        {
          if(DEBUGMEM>1) err(warnmem,"nf_check_factors");
          y = gerepilecopy(av, y);
        }
      }
    y = nf_pol_lift(y, bound, T);
    if (!y) return NULL;

    y = gerepilecopy(av, y);
    /* y is the candidate factor */
    pol = RXQX_divrem(C2ltpol, y, nfT, ONLY_DIVIDES);
    if (!pol) return NULL;

    y = Q_primpart(y);
    list[i++] = (long)QXQ_normalize(y, nfT);
    if (i >= r) break;

    if (C2lt) pol = Q_primpart(pol);
    if (lt) lt = absi(leading_term(pol));
    Clt  = mul_content(C, lt);
    C2lt = mul_content(C,Clt);
    C2ltpol = C2lt? gmul(C2lt,pol): pol;
  }
  y = Q_primpart(pol);
  list[i] = (long)QXQ_normalize(y, nfT); return list;
}

static GEN
nf_to_Zq(GEN x, GEN T, GEN pk, GEN pks2, GEN proj)
{
  GEN y;
  if (typ(x) != t_COL) return centermodii(x, pk, pks2);
  y = gmul(proj, x);
  if (!T) return centermodii(y, pk, pks2);
  y = vec_to_pol(y, varn(T));
  return centermod_i(FpX_rem(y, T, pk), pk, pks2);
}

/* Assume P in nfX form [ unifpol(,t_COL) ], lc(P) != 0 mod p.
 * Reduce P to Zp[X]/(T) mod p^a */
static GEN
ZqX(GEN P, GEN pk, GEN T, GEN proj)
{
  long i, l = lgef(P);
  GEN z, pks2 = shifti(pk,-1);

  z = cgetg(l,t_POL); z[1] = P[1];
  for (i=2; i<l; i++) z[i] = (long)nf_to_Zq((GEN)P[i],T,pk,pks2,proj);
  return normalizepol(z);
}

static GEN
ZqX_normalize(GEN P, GEN lt, nflift_t *L)
{
  GEN R = lt? gmul(mpinvmod(lt, L->pk), P): P;
  return ZqX(R, L->pk, L->Tpk, L->ZqProj);
}

/* We want to be able to reconstruct x, |x|^2 < C, from x mod pr^k */
static double
bestlift_bound(GEN C, long d, double alpha, GEN Npr)
{
  const double y = 1 / (alpha - 0.25); /* = 2 if alpha = 3/4 */
  double t;
  if (typ(C) != t_REAL) C = gmul(C, realun(DEFAULTPREC));
  setlg(C, DEFAULTPREC);
  t = rtodbl(mplog(gmul2n(divrs(C,d), 4))) * 0.5 + (d-1) * log(1.5 * sqrt(y));
  return ceil((t * d) / log(gtodouble(Npr)));
}

static GEN
get_R(GEN M)
{ 
  GEN R = sqred1_from_QR(M, DEFAULTPREC + (gexpo(M) >> TWOPOTBITS_IN_LONG));
  long i, l = lg(R);
  for (i=1; i<l; i++) coeff(R,i,i) = un;
  return R;
}

static void
init_proj(nflift_t *L, GEN nfT, GEN p)
{
  if (L->Tp)
  {
    GEN z = cgetg(3, t_VEC), proj;
    z[1] = (long)L->Tp;
    z[2] = (long)FpX_div(FpX_red(nfT,p), L->Tp, p);
    z = hensel_lift_fact(nfT, z, NULL, p, L->pk, L->k);
    L->Tpk = (GEN)z[1];
    proj = get_proj_modT(L->topow, L->Tpk, L->pk);
    if (L->topowden)
      proj = FpM_red(gmul(mpinvmod(L->topowden, L->pk), proj), L->pk);
    L->ZqProj = proj;
  }
  else
  {
    L->Tpk = NULL;
    L->ZqProj = dim1proj(L->prkHNF);
  }
}

static void
bestlift_init(long a, GEN nf, GEN pr, GEN C, nflift_t *L)
{
  const int D = 100;
  const double alpha = ((double)D-1) / D; /* LLL parameter */
  const long d = degpol(nf[1]);
  pari_sp av = avma;
  GEN prk, PRK, B, GSmin, pk;
  pari_timer ti;

  TIMERstart(&ti);
  if (!a) a = (long)bestlift_bound(C, d, alpha, idealnorm(nf,pr));

  for (;; avma = av, a<<=1)
  {
    if (DEBUGLEVEL>2) fprintferr("exponent: %ld\n",a);
    PRK = prk = idealpows(nf, pr, a);
    pk = gcoeff(prk,1,1);
    /* reduce size first, "scramble" matrix */
    PRK = lllintpartial_ip(PRK);
    /* now floating point reduction is fast */
    PRK = lllint_fp_ip(PRK, 4);
    PRK = lllint_i(PRK, D, 0, NULL, NULL, &B);
    if (!PRK) { PRK = prk; GSmin = pk; } /* nf = Q */
    else
    {
      pari_sp av2 = avma;
      GEN S = invmat( get_R(PRK) ), BB = GS_norms(B, DEFAULTPREC);
      GEN smax = gzero;
      long i, j;
      for (i=1; i<=d; i++)
      {
        GEN s = gzero;
        for (j=1; j<=d; j++)
          s = gadd(s, gdiv( gsqr(gcoeff(S,i,j)), (GEN)BB[j]));
        if (gcmp(s, smax) > 0) smax = s;
      }
      GSmin = gerepileupto(av2, ginv(gmul2n(smax, 2)));
    }
    if (gcmp(GSmin, C) >= 0) break;
  }
  if (DEBUGLEVEL>2)
    fprintferr("for this exponent, GSmin = %Z\nTime reduction: %ld\n",
      GSmin, TIMER(&ti));
  L->k = a;
  L->den = L->pk = pk;
  L->prk = PRK;
  L->iprk = ZM_inv(PRK, pk);
  L->GSmin= GSmin;
  L->prkHNF = prk;
  init_proj(L, (GEN)nf[1], (GEN)pr[1]);
}

static GEN
nf_LLL_cmbf(nfcmbf_t *T, GEN p, long k, long rec)
{
  nflift_t *L = T->L;
  GEN pk = L->pk, PRK = L->prk, PRKinv = L->iprk, GSmin = L->GSmin;
  GEN Tpk = L->Tpk;

  GEN famod = T->fact, nf = T->nf, ZC = T->ZC, Br = T->Br;
  GEN Pbase = T->polbase, P = T->pol, dn = T->dn;
  GEN nfT = (GEN)nf[1];
  GEN Btra;
  long dnf = degpol(nfT), dP = degpol(P);

  double BitPerFactor = 0.5; /* nb bits / modular factor */
  long i, C, tmax, n0;
  GEN lP, Bnorm, Tra, T2, TT, CM_L, m, list, ZERO;
  double Bhigh;
  pari_sp av, av2, lim;
  long ti_LLL = 0, ti_CF = 0;
  pari_timer ti2, TI;

  lP = absi(leading_term(P));
  if (is_pm1(lP)) lP = NULL;

  n0 = lg(famod) - 1;
 /* Lattice: (S PRK), small vector (vS vP). To find k bound for the image,
  * write S = S1 q + S0, P = P1 q + P0
  * |S1 vS + P1 vP|^2 <= Bhigh for all (vS,vP) assoc. to true factors */
  Btra = mulrr(ZC, mulsr(dP*dP, normlp(Br, 2, dnf)));
  Bhigh = get_Bhigh(n0, dnf);
  C = (long)ceil(sqrt(Bhigh/n0)) + 1; /* C^2 n0 ~ Bhigh */
  Bnorm = dbltor( n0 * C * C + Bhigh );
  ZERO = zeromat(n0, dnf);

  av = avma; lim = stack_lim(av, 1);
  TT = cgetg(n0+1, t_VEC);
  Tra  = cgetg(n0+1, t_MAT);
  for (i=1; i<=n0; i++) TT[i] = 0;
  CM_L = gscalsmat(C, n0);
  /* tmax = current number of traces used (and computed so far) */
  for(tmax = 0;; tmax++)
  {
    long a, b, bmin, bgood, delta, tnew = tmax + 1, r = lg(CM_L)-1;
    GEN oldCM_L, M_L, q, S1, P1, VV;
    int first = 1;

    /* bound for f . S_k(genuine factor) = ZC * bound for T_2(S_tnew) */
    Btra = mulrr(ZC, mulsr(dP*dP, normlp(Br, 2*tnew, dnf)));
    bmin = logint(ceil_safe(mpsqrt(Btra)), gdeux, NULL);
    if (DEBUGLEVEL>2)
      fprintferr("\nLLL_cmbf: %ld potential factors (tmax = %ld, bmin = %ld)\n",
                 r, tmax, bmin);

    /* compute Newton sums (possibly relifting first) */
    if (gcmp(GSmin, Btra) < 0)
    {
      nflift_t L1;
      GEN polred;

      bestlift_init(k<<1, nf, T->pr, Btra, &L1);
      polred = ZqX_normalize(Pbase, lP, &L1);
      k      = L1.k;
      pk     = L1.pk;
      PRK    = L1.prk;
      PRKinv = L1.iprk;
      GSmin  = L1.GSmin;
      Tpk    = L1.Tpk;
      famod = hensel_lift_fact(polred, famod, Tpk, p, pk, k);
      for (i=1; i<=n0; i++) TT[i] = 0;
    }
    for (i=1; i<=n0; i++)
    {
      GEN h, lPpow = lP? gpowgs(lP, tnew): NULL;
      GEN z = polsym_gen((GEN)famod[i], (GEN)TT[i], tnew, Tpk, pk);
      TT[i] = (long)z;
      h = (GEN)z[tnew+1];
      /* make Newton sums integral */
      lPpow = mul_content(lPpow, dn);
      if (lPpow) h = FpX_red(gmul(h,lPpow), pk);
      Tra[i] = (long)nf_bestlift(h, NULL, L); /* S_tnew(famod) */
    }

    /* compute truncation parameter */
    if (DEBUGLEVEL>2) { TIMERstart(&ti2); TIMERstart(&TI); }
    oldCM_L = CM_L;
    av2 = avma;
    b = delta = 0; /* -Wall */
AGAIN:
    M_L = Q_div_to_int(CM_L, stoi(C));
    T2 = gmul(Tra, M_L);
    VV = gdivround(gmul(PRKinv, T2), pk);
    T2 = gsub(T2, gmul(PRK, VV));

    if (first)
    { /* initialize lattice, using few p-adic digits for traces */
      a = gexpo(T2);
      bgood = (long)(a - max(32, BitPerFactor * r));
      b = max(bmin, bgood);
      delta = a - b;
    }
    else
    { /* add more p-adic digits and continue reduction */
      long b0 = gexpo(T2);
      if (b0 < b) b = b0;
      b = max(b-delta, bmin);
      if (b - delta/2 < bmin) b = bmin; /* near there. Go all the way */
    }

    /* restart with truncated entries */
    q = shifti(gun, b);
    P1 = gdivround(PRK, q);
    S1 = gdivround(Tra, q);
    T2 = gsub(gmul(S1, M_L), gmul(P1, VV));
    m = vconcat( CM_L, T2 );
    if (first)
    {
      first = 0;
      m = concatsp( m, vconcat(ZERO, P1) );
      /*     [ C M_L   0  ]
       * m = [            ]   square matrix
       *     [  T2'   PRK ]   T2' = Tra * M_L  truncated
       */
    }
    CM_L = LLL_check_progress(Bnorm, n0, m, b == bmin, /*dbg:*/ &ti_LLL);
    if (DEBUGLEVEL>2)
      fprintferr("LLL_cmbf: b =%4ld; r =%3ld -->%3ld, time = %ld\n",
                 b, lg(m)-1, CM_L? lg(CM_L)-1: 1, TIMER(&TI));
    if (!CM_L) { list = _col(QXQ_normalize(P,nfT)); break; }
    if (b > bmin)
    {
      CM_L = gerepilecopy(av2, CM_L);
      goto AGAIN;
    }
    if (DEBUGLEVEL>2) msgTIMER(&ti2, "for this trace");

    i = lg(CM_L) - 1;
    if (i == r && gegal(CM_L, oldCM_L))
    {
      CM_L = oldCM_L;
      avma = av2; continue;
    }

    if (i <= r && i*rec < n0)
    {
      pari_timer ti;
      if (DEBUGLEVEL>2) TIMERstart(&ti);
      list = nf_check_factors(T, P, Q_div_to_int(CM_L,stoi(C)), famod, pk);
      if (DEBUGLEVEL>2) ti_CF += TIMER(&ti);
      if (list) break;
      CM_L = gerepilecopy(av2, CM_L);
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"nf_LLL_cmbf");
      gerepileall(av, Tpk? 9: 8,
                      &CM_L,&TT,&Tra,&famod,&pk,&GSmin,&PRK,&PRKinv,&Tpk);
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
  pari_timer ti;

  if (DEBUGLEVEL>2) TIMERstart(&ti);
  T->fact = hensel_lift_fact(polred, famod, T->L->Tpk, p, T->L->pk, a);
  if (nft < 11) maxK = -1; /* few modular factors: try all posibilities */
  if (DEBUGLEVEL>2) msgTIMER(&ti, "Hensel lift");

  L = nfcmbf(T, p, a, maxK, klim);
  if (DEBUGLEVEL>2) msgTIMER(&ti, "Naive recombination");

  res     = (GEN)L[1];
  listmod = (GEN)L[2]; l = lg(listmod)-1;
  famod = (GEN)listmod[l];
  if (maxK >= 0 && lg(famod)-1 > 2*maxK)
  {
    if (l > 1) T->polbase = unifpol(nf, (GEN)res[l], t_COL);
    L = nf_LLL_cmbf(T, p, a, maxK);
    /* remove last elt, possibly unfactored. Add all new ones. */
    setlg(res, l); res = concatsp(res, L);
  }

  m = lg(res); z = cgetg(m, t_VEC);
  for (i=1;i<m; i++) z[i] = (long)unifpol(nf,(GEN)res[i], t_POLMOD);
  return z;
}

static GEN
nf_DDF_roots(GEN pol, GEN polred, GEN nfpol, GEN lt, GEN init_fa, long nbf,
             long fl, nflift_t *L)
{
  long Cltx_r[] = { evaltyp(t_POL)|_evallg(4), 0,0,0 };
  long i, m;
  GEN C2ltpol, C = L->topowden;
  GEN Clt  = mul_content(C, lt);
  GEN C2lt = mul_content(C,Clt);
  GEN z;

  if (L->Tpk)
  {
    int cof = (degpol(pol) > nbf); /* non trivial cofactor ? */
    z = FqX_split_roots(init_fa, L->Tp, L->p, cof? polred: NULL);
    z = hensel_lift_fact(polred, z, L->Tpk, L->p, L->pk, L->k);
    if (cof) setlg(z, lg(z)-1); /* remove cofactor */
    z = roots_from_deg1(z);
  }
  else
    z = rootpadicfast(polred, L->p, L->k);
  Cltx_r[1] = evalsigne(1) | evalvarn(varn(pol)) | evallgef(4);
  Cltx_r[3] = Clt? (long)Clt: un;
  C2ltpol  = C2lt? gmul(C2lt, pol): pol;
  for (m=1,i=1; i<lg(z); i++)
  {
    GEN q, r = (GEN)z[i];

    r = nf_bestlift_to_pol(r, NULL, L);
    Cltx_r[2] = lneg(r); /* check P(r) == 0 */
    q = RXQX_divrem(C2ltpol, Cltx_r, nfpol, ONLY_DIVIDES); /* integral */
    if (q) { 
      C2ltpol = C2lt? gmul(Clt,q): q;
      if (Clt) r = gdiv(r, Clt);
      z[m++] = (long)r;
    }
    else if (fl == 2) return cgetg(1, t_VEC);
  }
  z[0] = evaltyp(t_VEC) | evallg(m);
  return z;
}

/* return the factorization of the square-free polynomial x.
   The coeff of x are in Z_nf and its leading term is a rational integer.
   deg(x) > 1, deg(nfpol) > 1
   If fl = 1, return only the roots of x in nf
   If fl = 2, as fl=1 if pol splits, [] otherwise */
static GEN
nfsqff(GEN nf, GEN pol, long fl)
{
  long i, n, nbf, ct, maxf, dpol = degpol(pol);
  ulong pp;
  pari_sp av = avma;
  GEN pr, C0, dk, bad, polbase, init_fa = NULL;
  GEN N2, rep, polmod, polred, lt, nfpol;
  byteptr pt = diffptr;
  nfcmbf_t T;
  nflift_t L;
  pari_timer ti, ti_tot;

  if (DEBUGLEVEL>2) { TIMERstart(&ti); TIMERstart(&ti_tot); }
  nfpol = (GEN)nf[1]; n = degpol(nfpol);
  polbase = unifpol(nf, pol, t_COL);
  if (typ(polbase) != t_POL) err(typeer, "nfsqff");
  polmod  = unifpol(nf, pol, t_POLMOD);
  /* heuristic */
  if (dpol*3 < n) 
  {
    GEN z, t;
    if (DEBUGLEVEL>2) fprintferr("Using Trager's method\n");
    z = (GEN)polfnf(polmod, nfpol)[1];
    if (fl) {
      long l = lg(z);
      for (i = 1; i < l; i++)
      {
        t = (GEN)z[i]; if (degpol(t) > 1) break;
        z[i] = lneg(gdiv((GEN)t[3], (GEN)t[2]));
      }
      setlg(z, i);
    }
    return gerepilecopy(av, z);
  }

  pol = simplify_i(lift(polmod));
  lt  = leading_term(polbase); /* t_INT */
  if (gcmp1(lt)) lt = NULL;

  dk = absi((GEN)nf[3]);
  bad = mulii(dk,(GEN)nf[4]); if (lt) bad = mulii(bad, lt);

  polred = pr = NULL; /* gcc -Wall */
  nbf = 0; pp = 0;
  L.Tp = NULL;

  /* FIXME: slow factorization of large polynomials over large Fq */
  maxf = 1;
  if (dpol > 100) /* tough */
  {
    if (n >= 20) maxf = 4;
  }
  else
  {
    if (n >= 15) maxf = 4;
  }
  
  for (ct = 5;;)
  {
    GEN aT, apr, ap, modpr, red;
    long anbf;
    pari_timer ti_pr;

    GEN list, r = NULL, fa = NULL;
    pari_sp av2 = avma;
    if (DEBUGLEVEL>3) TIMERstart(&ti_pr);
    for (;;)
    {
      NEXT_PRIME_VIADIFF_CHECK(pp, pt);
      if (! umodiu(bad,pp)) continue;
      ap = utoi(pp);
      list = (GEN)factmod0(nfpol, ap)[1];
      if (maxf == 1)
      { /* deg.1 factors are best */
        r = (GEN)list[1];
        if (degpol(r) == 1) break;
      }
      else
      { /* otherwise, pick factor of largish degree */
        long i, dr;
        for (i = lg(list)-1; i > 0; i--)
        {
          r = (GEN)list[i]; dr = degpol(r);
          if (dr <= maxf) break;
        }
        if (i > 0) break;
      }
      avma = av2;
    }
    apr = apply_kummer(nf,r,gun,ap);

    modpr = zk_to_ff_init(nf,&apr,&aT,&ap);
    red = modprX(polbase, nf, modpr);
    if (!aT)
    { /* degree 1 */
      red = u_Fp_FpX(red, pp);
      if (!u_FpX_is_squarefree(red, pp)) { avma = av2; continue; }
      anbf = fl? u_FpX_nbroots(red, pp): u_FpX_nbfact(red, pp);
    }
    else
    {
      GEN q;
      if (!FqX_is_squarefree(red,aT,ap)) { avma = av2; continue; }
      q = gpowgs(ap, degpol(aT));
      anbf = fl? FqX_split_deg1(&fa, red, q, aT, ap)
               : FqX_split_by_degree(&fa, red, q, aT, ap);
    }
    if (fl == 2 && anbf < dpol) return cgetg(1,t_VEC);
    if (anbf <= 1)
    {
      if (!fl) /* irreducible */
        return gerepilecopy(av, _vec(QXQ_normalize(polmod, nfpol)));
      if (!anbf) return cgetg(1,t_VEC); /* no root */
    }

    if (!nbf || anbf < nbf
             || (anbf == nbf && cmpii((GEN)apr[4], (GEN)pr[4]) > 0))
    {
      nbf = anbf; pr = apr;
      L.Tp = aT; init_fa = fa;
    }
    else avma = av2;
    if (DEBUGLEVEL>3)
      fprintferr("%3ld %s at prime\n  %Z\nTime: %ld\n",
                 anbf, fl?"roots": "factors", apr, TIMER(&ti_pr));
    if (--ct <= 0) break;
  }
  if (DEBUGLEVEL>2) {
    msgTIMER(&ti, "choice of a prime ideal");
    fprintferr("Prime ideal chosen: %Z\n", pr);
  }

  L.tozk = (GEN)nf[8];
  L.topow= Q_remove_denom((GEN)nf[7], &L.topowden);
  T.ZC = L2_bound(nf, L.tozk, &(T.dn));
  T.Br = nf_root_bounds(pol, nf); if (lt) T.Br = gmul(T.Br, lt);

  if (fl) C0 = normlp(T.Br, 2, n);
  else    C0 = nf_factor_bound(nf, polbase); /* bound for T_2(Q_i), Q | P */
  T.bound = mulrr(T.ZC, C0); /* bound for |Q_i|^2 in Z^n on chosen Z-basis */

  N2 = mulsr(dpol*dpol, normlp(T.Br, 4, n)); /* bound for T_2(lt * S_2) */
  T.BS_2 = mulrr(T.ZC, N2); /* bound for |S_2|^2 on chosen Z-basis */

  if (DEBUGLEVEL>2) {
    msgTIMER(&ti, "bound computation");
    fprintferr("  1) T_2 bound for %s: %Z\n", fl?"root":"factor", C0);
    fprintferr("  2) Conversion from T_2 --> | |^2 bound : %Z\n", T.ZC);
    fprintferr("  3) Final bound: %Z\n", T.bound);
  }

  L.p = (GEN)pr[1];
  if (L.Tp && degpol(L.Tp) == 1) L.Tp = NULL;
  bestlift_init(0, nf, pr, T.bound, &L);
  if (DEBUGLEVEL>2) TIMERstart(&ti);
  polred = ZqX_normalize(polbase, lt, &L); /* monic */

  if (fl) return gerepilecopy(av,
                   nf_DDF_roots(pol, polred, nfpol, lt, init_fa, nbf, fl, &L));

  {
    pari_sp av2 = avma;
    if (L.Tp)
      rep = FqX_split_all(init_fa, L.Tp, L.p);
    else
    {
      long d;
      rep = cgetg(dpol + 1, t_VEC); rep[1] = (long)polred;
      d = FpX_split_berlekamp((GEN*)(rep + 1), L.p);
      setlg(rep, d + 1);
    }
    T.fact  = gerepilecopy(av2, sort_vecpol(rep));
  }
  if (DEBUGLEVEL>2) msgTIMER(&ti, "splitting mod %Z", pr);
  T.pr = pr;
  T.L  = &L;
  T.polbase = polbase;
  T.pol   = pol;
  T.nf    = nf;
  T.hint  = 1; /* useless */

  rep = nf_combine_factors(&T, polred, L.p, L.k, dpol-1);
  if (DEBUGLEVEL>2)
    fprintferr("Total Time: %ld\n===========\n", TIMER(&ti_tot));
  return gerepileupto(av, rep);
}

/* return the characteristic polynomial of alpha over nf, where alpha
   is an element of the algebra nf[X]/(T) given as a polynomial in X */
GEN
rnfcharpoly(GEN nf,GEN T,GEN alpha,int v)
{
  long vnf, vT, lT;
  pari_sp av = avma;
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
  p1 = caract2(T, unifpol(nf,alpha, t_POLMOD), v);
  return gerepileupto(av, unifpol(nf, p1, t_POLMOD));
}
