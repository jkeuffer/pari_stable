/* $Id$

Copyright (C) 2000-2004  The PARI group.

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
#include "paripriv.h"

static GEN nfsqff(GEN nf,GEN pol,long fl,GEN den);

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

typedef struct
{
  nflift_t *L;
  GEN nf;
  GEN pol, polbase;
  GEN fact;
  GEN pr;
  GEN Br, bound, ZC, BS_2;
  GEN dn;
} nfcmbf_t;

/* P,Q in Z[X,Y], T in Z[Y] irreducible. compute GCD in Q[Y]/(T)[X].
 *
 * We essentially follow M. Encarnacion "On a modular Algorithm for computing
 * GCDs of polynomials over number fields" (ISSAC'94).
 *
 * We procede as follows
 *  1:compute the gcd modulo primes discarding bad primes as they are detected.
 *  2:reconstruct the result via matratlift, stoping as soon as we get weird
 *    denominators.
 *  3:if matratlift succeeds, try the full division.
 * Suppose accuracy is insufficient to get the result right: matratlift will
 * rarely succeed, and even if it does the polynomial we get has sensible
 * coefficients, so the full division will not be too costly.
 *
 * If not NULL, den must a a multiple of the denominator of the gcd,
 * for example the discriminant of T.
 *
 * NOTE: if T is not irreducible, nfgcd may loop forever, esp. if gcd | T */
GEN
nfgcd_all(GEN P, GEN Q, GEN T, GEN den, GEN *Pnew)
{
  pari_sp btop, st_lim, ltop = avma;
  GEN lP, lQ, M, dsol, R, ax, bo, sol, mod = NULL;
  long vP = varn(P), vT = varn(T), dT = degpol(T), dM = 0, dR;
  ulong p;
  byteptr primepointer;

  if (!signe(P)) { if (Pnew) *Pnew = zeropol(vT); return gcopy(Q); }
  if (!signe(Q)) { if (Pnew) *Pnew = pol_1(vT);   return gcopy(P); }
  /*Compute denominators*/
  if (!den) den = ZX_disc(T);
  lP = leading_term(P);
  lQ = leading_term(Q);
  if ( !((typ(lP)==t_INT && is_pm1(lP)) || (typ(lQ)==t_INT && is_pm1(lQ))) )
    den = mulii(den, gcdii(ZX_resultant(lP, T), ZX_resultant(lQ, T)));

  btop = avma; st_lim = stack_lim(btop, 1);
  primepointer = init_modular(&p);
  for (;;)
  {
    NEXT_PRIME_VIADIFF_CHECK(p, primepointer);
    /*Discard primes dividing disc(T) or lc(PQ) */
    if (!smodis(den, p)) continue;
    if (DEBUGLEVEL>5) fprintferr("nfgcd: p=%d\n",p);
    /*Discard primes when modular gcd does not exist*/
    if ((R = FlxqX_safegcd(ZXX_to_FlxX(P,p,vT),
                           ZXX_to_FlxX(Q,p,vT),
                           ZX_to_Flx(T,p), p)) == NULL) continue;
    dR = degpol(R);
    if (dR == 0) { avma = ltop; if (Pnew) *Pnew = P; return pol_1(vP); }
    if (mod && dR > dM) continue; /* p divides Res(P/gcd, Q/gcd). Discard. */

    R = RgXX_to_RgM(FlxX_to_ZXX(R), dT);
    /* previous primes divided Res(P/gcd, Q/gcd)? Discard them. */
    if (!mod || dR < dM) { M = R; mod = utoipos(p); dM = dR; continue; }
    if (low_stack(st_lim, stack_lim(btop, 1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"nfgcd");
      gerepileall(btop, 2, &M, &mod);
    }

    ax = muliu(Fp_inv(utoipos(p), mod), p);
    M = ZM_add(R, ZM_Z_mul(ZM_sub(M, R), ax));
    mod = muliu(mod, p);
    M = FpM_red(M, mod);
    /* I suspect it must be better to take amax > bmax*/
    bo = sqrti(shifti(mod, -1));
    if ((sol = matratlift(M, mod, bo, bo, den)) == NULL) continue;
    sol = RgM_to_RgXX(sol,vP,vT);
    dsol = Q_primpart(sol);

    R = RgXQX_pseudorem(Q, dsol, T);
    if (signe(R)) continue;
    if (Pnew)
      *Pnew = RgXQX_pseudodivrem(P, dsol, T, &R);
    else
      R = RgXQX_pseudorem(P, dsol, T);
    if (signe(R)) continue;
    gerepileall(ltop, Pnew? 2: 1, &dsol, Pnew);
    return dsol; /* both remainders are 0 */
  }
}
GEN
nfgcd(GEN P, GEN Q, GEN T, GEN den)
{ return nfgcd_all(P,Q,T,den,NULL); }

GEN
nffactormod(GEN nf, GEN x, GEN pr)
{
  long j, l, vx = varn(x), vn;
  pari_sp av = avma;
  GEN F, E, rep, xrd, modpr, T, p;

  nf = checknf(nf);
  vn = varn(nf[1]);
  if (typ(x)!=t_POL) pari_err(typeer,"nffactormod");
  if (varncmp(vx,vn) >= 0)
    pari_err(talker,"polynomial variable must have highest priority in nffactormod");

  modpr = nf_to_Fq_init(nf, &pr, &T, &p);
  xrd = nfX_to_FqX(x, nf, modpr);
  rep = FqX_factor(xrd,T,p);
  settyp(rep, t_MAT);
  F = gel(rep,1); l = lg(F);
  E = gel(rep,2); settyp(E, t_COL);
  for (j = 1; j < l; j++) {
    gel(F,j) = FqX_to_nfX(gel(F,j), modpr);
    gel(E,j) = stoi(E[j]);
  }
  return gerepilecopy(av, rep);
}

static GEN
QXQX_normalize(GEN P, GEN T)
{
  GEN P0 = leading_term(P);
  long t = typ(P0);
  if (t == t_POL)
  {
    if (degpol(P0)) return RgXQX_RgXQ_mul(P, QXQ_inv(P0,T), T);
    P0 = gel(P0,2); t = typ(P0);
  }
  /* t = t_INT/t_FRAC */
  if (t == t_INT && is_pm1(P0) && signe(P0) > 0) return P; /* monic */
  return RgX_Rg_div(P, P0);
}
static GEN
get_den(GEN *nf, GEN T)
{
  GEN den = gen_1;
  if (!*nf)
  {
    GEN fa, P, q, D;
    *nf = nfinitall(T, nf_PARTIALFACT, DEFAULTPREC);
    D = gel(*nf, 3);
    if (is_pm1(D)) return gen_1;
    fa = Z_factor_limit(D, 0);
    P = gel(fa,1); q = gel(P, lg(P)-1);
    if (!BPSW_psp(q)) den = q; /* *nf[3] may be incorrect */
  }
  return den;
}

/* lt(A) is an integer; ensure it is not a constant t_POL. In place */
static void
ensure_lt_INT(GEN A)
{
  long n = lg(A)-1;
  GEN lt = gel(A,n);
  while (typ(lt) != t_INT) gel(A,n) = lt = gel(lt,2);
}

/* return the roots of pol in nf */
GEN
nfroots(GEN nf,GEN pol)
{
  pari_sp av = avma;
  GEN A, T, den;
  long d;

  if (!nf) return nfrootsQ(pol);
  T = get_nfpol(nf, &nf);
  A = fix_relative_pol(T,pol,1);
  d = degpol(A);
  if (d < 0) pari_err(zeropoler, "nfroots");
  if (d == 0) return cgetg(1,t_VEC);
  if (d == 1)
  {
    A = QXQX_normalize(A,T);
    A = mkpolmod(gneg_i(gel(A,2)), T);
    return gerepilecopy(av, mkvec(A));
  }
  if (degpol(T) == 1) return gerepileupto(av, nfrootsQ(simplify_shallow(A)));

  A = Q_primpart(A);
  den = get_den(&nf, T);
  (void)nfgcd_all(A, RgX_deriv(A), T,
                  den == gen_1? gel(nf,4): mulii(gel(nf,4), den), &A);
  if (degpol(A) != d) A = Q_primpart( QXQX_normalize(A, T) );
  ensure_lt_INT(A);
  A = nfsqff(nf,A,1, den);
  A = gerepileupto(av, QXQV_to_mod(A, T));
  gen_sort_inplace(A, (void*)&cmp_RgX, &cmp_nodata, NULL);
  return A;
}

/* assume x is squarefree monic in nf.zk[X] */
int
nfissplit(GEN nf, GEN x)
{
  pari_sp av = avma;
  long l;
  nf = checknf(nf);
  x = fix_relative_pol(gel(nf,1), x, 1);
  if (typ(x) != t_POL) pari_err(typeer, "nfissplit");
  l = lg(nfsqff(nf, x, 2, gen_1));
  avma = av; return l != 1;
}

/* return a minimal lift of elt modulo id */
static GEN
nf_bestlift(GEN elt, GEN bound, nflift_t *L)
{
  GEN u;
  long i,l = lg(L->prk), t = typ(elt);
  if (t != t_INT)
  {
    if (t == t_POL) elt = mulmat_pol(L->tozk, elt);
    u = ZM_ZC_mul(L->iprk,elt);
    for (i=1; i<l; i++) gel(u,i) = diviiround(gel(u,i), L->den);
  }
  else
  {
    u = ZC_Z_mul(gel(L->iprk,1), elt);
    for (i=1; i<l; i++) gel(u,i) = diviiround(gel(u,i), L->den);
    elt = scalarcol(elt, l-1);
  }
  u = ZC_sub(elt, ZM_ZC_mul(L->prk, u));
  if (bound && gcmp(RgC_fpnorml2(u,DEFAULTPREC), bound) > 0) u = NULL;
  return u;
}

/* Warning: return L->topowden * (best lift) */
static GEN
nf_bestlift_to_pol(GEN elt, GEN bound, nflift_t *L)
{
  pari_sp av = avma;
  GEN v, u = nf_bestlift(elt,bound,L);
  if (!u) return NULL;
  v = gclone(u); avma = av;
  u = gmul(L->topow, v);
  gunclone(v); return u;
}

/* return the T->powden * (lift of pol with coefficients of T2-norm <= C)
 * if it exists */
static GEN
nf_pol_lift(GEN pol, GEN bound, nfcmbf_t *T)
{
  long i, l = lg(pol);
  GEN x = cgetg(l,t_POL);

  x[1] = pol[1];
  for (i=2; i<l; i++)
  {
    GEN t = nf_bestlift_to_pol(gel(pol,i), bound, T->L);
    if (!t) return NULL;
    if (typ(t) == t_POL && lg(t) == 3) t = gel(t,2);
    gel(x,i) = t;
  }
  return x;
}

static GEN
zerofact(long v)
{
  GEN z = cgetg(3, t_MAT);
  gel(z,1) = mkcol(zeropol(v));
  gel(z,2) = mkcol(gen_1); return z;
}

/* Return the factorization of A in Q[X]/(T) in rep [pre-allocated with
 * cgeg(3,t_MAT)], reclaiming all memory between avma and rep.
 * y is the vector of irreducible factors of B = Q_primpart( A/gcd(A,A') ).
 * Bad primes divide 'bad' */
static void
fact_from_sqff(GEN rep, GEN A, GEN B, GEN y, GEN T, GEN bad)
{
  pari_sp av = (pari_sp)rep;
  long n = lg(y)-1;
  GEN ex;

  if (A != B)
  { /* not squarefree */
    if (n == 1)
    { /* perfect power, simple ! */
      y = gerepileupto(av, QXQXV_to_mod(y, T));
      ex = mkcol( utoipos(degpol(A) / degpol(gel(y,1))) );
    }
    else
    { /* compute valuations mod a prime of degree 1 (avoid coeff explosion) */
      pari_sp av1 = avma;
      long j;
      GEN quo, p, r, Bp, E = cgetalloc(t_VECSMALL,n+1);
      byteptr pt = diffptr;
      ulong pp = 0;
      for (;; avma = av1)
      {
        NEXT_PRIME_VIADIFF_CHECK(pp, pt);
        if (! umodiu(bad,pp)) continue;
        p = utoipos(pp);
        r = FpX_oneroot(T, p);
        if (!r) continue;
        Bp = FpXY_evalx(B, r, p);
        if (FpX_is_squarefree(Bp, p)) break;
      }

      quo = FpXY_evalx(Q_primpart(A), r, p);
      for (j=n; j>=2; j--)
      {
        GEN fact = FpXY_evalx(gel(y,j), r, p);
        long e = 0;
        for(;; e++)
        {
          GEN q = FpX_divrem(quo,fact,p,ONLY_DIVIDES);
          if (!q) break;
          quo = q;
        }
        E[j] = e;
      }
      E[1] = degpol(quo) / degpol(gel(y,1));
      y = gerepileupto(av, QXQXV_to_mod(y, T));
      ex = zc_to_ZC(E); pari_free((void*)E);
    }
  }
  else
  {
    y = gerepileupto(av, QXQXV_to_mod(y, T));
    ex = const_col(n, gen_1);
  }
  gel(rep,1) = y; settyp(y, t_COL);
  gel(rep,2) = ex;
}

/* return the factorization of x in nf */
GEN
nffactor(GEN nf,GEN pol)
{
  GEN bad, A, B, y, T, den, rep = cgetg(3, t_MAT);
  pari_sp av = avma;
  long dA;
  pari_timer ti;

  if (DEBUGLEVEL>2) { TIMERstart(&ti); fprintferr("\nEntering nffactor:\n"); }
  T = get_nfpol(nf, &nf);
  A = fix_relative_pol(T,pol,1);
  dA = degpol(A);
  if (dA <= 0) {
    avma = (pari_sp)(rep + 3);
    return (dA == 0)? trivfact(): zerofact(varn(pol));
  }
  A = Q_primpart( QXQX_normalize(A, T) );
  if (dA == 1) {
    GEN c;
    A = gerepilecopy(av, A); c = gel(A,2);
    if (typ(c) == t_POL && degpol(c) > 0) gel(A,2) = mkpolmod(c, ZX_copy(T));
    gel(rep,1) = mkcol(A);
    gel(rep,2) = mkcol(gen_1); return rep;
  }
  if (degpol(T) == 1) return gerepileupto(av, QX_factor(simplify_shallow(A)));

  den = get_den(&nf, T);
  bad = gel(nf,4); if (den != gen_1) bad = mulii(bad, den);
  (void)nfgcd_all(A, RgX_deriv(A), T, bad, &B);
  if (DEBUGLEVEL>2) msgTIMER(&ti, "squarefree test");
  if (degpol(B) != dA) B = Q_primpart( QXQX_normalize(B, T) );
  ensure_lt_INT(B);
  y = nfsqff(nf,B,0, den);
  if (DEBUGLEVEL>3) fprintferr("number of factor(s) found: %ld\n", lg(y)-1);

  fact_from_sqff(rep, A, B, y, T, bad);
  return sort_factor_pol(rep, cmp_RgX);
}

/* assume x scalar or t_COL */
static GEN
arch_for_T2(GEN G, GEN x)
{
  return (typ(x) == t_COL)? gmul(G,x): gmul(gel(G,1),x);
}
static GEN
arch_for_T2_prec(GEN G, GEN x, long prec)
{
  return (typ(x) == t_COL)? gmul(G, RgC_gtofp(x,prec))
                          : gmul(gel(G,1), gtofp(x, prec));
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
  long prec, i, j, d = degpol(polbase), n = nf_get_degree(nf), r1 = nf_get_r1(nf);

  binlS = bin = vecbinome(d-1);
  if (!gcmp1(lS)) binlS = gmul(lS, bin);

  N2 = cgetg(n+1, t_VEC);
  prec = gprecision(G);
  for (;;)
  {
    nffp_t F;

    matGS = cgetg(d+2, t_MAT);
    for (j=0; j<=d; j++) gel(matGS,j+1) = arch_for_T2(G, gel(polbase,j+2));
    matGS = shallowtrans(matGS);
    for (j=1; j <= r1; j++) /* N2[j] = || sigma_j(S) ||_2 */
    {
      gel(N2,j) = sqrtr( RgC_fpnorml2(gel(matGS,j), DEFAULTPREC) );
      if (lg(N2[j]) < DEFAULTPREC) goto PRECPB;
    }
    for (   ; j <= n; j+=2)
    {
      GEN q1 = RgC_fpnorml2(gel(matGS,j  ), DEFAULTPREC);
      GEN q2 = RgC_fpnorml2(gel(matGS,j+1), DEFAULTPREC);
      p1 = gmul2n(addrr(q1, q2), -1);
      gel(N2,j) = gel(N2,j+1) = sqrtr(p1);
      if (lg(N2[j]) < DEFAULTPREC) goto PRECPB;
    }
    if (j > n) break; /* done */
PRECPB:
    prec = (prec<<1)-2;
    remake_GM(nf, &F, prec); G = F.G;
    if (DEBUGLEVEL>1) pari_warn(warnprec, "nf_factor_bound", prec);
  }

  /* Take sup over 0 <= i <= d of
   * sum_sigma | binom(d-1, i-1) ||sigma(S)||_2 + binom(d-1,i) lc(S) |^2 */

  /* i = 0: n lc(S)^2 */
  C = mului(n, sqri(lS));
  /* i = d: sum_sigma ||sigma(S)||_2^2 */
  p1 = gnorml2(N2); if (gcmp(C, p1) < 0) C = p1;
  for (i = 1; i < d; i++)
  {
    GEN B = gel(bin,i), L = gel(binlS,i+1);
    GEN s = addri(mulir(B, gel(N2,1)),  L); /* j=1 */
    for (j = 2; j <= n; j++) s = addrr(s, sqrr(addri(mulir(B, gel(N2,j)), L)));
    if (mpcmp(C, s) < 0) C = s;
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
  GEN lt, C, s, G = gmael(nf,5,2), POL, bin;
  long i,prec,precnf, d = degpol(polbase), n = nf_get_degree(nf);

  precnf = gprecision(G);
  prec   = MEDDEFAULTPREC;
  bin = vecbinome(d);
  POL = polbase + 2;
  /* compute [POL]_2 */
  for (;;)
  {
    s = real_0(prec);
    for (i=0; i<=d; i++)
    {
      GEN p1 = gnorml2(arch_for_T2_prec(G, gel(POL,i), prec));
      if (!signe(p1)) continue;
      if (lg(p1) == 3) break;
      /* s += T2(POL[i]) / binomial(d,i) */
      s = addrr(s, gdiv(p1, gel(bin,i+1)));
    }
    if (i > d) break;

    prec = (prec<<1)-2;
    if (prec > precnf)
    {
      nffp_t F; remake_GM(nf, &F, prec); G = F.G;
      if (DEBUGLEVEL>1) pari_warn(warnprec, "nf_factor_bound", prec);
    }
  }
  lt = leading_term(polbase);
  s = mulri(s, muliu(sqri(lt), n));
  C = powruhalf(stor(3,DEFAULTPREC), 3 + 2*d); /* 3^{3/2 + d} */
  return divrr(mulrr(C, s), mulsr(d, mppi(DEFAULTPREC)));
}

static GEN
nf_factor_bound(GEN nf, GEN polbase)
{
  pari_sp av = avma;
  GEN a = nf_Mignotte_bound(nf, polbase);
  GEN b = nf_Beauzamy_bound(nf, polbase);
  if (DEBUGLEVEL>2)
  {
    fprintferr("Mignotte bound: %Ps\n",a);
    fprintferr("Beauzamy bound: %Ps\n",b);
  }
  return gerepileupto(av, gmin(a, b));
}

/* return Bs: if r a root of sigma_i(P), |r| < Bs[i] */
static GEN
nf_root_bounds(GEN P, GEN T)
{
  long lR, i, j, l, prec;
  GEN Ps, R, V, nf;

  if (RgX_is_rational(P)) return logmax_modulus_bound(P);
  T = get_nfpol(T, &nf);

  P = Q_primpart(P);
  prec = ZXY_max_lg(P) + 1;
  l = lg(P);
  if (nf && nf_get_prec(nf) >= prec)
    R = gel(nf,6);
  else
    R = cleanroots(T, prec);
  lR = lg(R);
  V = cgetg(lR, t_VEC);
  Ps = cgetg(l, t_POL); /* sigma (P) */
  Ps[1] = P[1];
  for (j=1; j<lg(R); j++)
  {
    GEN r = gel(R,j);
    for (i=2; i<l; i++) gel(Ps,i) = poleval(gel(P,i), r);
    gel(V,j) = logmax_modulus_bound(Ps);
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
  GEN nf, M, L, prep, den = *ptden;
  long prec;

  T = get_nfpol(T, &nf);
  prec = ZX_max_lg(T) + ZM_max_lg(tozk);
  (void)initgaloisborne(T, den, prec, &L, &prep, NULL);
  M = vandermondeinverse(L, RgX_gtofp(T,prec), den, prep);
  if (nf) M = RgM_mul(tozk, M);
  if (is_pm1(den)) den = NULL;
  *ptden = den;
  return RgM_fpnorml2(M, DEFAULTPREC);
}

/* || L ||_p^p in dimension n (L may be a scalar) */
static GEN
normlp(GEN L, long p, long n)
{
  long i,l, t = typ(L);
  GEN z;

  if (!is_vec_t(t)) return gmulsg(n, gpowgs(L, p));

  l = lg(L); z = gen_0;
  /* assert(n == l-1); */
  for (i=1; i<l; i++)
    z = gadd(z, gpowgs(gel(L,i), p));
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

  s = gel(T->S1, ind[1]);
  if (K == 1) return s;

  /* compute s = S1 u */
  for (j=2; j<=K; j++) s = ZC_add(s, gel(T->S1, ind[j]));

  /* compute v := - round(P^1 S u) */
  l = lg(s);
  v = cgetg(l, t_VECSMALL);
  for (i=1; i<l; i++)
  {
    double r, t = 0.;
    /* quick approximate computation */
    for (j=1; j<=K; j++) t += T->PinvSdbl[ ind[j] ][i];
    r = floor(t + 0.5);
    if (fabs(t + 0.5 - r) < 0.0001)
    { /* dubious, compute exactly */
      z = gen_0;
      for (j=1; j<=K; j++) z = addii(z, ((GEN**)T->dPinvS)[ ind[j] ][i]);
      v[i] = - itos( diviiround(z, T->d) );
    }
    else
      v[i] = - (long)r;
  }
  return ZC_add(s, ZM_zc_mul(T->P1, v));
}

static trace_data *
init_trace(trace_data *T, GEN S, nflift_t *L, GEN q)
{
  long e = gexpo(S), i,j, l,h;
  GEN qgood, S1, invd;

  if (e < 0) return NULL; /* S = 0 */

  qgood = int2n(e - 32); /* single precision check */
  if (cmpii(qgood, q) > 0) q = qgood;

  S1 = gdivround(S, q);
  if (gcmp0(S1)) return NULL;

  invd = invr(itor(L->den, DEFAULTPREC));

  T->dPinvS = ZM_mul(L->iprk, S);
  l = lg(S);
  h = lg(T->dPinvS[1]);
  T->PinvSdbl = (double**)cgetg(l, t_MAT);
  init_dalloc();
  for (j = 1; j < l; j++)
  {
    double *t = dalloc(h * sizeof(double));
    GEN c = gel(T->dPinvS,j);
    pari_sp av = avma;
    T->PinvSdbl[j] = t;
    for (i=1; i < h; i++) t[i] = rtodbl(mulri(invd, gel(c,i)));
    avma = av;
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
  y = FpXQX_red(z, T, pk); l = lg(y);
  for (i = 2; i < l; i++)
  {
    GEN c = gel(y,i);
    if (typ(c) == t_INT)
      c = centermodii(c, pk, pks2);
    else
      c = FpX_center(c, pk, pks2);
    gel(y,i) = c;
  }
  return y;
}

/* Naive recombination of modular factors: combine up to maxK modular
 * factors, degree <= klim
 *
 * target = polynomial we want to factor
 * famod = array of modular factors.  Product should be congruent to
 * target/lc(target) modulo p^a
 * For true factors: S1,S2 <= p^b, with b <= a and p^(b-a) < 2^31 */
static GEN
nfcmbf(nfcmbf_t *T, GEN p, long a, long maxK, long klim)
{
  GEN pol = T->pol, nf = T->nf, famod = T->fact, dn = T->dn;
  GEN bound = T->bound;
  GEN nfpol = gel(nf,1);
  long K = 1, cnt = 1, i,j,k, curdeg, lfamod = lg(famod)-1, dnf = degpol(nfpol);
  GEN res = cgetg(3, t_VEC);
  pari_sp av0 = avma;
  GEN pk = powiu(p,a), pks2 = shifti(pk,-1);

  GEN ind      = cgetg(lfamod+1, t_VECSMALL);
  GEN deg      = cgetg(lfamod+1, t_VECSMALL);
  GEN degsofar = cgetg(lfamod+1, t_VECSMALL);
  GEN listmod  = cgetg(lfamod+1, t_COL);
  GEN fa       = cgetg(lfamod+1, t_COL);
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
    GEN q = ceil_safe(sqrtr(T->BS_2));
    GEN t1,t2, ltdn, lt2dn;
    GEN trace1   = cgetg(lfamod+1, t_MAT);
    GEN trace2   = cgetg(lfamod+1, t_MAT);

    ltdn = mul_content(lt, dn);
    lt2dn= mul_content(ltdn, lt);

    for (i=1; i <= lfamod; i++)
    {
      pari_sp av = avma;
      GEN P = gel(famod,i);
      long d = degpol(P);

      deg[i] = d; P += 2;
      t1 = gel(P,d-1);/* = - S_1 */
      t2 = gsqr(t1);
      if (d > 1) t2 = gsub(t2, gmul2n(gel(P,d-2), 1));
      /* t2 = S_2 Newton sum */
      t2 = typ(t2)!=t_INT? FpX_rem(t2, Tpk, pk): modii(t2, pk);
      if (lt)
      {
	if (typ(t2)!=t_INT) {
	  t1 = FpX_Fp_mul(t1, ltdn, pk);
	  t2 = FpX_Fp_mul(t2, lt2dn, pk);
	} else {
	  t1 = Fp_mul(t1, ltdn, pk);
	  t2 = Fp_mul(t2, lt2dn, pk);
	}
      }
      gel(trace1,i) = gclone( nf_bestlift(t1, NULL, T->L) );
      gel(trace2,i) = gclone( nf_bestlift(t2, NULL, T->L) ); avma = av;
    }
    T1 = init_trace(&_T1, trace1, T->L, q);
    T2 = init_trace(&_T2, trace2, T->L, q);
    for (i=1; i <= lfamod; i++) {
      gunclone(gel(trace1,i));
      gunclone(gel(trace2,i));
    }
  }
  degsofar[0] = 0; /* sentinel */

  /* ind runs through strictly increasing sequences of length K,
   * 1 <= ind[i] <= lfamod */
nextK:
  if (K > maxK || 2*K > lfamod) goto END;
  if (DEBUGLEVEL > 3)
    fprintferr("\n### K = %d, %Ps combinations\n", K,binomial(utoipos(lfamod), K));
  setlg(ind, K+1); ind[1] = 1;
  i = 1; curdeg = deg[ind[1]];
  for(;;)
  { /* try all combinations of K factors */
    for (j = i; j < K; j++)
    {
      degsofar[j] = curdeg;
      ind[j+1] = ind[j]+1; curdeg += deg[ind[j+1]];
    }
    if (curdeg <= klim) /* trial divide */
    {
      GEN t, y, q, list;
      pari_sp av;

      av = avma;
      /* d - 1 test */
      if (T1)
      {
	t = get_trace(ind, T1);
	if (rtodbl(RgC_fpnorml2(t,DEFAULTPREC)) > Bhigh)
	{
	  if (DEBUGLEVEL>6) fprintferr(".");
	  avma = av; goto NEXT;
	}
      }
      /* d - 2 test */
      if (T2)
      {
	t = get_trace(ind, T2);
	if (rtodbl(RgC_fpnorml2(t,DEFAULTPREC)) > Bhigh)
	{
	  if (DEBUGLEVEL>3) fprintferr("|");
	  avma = av; goto NEXT;
	}
      }
      avma = av;
      y = lt; /* full computation */
      for (i=1; i<=K; i++)
      {
	GEN q = gel(famod, ind[i]);
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
      q = RgXQX_divrem(C2ltpol, y, nfpol, ONLY_DIVIDES);
      if (!q)
      {
	if (DEBUGLEVEL>3) fprintferr("*");
	avma = av; goto NEXT;
      }

      /* found a factor */
      list = cgetg(K+1, t_VEC);
      gel(listmod,cnt) = list;
      for (i=1; i<=K; i++) list[i] = famod[ind[i]];

      y = Q_primpart(y);
      gel(fa,cnt++) = QXQX_normalize(y, nfpol);
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
	  deg[k] = deg[i]; k++;
	}
      }
      lfamod -= K;
      if (lfamod < 11) maxK = lfamod-1;
      if (lfamod < 2*K) goto END;
      i = 1; curdeg = deg[ind[1]];

      if (C2lt) pol = Q_primpart(pol);
      if (lt) lt = absi(leading_term(pol));
      Clt  = mul_content(C, lt);
      C2lt = mul_content(C,Clt);
      C2ltpol = C2lt? gmul(C2lt,pol): pol;
      if (DEBUGLEVEL > 2)
      {
	fprintferr("\n"); msgTIMER(&ti, "to find factor %Ps",y);
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
  if (degpol(pol) > 0)
  { /* leftover factor */
    if (signe(leading_term(pol)) < 0) pol = gneg_i(pol);

    if (C2lt && lfamod < 2*K) pol = QXQX_normalize(Q_primpart(pol), nfpol);
    setlg(famod, lfamod+1);
    gel(listmod,cnt) = leafcopy(famod);
    gel(fa,cnt++) = pol;
  }
  if (DEBUGLEVEL>6) fprintferr("\n");
  if (cnt == 2) {
    avma = av0;
    gel(res,1) = mkvec(T->pol);
    gel(res,2) = mkvec(T->fact);
  }
  else
  {
    setlg(listmod, cnt); setlg(fa, cnt);
    gel(res,1) = fa;
    gel(res,2) = listmod;
    res = gerepilecopy(av0, res);
  }
  return res;
}

static GEN
nf_chk_factors(nfcmbf_t *T, GEN P, GEN M_L, GEN famod, GEN pk)
{
  GEN nf = T->nf, bound = T->bound;
  GEN nfT = gel(nf,1);
  long i, r;
  GEN pol = P, list, piv, y;
  GEN C2ltpol, C = T->L->topowden, Tpk = T->L->Tpk;
  GEN lc = absi(leading_term(pol)), lt = is_pm1(lc)? NULL: lc;
  GEN Clt  = mul_content(C, lt);
  GEN C2lt = mul_content(C,Clt);

  piv = special_pivot(M_L);
  if (!piv) return NULL;
  if (DEBUGLEVEL>3) fprintferr("special_pivot output:\n%Ps\n",piv);

  r  = lg(piv)-1;
  list = cgetg(r+1, t_COL);
  C2ltpol = C2lt? gmul(C2lt,pol): pol;
  for (i = 1;;)
  {
    pari_sp av = avma;
    if (DEBUGLEVEL)
      fprintferr("nf_LLL_cmbf: checking factor %ld (avma - bot = %lu)\n",
		 i, avma - bot);
    y = chk_factors_get(lt, famod, gel(piv,i), Tpk, pk);
    if (DEBUGLEVEL>2) fprintferr("... mod p^k (avma - bot = %lu)\n", avma-bot);

    if (! (y = nf_pol_lift(y, bound, T)) ) return NULL;
    if (DEBUGLEVEL>2) fprintferr("... lifted (avma - bot = %lu)\n", avma-bot);

    y = gerepilecopy(av, y);
    /* y is the candidate factor */
    pol = RgXQX_divrem(C2ltpol, y, nfT, ONLY_DIVIDES);
    if (!pol) return NULL;

    y = Q_primpart(y);
    gel(list,i) = QXQX_normalize(y, nfT);
    if (++i >= r) break;

    if (C2lt) pol = Q_primpart(pol);
    if (lt) lt = absi(leading_term(pol));
    Clt  = mul_content(C, lt);
    C2lt = mul_content(C,Clt);
    C2ltpol = C2lt? gmul(C2lt,pol): pol;
  }
  y = Q_primpart(pol);
  gel(list,i) = QXQX_normalize(y, nfT); return list;
}

static GEN
nf_to_Zq(GEN x, GEN T, GEN pk, GEN pks2, GEN proj)
{
  GEN y;
  if (typ(x) != t_COL) return centermodii(x, pk, pks2);
  if (!T)
  {
    y = ZV_dotproduct(proj, x);
    return centermodii(y, pk, pks2);
  }
  y = ZM_ZC_mul(proj, x);
  y = RgV_to_RgX(y, varn(T));
  return FpX_center(FpX_rem(y, T, pk), pk, pks2);
}

/* Assume P in nfX form, lc(P) != 0 mod p. Reduce P to Zp[X]/(T) mod p^a */
static GEN
ZqX(GEN P, GEN pk, GEN T, GEN proj)
{
  long i, l = lg(P);
  GEN z, pks2 = shifti(pk,-1);

  z = cgetg(l,t_POL); z[1] = P[1];
  for (i=2; i<l; i++) gel(z,i) = nf_to_Zq(gel(P,i),T,pk,pks2,proj);
  return normalizepol_lg(z, l);
}

static GEN
ZqX_normalize(GEN P, GEN lt, nflift_t *L)
{
  GEN R = lt? gmul(Fp_inv(lt, L->pk), P): P;
  return ZqX(R, L->pk, L->Tpk, L->ZqProj);
}

/* We want to be able to reconstruct x, |x|^2 < C, from x mod pr^k */
static double
bestlift_bound(GEN C, long d, double alpha, GEN Npr)
{
  const double y = 1 / (alpha - 0.25); /* = 2 if alpha = 3/4 */
  double t;
  C = gtofp(C,DEFAULTPREC);
  /* (1/2)log (4C/d) + (d-1)(log 3/2 sqrt(gamma)) */
  t = rtodbl(mplog(gmul2n(divru(C,d), 2))) * 0.5 + (d-1) * log(1.5 * sqrt(y));
  return ceil((t * d) / log(gtodouble(Npr)));
}

static GEN
get_R(GEN M)
{
  GEN R;
  long i, l, prec = DEFAULTPREC + divsBIL( gexpo(M) );

  for(;;)
  {
    R = Q_from_QR(M, prec);
    if (R) break;
    prec = (prec-1)<<1;
  }
  l = lg(R);
  for (i=1; i<l; i++) gcoeff(R,i,i) = gen_1;
  return R;
}

static void
init_proj(nflift_t *L, GEN nfT, GEN p)
{
  if (L->Tp)
  {
    GEN z = cgetg(3, t_VEC), proj;
    gel(z,1) = L->Tp;
    gel(z,2) = FpX_div(FpX_red(nfT,p), L->Tp, p);
    z = ZpX_liftfact(nfT, z, NULL, p, L->k, L->pk);
    L->Tpk = gel(z,1);
    proj = get_proj_modT(L->topow, L->Tpk, L->pk);
    if (L->topowden)
      proj = FpM_red(ZM_Z_mul(proj, Fp_inv(L->topowden, L->pk)), L->pk);
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
  const double alpha = 0.99; /* LLL parameter */
  const long d = nf_get_degree(nf);
  pari_sp av = avma, av2;
  GEN prk, PRK, B, GSmin, pk;
  pari_timer ti;

  TIMERstart(&ti);
  if (!a) a = (long)bestlift_bound(C, d, alpha, pr_norm(pr));

  for (;; avma = av, a<<=1)
  {
    GEN S, smax = gen_0;
    long i, j;
    if (DEBUGLEVEL>2) fprintferr("exponent: %ld\n",a);
    prk = idealpows(nf, pr, a);
    av2 = avma;
    pk = gcoeff(prk,1,1);
    PRK = ZM_lll_norms(prk, alpha, LLL_INPLACE, &B);
    S = RgM_inv( get_R(PRK) ); if (!S) continue;
    for (i=1; i<=d; i++)
    {
      GEN s = gen_0;
      for (j=1; j<=d; j++)
        s = gadd(s, gdiv( gsqr(gcoeff(S,i,j)), gel(B,j)));
      if (gcmp(s, smax) > 0) smax = s;
    }
    GSmin = ginv(gmul2n(smax, 2));
    if (gcmp(GSmin, C) >= 0) break;
  }
  gerepileall(av2, 2, &PRK, &GSmin);
  if (DEBUGLEVEL>2)
    fprintferr("for this exponent, GSmin = %Ps\nTime reduction: %ld\n",
      GSmin, TIMER(&ti));
  L->k = a;
  L->den = L->pk = pk;
  L->prk = PRK;
  L->iprk = ZM_inv(PRK, pk);
  L->GSmin= GSmin;
  L->prkHNF = prk;
  init_proj(L, gel(nf,1), pr_get_p(pr));
}

/* Let X = Tra * M_L, Y = bestlift(X) return V s.t Y = X - PRK V
 * and set *eT2 = gexpo(Y)  [cf nf_bestlift, but memory efficient] */
static GEN
get_V(GEN Tra, GEN M_L, GEN PRK, GEN PRKinv, GEN pk, long *eT2)
{
  long i, e = 0, l = lg(M_L);
  GEN V = cgetg(l, t_MAT);
  *eT2 = 0;
  for (i = 1; i < l; i++)
  { /* cf nf_bestlift(Tra * c) */
    pari_sp av = avma, av2;
    GEN v, T2 = ZM_ZC_mul(Tra, gel(M_L,i));

    v = gdivround(ZM_ZC_mul(PRKinv, T2), pk); /* small */
    av2 = avma;
    T2 = ZC_sub(T2, ZM_ZC_mul(PRK, v));
    e = gexpo(T2); if (e > *eT2) *eT2 = e;
    avma = av2;
    gel(V,i) = gerepileupto(av, v); /* small */
  }
  return V;
}

static GEN
nf_LLL_cmbf(nfcmbf_t *T, GEN p, long k, long rec)
{
  nflift_t *L = T->L;
  GEN pk = L->pk, PRK = L->prk, PRKinv = L->iprk, GSmin = L->GSmin;
  GEN Tpk = L->Tpk;

  GEN famod = T->fact, nf = T->nf, ZC = T->ZC, Br = T->Br;
  GEN Pbase = T->polbase, P = T->pol, dn = T->dn;
  GEN nfT = gel(nf,1);
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
  CM_L = scalarmat_s(C, n0);
  /* tmax = current number of traces used (and computed so far) */
  for(tmax = 0;; tmax++)
  {
    long a, b, bmin, bgood, delta, tnew = tmax + 1, r = lg(CM_L)-1;
    GEN oldCM_L, M_L, q, S1, P1, VV;
    int first = 1;

    /* bound for f . S_k(genuine factor) = ZC * bound for T_2(S_tnew) */
    Btra = mulrr(ZC, mulsr(dP*dP, normlp(Br, 2*tnew, dnf)));
    bmin = logint(ceil_safe(sqrtr(Btra)), gen_2, NULL);
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
      famod = ZpX_liftfact(polred, famod, Tpk, p, k, pk);
      for (i=1; i<=n0; i++) TT[i] = 0;
    }
    for (i=1; i<=n0; i++)
    {
      GEN h, lPpow = lP? powiu(lP, tnew): NULL;
      GEN z = polsym_gen(gel(famod,i), gel(TT,i), tnew, Tpk, pk);
      gel(TT,i) = z;
      h = gel(z,tnew+1);
      /* make Newton sums integral */
      lPpow = mul_content(lPpow, dn);
      if (lPpow)
        h = (typ(h) == t_INT)? Fp_mul(h, lPpow, pk): FpX_Fp_mul(h, lPpow, pk);
      gel(Tra,i) = nf_bestlift(h, NULL, L); /* S_tnew(famod) */
    }

    /* compute truncation parameter */
    if (DEBUGLEVEL>2) { TIMERstart(&ti2); TIMERstart(&TI); }
    oldCM_L = CM_L;
    av2 = avma;
    b = delta = 0; /* -Wall */
AGAIN:
    M_L = Q_div_to_int(CM_L, utoipos(C));
    VV = get_V(Tra, M_L, PRK, PRKinv, pk, &a);
    if (first)
    { /* initialize lattice, using few p-adic digits for traces */
      bgood = (long)(a - maxss(32, (long)(BitPerFactor * r)));
      b = maxss(bmin, bgood);
      delta = a - b;
    }
    else
    { /* add more p-adic digits and continue reduction */
      if (a < b) b = a;
      b = maxss(b-delta, bmin);
      if (b - delta/2 < bmin) b = bmin; /* near there. Go all the way */
    }

    /* restart with truncated entries */
    q = int2n(b);
    P1 = gdivround(PRK, q);
    S1 = gdivround(Tra, q);
    T2 = ZM_sub(ZM_mul(S1, M_L), ZM_mul(P1, VV));
    m = vconcat( CM_L, T2 );
    if (first)
    {
      first = 0;
      m = shallowconcat( m, vconcat(ZERO, P1) );
      /*     [ C M_L   0  ]
       * m = [            ]   square matrix
       *     [  T2'   PRK ]   T2' = Tra * M_L  truncated
       */
    }
    CM_L = LLL_check_progress(Bnorm, n0, m, b == bmin, /*dbg:*/ &ti_LLL);
    if (DEBUGLEVEL>2)
      fprintferr("LLL_cmbf: (a,b) =%4ld,%4ld; r =%3ld -->%3ld, time = %ld\n",
		 a,b, lg(m)-1, CM_L? lg(CM_L)-1: 1, TIMER(&TI));
    if (!CM_L) { list = mkcol(QXQX_normalize(P,nfT)); break; }
    if (b > bmin)
    {
      CM_L = gerepilecopy(av2, CM_L);
      goto AGAIN;
    }
    if (DEBUGLEVEL>2) msgTIMER(&ti2, "for this trace");

    i = lg(CM_L) - 1;
    if (i == r && ZM_equal(CM_L, oldCM_L))
    {
      CM_L = oldCM_L;
      avma = av2; continue;
    }

    if (i <= r && i*rec < n0)
    {
      pari_timer ti;
      if (DEBUGLEVEL>2) TIMERstart(&ti);
      list = nf_chk_factors(T, P, Q_div_to_int(CM_L,utoipos(C)), famod, pk);
      if (DEBUGLEVEL>2) ti_CF += TIMER(&ti);
      if (list) break;
    }
    CM_L = gerepilecopy(av2, CM_L);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"nf_LLL_cmbf");
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
  GEN res, L, listmod, famod = T->fact, nf = T->nf;
  long l, maxK = 3, nft = lg(famod)-1;
  pari_timer ti;

  if (DEBUGLEVEL>2) TIMERstart(&ti);
  T->fact = ZpX_liftfact(polred, famod, T->L->Tpk, p, a, T->L->pk);
  if (nft < 11) maxK = -1; /* few modular factors: try all posibilities */
  if (DEBUGLEVEL>2) msgTIMER(&ti, "Hensel lift");

  L = nfcmbf(T, p, a, maxK, klim);
  if (DEBUGLEVEL>2) msgTIMER(&ti, "Naive recombination");

  res     = gel(L,1);
  listmod = gel(L,2); l = lg(listmod)-1;
  famod = gel(listmod,l);
  if (maxK >= 0 && lg(famod)-1 > 2*maxK)
  {
    if (l > 1)
    {
      T->pol = gel(res,l);
      T->polbase = RgX_to_nfX(nf, gel(res,l));
    }
    L = nf_LLL_cmbf(T, p, a, maxK);
    /* remove last elt, possibly unfactored. Add all new ones. */
    setlg(res, l); res = shallowconcat(res, L);
  }
  return res;
}

static GEN
nf_DDF_roots(GEN pol, GEN polred, GEN nfpol, GEN ltdn, GEN init_fa, long nbf,
	     long fl, nflift_t *L)
{
  GEN z, Cltdnx_r, C2ltdnpol, C = L->topowden;
  GEN Cltdn  = mul_content(C, ltdn);
  GEN C2ltdn = mul_content(C,Cltdn);
  long i, m;

  if (L->Tpk)
  {
    int cof = (degpol(pol) > nbf); /* non trivial cofactor ? */
    z = FqX_split_roots(init_fa, L->Tp, L->p, cof? polred: NULL);
    z = ZpX_liftfact(polred, z, L->Tpk, L->p, L->k, L->pk);
    if (cof) setlg(z, lg(z)-1); /* remove cofactor */
    z = roots_from_deg1(z);
  }
  else
    z = rootpadicfast(polred, L->p, L->k);
  Cltdnx_r = deg1pol_shallow(Cltdn? Cltdn: gen_1, NULL, varn(pol));
  C2ltdnpol  = C2ltdn? gmul(C2ltdn, pol): pol;
  for (m=1,i=1; i<lg(z); i++)
  {
    GEN q, r = gel(z,i);

    r = nf_bestlift_to_pol(ltdn? gmul(ltdn,r): r, NULL, L);
    gel(Cltdnx_r,2) = gneg(r); /* check P(r) == 0 */
    q = RgXQX_divrem(C2ltdnpol, Cltdnx_r, nfpol, ONLY_DIVIDES); /* integral */
    if (q) {
      C2ltdnpol = C2ltdn? gmul(Cltdn,q): q;
      if (Cltdn) r = gdiv(r, Cltdn);
      gel(z,m++) = r;
    }
    else if (fl == 2) return cgetg(1, t_VEC);
  }
  z[0] = evaltyp(t_VEC) | evallg(m);
  return z;
}

static long
nf_pick_prime(long ct, GEN nf, GEN polbase, long fl,
	      GEN *lt, GEN *Fa, GEN *pr, GEN *Tp)
{
  GEN nfpol = gel(nf,1), dk, bad;
  long maxf, n = degpol(nfpol), dpol = degpol(polbase), nbf = 0;
  byteptr pt = diffptr;
  ulong pp = 0;

  *lt  = leading_term(polbase); /* t_INT */
  if (gcmp1(*lt)) *lt = NULL;
  dk = absi(gel(nf,3));
  bad = mulii(dk,gel(nf,4)); if (*lt) bad = mulii(bad, *lt);

  /* FIXME: slow factorization of large polynomials over large Fq */
  maxf = 1;
  if (ct > 1) {
    if (dpol > 100) /* tough */
    {
      if (n >= 20) maxf = 4;
    }
    else
    {
      if (n >= 15) maxf = 4;
    }
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
      ap = utoipos(pp);
      list = gel(FpX_factor(nfpol, ap),1);
      if (maxf == 1)
      { /* deg.1 factors are best */
	r = gel(list,1);
	if (degpol(r) == 1) break;
      }
      else
      { /* otherwise, pick factor of largish degree */
	long i, dr;
	for (i = lg(list)-1; i > 0; i--)
	{
	  r = gel(list,i); dr = degpol(r);
	  if (dr <= maxf) break;
	}
	if (i > 0) break;
      }
      avma = av2;
    }
    apr = primedec_apply_kummer(nf,r,1,ap);

    modpr = zk_to_Fq_init(nf,&apr,&aT,&ap);
    red = nfX_to_FqX(polbase, nf, modpr);
    if (!aT)
    { /* degree 1 */
      red = ZX_to_Flx(red, pp);
      if (!Flx_is_squarefree(red, pp)) { avma = av2; continue; }
      anbf = fl? Flx_nbroots(red, pp): Flx_nbfact(red, pp);
    }
    else
    {
      GEN q;
      if (!FqX_is_squarefree(red,aT,ap)) { avma = av2; continue; }
      q = powiu(ap, degpol(aT));
      anbf = fl? FqX_split_deg1(&fa, red, q, aT, ap)
	       : FqX_split_by_degree(&fa, red, q, aT, ap);
    }
    if (fl == 2 && anbf < dpol) return anbf;
    if (anbf <= 1)
    {
      if (!fl) return anbf; /* irreducible */
      if (!anbf) return 0; /* no root */
    }

    if (!nbf || anbf < nbf
	     || (anbf == nbf && pr_get_f(apr) > pr_get_f(*pr)))
    {
      nbf = anbf;
      *pr = apr;
      *Tp = aT;
      *Fa = fa;
    }
    else avma = av2;
    if (DEBUGLEVEL>3)
      fprintferr("%3ld %s at prime\n  %Ps\nTime: %ld\n",
		 anbf, fl?"roots": "factors", apr, TIMER(&ti_pr));
    if (--ct <= 0) return nbf;
  }
}

/* assume lt(T) is a t_INT and T square free */
static GEN
nfsqff_trager(GEN u, GEN T, GEN dent)
{
  long k = 0, i, lx;
  GEN P, x0, fa, n = ZX_ZXY_rnfequation(T, u, &k);
  int tmonic;
  if (DEBUGLEVEL>4) fprintferr("nfsqff_trager: choosing k = %ld\n",k);

  /* n guaranteed to be squarefree */
  fa = ZX_DDF(Q_primpart(n)); lx = lg(fa);
  if (lx == 2) return mkcol(u);

  tmonic = is_pm1(leading_term(T));
  P = cgetg(lx,t_COL);
  x0 = deg1pol_shallow(stoi(-k), gen_0, varn(T));
  for (i=lx-1; i>0; i--)
  {
    GEN f = gel(fa,i), F = RgXQX_translate(f, x0, T);
    if (!tmonic) F = Q_primpart(F);
    F = nfgcd(u, F, T, dent);
    if (typ(F) != t_POL || degpol(F) == 0)
      pari_err(talker,"reducible modulus in factornf");
    gel(P,i) = QXQX_normalize(F, T);
  }
  return P;
}

/* Factor polynomial a on the number field defined by polynomial T, using
 * Trager's trick */
GEN
polfnf(GEN a, GEN T)
{
  GEN rep = cgetg(3, t_MAT), A, B, y, dent, bad;
  long dA;
  int tmonic;

  if (typ(a)!=t_POL || typ(T)!=t_POL) pari_err(typeer,"polfnf");
  T = Q_primpart(T); tmonic = is_pm1(leading_term(T));
  A = Q_primpart( QXQX_normalize(fix_relative_pol(T,a,1), T) );
  dA = degpol(A);
  if (dA <= 0)
  {
    avma = (pari_sp)(rep + 3);
    return (dA == 0)? trivfact(): zerofact(varn(A));
  }
  bad = dent = ZX_disc(T);
  if (tmonic) dent = indexpartial(T, dent);
  (void)nfgcd_all(A,RgX_deriv(A), T, dent, &B);
  if (degpol(B) != dA) B = Q_primpart( QXQX_normalize(B, T) );
  ensure_lt_INT(B);
  y = nfsqff_trager(B, T, dent);
  fact_from_sqff(rep, A, B, y, T, bad);
  return sort_factor_pol(rep, cmp_RgX);
}

/* return the factorization of the square-free polynomial pol. Not memory-clean
   The coeffs of pol are in Z_nf and its leading term is a rational integer.
   deg(pol) > 0, deg(nfpol) > 1
   If fl = 1, return only the roots of x in nf
   If fl = 2, as fl=1 if pol splits, [] otherwise
   den is usually 1, otherwise nf.zk is doubtful, and den bounds the
   denominator of an arbitrary element of Z_nf on nf.zk */
static GEN
nfsqff(GEN nf, GEN pol, long fl, GEN den)
{
  long n, nbf, dpol = degpol(pol);
  GEN pr, C0, polbase, init_fa = NULL;
  GEN N2, res, polred, lt, nfpol = gel(nf,1);
  nfcmbf_t T;
  nflift_t L;
  pari_timer ti, ti_tot;

  if (DEBUGLEVEL>2) { TIMERstart(&ti); TIMERstart(&ti_tot); }
  n = degpol(nfpol);
  /* deg = 1 => irreducible */
  if (dpol == 1) return mkvec(QXQX_normalize(pol, nfpol));
  /* heuristic */
  if (dpol*3 < n)
  {
    GEN z;
    if (DEBUGLEVEL>2) fprintferr("Using Trager's method\n");
    z = nfsqff_trager(Q_primpart(pol), nfpol, mulii(den,gel(nf,4)));
    if (fl) {
      long i, l = lg(z);
      for (i = 1; i < l; i++)
      {
	GEN LT, t = gel(z,i); if (degpol(t) > 1) break;
        LT = gel(t,3);
        if (typ(LT) == t_POL) LT = gel(LT,2); /* constant */
	gel(z,i) = gdiv(gel(t,2), negi(LT));
      }
      setlg(z, i);
      if (fl == 2 && i != l) return cgetg(1,t_VEC);
    }
    return z;
  }

  polbase = RgX_to_nfX(nf, pol);
  nbf = nf_pick_prime(5, nf, polbase, fl, &lt, &init_fa, &pr, &L.Tp);
  if (fl == 2 && nbf < dpol) return cgetg(1,t_VEC);
  if (nbf <= 1)
  {
    if (!fl) return mkvec(QXQX_normalize(pol, nfpol)); /* irreducible */
    if (!nbf) return cgetg(1,t_VEC); /* no root */
  }

  if (DEBUGLEVEL>2) {
    msgTIMER(&ti, "choice of a prime ideal");
    fprintferr("Prime ideal chosen: %Ps\n", pr);
  }
  L.tozk = gel(nf,8);
  L.topow= Q_remove_denom(gel(nf,7), &L.topowden);
  T.dn = den; /* override */
  T.ZC = L2_bound(nf, L.tozk, &(T.dn));
  T.Br = nf_root_bounds(pol, nf); if (lt) T.Br = gmul(T.Br, lt);

  if (fl) C0 = normlp(T.Br, 2, n);
  else    C0 = nf_factor_bound(nf, polbase); /* bound for T_2(Q_i), Q | P */
  T.bound = mulrr(T.ZC, C0); /* bound for |Q_i|^2 in Z^n on chosen Z-basis */

  N2 = mulsr(dpol*dpol, normlp(T.Br, 4, n)); /* bound for T_2(lt * S_2) */
  T.BS_2 = mulrr(T.ZC, N2); /* bound for |S_2|^2 on chosen Z-basis */

  if (DEBUGLEVEL>2) {
    msgTIMER(&ti, "bound computation");
    fprintferr("  1) T_2 bound for %s: %Ps\n", fl?"root":"factor", C0);
    fprintferr("  2) Conversion from T_2 --> | |^2 bound : %Ps\n", T.ZC);
    fprintferr("  3) Final bound: %Ps\n", T.bound);
  }

  L.p = pr_get_p(pr);
  if (L.Tp && degpol(L.Tp) == 1) L.Tp = NULL;
  bestlift_init(0, nf, pr, T.bound, &L);
  if (DEBUGLEVEL>2) TIMERstart(&ti);
  polred = ZqX_normalize(polbase, lt, &L); /* monic */

  if (fl) {
    GEN z = nf_DDF_roots(pol, polred, nfpol, mul_content(lt, T.dn),
                         init_fa, nbf, fl, &L);
    if (lg(z) == 1) return cgetg(1, t_VEC);
    return z;
  }

  {
    pari_sp av = avma;
    if (L.Tp)
      res = FqX_split_all(init_fa, L.Tp, L.p);
    else
    {
      long d;
      res = cgetg(dpol + 1, t_VEC); gel(res,1) = FpX_red(polred,L.p);
      d = FpX_split_Berlekamp((GEN*)(res + 1), L.p);
      setlg(res, d + 1);
    }
    gen_sort_inplace(res, (void*)&cmp_RgX, &gen_cmp_RgX, NULL);
    T.fact  = gerepilecopy(av, res);
  }
  if (DEBUGLEVEL>2) msgTIMER(&ti, "splitting mod %Ps", pr);
  T.pr = pr;
  T.L  = &L;
  T.polbase = polbase;
  T.pol   = pol;
  T.nf    = nf;
  res = nf_combine_factors(&T, polred, L.p, L.k, dpol-1);
  if (DEBUGLEVEL>2)
    fprintferr("Total Time: %ld\n===========\n", TIMER(&ti_tot));
  return res;
}

/* assume pol monic in nf.zk[X] */
GEN
nfrootsall_and_pr(GEN nf, GEN pol)
{
  GEN J1,J2, pr, T = get_nfpol(nf,&nf), den = get_den(&nf, T);
  pari_sp av = avma;
  GEN z = gerepilecopy(av, nfsqff(nf, pol, 2, den));
  if (lg(z) == 1) return NULL;
  (void)nf_pick_prime(1, nf, RgX_to_nfX(nf, pol), 2,
		      &J1, &J2, &pr, &T);
  return mkvec3(z, pr, nf);
}
