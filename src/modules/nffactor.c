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

extern GEN FqX_gcd(GEN P, GEN Q, GEN T, GEN p);
extern double bound_vS(long tmax, GEN *BL);
extern GEN GS_norms(GEN B, long prec);
extern GEN lllgramint_i(GEN x, long alpha, GEN *ptfl, GEN *ptB);
extern GEN apply_kummer(GEN nf,GEN pol,GEN e,GEN p);
extern GEN hensel_lift_fact(GEN pol, GEN fact, GEN T, GEN p, GEN pev, long e);
extern GEN initgaloisborne(GEN T, GEN dn, GEN *ptL, GEN *ptprep, GEN *ptdis, long *ptprec);
extern GEN nf_get_T2(GEN base, GEN polr);
extern GEN nfgcd(GEN P, GEN Q, GEN nf, GEN den);
extern GEN nfreducemodpr_i(GEN x, GEN prh);
extern GEN pidealprimeinv(GEN nf, GEN x);
extern GEN polsym_gen(GEN P, GEN y0, long n, GEN T, GEN N);
extern GEN sort_factor(GEN y, int (*cmp)(GEN,GEN));
extern GEN special_pivot(GEN x);
extern GEN trivfact(void);
extern GEN vandermondeinverse(GEN L, GEN T, GEN den, GEN prep);
extern GEN vconcat(GEN A, GEN B);
extern GEN RXQX_red(GEN P, GEN T);
extern GEN RXQX_divrem(GEN x, GEN y, GEN T, GEN *pr);
#define RXQX_div(x,y,T) RXQX_divrem((x),(y),(T),NULL)
#define RXQX_rem(x,y,T) RXQX_divrem((x),(y),(T),ONLY_REM)
#define FqX_div(x,y,T,p) FpXQX_divres((x),(y),(T),(p),NULL)
#define FqX_mul FpXQX_mul
#define FqX_red FpXQX_red

static GEN nfsqff(GEN nf,GEN pol,long fl);

typedef struct /* for use in nfsqff */
{
  GEN nf, pol, h, hinv, fact, res, lt, den, pr;
  long nfact, nfactmod, hint;
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
      pol = gmul(pol,vun); break;

    case t_POL:
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

/* lift coeffs of pol to Zk (in algtobasis form) */
static GEN
zkX(GEN x, GEN modpr)
{
  long i, l;
  GEN z;

  if (typ(x)!=t_POL) return gcopy(x);
  l = lgef(x);
  z = cgetg(l, t_POL); z[1] = x[1];
  for (i=2; i<l; i++) z[i] = (long)ff_to_nf((GEN)x[i], modpr); 
  return z;
}

/* factorization of x modulo pr. Assume x already reduced */
static GEN
nffactormod_i(GEN x, GEN T, GEN p)
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
  rep = nffactormod_i(xrd,T,p);
  z = (GEN)rep[1]; l = lg(z);
  for (j = 1; j < l; j++) z[j] = (long)zkX((GEN)z[j], modpr);
  return gerepilecopy(av, rep);
}

/* If p doesn't divide bad and has a divisor of degree 1, return it. */
static GEN
choose_prime(GEN nf, GEN bad, GEN lim)
{
  GEN p, r, L, x = (GEN)nf[1];
  for (L = lim;; L = addis(p,2))
  {
    p = nextprime(L);
    if (divise(bad,p)) continue;
    r = rootmod(x, p);
    if (lg(r) > 1) break;
  }
  r = gsub(polx[varn(x)], lift_intern((GEN)r[1]));
  return apply_kummer(nf,r,gun,p);
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
nf_bestlift(GEN elt, nfcmbf_t *T)
{
  GEN u;
  long i,l = lg(T->h), t = typ(elt);
  if (t != t_INT)
  {
    if (t == t_POL) elt = algtobasis_i(T->nf,elt);
    u = gmul(T->hinv,elt);
    for (i=1; i<l; i++) u[i] = (long)gdivround((GEN)u[i], T->den);
  }
  else
  {
    u = gmul(elt, (GEN)T->hinv[1]);
    for (i=1; i<l; i++) u[i] = (long)gdivround((GEN)u[i], T->den);
    elt = gscalcol(elt, l-1);
  }
  u = gsub(elt, gmul(T->h, u));
  return gmul((GEN)T->nf[7], u);
}

/* return the lift of pol with coefficients of T2-norm <= C (if possible) */
static GEN
nf_pol_lift(GEN pol, nfcmbf_t *T)
{
  long i, d = lgef(pol);
  GEN x = cgetg(d,t_POL);
  x[1] = pol[1];
  for (i=2; i<d; i++)
    x[i] = (long)nf_bestlift((GEN)pol[i], T);
  return x;
}

/* return the factorization of x in nf */
GEN
nffactor(GEN nf,GEN pol)
{
  GEN A,g,y,p1,rep,T;
  long l, j, d = degpol(pol);
  gpmem_t av;
  if (DEBUGLEVEL>3) timer2();

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
      GEN fact=lift((GEN)y[j]), quo = g, rem;
      long e = 0;
      do { e++; quo = RXQX_divrem(quo,fact,T, &rem); } while (gcmp0(rem));
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

/* test if the matrix M is suitable */
static long
PRK_good_enough(GEN M, GEN p, long k, GEN C2)
{
  long i, l = lg(M);
  GEN min, prod, L2, p2k = gpowgs(p, k<<1);

  min = prod = gcoeff(M,1,1);
  for (i = 2; i < l; i++)
  {
    L2 = gcoeff(M,i,i); prod = mpmul(prod,L2);
    if (mpcmp(L2,min) < 0) min = L2;
  }
  return (mpcmp(mpmul(C2,prod), mpmul(min, p2k)) < 0);
}

/* We want to be able to reconstruct x, T_2(x) < C, from x mod pr^k
 * k > B / log(N pr) is probably OK.
 * Theoretical guaranteed bound is (n/2) [ log(C/n) + n*(n-1) * log(4)/4 ]
 * We replace log(4)/4 ~ 0.347 by 0.15.  Assume C a t_REAL */
static GEN
bestlift_bound(GEN C, long n)
{
  GEN t = addrr(mplog(divrs(C,n)), dbltor(n*(n-1) * 0.15));
  return gmul2n(mulrs(t,n), -1);
}

static GEN
get_T2(GEN nf, int tot_real, long prec)
{
  if (tot_real) return gmael(nf,5,4);
  if (prec <= nfgetprec(nf)) return gmael(nf,5,3);
  return nf_get_T2((GEN)nf[7], roots((GEN)nf[1],prec));
}

/* return the matrix corresponding to pr^e with R(pr^e) > C */
static GEN
bestlift_init(GEN nf, GEN pr, GEN C, long *kmax, GEN *prkmax)
{
  long k, prec, n = degpol(nf[1]);
  gpmem_t av = avma, av1, av2;
  int tot_real = !signe(gmael(nf,2,2)), early_try = (n <= 6);
  GEN dk,logdk,prk,PRK,p1,u,C2,T2,T2PRK;
  GEN p = (GEN)pr[1], logp = glog(p,DEFAULTPREC);
  GEN *gptr[2];

  dk = absi((GEN)nf[3]); logdk = glog(dk,DEFAULTPREC);
  C2 = gdiv(gmul2n(C,2), dk);

  av1 = avma; u = NULL;
  p1 = bestlift_bound(C, n);
  k = itos(gceil( divrr(p1,logp) ));
  for (;; k<<=1, avma = av1)
  {
    p1 = gmul2n(addrr(logdk , mulsr(k, logp)), -1);
    prec = MEDDEFAULTPREC + (long)(itos(gceil(p1))*pariK1);

    if (DEBUGLEVEL>2) fprintferr("exponent: %ld, precision: %ld\n",k,prec);
    prk = idealpows(nf, pr, k);
    PRK = gmul(prk, lllintpartial(prk)); av2 = avma;
    for(;;)
    {
      T2 = get_T2(nf, tot_real, prec);
      T2PRK = qf_base_change(T2,PRK,1);
      if (early_try && PRK_good_enough(T2PRK, p,k,C2)) break;
      early_try = 0;

      u = tot_real? lllgramall(T2PRK,2,lll_IM) : lllgramintern(T2PRK,2,1,prec);
      if (u) { T2PRK = qf_base_change(T2PRK,u,1); break; }

      prec = (prec<<1)-2;
      if (DEBUGLEVEL>1) err(warnprec,"nffactor[1]",prec);
    }
    if (early_try) break;

    if (DEBUGLEVEL>2) msgtimer("lllgram + base change");
    if (PRK_good_enough(T2PRK, p,k,C2)) { PRK = gmul(PRK, u); break; }
  }
  gptr[0] = &prk; gptr[1] = &PRK; gerepilemany(av, gptr, 2);
  *kmax   = k;
  *prkmax = prk; return PRK;
}

/* assume lc(pol) != 0 mod prh */
static GEN
nf_pol_red(GEN pol, GEN prh)
{
  long i, l = lgef(pol);
  GEN z = cgetg(l, t_POL); z[1] = pol[1];
  for (i=2; i<l; i++) z[i] = nfreducemodpr_i((GEN)pol[i], prh)[1];
  return z;
}

/* return a bound for T_2(P), P | polbase */
static GEN
nf_factor_bound(GEN nf, GEN polbase)
{
  GEN lt,C,run,p1,p2, T2 = gmael(nf,5,3);
  long i,prec,precnf, d = lgef(polbase), n = degpol(nf[1]);

  precnf = gprecision(T2);
  prec   = DEFAULTPREC;
  for (;;)
  {
    run= realun(prec);
    p1 = realzero(prec);
    for (i=2; i<d; i++)
    {
      p2 = gmul(run, (GEN)polbase[i]);
      p2 = qfeval(T2, p2); if (signe(p2) < 0) break;
      p1 = addrr(p1, gdiv(p2, binome(stoi(d), i-2)));
    }
    if (i == d) break;

    prec = (prec<<1)-2;
    if (prec > precnf)
    {
      if (DEBUGLEVEL>1) err(warnprec, "nfsqff", prec);
      T2 = nf_get_T2((GEN)nf[7], roots((GEN)nf[1], prec));
    }
  }
  lt = (GEN)leading_term(polbase)[1];
  p1 = gmul(p1, mulis(sqri(lt), n));
  C = gpow(stoi(3), dbltor(0.75 + d), DEFAULTPREC);
  return gdiv(gmul(C, p1), gmulsg(d, mppi(DEFAULTPREC)));
}

/* psf = product of modular factors, test all products with psf * P, with
 * P = product of modular factors of index >= fxn, deg(P) <= dlim, 
 * Number of mod. factors in P <= nlim 
 * */
static int
nfcmbf(nfcmbf_t *T,long fxn,GEN psf,long dlim, long nlim)
{
  int val = 0; /* assume failure */
  GEN newf, newpsf = NULL;
  long newd;
  gpmem_t av, ltop;

  /* Assertion: fxn <= T->nfactmod && dlim > 0 && nlim > 0 */

  /* first, try deeper factors without considering the current one */
  if (fxn != T->nfactmod)
  {
    val = nfcmbf(T,fxn+1,psf,dlim,nlim);
    if (val && psf) return 1;
  }

  /* second, try including the current modular factor in the product */
  newf = (GEN)T->fact[fxn];
  if (!newf) return val; /* modular factor already used */
  newd = degpol(newf);
  if (newd > dlim) return val; /* degree of new factor is too large */

  av = avma;
  if (newd % T->hint == 0)
  {
    GEN quo,rem, nf = T->nf, nfpol = (GEN)nf[1];

    newpsf = RXQX_mul(psf? psf: T->lt, newf, nfpol);
    newpsf = nf_pol_lift(simplify_i(newpsf), T);
    /* try out the new combination */
    ltop = avma;
    quo = RXQX_divrem(T->pol,newpsf, nfpol, &rem);
    if (gcmp0(rem))
    { /* found a factor */
      T->res[++T->nfact] = (long)QXQ_normalize(newpsf, nfpol);
      T->pol = primpart(quo);
      T->lt  = leading_term(T->pol);
      T->fact[fxn] = 0; /* remove used modular factor */
      return 1;
    }
    avma = ltop;
  }

  /* If room in degree limit + more modular factors to try, add more factors to
   * newpsf */
  if (nlim > 0 && newd < dlim && fxn < T->nfactmod
                              && nfcmbf(T,fxn+1,newpsf,dlim-newd,nlim-1))
  {
    T->fact[fxn] = 0; /* remove used modular factor */
    return 1;
  }
  avma = av; return val;
}

GEN nf_LLL_cmbf(nfcmbf_t *S, long a, GEN p, long rec);

/* return the factorization of the square-free polynomial x.
   The coeff of x are in Z_nf and its leading term is a rational integer.
   deg(x) > 1
   If fl = 1,return only the roots of x in nf */
static GEN
nfsqff(GEN nf,GEN pol, long fl)
{
  long i, k, m, n, nbf, anbf, ct;
  gpmem_t av = avma;
  GEN pr,rep,k2,C,h,dk,bad,p,prk,polbase,pk;
  GEN ap,polmod,polred,hinv,lt,minp,nfpol;
  nfcmbf_t T;

  if (DEBUGLEVEL>3) msgtimer("square-free");
  nfpol = (GEN)nf[1];
  polbase = unifpol(nf,pol,0);
  polmod  = unifpol(nf,pol,1);
  pol = lift(polmod);
  lt  = (GEN)leading_term(polbase)[1]; /* t_INT */

  dk = absi((GEN)nf[3]);
  bad = mulii(mulii(dk,(GEN)nf[4]), lt);
  n = degpol(nfpol);

  C = nf_factor_bound(nf, polbase);
  if (DEBUGLEVEL>3) fprintferr("Bound on the T2-norm of a factor: %Z\n", C);

  k2 = bestlift_bound(C, n);
  minp = gexp(gmul2n(k2,-6), DEFAULTPREC);
  if (expo(minp) > 32) minp = utoi(1UL<<31);
  minp = gceil(minp); if (DEBUGLEVEL>3)
  {
    fprintferr("lower bound for the prime numbers: %Z\n", minp);
    msgtimer("bounds computation");
  }

  p = polred = NULL; /* gcc -Wall */
  pr= NULL; nbf = BIGINT;
  for (ct = 5;; minp = addis(ap,1))
  {
    GEN apr = choose_prime(nf,bad,minp);
    GEN aprh = prime_to_ideal(nf,apr);

    ap = (GEN)apr[1];
    polred = nf_pol_red(polbase, aprh);
    if (!FpX_is_squarefree(polred,ap)) continue;

    ct--;
    anbf = fl? FpX_nbroots(polred,ap): FpX_nbfact(polred,ap);
    if (anbf < nbf)
    {
      nbf = anbf; pr = apr; p = ap;
      if (DEBUGLEVEL>3) {
        fprintferr("prime ideal considered: %Z\n", pr);
        fprintferr("number of irreducible factors: %ld\n", nbf);
      }
      if (fl)
      { if (!nbf) return cgetg(1,t_VEC); }
      else
        if (nbf == 1) return gerepilecopy(av, _vec(polmod));
    }
    if (pr && !ct) break;
  }
  if (DEBUGLEVEL>3) {
    fprintferr("prime ideal chosen: %Z\n", pr);
    msgtimer("choice of the prime ideal");
  }

  h = bestlift_init(nf,pr,C, &k,&prk);
  if (DEBUGLEVEL>3) msgtimer("computation of H");
  pk = gcoeff(prk,1,1);
  hinv = ZM_inv(h, pk);
  if (DEBUGLEVEL>3) msgtimer("computation of H^(-1)");

  /* polred is monic */
  polred = nf_pol_red(gmul(mpinvmod(lt,pk), polbase), prk);

  T.h        = h;
  T.hinv     = hinv;
  T.den      = pk;
  T.nf       = nf;

  if (fl)
  { /* roots only */
    long x_a[] = { evaltyp(t_POL)|_evallg(4), 0,0,0 };
    rep = rootpadicfast(polred, p, k);
    x_a[1] = pol[1]; setlgef(x_a, 4);
    x_a[3] = un;
    for (m=1,i=1; i<lg(rep); i++)
    {
      GEN rem,q, r = (GEN)rep[i];

      r = nf_bestlift(gmul(lt,r), &T);
      r = gdiv(r,lt);
      x_a[2] = lneg(r); /* check P(r) == 0 */
      q = RXQX_divrem(pol, x_a, nfpol, &rem);
      if (!signe(rem)) { pol = q; rep[m++] = (long)r; }
    }
    rep[0] = evaltyp(t_VEC) | evallg(m);
    return gerepilecopy(av, rep);
  }

  rep = (GEN)factmod0(polred,p)[1];
  rep = hensel_lift_fact(polred,rep,NULL,p,pk,k);
  if (DEBUGLEVEL>3) msgtimer("Hensel lift");
  m = lg(rep);
  T.pol      = pol;
  T.lt       = lt;
  T.fact     = rep;
  T.res      = cgetg(m,t_VEC);
  T.nfact    = 0;
  T.nfactmod = m-1;
  T.pr       = pr;
  T.hint     = 1;
#if 0
  nfcmbf(&T, 1,NULL,degpol(pol),2);
  m = T.nfact + 1;
  if (degpol(T.pol))
    T.res[m++] = (long)QXQ_normalize(T.pol,nfpol);
#else
  T.res = nf_LLL_cmbf(&T,k,p, 0);
  m = lg(T.res);
#endif
  if (DEBUGLEVEL>3) msgtimer("computation of the factors");

  rep = cgetg(m,t_VEC);
  for (i=1;i<m; i++) rep[i] = (long)unifpol(nf,(GEN)T.res[i],1);
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

/* relative Dedekind criterion over nf, applied to the order defined by a
 * root of irreducible polynomial P, modulo the prime ideal pr. Returns
 * [flag,basis,val], where basis is a pseudo-basis of the enlarged order,
 * flag is 1 iff this order is pr-maximal, and val is the valuation at pr of
 * the order discriminant */
GEN
rnfdedekind(GEN nf,GEN P0,GEN pr)
{
  long vt, r, d, n, m, i, j;
  gpmem_t av = avma;
  GEN Prd,P,p1,p2,p,tau,g,matid;
  GEN modpr,res,h,k,base,nfT,T,gzk,hzk;

  nf = checknf(nf); nfT = (GEN)nf[1]; P = lift(P0);
  res = cgetg(4,t_VEC);
  modpr = nf_to_ff_init(nf,&pr, &T, &p);
  tau = gmul((GEN)nf[7], (GEN)pr[5]);
  n = degpol(nfT);
  m = degpol(P);

  Prd = modprX(P, nf, modpr);
  p1 = (GEN)nffactormod_i(Prd,T,p)[1];
  r = lg(p1); if (r < 2) err(constpoler,"rnfdedekind");
  g = (GEN)p1[1];
  for (i=2; i<r; i++) g = FqX_mul(g, (GEN)p1[i], T, p);
  h = FqX_div(Prd,g, T, p);
  gzk = zkX(g, modpr);
  hzk = zkX(h, modpr);

  k = gsub(P, RXQX_mul(gzk,hzk, nfT));
  k = gdiv(RXQX_mul(tau,k,nfT), p);
  k = modprX(k, nf, modpr);

  p2 = FqX_gcd(g,h,  T,p);
  k  = FqX_gcd(p2,k, T,p); d = degpol(k);  /* <= m */

  vt = idealval(nf,discsr(P0),pr) - 2*d;
  res[3] = lstoi(vt);
  res[1] = (!d || vt<=1)? un: zero;

  base = cgetg(3,t_VEC);
  p1 = cgetg(m+d+1,t_MAT); base[1] = (long)p1;
  p2 = cgetg(m+d+1,t_VEC); base[2] = (long)p2;
 /* if d > 0, base[2] temporarily multiplied by p, for the final nfhermitemod
  * [ which requires integral ideals ] */
  matid = gscalmat(d? p: gun, n);
  for (j=1; j<=m; j++)
  {
    p2[j]=(long)matid;
    p1[j]=lgetg(m+1,t_COL);
    for (i=1; i<=m; i++) coeff(p1,i,j) = (i==j)?un:zero;
  }
  if (d)
  {
    GEN prinvp = pidealprimeinv(nf,pr); /* again multiplied by p */
    GEN X = polx[varn(P)], pal;

    pal = FqX_div(Prd,k, T,p);
    pal = zkX(pal, modpr);
    for (   ; j<=m+d; j++)
    {
      p1[j] = (long)pol_to_vec(pal,m);
      p2[j] = (long)prinvp;
      pal = RXQX_rem(RXQX_mul(pal,X,nfT),P,nfT);
    }
    /* the modulus is integral */
    base = nfhermitemod(nf,base, gmul(gpowgs(p, m-d),
				      idealpows(nf, prinvp, d)));
    base[2] = ldiv((GEN)base[2], p); /* cancel the factor p */
  }
  res[2]=(long)base; return gerepilecopy(av, res);
}

#if 0
/* Naive recombination of modular factors: combine up to maxK modular
 * factors, degree <= klim and divisible by hint
 *
 * target = polynomial we want to factor
 * famod = array of modular factors.  Product should be congruent to
 * target/lc(target) modulo p^a
 * All rational factors are bounded by p^b, b <= a and p^(b-a) < 2^(BIL-1) */
static GEN
nfcmbf2(GEN target, GEN famod, GEN p, long b, long a,
        long maxK, long klim,long hint)
{
  long K = 1, cnt = 1, i,j,k, curdeg, lfamod = lg(famod)-1;
  long spa_b, spa_bs2;
  GEN lc, lctarget, pa = gpowgs(p,a), pas2 = shifti(pa,-1);
  GEN trace    = cgetg(lfamod+1, t_VECSMALL);
  GEN ind      = cgetg(lfamod+1, t_VECSMALL);
  GEN degpol      = cgetg(lfamod+1, t_VECSMALL);
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
#endif

long
root_get_prec(GEN P)
{
  long i, j, z, prec = 0;
  for (i=2; i<lgef(P); i++)
  {
    GEN p = (GEN)P[i];
    if (typ(p) == t_INT)
    {
      z = lg(p);
      if (z > prec) prec = z;
    }
    else
    {
      for (j=2; j<lgef(p); j++)
      {
        z = lg(p[j]);
        if (z > prec) prec = z;
      }
    }
  }
  return prec + 1;
}

/* assume P monic. B_s = Mignotte bound for s(P). Vec( |B_s|^2, s ) */
static GEN
nf_root_bounds(GEN P, GEN T)
{
  long lR, i, j, l = lgef(P), prec = root_get_prec(P);
  GEN Ps, R, B, z, V;

  B = gzero;
  R = roots(T, prec);
  lR = lg(R);
  V = cgetg(lR, t_VEC);
  Ps = cgetg(l, t_POL); /* sigma (P) */
  Ps[1] = P[1];

  for (j=1; j<lg(R); j++)
  {
    GEN r = (GEN)R[j];
    for (i=2; i<l; i++) Ps[i] = (long)poleval((GEN)P[i], r);
    z = QuickNormL2(Ps, DEFAULTPREC);
    V[j] = (long)z;
  }
  return V;
}

/* return B such that if x in O_K, K = Z[X]/(T), then the L2-norm of the
 * coordinates of the numerator of x (in the basis 1,X,...,X^(n-1)) is
 *   <= B T_2(x)
 * *ptden = multiplicative bound for denom(x) */
static GEN
L2_bound(GEN T, GEN *ptden)
{
  long prec;
  GEN M, L, prep, den;
  den = initgaloisborne(T, NULL, &L, &prep, NULL, &prec);
  M = vandermondeinverse(L, gmul(T, realun(prec)), den, prep);
  *ptden = den; return QuickNormL2(M, DEFAULTPREC);
}

static GEN
normlp(GEN L, long p)
{
  long i,l = lg(L);
  GEN z = gzero;
  for (i=1; i<l; i++)
    z = gadd(z, gpowgs((GEN)L[i], p));
  return z;
}

/* assume pr has degree 1 */
GEN
nf_LLL_cmbf(nfcmbf_t *T, long a, GEN p, long rec)
{
  GEN dn, q, goodq, pa = T->den, famod = T->fact, nfT = (GEN)(T->nf[1]);
  GEN P = simplify(T->pol);
  GEN ZC = L2_bound(nfT, &dn);
  GEN Br = nf_root_bounds(P, nfT);
  GEN B, Btra, PRK = T->h, PRKinv = T->hinv, PRK_GSmin;
  long dnf = degpol(nfT), dP = degpol(P);

  long BitPerFactor = 3; /* nb bits / modular factor */
  long i,j,C,r,tmax,tnew,n0,n;
  GEN y, Tra, T2, T2r, TT, BL, m, u, norm, target, M, piv, list;
  gpmem_t av, av2, lim;

  P = unifpol(T->nf,P,0);
  n0 = n = r = lg(famod) - 1;
  list = cgetg(n0+1, t_COL);

  av = avma; lim = stack_lim(av, 1);
  TT = cgetg(n0+1, t_VEC);
  Tra  = cgetg(n0+1, t_MAT);
  for (i=1; i<=n0; i++) TT[i] = 0;
  BL = idmat(n0);
  /* FIXME: wasteful, but PRK should be close to LLL reduced already */
  u = lllgramint_i(gram_matrix(PRK), 4, NULL, &B);
  PRK_GSmin = vecmin(GS_norms(B, DEFAULTPREC));

  /* tmax = current number of traces used (and computed so far) */
  for(tmax = 0;; tmax++)
  {
    double BvS, Blow;
    if (DEBUGLEVEL>2)
      fprintferr("nf_LLL_cmbf: %ld potential factors (tmax = %ld)\n", r, tmax);

    /* Lattice: (S PRK), small vector (vS vP). Find a bound for the image 
     * write S = S1 q + S0, P = P1 q + P0 */
    BvS = bound_vS(tmax, &BL);
    r = lg(BL)-1;
    tnew = tmax+1;
    { /* bound for f . S_k(genuine factor) */
      GEN N2 = mulsr(dP*dP, normlp(Br, tnew)); /* bound for T_2(S_tnew) */
      double sqrtBvS = sqrt(BvS);
      Btra = mulrr(ZC, N2);
      /* assume q > sqrt(Btra) */
      Blow = 1. + 0.5*sqrtBvS + 0.5 * sqrt((double)dnf) * (sqrtBvS + 1);

      Blow *= Blow;
      /* q(S1 vS + P1 vP) <= Blow for all (vS,vP) assoc. to true factors */
      /* C^2 BvS ~ Blow */ 
      C = (long)ceil(sqrt(Blow/BvS)) + 1;
      M = dbltor( BvS * C * C + Blow );
    }

    q = ceil_safe(mpsqrt(Btra));
    if (gcmp(PRK_GSmin, Btra) < 0)
    {
      GEN prk, polred;
      av2 = avma;
      for (a<<=1;; avma = av2, a<<=1)
      {
        prk = idealpows(T->nf, T->pr, a);
        pa = gcoeff(prk,1,1);
        PRK = gmul(prk, lllintpartial(prk));

        u = lllgramint_i(gram_matrix(PRK), 4, NULL, &B);
        PRK_GSmin = vecmin(GS_norms(B, DEFAULTPREC));
        if (gcmp(PRK_GSmin, Btra) >= 0) break;
      }
      PRK = gmul(PRK, u);
      PRKinv = ZM_inv(PRK, pa);

      polred = nf_pol_red(P, prk);
      famod = hensel_lift_fact(polred,famod,NULL,p,pa,a);
      /* recompute old Newton sums to new precision */
      if (tmax)
        for (i=1; i<=n0; i++) TT[i] = 0;
    }

    for (i=1; i<=n0; i++)
    {
      GEN p2 = polsym_gen((GEN)famod[i], (GEN)TT[i], tnew, NULL, pa);
      GEN p3 = (GEN)p2[tnew+1];
      if (!gcmp1(dn)) p3 = modii(mulii(p3,dn), pa);
      TT[i] = (long)p2;
      Tra[i] = (long)gscalcol(p3, dnf); /* S_tnew(famod) */
    }

    av2 = avma;
    T2 = gmod( gmul(Tra, BL), pa );
    T2r= gsub(T2, gmul(PRK, gdivround(gmul(PRKinv, T2), pa)));

    goodq = shifti(gun, gexpo(T2r) - BitPerFactor * r);
    if (cmpii(goodq, q) > 0) q = goodq;

    m = concatsp( vconcat( gscalsmat(C, r), gdivround(T2r, q) ),
                  vconcat(zeromat(r, dnf),  gdivround(PRK,q)));
    /*     [  C     0  ]
     * m = [           ]   square matrix
     *     [ T2r    PRK]   T2r = Tra * BL  truncated
     */
    u = lllgramint_i(gram_matrix(m), 4, NULL, &B);
    norm = GS_norms(B, DEFAULTPREC);
    for (i=r+dnf; i>0; i--)
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
      if (r == 0) err(bugparier,"nf_LLL_cmbf [no factor]");
      if (DEBUGLEVEL>2) fprintferr("nf_LLL_cmbf: 1 factor\n");
      list[1] = (long)T->pol; setlg(list,2); return list;
    }

    setlg(u, r+1);
    for (i=1; i<=r; i++) setlg(u[i], n+1);
    BL = gerepileupto(av2, gmul(BL, u));
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[8]; gptr[0]=&BL; gptr[1]=&TT; gptr[2]=&Tra; gptr[3]=&famod;
      gptr[4]=&PRK_GSmin; gptr[5]=&PRK; gptr[6]=&PRKinv; gptr[7]=&pa;
      if(DEBUGMEM>1) err(warnmem,"nf_LLL_cmbf");
      gerepilemany(av, gptr, 8);
    }
    if (rec && r*rec >= n0) continue;

    av2 = avma;
    piv = special_pivot(BL);
    if (!piv) { avma = av2; continue; }
    if (DEBUGLEVEL) fprintferr("special_pivot output:\n%Z\n",piv);

    r = lg(piv); /* BL need not have maximal rank */
    target = T->pol;
    for (i=1; i<r; i++)
    {
      GEN p1 = (GEN)piv[i], rem;
      if (DEBUGLEVEL) fprintferr("LLL_cmbf: checking factor %ld\n",i);

      y = NULL;
      for (j=1; j<=n0; j++)
        if (signe(p1[j])) y = y? FpX_mul(y,(GEN)famod[j],T->den): (GEN)famod[j];
      y = nf_pol_lift(y, T);

      /* y is the candidate factor */
      target = RXQX_divrem(target,y,nfT, &rem);
      if (!gcmp0(rem)) break;
      list[i] = (long)y;
    }
    if (i == r)
    {
      if (DEBUGLEVEL>2) fprintferr("nf_LLL_cmbf: %ld factors\n", r);
      setlg(list,r); return list;
    }
    avma = av2;
  }
}
