/* $Id$

Copyright (C) 2010  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

/********************************************************************/
/**                                                                **/
/**                  L functions of elliptic curves                **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

/* Generic Buhler-Gross algorithm */

struct bg_data
{
  GEN E, N; /* ell, conductor */
  GEN bnd; /* t_INT; will need all an for n <= bnd */
  ulong rootbnd; /* sqrt(bnd) */
  GEN an; /* t_VECSMALL: cache of ap, n <= rootbnd */
  GEN ap; /* t_VECSMALL: cache of ap, p <= rootbnd */
  GEN p;  /* t_VECSMALL: primes <= rootbnd */
  long lp;
};

typedef void bg_fun(void*el, GEN *psum, GEN n, GEN a, long jmax);

static void
gen_BG_add(void *E, bg_fun *fun, struct bg_data *bg, GEN *psum, GEN n, long i, GEN a, GEN lasta)
{
  long j;
  ulong nn = itou_or_0(n);
  if (nn && nn <= bg->rootbnd) bg->an[nn] = itos(a);

  if (signe(a))
  {
    fun(E, psum, n, a, 0);
    j = 1;
  }
  else
    j = i;
  for(; j <= i; j++)
  {
    ulong p = bg->p[j];
    GEN nexta, pn = mului(p, n);
    if (cmpii(pn, bg->bnd) > 0) return;
    nexta = mulis(a, bg->ap[j]);
    if (i == j && umodiu(bg->N, p)) nexta = subii(nexta, mului(p, lasta));
    gen_BG_add(E, fun, bg, psum, pn, j, nexta, a);
  }
}

static void
gen_BG_init(struct bg_data *bg, GEN E, GEN N, GEN bnd, GEN ap)
{
  pari_sp av;
  long i = 1;
  bg->E = E; bg->N = N;
  bg->bnd = bnd;
  bg->rootbnd = itou(sqrtint(bnd));
  bg->lp = uprimepi(bg->rootbnd);
  bg->p = primes_zv(bg->lp);
  if (ap)
  { /* reuse known values */
    i = lg(ap);
    bg->ap = vecsmall_lengthen(ap, maxss(bg->lp,i-1));
  }
  else bg->ap = cgetg(bg->lp+1, t_VECSMALL);
  av = avma;
  for (  ; i <= bg->lp; i++, avma = av)
    bg->ap[i] = itos(ellap(E, utoipos(bg->p[i])));
  avma = av;
  bg->an = const_vecsmall(bg->rootbnd, 0);
  bg->an[1] = 1;
}

static GEN
gen_BG_rec(void *E, bg_fun *fun, struct bg_data *bg, GEN sum0)
{
  long i, j, lp = bg->lp;
  GEN bndov2 = shifti(bg->bnd, -1);
  pari_sp av = avma;
  GEN sum = gcopy(sum0), p;
  if(DEBUGLEVEL)
    err_printf("1st stage, using recursion for p <= %ld\n", bg->p[lp]);
  for (i = 1; i <= lp; i++)
  {
    ulong pp = bg->p[i];
    long ap = bg->ap[i];
    gen_BG_add(E, fun, bg, &sum, utoipos(pp), i, stoi(ap), gen_1);
    sum = gerepileupto(av, sum);
  }
  p = nextprime(utoipos(bg->p[lp]+1));
  if (DEBUGLEVEL) err_printf("2nd stage, looping for p <= %Ps\n", bndov2);
  for (  ; cmpii(p, bndov2)<=0; p = nextprime(addis(p,1)))
  {
    long jmax;
    GEN ap = ellap(bg->E, p);
    if (!signe(ap)) continue;

    jmax = itou( divii(bg->bnd, p) ); /* 2 <= jmax <= el->rootbound */
    fun(E, &sum, p, ap, -jmax); /*Beware: create a cache on the stack */
    for (j = 2;  j <= jmax; j++)
    {
      long aj = bg->an[j];
      GEN a, n;
      if (!aj) continue;
      a = mulis(ap, aj);
      n = muliu(p, j);
      fun(E, &sum, n, a, j);
    }
    gerepileall(av, 2, &sum, &p);
  }
  if (DEBUGLEVEL) err_printf("3nd stage, looping for p <= %Ps\n", bg->bnd);
  for (  ; cmpii(p, bg->bnd)<=0; p = nextprime(addis(p,1)))
  {
    GEN a = ellap(bg->E, p);
    if (!signe(a)) continue;
    fun(E, &sum, p, a, 0);
    gerepileall(av, 2, &p, &sum);
  }
  return gerepileupto(av, sum);
}

/* Computing L-series derivatives */

/* Implementation by C. Delaunay and X.-F. Roblot
   after a GP script of Tom Womack and John Cremona
   and the corresponding section of Henri Cohen's book GTM 239
   Generic Buhler-Gross iteration and baby-step-giant-step implementation
   by Bill Allombert.
*/

struct ellld {
  GEN E, N; /* ell, conductor */
  GEN bnd; /* t_INT; will need all an for n <= bnd */
  ulong rootbnd; /* floor(sqrt(bnd)) */
  ulong bgbnd; /* rootbnd+1 */
  long r; /* we are comuting L^{(r)}(1) */
  GEN X; /* t_REAL, 2Pi / sqrt(N) */
  GEN eX; /* t_REAL, exp(X) */
  GEN emX; /* t_REAL, exp(-X) */
  GEN gcache, gjcache, baby, giant; /* t_VEC of t_REALs */
  GEN alpha; /* t_VEC of t_REALs, except alpha[1] = gen_1 */
  GEN A; /* t_VEC of t_REALs, A[1] = 1 */
  long epsbit;
};

static GEN
init_alpha(long m, long prec)
{
  GEN a, si, p1;
  GEN s = gadd(pol_x(0), zeroser(0, m+1));
  long i;

  si = s;
  p1 = gmul(mpeuler(prec), s);
  for (i = 2; i <= m; i++)
  {
    si = gmul(si, s); /* = s^i */
    p1 = gadd(p1, gmul(divru(szeta(i, prec), i), si));
  }
  p1 = gexp(p1, prec); /* t_SER of valuation = 0 */

  a = cgetg(m+2, t_VEC);
  for (i = 1; i <= m+1; i++) gel(a, i) = gel(p1, i+1);
  return a;
}

/* assume r >= 2, return a t_VEC A of t_REALs of length > 2.
 * NB: A[1] = 1 */
static GEN
init_A(long r, long m, long prec)
{
  const long l = m+1;
  long j, s, n;
  GEN A, B, ONE, fj;
  pari_sp av0, av;

  A = cgetg(l, t_VEC); /* will contain the final result */
  gel(A,1) = real_1(prec);
  for (j = 2; j < l; j++) gel(A,j) = cgetr(prec);
  av0 = avma;
  B = cgetg(l, t_VEC); /* scratch space */
  for (j = 1; j < l; j++) gel(B,j) = cgetr(prec);
  ONE = real_1(prec);
  av = avma;

  /* We alternate between two temp arrays A, B (initially virtually filled
   * ONEs = 1.), which are swapped after each loop.
   * After the last loop, we want A to contain the final array: make sure
   * we swap an even number of times */
  if (odd(r)) swap(A, B);

  /* s = 1 */
    for (n = 2; n <= m; n++)
    {
      GEN p3 = ONE; /* j = 1 */
      for (j = 2; j <= n; j++) p3 = addrr(p3, divru(ONE, j));
      affrr(p3, gel(B, n)); avma = av;
    }
  swap(A, B); /* B becomes the new A, old A becomes the new scratchspace */
  for (s = 2; s <= r; s++)
  {
    for (n = 2; n <= m; n++)
    {
      GEN p3 = ONE; /* j = 1 */
      for (j = 2; j <= n; j++) p3 = addrr(p3, divru(gel(A, j), j));
      affrr(p3, gel(B, n)); avma = av;
    }
    swap(A, B); /* B becomes the new A, old A becomes the new scratchspace */
  }

  /* leave A[1] (division by 1) alone */
  fj = ONE; /* will destroy ONE now */
  for (j = 2; j < l; j++)
  {
    affrr(mulru(fj, j), fj);
    affrr(divrr(gel(A,j), fj), gel(A,j));
    avma = av;
  }
  avma = av0; return A;
}

/* x > 0 t_REAL, M >= 2 */
static long
estimate_prec_Sx(GEN x, long M)
{
  GEN p1, p2;
  pari_sp av = avma;

  x = rtor(x, DEFAULTPREC);
  p1 = divri(powru(x, M-2), mpfact(M-1)); /* x^(M-2) / (M-1)! */
  if (expo(x) < 0)
  {
    p2 = divrr(mulrr(p1, powru(x,3)), mulur(M,subsr(1,x)));/* x^(M+1)/(1-x)M! */
    if (cmprr(p2,p1) < 0) p1 = p2;
  }
  avma = av; return expo(p1);
}

/* x a t_REAL */
static long
number_of_terms_Sx(GEN x, long epsbit)
{
  long M, M1, M2;
  M1 = (long)(epsbit * 7.02901423262); /* epsbit * log(2) / (log(3) - 1) */
  M2 = itos(ceil_safe(gmul2n(x,1))); /* >= 2x */
  if (M2 < 2) M2 = 2;
  M = M2;
  for(;;)
  {
    if (estimate_prec_Sx(x, M) < -epsbit) M1 = M; else M2 = M;
    M = (M1+M2+1) >> 1;
    if (M >= M1) return M1;
  }
}

/* X t_REAL, emX = exp(-X) t_REAL; return t_INT */
static GEN
cutoff_point(long r, GEN X, GEN emX, long epsbit, long prec)
{
  GEN M1 = ceil_safe(divsr(7*prec2nbits(prec)+1, X));
  GEN M2 = gen_2, M = M1;
  for(;;)
  {
    GEN c = divrr(powgi(emX, M), powru(mulri(X,M), r+1));
    if (expo(c) < -epsbit) M1 = M; else M2 = M;
    M = shifti(addii(M1, M2), -1);
    if (cmpii(M2, M) >= 0) return M;
  }
}

/* x "small" t_REAL, use power series expansion. Returns a t_REAL */
static GEN
compute_Gr_VSx(struct ellld *el, GEN x)
{
  pari_sp av = avma;
  long r = el->r, n;
  /* n = 2 */
  GEN p1 = divrs(sqrr(x), -2); /* (-1)^(n-1) x^n / n! */
  GEN p2 = x;
  GEN p3 = shiftr(p1, -r);
  for (n = 3; ; n++)
  {
    if (expo(p3) < -el->epsbit) return gerepilecopy(av, p2);
    p2 = addrr(p2, p3);
    p1 = divrs(mulrr(p1, x), -n); /* (-1)^(n-1) x^n / n! */
    p3 = divri(p1, powuu(n, r));
  }
  /* sum_{n = 1}^{oo} (-1)^(n-1) x^n / (n! n^r) */
}

/* t_REAL, assume r >= 2. m t_INT or NULL; Returns a t_REAL */
static GEN
compute_Gr_Sx(struct ellld *el, GEN m, ulong sm)
{
  pari_sp av = avma;
  const long thresh_SMALL = 5;
  long i, r = el->r;
  GEN x = m? mulir(m, el->X): mulur(sm, el->X);
  GEN logx = mplog(x), p4;
  /* i = 0 */
  GEN p3 = gel(el->alpha, r+1);
  GEN p2 = logx;
  for (i = 1; i < r; i++)
  { /* p2 = (logx)^i / i! */
    p3 = addrr(p3, mulrr(gel(el->alpha, r-i+1), p2));
    p2 = divru(mulrr(p2, logx), i+1);
  }
  /* i = r, use alpha[1] = 1 */
  p3 = addrr(p3, p2);

  if (cmprs(x, thresh_SMALL) < 0)
    p4 = compute_Gr_VSx(el, x); /* x "small" use expansion near 0 */
  else
  { /* x "large" use expansion at infinity */
    pari_sp av = avma, lim = stack_lim(av, 2);
    long M = lg(el->A);
    GEN xi = sqrr(x); /* x^2 */
    p4 = x; /* i = 1. Uses A[1] = 1; NB: M > 1 */
    for (i = 2; i < M; i++)
    {
      GEN p5 = mulrr(xi, gel(el->A, i));
      if (expo(p5) < -el->epsbit) break;
      p4 = addrr(p4, p5);
      xi = mulrr(xi, x); /* = x^i */
      if (low_stack(lim, stack_lim(av, 2)))
      {
        if (DEBUGMEM > 0) pari_warn(warnmem, "compute_Gr_Sx");
        gerepileall(av, 2, &xi, &p4);
      }
    }
    p4 = mulrr(p4, m? powgi(el->emX, m): powru(el->emX, sm));
  }
  return gerepileuptoleaf(av, odd(r)? subrr(p4, p3): subrr(p3, p4));
}

static GEN
init_Gr(struct ellld *el, long prec)
{
  if (el->r == 0)
  {
    el->bgbnd = el->rootbnd+1;
    el->baby  = mpvecpow(el->emX, el->bgbnd);
    el->giant = mpvecpow(gel(el->baby,el->bgbnd), el->bgbnd);
    return gel(el->baby, 1);
  }
  else if (el->r == 1) el->gcache = mpveceint1(el->X, el->eX, el->rootbnd);
  else
  {
    long m, j, l = el->rootbnd;
    GEN G;
    m = number_of_terms_Sx(mulri(el->X, el->bnd), el->epsbit);
    el->alpha = init_alpha(el->r, prec);
    el->A = init_A(el->r, m, prec);
    G = cgetg(l+1, t_VEC);
    for (j = 1; j <= l; j++) gel(G,j) = compute_Gr_Sx(el, NULL, j);
    el->gcache = G;
  }
  return gel(el->gcache, 1);
}

/* m t_INT, returns a t_REAL */
static GEN
ellld_G(struct ellld *el, GEN m)
{
  if (cmpiu(m, el->rootbnd) <= 0) return gel(el->gcache, itos(m));
  if (el->r == 1) return mpeint1(mulir(m, el->X), powgi(el->eX,m));
  return compute_Gr_Sx(el, m, 0); /* r >= 2 */
}


/* el->r<=1 */
static GEN
ellld_Gmulti(struct ellld *el, GEN p, long jmax)
{
  el->gjcache = mpveceint1(mulir(p,el->X), powgi(el->eX,p), jmax);
  return gel(el->gjcache, 1);
}

static void
ellld_L1(void *E, GEN *psum, GEN n, GEN a, long j)
{
  struct ellld *el = (struct ellld *) E;
  GEN G;
  if (j==0 || el->r>=2) G = ellld_G(el, n);
  else if (j < 0)  G = ellld_Gmulti(el, n, -j);
  else G = gel(el->gjcache, j);
  *psum = addrr(*psum, divri(mulir(a, G), n));
}

static GEN
ellld_L1r0_G(struct ellld *el, GEN n)
{
  GEN q, r;
  if (cmpiu(n, el->bgbnd) <= 0) return gel(el->baby, itou(n));
  q = truedvmdis(n,el->bgbnd,&r);
  if (signe(r)==0) return gel(el->giant, itou(q));
  return gmul(gel(el->baby, itou(r)), gel(el->giant, itou(q)));
}

static void
ellld_L1r0(void *E, GEN *psum, GEN n, GEN a, long j)
{
  struct ellld *el = (struct ellld *) E;
  GEN G = ellld_L1r0_G(el, n);
  (void) j;
  *psum = addrr(*psum, divri(mulir(a, G), n));
}

/* Basic data independent from r (E, N, X, eX, emX) already filled,
 * Returns a t_REAL */
static GEN
ellL1_i(struct ellld *el, struct bg_data *bg, long r, GEN ap, long prec)
{
  GEN sum;
  if (DEBUGLEVEL) err_printf("in ellL1 with r = %ld, prec = %ld\n", r, prec);
  el->r = r;
  el->bnd = cutoff_point(r, el->X, el->emX, el->epsbit, prec);
  gen_BG_init(bg,el->E,el->N,el->bnd,ap);
  el->rootbnd = bg->rootbnd;
  sum = init_Gr(el, prec);
  if (DEBUGLEVEL>=3) err_printf("el_bnd = %Ps, N=%Ps\n", el->bnd, el->N);
  sum = gen_BG_rec(el, r?ellld_L1:ellld_L1r0, bg, sum);
  return mulri(shiftr(sum, 1), mpfact(r));
}

static void
init_el(struct ellld *el, GEN E, long *parity, long bitprec)
{
  GEN eX;
  long prec;
  checksmallell(E);
  el->E = ell_to_small_red(E, &el->N);
  prec = nbits2prec(bitprec+(expi(el->N)>>1));
  el->X = divrr(Pi2n(1, prec), sqrtr(itor(el->N, prec))); /* << 1 */
  eX = mpexp(el->X);
  if (realprec(eX) > prec) eX = rtor(eX, prec); /* avoid spurious accuracy increase */
  el->eX = eX;
  el->emX = invr(el->eX);
  el->epsbit = bitprec+1;
  *parity = (ellrootno_global(el->E, el->N) > 0)? 0: 1; /* rank parity */
}

static GEN
ellL1_bitprec(GEN E, long r, long bitprec)
{
  pari_sp av = avma;
  struct ellld el;
  struct bg_data bg;
  long parity;
  long prec = nbits2prec(bitprec)+1;
  if (r<0) pari_err(e_MISC,"derivative order must be nonnegative");
  init_el(&el, E, &parity, bitprec);
  if (parity != (r & 1)) return gen_0;
  return gerepileuptoleaf(av, ellL1_i(&el, &bg, r, NULL, prec));
}

GEN
ellL1(GEN E, long r, long prec) { return ellL1_bitprec(E, r, prec2nbits(prec)); }

GEN
ellanalyticrank(GEN e, GEN eps, long prec)
{
  struct ellld el;
  struct bg_data bg;
  long rk;
  pari_sp av = avma, av2;
  GEN ap = NULL;
  pari_timer T;

  if (!eps)
    eps = real2n(-prec2nbits(prec)/2+1, DEFAULTPREC);
  else
    if (typ(eps) != t_REAL) {
      eps = gtofp(eps, DEFAULTPREC);
      if (typ(eps) != t_REAL) pari_err_TYPE("ellanalyticrank", eps);
    }
  init_el(&el, e, &rk, prec2nbits(prec)); /* set rk to rank parity (0 or 1) */
  if (DEBUGLEVEL) {
    err_printf("ellanalyticrank: CURVE = %Ps\n", e);
    err_printf("Rank is %s\n", rk == 0? "even": "odd");
    err_printf("eps = %Ps\nconductor = %Ps\n", eps, el.N);
    timer_start(&T);
  }
  av2 = avma;
  for(;; rk += 2)
  {
    GEN Lr1 = ellL1_i(&el, &bg, rk, ap, prec);
    if (DEBUGLEVEL) timer_printf(&T, "L^(%ld)=%Ps", rk, Lr1);
    if (absr_cmp(Lr1, eps) > 0) return gerepilecopy(av, mkvec2(stoi(rk), Lr1));
    ap = gerepilecopy(av2, bg.ap);
  }
}

/* This file is a C version by Bill Allombert of a GP script by
   Christophe Delaunay which was based on a GP script by John Cremona.
   Reference: Henri Cohen's book GTM 239.
*/

struct heegner
{
  GEN baby, giant;
  ulong rootbnd;
};

static GEN
heegner_G(struct heegner *h, GEN n)
{
  GEN q, G, baby, giant;
  ulong r;
  long j,l;
  if (cmpiu(n, h->rootbnd) <= 0) return gel(h->baby, itou(n));
  q = diviu_rem(n,h->rootbnd,&r);
  giant = gel(h->giant, itou(q));
  if (!r) return giant;
  baby = gel(h->baby, r);
  l = lg(baby);
  G = cgetg(l, t_VEC);
  for (j = 1; j < l; j++) gel(G, j) = gmul(gel(baby,j), gel(giant,j));
  return G;
}

static void
heegner_L1(void*E, GEN *psum, GEN n, GEN a, long jmax)
{
  struct heegner *h = (struct heegner *) E;
  long j, l = lg(*psum);
  GEN G = heegner_G(h,n);
  GEN sum = cgetg(l, t_VEC);
  (void)jmax;
  for (j = 1; j < l; j++)
    gel(sum, j) = addrr(gel(*psum,j), divri(mulir(a, real_i(gel(G,j))), n));
  *psum = sum;
}

static GEN
fillstep(GEN qi, long nb)
{
  long i, k, np=lg(qi);
  GEN cache = cgetg(nb+1,t_VEC);
  gel(cache,1) = qi;
  for (i = 2; i<=nb; ++i)
  {
    gel(cache,i) = cgetg(np, t_VEC);
    for (k = 1; k<np; ++k)
      gmael(cache,i,k) = gmul(gel(qi,k),gmael(cache,i-1,k));
  }
  return cache;
}

static GEN
heegner_psi(GEN E, GEN N, GEN ymin, GEN points, long bitprec)
{
  pari_sp av = avma;
  struct heegner h;
  struct bg_data bg;
  GEN sum, qi;
  long k, np = lg(points);
  long prec = nbits2prec(bitprec)+1;
  GEN bnd = gceil(gdiv(mulsr(bitprec,mplog2(prec)),
                       gmul(Pi2n(1, prec), ymin)));
  GEN pim = PiI2(prec);
  gen_BG_init(&bg,E,N,bnd,NULL);
  h.rootbnd = bg.rootbnd + 1;
  qi = cgetg(np, t_VEC);
  for (k = 1; k<np; ++k)
    gel(qi, k) = gexp(gmul(pim, gel(points, k)), prec);
  h.baby  = fillstep(qi,h.rootbnd);
  h.giant = fillstep(gel(h.baby,h.rootbnd),h.rootbnd);
  sum = gen_BG_rec(&h, heegner_L1, &bg, real_i(qi));
  return gerepileupto(av, sum);
}

/*Returns lambda_bad list for one prime p */
static GEN
lambda1(GEN E, GEN p, long prec)
{
  pari_sp ltop = avma;
  GEN res, lp;
  long kod = itos(gel(elllocalred(E, p), 2));
  avma = ltop;
  if (kod==2 || kod ==-2) return mkvec(gen_0);
  lp = glog(p, prec);
  if (kod > 4)
  {
    long j, m = kod - 4;
    long n = Z_pval(ell_get_disc(E), p);
    long nl = 1 + (m >> 1L);
    res = cgetg(nl+1, t_VEC);
    for (j = 1; j <= nl; j++)
      /* *= (j-1)^2/n - (j-1) */
      gel(res, j) = gmul(lp, gsubgs(gdivgs(sqrs(j - 1), n), j - 1));
  }
  else if (kod < -4)
    res = mkvec3(gen_0, negr(lp), divrs(mulrs(lp, kod), 4));
  else
  {
    const long lam[] = {8,9,0,6,0,0,0,3,4};
    long m = -lam[kod+4];
    res = mkvec2(gen_0, divrs(mulrs(lp, m), 6));
  }
  return gerepilecopy(ltop, res);
}

static GEN
lambdalist(GEN E, GEN N, long prec)
{
  pari_sp ltop = avma;
  GEN res;
  long i, j, k, l, m, n;
  GEN plist = gel(Z_factor(N), 1);
  long np = lg(plist);
  GEN dis = ell_get_disc(E);
  GEN v = cgetg(np, t_VEC);
  long lr = 1;
  for (j = 1, i = 1 ; j < np; ++j)
  {
    GEN p = gel(plist, j);
    if (dvdii(dis, sqri(p)))
    {
      GEN l = lambda1(E, p, prec);
      gel(v, i++) = l;
      lr *= lg(l)-1;
    }
  }
  np = i;
  res = cgetg(lr+1, t_VEC);
  gel(res, 1) = gen_0; n = 1; m = 1;
  for (j = 1; j < np; ++j)
  {
    GEN w = gel(v, j);
    long lw = lg(w);
    for (k = 1; k <= n; k++)
    {
      GEN t = gel(res, k);
      for (l = 1, m = 0; l < lw; l++, m+=n)
        gel(res, k + m) = mpadd(t , gel(w, l));
    }
    n = m;
  }
  return gerepilecopy(ltop, res);
}

static long
testdisc(GEN ap, GEN M, long d, long s)
{
  long k, l1 = lg(M);
  for (k = s; k < l1; ++k)
    if (!ap[k] && umodui(-d, gel(M, k))==0) return 0;
  return 1;
}

static GEN
listedisc(long s, GEN M, GEN ap, long d)
{
  const long NBR_disc = 10;
  GEN v = cgetg(NBR_disc+1, t_VECSMALL);
  pari_sp av = avma;
  GEN F = gel(M,1);
  long j;
  for (j = 1; j <= NBR_disc; ++j)
  {
    GEN dd;
    do {
      avma = av; d-=(d&1L)?1:3; dd = stoi(d);
    } while(!Z_isfundamental(dd) || !Zn_issquare(dd, M) || !testdisc(ap, F, d, s));
    v[j] = d;
  }
  avma = av; return v;
}

/* L = vector of [q1,q2] or [q1,q2,q2'];
 * len = lg(L) */
static void
remplirliste(GEN N, GEN D, GEN b, GEN d, GEN L, long *s)
{
  long k, l = lg(L);
  GEN add, frm, frm2, V2, V = cgetg(4, t_QFI);
  gel(V, 1) = mulii(d, N);
  gel(V, 2) = b;
  gel(V, 3) = diviiexact(subii(sqri(b), D), mulii(mulsi(4, N), d));
  frm = redimag(V);
  for (k = 1; k < l; ++k)
  {
    GEN Lk = gel(L,k);
    GEN Lk1 = gel(Lk, 1);
    if (gequal(frm, gel(Lk,2)))
    {
      if (cmpii(gel(V,1), gel(Lk1,1)) < 0) gel(Lk,1) = V;
      return;
    }
    if (lg(Lk) == 4 && gequal(frm, gel(Lk,3)))
    {
      if (cmpii(gel(V,1), gel(Lk1,1)) < 0) gel(Lk,1) = V;
      return;
    }
  }
  V2 = cgetg(4, t_QFI);
  gel(V2, 1) = d;
  gel(V2, 2) = negi(b);
  gel(V2, 3) = mulii(gel(V, 3), N);
  frm2 = redimag(V2);
  add = gequal(frm, frm2)? mkvec2(V,frm): mkvec3(V,frm,frm2);
  vectrunc_append(L, add);
  *s += lg(add) - 2;
}

static GEN
listepoints(GEN L)
{
  long k, l = lg(L);
  GEN v = cgetg(l, t_VEC);
  for (k = 1; k < l; ++k)
  {
    GEN Lk = gel(L,k);
    gel(v, k) = mkvec2(gcopy(gel(Lk,1)), stoi(lg(Lk) - 2));
  }
  return v;
}

static GEN
listeheegner(GEN N, GEN D)
{
  pari_sp av = avma;
  const long kmin = 30;
  GEN b = Zn_sqrt(D, mulsi(4, N));
  long h = itos(gel(quadclassunit0(D, 0, NULL, DEFAULTPREC), 1));
  GEN LISTE = vectrunc_init(h+1);
  long k1, i, s = 0;
  for (k1=0;  ;k1++)
  {
    GEN bk1 =  addii(b, mulsi(2*k1, N));
    GEN di = divisors( diviiexact(subii(sqri(bk1), D), mulsi(4, N)) );
    for (i = 1; i < lg(di); i++)
      remplirliste(N, D, bk1, gel(di, i), LISTE, &s);
    if (k1 < kmin) continue;
    if (s==h) return gerepileupto(av, listepoints(LISTE));
  }
}

/* P a t_INT or t_FRAC, return its logarithmic height */
static GEN
heightQ(GEN P, long prec)
{
  long s;
  if (typ(P) == t_FRAC)
  {
    GEN a = gel(P,1), b = gel(P,2);
    P = absi_cmp(a,b) > 0 ? a: b;
  }
  s = signe(P);
  if (!s) return real_0(prec);
  if (s < 0) P = absi(P);
  return glog(P, prec);
}

/* t a t_INT or t_FRAC, returns max(1, log |t|), returns a t_REAL */
static GEN
logplusQ(GEN t, long prec)
{
  if (typ(t) == t_INT)
  {
    if (!signe(t)) return real_1(prec);
    if (signe(t) < 0) t = absi(t);
  }
  else
  {
    GEN a = gel(t,1), b = gel(t,2);
    if (absi_cmp(a, b) < 0) return real_1(prec);
    if (signe(a) < 0) t = gneg(t);
  }
  return glog(t, prec);
}

/* See GTM239, p532, Th 8.1.18
 * Return M such that h_naive <= M */
static GEN
hnaive_max(GEN ell, GEN ht)
{
  const long prec = LOWDEFAULTPREC; /* minimal accuracy */
  GEN b2     = ell_get_b2(ell), j = ell_get_j(ell);
  GEN logd   = glog(absi(ell_get_disc(ell)), prec);
  GEN logj   = logplusQ(j, prec);
  GEN hj     = heightQ(j, prec);
  GEN logb2p = signe(b2)? addrr(logplusQ(gdivgs(b2, 12),prec), mplog2(prec))
                        : real_1(prec);
  GEN mu     = addrr(divrs(addrr(logd, logj),6), logb2p);
  return addrs(addrr(addrr(ht, divrs(hj,12)), mu), 2);
}

static GEN
qfb_root(GEN Q, GEN vDi)
{
  GEN a2 = shifti(gel(Q, 1),1), b = gel(Q, 2);
  return mkcomplex(gdiv(negi(b),a2),divri(vDi,a2));
}

static GEN
qimag2(GEN Q)
{
  pari_sp av = avma;
  GEN z = gdiv(negi(qfb_disc(Q)), shifti(sqri(gel(Q, 1)),2));
  return gerepileupto(av, z);
}

/***************************************************/
/*Routines for increasing the imaginary parts using*/
/*Atkin-Lehner operators                           */
/***************************************************/

static long
myatk(GEN ell, GEN W)
{
  GEN M = gel(Z_factor(W), 1);
  long k, l = lg(M);
  long s = 1;
  for (k = 1; k < l; ++k) s *= ellrootno(ell, gel(M, k));
  return s;
}

static GEN
qfb_mult(GEN Q, GEN M)
{
  GEN A = gel(Q, 1) , B = gel(Q, 2) , C = gel(Q, 3);
  GEN a = gcoeff(M, 1, 1), b = gcoeff(M, 1, 2);
  GEN c = gcoeff(M, 2, 1), d = gcoeff(M, 2, 2);
  GEN W1 = addii(addii(mulii(sqri(a), A), mulii(mulii(c, a), B)), mulii(sqri(c), C));
  GEN W2 = addii(addii(mulii(mulii(shifti(b,1), a), A),
                       mulii(addii(mulii(d, a), mulii(c, b)), B)),
                 mulii(mulii(shifti(d,1), c), C));
  GEN W3 = addii(addii(mulii(sqri(b), A), mulii(mulii(d, b), B)), mulii(sqri(d), C));
  GEN D = gcdii(W1, gcdii(W2, W3));
  if (!equali1(D)) {
    W1 = diviiexact(W1,D);
    W2 = diviiexact(W2,D);
    W3 = diviiexact(W3,D);
  }
  return qfi(W1, W2, W3);
}

static void
best_point(GEN Q, GEN NQ, GEN f, GEN *u, GEN *v)
{
  long n, k;
  GEN U, c, d;
  GEN A = gel(f, 1);
  GEN B = gel(f, 2);
  GEN C = gel(f, 3);
  GEN q = qfi(mulii(NQ, C), negi(B), diviiexact(A, NQ));
  redimagsl2(q, &U);
  *u = c = gcoeff(U, 1, 1);
  *v = d = gcoeff(U, 2, 1);
  if (equali1(gcdii(mulii(*u, NQ), mulii(*v, Q))))
    return;
  for (n = 1; ; n++)
  {
    for (k = -n; k<=n; k++)
    {
      *u = addis(c, k); *v = addis(d, n);
      if (equali1(ggcd(mulii(*u, NQ), mulii(*v, Q))))
        return;
      *v= subis(d, n);
      if (equali1(ggcd(mulii(*u, NQ), mulii(*v, Q))))
        return;
      *u = addis(c, n); *v = addis(d, k);
      if (equali1(ggcd(mulii(*u, NQ), mulii(*v, Q))))
        return;
      *u = subis(c, n);
      if (equali1(ggcd(mulii(*u, NQ), mulii(*v, Q))))
        return;
    }
  }
}

static GEN
best_lift(GEN N, GEN Q, GEN NQ, GEN f)
{
  GEN a,b,c,d,M;
  best_point(Q, NQ, f, &c, &d);
  bezout(mulii(d, Q), mulii(NQ, c), &a, &b);
  M = mkmat2( mkcol2(mulii(d, Q), mulii(negi(N), c)),
              mkcol2(b, mulii(a, Q)));
  return qfb_mult(f, M);
}

static GEN
lift_points(GEN ell, GEN N, GEN f)
{
  GEN div = divisors(N);
  GEN tf = best_lift(N, gen_1, N, f);
  GEN yf = qimag2(tf);
  GEN Qf = gen_1;
  long l = lg(div);
  long k;
  for (k = 2; k < l; ++k)
  {
    GEN Q = gel(div, k);
    GEN NQ = diviiexact(N, Q);
    if (gequal1(gcdii(Q, NQ)))
    {
      GEN ti = best_lift(N, Q, NQ, f);
      if (gcmp(qimag2(ti), yf) > 0)
      {
        yf = qimag2(ti);
        Qf = Q;
        tf = ti;
      }
    }
  }
  return mkvec2copy(tf, stoi(myatk(ell, Qf)));
}

/***************************/
/*         Twists          */
/***************************/

static GEN
twistcurve(GEN e, GEN D)
{
  GEN D2 = sqri(D);
  GEN a4 = mulii(mulsi(-27, D2), ell_get_c4(e));
  GEN a6 = mulii(mulsi(-54, mulii(D, D2)), ell_get_c6(e));
  GEN ed = smallellinit(mkvec5(gen_0,gen_0,gen_0,a4,a6));
  return ellminimalmodel(ed, NULL);
}

static GEN
ltwist1(GEN ell, GEN D, long bitprec)
{
  pari_sp av = avma;
  GEN ed = twistcurve(ell, D);
  return gerepileuptoleaf(av, ellL1_bitprec(ed, 0, bitprec));
}

/* D discriminant (t_INT), tam Tamagawa number (t_INT), t = #E_tor (t_INT),
 * N conductor (t_INT)
 * mulf = ltwist1(E) (t_REAL, 16 correct bits) */
static long
heegner_index(GEN E, long t, GEN N, GEN tam, GEN D, GEN mulf, long prec)
{
  GEN a, b, c, ind;
  long wd22, e;
  GEN om = gabs(gimag(gel(E, 16)), prec); /* O_vol/O_re, t_REAL */

  a = divrs(divir(tam, om), 4); /* O_re*c(E)/(4*O_vol) */
  b = mulrr(divrs(sqrtr_abs(itor(D, prec)), t*t), mulf); /* sqrt(|D|)/|E_t|^2 * L(E_D,1) */
  if (equalis(D, -3))
    wd22 = 9;
  else if (equalis(D, -4))
    wd22 = 4;
  else
    wd22 = 1; /* (w(D)/2)^2 */
  c = shifti(stoi(wd22), omega(gcdii(N, D))); /* (w(D)/2)^2*2^omega(gcd(D,N)) */
  ind = sqrtr( mulri(mulrr(a, b), c) );
  ind = grndtoi(ind, &e); /* known to ~ 15 bits */
  if (e > expi(ind) - 12)
    pari_err(e_BUG,"ellheegner [contradicts Gross-Hayachi's conjecture!?]");
  if (e >= 0)
    pari_err_PREC("ellheegner (precision loss in truncation)");
  return itos(ind);
}

static long
is_tors(GEN E, GEN torsion, GEN P)
{
  long a, i;
  GEN Q, R;
  if (lg(gel(torsion,2))==1) return 0;
  a = itou(gmael(torsion,2,1));
  Q = gmael(torsion,3,1);
  if (!odd(a))
  {
    P = addell(E,P,P);
    if (ell_is_inf(P)) return 1;
    if (a==2) return 0;
    Q = addell(E,Q,Q);
    a >>=1;
  }
  if (gequal(P,Q)) return 1;
  R = Q;
  for(i=2; i<=a; i++)
  {
    R = addell(E,R,Q);
    if (gequal(R,P)) return 1;
  }
  return 0;
}

static GEN
heegner_try_point(GEN E, GEN lambdas, GEN ht, GEN torsion, GEN z, long prec)
{
  long l = lg(lambdas);
  long i, eps;
  GEN P = greal(pointell(E, z, prec)), x =  gel(P,1);
  GEN rh = subrr(ht, shiftr(ellheightoo(E, P, prec),1));
  for (i = 1; i < l; ++i)
  {
    GEN logd = shiftr(gsub(rh, gel(lambdas, i)), -1);
    GEN d, approxd = gexp(logd, prec);
    if (DEBUGLEVEL > 1)
      err_printf("Trying lambda number %ld, logd=%Ps, approxd=%Ps\n", i, logd, approxd);
    d = grndtoi(approxd, &eps);
    if (signe(d) > 0 && eps<-10)
    {
      GEN d2 = sqri(d);
      GEN approxn = mulir(d2, x);
      GEN n, ylist;
      if (DEBUGLEVEL > 1)
        err_printf("approxn=%Ps  eps=%ld\n", approxn,eps);
      n = ground(approxn);
      ylist = ellordinate(E, gdiv(n, d2), prec);
      if (lg(ylist) > 1)
      {
        GEN P = mkvec2(gdiv(n, d2), gel(ylist, 1));
        if (DEBUGLEVEL > 0)
          err_printf("Found point %Ps\n", P);
        if (!is_tors(E,torsion,P))
          return P;
      }
    }
  }
  return NULL;
}

static GEN
heegner_find_point(GEN e, GEN ht, GEN N, GEN torsion, GEN z1, long k, long prec)
{
  GEN lambdas = lambdalist(e, N, prec);
  pari_sp av = avma;
  long m;
  GEN Ore = gel(e, 15), Oim=gel(e, 16);
  for (m = 0; m < k; m++)
  {
    GEN P, z2 = divrs(addrr(z1, mulsr(m, Ore)), k);
    if (DEBUGLEVEL > 1)
      err_printf("Trying multiplier %ld\n",m);
    P = heegner_try_point(e, lambdas, ht, torsion, z2, prec);
    if (P) return P;
    if (signe(ell_get_disc(e)) > 0)
    {
      P = heegner_try_point(e, lambdas, ht, torsion, gadd(z2, gmul2n(Oim, -1)), prec);
      if (P) return P;
    }
    avma = av;
  }
  pari_err_BUG("ellheegner, point not found");
  return NULL; /* NOT REACHED */
}

static GEN
process_points(GEN ell, GEN N, long D)
{
  GEN ymin;
  GEN LISTE = listeheegner(N, stoi(D));
  long k, l = lg(LISTE);
  for (k = 2; k<l; k++)
  {
    GEN rel = lift_points(ell, N, gmael(LISTE, k, 1));
    gmael(LISTE, k, 1) = gel(rel, 1);
    gmael(LISTE, k, 2) = gmul(gel(rel, 2), gmael(LISTE, k, 2));
  }
  ymin = qimag2(gmael(LISTE, 1, 1));
  for (k = 2; k<l; k++)
  {
    GEN y = qimag2(gmael(LISTE, k, 1));
    if (gcmp(y, ymin) < 0) ymin = y;
  }
  return mkvec3(ymin,LISTE,stoi(D));
}

static void
heegner_find_disc(GEN *ppointsf, GEN *pmulf, GEN ell, GEN N)
{
  long d = 0;
  GEN M = Z_factor(mulsi(4, N)), F = gel(M,1);
  long k, s = smodis(N, 2) + 1,  lF = lg(F);
  GEN ap = cgetg(lF, t_VECSMALL);
  for (k = 1; k < lF; k++) ap[k] = equalis(ellap(ell, gel(F, k)), -1);
  for(;;)
  {
    GEN liste, listed = listedisc(s, M, ap, d);
    long k, l = lg(listed);
    if (DEBUGLEVEL)
      err_printf("List of discriminants...%Ps\n", listed);
    liste = cgetg(l, t_VEC);
    for (k = 1; k < l; ++k)
      gel(liste, k) = process_points(ell, N, listed[k]);
    liste = vecsort0(liste, gen_1, 4);
    for (k = 1; k < l; ++k)
    {
      GEN P = gel(liste,k);
      GEN mulf = ltwist1(ell, gel(P,3), 16);
      if (DEBUGLEVEL)
        err_printf(" L(E_%Ps,1) approx.  %Ps\n", gel(P,3), mulf);
      if (expo(mulf) > -8) {
        *ppointsf = P;
        *pmulf = mulf; return;
      }
    }
    d = listed[l-1];
  }
}

/* v a coordinate change from ellglobalred. Is it trivial ? (= [1,0,0,0]) */
static int
trivial_change(GEN v)
{
  return (equali1(gel(v,1))
          && !signe(gel(v,2)) && !signe(gel(v,3)) && !signe(gel(v,4)));
}

GEN
ellheegner(GEN E)
{
  pari_sp av = avma;
  GEN z, vDi;
  GEN P, ht, pointsf, pts, points, ymin, D, mulf, s, w1;
  long ind, lint;
  long i,k,l;
  long bitprec=16, prec=nbits2prec(bitprec)+1;
  pari_timer T;
  GEN red = ellglobalred(E), N = gel(red, 1), cb = gel(red,2);
  GEN tam = signe(ell_get_disc(E))>0 ? shifti(gel(red,3),1):gel(red,3);
  GEN torsion = elltors(E);
  long wtor = itos( gel(torsion,1) );

  if (trivial_change(cb)) cb = NULL; else E = ellchangecurve(E, cb);
  if (ellrootno(E, NULL) == 1)
    pari_err(e_MISC, "The curve has even analytic rank");
  w1 = gel(E,15); /* real period */
  while (1)
  {
    GEN hnaive;
    GEN l1 = ellL1_bitprec(E, 1, bitprec);
    long bitneeded;
    if (expo(l1) < 1 - bitprec/2)
      pari_err(e_MISC, "The curve has (probably) analytic rank > 1");
    ht = divrr(mulrs(l1, wtor * wtor), mulri(w1, tam));
    if (DEBUGLEVEL) err_printf("Expected height=%Ps\n", ht);
    hnaive = hnaive_max(E, ht);
    if (DEBUGLEVEL) err_printf("Naive height <= %Ps\n", hnaive);
    bitneeded = itos(gceil(divrr(hnaive, mplog2(prec)))) + 10;
    if (DEBUGLEVEL) err_printf("precision = %ld\n", bitneeded);
    if (bitprec>=bitneeded) break;
    bitprec = bitneeded;
    prec = nbits2prec(bitprec)+1;
    E = ellinit(E, prec);
    w1 = gel(E,15);
  }
  heegner_find_disc(&pointsf, &mulf, E, N);
  ymin = gsqrt(gel(pointsf, 1), prec);
  if (DEBUGLEVEL) err_printf("N = %Ps, ymin*N = %Ps\n",N,gmul(ymin,N));
  pts = gel(pointsf, 2);
  D = gel(pointsf, 3);
  vDi = gsqrt(negi(D), prec);
  l = lg(pts);
  points = cgetg(l, t_VEC);
  for (i = 1; i < l; ++i)
    gel(points, i) = qfb_root(gmael(pts, i, 1), vDi);
  if (DEBUGLEVEL) timer_start(&T);
  ind = heegner_index(E, wtor, N, tam, D, mulf, prec);
  if (DEBUGLEVEL)
    timer_printf(&T,"heegner_index");
  s = heegner_psi(E, N, ymin, points, bitprec);
  if (DEBUGLEVEL)
    timer_printf(&T,"heegner_psi");
  z = mulir(gmael(pts, 1, 2), gel(s, 1));
  for (k = 2; k < l; ++k)
    z = addrr(z, mulir(gmael(pts, k, 2), gel(s, k)));
  if (DEBUGLEVEL) err_printf("z=%Ps\n", z);
  z = gsub(z, gmul(w1, ground(gdiv(z, w1))));
  lint = lg(gel(torsion, 2)) >= 2 ? cgcd(ind, itos(gmael(torsion, 2, 1))): 1;
  P = heegner_find_point(E, ht, N, torsion, gmulsg(2*lint, z), lint*2*ind, prec);
  if (DEBUGLEVEL)
    timer_printf(&T,"heegner_find_point");
  if (cb)
    P = ellchangepointinv(P, cb);
  return gerepilecopy(av, P);
}
