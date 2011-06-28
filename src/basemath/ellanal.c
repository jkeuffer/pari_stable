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
  M2 = itos(ceilr(gmul2n(x,1))); /* >= 2x */
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
  GEN M1 = ceilr(divsr(7*bit_accuracy(prec)+1, X));
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
init_el(struct ellld *el, GEN E, long *parity, long prec)
{
  GEN eX;
  checksmallell(E);
  el->E = ell_to_small_red(E, &el->N);
  el->X = divrr(Pi2n(1, prec), sqrtr(itor(el->N, prec))); /* << 1 */
  eX = mpexp(el->X);
  if (realprec(eX) > prec) eX = rtor(eX, prec); /* avoid spurious accuracy increase */
  el->eX = eX;
  el->emX = invr(el->eX);
  el->epsbit = bit_accuracy(prec)+1;
  *parity = (ellrootno_global(el->E, el->N) > 0)? 0: 1; /* rank parity */
}

GEN
ellL1(GEN E, long r, long prec)
{
  pari_sp av = avma;
  struct ellld el;
  struct bg_data bg;
  long parity;
  if (r<0) pari_err(talker,"derivative order must be nonnegative");
  init_el(&el, E, &parity, prec);
  if (parity != (r & 1)) return gen_0;
  return gerepileuptoleaf(av, ellL1_i(&el, &bg, r, NULL, prec));
}

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
    eps = real2n(-bit_accuracy(prec)/2+1, DEFAULTPREC);
  else
    if (typ(eps) != t_REAL) {
      eps = gtofp(eps, DEFAULTPREC);
      if (typ(eps) != t_REAL) pari_err(typeer, "ellanalyticrank");
    }
  init_el(&el, e, &rk, prec); /* set rk to rank parity (0 or 1) */
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
