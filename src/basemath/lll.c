/* $Id$

Copyright (C) 2008  The PARI group.

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

/* default quality ratio for LLL: 99/100 */
static const long LLLDFT = 100;

/* assume flag & (LLL_KER|LLL_IM|LLL_ALL). LLL_INPLACE implies LLL_IM */
static GEN
lll_trivial(GEN x, long flag)
{
  GEN y;
  if (lg(x) == 1)
  { /* dim x = 0 */
    if (! (flag & LLL_ALL)) return cgetg(1,t_MAT);
    y=cgetg(3,t_VEC);
    gel(y,1) = cgetg(1,t_MAT);
    gel(y,2) = cgetg(1,t_MAT); return y;
  }
  /* dim x = 1 */
  if (gcmp0(gel(x,1)))
  {
    if (flag & LLL_KER) return matid(1);
    if (flag & LLL_IM)  return cgetg(1,t_MAT); /* also ok for LLL_INPLACE */
    y = cgetg(3,t_VEC);
    gel(y,1) = matid(1);
    gel(y,2) = cgetg(1,t_MAT); return y;
  }
  if (flag & LLL_INPLACE) return gcopy(x);
  if (flag & LLL_KER) return cgetg(1,t_MAT);
  if (flag & LLL_IM)  return matid(1);
  y=cgetg(3,t_VEC);
  gel(y,1) = cgetg(1,t_MAT);
  gel(y,2) = (flag & LLL_GRAM)? gcopy(x): matid(1);
  return y;
}

static GEN
lll_get_im(GEN h, long k)
{
  long l = lg(h) - k;
  h += k; h[0] = evaltyp(t_MAT) | evallg(l);
  return h;
}

/* k = dim Kernel */
static GEN
lll_finish(GEN h, long k, long flag)
{
  GEN g;
  if (flag & LLL_KER) { setlg(h,k+1); return h; }
  if (flag & LLL_IM) return lll_get_im(h, k);
  g = vecslice(h,1,k);
  return mkvec2(g, lll_get_im(h, k));
}

/********************************************************************/
/**                                                                **/
/**                   FPLLL (adapted from D. Stehle's code)        **/
/**                                                                **/
/********************************************************************/
/* Babai() and fplll() are a conversion to libpari API and data types 
   of the file proved.c in fplll-1.3 by Damien Stehle'.

  Copyright 2005, 2006 Damien Stehle'.

  This program is free software; you can redistribute it and/or modify it
  under the terms of the GNU General Public License as published by the
  Free Software Foundation; either version 2 of the License, or (at your
  option) any later version.

  This program implements ideas from the paper "Floating-point LLL Revisited",
  by Phong Nguyen and Damien Stehle', in the Proceedings of Eurocrypt'2005,
  Springer-Verlag; and was partly inspired by Shoup's NTL library:
  http://www.shoup.net/ntl/
*/

/* x - s*y */
static GEN
submuls(GEN x, GEN y, long s)
{
  pari_sp av;
  if (!signe(y)) return x;
  av = avma;
  (void)new_chunk(3+lgefint(x)+lgefint(y)); /* HACK */
  y = mulsi(s,y);
  avma = av; return subii(x, y);
}
static GEN
submul(GEN x, GEN y, GEN s)
{
  pari_sp av;
  if (!signe(y)) return x;
  av = avma;
  (void)new_chunk(lgefint(s)+lgefint(x)+lgefint(y)); /* HACK */
  y = mulii(s,y);
  avma = av; return subii(x, y);
}

/***********************************************/
/* Babai's Nearest Plane algorithm (iterative) */
/***********************************************/
/* Size-reduces b_kappa using mu_{i,j} and r_{i,j} for j<=i <kappa
Updates B (kappa); computes mu_{kappa,j}, r_{kappa,j} for j<=kappa, and s(kappa)
mu, r, s updated in place (affrr).
*/
static long
Babai(pari_sp av, long kappa, GEN *pG, GEN *pB, GEN *pU, GEN mu, GEN r, GEN s,
      long a, long zeros, long maxG, long n, GEN eta, GEN etaplus1, long prec)
{
  pari_sp lim = stack_lim(av,2);
  GEN B = *pB, G = *pG, U = *pU, tmp, rtmp, ztmp;
  long i, j, k, test, aa = (a > zeros)? a : zeros+1;
  long d = U ? lg(U)-1: 0;
  /* HACK: we set d = 0 (resp. n = 0) to avoid updating U (resp. B) */
  GEN maxmu = gen_0, max2mu = gen_0, max3mu;
  do {
    test=0;
    if (low_stack(lim, stack_lim(av,2)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"Babai");
      gerepileall(av,U?5:4,&B,&G,&maxmu,&max2mu,&U);
    }
    /* Step2: compute the GSO for stage kappa */
    max3mu = max2mu;
    max2mu = maxmu;
    maxmu = real_0(prec);
    for (j=aa; j<kappa; j++)
    {
      pari_sp btop = avma;
      k = zeros+1;
      if (j > k)
      {
        tmp  = mulrr(gmael(mu,j,k), gmael(r,kappa,k));
        rtmp = subir(gmael(G,kappa,j), tmp);
        for (k++; k<=j-1; k++)
        {
          tmp  = mulrr(gmael(mu,j,k), gmael(r,kappa,k));
          rtmp = subrr(rtmp,tmp);
        }
        affrr(rtmp, gmael(r,kappa,j));
      }
      else
        affir(gmael(G,kappa,j), gmael(r,kappa,j));
      affrr(divrr(gmael(r,kappa,j), gmael(r,j,j)), gmael(mu,kappa,j));
      if (absr_cmp(maxmu, gmael(mu,kappa,j))<0)
        maxmu = gmael(mu,kappa,j);
      avma = btop;
    }
    maxmu = absr(maxmu);
    if (typ(max3mu)==t_REAL && absr_cmp(max3mu, shiftr(max2mu, 5))<=0)
    {
      *pB = B; *pG = G; *pU = U;
      if (DEBUGLEVEL>5) fprintferr("prec too low\n");
      return kappa;
    }

    /* Step3--5: compute the X_j's  */
    for (j=kappa-1; j>zeros; j--)
    {
      tmp = gmael(mu,kappa,j);
      if (absr_cmp(tmp, eta) <= 0) continue; /* (essentially) size-reduced */

      test = 1;
      /* we consider separately the case |X| = 1 */
      if (absr_cmp(tmp, etaplus1) <= 0)
      {
        if (signe(tmp) > 0)
        { /* in this case, X = 1 */
          pari_sp btop = avma;
          for (k=zeros+1; k<j; k++)
            affrr(subrr(gmael(mu,kappa,k), gmael(mu,j,k)), gmael(mu,kappa,k));
          avma = btop;

          for (i=1; i<=n; i++)
            gmael(B,kappa,i) = subii(gmael(B,kappa,i), gmael(B,j,i));
          for (i=1; i<=d; i++)
            gmael(U,kappa,i) = subii(gmael(U,kappa,i), gmael(U,j,i));
          btop = avma;
          ztmp = subii(gmael(G,j,j), shifti(gmael(G,kappa,j), 1));
          ztmp = addii(gmael(G,kappa,kappa), ztmp);
          gmael(G,kappa,kappa) = gerepileuptoint(btop, ztmp);
          for (i=1; i<=j; i++)
            gmael(G,kappa,i) = subii(gmael(G,kappa,i), gmael(G,j,i));
          for (i=j+1; i<kappa; i++)
            gmael(G,kappa,i) = subii(gmael(G,kappa,i), gmael(G,i,j));
          for (i=kappa+1; i<=maxG; i++)
            gmael(G,i,kappa) = subii(gmael(G,i,kappa), gmael(G,i,j));
        }
        else
        { /* otherwise X = -1 */
          pari_sp btop = avma;
          for (k=zeros+1; k<j; k++)
            affrr(addrr(gmael(mu,kappa,k), gmael(mu,j,k)), gmael(mu,kappa,k));
          avma = btop;

          for (i=1; i<=n; i++)
            gmael(B,kappa,i) = addii(gmael(B,kappa,i), gmael(B,j,i));
          for (i=1; i<=d; i++)
            gmael(U,kappa,i) = addii(gmael(U,kappa,i),gmael(U,j,i));
          btop = avma;
          ztmp = addii(gmael(G,j,j), shifti(gmael(G,kappa,j), 1));
          ztmp = addii(gmael(G,kappa,kappa), ztmp);
          gmael(G,kappa,kappa) = gerepileuptoint(btop, ztmp);
          for (i=1; i<=j; i++)
            gmael(G,kappa,i) = addii(gmael(G,kappa,i), gmael(G,j,i));
          for (i=j+1; i<kappa; i++)
            gmael(G,kappa,i) = addii(gmael(G,kappa,i), gmael(G,i,j));
          for (i=kappa+1; i<=maxG; i++)
            gmael(G,i,kappa) = addii(gmael(G,i,kappa), gmael(G,i,j));
        }
      } else {        	
        /* we have |X| >= 2 */
        pari_sp btop;
        ztmp = roundr_safe(tmp);
        btop = avma;
        for (k=zeros+1; k<j; k++)
        {
          rtmp = subrr(gmael(mu,kappa,k), mulir(ztmp, gmael(mu,j,k)));
          affrr(rtmp, gmael(mu,kappa,k));
        }
        avma = btop;
        if (!is_bigint(ztmp))
        { /* X is stored in a long signed int */
          long xx = itos(ztmp);

          for (i=1; i<=n; i++)
            gmael(B,kappa,i) = submuls(gmael(B,kappa,i), gmael(B,j,i), xx);
          for (i=1; i<=d; i++)
            gmael(U,kappa,i) = submuls(gmael(U,kappa,i), gmael(U,j,i), xx);
          btop = avma;
          ztmp = shifti(mulis(gmael(G,kappa,j), xx), 1);
          ztmp = subii(mulii(gmael(G,j,j), sqrs(xx)), ztmp);
          ztmp = addii(gmael(G,kappa,kappa), ztmp);
          gmael(G,kappa,kappa) = gerepileuptoint(btop, ztmp);
          for (i=1; i<=j; i++)
            gmael(G,kappa,i) = submuls(gmael(G,kappa,i), gmael(G,j,i), xx);
          for (i=j+1; i<kappa; i++)
            gmael(G,kappa,i) = submuls(gmael(G,kappa,i), gmael(G,i,j), xx);
          for (i=kappa+1; i<=maxG; i++)
            gmael(G,i,kappa) = submuls(gmael(G,i,kappa), gmael(G,i,j), xx);
        } else {
          GEN tmp2  = itor(ztmp,prec);
          long expo = expo(tmp2)-bit_accuracy(lg(tmp2));
          GEN X = shifti(gfloor2n(tmp2, -expo), expo);
          pari_sp btop;

          for (i=1; i<=n; i++)
            gmael(B,kappa,i) = submul(gmael(B,kappa,i), gmael(B,j,i), X);
          for (i=1; i<=d; i++)
            gmael(U,kappa,i) = submul(gmael(U,kappa,i), gmael(U,j,i), X);
          btop = avma;
          ztmp = shifti(mulii(gmael(G,kappa,j), X), 1);
          ztmp = subii(mulii(gmael(G,j,j), sqri(X)), ztmp);
          ztmp = addii(gmael(G,kappa,kappa), ztmp);
          gmael(G,kappa,kappa) = gerepileuptoint(btop, ztmp);
          for (i=1; i<=j; i++)
            gmael(G,kappa,i) = submul(gmael(G,kappa,i), gmael(G,j,i), X);
          for (   ; i<kappa; i++)
            gmael(G,kappa,i) = submul(gmael(G,kappa,i), gmael(G,i,j), X);
          for (i=kappa+1; i<=maxG; i++)
            gmael(G,i,kappa) = submul(gmael(G,i,kappa), gmael(G,i,j), X);
        }
      }
    }
    /* Anything happened? */
    if (test) aa = zeros+1;
  } while (test);

  affir(gmael(G,kappa,kappa), gel(s,zeros+1));
  /* the last s[kappa-1]=r[kappa][kappa] is computed only if kappa increases */
  av = avma;
  for (k=zeros+1; k<=kappa-2; k++)
  {
    tmp = subrr(gel(s,k), mulrr(gmael(mu,kappa,k), gmael(r,kappa,k)));
    affrr(tmp, gel(s,k+1));
  }
  *pB = B; *pG = G; *pU = U; avma = av;
  return 0;
}

static void
rotate(GEN mu, long kappa2, long kappa, long d)
{
  long i, j;
  pari_sp av = avma;
  GEN mutmp = shallowcopy(gel(mu,kappa2));
  for (i=kappa2; i>kappa; i--)
    for (j=1;j<=d;j++) gmael(mu,i,j) = gmael(mu,i-1,j);
  for (j=1;j<=d;j++)   gmael(mu,kappa,j) = gel(mutmp,j);
  avma = av;
}

/* ****************** */
/* The LLL Algorithm  */
/* ****************** */

/* LLL-reduces the integer matrix(ces) (G,B,U)? "in place" */
static GEN
fplll(GEN *ptrB, GEN *ptrU, GEN *ptrr, double DELTA, double ETA, long flag, long prec)
{
  const long inplace = flag & LLL_INPLACE;
  const long gram = flag & LLL_GRAM; /*Gram matrix*/
  const long keepfirst = flag & LLL_KEEP_FIRST; /*never swap with first vector*/
  pari_sp av, av2, lim;
  long kappa, kappa2, d, n, i, j, zeros, kappamax, maxG, bab;
  GEN G, mu, r, s, tmp, SPtmp, alpha;
  GEN delta = dbltor(DELTA), eta = dbltor(ETA), etaplus1 = dbltor(ETA+1);
  const long triangular = 0;
  pari_timer T;
  GEN B = *ptrB, U;

  d = lg(B)-1;
  if (gram)
  {
    G = B;
    n = d;
    B = cgetg(1, t_VECSMALL); /* dummy */
  }
  else
  {
    G = zeromatcopy(d,d);
    n = lg(gel(B,1))-1;
  }
  U = inplace? NULL: *ptrU;

  if(DEBUGLEVEL>=4)
  {
    TIMERstart(&T);
    fprintferr("Entering L^2: LLL-parameters (%Z.3f,%.3Zf), working precision %d words\n",delta,eta, prec);
  }

  mu = cgetg(d+1, t_MAT);
  r  = cgetg(d+1, t_MAT);
  s  = cgetg(d+1, t_VEC);
  for (j = 1; j <= d; j++)
  {
    GEN M = cgetg(d+1, t_COL), R = cgetg(d+1, t_COL);
    gel(mu,j)= M;
    gel(r,j) = R;
    gel(s,j) = cgetr(prec);
    for (i = 1; i <= d; i++) {
      gel(R,i) = cgetr(prec);
      gel(M,i) = cgetr(prec);
    }
  }
  SPtmp = zerovec(d+1);
  alpha = cgetg(d+1, t_VECSMALL);
  av = avma; lim = stack_lim(av, 2);

  /* Step2: Initializing the main loop */
  kappamax = 1;
  i = 1;
  maxG = d; /* later updated to kappamax if (!gram) */

  do {
    if (!gram) gmael(G,i,i) = ZV_dotsquare(gel(B,i));
    affir(gmael(G,i,i), gmael(r,i,i));
  } while (signe(gmael(G,i,i)) == 0 && (++i <=d));
  zeros = i-1; /* all vectors B[i] with i <= zeros are zero vectors */
  kappa = i;
  if (zeros < d) affir(gmael(G,zeros+1,zeros+1), gmael(r,zeros+1,zeros+1));
  for (i=zeros+1; i<=d; i++) alpha[i]=1;

  while (++kappa <= d)
  {
    if (kappa>kappamax)
    {
      if (DEBUGLEVEL>=6) fprintferr("K%ld ",kappa);
      kappamax = kappa;
      if (!gram) {
        for (i=zeros+1; i<=kappa; i++)
          gmael(G,kappa,i) = ZV_dotproduct(gel(B,kappa), gel(B,i));
        maxG = kappamax;
      }
    }
    /* Step3: Call to the Babai algorithm, mu,r,s updated in place */
    bab = Babai(av, kappa, &G,&B,&U, mu,r,s, alpha[kappa], zeros, maxG,
      gram? 0 : ((triangular && kappamax <= n) ? kappamax: n),
      eta, etaplus1, prec);
    if (bab) {*ptrB=(gram?G:B); *ptrU=U; return NULL; }

    av2 = avma;
    tmp = mulrr(gmael(r,kappa-1,kappa-1), delta);
    if (cmprr(tmp, gel(s,kappa-1)) <= 0)
    { /* Step4: Success of Lovasz's condition */
      alpha[kappa] = kappa;
      tmp = mulrr(gmael(mu,kappa,kappa-1), gmael(r,kappa,kappa-1));
      affrr(subrr(gel(s,kappa-1), tmp), gmael(r,kappa,kappa));
      avma = av2;
    }
    else
    { /* Step5: Find the right insertion index kappa, kappa2 = initial kappa */
      kappa2 = kappa;
      do {
        kappa--;
        if (kappa<zeros+2 + (keepfirst ? 1: 0)) break;
        tmp = mulrr(gmael(r,kappa-1,kappa-1), delta);
      } while (cmprr(gel(s,kappa-1), tmp) <=0 );
      avma = av2;

      for (i=kappa; i<kappa2; i++)
        if (kappa <= alpha[i]) alpha[i] = kappa;
      for (i=kappa2; i>kappa; i--) alpha[i] = alpha[i-1];
      for (i=kappa2+1; i<=kappamax; i++)
        if (kappa < alpha[i]) alpha[i] = kappa;
      alpha[kappa] = kappa;

      /* Step6: Update the mu's and r's */
      rotate(mu,kappa2,kappa,d);
      rotate(r,kappa2,kappa,d);
      affrr(gel(s,kappa), gmael(r,kappa,kappa)); 

      /* Step7: Update B, G, U */
      if (!gram) rotate(B,kappa2,kappa,n);
      if (U) rotate(U,kappa2,kappa,d);

      for (i=1; i<=kappa2; i++) gel(SPtmp,i) = gmael(G,kappa2,i);
      for (i=kappa2+1; i<=maxG; i++) gel(SPtmp,i) = gmael(G,i,kappa2);
      for (i=kappa2; i>kappa; i--)
      {
        for (j=1; j<kappa; j++) gmael(G,i,j) = gmael(G,i-1,j);
        gmael(G,i,kappa) = gel(SPtmp,i-1);
        for (j=kappa+1; j<=i; j++) gmael(G,i,j) = gmael(G,i-1,j-1);
        for (j=kappa2+1; j<=maxG; j++) gmael(G,j,i) = gmael(G,j,i-1);
      }
      for (i=1; i<kappa; i++) gmael(G,kappa,i) = gel(SPtmp,i);
      gmael(G,kappa,kappa) = gel(SPtmp,kappa2);
      for (i=kappa2+1; i<=maxG; i++) gmael(G,i,kappa) = gel(SPtmp,i);

      /* Step8: Prepare the next loop iteration */
      if (kappa == zeros+1 && !signe(gmael(G,kappa,kappa)))
      {
        zeros++; kappa++;
        affir(gmael(G,kappa,kappa), gmael(r,kappa,kappa));
      }
    }
  }

  if (DEBUGLEVEL>=4) msgTIMER(&T,"LLL");
  if (ptrr) *ptrr = mattodiagonal_i(r);
  if (U && flag & (LLL_IM|LLL_KER|LLL_ALL)) U = lll_finish(U, zeros, flag);
  if (gram)
  {
    if (!inplace) return U;
    for (i = 1; i <= d; i++)
      for (j = i+1; j <= d; j++) gmael(G,i,j) = gmael(G,j,i);
    return G;
  }
  return inplace? B: U;
}

static long
good_prec(long d, double delta, double eta)
{
  double t = eta+1, rho = t*t / (delta - eta*eta);
  long goodprec = (ulong) (7.0 + 0.2*d + d*log2(rho)
      +  2.0 * log ((double) d) - log2( (eta-0.5)*(1.0-delta) ));
  return nbits2prec(goodprec); 
}

/* Assume x a ZM, if ptB != NULL, set it to Gram-Schmidt (squared) norms */
GEN
LLLint(GEN x, long D, long flag, GEN *B)
{
  pari_sp ltop=avma;
  const double ETA = 0.51, DELTA = (D-1) / (double)D;
  const long inplace = flag & LLL_INPLACE;
  long p,prec, d, n = lg(x)-1;
  GEN U;
  if (n <= 1) return lll_trivial(x, flag);
  d = lg(gel(x,1))-1;
  prec = good_prec(d,DELTA,ETA); 
  x = shallowcopy(x);
  U = inplace?NULL:matid(n);
  for (p = min(3,prec); p <= prec; p++)
  {
    GEN m = fplll(&x, &U, B, DELTA, ETA, flag, p);
    if (m) return m;
    gerepileall(ltop,inplace?1:2,&x,&U);
  }
  pari_err(bugparier,"LLLint");
  return NULL;
}

/********************************************************************/
/**                                                                **/
/**                        LLL OVER K[X]                           **/
/**                                                                **/
/********************************************************************/
static int
pslg(GEN x)
{
  long tx;
  if (gcmp0(x)) return 2;
  tx = typ(x); return is_scalar_t(tx)? 3: lg(x);
}

static int
REDgen(long k, long l, GEN h, GEN L, GEN B)
{
  GEN q, u = gcoeff(L,k,l);
  long i;

  if (pslg(u) < pslg(B)) return 0;

  q = gneg(gdeuc(u,B));
  gel(h,k) = gadd(gel(h,k), gmul(q,gel(h,l)));
  for (i=1; i<l; i++) gcoeff(L,k,i) = gadd(gcoeff(L,k,i), gmul(q,gcoeff(L,l,i)));
  gcoeff(L,k,l) = gadd(gcoeff(L,k,l), gmul(q,B)); return 1;
}

static int
do_SWAPgen(GEN h, GEN L, GEN B, long k, GEN fl, int *flc)
{
  GEN p1, la, la2, Bk;
  long ps1, ps2, i, j, lx;

  if (!fl[k-1]) return 0;

  la = gcoeff(L,k,k-1); la2 = gsqr(la);
  Bk = gel(B,k);
  if (fl[k])
  {
    GEN q = gadd(la2, gmul(gel(B,k-1),gel(B,k+1)));
    ps1 = pslg(gsqr(Bk));
    ps2 = pslg(q);
    if (ps1 <= ps2 && (ps1 < ps2 || !*flc)) return 0;
    *flc = (ps1 != ps2);
    gel(B,k) = gdiv(q, Bk);
  }

  lswap(h[k-1], h[k]); lx = lg(L);
  for (j=1; j<k-1; j++) lswap(coeff(L,k-1,j), coeff(L,k,j));
  if (fl[k])
  {
    for (i=k+1; i<lx; i++)
    {
      GEN t = gcoeff(L,i,k);
      p1 = gsub(gmul(gel(B,k+1),gcoeff(L,i,k-1)), gmul(la,t));
      gcoeff(L,i,k) = gdiv(p1, Bk);
      p1 = gadd(gmul(la,gcoeff(L,i,k-1)), gmul(gel(B,k-1),t));
      gcoeff(L,i,k-1) = gdiv(p1, Bk);
    }
  }
  else if (!gcmp0(la))
  {
    p1 = gdiv(la2, Bk);
    gel(B,k+1) = gel(B,k) = p1;
    for (i=k+2; i<=lx; i++) gel(B,i) = gdiv(gmul(p1,gel(B,i)),Bk);
    for (i=k+1; i<lx; i++)
      gcoeff(L,i,k-1) = gdiv(gmul(la,gcoeff(L,i,k-1)), Bk);
    for (j=k+1; j<lx-1; j++)
      for (i=j+1; i<lx; i++)
	gcoeff(L,i,j) = gdiv(gmul(p1,gcoeff(L,i,j)), Bk);
  }
  else
  {
    gcoeff(L,k,k-1) = gen_0;
    for (i=k+1; i<lx; i++)
    {
      gcoeff(L,i,k) = gcoeff(L,i,k-1);
      gcoeff(L,i,k-1) = gen_0;
    }
    B[k] = B[k-1]; fl[k] = 1; fl[k-1] = 0;
  }
  return 1;
}

static void
incrementalGSgen(GEN x, GEN L, GEN B, long k, GEN fl)
{
  GEN u = NULL; /* gcc -Wall */
  long i, j, tu;
  for (j=1; j<=k; j++)
    if (j==k || fl[j])
    {
      u = gcoeff(x,k,j); tu = typ(u);
      if (! is_extscalar_t(tu)) pari_err(typeer,"incrementalGSgen");
      for (i=1; i<j; i++)
	if (fl[i])
	{
	  u = gsub(gmul(gel(B,i+1),u), gmul(gcoeff(L,k,i),gcoeff(L,j,i)));
	  u = gdiv(u, gel(B,i));
	}
      gcoeff(L,k,j) = u;
    }
  if (gcmp0(u)) B[k+1] = B[k];
  else
  {
    B[k+1] = coeff(L,k,k); gcoeff(L,k,k) = gen_1; fl[k] = 1;
  }
}

static GEN
lllgramallgen(GEN x, long flag)
{
  long lx = lg(x), i, j, k, l, n;
  pari_sp av, lim;
  GEN B, L, h, fl;
  int flc;

  n = lx-1; if (n<=1) return lll_trivial(x,flag);
  if (lg(x[1]) != lx) pari_err(mattype1,"lllgramallgen");

  fl = cgetg(lx, t_VECSMALL);

  av = avma; lim = stack_lim(av,1);
  B = scalarcol_shallow(gen_1, lx);
  L = cgetg(lx,t_MAT);
  for (j=1; j<lx; j++) { gel(L,j) = zerocol(n); fl[j] = 0; }

  h = matid(n);
  for (i=1; i<lx; i++)
    incrementalGSgen(x, L, B, i, fl);
  flc = 0;
  for(k=2;;)
  {
    if (REDgen(k, k-1, h, L, gel(B,k))) flc = 1;
    if (do_SWAPgen(h, L, B, k, fl, &flc)) { if (k > 2) k--; }
    else
    {
      for (l=k-2; l>=1; l--)
	if (REDgen(k, l, h, L, gel(B,l+1))) flc = 1;
      if (++k > n) break;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"lllgramallgen");
      gerepileall(av,3,&B,&L,&h);
    }
  }
  k=1; while (k<lx && !fl[k]) k++;
  return lll_finish(h,k-1,flag);
}

static GEN
lllallgen(GEN x, long flag)
{
  pari_sp av = avma;
  if ((flag & LLL_GRAM) == 0) x = gram_matrix(x);
  return gerepilecopy(av, lllgramallgen(x, flag));
}
GEN
lllgen(GEN x) { return lllallgen(x, LLL_IM); }
GEN
lllkerimgen(GEN x) { return lllallgen(x, LLL_ALL); }
GEN
lllgramgen(GEN x)  { return lllallgen(x, LLL_IM|LLL_GRAM); }
GEN
lllgramkerimgen(GEN x)  { return lllallgen(x, LLL_ALL|LLL_GRAM); }

/* Assume x a ZM. Return x * lllint(x). No garbage collection */
GEN
lllint_ip(GEN x, long D) { return LLLint(x,D,LLL_INPLACE,NULL); }

static GEN
lllall_i(GEN x, long D, long flag)
{
  RgM_check_ZM(x, "lllall");
  return LLLint(x, D, flag, NULL);
}
static GEN
lllall(GEN x, long D, long flag)
{
  pari_sp av = avma;
  return gerepilecopy(av, lllall_i(x,D,flag));
}
GEN
lllint(GEN x) { return lllall(x,LLLDFT, LLL_IM); }
GEN
lllkerim(GEN x) { return lllall(x,LLLDFT, LLL_ALL); }
GEN
lllgramint(GEN x) { return lllall(x,LLLDFT, LLL_IM | LLL_GRAM); }
GEN
lllgramkerim(GEN x) { return lllall(x,LLLDFT, LLL_ALL | LLL_GRAM); }

static GEN
rescale_to_int(GEN x)
{
  long e, i,j, lx, hx, emin;
  GEN D = gen_1;
  int exact = 1;

  lx = lg(x); if (lx == 1) return x;
  hx = lg(x[1]);
  emin = HIGHEXPOBIT;
  for (j = 1; j < lx; j++)
    for (i = 1; i < hx; i++)
    {
      GEN c = gcoeff(x,i,j);
      switch(typ(c))
      {
        case t_REAL:
          exact = 0;
          if (!signe(c)) continue;
          e = expo(c) - bit_accuracy(lg(c));
          break;
        case t_INT:
          if (!signe(c)) continue;
          e = expi(c) + 32;
          break;
        case t_FRAC:
          e = expi(gel(c,1)) - expi(gel(c,2)) + 32;
          if (exact) D = lcmii(D, gel(c,2));
          break;
        default:
          pari_err(typeer,"rescale_to_int");
          return NULL; /* not reached */
      }
      if (e < emin) emin = e;
    }
  if (exact) return D == gen_1 ? x: Q_muli_to_int(x, D);
  return gcvtoi(gmul2n(x, -emin), &e);
}

/* If gram = 1, x = Gram(b_i), x = (b_i) otherwise
 * Quality ratio = delta = (D-1)/D. Suggested values: D = 4 or D = 100 */
GEN
lllfp(GEN x, long D, long flag)
{
  long n = lg(x)-1;
  pari_sp av = avma;
  GEN h;
  if (n <= 1) return matid(n);
  h = LLLint(flag & LLL_INPLACE? x: rescale_to_int(x), D, flag, NULL);
  return gerepilecopy(av, h);
}

GEN
lllgram(GEN x) { return lllfp(x,LLLDFT,LLL_GRAM|LLL_IM); }
GEN
lll(GEN x) { return lllfp(x,LLLDFT,LLL_IM); }

GEN
qflll0(GEN x, long flag)
{
  if (typ(x) != t_MAT) pari_err(typeer,"qflll");
  switch(flag)
  {
    case 0: return lll(x);
    case 1: return lllint(x);
    case 2: return lllintpartial(x);
    case 4: return lllkerim(x);
    case 5: return lllkerimgen(x);
    case 8: return lllgen(x);
    default: pari_err(flagerr,"qflll");
  }
  return NULL; /* not reached */
}

GEN
qflllgram0(GEN x, long flag)
{
  if (typ(x) != t_MAT) pari_err(typeer,"qflllgram");
  switch(flag)
  {
    case 0: return lllgram(x);
    case 1: return lllgramint(x);
    case 4: return lllgramkerim(x);
    case 5: return lllgramkerimgen(x);
    case 8: return lllgramgen(x);
    default: pari_err(flagerr,"qflllgram");
  }
  return NULL; /* not reached */
}

/********************************************************************/
/**                                                                **/
/**                          INTEGRAL LLL                          **/
/**         (faster than fplll for incremental knapsacks)          **/
/**                                                                **/
/********************************************************************/
/* L[k,] += q * L[l,], l < k. Inefficient if q = 0 */
static void
Zupdate_row(long k, long l, GEN q, GEN L, GEN B)
{
  long i, qq = itos_or_0(q);
  if (!qq)
  {
    for(i=1;i<l;i++)  gcoeff(L,k,i) = addii(gcoeff(L,k,i),mulii(q,gcoeff(L,l,i)));
    gcoeff(L,k,l) = addii(gcoeff(L,k,l), mulii(q,B));
    return;
  }
  if (qq == 1) {
    for (i=1;i<l; i++) gcoeff(L,k,i) = addii(gcoeff(L,k,i),gcoeff(L,l,i));
    gcoeff(L,k,l) = addii(gcoeff(L,k,l), B);
  } else if (qq == -1) {
    for (i=1;i<l; i++) gcoeff(L,k,i) = subii(gcoeff(L,k,i),gcoeff(L,l,i));
    gcoeff(L,k,l) = subii(gcoeff(L,k,l), B);
  } else {
    for(i=1;i<l;i++) gcoeff(L,k,i) = addii(gcoeff(L,k,i),mulsi(qq,gcoeff(L,l,i)));
    gcoeff(L,k,l) = addii(gcoeff(L,k,l), mulsi(qq,B));
  }
}

static void
ZRED(long k, long l, GEN x, GEN L, GEN B, long K)
{
  pari_sp av = avma;
  GEN q = truedivii(addii(B,shifti(gcoeff(L,k,l),1)), shifti(B,1));
  if (!signe(q)) { avma = av; return; }
  togglesign(q);
  Zupdate_row(k,l,q,L,B);
  ZC_lincomb1_inplace(gel(x,k), gel(x,l), q);
}

static int
do_ZSWAP(GEN x, GEN L, GEN B, long kmax, long k, long D, GEN fl)
{
  GEN la,la2,p1,Bk;
  long i, j, lx;
  pari_sp av;

  if (!fl[k-1]) return 0;
  av = avma;
  la = gcoeff(L,k,k-1); la2 = sqri(la);
  Bk = gel(B,k);
  if (fl[k])
  {
    GEN q;
    if (!D) return 0; /* only lswap non-kernel + kernel vector */
    q = addii(la2, mulii(gel(B,k-1),gel(B,k+1)));
    if (cmpii(mulsi(D-1,sqri(Bk)), mulsi(D,q)) <= 0) {
      avma = av; return 0;
    }
    gel(B,k) = diviiexact(q, Bk);
  }
  /* ZSWAP(k-1,k) */
  if (DEBUGLEVEL>3 && k==kmax)
  { /* output diagnostics associated to re-normalized rational quantities */
    pari_sp av1 = avma;
    GEN d = mulii(gel(B,k-1),gel(B,k+1));
    p1 = subii(mulsi(D-1, sqri(Bk)), mulsi(D, la2));
    fprintferr(" (%ld)", expi(p1) - expi(mulsi(D, d)));
    avma = av1;
  }
  lswap(x[k-1], x[k]); lx = lg(x);
  for (j=1; j<k-1; j++) lswap(coeff(L,k-1,j), coeff(L,k,j))
  if (fl[k])
  {
    av = avma;
    for (i=k+1; i<=kmax; i++)
    {
      GEN t = gcoeff(L,i,k);
      p1 = subii(mulii(gel(B,k+1),gcoeff(L,i,k-1)), mulii(la,t));
      p1 = diviiexact(p1, Bk);
      gcoeff(L,i,k) = icopy_av(p1,(GEN)av);
      av = avma = (pari_sp)coeff(L,i,k);

      p1 = addii(mulii(la,gcoeff(L,i,k-1)), mulii(gel(B,k-1),t));
      p1 = diviiexact(p1, Bk);
      gcoeff(L,i,k-1) = icopy_av(p1,(GEN)av);
      av = avma = (pari_sp)coeff(L,i,k-1);
    }
  }
  else if (signe(la))
  {
    p1 = diviiexact(la2, Bk);
    gel(B,k+1) = gel(B,k) = p1;
    for (i=k+2; i<=lx; i++) gel(B,i) = diviiexact(mulii(p1,gel(B,i)), Bk);
    for (i=k+1; i<=kmax; i++)
      gcoeff(L,i,k-1) = diviiexact(mulii(la,gcoeff(L,i,k-1)), Bk);
    for (j=k+1; j<kmax; j++)
      for (i=j+1; i<=kmax; i++)
	gcoeff(L,i,j) = diviiexact(mulii(p1,gcoeff(L,i,j)), Bk);
  }
  else
  {
    for (i=k+1; i<=kmax; i++)
    {
      gcoeff(L,i,k) = gcoeff(L,i,k-1);
      gcoeff(L,i,k-1) = gen_0;
    }
    B[k] = B[k-1]; fl[k] = 1; fl[k-1] = 0;
  }
  return 1;
}

static void
ZincrementalGS(GEN x, GEN L, GEN B, long k, GEN fl)
{
  GEN u = NULL; /* gcc -Wall */
  long i, j, s;
  for (j=1; j<=k; j++)
    if (j==k || fl[j])
    {
      pari_sp av = avma;
      u = ZV_dotproduct(gel(x,k), gel(x,j));
      for (i=1; i<j; i++)
	if (fl[i])
	{
	  u = subii(mulii(gel(B,i+1), u), mulii(gcoeff(L,k,i), gcoeff(L,j,i)));
	  u = diviiexact(u, gel(B,i));
	}
      gcoeff(L,k,j) = gerepileuptoint(av, u);
    }
  s = signe(u);
  if (s == 0) B[k+1] = B[k];
  else
  {
    if (s < 0) pari_err(talker, "not a definite matrix in lll");
    B[k+1] = coeff(L,k,k); gcoeff(L,k,k) = gen_1; fl[k] = 1;
  }
}
static GEN
GS_norms(GEN B, long prec)
{
  GEN N, b = itor(gel(B,1), prec);
  long k, lx = lg(B)-1;
  N = cgetg(lx, t_VEC);
  for (k=1; k<lx; k++)
  {
    GEN c = itor(gel(B,k+1), prec);
    gel(N,k) = divrr(c, b); b = c;
  }
  return N;
}

/* Assume x a ZM, set ptB to Gram-Schmidt (squared) norms */
GEN
lllint_knapsack_inplace(GEN x, long D, GEN *ptB)
{
  long lx = lg(x), j, k, l, n = lx-1, kmax;
  pari_sp av, lim;
  GEN B,L,fl;

  if (n <= 1)
  {
    *ptB = (n == 0)? cgetg(1, t_VEC): mkvec( gsqr(gcoeff(x,1,1)) );
    return lll_trivial(x, LLL_IM);
  }
  fl = cgetg(lx,t_VECSMALL);

  av = avma; lim = stack_lim(av,1); x = shallowcopy(x);
  B = scalarcol_shallow(gen_1, lx);
  L = cgetg(lx,t_MAT);
  for (j=1; j<lx; j++) { fl[j] = 0; gel(L,j) = zerocol(n); }
  ZincrementalGS(x, L, B, 1, fl);
  kmax = 1;
  if (DEBUGLEVEL>5) fprintferr("k = ");
  for (k=2;;)
  {
    if (k > kmax)
    {
      if (DEBUGLEVEL>3) fprintferr("K%ld ",k);
      ZincrementalGS(x, L, B, k, fl);
      kmax = k;
    }
    ZRED(k,k-1, x,L,gel(B,k),kmax);
    if (do_ZSWAP(x,L,B,kmax,k,D,fl))
    {
      if (k > 2) k--;
    }
    else
    {
      for (l=k-2; l; l--)
      {
        ZRED(k,l, x,L,gel(B,l+1),kmax);
        if (low_stack(lim, stack_lim(av,1)))
        {
          if(DEBUGMEM>1) pari_warn(warnmem,"lllint[1], kmax = %ld", kmax);
          gerepileall(av,3,&B,&L,&x);
        }
      }
      if (++k > n) break;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"lllint[2], kmax = %ld", kmax);
      gerepileall(av,3,&B,&L,&x);
    }
  }
  if (DEBUGLEVEL>3) fprintferr("\n");
  /* set B to { |b_i^*|^2 }_i, low accuracy */
  *ptB = GS_norms(B, DEFAULTPREC);
  return x;
}

/********************************************************************/
/**                                                                **/
/**                   INTEGRAL KERNEL (LLL REDUCED)                **/
/**                                                                **/
/********************************************************************/
GEN
matkerint0(GEN x, long flag)
{
  switch(flag)
  {
    case 0: return kerint(x);
    case 1: return kerint1(x);
    default: pari_err(flagerr,"matkerint");
  }
  return NULL; /* not reached */
}

GEN
kerint1(GEN x)
{
  pari_sp av = avma;
  return gerepilecopy(av, lllint_ip(matrixqz3(ker(x)), LLLDFT));
}

GEN
kerint(GEN x)
{
  pari_sp av = avma;
  GEN h = lllall_i(x, LLLDFT, LLL_KER);
  if (lg(h)==1) { avma = av; return cgetg(1, t_MAT); }
  return gerepilecopy(av, lllint_ip(h, LLLDFT));
}
