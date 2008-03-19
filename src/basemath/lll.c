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

/* Reference for the algorithm:
Floating-Point LLL Revisited, by Phong Nguyen and Damien Stehle
Proceedings of Eurocrypt 2005.
*/

/************************************/
/* ******************************** */
/* Babai's Nearest Plane algorithm  */
/* ******************************** */
/************************************/

/* Size-reduces b_kappa using mu_ij and r_ij for j<=i <kappa
updates B (kappa)
computes mu_kappaj, r_kappaj for j<=kappa, and s(kappa)
The algorithm is the iterative Babai algorithm of the paper
*/

static void
Babai (long kappa, GEN *ptrG, GEN *ptrB, GEN *ptrU,
       GEN *ptrmu, GEN *ptrr, GEN *ptrs,
       long a, long zeros, long kappamax, long n,
       GEN eta, long flag, long prec)
{
  const int gram = flag & LLL_GRAM; /*Gram matrix*/
  pari_sp av, lim;
  GEN G=*ptrG, B=*ptrB, U=*ptrU, mu=*ptrmu, r=*ptrr, s=*ptrs;
  long i, j, k, test;
  long aa = (a > zeros)? a : zeros+1;
  GEN tmp, rtmp, ztmp, onedothalfplus=addsr(1,eta);
  long d = U ? lg(U)-1: 0, maxG = gram? lg(G)-1: kappamax;
  av = avma; lim = stack_lim(av, 1);
  do {
    test=0;
    if (low_stack(lim, stack_lim(av,1)))
      gerepileall(av,U?6:5,&B,&G,&mu,&r,&s,&U);
    /* ************************************** */
    /* Step2: compute the GSO for stage kappa */
    /* ************************************** */

    for (j=aa; j<kappa; j++)
    {
      if (j > zeros+2)
      {
        pari_sp btop=avma;
        rtmp = itor(gmael(G,kappa,j), prec);
        for (k=zeros+1; k<=j-1; k++)
        {
          tmp  = mulrr(gmael(mu,j,k), gmael(r,kappa,k));
          rtmp = subrr(rtmp,tmp);
        }
        gmael(r,kappa,j) = gerepileupto(btop, rtmp);
      }
      else if (j==zeros+2)
      {
        pari_sp btop=avma;
        tmp = mulrr(gmael(mu,j,zeros+1), gmael(r,kappa,zeros+1));
        rtmp = itor(gmael(G,kappa,j), prec);
        gmael(r,kappa,j) = gerepileupto(btop, subrr(rtmp, tmp));
      }
      else
        gmael(r,kappa,j) = itor(gmael(G,kappa,j), prec);
      gmael(mu,kappa,j)  = divrr(gmael(r,kappa,j), gmael(r,j,j));
    }

    /* **************************** */
    /* Step3--5: compute the X_j's  */
    /* **************************** */

    for (j=kappa-1; j>zeros; j--)
    {
      /* test of the relaxed size-reduction condition */
      tmp = gmael(mu,kappa,j);
      if (absr_cmp(tmp, eta) > 0)
      {
        test = 1;
        /* we consider separately the case X = +-1 */
        if (absr_cmp(tmp, onedothalfplus) <= 0)
        {
          if ( signe(gmael(mu,kappa,j)) > 0 ) /* in this case, X is 1 */
          {
            for (k=zeros+1; k<j; k++)
              gmael(mu,kappa,k) = subrr(gmael(mu,kappa,k), gmael(mu,j,k));
            if (!gram)
              for (i=1; i<=n; i++)
                gmael(B,kappa,i) = subii(gmael(B,kappa,i), gmael(B,j,i));

            for (i=1; i<=d; i++)
              gmael(U,kappa,i) = subii(gmael(U,kappa,i), gmael(U,j,i));
            ztmp = shifti(gmael(G,kappa,j), 1);
            ztmp = subii(gmael(G,j,j), ztmp);
            gmael(G,kappa,kappa)=addii(gmael(G,kappa,kappa), ztmp);
            for (i=1; i<=j; i++)
              gmael(G,kappa,i) = subii(gmael(G,kappa,i), gmael(G,j,i));
            for (i=j+1; i<kappa; i++)
              gmael(G,kappa,i) = subii(gmael(G,kappa,i), gmael(G,i,j));
            for (i=kappa+1; i<=maxG; i++)
              gmael(G,i,kappa) = subii(gmael(G,i,kappa), gmael(G,i,j));
          }
          else          /* otherwise X is -1 */
          {
            for (k=zeros+1; k<j; k++)
              gmael(mu,kappa,k)=addrr(gmael(mu,kappa,k), gmael(mu,j,k));
            if (!gram)
              for (i=1; i<=n; i++)
                gmael(B,kappa,i)=addii(gmael(B,kappa,i), gmael(B,j,i));

            for (i=1; i<=d; i++)
              gmael(U,kappa,i)=addii(gmael(U,kappa,i),gmael(U,j,i));
            ztmp = shifti(gmael(G,kappa,j), 1);
            ztmp = addii(gmael(G,j,j), ztmp);
            gmael(G,kappa,kappa)=addii(gmael(G,kappa,kappa), ztmp);
            for (i=1; i<=j; i++)
              gmael(G,kappa,i)=addii(gmael(G,kappa,i), gmael(G,j,i));
            for (i=j+1; i<kappa; i++)
              gmael(G,kappa,i)=addii(gmael(G,kappa,i), gmael(G,i,j));
            for (i=kappa+1; i<=maxG; i++)
              gmael(G,i,kappa)=addii(gmael(G,i,kappa), gmael(G,i,j));
          }
        } else   /* we must have |X| >= 2 */
        {        	
          rtmp = rtor(gmael(mu,kappa,j),prec);
          ztmp = ceil_safe(rtmp);
          tmp  = itor(ztmp,prec);

          for (k=zeros+1; k<j; k++)
          {
            rtmp = mulrr(tmp, gmael(mu,j,k));
            gmael(mu,kappa,k) = subrr(gmael(mu,kappa,k), rtmp);
          }
          if (!is_bigint(ztmp))
            /* X is stored in a long signed int */
          {
            long xx = itos(ztmp);

            if (!gram)
              for (i=1; i<=n; i++)
                gmael(B,kappa,i) = subii(gmael(B,kappa,i),
                                          mulis(gmael(B,j,i),xx));
            for (i=1; i<=d; i++)
              gmael(U,kappa,i) = subii(gmael(U,kappa,i),
                                       mulis(gmael(U,j,i), xx));
            ztmp = shifti(mulis(gmael(G,kappa,j), xx), 1);
            ztmp = subii(mulii(gmael(G,j,j), sqrs(xx)), ztmp);
            gmael(G,kappa,kappa) = addii(gmael(G,kappa,kappa), ztmp);
            for (i=1; i<=j; i++)
              gmael(G,kappa,i) = subii(gmael(G,kappa,i),
                                        mulis(gmael(G,j,i), xx));
            for (i=j+1; i<kappa; i++)
              gmael(G,kappa,i) = subii(gmael(G,kappa,i),
                                        mulis(gmael(G,i,j), xx));
            for (i=kappa+1; i<=maxG; i++)
              gmael(G,i,kappa) = subii(gmael(G,i,kappa),
                                        mulis(gmael(G,i,j), xx));
          } else
          {
            long expo = gexpo(tmp)-bit_accuracy(lg(tmp));
            GEN X = shifti(gfloor2n(tmp, -expo), expo);
            if (!gram)
              for (i=1; i<=n; i++)
              {
                ztmp = mulii(X, gmael(B,j,i));
                gmael(B,kappa,i) = subii(gmael(B,kappa,i), ztmp);
              }

            for (i=1; i<=d; i++)
            {
              ztmp = mulii(X, gmael(U,j,i));
              gmael(U,kappa,i) = subii(gmael(U,kappa,i), ztmp);
            }

            ztmp = shifti(mulii(gmael(G,kappa,j), X), 1);
            ztmp = subii(mulii(gmael(G,j,j), sqri(X)), ztmp);
            gmael(G,kappa,kappa) = addii(gmael(G,kappa,kappa), ztmp);

            for (i=1; i<=j; i++)
            {
              ztmp = mulii(X, gmael(G,j,i));
              gmael(G,kappa,i) = subii(gmael(G,kappa,i), ztmp);
            }

            for (i=j+1; i<kappa; i++)
            {
              ztmp = mulii(X, gmael(G,i,j));
              gmael(G,kappa,i) = subii(gmael(G,kappa,i), ztmp);
            }

            for (i=kappa+1; i<=maxG; i++)
            {
              ztmp = mulii(X, gmael(G,i,j));
              gmael(G,i,kappa) = subii(gmael(G,i,kappa), ztmp);
            }
          }
        }
      }
    }
    /* Anything happened? */
    if (test) aa = zeros+1;
  } while (test);

  gel(s,zeros+1) = itor(gmael(G,kappa,kappa), prec);
  /* the last s[kappa-1]=r[kappa][kappa] is computed only if kappa increases */
  for (k=zeros+1; k<=kappa-2; k++)
  {
    tmp = mulrr(gmael(mu,kappa,k), gmael(r,kappa,k));
    gel(s,k+1) = subrr(gel(s,k), tmp);
  }
  *ptrG=G; *ptrB=B; *ptrU=U;
  *ptrmu=mu; *ptrr=r; *ptrs=s;
}

static void
rotate(GEN mu,long kappa2, long kappa,long d)
{
  long i,j;
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
fplll(GEN B, GEN *ptrr, GEN delta, GEN eta, long flag, long prec)
{
  const long inplace = flag & LLL_INPLACE;
  const long gram = flag & LLL_GRAM; /*Gram matrix*/
  const long keepfirst = flag & LLL_KEEP_FIRST; /*never swap with first vector*/
  pari_sp av, av2, lim;
  long kappa, kappa2, d, n, i, j, zeros, kappamax, maxG, newkappa;
  GEN U, G, mu, r, s, tmp, SPtmp, alpha;
  const long triangular = 0;
  pari_timer T;

  B = shallowcopy(B);
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
  U = inplace? NULL: matid(d);

  if(DEBUGLEVEL>=4)
  {
    TIMERstart(&T);
    fprintferr("Entering L^2: LLL-parameters (%Z.2f,%.2Zf), working precision %d words\n",delta,eta, prec);
  }

  alpha = cgetg(d+1, t_VECSMALL);

  mu = zeromatcopy(d,d);
  r  = zeromatcopy(d,d);
  s  = zerovec(d+1);
  SPtmp = zerovec(d+1);
  av = avma; lim = stack_lim(av, 1);

  /* ********************************* */
  /* Step2: Initializing the main loop */
  /* ********************************* */

  newkappa = 1;
  kappamax = 1;
  i = 1;

  do {
    if (!gram) gmael(G,i,i) = ZV_dotsquare(gel(B,i));
    gmael(r,i,i) = itor(gmael(G,i,i), prec);
  } while (signe(gmael(G,i,i)) == 0 && (++i <=d));
  zeros = i-1; /* all vectors B[i] with i <= zeros are zero vectors */
  kappa = i+1;
  if (zeros < d)
    gmael(r,zeros+1,zeros+1) = itor(gmael(G,zeros+1,zeros+1), prec);
  for (i=zeros+1; i<=d; i++)
    alpha[i]=1;

  while (kappa <= d)
  {
    if (kappa>kappamax)
    {
      if (!gram)
        for (i=zeros+1; i<=kappa; i++)
          gmael(G,kappa,i) = ZV_dotproduct(gel(B,kappa), gel(B,i));
      kappamax++;
    }
    if (DEBUGLEVEL>=6)
    {
      if (kappa>newkappa)
      {
        newkappa++; 
        fprintferr("K%ld ",kappa);
      }
    }

    if (low_stack(lim, stack_lim(av,1)))
        gerepileall(av,U?6:5,&B,&G,&mu,&r,&s,&U);

    /* ********************************** */
    /* Step3: Call to the Babai algorithm */
    /* ********************************** */
    Babai (kappa, &G, &B, &U, &mu, &r, &s, alpha[kappa], zeros, kappamax,
      (triangular && kappamax <= n) ? kappamax: n, eta, flag, prec);

    /* ************************************ */
    /* Step4: Success of Lovasz's condition */
    /* ************************************ */
    tmp = mulrr(gmael(r,kappa-1,kappa-1), delta);
    if (cmprr(tmp, gel(s,kappa-1)) <=0 )
    {
      alpha[kappa] = kappa;
      tmp = mulrr(gmael(mu,kappa,kappa-1), gmael(r,kappa,kappa-1));
      gmael(r,kappa,kappa) = subrr(gel(s,kappa-1), tmp);
      kappa++;
    }
    else
    {
      /* ******************************************* */
      /* Step5: Find the right insertion index kappa */
      /* kappa2 remains the initial kappa            */
      /* ******************************************* */
      kappa2 = kappa;
      av2 = avma;
      do {
        kappa--;
        if (kappa<zeros+2 + (keepfirst ? 1: 0)) break;
        tmp = mulrr(gmael(r,kappa-1,kappa-1), delta);
      } while (cmprr(gel(s,kappa-1), tmp) <=0 );
      avma = av2;

      for (i=kappa; i<kappa2; i++)
        if (kappa <= alpha[i]) alpha[i] = kappa;

      for (i=kappa2; i>kappa; i--)
        alpha[i] = alpha[i-1];

      for (i=kappa2+1; i<=kappamax; i++)
        if (kappa < alpha[i]) alpha[i] = kappa;
      alpha[kappa] = kappa;

      /* ****************************** */
      /* Step6: Update the mu's and r's */
      /* ****************************** */

      rotate(mu,kappa2,kappa,d);
      rotate(r,kappa2,kappa,d);

      gmael(r,kappa,kappa) = gel(s,kappa);

      /* ********************* */
      /* Step7: Update B, G, U */
      /* ********************* */

      if (!gram) rotate(B,kappa2,kappa,n);
      if (U) rotate(U,kappa2,kappa,d);

      maxG = gram ? n: kappamax;
      for (i=1; i<=kappa2; i++)
        gel(SPtmp,i) = gmael(G,kappa2,i);
      for (i=kappa2+1; i<=maxG; i++)
        gel(SPtmp,i) = gmael(G,i,kappa2);
      for (i=kappa2; i>kappa; i--)
      {
        for (j=1; j<kappa; j++)
          gmael(G,i,j) = gmael(G,i-1,j);
        gmael(G,i,kappa) = gel(SPtmp,i-1);
        for (j=kappa+1; j<=i; j++)
          gmael(G,i,j) = gmael(G,i-1,j-1);
        for (j=kappa2+1; j<=maxG; j++)
          gmael(G,j,i) = gmael(G,j,i-1);
      }
      for (i=1; i<kappa; i++)
        gmael(G,kappa,i) = gel(SPtmp,i);
      gmael(G,kappa,kappa) = gel(SPtmp,kappa2);
      for (i=kappa2+1; i<=maxG; i++)
        gmael(G,i,kappa) = gel(SPtmp,i);

      /* ************************************** */
      /* Step8: Prepare the next loop iteration */
      /* ************************************** */

      if ( kappa==zeros+1 && signe(gmael(G,kappa,kappa))==0 )
      {
        zeros++;
        kappa++;
        gmael(r,kappa,kappa) = itor(gmael(G,kappa,kappa),prec);
      }
      kappa++;
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
      +  2.0 * log ( (double) d )
      - log2( (eta-0.5)*(1.0-delta) ));
  return nbits2prec(goodprec); 
}

/* Assume x a ZM, if ptB != NULL, set it to Gram-Schmidt (squared) norms */
GEN
LLLint(GEN x, long D, long flag, GEN *B)
{
  const double ETA = 0.51, DELTA = (D-1) / (double)D;
  long prec, d, n = lg(x)-1;

  if (n <= 1) return lll_trivial(x, flag);
  d = lg(gel(x,1))-1;
  prec = good_prec(d,DELTA,ETA); 
  return fplll(x, B, dbltor(DELTA), dbltor(ETA), flag, prec);
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
  long e, prec = gprecision(x);
  GEN y;
  if (!prec) return Q_primpart(x);

  y = gmul2n(x, bit_accuracy(prec) - gexpo(x));
  return gcvtoi(y, &e);
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

static GEN
lllfp_wrap(GEN x, long D, long flag)
{
  GEN h = lllfp(x,D,flag);
  if (typ(h) == t_VEC) pari_err(talker, "not a definite matrix in lllgram");
  return h;
}
GEN
lllgram(GEN x) { return lllfp_wrap(x,LLLDFT,LLL_GRAM); }
GEN
lll(GEN x) { return lllfp_wrap(x,LLLDFT,0); }

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
