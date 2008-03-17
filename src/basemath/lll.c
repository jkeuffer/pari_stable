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

/* This file is a conversion to libpari API and data types 
   of the file proved.c in fplll-1.3
   by Damien Stehle'.

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

#include "pari.h"
#include "paripriv.h"

#define ETA "0.51"
#define DELTA "0.99"

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

void
Babai (int kappa, GEN G, GEN B, GEN U,
       GEN mu, GEN r, GEN s,
       int a, int zeros, int kappamax, int n,
       GEN eta, long prec)
{
  long i, j, k, test;
  long aa = (a > zeros)? a : zeros+1;
  GEN tmp, rtmp, ztmp;
  long loops=0;
  GEN onedothalfplus=addsr(1,eta);
  long d = lg(B)-1;

  do {
    test=0;
    loops++;
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
      tmp = mpabs(gmael(mu,kappa,j));
      if (cmprr(tmp, eta) > 0)
      {
        test = 1;
        /* we consider separately the case X = +-1 */
        if (cmprr(tmp, onedothalfplus) <= 0)
        {
          if ( signe(gmael(mu,kappa,j)) > 0 ) /* in this case, X is 1 */
          {
            for (k=zeros+1; k<j; k++)
              gmael(mu,kappa,k) = subrr(gmael(mu,kappa,k), gmael(mu,j,k));
            for (i=1; i<=n; i++)
              gmael(B,kappa,i) = subii(gmael(B,kappa,i), gmael(B,j,i));

            if (U)
              for (i=1; i<=d; i++)
                gmael(U,kappa,i) = subii(gmael(U,kappa,i), gmael(U,j,i));
            ztmp = shifti(gmael(G,kappa,j), 1);
            ztmp = subii(gmael(G,j,j), ztmp);
            gmael(G,kappa,kappa)=addii(gmael(G,kappa,kappa), ztmp);
            for (i=1; i<=j; i++)
              gmael(G,kappa,i) = subii(gmael(G,kappa,i), gmael(G,j,i));
            for (i=j+1; i<kappa; i++)
              gmael(G,kappa,i) = subii(gmael(G,kappa,i), gmael(G,i,j));
            for (i=kappa+1; i<=kappamax; i++)
              gmael(G,i,kappa) = subii(gmael(G,i,kappa), gmael(G,i,j));
          }
          else          /* otherwise X is -1 */
          {
            for (k=zeros+1; k<j; k++)
              gmael(mu,kappa,k)=addrr(gmael(mu,kappa,k), gmael(mu,j,k));
            for (i=1; i<=n; i++)
              gmael(B,kappa,i)=addii(gmael(B,kappa,i), gmael(B,j,i));

            if (U)
              for (i=1; i<=d; i++)
                gmael(U,kappa,i)=addii(gmael(U,kappa,i),gmael(U,j,i));
            ztmp = shifti(gmael(G,kappa,j), 1);
            ztmp = addii(gmael(G,j,j), ztmp);
            gmael(G,kappa,kappa)=addii(gmael(G,kappa,kappa), ztmp);
            for (i=1; i<=j; i++)
              gmael(G,kappa,i)=addii(gmael(G,kappa,i), gmael(G,j,i));
            for (i=j+1; i<kappa; i++)
              gmael(G,kappa,i)=addii(gmael(G,kappa,i), gmael(G,i,j));
            for (i=kappa+1; i<=kappamax; i++)
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

            for (i=1; i<=n; i++)
              gmael(B,kappa,i) = subii(gmael(B,kappa,i),
                                        mulis(gmael(B,j,i),xx));
            if (U)
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
            for (i=kappa+1; i<=kappamax; i++)
              gmael(G,i,kappa) = subii(gmael(G,i,kappa),
                                        mulis(gmael(G,i,j), xx));
          } else
          {
            long expo = gexpo(tmp)-bit_accuracy(lg(tmp));
            GEN X = shifti(gfloor2n(tmp, -expo), expo);
            for (i=1; i<=n; i++)
            {
              ztmp = mulii(X, gmael(B,j,i));
              gmael(B,kappa,i) = subii(gmael(B,kappa,i), ztmp);
            }

            if (U)
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

            for (i=kappa+1; i<=kappamax; i++)
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
}

static void
rotate(GEN mu,long kappa2, long kappa,long d)
{
  long i,j;
  GEN mutmp = shallowcopy(gel(mu,kappa2));
  for (i=kappa2; i>kappa; i--)
    for (j=1;j<=d;j++)
      gmael(mu,i,j) = gmael(mu,i-1,j);
  for (j=1;j<=d;j++)
    gmael(mu,kappa,j) = gel(mutmp,j);
}

/* ****************** */
/* The LLL Algorithm  */
/* ****************** */

/* LLL-reduces the integer matrix(ces) (G,B,U)? "in place" */

GEN
fplll (GEN G, GEN B, GEN U, GEN delta, GEN eta, long prec)
{
  pari_sp ltop=avma, av, av2;
  int kappa, kappa2, d, n=0, i, j, zeros, kappamax;
  GEN mu, r, s;
  GEN tmp;
  GEN SPtmp;
  GEN alpha;
  const long triangular=0;
  pari_timer T;
  int newkappa, loops, lovasz;

  d = lg(B)-1;
  n = lg(gel(B,1))-1;
  if(DEBUGLEVEL>=2)
  {
    TIMERstart(&T);
    fprintferr("Entering LLL^2: LLL-reduction factors(%Zs,%Zs)\n",delta,eta);
    fprintferr("Working precision set to %d words\n", prec);
  }

  alpha = cgetg(d+1, t_VECSMALL);

  mu = zeromatcopy(d,d);
  r  = zeromatcopy(d,d);
  s  = zerovec(d+1);
  SPtmp = zerovec(d+1);
  av = avma;

  /* ********************************* */
  /* Step2: Initializing the main loop */
  /* ********************************* */

  newkappa = 1;
  loops = lovasz = 0;
  kappamax = 1;
  i = 1;

  do {
    gmael(G,i,i) = ZV_dotsquare(gel(B,i));
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
      for (i=zeros+1; i<=kappa; i++)
        gmael(G,kappa,i) = ZV_dotproduct(gel(B,kappa), gel(B,i));
      kappamax++;
    }
    loops++;
    if (DEBUGLEVEL>=2)
    {
      if (kappa>newkappa)
      {
        newkappa++; 
        fprintferr("K%ld ",kappa);
      }
    }

    /* ********************************** */
    /* Step3: Call to the Babai algorithm */
    /* ********************************** */

    if (triangular)
    {
      if (kappamax + 0 <= n) 
        Babai (kappa, G, B, U, mu, r, s,
          alpha[kappa], zeros, kappamax, kappamax+0, eta, prec);
      else
        Babai (kappa, G, B, U, mu, r, s,
          alpha[kappa], zeros, kappamax, n, eta, prec);
    } else 
      Babai (kappa, G, B, U, mu, r, s,
        alpha[kappa], zeros, kappamax, n, eta, prec);

    if (loops%100==0)
    {
      if (U)
        gerepileall(av,6,&B,&G,&U,&mu,&r,&s);
      else
        gerepileall(av,5,&B,&G,&mu,&r,&s);
    }

    /* ************************************ */
    /* Step4: Success of Lovasz's condition */
    /* ************************************ */
    /* xtt * gmael(r,kappa-1,kappa-1) <= s[kappa-2] ?? */

    tmp = mulrr(gmael(r,kappa-1,kappa-1), delta);
    lovasz++;
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
        lovasz++;
        kappa--;
        if (kappa<zeros+2) break;
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

      rotate(B,kappa2,kappa,d);
      if (U) rotate(U,kappa2,kappa,d);

      for (i=1; i<=kappa2; i++)
        gel(SPtmp,i) = gmael(G,kappa2,i);
      for (i=kappa2+1; i<=kappamax; i++)
        gel(SPtmp,i) = gmael(G,i,kappa2);
      for (i=kappa2; i>kappa; i--)
      {
        for (j=1; j<kappa; j++)
          gmael(G,i,j) = gmael(G,i-1,j);
        gmael(G,i,kappa) = gel(SPtmp,i-1);
        for (j=kappa+1; j<=i; j++)
          gmael(G,i,j) = gmael(G,i-1,j-1);
        for (j=kappa2+1; j<=kappamax; j++)
          gmael(G,j,i) = gmael(G,j,i-1);
      }
      for (i=1; i<kappa; i++)
        gmael(G,kappa,i) = gel(SPtmp,i);
      gmael(G,kappa,kappa) = gel(SPtmp,kappa2);
      for (i=kappa2+1; i<=kappamax; i++)
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

  if (DEBUGLEVEL>=2)
    msgTIMER(&T,"LLL");
  if (U)
    return gerepilecopy(ltop,mkvec2(B,U));
  else
    return gerepilecopy(ltop,B);
}

/* determinant in a ring A: all computations are done within A
 * (Gauss-Bareiss algorithm) */
GEN
gminor(GEN a, long n)
{
  pari_sp av, lim;
  long nbco = n,i,j,k,s;
  GEN p,pprec;

  if (typ(a)!=t_MAT) pari_err(mattype1,"det");
  if (!nbco) return gen_1;
  if (DEBUGLEVEL > 7) (void)timer2();

  av = avma; lim = stack_lim(av,2);
  a = shallowcopy(a); s = 1;
  for (pprec=gen_1,i=1; i<nbco; i++,pprec=p)
  {
    GEN ci, ck, m, p1;
    int diveuc = (gcmp1(pprec)==0);

    p = gcoeff(a,i,i);
    if (gcmp0(p))
    {
      k=i+1; while (k<=nbco && gcmp0(gcoeff(a,i,k))) k++;
      if (k>nbco) return gerepilecopy(av, p);
      lswap(a[k], a[i]); s = -s;
      p = gcoeff(a,i,i);
    }
    ci = gel(a,i);
    for (k=i+1; k<=nbco; k++)
    {
      ck = gel(a,k); m = gel(ck,i);
      if (gcmp0(m))
      {
	if (gcmp1(p))
	{
	  if (diveuc)
	    gel(a,k) = gdiv(gel(a,k), pprec);
	}
	else
	  for (j=i+1; j<=nbco; j++)
	  {
	    p1 = gmul(p, gel(ck,j));
	    if (diveuc) p1 = gdiv(p1,pprec);
	    gel(ck,j) = p1;
	  }
      }
      else
      {
	m = gneg_i(m);
	for (j=i+1; j<=nbco; j++)
	{
	  p1 = gadd(gmul(p,gel(ck,j)), gmul(m,gel(ci,j)));
	  if (diveuc) p1 = gdiv(p1,pprec);
	  gel(ck,j) = p1;
	}
      }
      if (low_stack(lim,stack_lim(av,2)))
      {
	if(DEBUGMEM>1) pari_warn(warnmem,"det. col = %ld",i);
	gerepileall(av,2, &a,&pprec); p = gcoeff(a,i,i); ci = gel(a,i);
      }
    }
    if (DEBUGLEVEL > 7) msgtimer("det, col %ld / %ld",i,nbco-1);
  }
  p = gcoeff(a,nbco,nbco);
  if (s < 0) p = gneg(p); else p = gcopy(p);
  return gerepileupto(av, p);
}

GEN compute_B(GEN A)
{
  GEN B=cgetg(lg(A)+1,t_COL);
  long i;
  A = gmul(shallowtrans(A),A);
  for(i=0;i<lg(A);i++)
    gel(B,i+1) = gminor(A,i);
  return B;
}

GEN
LLL(GEN B, long flag)
{
  pari_sp av=avma;
  if (typ(B)!=t_MAT) pari_err(typeer,"LLL");
  long prec = DEFAULTPREC;
  long n = lg(B)-1;
  long d = lg(gel(B,1))-1;
  GEN G, U = NULL;
  GEN eta = strtor(ETA,prec);
  GEN delta  = strtor(DELTA,prec);
  double rho = rtodbl(gdiv(gsqr(addrs(eta,1)), gsub(delta,gsqr(eta))));
  long goodprec = (ulong) (7.0 + 0.2*d + d* log(rho)/ log(2.0)
      +  2.0 * log ( (double) d )
      - log( (rtodbl(eta)-0.5)*(1.0-rtodbl(delta)) ) / log(2));
  goodprec = nbits2prec(goodprec); 
  G = zeromatcopy(n,n);
  B = shallowcopy(B);
  if (flag) U = matid(n);
  B = fplll(G, B, U, strtor(DELTA,goodprec), strtor(ETA,goodprec), goodprec);
  if (flag)
    return gerepilecopy(av, B);
  else
    return gerepilecopy(av, mkvec2(B,compute_B(B)));
}
