/*
  Copyright 2005, 2006 Damien Stehle'.

  This program is free software; you can redistribute it and/or modify it
  under the terms of the GNU General Public License as published by the
  Free Software Foundation; either version 2 of the License, or (at your
  option) any later version.

  This program is distributed in the hope that it will be useful, but WITHOUT
  ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
  FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
  more details.

  You should have received a copy of the GNU General Public License along
  with this program; see the file COPYING.  If not, write to the Free
  Software Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
  02111-1307, USA.

  This program implements ideas from the paper "Floating-point LLL Revisited", 
  by Phong Nguyen and Damien Stehle', in the Proceedings of Eurocrypt'2005, 
  Springer-Verlag; and was partly inspired by Shoup's NTL library: 
  http://www.shoup.net/ntl/

*/

#include "pari.h"
#include "paripriv.h"

#define VERBOSE

#ifndef ETA
#define ETA "0.51"
#endif
#ifndef DELTA
#define DELTA "0.99"
#endif

GEN halfplus, onedothalfplus, ctt;

// #define TRIANGULAR
// #define WITH_TRANSFORM

#ifdef TRIANGULAR
#ifndef SHIFT 
#define SHIFT 0
#endif
#endif

static void
Print_matf (GEN B, int d, int n)
{
  int i, j;
  fprintferr("[");
  for (i=1;i<=d;i++)
    {
      fprintferr("[");
      for (j=1;j<=n;j++)
        {
          fprintferr("% .9Ze",gmael(B,i,j));
          if (j < n) fprintferr(" ");
        }
      fprintferr("]\n");
    }
  fprintferr("]\n");
}

static void
Print_mat (GEN B, int d, int n)
{
  int i, j;
  fprintferr("[");
  for (i=1;i<=d;i++)
    {
      fprintferr("[");
      for (j=1;j<=n;j++)
        {
          fprintferr("%Zd",gmael(B,i,j));
          if (j < n) fprintferr(" ");
        }
      fprintferr("]\n");
    }
  fprintferr("]\n");
}



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
       int a, int zeros, int kappamax, int n, long prec)
{
  long i, j, k, test, sg;
  long xx;
  long expo;
  GEN X;
  long aa = (a > zeros)? a : zeros+1;
  GEN tmp, rtmp, ztmp;
  long loops=0;
  if (DEBUGLEVEL>=4)
  {
    fprintferr("\nr: \n");
    Print_matf(r, kappamax, kappamax);
    fprintferr("\n          STARTING BABAI WITH k=%d\n", kappa);
    fprintferr("\nmu: \n");
    Print_matf(mu, kappamax, kappamax);
    fprintferr("a is %d, zeros is %d, aa is %d\n", a, zeros, aa);
    Print_mat(B, kappamax, n);
  }

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
        tmp  = gmul(gmael(mu,j,zeros+1), gmael(r,kappa,zeros+1));
        rtmp = itor(gmael(G,kappa,j), prec);
        rtmp = gsub(rtmp, tmp);
        for (k=zeros+2; k<j-1; k++)
        {
          tmp  = gmul(gmael(mu,j,k), gmael(r,kappa,k));
          rtmp = gsub(rtmp,tmp);
        }
        tmp = gmul(gmael(mu,j,j-1), gmael(r,kappa,j-1));
        gmael(r,kappa,j) = gsub(rtmp, tmp);
      }
      else if (j==zeros+2)
      {              
        tmp = gmul(gmael(mu,j,zeros+1), gmael(r,kappa,zeros+1));
        rtmp = itor(gmael(G,kappa,j), prec);
        gmael(r,kappa,j) = gsub(rtmp, tmp);
      }
      else
        gmael(r,kappa,j) = itor(gmael(G,kappa,j), prec);
      gmael(mu,kappa,j)  = gdiv(gmael(r,kappa,j), gmael(r,j,j));
    }
    if (DEBUGLEVEL>=4)
    {
      fprintferr("\nmu :\n");
      Print_matf(mu, kappa, kappa);
      fprintferr("\nr :\n");
      Print_matf(r, kappa, kappa);
    }

    /* **************************** */
    /* Step3--5: compute the X_j's  */
    /* **************************** */

    for (j=kappa-1; j>zeros; j--)
    {
      /* test of the relaxed size-reduction condition */
      tmp = mpabs(gmael(mu,kappa,j));
      if (DEBUGLEVEL>=4)
        fprintferr( "tmp is : %Zs\n",tmp);
      if (gcmp(tmp, halfplus) > 0) 
      {
        test = 1;
        /* we consider separately the case X = +-1 */     
        if (gcmp(tmp, onedothalfplus) <= 0)
        {
          sg = gsigne(gmael(mu,kappa,j));
          if ( sg >=0 )   /* in this case, X is 1 */
          {
            for (k=zeros+1; k<j; k++)
              gmael(mu,kappa,k) = gsub(gmael(mu,kappa,k),gmael(mu,j,k));
            for (i=1; i<=n; i++)    
              gmael(B,kappa,i) = subii(gmael(B,kappa,i), gmael(B,j,i));

#ifdef WITH_TRANSFORM
            for (i=1; i<=d; i++) 
              gmael(U,kappa,i) = subii(gmael(U,kappa,i), gmael(U,j,i));
#endif
            ztmp=muliu(gmael(G,kappa,j), 2);
            ztmp=subii(gmael(G,j,j), ztmp);
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
              gmael(mu,kappa,k)=gadd(gmael(mu,kappa,k), gmael(mu,j,k));
            for (i=1; i<=n; i++)    
              gmael(B,kappa,i)=addii(gmael(B,kappa,i), gmael(B,j,i));

#ifdef WITH_TRANSFORM
            for (i=1; i<=d; i++)    
              gmael(U,kappa,i)=addii(gmael(U,kappa,i),gmael(U,j,i));
#endif
            ztmp=muliu(gmael(G,kappa,j), 2);
            ztmp=addii(gmael(G,j,j), ztmp);
            gmael(G,kappa,kappa)=addii(gmael(G,kappa,kappa), ztmp);
            for (i=1; i<=j; i++)
              gmael(G,kappa,i)=addii(gmael(G,kappa,i), gmael(G,j,i));
            for (i=j+1; i<kappa; i++)
              gmael(G,kappa,i)=addii(gmael(G,kappa,i), gmael(G,i,j));
            for (i=kappa+1; i<=kappamax; i++)
              gmael(G,i,kappa)=addii(gmael(G,i,kappa), gmael(G,i,j));
          }
        }

        else   /* we must have |X| >= 2 */
        {        	
          rtmp = rtor(gmael(mu,kappa,j),prec);
          tmp=itor(ceil_safe(rtmp),prec);

          for (k=zeros+1; k<j; k++)
          {
            rtmp = gmul(tmp, gmael(mu,j,k));
            gmael(mu,kappa,k) = gsub(gmael(mu,kappa,k), rtmp);
          }
          if (0 && !is_bigint(tmp))
            /* X is stored in a long signed int */        	  
          {        	      
            xx = itos(tmp);
            if (DEBUGLEVEL>=4)
            {
              fprintferr("          xx[%d] is %ld\n", j, xx);
              fprintferr("          and tmp was %Zs\n",tmp);
            }

            for (i=1; i<=n; i++)  
              gmael(B,kappa,i) = subii(gmael(B,kappa,i),
                                        mulis(gmael(B,j,i),xx));
#ifdef WITH_TRANSFORM
            for (i=1; i<=d; i++)  
              gmael(U,kappa,i) = subii(gmael(U,kappa,i),
                                      mulis(gmael(U,j,i), xx));
#endif
            gmael(G,kappa,kappa) = subii(gmael(G,kappa,kappa),
                                          mulis(gmael(G,kappa,j), 2*xx));

            ztmp = mulis(gmael(G,j,j), xx);
            ztmp = mulis(ztmp, xx);
            gmael(G,kappa,kappa)=addii(gmael(G,kappa,kappa), ztmp);
            for (i=1; i<=j; i++)
              gmael(G,kappa,i) = subii(gmael(G,kappa,i),
                                        mulis(gmael(G,j,i), xx));
            for (i=j+1; i<kappa; i++)
              gmael(G,kappa,i) = subii(gmael(G,kappa,i),
                                        mulis(gmael(G,i,j), xx));
            for (i=kappa+1; i<=kappamax; i++)
              gmael(G,i,kappa) = subii(gmael(G,i,kappa), 
                                        mulis(gmael(G,i,j), xx));
          }

          else
          {
            expo = gexpo(tmp)-bit_accuracy(lg(tmp));
            X = gfloor2n(tmp,-expo);
            if (DEBUGLEVEL>=4)
            {
              fprintferr("tmp is %Zs\n",tmp);
              fprintferr("and expo is %d, and X is %Zs\n", (int) expo,X);
            }

            if (expo <= 0)
            {
              X = shifti(X,expo);
              expo = 0;
              for (i=1; i<=n; i++) 
              {
                ztmp = mulii(X, gmael(B,j,i));
                gmael(B,kappa,i) = subii(gmael(B,kappa,i), ztmp);
              }
#ifdef WITH_TRANSFORM
              for (i=1; i<=d; i++) 
              {
                ztmp = mulii(X, gmael(U,j,i));
                gmael(U,kappa,i) = subii(gmael(U,kappa,i), ztmp);
              }
#endif
              ztmp = mulii(gmael(G,kappa,j), X);
              ztmp = muliu(ztmp, 2);
              gmael(G,kappa,kappa) = subii(gmael(G,kappa,kappa), ztmp);
              ztmp = mulii(gmael(G,j,j), X);
              ztmp = mulii(ztmp, X);
              gmael(G,kappa,kappa) = addii(gmael(G,kappa,kappa), ztmp);
              for (i=1; i<=j; i++)
              {
                ztmp = mulii( X, gmael(G,j,i));
                gmael(G,kappa,i) = subii(gmael(G,kappa,i), ztmp);
              }
              for (i=j+1; i<kappa; i++)
              {
                ztmp = mulii( X, gmael(G,i,j));
                gmael(G,kappa,i) = subii(gmael(G,kappa,i), ztmp);
              } 
              for (i=kappa+1; i<=kappamax; i++)
              {
                ztmp = mulii( X, gmael(G,i,j));
                gmael(G,i,kappa) = subii(gmael(G,i,kappa), ztmp);
              }
            }
            else
            {
              for (i=1; i<=n; i++)  
              {
                ztmp = mulii( X, gmael(B,j,i));
                ztmp = shifti( ztmp, expo); 
                gmael(B,kappa,i) = subii( 
                    gmael(B,kappa,i), ztmp);
              }

#ifdef WITH_TRANSFORM
              for (i=1; i<=d; i++)  
              {
                ztmp = mulii( X, gmael(U,j,i));
                ztmp = shifti( ztmp, expo); 
                gmael(U,kappa,i) = subii( 
                    gmael(U,kappa,i), ztmp);
              }
#endif

              ztmp = mulii( gmael(G,kappa,j), X);
              ztmp = shifti( ztmp, expo+1);
              gmael(G,kappa,kappa) = subii( 
                  gmael(G,kappa,kappa), ztmp);
              ztmp = mulii( gmael(G,j,j), X);
              ztmp = mulii( ztmp,  X);
              ztmp = shifti( ztmp, 2*expo);
              gmael(G,kappa,kappa) = addii( 
                  gmael(G,kappa,kappa), ztmp);

              for (i=1; i<=j; i++)
              {
                ztmp = mulii( X, gmael(G,j,i));
                ztmp = shifti( ztmp, expo);
                gmael(G,kappa,i) = subii(gmael(G,kappa,i), ztmp);
              }

              for (i=j+1; i<kappa; i++)
              {
                ztmp = mulii( X, gmael(G,i,j));
                ztmp = shifti( ztmp, expo);
                gmael(G,kappa,i) = subii(gmael(G,kappa,i), ztmp);
              } 

              for (i=kappa+1; i<=kappamax; i++)
              {
                ztmp = mulii( X, gmael(G,i,j));
                ztmp = shifti( ztmp, expo);
                gmael(G,i,kappa) = subii(gmael(G,i,kappa), ztmp);
              }
            }
          }
        }
      }
    }
    /* Anything happened? */
    if (test) aa = zeros+1;
    if (DEBUGLEVEL>=4)
    {
      fprintferr("          test is %d\n", test);
      fprintferr("\nmu: \n");
      Print_matf (mu, kappa, kappa);
      fprintferr("\nr: \n");
      Print_matf (r, kappa, kappa);
    }
  } while (test);

  gel(s,zeros) = itor(gmael(G,kappa,kappa), prec);
  /* the last s[kappa-1]=r[kappa][kappa] is computed only if kappa increases */
  for (k=zeros+1; k<=kappa-2; k++)
  {
    tmp = gmul(gmael(mu,kappa,k), gmael(r,kappa,k));
    gel(s,k) = gsub(gel(s,k-1), tmp);
  }
  if (DEBUGLEVEL>=4)
  {
    fprintferr("          Number of loops is %d\n", loops);
    Print_mat (G, kappamax, kappamax);
  }
}

/* ****************** */
/* The LLL Algorithm  */
/* ****************** */

/* LLL-reduces the integer matrix(ces) (G,B,U)? "in place" */

void 
fplll (GEN G, GEN B, GEN U, long prec)
{
  int kappa, kappa2, d, n=0, i, j, zeros, kappamax;
  GEN mu, r;
  GEN s, mutmp;
  GEN tmp;
  GEN SPtmp;
  GEN alpha;
  GEN Btmp;

  int newkappa, loops, lovasz;

  d = lg(B)-1;
  n = lg(gel(B,1))-1;
  if(DEBUGLEVEL>=4)
   fprintferr ("d = %d, n=%d\n", d, n);
  if(DEBUGLEVEL>=2)
  {
    fprintferr("Entering LLL^2: LLL-reduction factors(%Zs,%Zs)\n",ctt,halfplus);
    fprintferr("Working precision set to %d words\n", prec);
  }

  alpha = cgetg(d+1, t_VECSMALL);

  mu = zeromatcopy(d,d);
  r  = zeromatcopy(d,d);
  s  = zerovec(d+2)+1;
  SPtmp = zerovec(d+1);

  if (DEBUGLEVEL>=4)
  {
    Print_mat (B, d, n);
    fprintferr("Step 1 is over\n");
  }

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
  } while ((signe(gmael(G,i,i)) == 0)&&(++i <=d));
  zeros = i-1; /* all vectors B[i] with i <= zeros are zero vectors */
  kappa = i+1;
  if (zeros < d)
    gmael(r,zeros+1,zeros+1) = itor(gmael(G,zeros+1,zeros+1), prec);
  for (i=zeros+1; i<=d; i++)
    alpha[i]=1;
  if (DEBUGLEVEL>=4)
  {
    fprintferr("Step 2 is over\n");
    fprintferr("kappa is %d and d is %d\n", kappa, d);
  }
  
  while (kappa <= d)
  {
    if (kappa>kappamax)
    {
      for (i=zeros+1; i<=kappa; i++)
        gmael(G,kappa,i) = ZV_dotproduct(gel(B,kappa), gel(B,i));
      kappamax++; 
    }
    if (DEBUGLEVEL>=2)
    {
      loops++;
      if (kappa>newkappa)
      {
        newkappa++;
        fprintferr("Discovering vector k = %d, iterations = %d\n", 
            kappa, loops);
      }
    }
    if (DEBUGLEVEL>=4)
    {
      fprintferr("alpha= ");
      for (i=zeros+1; i<=d; i++)
        fprintferr("%d ",alpha[i]);
      fprintferr("\n");
      fprintferr("entering the while loop with k=%d\n", kappa);
      Print_mat (B, d, n);
    }

      /* ********************************** */
      /* Step3: Call to the Babai algorithm */
      /* ********************************** */   

#ifdef TRIANGULAR 
      if (kappamax + SHIFT <= n){        
        Babai (kappa, G, B, U, mu, r, s,  
               alpha[kappa], zeros, kappamax, kappamax+SHIFT, prec);
      }
      else {
        Babai (kappa, G, B, U, mu, r, s,  
               alpha[kappa], zeros, kappamax, n, prec);
      }
#else
      Babai (kappa, G, B, U, mu, r, s, 
             alpha[kappa], zeros, kappamax, n, prec); 
#endif

      if(DEBUGLEVEL>=4)
      {
        fprintferr("Step 3 is over\n");
        Print_mat(B, kappamax, n);
        Print_matf(r, kappamax, kappamax);
      }

      /* ************************************ */
      /* Step4: Success of Lovasz's condition */
      /* ************************************ */  
      /* xtt * gmael(r,kappa-1,kappa-1) <= s[kappa-2] ?? */
      
      tmp = gmul(gmael(r,kappa-1,kappa-1), ctt);
      if (DEBUGLEVEL>=4)
        fprintferr("s[%ld] is %Zs\n %Zs\n", kappa-2, gel(s,kappa-2),
                                            gmael(r,kappa-1,kappa-1));
      lovasz++;
      if (gcmp(tmp, gel(s,kappa-2)) <=0 )
      {
        alpha[kappa] = kappa;
        tmp = gmul(gmael(mu,kappa,kappa-1), gmael(r,kappa,kappa-1));
        gmael(r,kappa,kappa) = gsub(gel(s,kappa-2), tmp);
        kappa++;
      } 
      else
      {
        /* ******************************************* */
        /* Step5: Find the right insertion index kappa */
        /* kappa2 remains the initial kappa            */
        /* ******************************************* */  
        kappa2 = kappa;
        do {
          lovasz++;
          kappa--;
          if (kappa<zeros+2) break;
          tmp = gmul(gmael(r,kappa-1,kappa-1), ctt);
        } while (gcmp(gel(s,kappa-2), tmp) <=0 );

        if (DEBUGLEVEL>=4)
        {
          fprintferr( "Index of insertion: %d \n", kappa);
          fprintferr("Step 5 is over\n");
          fprintferr("alpha= ");
          for (i=1; i<=kappamax; i++)
            fprintferr("%d ", alpha[i]);
          fprintferr("\n");
        }

        for (i=kappa; i<kappa2; i++)
          if (kappa <= alpha[i]) alpha[i] = kappa;

        for (i=kappa2; i>kappa; i--)
          alpha[i] = alpha[i-1];

        for (i=kappa2+1; i<=kappamax; i++)
          if (kappa < alpha[i]) alpha[i] = kappa;
        alpha[kappa] = kappa;

        if (DEBUGLEVEL>=4)
        {
          fprintferr("alpha= ");
          for (i=1; i<=d; i++)
            fprintferr("%d ", alpha[i]);
          fprintferr("\n");
        }

        /* ****************************** */
        /* Step6: Update the mu's and r's */
        /* ****************************** */  

        mutmp = shallowcopy(gel(mu,kappa2));
        for (i=kappa2; i>kappa; i--)
          for (j=1;j<=d;j++)
            gmael(mu,i,j) = gmael(mu,i-1,j);
        for (j=1;j<=d;j++)
          gmael(mu,kappa,j) = gel(mutmp,j);

        mutmp = shallowcopy(gel(r,kappa2));
        for (i=kappa2; i>kappa; i--)
          for (j=1;j<=d;j++)
            gmael(r,i,j) = gmael(r,i-1,j);
        for (j=1;j<=d;j++)
          gmael(r,kappa,j) = gel(mutmp,j);

        gmael(r,kappa,kappa) = gel(s,kappa-1);

        if (DEBUGLEVEL>=4)
          fprintferr("Step 6 is over\n");

        /* ********************* */
        /* Step7: Update B, G, U */
        /* ********************* */  	  

        Btmp = shallowcopy(gel(B, kappa2));
        for (i=kappa2; i>kappa; i--)
          for(j=1; j<=n; j++)
            gmael(B,i,j) = gmael(B,i-1,j);
        for(j=1; j<=n; j++)
          gmael(B,kappa,j) = gel(Btmp,j);

#ifdef WITH_TRANSFORM
          Btmp = shallowcopy(gel(U,kappa2));
          for (i=kappa2; i>kappa; i--)
            for(j=1; j<=n; j++)
              gmael(U,i,j) = gmael(U,i-1,j);
          for(j=1; j<=n; j++)
            gmael(U,kappa,j) = gel(Btmp, j);
#endif
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
          if (DEBUGLEVEL>=4)
          {
            Print_mat (B, kappamax, n);
            Print_mat (G, kappamax, kappamax);
            fprintferr("Step 7 is over\n");
          } 

          /* ************************************** */
          /* Step8: Prepare the next loop iteration */
          /* ************************************** */  	  

          if ( (kappa==zeros+1) && (signe(gmael(G,kappa,kappa))==0) )
          {
            zeros++;
            kappa++;
            gmael(r,kappa,kappa) = gmael(G,kappa,kappa);
          }
          kappa++;
          if (DEBUGLEVEL>=4)
          { 
            Print_mat (B, kappamax, n);
            Print_mat (G, kappamax, kappamax);
            fprintferr("Step 8 is over, new kappa=%d\n",kappa);
          }
        }
    }

  if (DEBUGLEVEL>=2)
  {
    tmp= gen_1;
    for (i = zeros+1; i<=d; i++)
      tmp = gmul( tmp, gmael(r,i,i));
    tmp= gsqrt(tmp,prec);
    fprintferr( "\nLoop iterations = %d \n", loops);
    fprintferr( "Lovasz tests = %d \n", lovasz);
    if (zeros < d)
    {
      fprintferr("Vol(L) is %Zs\n", tmp);
      tmp = gsqrt(gmael(r,zeros+1,zeros+1),prec);
      fprintferr("||b_1|| is %Zs \n", tmp); 
    }
  }
}

GEN
LLL(GEN B, long prec)
{
  pari_sp av=avma;
  long n = lg(B)-1;
  long d = lg(gel(B,1))-1;
  GEN G = zeromatcopy(d,n);
  GEN U = zeromatcopy(d,n);
  B = gcopy(B);
  halfplus=strtor(ETA,prec) ;
  onedothalfplus=addsr(1,halfplus);
  ctt=strtor(DELTA,prec);
  fplll(G,B,U,prec);
  return gerepileupto(av, B);
}
