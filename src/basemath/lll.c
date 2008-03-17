/*
  Copyright 2005, 2006 Damien Stehlé.

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
  by Phong Nguyen and Damien Stehlé, in the Proceedings of Eurocrypt'2005, 
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

// #define VERBOSE
// #define TRIANGULAR
// #define WITH_TRANSFORM

#ifdef TRIANGULAR
#ifndef SHIFT 
#define SHIFT 0
#endif
#endif

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
  if (DEBUGLEVEL)
  {
    fprintferr("\nr: \n%Zs\n",r);
    fprintferr("\n          STARTING BABAI WITH k=%d\n", kappa);
    fprintferr("\nmu: \n%Zs\n",mu);
    fprintferr("a is %d, zeros is %d, aa is %d\n", a, zeros, aa);
    fprintferr("%Zs\n",B);
  }

  do
  {
    test=0;

    /* ************************************** */
    /* Step2: compute the GSO for stage kappa */
    /* ************************************** */

    for (j=aa; j<kappa; j++)
    {
      if (j > zeros+2)
      {
        tmp  = gmul(gcoeff(mu,j,zeros+1), gcoeff(r,kappa,zeros+1));
        rtmp = gsub(itor(gcoeff(G,kappa,j),prec), tmp);
        for (k=zeros+2; k<j-1; k++)
        {
          tmp  = gmul(gcoeff(mu,j,k), gcoeff(r,kappa,k));
          rtmp = gsub(rtmp,tmp);
        }
        tmp = gmul(gcoeff(mu,j,j-1), gcoeff(r,kappa,j-1));
        gcoeff(r,kappa,j) = gsub(rtmp, tmp);
      }
      else if (j==zeros+2)
      {              
        tmp = gmul(gcoeff(mu,j,zeros+1), gcoeff(r,kappa,zeros+1));
        rtmp = itor(gcoeff(G,kappa,j), prec);
        gcoeff(r,kappa,j) = gsub(rtmp, tmp);
      }
      else
        gcoeff(r,kappa,j) = itor(gcoeff(G,kappa,j), prec);
      gcoeff(mu,kappa,j)= gdiv(gcoeff(r,kappa,j), gcoeff(r,j,j));
    }
    if (DEBUGLEVEL>=4)
    {
      fprintferr("\nmu:\n %Zs\n", mu);
      fprintferr("\nr :\n %Zs\n", r);
    }

    /* **************************** */
    /* Step3--5: compute the X_j's  */
    /* **************************** */

    for (j=kappa-1; j>zeros; j--)
    {
      /* test of the relaxed size-reduction condition */
      tmp = mpabs(gcoeff(mu,kappa,j));
      if (gcmp(tmp, halfplus) > 0) 
      {
        test = 1;
        /* we consider separately the case X = +-1 */     
        if (gcmp(tmp, onedothalfplus) <= 0)
        {
          sg = gsigne(gcoeff(mu,kappa,j));
          if ( sg >=0 )   /* in this case, X is 1 */
          {
            for (k=zeros+1; k<j; k++)
              gcoeff(mu,kappa,k) = gsub(gcoeff(mu,kappa,k),gcoeff(mu,j,k));
            for (i=1; i<=n; i++)    
              gcoeff(B,kappa,i) = subii(gcoeff(B,kappa,i), gcoeff(B,j,i));

#ifdef WITH_TRANSFORM
            for (i=1; i<=d; i++) 
              gcoeff(U,kappa,i) = subii(gcoeff(U,kappa,i), gcoeff(U,j,i));
#endif
            ztmp=muliu(gcoeff(G,kappa,j), 2);
            ztmp=subii(gcoeff(G,j,j), ztmp);
            gcoeff(G,kappa,kappa)=addii(gcoeff(G,kappa,kappa), ztmp);
            for (i=1; i<=j; i++)
              gcoeff(G,kappa,i)=subii(gcoeff(G,kappa,i), gcoeff(G,j,i)); 
            for (i=j+1; i<kappa; i++)
              gcoeff(G,kappa,i)=subii(gcoeff(G,kappa,i), gcoeff(G,i,j));
            for (i=kappa+1; i<=kappamax; i++)
              gcoeff(G,i,kappa)=subii(gcoeff(G,i,kappa), gcoeff(G,i,j));
          }
          else          /* otherwise X is -1 */ 
          {
            for (k=zeros+1; k<j; k++)
              gcoeff(mu,kappa,k)=gadd(gcoeff(mu,kappa,k), gcoeff(mu,j,k));
            for (i=1; i<=n; i++)    
              gcoeff(B,kappa,i)=addii(gcoeff(B,kappa,i), gcoeff(B,j,i));

#ifdef WITH_TRANSFORM
            for (i=1; i<=d; i++)    
              gcoeff(U,kappa,i)=addii(gcoeff(U,kappa,i),gcoeff(U,j,i));
#endif
            ztmp=muliu(gcoeff(G,kappa,j), 2);
            ztmp=addii(gcoeff(G,j,j), ztmp);
            gcoeff(G,kappa,kappa)=addii(gcoeff(G,kappa,kappa), ztmp);
            for (i=1; i<=j; i++)
              gcoeff(G,kappa,i)=addii(gcoeff(G,kappa,i), gcoeff(G,j,i));
            for (i=j+1; i<kappa; i++)
              gcoeff(G,kappa,i)=addii(gcoeff(G,kappa,i), gcoeff(G,i,j));
            for (i=kappa+1; i<=kappamax; i++)
              gcoeff(G,i,kappa)=addii(gcoeff(G,i,kappa), gcoeff(G,i,j));
          }
        }

        else   /* we must have |X| >= 2 */
        {        	
          tmp=ground(gcoeff(mu,kappa,j));
          for (k=zeros+1; k<j; k++)
          {
            rtmp = gmul(tmp, gcoeff(mu,j,k));
            gcoeff(mu,kappa,k) = gsub(gcoeff(mu,kappa,k), rtmp);
          }
          if (!is_bigint(tmp))
            /* X is stored in a long signed int */        	  
          {        	      
            xx = itos(tmp);
            for (i=1; i<=n; i++)  
              gcoeff(B,kappa,i) = subii(gcoeff(B,kappa,i),
                                        mulis(gcoeff(B,j,i),xx));
#ifdef WITH_TRANSFORM
            for (i=1; i<=d; i++)  
              gcoeff(U,kappa,i) = subii(gcoeff(U,kappa,i),
                                      mulis(gcoeff(U,j,i), xx));
#endif
            gcoeff(G,kappa,kappa) = subii(gcoeff(G,kappa,kappa),
                                          mulis(gcoeff(G,kappa,j), 2*xx));

            ztmp = mulis(gcoeff(G,j,j), xx);
            ztmp = mulis(ztmp, xx);
            gcoeff(G,kappa,kappa)=addii(gcoeff(G,kappa,kappa), ztmp);
            for (i=1; i<=j; i++)
              gcoeff(G,kappa,i) = subii(gcoeff(G,kappa,i),
                                        mulis(gcoeff(G,j,i), xx));
            for (i=j+1; i<kappa; i++)
              gcoeff(G,kappa,i) = subii(gcoeff(G,kappa,i),
                                        mulis(gcoeff(G,i,j), xx));
            for (i=kappa+1; i<=kappamax; i++)
              gcoeff(G,i,kappa) = subii(gcoeff(G,i,kappa), 
                                        mulis(gcoeff(G,i,j), xx));
          }

          else
          {
            X = grndtoi(tmp,&expo);
            if (expo <= 0)
            {
              expo = 0;
              for (i=1; i<=n; i++) 
              {
                ztmp = mulii(X, gcoeff(B,j,i));
                gcoeff(B,kappa,i) = subii(gcoeff(B,kappa,i), ztmp);
              }
#ifdef WITH_TRANSFORM
              for (i=1; i<=d; i++) 
              {
                ztmp = mulii(X, gcoeff(U,j,i));
                gcoeff(U,kappa,i) = subii(gcoeff(U,kappa,i), ztmp);
              }
#endif
              ztmp = mulii(gcoeff(G,kappa,j), X);
              ztmp = muliu(ztmp, 2);
              gcoeff(G,kappa,kappa) = subii(gcoeff(G,kappa,kappa), ztmp);
              ztmp = mulii(gcoeff(G,j,j), X);
              ztmp = mulii(ztmp, X);
              gcoeff(G,kappa,kappa) = addii(gcoeff(G,kappa,kappa), ztmp);
              for (i=1; i<=j; i++)
              {
                ztmp = mulii( X, gcoeff(G,j,i));
                gcoeff(G,kappa,i) = subii(gcoeff(G,kappa,i), ztmp);
              }
              for (i=j+1; i<kappa; i++)
              {
                ztmp = mulii( X, gcoeff(G,i,j));
                gcoeff(G,kappa,i) = subii(gcoeff(G,kappa,i), ztmp);
              } 
              for (i=kappa+1; i<=kappamax; i++)
              {
                ztmp = mulii( X, gcoeff(G,i,j));
                gcoeff(G,i,kappa) = subii(gcoeff(G,i,kappa), ztmp);
              }
            }
            else
            {
              for (i=1; i<=n; i++)  
              {
                ztmp = mulii( X, gcoeff(B,j,i));
                ztmp = shifti( ztmp, expo); 
                gcoeff(B,kappa,i) = subii( 
                    gcoeff(B,kappa,i), ztmp);
              }

#ifdef WITH_TRANSFORM
              for (i=1; i<=d; i++)  
              {
                ztmp = mulii( X, gcoeff(U,j,i));
                ztmp = shifti( ztmp, expo); 
                gcoeff(U,kappa,i) = subii( 
                    gcoeff(U,kappa,i), ztmp);
              }
#endif

              ztmp = mulii( gcoeff(G,kappa,j), X);
              ztmp = shifti( ztmp, expo+1);
              gcoeff(G,kappa,kappa) = subii( 
                  gcoeff(G,kappa,kappa), ztmp);
              ztmp = mulii( gcoeff(G,j,j), X);
              ztmp = mulii( ztmp,  X);
              ztmp = shifti( ztmp, 2*expo);
              gcoeff(G,kappa,kappa) = addii( 
                  gcoeff(G,kappa,kappa), ztmp);

              for (i=1; i<=j; i++)
              {
                ztmp = mulii( X, gcoeff(G,j,i));
                ztmp = shifti( ztmp, expo);
                gcoeff(G,kappa,i) = subii( 
                    gcoeff(G,kappa,i), ztmp);
              }

              for (i=j+1; i<kappa; i++)
              {
                ztmp = mulii( X, gcoeff(G,i,j));
                ztmp = shifti( ztmp, expo);
                gcoeff(G,kappa,i) = subii( 
                    gcoeff(G,kappa,i), ztmp);
              } 

              for (i=kappa+1; i<=kappamax; i++)
              {
                ztmp = mulii( X, gcoeff(G,i,j));
                ztmp = shifti( ztmp, expo);
                gcoeff(G,i,kappa) = subii( 
                    gcoeff(G,i,kappa), ztmp);
              }
            }
          }
        }
      }
    }
    /* Anything happened? */
    if (test) aa = zeros+1;
  } while (test);

  gel(s,zeros) = itor(gcoeff(G,kappa,kappa),prec);
  /* the last s[kappa-1]=r[kappa][kappa] is computed only if kappa increases */
  for (k=zeros+1; k<=kappa-2; k++)
  {
    tmp = gmul(gcoeff(mu,kappa,k), gcoeff(r,kappa,k));
    gel(s,k) = gsub(gel(s,k-1), tmp);
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

  n = lg(B)-1;
  d = lg(gel(B,1))-1;
  if(DEBUGLEVEL>=4)
   fprintferr ("d = %d, n=%d\n", d, n);
  if(DEBUGLEVEL>=2)
  {
    fprintferr("Entering LLL^2: LLL-reduction factors(%Zs,%Zs)\n",ctt,halfplus);
    fprintferr("Working precision set to %d bits\n", prec);
  }

  alpha = cgetg(d+1, t_VECSMALL);

  mu = zeromatcopy(d,d);
  r  = zeromatcopy(d,d);
  s  = zerovec(d+2)+1;
  SPtmp = zerovec(d+1);

  /* ********************************* */
  /* Step2: Initializing the main loop */
  /* ********************************* */   
  
  newkappa = 1;
  loops = lovasz = 0;
  kappamax = 1;
  i = 1; 

  do {
    gcoeff(G,i,i) = ZV_dotsquare(row(B,i));
    gcoeff(r,i,i) = itor(gcoeff(G,i,i), prec);
  } while ((signe(gcoeff(G,i,i)) == 0)&&(++i <=d));
  zeros = i-1; /* all vectors B[i] with i <= zeros are zero vectors */
  kappa = i+1;
  if (zeros < d)
    gcoeff(r,zeros+1,zeros+1) = itor(gcoeff(G,zeros+1,zeros+1),prec);
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
        gcoeff(G,kappa,i) = ZV_dotproduct(row(B,kappa), row(B,i));
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
        output(B);output(r);
      }

      /* ************************************ */
      /* Step4: Success of Lovasz's condition */
      /* ************************************ */  
      /* xtt * gcoeff(r,kappa-1,kappa-1) <= s[kappa-2] ?? */
      
      tmp = gmul( gcoeff(r,kappa-1,kappa-1), ctt);
      if (DEBUGLEVEL>=4)
        fprintferr("s[%ld] is %Zs\n %Zs\n", kappa-2, gel(s,kappa-2),
                                            gcoeff(r,kappa-1,kappa-1));
      lovasz++;
      if( gcmp(tmp, gel(s,kappa-2)) <=0 ) {
        alpha[kappa] = kappa;
        tmp = gmul( gcoeff(mu,kappa,kappa-1), gcoeff(r,kappa,kappa-1));
        gcoeff(r,kappa,kappa) = gsub( gel(s,kappa-2), tmp);
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
          tmp = gmul(gcoeff(r,kappa-1,kappa-1), ctt);
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

        mutmp = row(mu,kappa2);
        for (i=kappa2; i>kappa; i--)
          for (j=1;j<=d;j++)
            gcoeff(mu,i,j) = gcoeff(mu,i-1,j);
        for (j=1;j<=d;j++)
          gcoeff(mu,kappa,j) = gel(mutmp,j);

        mutmp = row(r,kappa2);
        for (i=kappa2; i>kappa; i--)
          for (j=1;j<=d;j++)
            gcoeff(r,i,j) = gcoeff(r,i-1,j);
        for (j=1;j<=d;j++)
          gcoeff(r,kappa,j) = gel(mutmp,j);

        gcoeff(r,kappa,kappa) = gel(s,kappa-1);

        if (DEBUGLEVEL>=4)
          fprintferr("Step 6 is over\n");

        /* ********************* */
        /* Step7: Update B, G, U */
        /* ********************* */  	  

        Btmp = row(B, kappa2);
        for (i=kappa2; i>kappa; i--)
          for(j=1; j<=n; j++)
            gcoeff(B,i,j) = gcoeff(B,i-1,j);
        for(j=1; j<=n; j++)
          gcoeff(B,kappa,j) = gel(Btmp,j);

#ifdef WITH_TRANSFORM
          Btmp = row(U,kappa2);
          for (i=kappa2; i>kappa; i--)
            for(j=1; j<=n; j++)
              gcoeff(U,i,j) = gcoeff(U,i-1,j);
          for(j=1; j<=n; j++)
            gcoeff(U,kappa,j) = gel(Btmp, j);
#endif
          for (i=1; i<=kappa2; i++)
            gel(SPtmp,i) = gcoeff(G,kappa2,i);
          for (i=kappa2+1; i<=kappamax; i++)
            gel(SPtmp,i) = gcoeff(G,i,kappa2);
          for (i=kappa2; i>kappa; i--)
          {
            for (j=1; j<kappa; j++)
              gcoeff(G,i,j) = gcoeff(G,i-1,j);
            gcoeff(G,i,kappa) = gel(SPtmp,i-1);
            for (j=kappa+1; j<=i; j++)
              gcoeff(G,i,j) = gcoeff(G,i-1,j-1);
            for (j=kappa2+1; j<=kappamax; j++)
              gcoeff(G,j,i) = gcoeff(G,j,i-1);     
          }
          for (i=1; i<kappa; i++)
            gcoeff(G,kappa,i) = gel(SPtmp,i);
          gcoeff(G,kappa,kappa) = gel(SPtmp,kappa2);
          for (i=kappa2+1; i<=kappamax; i++)
            gcoeff(G,i,kappa) = gel(SPtmp,i);
          if (DEBUGLEVEL>=4)
          {
            output(B);
            output(G);
            fprintferr("Step 7 is over\n");
          } 

          /* ************************************** */
          /* Step8: Prepare the next loop iteration */
          /* ************************************** */  	  


          if ( (kappa==zeros+1) && (signe(gcoeff(G,kappa,kappa))==0) )
          {
            zeros++;
            kappa++;
            gcoeff(r,kappa,kappa) = gcoeff(G,kappa,kappa);
          }
          kappa++;
          if (DEBUGLEVEL)
          {
            output(B); output(G);
            fprintferr("Step 8 is over, new kappa=%d\n",kappa);
          }

        }
    }

  if (DEBUGLEVEL>=2)
  {
    tmp= gen_1;
    for (i = zeros+1; i<=d; i++)
      tmp = gmul( tmp, gcoeff(r,i,i));
    tmp= gsqrt(tmp,prec);
    fprintferr( "\nLoop iterations = %d \n", loops);
    fprintferr( "Lovasz tests = %d \n", lovasz);
    if (zeros < d)
    {
      fprintferr("Vol(L) is %Zs\n", tmp);
      tmp = gsqrt(gcoeff(r,zeros+1,zeros+1),prec);
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
