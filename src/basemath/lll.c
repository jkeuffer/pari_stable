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

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <float.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <ctype.h>
#include <limits.h>
#include <gmp.h>

#ifndef NOT_USING_MPFR
#define USING_MPFR
#endif


#ifdef USING_MPFR
#include <mpfr.h>
#endif
#ifdef ZUSE_MPFR
mp_prec_t intprec;
#endif

#ifndef USE_DOUBLE
#ifndef USE_DPE
#ifndef USE_MPFR
#ifndef USE_LONGDOUBLE
#define USE_DPE
#endif
#endif
#endif
#endif

#ifndef ZUSE_MPZ
#ifndef ZUSE_INT
#ifndef ZUSE_MPFR
#ifndef ZUSE_DPE
#define ZUSE_MPZ
#endif
#endif
#endif
#endif

#ifdef USE_DPE
#ifdef FORCE_LONGDOUBLE
#define DPE_USE_LONGDOUBLE
#endif
#endif


#if (LONG_MAX==2147483647L)
#define CPU_32
#define CPU_SIZE 32
#define MAX_LONG 0x1p30
#else
#define CPU_64
#define CPU_SIZE 64
#define MAX_LONG 0x1p53
#endif

#ifndef ETA
#define ETA 0.51
#endif
#ifndef DELTA
#define DELTA 0.99
#endif


#include "intclass.h"
#include "mat.h"
#include "generate.h"
#include "fpclass.h"
#include "basic.h"
#include "proved.h"

FP_NR halfplus, onedothalfplus, ctt;
ZRANDSTATE state;


// #define VERBOSE
// #define TRIANGULAR
// #define DEBUG 
// #define WITH_TRANSFORM

#ifdef TRIANGULAR
#ifndef SHIFT 
#define SHIFT 0
#endif
#endif

#ifdef DEBUG
#define LOOPS_BABAI 10
#endif

/* Reference for the algorithm:
Floating-Point LLL Revisited, by Phong Nguyen and Damien Stehle
Proceedings of Eurocrypt 2005.
*/


#ifdef VERBOSE
int
cputime ()
{
  struct rusage rus;

  getrusage (RUSAGE_SELF, &rus);
  return rus.ru_utime.tv_sec * 1000 + rus.ru_utime.tv_usec / 1000;
}
#endif


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
Babai (int kappa, mat_ZZ *G, mat_ZZ *B, mat_ZZ *U, 
       mat_RR *mu, mat_RR *r, FP_NR *s, 
       int a, int zeros, int kappamax, int n,
       Z_NR ztmp, FP_NR tmp, FP_NR rtmp)
{
  int d, i, j, k, test, aa, sg;
  signed long xx;
  MP_EXP_T expo;
  U->NumRows = U->NumRows;
  B->NumRows = B->NumRows;
#ifdef DEBUG
  int loops=0;
#endif 
#ifdef USE_MPFR
  Z_NR X;
  ZINIT (X);
#else
  long int X;
#endif

  d = G->NumRows;

  if (a > zeros)
    aa = a;
  else
    aa = zeros+1;

#ifdef DEBUG
  printf("\nr: \n");
  Print_matf (r->coeff, kappamax, kappamax);
  printf("\n          STARTING BABAI WITH k=%d AND dim=%d\n", kappa, d);
  loops = 0;
  printf("\nmu: \n");
  Print_matf (mu->coeff, kappamax, kappamax);
  printf ("a is %d, zeros is %d, aa is %d\n", a, zeros, aa);
  Print_mat (B->coeff, kappamax, n);
#endif

  do
    {
      test=0;

#ifdef DEBUG     
      loops++; 
      if (loops>LOOPS_BABAI){	  
	printf("INFINITE LOOP?\n");
	exit(0);
      }
#endif 


      /* ************************************** */
      /* Step2: compute the GSO for stage kappa */
      /* ************************************** */

      for (j=aa; j<kappa; j++){
	if (j > zeros+2){
	  MUL (tmp, mu->coeff[j][zeros+1], r->coeff[kappa][zeros+1]);
	  SET_Z (rtmp, G->coeff[kappa][j]);
	  SUB (rtmp, rtmp, tmp);
	  for (k=zeros+2; k<j-1; k++){
	    MUL (tmp, mu->coeff[j][k], r->coeff[kappa][k]);
	    SUB (rtmp, rtmp, tmp);
	  }
	  MUL (tmp, mu->coeff[j][j-1], r->coeff[kappa][j-1]);
	  SUB (r->coeff[kappa][j], rtmp, tmp);
	}
	else if (j==zeros+2){	      
	  MUL (tmp, mu->coeff[j][zeros+1], r->coeff[kappa][zeros+1]);
	  SET_Z (rtmp, G->coeff[kappa][j]);
	  SUB (r->coeff[kappa][j], rtmp, tmp);
	}
	else
	  SET_Z (r->coeff[kappa][j], G->coeff[kappa][j]);
	
	DIV (mu->coeff[kappa][j], r->coeff[kappa][j], r->coeff[j][j]);
      }
      
#ifdef DEBUG
      if (loops <=LOOPS_BABAI){
	printf("\nmu :\n");
	Print_matf (mu->coeff, kappa, kappa);
	printf("\nr :\n");
	Print_matf (r->coeff, kappa, kappa);
      }
#endif

      /* **************************** */
      /* Step3--5: compute the X_j's  */
      /* **************************** */
      
      for (j=kappa-1; j>zeros; j--)
	{
	  /* test of the relaxed size-reduction condition */
	  
	  ABS (tmp, mu->coeff[kappa][j]);

#ifdef DEBUG
	  if (loops<=LOOPS_BABAI)
	    {
	      printf( "tmp is : "); 
	      OUT(tmp); printf( "\n");
	    }
#endif

	  if ((CMP (tmp, halfplus)) > 0) 
	    {
	      test = 1;
	      /* we consider separately the case X = +-1 */     
	      if ((CMP (tmp, onedothalfplus))<=0 )   
		{
#ifdef DEBUG
#ifdef USE_MPFR
		  printf(" X is pm1, tmp is %E, halfplus is %E\n",
			 mpfr_get_d (tmp, GMP_RNDN), 
			 mpfr_get_d (halfplus, GMP_RNDN));
#endif
#endif
		  
		  sg = SGN ( mu->coeff[kappa][j]);
		  if ( sg >=0 )   /* in this case, X is 1 */
		    {

		      for (k=zeros+1; k<j; k++)
			SUB (mu->coeff[kappa][k], 
			     mu->coeff[kappa][k], 
			     mu->coeff[j][k]);
		      
		      for (i=1; i<=n; i++)    
		        ZSUB (B->coeff[kappa][i], 
				 B->coeff[kappa][i], 
				 B->coeff[j][i]);

#ifdef WITH_TRANSFORM
		      for (i=1; i<=d; i++) 
			ZSUB (U->coeff[kappa][i], 
			      U->coeff[kappa][i], 
			      U->coeff[j][i]);
#endif

		      ZMUL_UI (ztmp, G->coeff[kappa][j], 2);
		      ZSUB (ztmp, G->coeff[j][j], ztmp);
		      ZADD (G->coeff[kappa][kappa], 
			    G->coeff[kappa][kappa], ztmp);

    
		      for (i=1; i<=j; i++)
			ZSUB (G->coeff[kappa][i], 
			      G->coeff[kappa][i], 
			      G->coeff[j][i]);

		      for (i=j+1; i<kappa; i++)
			ZSUB (G->coeff[kappa][i], 
			      G->coeff[kappa][i], 
			      G->coeff[i][j]);
		      
		      for (i=kappa+1; i<=kappamax; i++)
			ZSUB (G->coeff[i][kappa], 
			      G->coeff[i][kappa], 
			      G->coeff[i][j]);
		    }
		  
		  else          /* otherwise X is -1 */ 
		    {
		      for (k=zeros+1; k<j; k++)
			ADD (mu->coeff[kappa][k], 
			     mu->coeff[kappa][k], 
			     mu->coeff[j][k]);

		      for (i=1; i<=n; i++)    
			ZADD (B->coeff[kappa][i], 
			      B->coeff[kappa][i], 
			      B->coeff[j][i]);

#ifdef WITH_TRANSFORM
		      for (i=1; i<=d; i++)    
			ZADD (U->coeff[kappa][i], 
			      U->coeff[kappa][i], 
			      U->coeff[j][i]);
#endif
    
		      ZMUL_UI (ztmp, G->coeff[kappa][j], 2);
		      ZADD (ztmp, G->coeff[j][j], ztmp);
		      ZADD (G->coeff[kappa][kappa], 
			    G->coeff[kappa][kappa], ztmp);

		      for (i=1; i<=j; i++)
			ZADD (G->coeff[kappa][i], 
			      G->coeff[kappa][i], 
			      G->coeff[j][i]);

		      for (i=j+1; i<kappa; i++)
			ZADD (G->coeff[kappa][i], 
			      G->coeff[kappa][i], 
			      G->coeff[i][j]);

		      for (i=kappa+1; i<=kappamax; i++)
			ZADD (G->coeff[i][kappa], 
			      G->coeff[i][kappa], 
			      G->coeff[i][j]);
		    }
		}
	      
	      else   /* we must have |X| >= 2 */
		{		

		  RND (tmp, mu->coeff[kappa][j]);
		  
		  for (k=zeros+1; k<j; k++)
		    {
		      MUL (rtmp, tmp, mu->coeff[j][k]);
		      SUB (mu->coeff[kappa][k], mu->coeff[kappa][k], rtmp);
		    }
		  
		  if (EXP(tmp) < CPU_SIZE-2)   
		    /* X is stored in a long signed int */		  
		    {		      
		      GET_SI (xx, tmp);
		      
#ifdef DEBUG
		      if (loops<=LOOPS_BABAI)
			{
			  printf("          xx[%d] is %ld\n", j, xx);
			  printf("          and tmp was ");
			  OUT(tmp); printf("\n");
			}
#endif

		      for (i=1; i<=n; i++)  
			{
			  if (xx > 0)
			    {
			      ZSUBMUL_UI (B->coeff[kappa][i], 
					  B->coeff[j][i], 
					  (unsigned long int) xx);
			    }
			  else
			    {
			      ZADDMUL_UI (B->coeff[kappa][i], 
					  B->coeff[j][i], 
					  (unsigned long int) -xx);
			    }
			}

#ifdef WITH_TRANSFORM
		      for (i=1; i<=d; i++)  
			{
			  if (xx > 0)
			    {
			      ZSUBMUL_UI (U->coeff[kappa][i], 
					  U->coeff[j][i], 
					  (unsigned long int) xx);
			    }
			  else
			    {
			      ZADDMUL_UI (U->coeff[kappa][i], 
					  U->coeff[j][i], 
					  (unsigned long int) -xx);
			    }
			}
#endif


		      if (xx>0)
			{
			  ZSUBMUL_UI (G->coeff[kappa][kappa], 
				      G->coeff[kappa][j],
				      (unsigned long int) 2*xx);
			}
		      else
			{
			  ZADDMUL_UI (G->coeff[kappa][kappa], 
				      G->coeff[kappa][j],
				      (unsigned long int) -2*xx);
			}
		      
		      ZMUL_SI (ztmp, G->coeff[j][j], xx);
		      ZMUL_SI (ztmp, ztmp, xx);
		      ZADD (G->coeff[kappa][kappa], 
			    G->coeff[kappa][kappa], ztmp);	

		      for (i=1; i<=j; i++)
			{
			  if (xx>0)
			    {
			      ZSUBMUL_UI (G->coeff[kappa][i], 
					  G->coeff[j][i], 
					  (unsigned long int) xx);
			    }
			  else
			    {
			      ZADDMUL_UI (G->coeff[kappa][i], 
					  G->coeff[j][i], 
					  (unsigned long int) -xx);
			    }

			}

		      for (i=j+1; i<kappa; i++)
			{
			  if (xx>0)
			    {
			      ZSUBMUL_UI (G->coeff[kappa][i], 
					  G->coeff[i][j], 
					  (unsigned long int) xx);
			    }
			  else
			    {
			      ZADDMUL_UI (G->coeff[kappa][i], 
					  G->coeff[i][j], 
					  (unsigned long int) -xx);
			    }
			} 
		      
		      for (i=kappa+1; i<=kappamax; i++)
			{
			  if (xx>0)
			    {
			      ZSUBMUL_UI (G->coeff[i][kappa], 
					  G->coeff[i][j], 
					  (unsigned long int) xx);
			    }
			  else
			    {
			      ZADDMUL_UI (G->coeff[i][kappa], 
					  G->coeff[i][j], 
					  (unsigned long int) -xx);
			    }
			}
		    }
		  
		  else
		    {
#ifdef USE_MPFR
		      expo = GET_Z_EXP (X, tmp);
#ifdef DEBUG
		      printf("tmp is "); OUT (tmp);
		      printf("\nand expo is %d, and X is ", (int) expo);
		      ZOUT(X); printf("\n");
#endif
		      if (expo <= 0)
			{
			  ZDIV_2EXP (X, X, -expo);
			  expo = 0;

			  for (i=1; i<=n; i++) 
			    {
			      ZMUL (ztmp, X, B->coeff[j][i]);
			      ZSUB (B->coeff[kappa][i], 
				    B->coeff[kappa][i], ztmp);
			    }

#ifdef WITH_TRANSFORM
			  for (i=1; i<=d; i++) 
			    {
			      ZMUL (ztmp, X, U->coeff[j][i]);
			      ZSUB (U->coeff[kappa][i], 
				    U->coeff[kappa][i], ztmp);
			    }
#endif

			  ZMUL (ztmp, G->coeff[kappa][j], X);
			  ZMUL_UI (ztmp, ztmp, 2);
			  ZSUB (G->coeff[kappa][kappa], 
				G->coeff[kappa][kappa], ztmp);
			  ZMUL (ztmp, G->coeff[j][j], X);
			  ZMUL (ztmp, ztmp, X);
			  ZADD (G->coeff[kappa][kappa], 
				G->coeff[kappa][kappa], ztmp);

			  for (i=1; i<=j; i++)
			    {
			      ZMUL (ztmp, X, G->coeff[j][i]);
			      ZSUB (G->coeff[kappa][i], 
				    G->coeff[kappa][i], ztmp);
			    }

			  for (i=j+1; i<kappa; i++)
			    {
			      ZMUL (ztmp, X, G->coeff[i][j]);
			      ZSUB (G->coeff[kappa][i], 
				    G->coeff[kappa][i], ztmp);
			    } 

			  for (i=kappa+1; i<=kappamax; i++)
			    {
			      ZMUL (ztmp, X, G->coeff[i][j]);
			      ZSUB (G->coeff[i][kappa], 
				       G->coeff[i][kappa], ztmp);
			    }
			}


		      else
			{
			  for (i=1; i<=n; i++)  
			    {
			      ZMUL (ztmp, X, B->coeff[j][i]);
			      ZMUL_2EXP (ztmp, ztmp, expo); 
			      ZSUB (B->coeff[kappa][i], 
				    B->coeff[kappa][i], ztmp);
			    }

#ifdef WITH_TRANSFORM
			  for (i=1; i<=d; i++)  
			    {
			      ZMUL (ztmp, X, U->coeff[j][i]);
			      ZMUL_2EXP (ztmp, ztmp, expo); 
			      ZSUB (U->coeff[kappa][i], 
				    U->coeff[kappa][i], ztmp);
			    }
#endif

			  ZMUL (ztmp, G->coeff[kappa][j], X);
			  ZMUL_2EXP (ztmp, ztmp, expo+1);
			  ZSUB (G->coeff[kappa][kappa], 
				G->coeff[kappa][kappa], ztmp);
			  ZMUL (ztmp, G->coeff[j][j], X);
			  ZMUL (ztmp, ztmp, X);
			  ZMUL_2EXP (ztmp, ztmp, 2*expo);
			  ZADD (G->coeff[kappa][kappa], 
				G->coeff[kappa][kappa], ztmp);

			  for (i=1; i<=j; i++)
			    {
			      ZMUL (ztmp, X, G->coeff[j][i]);
			      ZMUL_2EXP (ztmp, ztmp, expo);
			      ZSUB (G->coeff[kappa][i], 
				       G->coeff[kappa][i], ztmp);
			    }

			  for (i=j+1; i<kappa; i++)
			    {
			      ZMUL (ztmp, X, G->coeff[i][j]);
			      ZMUL_2EXP (ztmp, ztmp, expo);
			      ZSUB (G->coeff[kappa][i], 
				       G->coeff[kappa][i], ztmp);
			    } 

			  for (i=kappa+1; i<=kappamax; i++)
			    {
			      ZMUL (ztmp, X, G->coeff[i][j]);
			      ZMUL_2EXP (ztmp, ztmp, expo);
			      ZSUB (G->coeff[i][kappa], 
				       G->coeff[i][kappa], ztmp);
			    }
			}
#else
		      expo = GET_Z_EXP (&X, tmp);

		      for (i=1; i<=n; i++)  
			{
			  ZMUL_2EXP (ztmp, B->coeff[j][i], expo); 
			  if (X>0)
			    {
			      ZSUBMUL_UI (B->coeff[kappa][i], 
					  ztmp, 
					  (unsigned long int) X);
			    }
			  else
			    {
			      ZADDMUL_UI (B->coeff[kappa][i], 
					  ztmp, 
					  (unsigned long int) -X);
			    }
			}
		      

#ifdef WITH_TRANSFORM
		      for (i=1; i<=d; i++)  
			{
			  ZMUL_2EXP (ztmp, U->coeff[j][i], expo); 
			  if (X>0)
			    {
			      ZSUBMUL_UI (U->coeff[kappa][i], 
					  ztmp, 
					  (unsigned long int) X);
			    }
			  else
			    {
			      ZADDMUL_UI (U->coeff[kappa][i], 
					  ztmp, 
					  (unsigned long int) -X);
			    }
			}
#endif


		      ZMUL_2EXP (ztmp, G->coeff[kappa][j], expo+1);
		      if (X>0)
			{
			  ZSUBMUL_UI (G->coeff[kappa][kappa], ztmp, 
				      (unsigned long int) X);
			}
		      else
			{
			  ZADDMUL_UI (G->coeff[kappa][kappa], ztmp, 
				      (unsigned long int) -X);

			}
		      
		      ZMUL_SI (ztmp, G->coeff[j][j], X);
		      ZMUL_SI (ztmp, ztmp, X);
		      ZMUL_2EXP (ztmp, ztmp, 2*expo);
		      ZADD (G->coeff[kappa][kappa], 
			    G->coeff[kappa][kappa], ztmp);

		      for (i=1; i<=j; i++)
			{
			  ZMUL_2EXP (ztmp, G->coeff[j][i], expo);
			  if (X>0)
			    {
			      ZSUBMUL_UI (G->coeff[kappa][i], ztmp,
					  (unsigned long int) X);
			    }
			  else
			    {
			      ZADDMUL_UI (G->coeff[kappa][i], ztmp,
					  (unsigned long int) -X);
			    }
			}
		      
		      for (i=j+1; i<kappa; i++)
			{
			  ZMUL_2EXP (ztmp, G->coeff[i][j], expo);
			  if (X>0)
			    {
			      ZSUBMUL_UI (G->coeff[kappa][i], ztmp,
					  (unsigned long int) X);
			    }

			  else
			    {
			      ZADDMUL_UI (G->coeff[kappa][i], ztmp,
					  (unsigned long int) -X);
			    }
			} 
		      
		      for (i=kappa+1; i<=kappamax; i++)
			{
			  ZMUL_2EXP (ztmp, G->coeff[i][j], expo);
			  if (X>0)
			    {
			      ZSUBMUL_UI (G->coeff[i][kappa], ztmp,
					  (unsigned long int) X);
			    }
			  else
			    {
			      ZADDMUL_UI (G->coeff[i][kappa], ztmp,
					  (unsigned long int) -X);
			    }
			}

#endif
		    }
		}
	    }
	}

      
      /* Anything happened? */
      if (test) aa = zeros+1;
      
#ifdef DEBUG
      if (loops<=LOOPS_BABAI)
	{
	  printf("          test is %d\n", test);
	  printf("\nmu: \n");
	  Print_matf (mu->coeff, kappa, kappa);
	  printf("\nr: \n");
	  Print_matf (r->coeff, kappa, kappa);
	}
#endif
      
    }
  while (test);
  

  SET_Z (s[zeros], G->coeff[kappa][kappa]);
  /* the last s[kappa-1]=r[kappa][kappa] is computed only if kappa increases */
  for (k=zeros+1; k<=kappa-2; k++){
    MUL (tmp, mu->coeff[kappa][k], r->coeff[kappa][k]);
    SUB (s[k], s[k-1], tmp);
  }
  
#ifdef DEBUG
  printf("          Number of loops is %d\n", loops);
  Print_mat (G->coeff, kappamax, kappamax);
#endif
#ifdef USE_MPFR
  ZCLEAR (X);
#endif
  
}





/* ****************** */
/* ****************** */
/* ****************** */
/* The LLL Algorithm  */
/* ****************** */
/* ****************** */
/* ****************** */

/* LLL-reduces the integer matrix(ces) (G,B,U)? "in place" */


void 
LLL (mat_ZZ *G, mat_ZZ *B, mat_ZZ *U)
{
  int kappa, kappa2, d, n=0, i, j, zeros, kappamax;
  mat_RR mu, r;
  FP_NR *s, *mutmp;
  FP_NR tmp, rtmp;
  Z_NR ztmp;
  Z_NR *SPtmp;
  int *alpha;
#ifdef USE_DPE
#ifdef FORCE_LONGDOUBLE
  long double tmp2, y;
#endif
#endif
  Z_NR *Btmp;

#ifdef VERBOSE
  int newkappa, start, loops, lovasz;
#endif


  d = B->NumCols;
  n = B->NumRows;


#ifdef DEBUG
  printf ("d = %d, n=%d\n", d, n);
#endif
  

#ifdef VERBOSE
  fprintf (stderr, 
	   "\nEntering LLL^2: LLL-reduction factors ( ");
  OUT2 (ctt); fprintf (stderr, ", ");
  OUT2 (halfplus); fprintf(stderr, ")\n");
#ifdef USE_MPFR
  fprintf (stderr, 
	   "Working precision set to %d bits\n", 
	   (int) mpfr_get_default_prec());
  if (mpfr_get_default_prec()<53) fprintf(stderr, "Be careful, your precision is particularly low.\n");
#else
#ifdef USE_DPE
#ifdef FORCE_LONGDOUBLE
  tmp2 = 1.0;
  for (j = 0; (y = tmp2 + 1.0) != tmp2; j++, tmp2 = 2.0 * tmp2);
  fprintf ( stderr, 
	    "Working precision set to %d bits.\n", j);
#else

  fprintf ( stderr, 
	    "Working precision set to 53 bits\n");
#endif
#endif
#endif
  fprintf (stderr, 
	   "With MPFR and without forcing a precision, the reduction is guaranteed.\nWith DOUBLES or DPE, the reduction is guaranteed up to dimension 12,\nthe first reported failure is in dimension 55, and it has a\nreasonable chance to terminate in dimension less than 150\n\n");
#endif

  alpha = (int *) malloc((d+1) * sizeof(int)); 
  INIT (tmp);
  INIT (rtmp);
  ZINIT (ztmp);


  init_matrixf (&mu, d, d);
  init_matrixf (&r, d, d);

  s = init_vecf (d+1);
  SPtmp = init_vec (d+1);
  
#ifdef VERBOSE  
  start = cputime();
#endif

#ifdef DEBUG 
  Print_mat (B->coeff, d, n);
  printf("Step 1 is over\n");
#endif 


  /* ********************************* */
  /* Step2: Initializing the main loop */
  /* ********************************* */   
  

#ifdef VERBOSE  
  newkappa = 1;
  loops = lovasz = 0;
#endif

  kappamax = 1;
  i = 1; 

  do {
    ScalarProduct (G->coeff[i][i], B->coeff[i], B->coeff[i], n);
    SET_Z (r.coeff[i][i], G->coeff[i][i]);
  }
  while ((ZSGN (G->coeff[i][i]) == 0)&&(++i <=d));
  zeros = i-1; /* all vectors B[i] with i <= zeros are zero vectors */
  kappa = i+1;

  if (zeros < d) SET_Z (r.coeff[zeros+1][zeros+1], G->coeff[zeros+1][zeros+1]);
  
  for (i=zeros+1; i<=d; i++)
    alpha[i]=1;
  
#ifdef DEBUG
  printf("Step 2 is over\n"); 
  printf("kappa is %d and d is %d\n", kappa, d);
#endif  
  
  while (kappa <= d)
    {

      if (kappa>kappamax) {
	for (i=zeros+1; i<=kappa; i++)
	  ScalarProduct (G->coeff[kappa][i], B->coeff[kappa], B->coeff[i], n);
	kappamax++; 
      }


#ifdef VERBOSE
      loops++;
      if (kappa>newkappa)
	{
	  newkappa++;
	  fprintf (stderr, 
		   "Discovering vector k = %d, iterations = %d ", 
		   kappa, loops);
	  fprintf(stderr, "cputime is %d ms\n", (cputime()-start));
	}
#endif

#ifdef DEBUG
      printf("alpha= ");
      for (i=zeros+1; i<=d; i++) 
	printf("%d ",alpha[i]);
      printf("\n");
      printf("entering the while loop with k=%d\n", kappa);
      Print_mat (B->coeff, d, n);
#endif


      /* ********************************** */
      /* Step3: Call to the Babai algorithm */
      /* ********************************** */   

#ifdef TRIANGULAR 
      if (kappamax + SHIFT <= n){	
	Babai (kappa, G, B, U, &mu, &r, s,  
	       alpha[kappa], zeros, kappamax, kappamax+SHIFT, 
	       ztmp, tmp, rtmp);
      }
      else {
	Babai (kappa, G, B, U, &mu, &r, s,  
	       alpha[kappa], zeros, kappamax, n, 
	       ztmp, tmp, rtmp);
      }
#else
      Babai (kappa, G, B, U, &mu, &r, s, 
	     alpha[kappa], zeros, kappamax, n, 
	     ztmp, tmp, rtmp);
#endif

      
#ifdef DEBUG      
      printf("Step 3 is over\n");  
      Print_mat (B->coeff, kappamax, n);
      Print_matf (r.coeff, kappamax, kappamax);
#endif
      
      /* ************************************ */
      /* Step4: Success of Lovasz's condition */
      /* ************************************ */  
      /* xtt * r.coeff[kappa-1][kappa-1] <= s[kappa-2] ?? */
      
      MUL (tmp, r.coeff[kappa-1][kappa-1], ctt);

#ifdef DEBUG
      printf("s[%d] is ", kappa-2);
      OUT(s[kappa-2]); printf("\n");
      OUT(r.coeff[kappa-1][kappa-1]); printf("\n");
#endif

#ifdef VERBOSE
      lovasz++;
#endif


      if( (CMP (tmp, s[kappa-2])) <=0 ) {
	alpha[kappa] = kappa;
	MUL (tmp, mu.coeff[kappa][kappa-1], r.coeff[kappa][kappa-1]);
	SUB (r.coeff[kappa][kappa], s[kappa-2], tmp);
	kappa++;
      } 
      else
	{

	  /* ******************************************* */
	  /* Step5: Find the right insertion index kappa */
          /* kappa2 remains the initial kappa            */
	  /* ******************************************* */  

	  kappa2 = kappa;
	  do
	    {
#ifdef VERBOSE
	      lovasz++;
#endif
	      kappa--;
	      MUL (tmp, r.coeff[kappa-1][kappa-1], ctt);
	    }
	  while ((kappa>=zeros+2) && ((CMP (s[kappa-2], tmp) <=0 )));

#ifdef DEBUG
	  printf( "Index of insertion: %d \n", kappa);
	  printf("Step 5 is over\n");
	  printf("alpha= ");
	  for (i=1; i<=kappamax; i++) 
	    printf("%d ", alpha[i]);
	  printf("\n");
#endif
	  
	  for (i=kappa; i<kappa2; i++)
	    if (kappa <= alpha[i]) alpha[i] = kappa;

	  for (i=kappa2; i>kappa; i--)
	    alpha[i] = alpha[i-1];

	  for (i=kappa2+1; i<=kappamax; i++)
	    if (kappa < alpha[i]) alpha[i] = kappa;
	  
	  alpha[kappa] = kappa;
	  
#ifdef DEBUG
	  printf("alpha= ");
	  for (i=1; i<=d; i++) 
	    printf("%d ",alpha[i]);
	  printf("\n");
#endif

	  /* ****************************** */
	  /* Step6: Update the mu's and r's */
	  /* ****************************** */  
	  
	  mutmp = mu.coeff[kappa2];
	  for (i=kappa2; i>kappa; i--)
	    mu.coeff[i] = mu.coeff[i-1];
	  mu.coeff[kappa] = mutmp;
	  
	  mutmp = r.coeff[kappa2];
	  for (i=kappa2; i>kappa; i--)
	    r.coeff[i] = r.coeff[i-1];
	  r.coeff[kappa] = mutmp;
	  
	  SET (r.coeff[kappa][kappa], s[kappa-1]);
	  
#ifdef DEBUG 
	  printf("Step 6 is over\n");
#endif
	  
	  /* ********************* */
	  /* Step7: Update B, G, U */
	  /* ********************* */  	  
	  
	  Btmp = B->coeff[kappa2];
	  for (i=kappa2; i>kappa; i--)
	    B->coeff[i] = B->coeff[i-1];
	  B->coeff[kappa] = Btmp;

#ifdef WITH_TRANSFORM
	  Btmp = U->coeff[kappa2];
	  for (i=kappa2; i>kappa; i--)
	    U->coeff[i] = U->coeff[i-1];
	  U->coeff[kappa] = Btmp;
#endif

	  for (i=1; i<=kappa2; i++)
	    ZSET (SPtmp[i], G->coeff[kappa2][i]);

	  for (i=kappa2+1; i<=kappamax; i++)
	    ZSET (SPtmp[i], G->coeff[i][kappa2]);
	  
	  for (i=kappa2; i>kappa; i--)
	    {
	      for (j=1; j<kappa; j++)
		ZSET (G->coeff[i][j], G->coeff[i-1][j]);
	      
	      ZSET (G->coeff[i][kappa], SPtmp[i-1]);
	      
	      for (j=kappa+1; j<=i; j++)
		ZSET (G->coeff[i][j], G->coeff[i-1][j-1]);
	      
	      for (j=kappa2+1; j<=kappamax; j++)
		ZSET (G->coeff[j][i], G->coeff[j][i-1]);     
	    }
	  
	  for (i=1; i<kappa; i++)
	    ZSET (G->coeff[kappa][i], SPtmp[i]);

	  ZSET (G->coeff[kappa][kappa], SPtmp[kappa2]);

	  for (i=kappa2+1; i<=kappamax; i++)
	    ZSET (G->coeff[i][kappa], SPtmp[i]);

#ifdef DEBUG
	  Print_mat (B->coeff, kappamax, n);
	  Print_mat (G->coeff, kappamax, kappamax);
	  printf("Step 7 is over\n");
#endif
	  


	  /* ************************************** */
	  /* Step8: Prepare the next loop iteration */
	  /* ************************************** */  	  


	  if ( (kappa==zeros+1) && (ZSGN(G->coeff[kappa][kappa])==0) )
	    {
	      zeros++;
	      kappa++;
	      SET_Z (r.coeff[kappa][kappa], G->coeff[kappa][kappa]);
	    }
	  
	  kappa++;
	  
#ifdef DEBUG	  
	  Print_mat (B->coeff, kappamax, n);
	  Print_mat (G->coeff, kappamax, kappamax);
	  printf("Step 8 is over, new kappa=%d\n",kappa);
#endif
	  
	}

    };  

 
#ifdef VERBOSE
  SET_D (tmp, 1.0);
  for (i = zeros+1; i<=d; i++)
    MUL (tmp, tmp, r.coeff[i][i]);
  SQRT (tmp, tmp);

  fprintf (stderr, "\nLoop iterations = %d \n", loops);
  fprintf (stderr, "Lovasz tests = %d \n", lovasz);
  fprintf (stderr, "Cputime is %d ms\n", (cputime()-start));
  if (zeros < d)
    {
      fprintf (stderr, "Vol(L) is "); OUT2(tmp); fprintf(stderr, "\n");      
      SQRT (tmp, r.coeff[zeros+1][zeros+1]);
      fprintf (stderr, "||b_1|| is "); 
      OUT2(tmp); fprintf(stderr, "\n\n");
    }
#endif
  

  free (alpha);

  clear_matrixf (&mu, d, d);
  clear_matrixf (&r, d, d);

  CLEAR (tmp);
  CLEAR (rtmp);
  ZCLEAR (ztmp);

  clear_vecf (s, d+1);
  clear_vec (SPtmp, d+1);
}





/* ********************** */
/*  MAIN **************** */
/* ********************** */

int
main (int argc, char *argv[])
{
  int d=0, i, j, n, bits, bits2=0, decal;
  double alpha, delta, eta;
  mat_ZZ B, G, U;
  char c=0;
#ifdef USE_MPFR
  double rho;
  int wantedprec=0, goodprec;
#endif
#ifdef USING_MPFR
  mpfr_t tmp;
  size_t s=0;
#endif
  argc=argc;

  INIT (halfplus);
  INIT (onedothalfplus);
  INIT (ctt);
  
  ZRANDINIT (state);
  decal = 1;

  delta = DELTA;
  eta = ETA;

  if (strcmp(argv[1],"-delta")==0) 
    {
      decal+=2;
      delta = atof(argv[2]);
    }

  if (strcmp(argv[decal],"-eta")==0)
    {
      eta = atof(argv[decal+1]);
      decal+=2;
    }

  if (strcmp(argv[decal],"-delta")==0)
    {
      delta = atof(argv[decal+1]);
      decal+=2;
    }

  if ((delta >=1.0 ) || (delta <=0.25) || (eta <=0.5) || (eta>=sqrt(delta)))
    {
      fprintf (stderr, "Incorrect parameters! You must choose\ndelta in (0.25,1) and eta in (0.5, sqrt(delta))\n"); 
      exit(1);
    }


  SET_D (halfplus, eta) ;
  SET_D (onedothalfplus, 1.0+eta);
  SET_D (ctt, delta);  

  if ( strcmp(argv[decal], "h")==0) 
    {
      printf("Please have a look at the README file.\n");
      exit(1);
    }
  

  if (strcmp(argv[decal], "m")==0)
    {
      d = atoi(argv[decal+1]);
      n = atoi(argv[decal+2]);
      init_matrix (&B, d, n);
#ifdef ZUSE_MPFR
      intprec = atoi(argv[decal+3]);
      SET_WANTED_PREC(wantedprec,decal+4);
#else
      SET_WANTED_PREC(wantedprec,decal+3);
#endif

      /* read initial '[' */
      while (isspace(c = getchar ()) || c == '\n');
      if (c != '[')
        {
          fprintf (stderr, "Error: '[' expected\n");
          exit (1);
        }

      for (i=1; i<=d; i++)
	{
	  while (isspace(c = getchar ()) || c == '\n');
	  if (c != '[')
	    {
	      fprintf (stderr, "Error at row %d: '[' expected instead of %c\n", i, c);
	      exit (1);
	    }
	  for (j=1; j<=n; j++)
	    ZIN(B.coeff[i][j]);

	  while (isspace(c = getchar ()) || c=='\n');
	  if (c != ']')
	    {
	      fprintf (stderr, "Error: ']' expected at line %u\n", i);
	      exit (1);
	    }
	}
    }

  if (strcmp(argv[decal], "r")==0)
    {
      d = atoi(argv[decal+1]);
      bits = atoi(argv[decal+2]);
#ifdef ZUSE_MPFR
      intprec = atoi(argv[decal+3]);
      SET_WANTED_PREC(wantedprec,decal+4);
#else
      SET_WANTED_PREC(wantedprec,decal+3);
#endif

      init_matrix (&B, d, d+1);
      intrel (&B, bits, d);
    }   

  if (strcmp(argv[decal], "simdioph")==0)
    {
      d = atoi(argv[decal+1]);
      bits = atoi(argv[decal+2]);
      bits2 = atoi(argv[decal+3]);

#ifdef ZUSE_MPFR
      intprec = atoi(argv[decal+4]);
      SET_WANTED_PREC(wantedprec,decal+5);
#else
      SET_WANTED_PREC(wantedprec,decal+4);
#endif

      init_matrix (&B, d+1, d+1);
      simdioph (&B, bits, bits2, d);
    }   

#ifdef ZUSE_MPZ
  if (strcmp(argv[decal], "gm")==0)
    {
      d = atoi(argv[decal+1]);
      bits = atoi(argv[decal+2]);
      SET_WANTED_PREC(wantedprec,decal+3);
      init_matrix (&B, d, d);
      goldstein_mayer (&B, bits, d);
    }   
#endif

  if (strcmp(argv[decal], "n")==0)
    {
      d = atoi(argv[decal+1]);
      bits = atoi(argv[decal+2]);
      i = atoi(argv[decal+3]);
#ifdef ZUSE_MPFR
      intprec = atoi(argv[decal+4]);
      SET_WANTED_PREC(wantedprec,decal+5);
#else
      SET_WANTED_PREC(wantedprec,decal+4);
#endif
      init_matrix (&B, 2*d, 2*d);
      ntrulike (&B, bits, d, i); 
    }  

  if (strcmp(argv[decal], "n2")==0)
    {
      d = atoi(argv[decal+1]);
      bits = atoi(argv[decal+2]);
      i = atoi(argv[decal+3]);
#ifdef ZUSE_MPFR
      intprec = atoi(argv[decal+4]);
      SET_WANTED_PREC(wantedprec,decal+5);
#else
      SET_WANTED_PREC(wantedprec,decal+4);
#endif
      init_matrix (&B, 2*d, 2*d);
      ntrulike2 (&B, bits, d, i); 
    }  

  if (strcmp(argv[decal], "a")==0)
    {
      d = atoi(argv[decal+1]);
      alpha = atof(argv[decal+2]);
#ifdef ZUSE_MPFR
      intprec = atoi(argv[decal+3]);
      SET_WANTED_PREC(wantedprec,decal+4);
#else
      SET_WANTED_PREC(wantedprec,decal+3);
#endif
      init_matrix (&B, d, d);
      ajtai (&B, d, alpha);
    }  

#ifndef ZUSE_MPFR
  if (strcmp(argv[decal], "u")==0)
    {
      d = atoi(argv[decal+1]);
      bits = atoi(argv[decal+2]);
      SET_WANTED_PREC(wantedprec,decal+3);
      init_matrix (&B, d, d);
      uniform (&B, bits, d); 
    }  
#endif    

#ifdef USING_MPFR
  if (strcmp(argv[decal], "b")==0)
    {
      d = atoi(argv[decal+1]);
#ifdef ZUSE_MPFR
      intprec = atoi(argv[decal+2]);
      SET_WANTED_PREC(wantedprec,decal+3);
#else
      SET_WANTED_PREC(wantedprec,decal+2);
#endif
      mpfr_set_default_prec (1000);
      init_matrix (&B, d, d);
      GenerateBad (&B, d); 
    }  


  if (strcmp(argv[decal], "k")==0)
    {
      d = atoi(argv[decal+1]);    
      init_matrix (&B, d, d+1);
      bits = atoi(argv[decal+2]);      
      mpfr_init2 (tmp, 2*bits);
#ifdef ZUSE_MPFR
      intprec = atoi(argv[decal+3]);
      SET_WANTED_PREC(wantedprec,decal+4);
#else
      SET_WANTED_PREC(wantedprec,decal+3);
#endif

      for (i=1; i<=d; i++)
	{
	  while (isspace(c) || c=='\n') c = getchar ();
	  s = mpfr_inp_str (tmp, stdin, 10, GMP_RNDN); 
	  if (s==0) fprintf( stderr, "error while reading the input, i est %d \n", i), abort();

          mpfr_mul_2ui (tmp, tmp, bits, GMP_RNDN);
#ifdef ZUSE_MPFR
	  ZSET (B.coeff[i][1], tmp);
#else
	  ZMPFR_GET_Z (B.coeff[i][1], tmp);
#endif
	}
      c = getchar();
      
      for (i=1; i<=d; i++)
	{
	  for(j=2; j<=i; j++)
	    ZSET_UI ( B.coeff[i][j],0);
	  ZSET_UI ( B.coeff[i][i+1],1);
	  for(j=i+2; j<=d+1; j++)
	    ZSET_UI ( B.coeff[i][j],0);
	}
    }
#endif
    

#ifdef USE_MPFR
  rho = (1.0 + eta) * (1.0+eta) / (delta - eta*eta);
  goodprec = (unsigned int) (7.0 + 0.2*d + d* log(rho)/ log(2.0) 
			     +  2.0 * log ( (double) d )  
			     - log( (eta-0.5)*(1.0-delta) ) / log(2));

  if (wantedprec == 0) wantedprec = goodprec;
  mpfr_set_default_prec (wantedprec);
#endif

  
  init_matrix (&G, B.NumRows, B.NumRows);


#ifdef WITH_TRANSFORM
  init_matrix (&U, B.NumRows, B.NumRows);
  for (i=1; i<=B.NumRows; i++)
    for (j=1; j<=B.NumRows; j++)
      {
	if (i==j) ZSET_UI (U.coeff[i][i], 1);
	else ZSET_UI (U.coeff[i][j], 0);
      }
#else
  init_matrix (&U, 0, 0);
#endif

  //  Print_magma (B.coeff, B.NumCols, B.NumRows);

  LLL(&G, &B, &U);

  Print_mat (B.coeff, B.NumCols, B.NumRows);

#ifdef WITH_TRANSFORM
  Print_mat (U.coeff, U.NumCols, U.NumRows);
#endif

  clear_matrix (&B, B.NumCols, B.NumRows);

  clear_matrix (&U, U.NumCols, U.NumRows);
  

#ifdef USING_MPFR
  if (strcmp(argv[decal], "k")==0) mpfr_clear (tmp);
#endif

  return 0;
}

