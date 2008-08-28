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

/********************************************************************/
/**                                                                **/
/**                 LLL Algorithm and close friends                **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

/********************************************************************/
/**             QR Factorization via Householder matrices          **/
/********************************************************************/
static int
no_prec_pb(GEN x)
{
  return (typ(x) != t_REAL || lg(x) >  3
			   || expo(x) < BITS_IN_LONG/2);
}
/* zero x[1..k-1], fill mu */
static int
FindApplyQ(GEN x, GEN mu, GEN B, long k, GEN Q, long prec)
{
  long i, lx = lg(x)-1;
  GEN x2, x1, xd = x + (k-1);

  x1 = gel(xd,1);
  x2 = gsqr(x1);
  if (k < lx)
  {
    long lv = lx - (k-1) + 1;
    GEN beta, Nx, v = cgetg(lv, t_VEC);
    for (i=2; i<lv; i++) {
      x2 = mpadd(x2, gsqr(gel(xd,i)));
      gel(v,i) = gel(xd,i);
    }
    if (!signe(x2)) return 0;
    Nx = gsqrt(x2, prec); if (signe(x1) < 0) setsigne(Nx, -1);
    gel(v,1) = mpadd(x1, Nx);

    if (!signe(x1))
      beta = gtofp(x2, prec); /* make sure typ(beta) != t_INT */
    else
      beta = mpadd(x2, mpmul(Nx,x1));
    gel(Q,k) = mkvec2(invr(beta), v);

    togglesign(Nx);
    gcoeff(mu,k,k) = Nx;
  }
  else
    gcoeff(mu,k,k) = gel(x,k);
  gel(B,k) = x2;
  for (i=1; i<k; i++) gcoeff(mu,k,i) = gel(x,i);
  return no_prec_pb(x2);
}

static void
ApplyQ(GEN Q, GEN r)
{
  GEN s, rd, beta = gel(Q,1), v = gel(Q,2);
  long i, l = lg(v), lr = lg(r);

  rd = r + (lr - l);
  s = mpmul(gel(v,1), gel(rd,1));
  for (i=2; i<l; i++) s = mpadd(s, mpmul(gel(v,i) ,gel(rd,i)));
  s = mpmul(beta, s);
  for (i=1; i<l; i++) gel(rd,i) = mpsub(gel(rd,i), mpmul(s, gel(v,i)));
}
static GEN
ApplyAllQ(GEN Q, GEN r0, long k)
{
  pari_sp av = avma;
  GEN r = leafcopy(r0);
  long j;
  for (j=1; j<k; j++) ApplyQ(gel(Q,j), r);
  return gerepilecopy(av, r);
}
/* compute B[k] = | x[k] |^2, update mu(k, 1..k-1) using Householder matrices
 * (Q = Householder(x[1..k-1]) in factored form) */
static int
incrementalQ(GEN x, GEN L, GEN B, GEN Q, long k, long prec)
{
  GEN r = ApplyAllQ(Q, gel(x,k), k);
  return FindApplyQ(r, L, B, k, Q, prec);
}
GEN
Q_from_QR(GEN x, long prec)
{
  long j, k = lg(x)-1;
  GEN B = cgetg(k+1, t_VEC), Q = cgetg(k+1, t_VEC), L = zeromatcopy(k,k);
  for (j=1; j<=k; j++)
    if (! incrementalQ(x, L, B, Q, j, prec)) return NULL;
  for (j=1; j<k; j++)
  { /* should set gel(m,j) = gen_1; but need it later */
    GEN m = gel(L,j), invNx = ginv(gel(m,j));
    long i;
    for (i=j+1; i<=k; i++) gel(m,i) = gmul(invNx, gel(m,i));
  }
  for (j=1; j<=k; j++) gcoeff(L,j,j) = gel(B,j);
  return shallowtrans(L);
}
GEN
R_from_QR(GEN x, long prec)
{
  long j, k = lg(x)-1;
  GEN B = cgetg(k+1, t_VEC), Q = cgetg(k+1, t_VEC), L = zeromatcopy(k,k);
  for (j=1; j<=k; j++)
    if (!incrementalQ(x, L, B, Q, j, prec)) return NULL;
  return shallowtrans(L);
}

/********************************************************************/
/**             QR Factorization via Gram-Schmidt                  **/
/********************************************************************/

#if 0
/* return Gram-Schmidt orthogonal basis (f) associated to (e), B is the
 * vector of the (f_i . f_i)*/
GEN
gram_schmidt(GEN e, GEN *ptB)
{
  long i,j,lx = lg(e);
  GEN f = RgM_shallowcopy(e), B, iB;

  B = cgetg(lx, t_VEC);
  iB= cgetg(lx, t_VEC);

  for (i=1;i<lx;i++)
  {
    GEN p1 = NULL;
    pari_sp av = avma;
    for (j=1; j<i; j++)
    {
      GEN mu = gmul(RgV_dotproduct(gel(e,i),gel(f,j)), gel(iB,j));
      GEN p2 = gmul(mu, gel(f,j));
      p1 = p1? gadd(p1,p2): p2;
    }
    p1 = p1? gerepileupto(av, gsub(gel(e,i), p1)): gel(e,i);
    gel(f,i) = p1;
    gel(B,i) = RgV_dotsquare(gel(f,i));
    gel(iB,i) = ginv(gel(B,i));
  }
  *ptB = B; return f;
}
#endif

/********************************************************************/
/**                                                                **/
/**                          LLL ALGORITHM                         **/
/**                                                                **/
/********************************************************************/
static GEN
round_safe(GEN q)
{
  if (typ(q) == t_INT) return q;
  if (expo(q) > 30)
  {
    long e;
    q = grndtoi(q, &e);
    if (e > 0) return NULL;
  } else
    q = ground(q);
  return q;
}

GEN
gram_matrix(GEN x)
{
  long i,j, lx = lg(x), tx = typ(x);
  GEN g;
  if (!is_matvec_t(tx)) pari_err(typeer,"gram");
  g = cgetg(lx,t_MAT);
  for (i=1; i<lx; i++)
  {
    gel(g,i) = cgetg(lx,t_COL);
    for (j=1; j<=i; j++)
      gcoeff(g,i,j) = gcoeff(g,j,i) = RgV_dotproduct(gel(x,i),gel(x,j));
  }
  return g;
}

/* Def: a matrix M is said to be -partially reduced- if | m1 +- m2 | >= |m1|
 * for any two columns m1 != m2, in M.
 *
 * Input: an integer matrix mat whose columns are linearly independent. Find
 * another matrix T such that mat * T is partially reduced.
 *
 * Output: mat * T if flag = 0;  T if flag != 0,
 *
 * This routine is designed to quickly reduce lattices in which one row
 * is huge compared to the other rows.  For example, when searching for a
 * polynomial of degree 3 with root a mod N, the four input vectors might
 * be the coefficients of
 *     X^3 - (a^3 mod N), X^2 - (a^2 mod N), X - (a mod N), N.
 * All four constant coefficients are O(p) and the rest are O(1). By the
 * pigeon-hole principle, the coefficients of the smallest vector in the
 * lattice are O(p^(1/4)), hence significant reduction of vector lengths
 * can be anticipated.
 *
 * An improved algorithm would look only at the leading digits of dot*.  It
 * would use single-precision calculations as much as possible.
 *
 * Original code: Peter Montgomery (1994) */
static GEN
lllintpartialall(GEN m, long flag)
{
  const long ncol = lg(m)-1;
  const pari_sp av = avma;
  GEN tm1, tm2, mid;

  if (ncol <= 1) return flag? matid(ncol): gcopy(m);

  tm1 = flag? matid(ncol): NULL;
  {
    const pari_sp av2 = avma;
    GEN dot11 = ZV_dotsquare(gel(m,1));
    GEN dot22 = ZV_dotsquare(gel(m,2));
    GEN dot12 = ZV_dotproduct(gel(m,1), gel(m,2));
    GEN tm  = matid(2); /* For first two columns only */

    int progress = 0;
    long npass2 = 0;

/* Row reduce the first two columns of m. Our best result so far is
 * (first two columns of m)*tm.
 *
 * Initially tm = 2 x 2 identity matrix.
 * Inner products of the reduced matrix are in dot11, dot12, dot22. */
    while (npass2 < 2 || progress)
    {
      GEN dot12new, q = diviiround(dot12, dot22);

      npass2++; progress = signe(q);
      if (progress)
      {/* Conceptually replace (v1, v2) by (v1 - q*v2, v2), where v1 and v2
	* represent the reduced basis for the first two columns of the matrix.
	* We do this by updating tm and the inner products. */
        togglesign(q);
	dot12new = addii(dot12, mulii(q, dot22));
	dot11 = addii(dot11, mulii(q, addii(dot12, dot12new)));
	dot12 = dot12new;
	ZC_lincomb1_inplace(gel(tm,1), gel(tm,2), q);
      }

      /* Interchange the output vectors v1 and v2.  */
      swap(dot11,dot22);
      swap(gel(tm,1), gel(tm,2));

      /* Occasionally (including final pass) do garbage collection.  */
      if ((npass2 & 0xff) == 0 || !progress)
	gerepileall(av2, 4, &dot11,&dot12,&dot22,&tm);
    } /* while npass2 < 2 || progress */

    {
      long i;
      GEN det12 = subii(mulii(dot11, dot22), sqri(dot12));

      mid = cgetg(ncol+1, t_MAT);
      for (i = 1; i <= 2; i++)
      {
        GEN tmi = gel(tm,i);
	if (tm1)
	{
          GEN tm1i = gel(tm1,i);
	  gel(tm1i,1) = gel(tmi,1);
	  gel(tm1i,2) = gel(tmi,2);
	}
	gel(mid,i) = ZC_lincomb(gel(tmi,1),gel(tmi,2), gel(m,1),gel(m,2));
      }
      for (i = 3; i <= ncol; i++)
      {
	GEN c = gel(m,i);
	GEN dot1i = ZV_dotproduct(gel(mid,1), c);
	GEN dot2i = ZV_dotproduct(gel(mid,2), c);
       /* ( dot11  dot12 ) (q1)   ( dot1i )
	* ( dot12  dot22 ) (q2) = ( dot2i )
	*
	* Round -q1 and -q2 to nearest integer. Then compute
	*   c - q1*mid[1] - q2*mid[2].
	* This will be approximately orthogonal to the first two vectors in
	* the new basis. */
	GEN q1neg = subii(mulii(dot12, dot2i), mulii(dot22, dot1i));
	GEN q2neg = subii(mulii(dot12, dot1i), mulii(dot11, dot2i));

	q1neg = diviiround(q1neg, det12);
	q2neg = diviiround(q2neg, det12);
	if (tm1)
	{
	  gcoeff(tm1,1,i) = addii(mulii(q1neg, gcoeff(tm,1,1)),
				  mulii(q2neg, gcoeff(tm,1,2)));
	  gcoeff(tm1,2,i) = addii(mulii(q1neg, gcoeff(tm,2,1)),
				  mulii(q2neg, gcoeff(tm,2,2)));
	}
	gel(mid,i) = ZC_add(c, ZC_lincomb(q1neg,q2neg, gel(mid,1),gel(mid,2)));
      } /* for i */
    } /* local block */
  }
  if (DEBUGLEVEL>6)
  {
    if (tm1) fprintferr("tm1 = %Ps",tm1);
    fprintferr("mid = %Ps",mid); /* = m * tm1 */
  }
  gerepileall(av, tm1? 2: 1, &mid, &tm1);
  {
   /* For each pair of column vectors v and w in mid * tm2,
    * try to replace (v, w) by (v, v - q*w) for some q.
    * We compute all inner products and check them repeatedly. */
    const pari_sp av3 = avma, lim = stack_lim(av3,2);
    long i, j, npass = 0, e = LONG_MAX;
    GEN dot = cgetg(ncol+1, t_MAT); /* scalar products */

    tm2 = matid(ncol);
    for (i=1; i <= ncol; i++)
    {
      gel(dot,i) = cgetg(ncol+1,t_COL);
      for (j=1; j <= i; j++)
	gcoeff(dot,j,i) = gcoeff(dot,i,j) = ZV_dotproduct(gel(mid,i),gel(mid,j));
    }
    for(;;)
    {
      long reductions = 0, olde = e;
      for (i=1; i <= ncol; i++)
      {
	long ijdif;
	for (ijdif=1; ijdif < ncol; ijdif++)
	{
	  long d, k1, k2;
	  GEN codi, q;

	  j = i + ijdif; if (j > ncol) j -= ncol;
	  /* let k1, resp. k2,  index of larger, resp. smaller, column */
	  if (cmpii(gcoeff(dot,i,i), gcoeff(dot,j,j)) > 0) { k1 = i; k2 = j; }
	  else                                             { k1 = j; k2 = i; }
	  codi = gcoeff(dot,k2,k2);
	  q = signe(codi)? diviiround(gcoeff(dot,k1,k2), codi): gen_0;
	  if (!signe(q)) continue;

	  /* Try to subtract a multiple of column k2 from column k1.  */
	  reductions++; togglesign_safe(&q);
	  ZC_lincomb1_inplace(gel(tm2,k1), gel(tm2,k2), q);
	  ZC_lincomb1_inplace(gel(dot,k1), gel(dot,k2), q);
	  gcoeff(dot,k1,k1) = addii(gcoeff(dot,k1,k1),
			            mulii(q, gcoeff(dot,k2,k1)));
	  for (d = 1; d <= ncol; d++) gcoeff(dot,k1,d) = gcoeff(dot,d,k1);
	} /* for ijdif */
	if (low_stack(lim, stack_lim(av3,2)))
	{
	  if(DEBUGMEM>1) pari_warn(warnmem,"lllintpartialall");
	  gerepileall(av3, 2, &dot,&tm2);
	}
      } /* for i */
      if (!reductions) break;
      e = 0;
      for (i = 1; i <= ncol; i++) e += expi( gcoeff(dot,i,i) );
      if (e == olde) break;
      if (DEBUGLEVEL>6)
      {
	npass++;
	fprintferr("npass = %ld, red. last time = %ld, log_2(det) ~ %ld\n\n",
		    npass, reductions, e);
      }
    } /* for(;;)*/

   /* Sort columns so smallest comes first in m * tm1 * tm2.
    * Use insertion sort. */
    for (i = 1; i < ncol; i++)
    {
      long j, s = i;

      for (j = i+1; j <= ncol; j++)
	if (cmpii(gcoeff(dot,s,s),gcoeff(dot,j,j)) > 0) s = j;
      if (i != s)
      { /* Exchange with proper column; only the diagonal of dot is updated */
	swap(gel(tm2,i), gel(tm2,s));
	swap(gcoeff(dot,i,i), gcoeff(dot,s,s));
      }
    }
    i = 1;
    while (i <= ncol && !signe(gcoeff(dot,i,i))) i++;
    if (i > 1)
    {
      tm2 += (i - 1);
      tm2[0] = evaltyp(t_MAT)|evallg(ncol - i);
    }
  } /* local block */
  return gerepileupto(av, ZM_mul(tm1? tm1: mid, tm2));
}

GEN
lllintpartial(GEN mat) { return lllintpartialall(mat,1); }

GEN
lllintpartial_inplace(GEN mat) { return lllintpartialall(mat,0); }

/********************************************************************/
/**                                                                **/
/**                    COPPERSMITH ALGORITHM                       **/
/**           Finding small roots of univariate equations.         **/
/**                                                                **/
/********************************************************************/

static int
check_condition(double beta, double tau, double rho, long d, long delta, long t)
{
  long dim = d*delta + t;
  double cond = d*delta*(delta+1)/2 - beta*delta*dim
    + rho*delta*(delta - 1) / 2
    + rho * t * delta + tau*dim*(dim - 1)/2;

  if (DEBUGLEVEL >= 4)
    fprintferr("delta = %d, t = %d, cond = %.1lf\n", delta, t, cond);

  return (cond <= 0);
}

static void
choose_params(GEN P, GEN N, GEN X, GEN B, long *pdelta, long *pt)
{
  long d = degpol(P);
  GEN P0 = leading_term(P);
  double logN = gtodouble(glog(N, DEFAULTPREC));
  double tau, beta, rho;
  long delta, t;
  tau = gtodouble(glog(X, DEFAULTPREC)) / logN;
  beta = gtodouble(glog(B, DEFAULTPREC)) / logN;
  if (tau >= beta * beta / d) pari_err(talker, "bound too large");
  /* TODO : remove P0 completely ! */
  rho = gtodouble(glog(P0, DEFAULTPREC)) / logN;

  /* Enumerate (delta,t) by increasing dimension of resulting lattice.
   * Not subtle, but o(1) for computing time */
  t = d; delta = 0;
  for(;;)
  {
    t += d * delta + 1; delta = 0;
    while (t >= 0) {
      if (check_condition(beta, tau, rho, d, delta, t)) {
	*pdelta = delta; *pt = t; return;
      }
      delta++; t -= d;
    }
  }
}

static GEN
do_exhaustive(GEN P, GEN N, long x, GEN B)
{
  GEN tst, sol = vecsmalltrunc_init(2*x + 2);
  long j, l;

  for (j = -x; j <= x; j++)
  {
    tst = gcdii(FpX_eval(P, stoi(j), N), N);

    if (cmpii(tst, B) >= 0) /* We have found a factor of N >= B */
    {
      for (l = 1; l < lg(sol) && j != sol[l]; l++) /*empty*/;
      if (l == lg(sol)) vecsmalltrunc_append(sol, j);
    }
  }
  return zv_to_ZV(sol);
}

/* General Coppersmith, look for a root x0 <= p, p >= B, p | N, |x0| <= X */
GEN
zncoppersmith(GEN P0, GEN N, GEN X, GEN B)
{
  GEN Q, R, N0, M, sh, short_pol, *Xpowers, z, r, sol, nsp, P, tst, Z;
  long delta, i, j, row, d, l, dim, t, bnd = 10;
  const ulong X_SMALL = 1000;

  pari_sp av = avma;

  if (typ(P0) != t_POL || typ(N) != t_INT) pari_err(typeer, "zncoppersmith");
  if (typ(X) != t_INT) {
    X = gfloor(X);
    if (typ(X) != t_INT) pari_err(typeer, "zncoppersmith");
  }
  if (signe(X) < 0) pari_err(talker, "negative bound in zncoppersmith");
  if (!B) B = N;
  if (typ(B) != t_INT) B = gceil(B);

  if (cmpiu(X, X_SMALL) <= 0)
    return gerepileupto(av, do_exhaustive(P0, N, itos(X), B));

  /* bnd-hack is only for the case B = N */
  if (!equalii(B,N)) bnd = 1;

  P = leafcopy(P0); d = degpol(P);
  if (d == 0) { avma = av; return cgetg(1, t_VEC); }
  if (d < 0) pari_err(talker, "zero polynomial forbidden");

  if (!gcmp1(gel(P,d+2)))
  {
    gel(P,d+2) = bezout(gel(P,d+2), N, &z, &r);
    for (j = 0; j < d; j++) gel(P,j+2) = modii(mulii(gel(P,j+2), z), N);
  }
  if (DEBUGLEVEL >= 2) fprintferr("Modified P: %Ps\n", P);

  choose_params(P, N, X, B, &delta, &t);
  if (DEBUGLEVEL >= 2)
    fprintferr("Init: trying delta = %d, t = %d\n", delta, t);
  for(;;)
  {
    dim = d * delta + t;

    /* TODO: In case of failure do not recompute the full vector */
    Xpowers = (GEN*)new_chunk(dim + 1);
    Xpowers[0] = gen_1;
    for (j = 1; j <= dim; j++) Xpowers[j] = mulii(Xpowers[j-1], X);

    /* TODO: in case of failure, use the part of the matrix already computed */
    M = zeromatcopy(dim,dim);

    /* Rows of M correspond to the polynomials
     * N^delta, N^delta Xi, ... N^delta (Xi)^d-1,
     * N^(delta-1)P(Xi), N^(delta-1)XiP(Xi), ... N^(delta-1)P(Xi)(Xi)^d-1,
     * ...
     * P(Xi)^delta, XiP(Xi)^delta, ..., P(Xi)^delta(Xi)^t-1 */
    for (j = 1; j <= d;   j++) gcoeff(M, j, j) = gel(Xpowers,j-1);

    /* P-part */
    if (delta) row = d + 1; else row = 0;

    Q = P;
    for (i = 1; i < delta; i++)
    {
      for (j = 0; j < d; j++,row++)
	for (l = j + 1; l <= row; l++)
	  gcoeff(M, l, row) = mulii(Xpowers[l-1], gel(Q,l-j+1));
      Q = ZX_mul(Q, P);
    }
    for (j = 0; j < t; row++, j++)
      for (l = j + 1; l <= row; l++)
	gcoeff(M, l, row) = mulii(Xpowers[l-1], gel(Q,l-j+1));

    /* N-part */
    row = dim - t; N0 = N;
    while (row >= 1)
    {
      for (j = 0; j < d; j++,row--)
	for (l = 1; l <= row; l++)
	  gcoeff(M, l, row) = mulii(gmael(M, row, l), N0);
      if (row >= 1) N0 = mulii(N0, N);
    }
    /* Z is the upper bound for the L^1 norm of the polynomial,
       ie. N^delta if B = N, B^delta otherwise */
    if (B != N) Z = powiu(B, delta); else Z = N0;

    if (DEBUGLEVEL >= 2)
    {
      if (DEBUGLEVEL >= 6) fprintferr("Matrix to be reduced:\n%Ps\n", M);
      fprintferr("Entering LLL\nbitsize bound: %ld\n", expi(Z));
      fprintferr("expected shvector bitsize: %ld\n", expi(ZM_det_triangular(M))/dim);
    }

    sh = ZM_lll(M, 0.75, LLL_INPLACE);
    /* Take the first vector if it is non constant */
    short_pol = gel(sh,1);
    if (ZV_isscalar(short_pol)) short_pol = gel(sh, 2);

    nsp = gen_0;
    for (j = 1; j <= dim; j++) nsp = addii(nsp, absi(gel(short_pol,j)));

    if (DEBUGLEVEL >= 2)
    {
      fprintferr("Candidate: %Ps\n", short_pol);
      fprintferr("bitsize Norm: %ld\n", expi(nsp));
      fprintferr("bitsize bound: %ld\n", expi(mului(bnd, Z)));
    }
    if (cmpii(nsp, mului(bnd, Z)) < 0) break; /* SUCCESS */

    /* Failed with the precomputed or supplied value */
    t++; if (t == d) { delta++; t = 1; }
    if (DEBUGLEVEL >= 2)
      fprintferr("Increasing dim, delta = %d t = %d\n", delta, t);
  }
  bnd = itos(divii(nsp, Z)) + 1;

  while (!signe(short_pol[dim])) dim--;

  R = cgetg(dim + 2, t_POL); R[1] = P[1];
  for (j = 1; j <= dim; j++)
    gel(R,j+1) = diviiexact(gel(short_pol,j), Xpowers[j-1]);
  gel(R,2) = subii(gel(R,2), mului(bnd - 1, N0));

  sol = cgetg(1, t_VEC);
  for (i = -bnd + 1; i < bnd; i++)
  {
    r = nfrootsQ(R);
    if (DEBUGLEVEL >= 2) fprintferr("Roots: %Ps\n", r);

    for (j = 1; j < lg(r); j++)
    {
      z = gel(r,j);
      tst = gcdii(FpX_eval(P, z, N), N);

      if (cmpii(tst, B) >= 0) /* We have found a factor of N >= B */
      {
	for (l = 1; l < lg(sol) && !equalii(z, gel(sol,l)); l++) /*empty*/;
	if (l == lg(sol)) sol = shallowconcat(sol, z);
      }
    }
    if (i < bnd) gel(R,2) = addii(gel(R,2), Z);
  }
  return gerepilecopy(av, sol);
}

/********************************************************************/
/**                                                                **/
/**                   LINEAR & ALGEBRAIC DEPENDENCE                **/
/**                                                                **/
/********************************************************************/

static int
real_indep(GEN re, GEN im, long bitprec)
{
  GEN p1 = gsub(gmul(gel(re,1),gel(im,2)),
		gmul(gel(re,2),gel(im,1)));
  return (!gcmp0(p1) && gexpo(p1) > - bitprec);
}

GEN
lindep2(GEN x, long bit)
{
  long tx=typ(x), lx=lg(x), ly, i, j;
  pari_sp av = avma;
  GEN re, im, M;

  if (! is_vec_t(tx)) pari_err(typeer,"lindep2");
  if (lx<=2) return cgetg(1,t_VEC);
  if (bit < 0) pari_err(talker, "negative accuracy in lindep2");
  if (!bit)
  {
    bit = gprecision(x);
    if (!bit)
    {
      x = primpart(x);
      bit = 32 + gexpo(x);
    }
    else
      bit = (long)bit_accuracy_mul(bit, 0.8);
  }
  else
    bit = (long) (bit/LOG10_2);
  re = real_i(x);
  im = imag_i(x);
  /* independent over R ? */
  if (lx == 3 && real_indep(re,im,bit)) { avma = av; return cgetg(1, t_VEC); }
  if (gcmp0(im)) im = NULL;
  ly = im? lx+2: lx+1;
  M = cgetg(lx,t_MAT);
  for (i=1; i<lx; i++)
  {
    GEN c = cgetg(ly,t_COL); gel(M,i) = c;
    for (j=1; j<lx; j++) gel(c,j) = (i==j)? gen_1: gen_0;
    gel(c,lx)           = gtrunc2n(gel(re,i), bit);
    if (im) gel(c,lx+1) = gtrunc2n(gel(im,i), bit);
  }
  M = ZM_lll(M, 0.99, LLL_INPLACE);
  M = gel(M,1);
  M[0] = evaltyp(t_COL) | evallg(lx);
  return gerepilecopy(av, M);
}

static int
quazero(GEN x, long EXP)
{ return gcmp0(x) || (typ(x)==t_REAL && expo(x) < EXP); }
GEN
lindep(GEN x)
{
  GEN b, be, bn, m, qzer, re, im, RE, IM, px, py, pxy;
  long i,j, fl, lx = lg(x), n = lx-1;
  pari_sp av = avma, lim = stack_lim(av,1), av0, av1;
  long EXP, prec = gprecision(x);

  if (!prec) prec = DEFAULTPREC;
  EXP = 2*n - bit_accuracy(prec);

  if (! is_vec_t(typ(x))) pari_err(typeer,"lindep");
  if (n <= 1) return cgetg(1,t_VEC);
  x = RgC_gtofp(x, prec);
  re = real_i(x);
  im = imag_i(x);
  /* independent over R ? */
  if (n == 2 && real_indep(re,im,bit_accuracy(prec)))
    { avma = av; return cgetg(1, t_VEC); }
  if (EXP > -10) pari_err(precer,"lindep");

  qzer = cgetg(lx, t_VECSMALL);
  b = matid(n);
  be = cgetg(lx, t_MAT);
  bn = cgetg(lx, t_COL);
  m = cgetg(lx, t_VEC); /* vector of columns of increasing length */
  for (i=1; i<=n; i++)
  {
    GEN cb = cgetg(lx,t_COL), cm = cgetg(i, t_COL);
    gel(bn,i) = cgetr(prec+1);
    gel(be,i) = cb;
    gel(m,i) = cm;
    for (j=1; j<i ; j++) gel(cm,j) = cgetr(prec+1);
    for (j=1; j<=n; j++) gel(cb,j) = cgetr(prec+1);
  }
  px = RgV_dotsquare(re);
  py = RgV_dotsquare(im); pxy = RgV_dotproduct(re,im);
  if (quazero(px,EXP)) { re = im; px = py; fl = 1; }
  else {
    GEN u = mpsub(mpmul(px,py), gsqr(pxy));
    fl = quazero(u,EXP);
    if (!fl) {
      RE = RgC_Rg_div(re, u);
      IM = RgC_Rg_div(im, u);
    }
  }
  if (fl) {
    RE = RgC_Rg_div(re, px);
    IM = NULL;
  }
  av0 = av1 = avma;
  for (i=1; i<=n; i++,avma = av1)
  {
    GEN bei = gel(be,i);
    GEN C, d = RgV_dotproduct(gel(b,i), re);
    if (fl)
      C = RgC_Rg_mul(RE, d);
    else
    {
      GEN w, v, u = RgV_dotproduct(gel(b,i), im);
      v = gsub(gmul(py,d), gmul(pxy,u));
      w = gsub(gmul(px,u), gmul(pxy,d));
      C = RgC_add(RgC_Rg_mul(RE,v), RgC_Rg_mul(IM,w));
    }
    C = RgC_sub(gel(b,i), C);
    for (j=1; j<i; j++)
    {
      GEN mij = gmael(m,i,j);
      if (qzer[j]) affrr(gel(bn,j), mij);
      else
      {
        GEN u = RgV_dotproduct(gel(b,i), gel(be,j));
	mpaff(mpdiv(u, gel(bn,j)), mij);
	C = RgC_sub(C, RgC_Rg_mul(gel(be,j), mij));
      }
    }
    for (j=1; j<=n; j++) affrr(gel(C,j), gel(bei,j));
    affrr(RgV_dotsquare(bei), gel(bn,i));
    qzer[i] = quazero(gel(bn,i),EXP);
  }
  while (qzer[n])
  {
    GEN c1, f, r, em = gel(bn,1);
    long e, k;
    j = 1;
    for (i=2; i<n; i++)
    {
      GEN u = shiftr(gel(bn,i),i);
      if (cmprr(u,em) > 0) { em = u; j = i; }
    }
    i = j; k = i+1;
    avma = av1; r = grndtoi(gmael(m,k,i), &e);
    if (e >= 0) pari_err(precer,"lindep");
    togglesign_safe(&r);
    ZC_lincomb1_inplace(gel(b,k), gel(b,i), r);
    swap(gel(b,k), gel(b,i));
    av1 = avma;
    f = addir(r, gmael(m,k,i));
    for (j=1; j<i; j++)
      if (!qzer[j])
      {
        GEN mij = gmael(m,i,j), mkj = gmael(m,k,j);
	GEN u = mpadd(mkj, mulir(r,mij));
	affrr(mij, mkj);
	affrr(u,   mij);
      }
    c1 = addrr(gel(bn,k), mulrr(gsqr(f),gel(bn,i)));
    if (!quazero(c1,EXP))
    {
      GEN c2 = divrr(mulrr(gel(bn,i),f),c1);
      GEN c3 = divrr(gel(bn,k),c1);
      affrr(c2, gmael(m,k,i));
      mulrrz(c3,gel(bn,i), gel(bn,k));
      qzer[k] = quazero(gel(bn,k),EXP);
      affrr(c1, gel(bn,i));
      qzer[i] = 0;
      for (j=i+2; j<=n; j++)
      {
	GEN mjk = gmael(m,j,k), mji = gmael(m,j,i);
        GEN u = addrr(mulrr(mjk,c3), mulrr(mji,c2));
	affrr(subrr(mji,mulrr(f,mjk)), mjk);
	affrr(u, mji);
      }
    }
    else
    {
      affrr(gel(bn,i), gel(bn,k));
      qzer[k] = qzer[i];
      affrr(c1, gel(bn,i));
      qzer[i] = 1;
      for (j=i+2; j<=n; j++) affrr(gmael(m,j,i), gmael(m,j,k));
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"lindep");
      b = gerepilecopy(av0, b);
      av1 = avma;
    }
  }
  return gerepileupto(av, RgM_solve(shallowtrans(b), col_ei(n,n)));
}

/* PSLQ Programs */

typedef struct {
  long vmind, t12, t1234, reda, fin;
  long ct;
  pari_timer t;
} pslq_timer;

/* WARNING: for double ** matrices, A[i] is the i-th ROW of A */
typedef struct {
  double *y, **H, **A, **B;
  double *W; /* scratch space */
  long n;
  pslq_timer *T;
} pslqL2_M;

typedef struct {
  GEN y, H, A, B;
  long n, EXP;
  int flreal;
  pslq_timer *T;
} pslq_M;

void
init_dalloc(void)
{ /* correct alignment for dalloc */
  (void)new_chunk((avma % sizeof(double)) / sizeof(long));
}

double *
dalloc(size_t n)
{
  return (double*)new_chunk(n / sizeof(long));
}

char *
stackmalloc(size_t N)
{
  long n = nchar2nlong(N);
  return (char*)new_chunk(n);
}

static double
conjd(double x) { return x; }

static double
sqrd(double a) { return a*a; }

static void
redall(pslq_M *M, long i, long jsup)
{
  long j, k, n = M->n;
  GEN t,b;
  GEN A = M->A, B = M->B, H = M->H, y = M->y;
  const GEN Bi = gel(B,i);

  for (j=jsup; j>=1; j--)
  {
    pari_sp av = avma;
    t = round_safe( gdiv(gcoeff(H,i,j), gcoeff(H,j,j)) );
    if (!t || gcmp0(t)) { avma = av; continue; }

    b = gel(B,j);
    gel(y,j) = gadd(gel(y,j), gmul(t,gel(y,i)));
    for (k=1; k<=j; k++)
      gcoeff(H,i,k) = gsub(gcoeff(H,i,k), gmul(t,gcoeff(H,j,k)));
    for (k=1; k<=n; k++)
    {
      gcoeff(A,i,k) = gsub(gcoeff(A,i,k), gmul(t,gcoeff(A,j,k)));
      gel(b,k) = gadd(gel(b,k), gmul(t,gel(Bi,k)));
    }
  }
}

static void
redallbar(pslqL2_M *Mbar, long i, long jsup)
{
  long j, k, n = Mbar->n;
  double t;
  double *hi = Mbar->H[i], *ai = Mbar->A[i], *hj, *aj;

#ifdef DEBUGPSLQ
fprintferr("%ld:\n==\n",i);
#endif
  for (j=jsup; j>=1; j--)
  {
    hj = Mbar->H[j];
    t = floor(0.5 + hi[j] / hj[j]);
    if (!t) continue;
#ifdef DEBUGPSLQ
fprintferr("%15.15e ",t);
#endif
    aj = Mbar->A[j];

    Mbar->y[j] += t * Mbar->y[i];
    for (k=1; k<=j; k++) hi[k] -= t * hj[k];
    for (k=1; k<=n; k++) {
      ai[k]         -= t * aj[k];
      Mbar->B[k][j] += t * Mbar->B[k][i];
    }
#ifdef DEBUGPSLQ
fprintferr("  %ld:\n",j); dprintmat(Mbar->H,n,n-1);
#endif
  }
}

static long
vecabsminind(GEN v)
{
  long l = lg(v), m = 1, i;
  GEN t, la = mpabs(gel(v,1));
  for (i=2; i<l; i++)
  {
    t = mpabs(gel(v,i));
    if (mpcmp(t,la) < 0) { la = t; m = i; }
  }
  return m;
}

static long
vecmaxind(GEN v)
{
  long l = lg(v), m = 1, i;
  GEN t, la = gel(v,1);
  for (i=2; i<l; i++)
  {
    t = gel(v,i);
    if (mpcmp(t,la) > 0) { la = t; m = i; }
  }
  return m;
}

static long
vecmaxindbar(double *v, long n)
{
  long m = 1, i;
  double la = v[1];
  for (i=2; i<=n; i++)
    if (v[i] > la) { la = v[i]; m = i; }
  return m;
}

static GEN
maxnorml2(pslq_M *M)
{
  long n = M->n, i, j;
  GEN ma = gen_0, s;

  for (i=1; i<=n; i++)
  {
    s = gen_0;
    for (j=1; j<n; j++) s = gadd(s, gnorm(gcoeff(M->H,i,j)));
    if (gcmp(ma,s) < 0) ma = s;
  }
  return sqrtr(gtofp(ma, DEFAULTPREC));
}

static void
init_timer(pslq_timer *T)
{
  T->vmind = T->t12 = T->t1234 = T->reda = T->fin = T->ct = 0;
  TIMERstart(&T->t);
}

static int
is_zero(GEN x, long e, long prec)
{
  if (gcmp0(x)) return 1;
  if (typ(x) == t_REAL)
  {
    long ex = expo(x);
    return (ex < e || (prec != 3 && lg(x) == 3 && ex < (e>>1)));
  }
  return gexpo(x) < e;
}

static GEN
init_pslq(pslq_M *M, GEN x, long *PREC)
{
  long tx = typ(x), lx = lg(x), n = lx-1, i, j, k, prec;
  GEN s1, s, sinv;

  if (! is_vec_t(tx)) pari_err(typeer,"pslq");
  /* check trivial cases */
  for (k = 1; k <= n; k++)
    if (gcmp0(gel(x,k))) return col_ei(n, k);
  if (n <= 1) return cgetg(1, t_COL);
  prec = gprecision(x) - 1; /* don't trust the last word */
  if (prec < 0)
  { /* exact components */
    pari_sp av = avma;
    GEN im, U = NULL;
    x = Q_primpart(x);
    im = imag_i(x);
    x = real_i(x); settyp(x, t_VEC);
    if (!gcmp0(im))
    {
      U = gel(extendedgcd(im),2);
      setlg(U, lg(U)-1); /* remove last column */
      x = gmul(x, U);
      if (n == 2) /* x has a single component */
	return gcmp0(gel(x,1))? gel(U,1): cgetg(1, t_COL);
    }
    x = gel(extendedgcd(x),2);
    x = gel(x,1);
    if (U) x = gmul(U, x);
    return gerepilecopy(av, x);
  }
  if (prec < DEFAULTPREC) prec = DEFAULTPREC;
  *PREC = prec;
  M->EXP = - bit_accuracy(prec) + maxss(n, 8);
  M->flreal = is_zero(imag_i(x), M->EXP, prec);
  if (!M->flreal)
    return lindep(x); /* FIXME */
  else
    x = real_i(x);

  if (DEBUGLEVEL>=3) init_timer(M->T);
  x = RgC_gtofp(x, prec); settyp(x,t_VEC);
  M->n = n;
  M->A = matid(n);
  M->B = matid(n);
  s1 = cgetg(lx,t_VEC); gel(s1,n) = gnorm(gel(x,n));
  s  = cgetg(lx,t_VEC); gel(s,n) = gabs(gel(x,n),prec);
  for (k=n-1; k>=1; k--)
  {
    gel(s1,k) = gadd(gel(s1,k+1), gnorm(gel(x,k)));
    gel(s,k) = gsqrt(gel(s1,k), prec);
  }
  sinv = ginv(gel(s,1));
  s    = gmul(sinv,s);
  M->y = gmul(sinv, x);
  M->H = cgetg(n,t_MAT);
  for (j=1; j<n; j++)
  {
    GEN d, c = cgetg(lx,t_COL);

    gel(M->H,j) = c;
    for (i=1; i<j; i++) gel(c,i) = gen_0;
    gel(c,j) = gdiv(gel(s,j+1),gel(s,j));
    d = gneg( gdiv(gel(M->y,j), gmul(gel(s,j),gel(s,j+1)) ));
    for (i=j+1; i<=n; i++) gel(c,i) = gmul(gconj(gel(M->y,i)), d);
  }
  for (i=2; i<=n; i++) redall(M, i, i-1);
  return NULL;
}

static void
SWAP(pslq_M *M, long m)
{
  long j, n = M->n;
  swap(gel(M->y,m), gel(M->y,m+1));
  swap(gel(M->B,m), gel(M->B,m+1));
  for (j=1; j<=n; j++) swap(gcoeff(M->A,m,j), gcoeff(M->A,m+1,j));
  for (j=1; j<n;  j++) swap(gcoeff(M->H,m,j), gcoeff(M->H,m+1,j));
}

static void
SWAPbar(pslqL2_M *M, long m)
{
  long j, n = M->n;
  dswap(M->y[m], M->y[m+1]);
  pdswap(M->A[m], M->A[m+1]);
  pdswap(M->H[m], M->H[m+1]);
  for (j=1; j<=n; j++) dswap(M->B[j][m], M->B[j][m+1]);
}

static GEN
one_step_gen(pslq_M *M, GEN tabga, long prec)
{
  GEN H = M->H, p1;
  long n = M->n, i, m;

  p1 = cgetg(n,t_VEC);
  for (i=1; i<n; i++) gel(p1,i) = gmul(gel(tabga,i), gabs(gcoeff(H,i,i),prec));
  m = vecmaxind(p1);
  if (DEBUGLEVEL>3) M->T->vmind += TIMER(&M->T->t);
  SWAP(M, m);
  if (m <= n-2)
  {
    GEN tinv, t3, t4, t1c, t2c, t1 = gcoeff(H,m,m), t2 = gcoeff(H,m,m+1);
    tinv = ginv( gsqrt(gadd(gnorm(t1), gnorm(t2)), prec) );
    t1 = gmul(t1, tinv);
    t2 = gmul(t2, tinv);
    if (M->flreal) { t1c = t1; t2c = t2; }
    else           { t1c = gconj(t1); t2c = gconj(t2); }
    if (DEBUGLEVEL>3) M->T->t12 += TIMER(&M->T->t);
    for (i=m; i<=n; i++)
    {
      t3 = gcoeff(H,i,m);
      t4 = gcoeff(H,i,m+1);
      gcoeff(H,i,m) = gadd(gmul(t1c,t3), gmul(t2c,t4));
      gcoeff(H,i,m+1) = gsub(gmul(t1, t4), gmul(t2, t3));
    }
    if (DEBUGLEVEL>3) M->T->t1234 += TIMER(&M->T->t);
  }
  for (i=1; i<n; i++)
    if (is_zero(gcoeff(H,i,i), M->EXP, prec)) {
      m = vecabsminind(M->y); return gel(M->B,m);
    }
  for (i=m+1; i<=n; i++) redall(M, i, minss(i-1,m+1));

  if (DEBUGLEVEL>3) M->T->reda += TIMER(&M->T->t);
  if (gexpo(M->A) >= -M->EXP) return ginv(maxnorml2(M));
  m = vecabsminind(M->y);
  if (is_zero(gel(M->y,m), M->EXP, prec)
   && gexpo(M->y) - gexpo(gel(M->y,m)) > 20)
    return gel(M->B,m);

  if (DEBUGLEVEL>2)
  {
    if (DEBUGLEVEL>3) M->T->fin += TIMER(&M->T->t);
    M->T->ct++;
    if ((M->T->ct&0xff) == 0)
    {
      if (DEBUGLEVEL == 3)
	fprintferr("time for ct = %ld : %ld\n",M->T->ct, TIMER(&M->T->t));
      else
	fprintferr("time [max,t12,loop,reds,fin] = [%ld, %ld, %ld, %ld, %ld]\n",
		   M->T->vmind, M->T->t12, M->T->t1234, M->T->reda, M->T->fin);
    }
  }
  return NULL; /* nothing interesting */
}

static GEN
get_tabga(int flreal, long n, long prec)
{
  GEN ga = sqrtr( flreal? divru(stor(4, prec), 3): stor(2, prec) );
  GEN tabga = cgetg(n,t_VEC);
  long i;
  gel(tabga,1) = ga;
  for (i = 2; i < n; i++) gel(tabga,i) = gmul(gel(tabga,i-1),ga);
  return tabga;
}

GEN
pslq(GEN x)
{
  GEN tabga, p1;
  long prec;
  pari_sp av0 = avma, lim = stack_lim(av0,1), av;
  pslq_M M;
  pslq_timer T; M.T = &T;

  p1 = init_pslq(&M, x, &prec);
  if (p1) return p1;

  tabga = get_tabga(M.flreal, M.n, prec);
  av = avma;
  if (DEBUGLEVEL>=3) msgTIMER(&M.T->t, "Initialization");
  for (;;)
  {
    if ((p1 = one_step_gen(&M, tabga, prec)))
      return gerepilecopy(av0, p1);

    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"pslq");
      gerepileall(av,4,&M.y,&M.H,&M.A,&M.B);
    }
  }
}

/* W de longueur n-1 */

static double
dnorml2(double *W, long n, long row)
{
  long i;
  double s = 0.;

  for (i=row; i<n; i++) s += W[i]*W[i];
  return s;
}

/* Hbar *= Pbar */
static void
dmatmul(pslqL2_M *Mbar, double **Pbar, long row)
{
  const long n = Mbar->n; /* > row */
  long i, j, k;
  double s, *W = Mbar->W, **H = Mbar->H;

  for (i = row; i <= n; i++)
  {
    for (j = row; j < n; j++)
    {
      k = row; s = H[i][k] * Pbar[k][j];
      for ( ; k < n; k++) s += H[i][k] * Pbar[k][j];
      W[j] = s;
    }
    for (j = row; j < n; j++) H[i][j] = W[j];
  }
}

/* compute n-1 x n-1 matrix Pbar */
static void
dmakep(pslqL2_M *Mbar, double **Pbar, long row)
{
  long i, j, n = Mbar->n;
  double pro, nc, *C = Mbar->H[row], *W = Mbar->W;

  nc = sqrt(dnorml2(C,n,row));
  W[row] = (C[row] < 0) ? C[row] - nc : C[row] + nc;
  for (i=row; i<n; i++) W[i] = C[i];
  pro = -2.0 / dnorml2(W, n, row);
      /* must have dnorml2(W,n,row) = 2*nc*(nc+fabs(C[1])) */
  for (j=row; j<n; j++)
  {
    for (i=j+1; i<n; i++)
      Pbar[j][i] = Pbar[i][j] = pro * W[i] * W[j];
    Pbar[j][j] = 1.0 + pro * W[j] * W[j];
  }
}

static void
dLQdec(pslqL2_M *Mbar, double **Pbar)
{
  long row, j, n = Mbar->n;

  for (row=1; row<n; row++)
  {
    dmakep(Mbar, Pbar, row);
    dmatmul(Mbar, Pbar, row);
    for (j=row+1; j<n; j++) Mbar->H[row][j] = 0.;
  }
}

#ifdef DEBUGPSLQ
static void
dprintvec(double *V, long m)
{
  long i;
  fprintferr("[");
  for (i=1; i<m; i++) fprintferr("%15.15e, ",V[i]);
  fprintferr("%15.15e]\n",V[m]); pari_flush();
}

static void
dprintmat(double **M, long r, long c)
{
  long i, j;
  fprintferr("[");
  for (i=1; i<r; i++)
  {
    for (j=1; j<c; j++) fprintferr("%15.15e, ",M[i][j]);
    fprintferr("%15.15e;\n ",M[i][c]);
  }
  for (j=1; j<c; j++) fprintferr("%15.15e, ",M[r][j]);
  fprintferr("%15.15e]\n",M[r][c]); pari_flush();
}
#endif

static long
initializedoubles(pslqL2_M *Mbar, pslq_M *M, long prec)
{
  long i, j, n = Mbar->n;
  GEN ypro;
  pari_sp av = avma;

  ypro = gdiv(M->y, vecmax(gabs(M->y,prec)));
  for (i=1; i<=n; i++)
  {
    if (gexpo(gel(ypro,i)) < -0x3ff) return 0;
    Mbar->y[i] = rtodbl(gel(ypro,i));
  }
  avma = av;
  for (j=1; j<=n; j++)
    for (i=1; i<=n; i++)
    {
      if (i==j) Mbar->A[i][j] = Mbar->B[i][j] = 1.;
      else      Mbar->A[i][j] = Mbar->B[i][j] = 0.;
      if (j < n)
      {
	GEN h = gcoeff(M->H,i,j);
	if (!gcmp0(h) && labs(gexpo(h)) > 0x3ff) return 0;
	Mbar->H[i][j] = rtodbl(h);
      }
    }
  return 1;
}

/* T(arget) := S(ource) */
static void
storeprecdoubles(pslqL2_M *T, pslqL2_M *S)
{
  long n = T->n, i, j;

  for (i=1; i<=n; i++)
  {
    for (j=1; j<n; j++)
    {
      T->H[i][j] = S->H[i][j];
      T->A[i][j] = S->A[i][j];
      T->B[i][j] = S->B[i][j];
    }
    T->A[i][n] = S->A[i][n];
    T->B[i][n] = S->B[i][n];
    T->y[i] = S->y[i];
  }
}

static long
checkentries(pslqL2_M *Mbar)
{
  long n = Mbar->n, i, j;
  double *p1, *p2;

  for (i=1; i<=n; i++)
  {
    if (dblexpo(Mbar->y[i]) < -46) return 0;
    p1 = Mbar->A[i];
    p2 = Mbar->B[i];
    for (j=1; j<=n; j++)
      if (dblexpo(p1[j]) > 43 || dblexpo(p2[j]) > 43) return 0;
  }
  return 1;
}

static long
applybar(pslq_M *M, pslqL2_M *Mbar, GEN Abargen, GEN Bbargen)
{
  long n = Mbar->n, i, j;
  double *p1, *p2;

  for (i=1; i<=n; i++)
  {
    p1 = Mbar->A[i];
    p2 = Mbar->B[i];
    for (j=1; j<=n; j++)
    {
      if (dblexpo(p1[j]) >= 52 || dblexpo(p2[j]) >= 52) return 0;
      gcoeff(Abargen,i,j) = stoi((long)floor(p1[j]));
      gcoeff(Bbargen,i,j) = stoi((long)floor(p2[j]));
    }
  }
  M->y = gmul(M->y, Bbargen);
  M->B = gmul(M->B, Bbargen);
  M->A = gmul(Abargen, M->A);
  M->H = gmul(Abargen, M->H); return 1;
}

static GEN
checkend(pslq_M *M, long prec)
{
  long i, m, n = M->n;

  for (i=1; i<=n-1; i++)
    if (is_zero(gcoeff(M->H,i,i), M->EXP, prec))
    {
      m = vecabsminind(M->y);
      return gel(M->B,m);
    }
  if (gexpo(M->A) >= -M->EXP)
    return ginv( maxnorml2(M) );
  m = vecabsminind(M->y);
  if (is_zero(gel(M->y,m), M->EXP, prec)) return gel(M->B,m);
  return NULL;
}

GEN
pslqL2(GEN x)
{
  GEN Abargen, Bbargen, tabga, p1;
  long lx = lg(x), n = lx-1, i, m, ctpro, flreal, flit, prec;
  pari_sp av0 = avma, lim = stack_lim(av0,1), av;
  double *tabgabar, gabar, tinvbar, t1bar, t2bar, t3bar, t4bar;
  double **Pbar, **Abar, **Bbar, **Hbar;
  pslqL2_M Mbar, Mbarst;
  pslq_M M;
  pslq_timer T; M.T = &T;

  p1 = init_pslq(&M, x, &prec);
  if (p1) return p1;

  flreal = M.flreal;
  tabga = get_tabga(flreal, n, prec);
  Abargen = matid(n);
  Bbargen = matid(n);

  Mbarst.n = Mbar.n = n;
  Mbar.A = Abar = (double**)new_chunk(n+1);
  Mbar.B = Bbar = (double**)new_chunk(n+1);
  Mbar.H = Hbar = (double**)new_chunk(n+1);
  Mbarst.A = (double**)new_chunk(n+1);
  Mbarst.B = (double**)new_chunk(n+1);
  Mbarst.H = (double**)new_chunk(n+1);
  Pbar   = (double**)new_chunk(n);

  tabgabar = dalloc((n+1)*sizeof(double));
  Mbar.y = dalloc((n+1)*sizeof(double));
  Mbarst.y = dalloc((n+1)*sizeof(double));

  Mbar.W = dalloc((n+1)*sizeof(double));
  for (i=1; i< n; i++)  Pbar[i] = dalloc((n+1)*sizeof(double));
  for (i=1; i<=n; i++)  Abar[i] = dalloc((n+1)*sizeof(double));
  for (i=1; i<=n; i++)  Bbar[i] = dalloc((n+1)*sizeof(double));
  for (i=1; i<=n; i++)  Hbar[i] = dalloc(n*sizeof(double));
  for (i=1; i<=n; i++) Mbarst.A[i] = dalloc((n+1)*sizeof(double));
  for (i=1; i<=n; i++) Mbarst.B[i] = dalloc((n+1)*sizeof(double));
  for (i=1; i<=n; i++) Mbarst.H[i] = dalloc(n*sizeof(double));

  gabar = gtodouble(gel(tabga,1)); tabgabar[1] = gabar;
  for (i=2; i<n; i++) tabgabar[i] = tabgabar[i-1]*gabar;

  av = avma;
  if (DEBUGLEVEL>=3) msgTIMER(&M.T->t, "Initialization");
RESTART:
  flit = initializedoubles(&Mbar, &M, prec);
  storeprecdoubles(&Mbarst, &Mbar);
  if (flit) dLQdec(&Mbar, Pbar);
  ctpro = 0;
  for (;;)
  {
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"pslq");
      gerepileall(av,4,&M.y,&M.H,&M.A,&M.B);
    }
    if (flit)
    {
      ctpro++;
      for (i=1; i<n; i++) Mbar.W[i] = tabgabar[i]*fabs(Hbar[i][i]);
      m = vecmaxindbar(Mbar.W, n-1);
      SWAPbar(&Mbar, m);
      if (m <= n-2)
      {
	tinvbar = 1.0 / sqrt(sqrd(Hbar[m][m]) + sqrd(Hbar[m][m+1]));
	t1bar = tinvbar*Hbar[m][m];
	t2bar = tinvbar*Hbar[m][m+1];
	if (DEBUGLEVEL>=4) T.t12 += TIMER(&M.T->t);
	for (i=m; i<=n; i++)
	{
	  t3bar = Hbar[i][m];
	  t4bar = Hbar[i][m+1];
	  if (flreal)
	    Hbar[i][m] = t1bar*t3bar + t2bar*t4bar;
	  else
	    Hbar[i][m] = conjd(t1bar)*t3bar + conjd(t2bar)*t4bar;
	  Hbar[i][m+1] = t1bar*t4bar - t2bar*t3bar;
	}
	if (DEBUGLEVEL>=4) T.t1234 += TIMER(&M.T->t);
      }

      flit = checkentries(&Mbar);
      if (flit)
      {
	storeprecdoubles(&Mbarst, &Mbar);
	for (i=m+1; i<=n; i++) redallbar(&Mbar, i, minss(i-1,m+1));
      }
      else
      {
	if (applybar(&M, &Mbar, Abargen,Bbargen))
	{
	  if ( (p1 = checkend(&M, prec)) ) return gerepilecopy(av0, p1);
	  goto RESTART;
	}
	else
	{
	  if (ctpro == 1) goto DOGEN;
	  storeprecdoubles(&Mbar, &Mbarst); /* restore */
	  if (! applybar(&M, &Mbar, Abargen,Bbargen)) pari_err(bugparier,"pslqL2");
	  if ( (p1 = checkend(&M, prec)) ) return gerepilecopy(av0, p1);
	  goto RESTART;
	}
      }
    }
    else
    {
DOGEN:
      if ((p1 = one_step_gen(&M, tabga, prec)))
	return gerepilecopy(av, p1);
    }
  }
}

/* x is a vector of elts of a p-adic field */
GEN
plindep(GEN x)
{
  long i, j, prec = LONG_MAX, nx = lg(x)-1, v;
  pari_sp av = avma;
  GEN p = NULL, pn,p1,m,a;

  if (nx < 2) return cgetg(1,t_VEC);
  for (i=1; i<=nx; i++)
  {
    p1 = gel(x,i);
    if (typ(p1) != t_PADIC) continue;

    j = precp(p1); if (j < prec) prec = j;
    if (!p) p = gel(p1,2);
    else if (!equalii(p, gel(p1,2)))
      pari_err(talker,"inconsistent primes in plindep");
  }
  if (!p) pari_err(talker,"not a p-adic vector in plindep");
  v = ggval(x,p); pn = powiu(p,prec);
  if (v != 0) x = gmul(x, powis(p, -v));
  x = RgV_to_FpV(x, pn);

  a = negi(gel(x,1));
  m = cgetg(nx,t_MAT);
  for (i=1; i<nx; i++)
  {
    GEN c = zerocol(nx);
    gel(c,1+i) = a;
    gel(c,1) = gel(x,i+1);
    gel(m,i) = c;
  }
  m = ZM_lll(ZM_hnfmodid(m, pn), 0.99, LLL_INPLACE);
  return gerepilecopy(av, gel(m,1));
}

GEN
lindep0(GEN x,long bit)
{
  long i, tx = typ(x);
  if (! is_vec_t(tx) && tx != t_MAT) pari_err(typeer,"lindep");
  for (i = 1; i < lg(x); i++)
    if (typ(gel(x,i)) == t_PADIC) return plindep(x);
  switch (bit)
  {
    case -1: return lindep(x);
    case -2: return deplin(x);
    case -3: return pslq(x);
    case -4: return pslqL2(x);
    default: return lindep2(x, bit);
  }
}

GEN
algdep0(GEN x, long n, long bit)
{
  long tx = typ(x), i;
  pari_sp av;
  GEN y;

  if (! is_scalar_t(tx)) pari_err(typeer,"algdep0");
  if (tx==t_POLMOD) { y = gcopy(gel(x,1)); setvarn(y,0); return y; }
  if (gcmp0(x)) return pol_x(0);
  if (n <= 0)
  {
    if (!n) return gen_1;
    pari_err(talker,"negative polynomial degree in algdep");
  }

  av = avma; y = cgetg(n+2,t_COL);
  gel(y,1) = gen_1;
  gel(y,2) = x; /* n >= 1 */
  for (i=3; i<=n+1; i++) gel(y,i) = gmul(gel(y,i-1),x);
  if (typ(x) == t_PADIC)
    y = plindep(y);
  else
  {
    y = lindep0(y, bit);
    if (typ(y) == t_REAL) return gerepileupto(av, y);
  }
  if (lg(y) < 2) pari_err(talker,"higher degree than expected in algdep");
  y = RgV_to_RgX(y, 0);
  if (gsigne(leading_term(y)) > 0) return gerepilecopy(av, y);
  return gerepileupto(av, RgX_neg(y));
}

GEN
algdep(GEN x, long n)
{
  return algdep0(x,n,0);
}

/********************************************************************/
/**                                                                **/
/**                              MINIM                             **/
/**                                                                **/
/********************************************************************/
void
minim_alloc(long n, double ***q, GEN *x, double **y,  double **z, double **v)
{
  long i, s;

  *x = cgetg(n, t_VECSMALL);
  *q = (double**) new_chunk(n);
  s = n * sizeof(double);
  init_dalloc();
  *y = dalloc(s);
  *z = dalloc(s);
  *v = dalloc(s);
  for (i=1; i<n; i++) (*q)[i] = dalloc(s);
}

/* If V depends linearly from the columns of the matrix, return 0.
 * Otherwise, update INVP and L and return 1. No GC. */
static int
addcolumntomatrix(GEN V, GEN invp, GEN L)
{
  GEN a = RgM_zc_mul(invp,V);
  long i,j,k, n = lg(invp);

  if (DEBUGLEVEL>6)
  {
    fprintferr("adding vector = %Ps\n",V);
    fprintferr("vector in new basis = %Ps\n",a);
    fprintferr("list = %Ps\n",L);
    fprintferr("base change matrix =\n%Ps\n", invp);
  }
  k = 1; while (k<n && (L[k] || gcmp0(gel(a,k)))) k++;
  if (k == n) return 0;
  L[k] = 1;
  for (i=k+1; i<n; i++) gel(a,i) = gdiv(gneg_i(gel(a,i)),gel(a,k));
  for (j=1; j<=k; j++)
  {
    GEN c = gel(invp,j), ck = gel(c,k);
    if (gcmp0(ck)) continue;
    gel(c,k) = gdiv(ck, gel(a,k));
    if (j==k)
      for (i=k+1; i<n; i++)
	gel(c,i) = gmul(gel(a,i), ck);
    else
      for (i=k+1; i<n; i++)
	gel(c,i) = gadd(gel(c,i), gmul(gel(a,i), ck));
  }
  return 1;
}

/* Minimal vectors for the integral definite quadratic form: a.
 * Result u:
 *   u[1]= Number of vectors of square norm <= BORNE
 *   u[2]= maximum norm found
 *   u[3]= list of vectors found (at most STOCKMAX)
 *
 *  If BORNE = gen_0: Minimal non-zero vectors.
 *  flag = min_ALL,   as above
 *  flag = min_FIRST, exits when first suitable vector is found.
 *  flag = min_PERF,  only compute rank of the family of v.v~ (v min.)
 *  flag = min_VECSMALL, return a t_VECSMALL of (half) the number of vectors for each norm
 *  flag = min_VECSMALL2, same but count only vectors with even norm, and shift the answer
 */
static GEN
minim0(GEN a, GEN BORNE, GEN STOCKMAX, long flag)
{
  GEN x,res,p1,u,r,L,gnorme,invp,V;
  long n = lg(a), i, j, k, s, maxrank;
  pari_sp av0 = avma, av1, av, lim;
  double p,maxnorm,BOUND,*v,*y,*z,**q;
  const double eps = 0.0001;
  int stockall = 0;

  if (!BORNE) BORNE = gen_0;
  else BORNE = gfloor(BORNE);
  if (!STOCKMAX) stockall = 1;
  else if (typ(STOCKMAX) != t_INT) pari_err(typeer, "minim0");
  if (typ(a) != t_MAT) pari_err(typeer,"minim0");

  maxrank = 0; res = V = invp = NULL; /* gcc -Wall */
  switch(flag)
  {
    case min_FIRST:
      if (gcmp0(BORNE)) pari_err(talker,"bound = 0 in minim2");
      res = cgetg(3,t_VEC); break;
    case min_ALL: res = cgetg(4,t_VEC); break;
    case min_PERF: break;
    case min_VECSMALL:
    case min_VECSMALL2:
      maxrank = itos(BORNE);
      if (maxrank <= 0) return cgetg(1, t_VECSMALL);

      res = const_vecsmall(maxrank, 0);
      if (flag == min_VECSMALL2) BORNE = shifti(BORNE,1);
      if (gcmp0(BORNE)) return res;
      break;
    default: pari_err(flagerr, "minim0");
  }
  if (n == 1)
  {
    switch(flag)
    {
      case min_FIRST: avma=av0; return cgetg(1,t_VEC);
      case min_VECSMALL:
      case min_VECSMALL2: return res;
      case min_PERF:  avma=av0; return gen_0;
    }
    gel(res,1) = gel(res,2) = gen_0;
    gel(res,3) = cgetg(1,t_MAT); return res;
  }

  av = avma;
  minim_alloc(n, &q, &x, &y, &z, &v);
  av1 = avma;

  u = lllgramint(a);
  if (lg(u) != n) pari_err(talker,"not a definite form in minim0");
  a = qf_apply_ZM(a,u);

  n--;
  a = RgM_gtofp(a, DEFAULTPREC);
  r = qfgaussred_positive(a);
  if (!r) pari_err(precer, "minim0");
  for (j=1; j<=n; j++)
  {
    v[j] = rtodbl(gcoeff(r,j,j));
    for (i=1; i<j; i++) q[i][j] = rtodbl(gcoeff(r,i,j));
  }

  if (flag==min_PERF || gcmp0(BORNE))
  {
    double c;
    p = rtodbl(gcoeff(a,1,1));
    for (i=2; i<=n; i++) { c = rtodbl(gcoeff(a,i,i)); if (c < p) p = c; }
    BORNE = roundr(dbltor(p));
    maxnorm = -1.; /* don't update maxnorm */
  }
  else
  {
    p = gtodouble(BORNE);
    maxnorm = 0.;
  }
  BOUND = p * (1 + eps);
  if (BOUND == p) pari_err(precer, "minim0");

  switch(flag)
  {
    case min_ALL:
      maxrank = stockall? 200: itos(STOCKMAX);
      if (maxrank < 0) pari_err(talker,"negative number of vectors in minim0");
      L = new_chunk(1+maxrank);
      break;
    case min_PERF:
      BORNE = gerepileupto(av1,BORNE);
      maxrank = (n*(n+1)) >> 1;
      L = const_vecsmall(maxrank, 0);
      V = cgetg(1+maxrank, t_VECSMALL);
  }

  s = 0; av1 = avma; lim = stack_lim(av1,1);
  k = n; y[n] = z[n] = 0;
  x[n] = (long)sqrt(BOUND/v[n]);
  if (flag == min_PERF) invp = matid(maxrank);
  for(;;x[1]--)
  {
    do
    {
      if (k>1)
      {
	long l = k-1;
	z[l] = 0;
	for (j=k; j<=n; j++) z[l] += q[l][j]*x[j];
	p = (double)x[k] + z[k];
	y[l] = y[k] + p*p*v[k];
	x[l] = (long)floor(sqrt((BOUND-y[l])/v[l])-z[l]);
	k = l;
      }
      for(;;)
      {
	p = (double)x[k] + z[k];
	if (y[k] + p*p*v[k] <= BOUND) break;
	k++; x[k]--;
      }
    }
    while (k > 1);
    if (! x[1] && y[1]<=eps) break;

    p = (double)x[1] + z[1]; p = y[1] + p*p*v[1]; /* norm(x) */
    if (maxnorm >= 0)
    {
      if (flag == min_FIRST)
      {
	gel(res,2) = gerepileupto(av, ZM_zc_mul(u,x));
	av = avma;
	gel(res,1) = gerepileuptoint(av, roundr(dbltor(p))); return res;
      }
      if (p > maxnorm) maxnorm = p;
    }
    else
    {
      pari_sp av2 = avma;
      gnorme = roundr(dbltor(p));
      if (gcmp(gnorme,BORNE) >= 0) avma = av2;
      else
      {
	BOUND=gtodouble(gnorme)*(1+eps); s=0;
	affii(gnorme,BORNE); avma = av1;
	if (flag == min_PERF) invp = matid(maxrank);
      }
    }
    s++;

    switch(flag)
    {
      case min_ALL:
	if (s > maxrank && stockall) /* overflow */
	{
	  long maxranknew = maxrank << 1;
	  GEN Lnew = new_chunk(1 + maxranknew);
	  for (i=1; i<=maxrank; i++) Lnew[i] = L[i];
	  L = Lnew; maxrank = maxranknew;
	}
	if (s<=maxrank)
	{
	  p1 = new_chunk(n+1); gel(L,s) = p1;
	  for (i=1; i<=n; i++) p1[i] = x[i];
	}
	break;

      case min_VECSMALL:
	{
	  ulong norm = (ulong)(p + 0.5);
	  res[norm]++;
	}
	break;

      case min_VECSMALL2:
	{
	  ulong norm = (ulong)(p + 0.5);
	  if ((norm&1) == 0) res[norm>>1]++;
	}
	break;

      case min_PERF:
      {
	long I=1;
	pari_sp av2=avma;

	for (i=1; i<=n; i++)
	  for (j=i; j<=n; j++,I++) V[I] = x[i]*x[j];
	if (! addcolumntomatrix(V,invp,L))
	{
	  if (DEBUGLEVEL>1) { fprintferr("."); flusherr(); }
	  s--; avma=av2; continue;
	}

	if (DEBUGLEVEL>1) { fprintferr("*"); flusherr(); }
	if (s == maxrank)
	{
	  if (DEBUGLEVEL>1) { fprintferr("\n"); flusherr(); }
	  avma=av0; return stoi(s);
	}

	if (low_stack(lim, stack_lim(av1,1)))
	{
	  if(DEBUGMEM>1) pari_warn(warnmem,"minim0, rank>=%ld",s);
	  invp = gerepilecopy(av1, invp);
	}
      }
    }
  }
  switch(flag)
  {
    case min_FIRST:
      avma=av0; return cgetg(1,t_VEC);
    case min_VECSMALL:
    case min_VECSMALL2:
      avma=av; return res;
    case min_PERF:
      if (DEBUGLEVEL>1) { fprintferr("\n"); flusherr(); }
      avma=av0; return stoi(s);
  }
  k = minss(s,maxrank);
  r = (maxnorm >= 0) ? roundr(dbltor(maxnorm)): BORNE;

  L[0] = evaltyp(t_MAT) | evallg(k + 1);
  for (j=1; j<=k; j++) gel(L,j) = ZM_zc_mul(u, gel(L,j));

  gerepileall(av, 2, &r, &L);
  gel(res,1) = stoi(s<<1);
  gel(res,2) = r;
  gel(res,3) = L; return res;
}

GEN
qfrep0(GEN a, GEN borne, long flag)
{
  pari_sp av = avma;
  GEN g = minim0(a, borne, gen_0, (flag & 1)? min_VECSMALL2: min_VECSMALL);
  if ((flag & 2) == 0) g = gerepileupto(av, gtovec(g));
  return g;
}

GEN
qfminim0(GEN a, GEN borne, GEN stockmax, long flag, long prec)
{
  switch(flag)
  {
    case 0: return minim0(a,borne,stockmax,min_ALL);
    case 1: return minim0(a,borne,gen_0   ,min_FIRST);
    case 2:
    {
      long maxnum = stockmax? itos(stockmax): -2;
      if (typ(a) != t_MAT) pari_err(typeer,"qfminim0");
      return fincke_pohst(a,borne,maxnum,prec,NULL);
    }
    default: pari_err(flagerr,"qfminim");
  }
  return NULL; /* not reached */
}

GEN
minim(GEN a, GEN borne, GEN stockmax)
{
  return minim0(a,borne,stockmax,min_ALL);
}

GEN
minim2(GEN a, GEN borne, GEN stockmax)
{
  return minim0(a,borne,stockmax,min_FIRST);
}

GEN
perf(GEN a)
{
  return minim0(a,gen_0,gen_0,min_PERF);
}

static GEN
clonefill(GEN S, long s, long t)
{ /* initialize to dummy values */
  GEN T = S, dummy = cgetg(1, t_STR);
  long i;
  for (i = s+1; i <= t; i++) gel(S,i) = dummy;
  S = gclone(S); if (isclone(T)) gunclone(T);
  return S;
}

INLINE void
step(GEN x, GEN y, GEN inc, long k)
{
  if (!signe(y[k]))
    gel(x,k) = addis(gel(x,k), 1); /* leading coeff > 0 */
  else
  {
    long i = inc[k];
    gel(x,k) = addis(gel(x,k), i),
    inc[k] = (i > 0)? -1-i: 1-i;
  }
}
/* q is the Gauss reduction of the quadratic form */
/* general program for positive definit quadratic forms (real coeffs).
 * Enumerate vectors whose norm is less than BORNE, minimal vectors
 * if BORNE = NULL (implies check = NULL).
 * If (check != NULL) consider only vectors passing the check, and assumes
 *   we only want the smallest possible vectors */
static GEN
smallvectors(GEN q, GEN BORNE, long maxnum, FP_chk_fun *CHECK)
{
  long N = lg(q), n = N-1, i, j, k, s, epsbit, prec, checkcnt = 1;
  pari_sp av, av1, lim;
  GEN inc, S, x, y, z, v,  eps, p1, alpha, norms;
  GEN norme1, normax1, borne1, borne2;
  GEN (*check)(void *,GEN) = CHECK? CHECK->f: NULL;
  void *data = CHECK? CHECK->data: NULL;
  long stockmax, skipfirst = CHECK? CHECK->skipfirst: 0;
  int stockall = (maxnum < 0);

  prec = gprecision(q);
  epsbit = bit_accuracy(prec) >> 1;
  eps = real2n(-epsbit, 3);
  alpha = dbltor(0.95);
  normax1 = gen_0;
  norme1 = BORNE ? BORNE: gsqr(gcoeff(q,1,1));
  borne1 = mpadd(norme1,eps);
  if (!BORNE) borne2 = mpsub(norme1,eps);
  else        borne2 = mpmul(norme1,alpha);
  if (DEBUGLEVEL>2)
    fprintferr("smallvectors looking for norm < %Ps\n",gprec_w(borne1,3));

  v = cgetg(N,t_VEC);
  inc = const_vecsmall(n, 1);

  av = avma; lim = stack_lim(av,2);
  stockmax = stockall? 200: maxnum;
  if (check) norms = cgetg(stockmax+1,t_VEC);
  S = cgetg(stockmax+1,t_VEC);
  x = cgetg(N,t_COL);
  y = cgetg(N,t_COL);
  z = cgetg(N,t_COL);
  for (i=1; i<N; i++) {
    gel(v,i) = gcoeff(q,i,i);
    gel(x,i) = gel(y,i) = gel(z,i) = gen_0;
  }

  gel(x,n) = gen_0; s = 0; k = n;
  for(;; step(x,y,inc,k)) /* main */
  {
    do
    {
      int fl = 0;
      if (k > 1)
      {
	k--;
	av1 = avma; p1 = mpmul(gcoeff(q,k,k+1),gel(x,k+1));
	for (j=k+2; j<N; j++)
	  p1 = mpadd(p1, mpmul(gcoeff(q,k,j),gel(x,j)));
	gel(z,k) = gerepileuptoleaf(av1,p1);

	av1 = avma; p1 = gsqr(mpadd(gel(x,k+1),gel(z,k+1)));
	p1 = mpadd(gel(y,k+1), mpmul(p1,gel(v,k+1)));
	gel(y,k) = gerepileuptoleaf(av1, p1);
	/* skip the [x_1,...,x_skipfirst,0,...,0] */
	if ((k <= skipfirst && !signe(y[skipfirst]))
	 || mpcmp(borne1, gel(y,k)) < 0) fl = 1;
	else
	  gel(x,k) = mpround( mpneg(gel(z,k)) );
      }
      for(;; step(x,y,inc,k))
      {
	if (!fl)
	{
	  av1 = avma;
	  p1 = mpmul(gel(v,k), gsqr(mpadd(gel(x,k), gel(z,k))));
	  i = mpcmp(mpsub(mpadd(p1,gel(y,k)), borne1), gmul2n(p1,-epsbit));
	  avma = av1; if (i <= 0) break;

	  step(x,y,inc,k);

	  av1 = avma; /* same as above */
	  p1 = mpmul(gel(v,k), gsqr(mpadd(gel(x,k), gel(z,k))));
	  i = mpcmp(mpsub(mpadd(p1,gel(y,k)), borne1), gmul2n(p1,-epsbit));
	  avma = av1; if (i <= 0) break;
	}
	fl = 0; inc[k] = 1;
	if (++k > n) goto END;
      }

      if (low_stack(lim, stack_lim(av,2)))
      {
	if(DEBUGMEM>1) pari_warn(warnmem,"smallvectors");
	if (stockmax) S = clonefill(S, s, stockmax);
	if (check) {
	  GEN dummy = cgetg(1, t_STR);
	  for (i=s+1; i<=stockmax; i++) gel(norms,i) = dummy;
	}
	gerepileall(av,check?7:6,&x,&y,&z,&normax1,&borne1,&borne2,&norms);
      }
    }
    while (k > 1);
    if (!signe(x[1]) && !signe(y[1])) continue; /* exclude 0 */

    av1 = avma; p1 = gsqr(mpadd(gel(x,1),gel(z,1)));
    norme1 = mpadd(gel(y,1), mpmul(p1, gel(v,1)));
    if (mpcmp(norme1,borne1) > 0) { avma=av1; continue; /* main */ }

    norme1 = gerepileupto(av1,norme1);
    if (check)
    {
      if (checkcnt < 5 && mpcmp(norme1, borne2) < 0)
      {
	if (!check(data,x)) { checkcnt++ ; continue; /* main */}
	if (DEBUGLEVEL>4) fprintferr("New bound: %Ps", norme1);
	borne1 = mpadd(norme1, eps);
	borne2 = mpmul(borne1, alpha);
	s = 0; checkcnt = 0;
      }
    }
    else
    {
      if (!BORNE) /* find minimal vectors */
      {
	if (mpcmp(norme1, borne2) < 0)
	{
	  borne1 = mpadd(norme1, eps);
	  borne2 = mpsub(norme1, eps);
	  s = 0;
	}
      }
      else
	if (mpcmp(norme1,normax1) > 0) normax1 = norme1;
    }

    if (++s <= stockmax)
    {
      if (check) gel(norms,s) = norme1;
      gel(S,s) = leafcopy(x);
      if (s == stockmax)
      { /* overflow */
	long stockmaxnew= (stockall && (stockmax < 10000L || maxnum == -1))
			  ? stockmax<<1 : stockmax;
	GEN Snew = cgetg(stockmaxnew + 1, t_VEC);
	if (check)
	{
	  pari_sp av2 = avma;
	  GEN per = indexsort(norms);
	  if (DEBUGLEVEL>2) fprintferr("sorting...\n");
	  for (j = 0, i = 1; i <= s; i++)
	  { /* let N be the minimal norm so far for x satisfying 'check'. Keep
	     * all elements of norm N */
	    long k = per[i];
	    norme1 = gel(norms,k);
	    if (j  && mpcmp(norme1, borne1) > 0) break;
	    if (j  || check(data,gel(S,k)))
	    {
	      if (!j) borne1 = mpadd(norme1,eps);
	      Snew[++j] = S[k];
	    }
	  }
	  s = j; avma = av2;
	  if (s)
	  {
	    norme1 = gel(norms, per[i-1]);
	    borne1 = mpadd(norme1, eps);
	    borne2 = mpmul(borne1, alpha);
	    checkcnt = 0;
	  }
	}
	else
	{
	  if (!stockall && BORNE) goto END;
	  for (i = 1; i <= s; i++) Snew[i] = S[i];
	}
	if (stockmax != stockmaxnew)
	{
	  stockmax = stockmaxnew;
	  norms = cgetg(stockmax+1, t_VEC);
	  for (i = 1; i <= s; i++) gel(norms,i) = norme1;
	  Snew = clonefill(Snew, s, stockmax);
	  if (isclone(S)) gunclone(S);
	  S = Snew;
	}
      }
    }
  }
END:
  if (s < stockmax) stockmax = s;
  if (check)
  {
    GEN per, alph, pols, p;
    if (DEBUGLEVEL>2) fprintferr("final sort & check...\n");
    setlg(norms,stockmax+1); per = indexsort(norms);
    alph = cgetg(stockmax+1,t_VEC);
    pols = cgetg(stockmax+1,t_VEC);
    for (j=0,i=1; i<=stockmax; i++)
    {
      long t = per[i];
      norme1 = gel(norms,t);
      if (j && mpcmp(norme1, borne1) > 0) break;
      if ((p = check(data,gel(S,t))))
      {
	if (!j) borne1 = mpadd(norme1,eps);
	j++; gel(pols,j) = p; alph[j]=S[t];
      }
    }
    setlg(pols,j+1);
    setlg(alph,j+1);
    if (stockmax && isclone(S)) { alph = gcopy(alph); gunclone(S); }
    return mkvec2(pols, alph);
  }
  if (stockmax)
  {
    setlg(S,stockmax+1);
    settyp(S,t_MAT);
    if (isclone(S)) { p1 = S; S = gcopy(S); gunclone(p1); }
  }
  else
    S = cgetg(1,t_MAT);
  if (!BORNE) normax1 = mpsub(borne1, eps);
  return mkvec3(utoi(s<<1), normax1, S);
}

/* solve q(x) = x~.a.x <= bound, a > 0.
 * If check is non-NULL keep x only if check(x).
 * If a is a vector, assume a[1] is the LLL-reduced Cholesky form of q */
GEN
fincke_pohst(GEN a, GEN B0, long stockmax, long PREC, FP_chk_fun *CHECK)
{
  pari_sp av = avma;
  VOLATILE long i,j,l;
  VOLATILE GEN r,rinv,rinvtrans,u,v,res,z,vnorm,rperm,perm,uperm, bound = B0;

  if (typ(a) == t_VEC)
  {
    r = gel(a,1);
    u = NULL;
  }
  else
  {
    long prec = PREC;
    l = lg(a);
    if (l == 1)
    {
      if (CHECK) pari_err(talker, "dimension 0 in fincke_pohst");
      z = cgetg(4,t_VEC);
      gel(z,1) = gel(z,2) = gen_0;
      gel(z,3) = cgetg(1,t_MAT); return z;
    }
    i = gprecision(a); if (i) prec = i;
    if (DEBUGLEVEL>2) fprintferr("first LLL: prec = %ld\n", prec);
    u = i? lllfp(a, 0.75, LLL_GRAM): ZM_lll(a, 0.75, LLL_GRAM);
    if (lg(u) != lg(a)) return NULL;
    r = qf_apply_ZM(a,u);
    if (!i) {
      prec = DEFAULTPREC + nbits2nlong(gexpo(r));
      if (prec < PREC) prec = PREC;
    }
    r = qfgaussred_positive(r);
    if (!r) return NULL;
    for (i=1; i<l; i++)
    {
      GEN s = gsqrt(gcoeff(r,i,i), prec);
      gcoeff(r,i,i) = s;
      for (j=i+1; j<l; j++) gcoeff(r,i,j) = gmul(s, gcoeff(r,i,j));
    }
  }
  /* now r~ * r = a in LLL basis */
  rinv = RgM_inv(r);
  if (!rinv) return NULL;
  rinvtrans = shallowtrans(rinv);
  if (DEBUGLEVEL>2)
    fprintferr("Fincke-Pohst, final LLL: prec = %ld\n", gprecision(rinvtrans));
  v = lll(rinvtrans);
  if (lg(v) != lg(rinvtrans)) return NULL;

  rinvtrans = gmul(rinvtrans, v);
  v = ZM_inv(shallowtrans(v),gen_1);
  r = gmul(r,v);
  u = u? ZM_mul(u,v): v;

  l = lg(r);
  vnorm = cgetg(l,t_VEC);
  for (j=1; j<l; j++) gel(vnorm,j) = gnorml2(gel(rinvtrans,j));
  rperm = cgetg(l,t_MAT);
  uperm = cgetg(l,t_MAT); perm = indexsort(vnorm);
  for (i=1; i<l; i++) { uperm[l-i] = u[perm[i]]; rperm[l-i] = r[perm[i]]; }
  u = uperm;
  r = rperm; res = NULL;
  CATCH(precer) { }
  TRY {
    if (CHECK && CHECK->f_init) bound = CHECK->f_init(CHECK, r, u);
    r = Q_from_QR(r, gprecision(vnorm));
    if (!r) pari_err(precer,"fincke_pohst");
    res = smallvectors(r, bound, stockmax, CHECK);
  } ENDCATCH;
  if (CHECK)
  {
    if (CHECK->f_post) res = CHECK->f_post(CHECK, res, u);
    return res;
  }
  if (!res) pari_err(precer,"fincke_pohst");

  z = cgetg(4,t_VEC);
  gel(z,1) = gcopy(gel(res,1));
  gel(z,2) = gcopy(gel(res,2));
  gel(z,3) = ZM_mul(u, gel(res,3)); return gerepileupto(av,z);
}
