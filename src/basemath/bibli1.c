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
#include "parinf.h"
extern GEN extendedgcd(GEN A);
extern GEN ZV_lincomb(GEN u, GEN v, GEN X, GEN Y);
extern int addcolumntomatrix(GEN V,GEN INVP,GEN L);
extern long expodb(double x);

/* default quality ratio for LLL: 99/100 */
#define LLLDFT 100

/* scalar product x.x */
GEN
sqscal(GEN x)
{
  long i, lx;
  pari_sp av;
  GEN z;
  lx = lg(x);
  if (lx == 1) return gzero;
  av = avma;
  z = gsqr((GEN)x[1]);
  for (i=2; i<lx; i++)
    z = gadd(z, gsqr((GEN)x[i]));
  return gerepileupto(av,z);
}

/* scalar product x.y */
GEN
gscal(GEN x,GEN y)
{
  long i, lx;
  pari_sp av;
  GEN z;
  if (x == y) return sqscal(x);
  lx = lg(x);
  if (lx == 1) return gzero;
  av = avma;
  z = gmul((GEN)x[1],(GEN)y[1]);
  for (i=2; i<lx; i++)
    z = gadd(z, gmul((GEN)x[i],(GEN)y[i]));
  return gerepileupto(av,z);
}

static GEN
sqscali(GEN x)
{
  long i, lx;
  pari_sp av;
  GEN z;
  lx = lg(x);
  if (lx == 1) return gzero;
  av = avma;
  z = sqri((GEN)x[1]);
  for (i=2; i<lx; i++)
    z = addii(z, sqri((GEN)x[i]));
  return gerepileuptoint(av,z);
}

static GEN
gscali(GEN x,GEN y)
{
  long i, lx;
  pari_sp av;
  GEN z;
  if (x == y) return sqscali(x);
  lx = lg(x);
  if (lx == 1) return gzero;
  av = avma;
  z = mulii((GEN)x[1],(GEN)y[1]);
  for (i=2; i<lx; i++)
    z = addii(z, mulii((GEN)x[i],(GEN)y[i]));
  return gerepileuptoint(av,z);
}

/********************************************************************/
/**             QR Factorization via Householder matrices          **/
/********************************************************************/
static int
no_prec_pb(GEN x)
{
  return (typ(x) != t_REAL || lg(x) >  3
                           || expo(x) < (long)BITS_IN_HALFULONG);
}
/* zero x[1..k-1], fill mu */
static int
FindApplyQ(GEN x, GEN mu, GEN B, long k, GEN Q, long prec)
{
  long i, lx = lg(x)-1, lv = lx - (k-1);
  GEN v, p1, beta, Nx, x2, x1, xd = x + (k-1);

  x1 = (GEN)xd[1];
  x2 = gsqr(x1);
  if (k < lx)
  {
    for (i=2; i<=lv; i++) x2 = mpadd(x2, gsqr((GEN)xd[i]));
    Nx = gsqrt(x2, prec);
    if (signe(x1) < 0) setsigne(Nx, -1);
    v = cgetg(lv+1, t_VEC);
    v[1] = lmpadd(x1, Nx);
    for (i=2; i<=lv; i++) v[i] = xd[i];
    if (gcmp0(x2)) return 0;

    if (gcmp0(x1))
      beta = mpmul(x2, realun(prec)); /* make sure typ(beta) != t_INT */
    else
      beta = mpadd(x2, mpmul(Nx,x1));
    beta = ginv(beta);
    p1 = cgetg(3,t_VEC); Q[k] = (long)p1;
    p1[1] = (long)beta;
    p1[2] = (long)v;

    coeff(mu,k,k) = lmpneg(Nx);
  }
  else
    coeff(mu,k,k) = x[k];
  if (B)
  {
    B[k] = (long)x2;
    for (i=1; i<k; i++) coeff(mu,k,i) = x[i];
  }
  else
    for (i=1; i<k; i++) coeff(mu,i,k) = x[i];
  return no_prec_pb(x2);
}

static void
ApplyQ(GEN Q, GEN r)
{
  GEN s, rd, beta = (GEN)Q[1], v = (GEN)Q[2];
  long i, l = lg(v), lr = lg(r);

  rd = r + (lr - l);
  s = mpmul((GEN)v[1], (GEN)rd[1]);
  for (i=2; i<l; i++) s = mpadd(s, mpmul((GEN)v[i] ,(GEN)rd[i]));
  s = mpneg(mpmul(beta, s));
  for (i=1; i<l; i++) rd[i] = lmpadd((GEN)rd[i], mpmul(s, (GEN)v[i]));
}

static GEN
ApplyAllQ(GEN Q, GEN r0, long k)
{
  pari_sp av = avma;
  GEN r = dummycopy(r0);
  long j;
  for (j=1; j<k; j++) ApplyQ((GEN)Q[j], r);
  return gerepilecopy(av, r);
}

/* compute B[k] = | x[k] |^2, update mu(k, 1..k-1) using Householder matrices
 * (Q = Householder(x[1..k-1]) in factored form) */
static int
incrementalQ(GEN x, GEN L, GEN B, GEN Q, long k, long prec)
{
  GEN r = ApplyAllQ(Q, (GEN)x[k], k);
  return FindApplyQ(r, L, B, k, Q, prec);
}

/* Q vector of Householder matrices orthogonalizing x[1..j0].
 * Q[i] = 0 means not computed yet */
static int
Householder_get_mu(GEN x, GEN L, GEN B, long k, GEN Q, long prec)
{
  GEN Nx, invNx, m;
  long i, j, j0;
  if (!Q) Q = zerovec(k);
  for (j=1; j<=k; j++)
    if (typ(Q[j]) == t_INT) break;
  j0 = j;
  for (   ; j<=k; j++)
    if (! incrementalQ(x, L, B, Q, j, prec)) return 0;
  for (j=1; j<=k; j++)
  {
    m = (GEN)L[j]; Nx = (GEN)m[j]; /* should set m[j] = un; but need it later */
    if (j == k) break;
    invNx = ginv(Nx);
    for (i=max(j0, j+1); i<=k; i++) m[i] = lmpmul(invNx, (GEN)m[i]);
  }
  return 1;
}

GEN
sqred1_from_QR(GEN x, long prec)
{
  long j, k = lg(x)-1;
  GEN L, B = zerovec(k);
  L = cgetg(k+1, t_MAT);
  for (j=1; j<=k; j++) L[j] = (long)zerocol(k);
  if (!Householder_get_mu(x, L, B, k, NULL, prec)) return NULL;
  for (j=1; j<=k; j++) coeff(L,j,j) = B[j];
  return gtrans_i(L);
}

GEN
R_from_QR(GEN x, long prec)
{
  long j, k = lg(x)-1;
  GEN L, B = zerovec(k), Q = cgetg(k+1, t_VEC);
  L = cgetg(k+1, t_MAT);
  for (j=1; j<=k; j++) L[j] = (long)zerocol(k);
  for (j=1; j<=k; j++)
    if (!incrementalQ(x, L, B, Q, j, prec)) return NULL;
  return gtrans_i(L);
}

/********************************************************************/
/**             QR Factorization via Gram-Schmidt                  **/
/********************************************************************/

/* compute B[k] = | x[k] |^2, update mu(k, 1..k-1).
 * Classical Gram-Schmidt (unstable!) */
static int
incrementalGS(GEN x, GEN mu, GEN B, long k)
{
  GEN s,A = cgetg(k+1, t_COL); /* scratch space */
  long i, j;
  pari_sp av;
  A[1] = coeff(x,k,1);
  for(j=1;j<k;)
  {
    coeff(mu,k,j) = lmpdiv((GEN)A[j], (GEN)B[j]);
    j++; av = avma;
    /* A[j] <-- x[k,j] - sum_{i<j} mu[j,i] A[i] */
    s = mpmul(gcoeff(mu,j,1),(GEN)A[1]);
    for (i=2; i<j; i++) s = mpadd(s, mpmul(gcoeff(mu,j,i),(GEN)A[i]));
    s = mpneg(s); A[j] = (long)gerepileuptoleaf(av, mpadd(gcoeff(x,k,j), s));
  }
  B[k] = A[k]; return (signe((GEN)B[k]) > 0 && no_prec_pb((GEN)B[k]));
}

#if 0
/* return Gram-Schmidt orthogonal basis (f) associated to (e), B is the
 * vector of the (f_i . f_i)*/
GEN
gram_schmidt(GEN e, GEN *ptB)
{
  long i,j,lx = lg(e);
  GEN f = dummycopy(e), B, iB;

  B = cgetg(lx, t_VEC);
  iB= cgetg(lx, t_VEC);

  for (i=1;i<lx;i++)
  {
    GEN p1 = NULL;
    pari_sp av;
    B[i] = (long)sqscal((GEN)f[i]);
    iB[i]= linv((GEN)B[i]); av = avma;
    for (j=1; j<i; j++)
    {
      GEN mu = gmul(gscal((GEN)e[i],(GEN)f[j]), (GEN)iB[j]);
      GEN p2 = gmul(mu, (GEN)f[j]);
      p1 = p1? gadd(p1,p2): p2;
    }
    p1 = p1? gerepileupto(av, gsub((GEN)e[i], p1)): (GEN)e[i];
    f[i] = (long)p1;
  }
  *ptB = B; return f;
}
#endif

/********************************************************************/
/**                                                                **/
/**                          LLL ALGORITHM                         **/
/**                                                                **/
/********************************************************************/
#define swap(x,y) { long _t=x; x=y; y=_t; }
#define gswap(x,y) { GEN _t=x; x=y; y=_t; }

static GEN
lll_trivial(GEN x, long flag)
{
  GEN y;
  if (lg(x) == 1)
  { /* dim x = 0 */
    if (! (flag & lll_ALL)) return cgetg(1,t_MAT);
    y=cgetg(3,t_VEC);
    y[1]=lgetg(1,t_MAT);
    y[2]=lgetg(1,t_MAT); return y;
  }
  /* here dim = 1 */
  if (gcmp0((GEN)x[1]))
  {
    switch(flag & (~lll_GRAM))
    {
      case lll_KER: return idmat(1);
      case lll_IM : return cgetg(1,t_MAT);
      default: y=cgetg(3,t_VEC);
        y[1]=(long)idmat(1);
        y[2]=lgetg(1,t_MAT); return y;
    }
  }
  if (flag & lll_GRAM) flag ^= lll_GRAM; else x = NULL;
  switch (flag)
  {
    case lll_KER: return cgetg(1,t_MAT);
    case lll_IM : return idmat(1);
    default: y=cgetg(3,t_VEC);
      y[1]=lgetg(1,t_MAT);
      y[2]=x? lcopy(x): (long)idmat(1); return y;
  }
}

static GEN
lll_finish(GEN h,GEN fl,long flag)
{
  long i, k, l = lg(fl);
  GEN y, g;

  k=1; while (k<l && !fl[k]) k++;
  switch(flag & (~lll_GRAM))
  {
    case lll_KER: setlg(h,k);
      return h;

    case lll_IM: h += k-1; h[0] = evaltyp(t_MAT) | evallg(l-k+1);
      return h;
  }
  y = cgetg(3,t_VEC);
  g = cgetg(k, t_MAT); for (i=1; i<k; i++) g[i] = h[i];
  y[1] = (long)g;
  h += k-1; h[0] = evaltyp(t_MAT) | evallg(l-k+1);
  y[2] = (long)h; return y;
}

/* h[,k] += q * h[,l] */
static void
Zupdate_col(long k, long l, GEN q, long K, GEN h)
{
  GEN *hl, *hk;
  long i;

  if (!h) return;
  hl = (GEN*)h[l]; hk = (GEN*)h[k];
  if (is_pm1(q))
  {
    if (signe(q) > 0)
      for (i=1;i<=K;i++) { if (signe(hl[i])) hk[i] = addii(hk[i],hl[i]); }
    else
      for (i=1;i<=K;i++) { if (signe(hl[i])) hk[i] = subii(hk[i],hl[i]); }
  } else
      for (i=1;i<=K;i++) if (signe(hl[i])) hk[i] = addii(hk[i],mulii(q,hl[i]));
}

/* L[k,] += q * L[l,], l < k */
static void
Zupdate_row(long k, long l, GEN q, GEN L, GEN B)
{
  long i;
  if (is_pm1(q))
  {
    if (signe(q) > 0)
    {
      for (i=1;i<l; i++) coeff(L,k,i) = laddii(gcoeff(L,k,i),gcoeff(L,l,i));
      coeff(L,k,l) = laddii(gcoeff(L,k,l), B);
    } else {
      for (i=1;i<l; i++) coeff(L,k,i) = lsubii(gcoeff(L,k,i),gcoeff(L,l,i));
      coeff(L,k,l) = laddii(gcoeff(L,k,l), negi(B));
    }
  } else {
    for(i=1;i<l;i++)  coeff(L,k,i)=laddii(gcoeff(L,k,i),mulii(q,gcoeff(L,l,i)));
    coeff(L,k,l) = laddii(gcoeff(L,k,l), mulii(q,B));
  }
}

static void
update_row(long k, long l, GEN q, GEN L)
{
  long i;
  if (is_pm1(q))
  {
    if (signe(q) > 0)
    {
      for (i=1;i<l; i++) coeff(L,k,i) = lmpadd(gcoeff(L,k,i),gcoeff(L,l,i));
    } else {
      for (i=1;i<l; i++) coeff(L,k,i) = lmpsub(gcoeff(L,k,i),gcoeff(L,l,i));
    }
  } else {
    for(i=1;i<l;i++)  coeff(L,k,i)=lmpadd(gcoeff(L,k,i),mpmul(q,gcoeff(L,l,i)));
  }
  coeff(L,k,l) = lmpadd(gcoeff(L,k,l), q);
}

static void
ZRED_gram(long k, long l, GEN x, GEN h, GEN L, GEN B, long K)
{
  long i,lx;
  GEN q = truedvmdii(addii(B,shifti(gcoeff(L,k,l),1)), shifti(B,1), NULL);
  GEN xk,xl;
  if (!signe(q)) return;
  q = negi(q);
  xl = (GEN) x[l]; xk = (GEN) x[k];
  lx = lg(xl);
  if (is_pm1(q))
  {
    if (signe(q) > 0)
    {
      xk[k] = laddii((GEN)xk[k], (GEN)xl[k]);
      for (i=1;i<lx;i++) coeff(x,k,i) = xk[i] = laddii((GEN)xk[i], (GEN)xl[i]);
    } else {
      xk[k] = lsubii((GEN)xk[k], (GEN)xl[k]);
      for (i=1;i<lx;i++) coeff(x,k,i) = xk[i] = lsubii((GEN)xk[i], (GEN)xl[i]);
    }
  } else { /* h[,k] += q* h[,l]. x[,k] += q * x[,l]. L[k,] += q* L[l,] */
    xk[k] = laddii((GEN)xk[k], mulii(q,(GEN)xl[k]));
    for(i=1;i<lx;i++) coeff(x,k,i)=xk[i]=laddii((GEN)xk[i],mulii(q,(GEN)xl[i]));
  }
  Zupdate_row(k,l,q,L,B);
  Zupdate_col (k,l,q,K,h);
}

static void
ZRED(long k, long l, GEN x, GEN h, GEN L, GEN B, long K)
{
  GEN q = truedvmdii(addii(B,shifti(gcoeff(L,k,l),1)), shifti(B,1), NULL);
  if (!signe(q)) return;
  q = negi(q);
  Zupdate_row(k,l,q,L,B);
  Zupdate_col (k,l,q,K,h);
  x[k] = (long)ZV_lincomb(gun, q, (GEN)x[k], (GEN)x[l]);
}

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

/* b[k] <-- b[k] - round(L[k,l]) b[l], only b[1] ... b[K] modified so far
 * assume l < k and update x = Gram(b), L = Gram Schmidt coeffs. */
static int
RED_gram(long k, long l, GEN x, GEN h, GEN L, long K)
{
  long i,lx;
  GEN q = round_safe(gcoeff(L,k,l));
  GEN xk, xl;

  if (!q) return 0;
  if (!signe(q)) return 1;
  q = negi(q); lx = lg(x);
  xk = (GEN)x[k]; xl = (GEN)x[l];
  if (is_pm1(q))
  {
    if (signe(q) > 0)
    {
      xk[k] = lmpadd((GEN)xk[k], (GEN)xl[k]);
      for (i=1;i<lx;i++) coeff(x,k,i)=xk[i]=lmpadd((GEN)xk[i], (GEN)xl[i]);
    } else {
      xk[k] = lmpsub((GEN)xk[k], (GEN)xl[k]);
      for (i=1;i<lx;i++) coeff(x,k,i)=xk[i]=lmpsub((GEN)xk[i], (GEN)xl[i]);
    }
  } else {
    xk[k] = lmpadd((GEN)xk[k], mpmul(q,(GEN)xl[k]));
    for (i=1;i<lx;i++)
      coeff(x,k,i)=xk[i]=lmpadd((GEN)xk[i], mpmul(q,(GEN)xl[i]));
  }
  update_row(k,l,q,L);
  Zupdate_col(k,l,q,K,h); return 1;
}

static void
update_col(long k, long l, GEN q, GEN x)
{
  long i,lx;
  GEN xk = (GEN)x[k], xl = (GEN)x[l];
  lx = lg(xk);
  if (is_pm1(q))
  {
    if (signe(q) > 0)
    {
      for (i=1;i<lx;i++) xk[i] = lmpadd((GEN)xk[i], (GEN)xl[i]);
    } else {
      for (i=1;i<lx;i++) xk[i] = lmpsub((GEN)xk[i], (GEN)xl[i]);
    }
  } else {
    for (i=1;i<lx;i++) xk[i] = lmpadd((GEN)xk[i], mpmul(q,(GEN)xl[i]));
  }
}

static int
RED(long k, long l, GEN x, GEN h, GEN L, long K)
{
  GEN q = round_safe(gcoeff(L,k,l));
  if (!q) return 0;
  if (!signe(q)) return 1;
  q = negi(q);
  update_col(k,l,q,x);
  update_row(k,l,q,L);
  Zupdate_col(k,l,q,K,h); return 1;
}

static int
do_ZSWAP(GEN x, GEN h, GEN L, GEN B, long kmax, long k, long D, GEN fl,
         int gram)
{
  GEN la,la2,p1,Bk;
  long i, j, lx;
  pari_sp av;

  if (!fl[k-1]) return 0;
  av = avma;
  la = gcoeff(L,k,k-1); la2 = sqri(la);
  Bk = (GEN)B[k];
  if (fl[k])
  {
    GEN q;
    if (!D) return 0; /* only swap non-kernel + kernel vector */
    q = addii(la2, mulii((GEN)B[k-1],(GEN)B[k+1]));
    if (cmpii(mulsi(D-1,sqri(Bk)), mulsi(D,q)) <= 0) {
      avma = av; return 0;
    }
    B[k] = (long)diviiexact(q, Bk);
  }
  /* ZSWAP(k-1,k) */
  if (DEBUGLEVEL>3 && k==kmax)
  { /* output diagnostics associated to re-normalized rational quantities */
    pari_sp av1 = avma;
    GEN d = mulii((GEN)B[k-1],(GEN)B[k+1]);
    p1 = subii(mulsi(D-1, sqri(Bk)), mulsi(D, la2));
    fprintferr(" (%ld)", expi(p1) - expi(mulsi(D, d)));
    avma = av1;
  }
  if (h) swap(h[k-1], h[k]);
  swap(x[k-1], x[k]); lx = lg(x);
  if (gram)
    for (j=1; j < lx; j++) swap(coeff(x,k-1,j), coeff(x,k,j));
  for (j=1; j<k-1; j++) swap(coeff(L,k-1,j), coeff(L,k,j))
  if (fl[k])
  {
    av = avma;
    for (i=k+1; i<=kmax; i++)
    {
      GEN t = gcoeff(L,i,k);
      p1 = subii(mulii((GEN)B[k+1],gcoeff(L,i,k-1)), mulii(la,t));
      p1 = diviiexact(p1, Bk);
      coeff(L,i,k) = (long)icopy_av(p1,(GEN)av);
      av = avma = (pari_sp)coeff(L,i,k);

      p1 = addii(mulii(la,gcoeff(L,i,k-1)), mulii((GEN)B[k-1],t));
      p1 = diviiexact(p1, Bk);
      coeff(L,i,k-1) = (long)icopy_av(p1,(GEN)av);
      av = avma = (pari_sp)coeff(L,i,k-1);
    }
  }
  else if (signe(la))
  {
    p1 = diviiexact(la2, Bk);
    B[k+1] = B[k] = (long)p1;
    for (i=k+2; i<=lx; i++) B[i] = (long)diviiexact(mulii(p1,(GEN)B[i]), Bk);
    for (i=k+1; i<=kmax; i++)
      coeff(L,i,k-1) = (long)diviiexact(mulii(la,gcoeff(L,i,k-1)), Bk);
    for (j=k+1; j<kmax; j++)
      for (i=j+1; i<=kmax; i++)
        coeff(L,i,j) = (long)diviiexact(mulii(p1,gcoeff(L,i,j)), Bk);
  }
  else
  {
    for (i=k+1; i<=kmax; i++)
    {
      coeff(L,i,k) = coeff(L,i,k-1);
      coeff(L,i,k-1) = zero;
    }
    B[k] = B[k-1]; fl[k] = 1; fl[k-1] = 0;
  }
  return 1;
}

static int
do_SWAP(GEN x, GEN h, GEN L, GEN B, long kmax, long k, GEN delta, int gram)
{
  GEN la,la2, BK,BB,q;
  long i, j, lx;
  pari_sp av;

  av = avma;
  la = gcoeff(L,k,k-1); la2 = gsqr(la);
  q = mpmul((GEN)B[k-1], mpsub(delta,la2));
  if (mpcmp(q, (GEN)B[k]) <= 0) { avma = av; return 0; }

  /* SWAP(k-1,k) */
  if (DEBUGLEVEL>3 && k==kmax) {
    fprintferr(" (%ld)", gexpo(q) - gexpo((GEN)B[k])); flusherr();
  }
  BB = mpadd((GEN)B[k], mpmul((GEN)B[k-1],la2));
  if (!signe(BB)) { B[k] = 0; return 1; } /* precision pb */

  coeff(L,k,k-1) = lmpdiv(mpmul(la,(GEN)B[k-1]), BB);
  BK = mpdiv((GEN)B[k], BB);
  B[k] = lmpmul((GEN)B[k-1], BK);
  B[k-1] = (long)BB;

  if (h) swap(h[k-1],h[k]);
  swap(x[k-1],x[k]); lx = lg(x);
  if (gram)
    for (j=1; j < lx; j++) swap(coeff(x,k-1,j), coeff(x,k,j));
  for (j=1; j<k-1; j++) swap(coeff(L,k-1,j), coeff(L,k,j))
  for (i=k+1; i<=kmax; i++)
  {
    GEN t = gcoeff(L,i,k);
    coeff(L,i,k) = lmpsub(gcoeff(L,i,k-1), mpmul(la,t));
    coeff(L,i,k-1) = lmpadd(t, mpmul(gcoeff(L,k,k-1), gcoeff(L,i,k)));
  }
  return 1;
}
static void
ZincrementalGS(GEN x, GEN L, GEN B, long k, GEN fl, int gram)
{
  GEN u = NULL; /* gcc -Wall */
  long i, j, s;
  for (j=1; j<=k; j++)
    if (j==k || fl[j])
    {
      pari_sp av = avma;
      u = gram? gcoeff(x,k,j): gscali((GEN)x[k], (GEN)x[j]);
      for (i=1; i<j; i++)
        if (fl[i])
        {
          u = subii(mulii((GEN)B[i+1], u), mulii(gcoeff(L,k,i), gcoeff(L,j,i)));
          u = diviiexact(u, (GEN)B[i]);
        }
      coeff(L,k,j) = lpileuptoint(av, u);
    }
  s = signe(u);
  if (s == 0) B[k+1] = B[k];
  else
  {
    if (s < 0) err(lllger3);
    B[k+1] = coeff(L,k,k); coeff(L,k,k) = un; fl[k] = 1;
  }
}

/* x integer matrix. Beware: this function can return NULL */
GEN
lllint_marked(long MARKED, GEN x, long D, int gram,
              GEN *pth, GEN *ptfl, GEN *ptB)
{
  long lx = lg(x), hx, i, j, k, l, n, kmax;
  pari_sp av, lim;
  GEN B,L,h,fl;

  if (typ(x) != t_MAT) err(typeer,"lllint");
  fl = cgetg(lx,t_VECSMALL);
  if (ptfl) *ptfl = fl;
  n = lx-1; if (n <= 1) return NULL;
  hx = lg(x[1]);
  if (gram && hx != lx) err(mattype1,"lllint");

  av = avma; lim = stack_lim(av,1); x = dummycopy(x);
  B = gscalcol(gun, lx);
  L = cgetg(lx,t_MAT);
  for (j=1; j<lx; j++)
  {
    for (i=1; i<hx; i++)
      if (typ(gcoeff(x,i,j)) != t_INT) err(lllger4);
    fl[j] = 0; L[j] = (long)zerocol(n);
  }
  h = pth? idmat(n): NULL;
  ZincrementalGS(x, L, B, 1, fl, gram);
  kmax = 1;
  if (DEBUGLEVEL>5) fprintferr("k = ");
  for (k=2;;)
  {
    if (k > kmax)
    {
      if (DEBUGLEVEL>3) fprintferr("K%ld ",k);
      ZincrementalGS(x, L, B, k, fl, gram);
      kmax = k;
    }
    if (k != MARKED)
    {
      if (!gram) ZRED(k,k-1, x,h,L,(GEN)B[k],kmax);
      else  ZRED_gram(k,k-1, x,h,L,(GEN)B[k],kmax);
    }
    if (do_ZSWAP(x,h,L,B,kmax,k,D,fl,gram))
    {
      if      (MARKED == k)   MARKED = k-1;
      else if (MARKED == k-1) MARKED = k;
      if (k > 2) k--;
    }
    else
    {
      if (k != MARKED)
        for (l=k-2; l; l--)
        {
          if (!gram) ZRED(k,l, x,h,L,(GEN)B[l+1],kmax);
          else  ZRED_gram(k,l, x,h,L,(GEN)B[l+1],kmax);
          if (low_stack(lim, stack_lim(av,1)))
          {
            if(DEBUGMEM>1) err(warnmem,"lllint[1], kmax = %ld", kmax);
            gerepileall(av,h?4:3,&B,&L,&x,&h);
          }
        }
      if (++k > n) break;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"lllint[2], kmax = %ld", kmax);
      gerepileall(av,h?4:3,&B,&L,&x,&h);
    }
  }
  if (DEBUGLEVEL>3) fprintferr("\n");
  if (ptB)  *ptB  = B;
  if (ptfl) *ptfl = fl;
  if (pth)  *pth = h;
  if (MARKED && MARKED != 1)
  {
    if (B)  { swap( B[1],  B[MARKED]); }
    if (fl) { swap(fl[1], fl[MARKED]); }
    if (h)  { swap( h[1],  h[MARKED]); }
    swap(x[1], x[MARKED]);
  }
  return h? h: x;
}

/* Beware: this function can return NULL (dim x <= 1) */
GEN
lllint_i(GEN x, long D, int gram, GEN *pth, GEN *ptfl, GEN *ptB)
{
  return lllint_marked(0, x,D,gram,pth,ptfl,ptB);
}

/* return x * lllint(x). No garbage collection */
GEN
lllint_ip(GEN x, long D)
{
  GEN fl, h = lllint_i(x, D, 0, NULL, &fl, NULL);
  if (!h) return x;
  return lll_finish(h, fl, lll_IM);
}

GEN
lllall(GEN x, long D, int gram, long flag)
{
  pari_sp av = avma;
  GEN fl, junk, h = lllint_i(x, D, gram, &junk, &fl, NULL);
  if (!h) return lll_trivial(x,flag);
  return gerepilecopy(av, lll_finish(h,fl,flag));
}

GEN
lllint(GEN x) { return lllall(x,LLLDFT,0, lll_IM); }

GEN
lllkerim(GEN x) { return lllall(x,LLLDFT,0, lll_ALL); }

GEN
lllgramint(GEN x) { return lllall(x,LLLDFT,1, lll_IM | lll_GRAM); }

GEN
lllgramkerim(GEN x) { return lllall(x,LLLDFT,1, lll_ALL | lll_GRAM); }

static int
pslg(GEN x)
{
  long tx;
  if (gcmp0(x)) return 2;
  tx = typ(x); return is_scalar_t(tx)? 3: lgef(x);
}

static GEN
to_MP(GEN x, long prec)
{
  GEN y;
  if (typ(x) == t_INT && !signe(x)) return gzero;
  y = cgetr(prec); gaffect(x, y); return y;
}
static GEN
col_to_MP(GEN x, long prec)
{
  long j, l = lg(x);
  GEN y = cgetg(l, t_COL);
  for (j=1; j<l; j++) y[j] = (long)to_MP((GEN)x[j], prec);
  return y;
}
static GEN
mat_to_MP(GEN x, long prec)
{
  long j, l = lg(x);
  GEN y;
  if (typ(x) != t_MAT) return col_to_MP(x, prec);
  y = cgetg(l, t_MAT);
  for (j=1; j<l; j++) y[j] = (long)col_to_MP((GEN)x[j], prec);
  return y;
}

static GEN
to_mp(GEN x, long prec)
{
  GEN y;
  if (typ(x) == t_INT) return x;
  y = cgetr(prec); gaffect(x, y); return y;
}
static GEN
col_to_mp(GEN x, long prec)
{
  long j, l = lg(x);
  GEN y = cgetg(l, t_COL);
  for (j=1; j<l; j++) y[j] = (long)to_mp((GEN)x[j], prec);
  return y;
}
static GEN
mat_to_mp(GEN x, long prec)
{
  long j, l = lg(x);
  GEN y = cgetg(l, t_MAT);
  for (j=1; j<l; j++) y[j] = (long)col_to_mp((GEN)x[j], prec);
  return y;
}

static int
REDgen(long k, long l, GEN h, GEN L, GEN B)
{
  GEN q, u = gcoeff(L,k,l);
  long i;

  if (pslg(u) < pslg(B)) return 0;

  q = gneg(gdeuc(u,B));
  h[k] = ladd((GEN)h[k], gmul(q,(GEN)h[l]));
  for (i=1; i<l; i++) coeff(L,k,i) = ladd(gcoeff(L,k,i), gmul(q,gcoeff(L,l,i)));
  coeff(L,k,l) = ladd(gcoeff(L,k,l), gmul(q,B)); return 1;
}

static int
do_SWAPgen(GEN h, GEN L, GEN B, long k, GEN fl, int *flc)
{
  GEN p1, la, la2, Bk;
  long ps1, ps2, i, j, lx;

  if (!fl[k-1]) return 0;

  la = gcoeff(L,k,k-1); la2 = gsqr(la);
  Bk = (GEN)B[k];
  if (fl[k])
  {
    GEN q = gadd(la2, gmul((GEN)B[k-1],(GEN)B[k+1]));
    ps1 = pslg(gsqr(Bk));
    ps2 = pslg(q);
    if (ps1 <= ps2 && (ps1 < ps2 || !*flc)) return 0;
    *flc = (ps1 != ps2);
    B[k] = ldiv(q, Bk);
  }

  swap(h[k-1], h[k]); lx = lg(L);
  for (j=1; j<k-1; j++) swap(coeff(L,k-1,j), coeff(L,k,j));
  if (fl[k])
  {
    for (i=k+1; i<lx; i++)
    {
      GEN t = gcoeff(L,i,k);
      p1 = gsub(gmul((GEN)B[k+1],gcoeff(L,i,k-1)), gmul(la,t));
      coeff(L,i,k)   = ldiv(p1, Bk);
      p1 = gadd(gmul(la,gcoeff(L,i,k-1)), gmul((GEN)B[k-1],t));
      coeff(L,i,k-1) = ldiv(p1, Bk);
    }
  }
  else if (!gcmp0(la))
  {
    p1 = gdiv(la2, Bk);
    B[k+1] = B[k] = (long)p1;
    for (i=k+2; i<=lx; i++) B[i] = ldiv(gmul(p1,(GEN)B[i]),Bk);
    for (i=k+1; i<lx; i++)
      coeff(L,i,k-1) = ldiv(gmul(la,gcoeff(L,i,k-1)), Bk);
    for (j=k+1; j<lx-1; j++)
      for (i=j+1; i<lx; i++)
        coeff(L,i,j) = ldiv(gmul(p1,gcoeff(L,i,j)), Bk);
  }
  else
  {
    coeff(L,k,k-1) = zero;
    for (i=k+1; i<lx; i++)
    {
      coeff(L,i,k) = coeff(L,i,k-1);
      coeff(L,i,k-1) = zero;
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
      if (! is_extscalar_t(tu)) err(lllger4);
      for (i=1; i<j; i++)
        if (fl[i])
        {
          u = gsub(gmul((GEN)B[i+1],u), gmul(gcoeff(L,k,i),gcoeff(L,j,i)));
          u = gdiv(u, (GEN)B[i]);
        }
      coeff(L,k,j) = (long)u;
    }
  if (gcmp0(u)) B[k+1] = B[k];
  else
  {
    B[k+1] = coeff(L,k,k); coeff(L,k,k) = un; fl[k] = 1;
  }
}

static GEN
lllgramallgen(GEN x, long flag)
{
  long lx = lg(x), i, j, k, l, n;
  pari_sp av0 = avma, av, lim;
  GEN B, L, h, fl;
  int flc;

  if (typ(x) != t_MAT) err(typeer,"lllgramallgen");
  n = lx-1; if (n<=1) return lll_trivial(x,flag);
  if (lg(x[1]) != lx) err(mattype1,"lllgramallgen");

  fl = cgetg(lx, t_VECSMALL);

  av = avma; lim = stack_lim(av,1);
  B = gscalcol(gun, lx);
  L = cgetg(lx,t_MAT);
  for (j=1; j<lx; j++) { L[j] = (long)zerocol(n); fl[j] = 0; }

  h = idmat(n);
  for (i=1; i<lx; i++)
    incrementalGSgen(x, L, B, i, fl);
  flc = 0;
  for(k=2;;)
  {
    if (REDgen(k, k-1, h, L, (GEN)B[k])) flc = 1;
    if (do_SWAPgen(h, L, B, k, fl, &flc)) { if (k > 2) k--; }
    else
    {
      for (l=k-2; l>=1; l--)
        if (REDgen(k, l, h, L, (GEN)B[l+1])) flc = 1;
      if (++k > n) break;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"lllgramallgen");
      gerepileall(av,3,&B,&L,&h);
    }
  }
  return gerepilecopy(av0, lll_finish(h,fl,flag));
}

static GEN
_mul2n(GEN x, long e) { return e? gmul2n(x, e): x; }

/* E = scaling exponents
 * F = backward scaling exponents
 * X = lattice basis, Xs = associated scaled basis
 * Q = vector of Householder transformations
 * h = base change matrix (from X0)
 * R = from QR factorization of Xs[1..k-1] */
static int
HRS(int MARKED, long k, int prim, long kmax, GEN X, GEN Xs, GEN h, GEN R,
    GEN Q, GEN E, GEN F)
{
  long e, i, N = lg(X[k]);
  const long prec = MEDDEFAULTPREC; /* 128 bits */
  GEN q, tau2, rk;
  int rounds = 0, overf;

  E[k] = prim? E[k-1]: 0;
  F[k] = 0;
  Xs[k] = E[k]? lmul2n((GEN)X[k], E[k]): (long)dummycopy((GEN)X[k]);
  rounds = 0;
  if (k == MARKED) goto DONE; /* no size reduction/scaling */

UP:
  rk = ApplyAllQ(Q, col_to_MP((GEN)Xs[k], prec), k);
  overf = 0;
  for (i = k-1; i > 0; i--)
  { /* size seduction of Xs[k] */
    GEN q2, mu, muint;
    long ex;
    pari_sp av = avma;

    mu = mpdiv((GEN)rk[i], gcoeff(R,i,i));
    if (!signe(mu)) { avma = av; continue; }
    mu = _mul2n(mu, -F[i]); /*backward scaling*/
    ex = gexpo(mu);
    if (ex > 10) {
      overf = 1; /* large size reduction */
      muint = ex > 30? ceil_safe(mu): ground(mu);
    }
    else if (fabs(gtodouble(mu)) > 0.51)
      muint = ground(mu);
    else { avma = av; continue; }

    q = gerepileuptoint(av, negi(muint));
    q2= _mul2n(q, F[i]); /*backward scaling*/
    Zupdate_col(k, i, q2, N-1, Xs);
    rk = gadd(rk, gmul(q2, (GEN)R[i]));
    /* if in HRS', propagate the last SR on X (for SWAP test) */
    if (prim && (i == k-1)) {
      Zupdate_col(k, i, q, kmax, h);
       update_col(k, i, q, X);
    }
  }
  /* If large size-reduction performed, restart from exact data */
  if (overf)
  {
    if (++rounds > 100) return 0; /* detect infinite loop */
    goto UP;
  }

  if (prim || k == 1) goto DONE; /* DONE */

  rounds = 0;
  /* rescale Xs[k] ? */
  tau2 = signe(rk[k])? gsqr((GEN)rk[k]): gzero;
  for (i = k+1; i < N; i++)
    if (signe(rk[i])) tau2 = mpadd(tau2, gsqr((GEN)rk[i]));
  q = mpdiv(gsqr(gcoeff(R,1,1)), tau2);
  e = gexpo(q)/2 + F[1]; /* ~ log_2 (||Xs[1]|| / tau), backward scaling*/
  if (e > 0)
  { /* rescale */
    if (e > 30) e = 30;
    Xs[k] = lmul2n((GEN)Xs[k], e);
    E[k] += e; goto UP; /* one more round */
  }
  else if (e < 0)
  { /* enable backward scaling */
    for (i = 1; i < k; i++) F[i] -= e;
  }

DONE:
  rk = ApplyAllQ(Q, col_to_MP((GEN)Xs[k], prec), k);
  (void)FindApplyQ(rk, R, NULL, k, Q, prec);
  return 1;
}

static GEN
rescale_to_int(GEN x)
{
  long e, prec = gprecision(x);
  GEN y;
  if (!prec) return Q_primpart(x);

  y = gmul2n(x, bit_accuracy(prec) - gexpo(x));
  return gcvtoi(y, &e);
}

GEN
lll_scaled(int MARKED, GEN X0, long D)
{
  GEN delta, X, Xs, h, R, Q, E, F;
  long j, kmax = 1, k, N = lg(X0);
  pari_sp lim, av, av0 = avma;
  int retry = 0;

  delta = stor(D-1, DEFAULTPREC);
  delta = divrs(delta,D);
  E  = vecsmall_const(N-1, 0);
  F  = vecsmall_const(N-1, 0);

  av = avma; lim = stack_lim(av, 1);
  h = idmat(N-1);
  X = rescale_to_int(X0);

PRECPB:
  k = 1;
  if (retry++) return _vec(h);
  Q  = zerovec(N-1);
  Xs = zeromat(N-1, N-1);
  R  = cgetg(N, t_MAT);
  for (j=1; j<N; j++) R[j] = (long)zerocol(N-1);

  while (k < N)
  {
    pari_sp av1;
    if (k == 1) {
      HRS(MARKED, 1, 0, kmax, X, Xs, h, R, Q, E, F);
      k = 2;
    }
    if (k > kmax) {
      kmax = k;
      if (DEBUGLEVEL>3) {fprintferr(" K%ld",k);flusherr();}
    }
    if (!HRS(MARKED, k, 1, kmax, X, Xs, h, R, Q, E, F)) goto PRECPB;

    av1 = avma;
    if (mpcmp( mpmul(delta, gsqr(gcoeff(R, k-1,k-1))),
               mpadd(gsqr(gcoeff(R,k-1,k)), gsqr(gcoeff(R, k,k)))) > 0)
    {
      if (DEBUGLEVEL>3 && k == kmax)
      {
        GEN q = mpsub( mpmul(delta, gsqr(gcoeff(R, k-1,k-1))),
                       gsqr(gcoeff(R,k-1,k)));
        fprintferr(" (%ld)", gexpo(q) - gexpo(gsqr(gcoeff(R, k,k))));
      }
      swap(X[k], X[k-1]);
      swap(h[k], h[k-1]);
      if      (MARKED == k)   MARKED = k-1;
      else if (MARKED == k-1) MARKED = k;
      avma = av1; k--;
    }
    else
    {
      avma = av1;
      if (!HRS(MARKED, k, 0, kmax, X, Xs, h, R, Q, E, F)) goto PRECPB;
      k++;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"lllfp[1]");
      gerepileall(av,5,&X,&Xs, &R,&h,&Q);
    }
  }
  return gerepilecopy(av0, h);
}

static long
good_prec(GEN x, long kmax)
{
  long prec = ((kmax<<2) + gexpo((GEN)x[kmax])) >> TWOPOTBITS_IN_LONG;
  if (prec < DEFAULTPREC) prec = DEFAULTPREC;
  return prec;
}

/* If gram = 1, x = Gram(b_i), x = (b_i) otherwise
 * Quality ratio = delta = (D-1)/D. Suggested values: D = 4 or D = 100
 *
 * If precision problems:
 *   if (flag = 1): return NULL
 *   if (flag = 2): return _vec ( h )  [ partial transformation matrix ],
 *     unless we could not even start; return NULL in this case.
 *   Error otherwise
 *
 * If MARKED != 0 make sure e[MARKED] is the first vector of the output basis
 * (which may then not be LLL-reduced) */
GEN
lllfp_marked(int MARKED, GEN x, long D, long flag, long prec, int gram)
{
  GEN xinit,L,h,B,L1,delta, Q, H = NULL;
  long retry = 2, lx = lg(x), hx, l, i, j, k, k1, n, kmax, KMAX;
  pari_sp av0 = avma, av, lim;
  int isexact, exact_can_leave, count, count_max = 8;

  if (typ(x) != t_MAT) err(typeer,"lllfp");
  n = lx-1; if (n <= 1) return idmat(n);
#if 0 /* doesn't work yet */
  return lll_scaled(MARKED, x, D);
#endif

  hx = lg(x[1]);
  if (hx != lx)
  {
    if (gram) err(mattype1,"lllfp");
    if (lx > hx) err(talker,"dependant vectors in lllfp");
  }
  delta = divrs(stor(D-1, DEFAULTPREC), D);
  xinit = x;
  av = avma; lim = stack_lim(av,1);
  if (gram) {
    for (k=2,j=1; j<lx; j++)
    {
      GEN p1=(GEN)x[j];
      for (i=1; i<=j; i++)
        if (typ(p1[i]) == t_REAL) { l = lg(p1[i]); if (l>k) k=l; }
    }
  } else {
    for (k=2,j=1; j<lx; j++)
    {
      GEN p1=(GEN)x[j];
      for (i=1; i<hx; i++)
        if (typ(p1[i]) == t_REAL) { l = lg(p1[i]); if (l>k) k=l; }
    }
  }
  if (k == 2)
  {
    if (!prec) return lllint_marked(MARKED, x, D, gram, &h, NULL, NULL);
    x = mat_to_MP(x, prec);
    isexact = 1;
  }
  else
  {
    if (prec < k) prec = k;
    x = mat_to_mp(x, prec+1);
    isexact = 0;
  }
 /* kmax = maximum column index attained during this run
  * KMAX = same over all runs (after PRECPB) */
  kmax = KMAX = 1;
  h = idmat(n);

#ifdef LONG_IS_64BIT
#  define PREC_THRESHOLD 32
#  define PREC_DEC_THRESHOLD 7
#else
#  define PREC_THRESHOLD 62
#  define PREC_DEC_THRESHOLD 12
#endif
PRECPB:
  switch(retry--)
  {
    case 2: break; /* entry */
    case 1:
      if (DEBUGLEVEL>3) fprintferr("\n");
      if (flag == 2) return _vec(h);
      if (isexact || (gram && kmax > 2))
      { /* some progress but precision loss, try again */
        if (prec < PREC_THRESHOLD)
          prec = (prec<<1)-2;
        else
          prec = (long)((prec-2) * 1.25 + 2);
        if (DEBUGLEVEL) err(warnprec,"lllfp",prec);
        if (isexact)
        {
          H = H? gmul(H, h): h;
          xinit = gram? qf_base_change(xinit, h, 1): gmul(xinit, h);
          gerepileall(av, 2, &xinit, &H);
          x = mat_to_MP(xinit, prec); 
          h = idmat(n);
          retry = 1; /* never abort if x is exact */
          count_max = min(count_max << 1, 512);
          if (DEBUGLEVEL>3) fprintferr("count_max = %ld\n", count_max);
        }
        else
        {
          x = gprec_w(xinit,prec);
          x = gram? qf_base_change(x, h, 1): gmul(x, h);
          gerepileall(av, 2, &h, &x);
        }
        kmax = 1; break;
      } /* fall through */
    case 0: /* give up */
      if (DEBUGLEVEL>3) fprintferr("\n");
      if (DEBUGLEVEL) err(warner,"lllfp giving up");
      if (flag) { avma=av; return NULL; }
      err(lllger3);
  }
  exact_can_leave = 1;
  count = 0;
  Q = zerovec(n);
  L = cgetg(lx,t_MAT);
  B = cgetg(lx,t_COL);
  for (j=1; j<lx; j++) { L[j] = (long)zerocol(n); B[j] = zero; }
  if (gram && !incrementalGS(x, L, B, 1))
  {
    if (flag) return NULL;
    err(lllger3);
  }
  if (DEBUGLEVEL>5) fprintferr("k =");
  for(k=2;;)
  {
    if (k > kmax)
    {
      kmax = k;
      if (KMAX < kmax) { KMAX = kmax; count_max = 8; }
      if (DEBUGLEVEL>3) {fprintferr(" K%ld",k);flusherr();}
      if (gram) j = incrementalGS(x, L, B, k);
      else      j = Householder_get_mu(x, L, B, k, Q, prec);
      if (!j) goto PRECPB;
      count = 0;
    }
    else if (isexact && prec > PREC_DEC_THRESHOLD && k == kmax-1
                                                  && ++count > count_max)
    { /* try to reduce precision */
      count = 0;
      prec = (prec+2) >> 1;
      if (DEBUGLEVEL>3) fprintferr("\n...LLL reducing precision to %ld\n",prec);
      H = H? gmul(H, h): h;
      xinit = gram? qf_base_change(xinit, h, 1): gmul(xinit, h);
      gerepileall(av, 5,&B,&L,&Q,&H,&xinit);
      x = mat_to_MP(xinit, prec); 
      h = idmat(n);
    }
    else if (DEBUGLEVEL>5) fprintferr(" %ld",k);
    L1 = gcoeff(L,k,k-1);
    if (typ(L1) == t_REAL && expo(L1) + 20 > bit_accuracy(lg(L1)))
    {
      if (!gram) goto PRECPB;
      if (DEBUGLEVEL>3)
	fprintferr("\nRecomputing Gram-Schmidt, kmax = %ld\n", kmax);
      for (k1=1; k1<=kmax; k1++)
        if (!incrementalGS(x, L, B, k1)) goto PRECPB;
    }
    if (k != MARKED)
    {
      if (!gram) j = RED(k,k-1, x,h,L,KMAX);
      else  j = RED_gram(k,k-1, x,h,L,KMAX);
      if (!j) goto PRECPB;
    }
    if (do_SWAP(x,h,L,B,kmax,k,delta,gram))
    {
      if      (MARKED == k)   MARKED = k-1;
      else if (MARKED == k-1) MARKED = k;
      if (!B[k]) goto PRECPB;
      Q[k] = Q[k-1] = zero;
      exact_can_leave = 0;
      if (k>2) k--;
    }
    else
    {
      if (k != MARKED)
        for (l=k-2; l; l--)
        {
          if (!gram) j = RED(k,l, x,h,L,KMAX);
          else  j = RED_gram(k,l, x,h,L,KMAX);
          if (!j) goto PRECPB;
          if (low_stack(lim, stack_lim(av,1)))
          {
            if(DEBUGMEM>1) err(warnmem,"lllfp[1], kmax = %ld", kmax);
            gerepileall(av,H? 7: 5,&B,&L,&h,&x,&Q,&H,&xinit);
          }
        }
      if (++k > n)
      {
        if (isexact)
        {
          if (exact_can_leave) { if (H) h = H; break; }

          if (DEBUGLEVEL>3) fprintferr("\nChecking LLL basis...");
          H = H? gmul(H, h): h;
          xinit = gram? qf_base_change(xinit, h, 1): gmul(xinit, h);

          prec = good_prec(xinit, kmax);
#if 0 /* slower */
          if (prec == DEFAULTPREC) {
            if (DEBUGLEVEL>3) fprintferr("switch to integral algorithm\n");
            h = gram? lllgramint(xinit): lllint(xinit);
            if (H) h = gmul(H, h);

            break;
          }
#endif
          if (DEBUGLEVEL>3) fprintferr("in precision %ld\n", prec);
          x = mat_to_MP(xinit, prec);
          h = idmat(n);
          exact_can_leave = 1;
          k = 2; kmax = 1; continue;
        }
        else if (!gram && Q[n-1] == zero)
        {
          if (DEBUGLEVEL>3) fprintferr("\nChecking LLL basis\n");
          j = Householder_get_mu(gmul(xinit,h), L, B, n, Q, prec);
          if (!j) goto PRECPB;
          k = 2; continue;
        }
        break;
      }
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"lllfp[2], kmax = %ld", kmax);
      gerepileall(av,H? 7: 5,&B,&L,&h,&x,&Q,&H,&xinit);
    }
  }
  if (DEBUGLEVEL>3) fprintferr("\n");
  if (MARKED && MARKED != 1) swap(h[1], h[MARKED]);
  return gerepilecopy(av0, h);
}

GEN
lllgramintern(GEN x, long D, long flag, long prec)
{
  return lllfp_marked(0, x,D,flag,prec,1);
}

GEN
lllintern(GEN x, long D, long flag, long prec)
{
  return lllfp_marked(0, x,D,flag,prec,0);
}

GEN
lllgram(GEN x,long prec) { return lllgramintern(x,LLLDFT,0,prec); }

GEN
lll(GEN x,long prec) { return lllintern(x,LLLDFT,0,prec); }

GEN
qflll0(GEN x, long flag, long prec)
{
  switch(flag)
  {
    case 0: return lll(x,prec);
    case 1: return lllint(x);
    case 2: return lllintpartial(x);
    case 4: return lllkerim(x);
    case 5: return lllkerimgen(x);
    case 8: return lllgen(x);
    default: err(flagerr,"qflll");
  }
  return NULL; /* not reached */
}

GEN
qflllgram0(GEN x, long flag, long prec)
{
  switch(flag)
  {
    case 0: return lllgram(x,prec);
    case 1: return lllgramint(x);
    case 4: return lllgramkerim(x);
    case 5: return lllgramkerimgen(x);
    case 8: return lllgramgen(x);
    default: err(flagerr,"qflllgram");
  }
  return NULL; /* not reached */
}

GEN
gram_matrix(GEN b)
{
  long i,j, lx = lg(b);
  GEN g;
  if (typ(b) != t_MAT) err(typeer,"gram");
  g = cgetg(lx,t_MAT);
  for (i=1; i<lx; i++)
  {
    g[i] = lgetg(lx,t_COL);
    for (j=1; j<=i; j++)
      coeff(g,i,j) = coeff(g,j,i) = (long)gscal((GEN)b[i],(GEN)b[j]);
  }
  return g;
}

GEN
lllgen(GEN x) {
  pari_sp av = avma;
  return gerepileupto(av, lllgramgen(gram_matrix(x)));
}

GEN
lllkerimgen(GEN x) {
  pari_sp av = avma;
  return gerepileupto(av, lllgramallgen(gram_matrix(x),lll_ALL));
}

GEN
lllgramgen(GEN x) { return lllgramallgen(x,lll_IM); }

GEN
lllgramkerimgen(GEN x) { return lllgramallgen(x,lll_ALL); }

/*  This routine is functionally similar to lllint when all = 0.
 *
 *    The input is an integer matrix mat (not necessarily square) whose
 *  columns are linearly independent.  It outputs another matrix T such that
 *  mat * T is partially reduced.  If all = 0, the size of mat * T is the
 *  same as the size of mat.  If all = 1 the number of columns of mat * T
 *  is at most equal to its number of rows.  A matrix M is said to be
 *  -partially reduced- if | m1 +- m2 | >= |m1| for any two distinct
 *  columns m1, m2, in M.
 *
 *    This routine is designed to quickly reduce lattices in which one row
 *  is huge compared to the other rows.  For example, when searching for a
 *  polynomial of degree 3 with root a mod p, the four input vectors might
 *  be the coefficients of
 *      X^3 - (a^3 mod p), X^2 - (a^2 mod p), X - (a mod p), p.
 *  All four constant coefficients are O(p) and the rest are O(1). By the
 *  pigeon-hole principle, the coefficients of the smallest vector in the
 *  lattice are O(p^(1/4)), Hence significant reduction of vector lengths
 *  can be anticipated.
 *
 *  		Peter Montgomery (July, 1994)
 *
 *  If flag = 1 complete the reduction using lllint, otherwise return
 *  partially reduced basis. */
GEN
lllintpartialall(GEN m, long flag)
{
  const long ncol = lg(m)-1;
  const pari_sp ltop1 = avma;
  long ncolnz;
  GEN tm1, tm2, mid;

  if (typ(m) != t_MAT) err(typeer,"lllintpartialall");
  if (ncol <= 1) return idmat(ncol);

  {
    GEN dot11 = sqscali((GEN)m[1]);
    GEN dot22 = sqscali((GEN)m[2]);
    GEN dot12 = gscali((GEN)m[1], (GEN)m[2]);
    GEN tm  = idmat(2); /* For first two columns only */

    int progress = 0;
    long npass2 = 0;

/* Try to row reduce the first two columns of m.
 * Our best result so far is (first two columns of m)*tm.
 *
 * Initially tm = 2 x 2 identity matrix.
 * The inner products of the reduced matrix are in
 * dot11, dot12, dot22. */
    while (npass2 < 2 || progress)
    {
      GEN dot12new, q = diviiround(dot12, dot22);

      npass2++; progress = signe(q);
      if (progress)
      {
       /* Conceptually replace (v1, v2) by (v1 - q*v2, v2),
        * where v1 and v2 represent the reduced basis for the
        * first two columns of the matrix.
        *
        * We do this by updating tm and the inner products.
        *
        * An improved algorithm would look only at the leading
        * digits of dot11, dot12, dot22.  It would use
        * single-precision calculations as much as possible. */
        q = negi(q);
        dot12new = addii(dot12, mulii(q, dot22));
        dot11 = addii(dot11, mulii(q, addii(dot12, dot12new)));
        dot12 = dot12new;
        tm[1] = (long)ZV_lincomb(gun,q, (GEN)tm[1],(GEN)tm[2]);
      }

      /* Interchange the output vectors v1 and v2.  */
      gswap(dot11,dot22); swap(tm[1],tm[2]);

      /* Occasionally (including final pass) do garbage collection.  */
      if (npass2 % 8 == 0 || !progress)
        gerepileall(ltop1, 4, &dot11,&dot12,&dot22,&tm);
    } /* while npass2 < 2 || progress */

    {
      long icol;
      GEN det12 = subii(mulii(dot11, dot22), mulii(dot12, dot12));

      tm1 = idmat(ncol);
      mid = cgetg(ncol+1, t_MAT);
      for (icol = 1; icol <= 2; icol++)
      {
        coeff(tm1,1,icol) = coeff(tm,1,icol);
	coeff(tm1,2,icol) = coeff(tm,2,icol);
        mid[icol] = (long)ZV_lincomb(
           gcoeff(tm,1,icol),gcoeff(tm,2,icol), (GEN)m[1],(GEN)m[2]);
      }
      for (icol = 3; icol <= ncol; icol++)
      {
        GEN curcol = (GEN)m[icol];
	GEN dot1i = gscali((GEN)mid[1], curcol);
        GEN dot2i = gscali((GEN)mid[2], curcol);
       /* Try to solve
        *
        * ( dot11  dot12 ) (q1)    ( dot1i )
        * ( dot12  dot22 ) (q2)  = ( dot2i )
        *
        * Round -q1 and -q2 to the nearest integer.
        * Then compute curcol - q1*mid[1] - q2*mid[2].
        * This will be approximately orthogonal to the
        * first two vectors in the new basis. */
	GEN q1neg = subii(mulii(dot12, dot2i), mulii(dot22, dot1i));
        GEN q2neg = subii(mulii(dot12, dot1i), mulii(dot11, dot2i));

        q1neg = diviiround(q1neg, det12);
        q2neg = diviiround(q2neg, det12);
        coeff(tm1, 1, icol) = ladd(mulii(q1neg, gcoeff(tm,1,1)),
				   mulii(q2neg, gcoeff(tm,1,2)));
        coeff(tm1, 2, icol) = ladd(mulii(q1neg, gcoeff(tm,2,1)),
				   mulii(q2neg, gcoeff(tm,2,2)));
        mid[icol] = ladd(curcol,
          ZV_lincomb(q1neg,q2neg, (GEN)mid[1],(GEN)mid[2]));
      } /* for icol */
    } /* local block */
  }
  if (DEBUGLEVEL>6)
  {
    fprintferr("tm1 = %Z",tm1);
    fprintferr("mid = %Z",mid);
  }
  gerepileall(ltop1,2, &tm1, &mid);
  {
   /* For each pair of column vectors v and w in mid * tm2,
    * try to replace (v, w) by (v, v - q*w) for some q.
    * We compute all inner products and check them repeatedly. */
    const pari_sp ltop3 = avma; /* Excludes region with tm1 and mid */
    const pari_sp lim = stack_lim(ltop3,1);
    long icol, reductions, npass = 0;
    GEN dotprd = cgetg(ncol+1, t_MAT);

    tm2 = idmat(ncol);
    for (icol=1; icol <= ncol; icol++)
    {
      long jcol;

      dotprd[icol] = lgetg(ncol+1,t_COL);
      for (jcol=1; jcol <= icol; jcol++)
	coeff(dotprd,jcol,icol) = coeff(dotprd,icol,jcol) =
          (long)gscali((GEN)mid[icol], (GEN)mid[jcol]);
    } /* for icol */
    for(;;)
    {
      reductions = 0;
      for (icol=1; icol <= ncol; icol++)
      {
	long ijdif;
        for (ijdif=1; ijdif < ncol; ijdif++)
	{
          long dcol, jcol, k1, k2;
          GEN codi, q;

          jcol = icol + ijdif;
          if (jcol > ncol) jcol -= ncol;
          if (cmpii(gcoeff(dotprd,icol,icol),
		    gcoeff(dotprd,jcol,jcol) ) > 0)
          { k1 = icol; k2 = jcol; }
          else
          { k2 = icol; k1 = jcol; }
	  /* k1, resp. k2,  index of larger, resp. smaller, column */
	  codi = gcoeff(dotprd,k2,k2);
          q = signe(codi)? diviiround(gcoeff(dotprd,k1,k2), codi): gzero;
          if (!signe(q)) continue;

	  /* Try to subtract a multiple of column k2 from column k1.  */
          reductions++; q = negi(q);
          tm2[k1]   = (long)ZV_lincomb(gun,q, (GEN)tm2[k1], (GEN)tm2[k2]);
          dotprd[k1]= (long)ZV_lincomb(gun,q, (GEN)dotprd[k1], (GEN)dotprd[k2]);
          coeff(dotprd, k1, k1) = laddii(gcoeff(dotprd,k1,k1),
                                         mulii(q, gcoeff(dotprd,k2,k1)));
          for (dcol = 1; dcol <= ncol; dcol++)
            coeff(dotprd,k1,dcol) = coeff(dotprd,dcol,k1);
        } /* for ijdif */
        if (low_stack(lim, stack_lim(ltop3,1)))
	{
          if(DEBUGMEM>1) err(warnmem,"lllintpartialall");
	  gerepileall(ltop3, 2, &dotprd,&tm2);
        }
      } /* for icol */
      if (!reductions) break;
      if (DEBUGLEVEL>6)
      {
	GEN diag_prod = dbltor(1.0);
	for (icol = 1; icol <= ncol; icol++)
	  diag_prod = mpmul(diag_prod, gcoeff(dotprd,icol,icol));
        npass++;
	fprintferr("npass = %ld, red. last time = %ld, diag_prod = %Z\n\n",
	            npass, reductions, diag_prod);
      }
    } /* for(;;)*/

   /* Sort columns so smallest comes first in m * tm1 * tm2.
    * Use insertion sort. */
    for (icol = 1; icol < ncol; icol++)
    {
      long jcol, s = icol;

      for (jcol = icol+1; jcol <= ncol; jcol++)
	if (cmpii(gcoeff(dotprd,s,s),gcoeff(dotprd,jcol,jcol)) > 0) s = jcol;
      if (icol != s)
      { /* Exchange with proper column */
        /* Only diagonal of dotprd is updated */
        swap(tm2[icol], tm2[s]);
        swap(coeff(dotprd,icol,icol), coeff(dotprd,s,s));
      }
    } /* for icol */
    icol = 1;
    while (icol <= ncol && !signe(gcoeff(dotprd,icol,icol))) icol++;
    ncolnz = ncol - icol + 1;
  } /* local block */

  if (flag)
  {
    if (ncolnz == lg((GEN)m[1])-1)
    {
      tm2 += (ncol-ncolnz);
      tm2[0]=evaltyp(t_MAT)|evallg(ncolnz+1);
    }
    else
    {
      tm1 = gmul(tm1, tm2);
      tm2 = lllint(gmul(m, tm1));
    }
  }
  if (DEBUGLEVEL>6)
    fprintferr("lllintpartial output = %Z", gmul(tm1, tm2));
  return gerepileupto(ltop1, gmul(tm1, tm2));
}

GEN
lllintpartial(GEN mat)
{
  return lllintpartialall(mat,1);
}

/********************************************************************/
/**                                                                **/
/**                   LINEAR & ALGEBRAIC DEPENDENCE                **/
/**                                                                **/
/********************************************************************/

GEN pslq(GEN x);
GEN pslqL2(GEN x);

GEN
lindep0(GEN x,long bit,long prec)
{
  switch (bit)
  {
    case 0: return pslq(x);
    case -1: return lindep(x,prec);
    case -2: return deplin(x);
    case -3: return pslqL2(x);
    default: return lindep2(x,labs(bit));
  }
}

static int
real_indep(GEN re, GEN im, long bitprec)
{
  GEN p1 = gsub(gmul((GEN)re[1],(GEN)im[2]),
                gmul((GEN)re[2],(GEN)im[1]));
  return (!gcmp0(p1) && gexpo(p1) > - bitprec);
}

GEN
lindep2(GEN x, long bit)
{
  long tx=typ(x), lx=lg(x), ly, i, j, e;
  pari_sp av = avma;
  GEN re,im,p1,p2;

  if (! is_vec_t(tx)) err(typeer,"lindep2");
  if (lx<=2) return cgetg(1,t_VEC);
  re = greal(x);
  im = gimag(x); bit = (long) (bit/L2SL10);
  /* independant over R ? */
  if (lx == 3 && real_indep(re,im,bit))
    { avma = av; return cgetg(1, t_VEC); }

  if (gcmp0(im)) im = NULL;
  ly = im? lx+2: lx+1;
  p2=cgetg(lx,t_MAT);
  for (i=1; i<lx; i++)
  {
    p1 = cgetg(ly,t_COL); p2[i] = (long)p1;
    for (j=1; j<lx; j++) p1[j] = (i==j)? un: zero;
    p1[lx]           = lcvtoi(gshift((GEN)re[i],bit),&e);
    if (im) p1[lx+1] = lcvtoi(gshift((GEN)im[i],bit),&e);
  }
  p1 = (GEN)lllint_ip(p2,100)[1];
  p1[0] = evaltyp(t_COL) | evallg(lx);
  return gerepilecopy(av, p1);
}

#define quazero(x) (gcmp0(x) || (typ(x)==t_REAL && expo(x) < EXP))
GEN
lindep(GEN x, long prec)
{
  GEN *b,*be,*bn,**m,qzer;
  GEN c1,c2,c3,px,py,pxy,re,im,p1,p2,r,f,em;
  long i,j,fl,k, lx = lg(x), tx = typ(x), n = lx-1;
  pari_sp av = avma, lim = stack_lim(av,1), av0, av1;
  const long EXP = - bit_accuracy(prec) + 2*n;

  if (! is_vec_t(tx)) err(typeer,"lindep");
  if (n <= 1) return cgetg(1,t_VEC);
  x = gmul(x, realun(prec)); if (tx != t_COL) settyp(x,t_COL);
  re = greal(x);
  im = gimag(x);
  /* independant over R ? */
  if (n == 2 && real_indep(re,im,bit_accuracy(prec)))
    { avma = av; return cgetg(1, t_VEC); }
  if (EXP > -10) err(precer,"lindep");

  qzer = cgetg(lx, t_VECSMALL);
  b = (GEN*)idmat(n);
  be= (GEN*)new_chunk(lx);
  bn= (GEN*)new_chunk(lx);
  m = (GEN**)new_chunk(lx);
  for (i=1; i<=n; i++)
  {
    bn[i] = cgetr(prec+1);
    be[i] = cgetg(lx,t_COL);
    m[i]  = (GEN*)new_chunk(lx);
    for (j=1; j<i ; j++) m[i][j] = cgetr(prec+1);
    for (j=1; j<=n; j++) be[i][j]= lgetr(prec+1);
  }
  px = sqscal(re);
  py = sqscal(im); pxy = gscal(re,im);
  p1 = mpsub(mpmul(px,py), gsqr(pxy));
  if (quazero(px)) { re = im; px = py; fl = 1; } else fl = quazero(p1);
  av0 = av1 = avma;
  for (i=1; i<=n; i++)
  {
    p2 = gscal(b[i],re);
    if (fl) p2 = gmul(gdiv(p2,px),re);
    else
    {
      GEN p5,p6,p7;
      p5 = gscal(b[i],im);
      p6 = gdiv(gsub(gmul(py,p2),gmul(pxy,p5)), p1);
      p7 = gdiv(gsub(gmul(px,p5),gmul(pxy,p2)), p1);
      p2 = gadd(gmul(p6,re), gmul(p7,im));
    }
    p2 = gsub(b[i],p2);
    for (j=1; j<i; j++)
      if (qzer[j]) affrr(bn[j], m[i][j]);
      else
      {
        gdivz(gscal(b[i],be[j]),bn[j], m[i][j]);
        p2 = gsub(p2, gmul(m[i][j],be[j]));
      }
    gaffect(p2,          be[i]);
    affrr(sqscal(be[i]), bn[i]);
    qzer[i] = quazero(bn[i]); avma = av1;
  }
  while (qzer[n])
  {
    long e;
    if (DEBUGLEVEL>8)
    {
      fprintferr("qzer[%ld]=%ld\n",n,qzer[n]);
      for (k=1; k<=n; k++)
	for (i=1; i<k; i++) output(m[k][i]);
    }
    em=bn[1]; j=1;
    for (i=2; i<n; i++)
    {
      p1=shiftr(bn[i],i);
      if (cmprr(p1,em)>0) { em=p1; j=i; }
    }
    i=j; k=i+1;
    avma = av1; r = grndtoi(m[k][i], &e);
    if (e >= 0) err(precer,"lindep");
    r  = negi(r);
    p1 = ZV_lincomb(gun,r, b[k],b[i]);
    b[k] = b[i];
    b[i]  = p1;
    av1 = avma;
    f = addir(r,m[k][i]);
    for (j=1; j<i; j++)
      if (!qzer[j])
      {
        p1 = mpadd(m[k][j], mulir(r,m[i][j]));
        affrr(m[i][j],m[k][j]);
        mpaff(p1,m[i][j]);
      }
    c1 = addrr(bn[k], mulrr(gsqr(f),bn[i]));
    if (!quazero(c1))
    {
      c2 = divrr(mulrr(bn[i],f),c1); affrr(c2, m[k][i]);
      c3 = divrr(bn[k],c1);
      mulrrz(c3,bn[i], bn[k]); qzer[k] = quazero(bn[k]);
      affrr(c1,        bn[i]); qzer[i] = 0;
      for (j=i+2; j<=n; j++)
      {
        p1 = addrr(mulrr(m[j][k],c3), mulrr(m[j][i],c2));
        subrrz(m[j][i],mulrr(f,m[j][k]), m[j][k]);
        affrr(p1, m[j][i]);
      }
    }
    else
    {
      affrr(bn[i], bn[k]); qzer[k] = qzer[i];
      affrr(c1,    bn[i]); qzer[i] = 1;
      for (j=i+2; j<=n; j++) affrr(m[j][i], m[j][k]);
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"lindep");
      b = (GEN*)gerepilecopy(av0, (GEN)b);
      av1 = avma;
    }
  }
  p1 = cgetg(lx,t_COL); p1[n] = un; for (i=1; i<n; i++) p1[i] = zero;
  return gerepileupto(av, gauss(gtrans_i((GEN)b),p1));
}

/* PSLQ Programs */

typedef struct {
  long vmind, t12, t1234, reda, fin;
  long ct;
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
init_dalloc()
{ /* correct alignment for dalloc */
  avma -= avma % sizeof(double);
  if (avma < bot) err(errpile);
}

double *
dalloc(size_t n)
{
  if (avma - bot < n) err(errpile);
  avma -= n; return (double*)avma;
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
  const GEN Bi = (GEN)B[i];

  for (j=jsup; j>=1; j--)
  {
    pari_sp av = avma;
    t = round_safe( gdiv(gcoeff(H,i,j), gcoeff(H,j,j)) );
    if (!t || gcmp0(t)) { avma = av; continue; }

    b = (GEN)B[j];
    y[j] = ladd((GEN)y[j], gmul(t,(GEN)y[i]));
    for (k=1; k<=j; k++)
      coeff(H,i,k) = lsub(gcoeff(H,i,k), gmul(t,gcoeff(H,j,k)));
    for (k=1; k<=n; k++)
    {
      coeff(A,i,k) = lsub(gcoeff(A,i,k), gmul(t,gcoeff(A,j,k)));
      b[k] = ladd((GEN)b[k], gmul(t,(GEN)Bi[k]));
    }
  }
}

static void
redallbar(pslqL2_M *Mbar, long i, long jsup)
{
  long j, k, n = Mbar->n;
  double t;
  double *hi = Mbar->H[i], *ai = Mbar->A[i], *hj, *aj;

#if 0
fprintferr("%ld:\n==\n",i);
#endif
  for (j=jsup; j>=1; j--)
  {
    hj = Mbar->H[j];
    t = floor(0.5 + hi[j] / hj[j]);
    if (!t) continue;
#if 0
fprintferr("%15.15e ",t);
#endif
    aj = Mbar->A[j];

    Mbar->y[j] += t * Mbar->y[i];
    for (k=1; k<=j; k++) hi[k] -= t * hj[k];
    for (k=1; k<=n; k++) {
      ai[k]         -= t * aj[k];
      Mbar->B[k][j] += t * Mbar->B[k][i];
    }
#if 0
fprintferr("  %ld:\n",j); dprintmat(Mbar->H,n,n-1);
#endif
  }
}

static long
vecabsminind(GEN v)
{
  long l = lg(v), m = 1, i;
  GEN t, la = mpabs((GEN)v[1]);
  for (i=2; i<l; i++)
  {
    t = mpabs((GEN)v[i]);
    if (mpcmp(t,la) < 0) { la = t; m = i; }
  }
  return m;
}

static long
vecmaxind(GEN v)
{
  long l = lg(v), m = 1, i;
  GEN t, la = (GEN)v[1];
  for (i=2; i<l; i++)
  {
    t = (GEN)v[i];
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
  GEN ma = gzero, s;

  for (i=1; i<=n; i++)
  {
    s = gzero;
    for (j=1; j<n; j++) s = gadd(s, gnorm(gcoeff(M->H,i,j)));
    ma = gmax(ma, s);
  }
  return gsqrt(ma, DEFAULTPREC);
}

static void
init_timer(pslq_timer *T)
{
  T->vmind = T->t12 = T->t1234 = T->reda = T->fin = T->ct = 0;
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

  if (! is_vec_t(tx)) err(typeer,"pslq");
  /* check trivial cases */
  for (k = 1; k <= n; k++)
    if (gcmp0((GEN)x[k])) return vec_ei(n, k);
  if (n <= 1) return cgetg(1, t_COL);
  prec = gprecision(x)-1;
  if (prec < 0)
  { /* exact components */
    pari_sp av = avma;
    GEN im, U = NULL;
    x = Q_primpart(x);
    im = gimag(x);
    if (!gcmp0(im))
    {
      U = (GEN)extendedgcd(im)[2];
      setlg(U, lg(U)-1); /* remove last column */
      x = gmul(greal(x), U);
      if (n == 2) /* x has a single component */
        return gcmp0((GEN)x[1])? (GEN)U[1]: cgetg(1, t_COL);
    }
    x = (GEN)extendedgcd(x)[2];
    x = (GEN)x[1];
    if (U) x = gmul(U, x);
    return gerepilecopy(av, x);
  }
  if (prec < DEFAULTPREC) prec = DEFAULTPREC;
  *PREC = prec;
  M->EXP = - bit_accuracy(prec) + max(2*n, 32);
  M->flreal = is_zero(gimag(x), M->EXP, prec);
  if (!M->flreal)
    return lindep(x,prec); /* FIXME */
  else
    x = greal(x);

  if (DEBUGLEVEL>=3) { (void)timer(); init_timer(M->T); }
  x = col_to_MP(x, prec); settyp(x,t_VEC);
  M->n = n;
  M->A = idmat(n);
  M->B = idmat(n);
  s1 = cgetg(lx,t_VEC); s1[n] = lnorm((GEN)x[n]);
  s  = cgetg(lx,t_VEC); s[n]  = (long)gabs((GEN)x[n],prec);
  for (k=n-1; k>=1; k--)
  {
    s1[k] = ladd((GEN)s1[k+1], gnorm((GEN)x[k]));
    s[k]  = (long)gsqrt((GEN)s1[k], prec);
  }
  sinv = ginv((GEN)s[1]);
  s    = gmul(sinv,s);
  M->y = gmul(sinv, x);
  M->H = cgetg(n,t_MAT);
  for (j=1; j<n; j++)
  {
    GEN d, c = cgetg(lx,t_COL);

    M->H[j] = (long)c;
    for (i=1; i<j; i++) c[i] = zero;
    c[j] = ldiv((GEN)s[j+1],(GEN)s[j]);
    d = gneg( gdiv((GEN)M->y[j], gmul((GEN)s[j],(GEN)s[j+1]) ));
    for (i=j+1; i<=n; i++) c[i] = lmul(gconj((GEN)M->y[i]), d);
  }
  for (i=2; i<=n; i++) redall(M, i, i-1);
  return NULL;
}

static void
SWAP(pslq_M *M, long m)
{
  long j, n = M->n;
  swap(M->y[m], M->y[m+1]);
  swap(M->B[m], M->B[m+1]);
  for (j=1; j<=n; j++) swap(coeff(M->A,m,j), coeff(M->A,m+1,j));
  for (j=1; j<n;  j++) swap(coeff(M->H,m,j), coeff(M->H,m+1,j));
}

#define dswap(x,y) { double _t=x; x=y; y=_t; }
#define ddswap(x,y) { double* _t=x; x=y; y=_t; }

static void
SWAPbar(pslqL2_M *M, long m)
{
  long j, n = M->n;
  dswap(M->y[m], M->y[m+1]);
  ddswap(M->A[m], M->A[m+1]);
  ddswap(M->H[m], M->H[m+1]);
  for (j=1; j<=n; j++) dswap(M->B[j][m], M->B[j][m+1]);
}

static GEN
one_step_gen(pslq_M *M, GEN tabga, long prec)
{
  GEN H = M->H, p1;
  long n = M->n, i, m;

  p1 = cgetg(n,t_VEC);
  for (i=1; i<n; i++) p1[i] = lmul((GEN)tabga[i], gabs(gcoeff(H,i,i),prec));
  m = vecmaxind(p1);
  if (DEBUGLEVEL>3) M->T->vmind += timer();
  SWAP(M, m);
  if (m <= n-2)
  {
    GEN tinv, t3, t4, t1c, t2c, t1 = gcoeff(H,m,m), t2 = gcoeff(H,m,m+1);
    tinv = ginv( gsqrt(gadd(gnorm(t1), gnorm(t2)), prec) );
    t1 = gmul(t1, tinv);
    t2 = gmul(t2, tinv);
    if (M->flreal) { t1c = t1; t2c = t2; }
    else           { t1c = gconj(t1); t2c = gconj(t2); }
    if (DEBUGLEVEL>3) M->T->t12 += timer();
    for (i=m; i<=n; i++)
    {
      t3 = gcoeff(H,i,m);
      t4 = gcoeff(H,i,m+1);
      coeff(H,i,m)  = ladd(gmul(t1c,t3), gmul(t2c,t4));
      coeff(H,i,m+1)= lsub(gmul(t1, t4), gmul(t2, t3));
    }
    if (DEBUGLEVEL>3) M->T->t1234 += timer();
  }
  for (i=1; i<n; i++)
    if (is_zero(gcoeff(H,i,i), M->EXP, prec)) {
      m = vecabsminind(M->y); return (GEN)M->B[m];
    }
  for (i=m+1; i<=n; i++) redall(M, i, min(i-1,m+1));

  if (DEBUGLEVEL>3) M->T->reda += timer();
  if (gexpo(M->A) >= -M->EXP) return ginv(maxnorml2(M));
  m = vecabsminind(M->y);
  if (is_zero((GEN)M->y[m], M->EXP, prec)) return (GEN)M->B[m];

  if (DEBUGLEVEL>2)
  {
    if (DEBUGLEVEL>3) M->T->fin += timer();
    M->T->ct++;
    if ((M->T->ct&0xff) == 0)
    {
      if (DEBUGLEVEL == 3)
        fprintferr("time for ct = %ld : %ld\n",M->T->ct,timer());
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
  GEN ga = mpsqrt( flreal? divrs(stor(4, prec), 3): stor(2, prec) );
  GEN tabga = cgetg(n,t_VEC);
  long i;
  tabga[1] = (long)ga;
  for (i = 2; i < n; i++) tabga[i] = lmul((GEN)tabga[i-1],ga);
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
  if (DEBUGLEVEL>=3) printf("Initialization time = %ld\n",timer());
  for (;;)
  {
    if ((p1 = one_step_gen(&M, tabga, prec)))
      return gerepilecopy(av0, p1);

    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"pslq");
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

void
dprintvec(double *V, long m)
{
  long i;
  fprintferr("[");
  for (i=1; i<m; i++) fprintferr("%15.15e, ",V[i]);
  fprintferr("%15.15e]\n",V[m]); pariflush();
}

void
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
  fprintferr("%15.15e]\n",M[r][c]); pariflush();
}

static long
initializedoubles(pslqL2_M *Mbar, pslq_M *M, long prec)
{
  long i, j, n = Mbar->n;
  GEN ypro;
  pari_sp av = avma;

  ypro = gdiv(M->y, vecmax(gabs(M->y,prec)));
  for (i=1; i<=n; i++)
  {
    if (gexpo((GEN)ypro[i]) < -0x3ff) return 0;
    Mbar->y[i] = rtodbl((GEN)ypro[i]);
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
    if (expodb(Mbar->y[i]) < -46) return 0;
    p1 = Mbar->A[i];
    p2 = Mbar->B[i];
    for (j=1; j<=n; j++)
      if (expodb(p1[j]) > 43 || expodb(p2[j]) > 43) return 0;
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
      if (expodb(p1[j]) >= 52 || expodb(p2[j]) >= 52) return 0;
      coeff(Abargen,i,j) = (long)mpent(dbltor(p1[j]));
      coeff(Bbargen,i,j) = (long)mpent(dbltor(p2[j]));
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
      return (GEN)M->B[m];
    }
  if (gexpo(M->A) >= -M->EXP)
    return ginv( maxnorml2(M) );
  m = vecabsminind(M->y);
  if (is_zero((GEN)M->y[m], M->EXP, prec)) return (GEN)M->B[m];
  return NULL;
}

GEN
pslqL2(GEN x)
{
  GEN Abargen, Bbargen, tabga, p1;
  long lx = lg(x), n = lx-1, i, m, ctpro, flreal, flit, prec;
  pari_sp av0 = avma, lim = stack_lim(av0,1), av;
  double *tabgabar, gabar, tinvbar, t1bar, t2bar, t3bar, t4bar;
  double **Pbar, **Abar, **Bbar, **Hbar, *ybar;
  pslqL2_M Mbar, Mbarst;
  pslq_M M;
  pslq_timer T; M.T = &T;

  p1 = init_pslq(&M, x, &prec);
  if (p1) return p1;

  flreal = M.flreal;
  tabga = get_tabga(flreal, n, prec);
  Abargen = idmat(n);
  Bbargen = idmat(n);

  Mbarst.n = Mbar.n = n;
  Mbar.A = Abar = (double**)new_chunk(n+1);
  Mbar.B = Bbar = (double**)new_chunk(n+1);
  Mbar.H = Hbar = (double**)new_chunk(n+1);
  Mbarst.A = (double**)new_chunk(n+1);
  Mbarst.B = (double**)new_chunk(n+1);
  Mbarst.H = (double**)new_chunk(n+1);
  Pbar   = (double**)new_chunk(n);

  tabgabar = dalloc((n+1)*sizeof(double));
  Mbar.y = ybar = dalloc((n+1)*sizeof(double));
  Mbarst.y = dalloc((n+1)*sizeof(double));

  Mbar.W = dalloc((n+1)*sizeof(double));
  for (i=1; i< n; i++)  Pbar[i] = dalloc((n+1)*sizeof(double));
  for (i=1; i<=n; i++)  Abar[i] = dalloc((n+1)*sizeof(double));
  for (i=1; i<=n; i++)  Bbar[i] = dalloc((n+1)*sizeof(double));
  for (i=1; i<=n; i++)  Hbar[i] = dalloc(n*sizeof(double));
  for (i=1; i<=n; i++) Mbarst.A[i] = dalloc((n+1)*sizeof(double));
  for (i=1; i<=n; i++) Mbarst.B[i] = dalloc((n+1)*sizeof(double));
  for (i=1; i<=n; i++) Mbarst.H[i] = dalloc(n*sizeof(double));

  gabar = gtodouble((GEN)tabga[1]); tabgabar[1] = gabar;
  for (i=2; i<n; i++) tabgabar[i] = tabgabar[i-1]*gabar;

  av = avma;
  if (DEBUGLEVEL>=3) printf("Initialization time = %ld\n",timer());
RESTART:
  flit = initializedoubles(&Mbar, &M, prec);
  storeprecdoubles(&Mbarst, &Mbar);
  if (flit) dLQdec(&Mbar, Pbar);
  ctpro = 0;
  for (;;)
  {
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"pslq");
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
	if (DEBUGLEVEL>=4) T.t12 += timer();
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
	if (DEBUGLEVEL>=4) T.t1234 += timer();
      }

      flit = checkentries(&Mbar);
      if (flit)
      {
	storeprecdoubles(&Mbarst, &Mbar);
	for (i=m+1; i<=n; i++) redallbar(&Mbar, i, min(i-1,m+1));
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
          if (! applybar(&M, &Mbar, Abargen,Bbargen)) err(bugparier,"pslqL2");
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
  long i, j, prec = VERYBIGINT, lx = lg(x)-1, ly, v;
  pari_sp av = avma;
  GEN p = NULL, pn,p1,m,a;

  if (lx < 2) return cgetg(1,t_VEC);
  for (i=1; i<=lx; i++)
  {
    p1 = (GEN)x[i];
    if (typ(p1) != t_PADIC) continue;

    j = precp(p1); if (j < prec) prec = j;
    if (!p) p = (GEN)p1[2];
    else if (!egalii(p, (GEN)p1[2]))
      err(talker,"inconsistent primes in plindep");
  }
  if (!p) err(talker,"not a p-adic vector in plindep");
  v = ggval(x,p); pn = gpowgs(p,prec);
  if (v != 0) x = gmul(x, gpowgs(p, -v));
  x = lift_intern(gmul(x, gmodulcp(gun, pn)));

  ly = 2*lx - 1;
  m = cgetg(ly+1,t_MAT);
  for (j=1; j<=ly; j++) m[j] = (long)zerocol(lx);
  a = negi((GEN)x[1]);
  for (i=1; i<lx; i++)
  {
    coeff(m,1+i,i) = (long)a;
    coeff(m,1  ,i) = x[i+1];
  }
  for (i=1; i<=lx; i++) coeff(m,i,lx-1+i) = (long)pn;
  m = lllint_ip(m, 100);
  return gerepilecopy(av, (GEN)m[1]);
}

GEN
algdep0(GEN x, long n, long bit, long prec)
{
  long tx = typ(x), i, k;
  pari_sp av;
  GEN y,p1;

  if (! is_scalar_t(tx)) err(typeer,"algdep0");
  if (tx==t_POLMOD) { y = forcecopy((GEN)x[1]); setvarn(y,0); return y; }
  if (gcmp0(x)) return polx[0];
  if (n <= 0)
  {
    if (!n) return gun;
    err(talker,"negative polynomial degree in algdep");
  }

  av = avma; p1 = cgetg(n+2,t_COL);
  p1[1] = un;
  p1[2] = (long)x; /* n >= 1 */
  for (i=3; i<=n+1; i++) p1[i] = lmul((GEN)p1[i-1],x);
  if (typ(x) == t_PADIC)
    p1 = plindep(p1);
  else
    p1 = lindep0(p1, bit, prec);
  if (typ(p1) == t_REAL) return gerepileupto(av, p1);
  if (lg(p1) < 2) err(talker,"higher degree than expected in algdep");
  y = cgetg(n+3,t_POL);
  y[1] = evalsigne(1) | evalvarn(0);
  k = 1; while (k < n && gcmp0((GEN)p1[k])) k++;
  for (i=0; i<=n+1-k; i++) y[i+2] = p1[k+i];
  (void)normalizepol_i(y, n+4-k);
  y = (gsigne(leading_term(y)) > 0)? gcopy(y): gneg(y);
  return gerepileupto(av,y);
}

GEN
algdep2(GEN x, long n, long bit)
{
  return algdep0(x,n,bit,0);
}

GEN
algdep(GEN x, long n, long prec)
{
  return algdep0(x,n,0,prec);
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
    default: err(flagerr,"matkerint");
  }
  return NULL; /* not reached */
}

GEN
kerint1(GEN x)
{
  pari_sp av = avma;
  return gerepilecopy(av, lllint_ip(matrixqz3(ker(x)), 100));
}

GEN
kerint(GEN x)
{
  pari_sp av = avma;
  GEN fl, junk, h = lllint_i(x, 0, 0, &junk, &fl, NULL);
  if (h) h = lll_finish(h,fl, lll_KER);
  else   h = lll_trivial(x, lll_KER);
  if (lg(h)==1) { avma = av; return cgetg(1, t_MAT); }
  return gerepilecopy(av, lllint_ip(h, 100));
}

/********************************************************************/
/**                                                                **/
/**                              MINIM                             **/
/**                                                                **/
/********************************************************************/
/* x is a non-empty matrix, y is a compatible VECSMALL (dimension > 0). */
GEN
gmul_mat_smallvec(GEN x, GEN y)
{
  long c = lg(x), l = lg(x[1]), i, j;
  pari_sp av;
  GEN z = cgetg(l,t_COL), s;

  for (i=1; i<l; i++)
  {
    av = avma; s = gmulgs(gcoeff(x,i,1),y[1]);
    for (j=2; j<c; j++)
       if (y[j]) s = gadd(s, gmulgs(gcoeff(x,i,j),y[j]));
    z[i] = lpileupto(av,s);
  }
  return z;
}

/* same, x integral */
GEN
gmul_mati_smallvec(GEN x, GEN y)
{
  long c = lg(x), l = lg(x[1]), i, j;
  pari_sp av;
  GEN z = cgetg(l,t_COL), s;

  for (i=1; i<l; i++)
  {
    av = avma; s = mulis(gcoeff(x,i,1),y[1]);
    for (j=2; j<c; j++)
      if (y[j]) s = addii(s, mulis(gcoeff(x,i,j),y[j]));
    z[i] = lpileuptoint(av,s);
  }
  return z;
}

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

/* Minimal vectors for the integral definite quadratic form: a.
 * Result u:
 *   u[1]= Number of vectors of square norm <= BORNE
 *   u[2]= maximum norm found
 *   u[3]= list of vectors found (at most STOCKMAX)
 *
 *  If BORNE = gzero: Minimal non-zero vectors.
 *  flag = min_ALL,   as above
 *  flag = min_FIRST, exits when first suitable vector is found.
 *  flag = min_PERF,  only compute rank of the family of v.v~ (v min.)
 */
static GEN
minim00(GEN a, GEN BORNE, GEN STOCKMAX, long flag)
{
  GEN x,res,p1,u,r,liste,gnorme,invp,V, *gptr[2];
  long n = lg(a), i, j, k, s, maxrank;
  pari_sp av0 = avma, av1, av, tetpil, lim;
  double p,maxnorm,BOUND,*v,*y,*z,**q, eps = 0.000001;

  maxrank = 0; res = V = invp = NULL; /* gcc -Wall */
  switch(flag)
  {
    case min_FIRST:
      if (gcmp0(BORNE)) err(talker,"bound = 0 in minim2");
      res = cgetg(3,t_VEC); break;
    case min_ALL: res = cgetg(4,t_VEC); break;
    case min_PERF: break;
    default: err(talker, "incorrect flag in minim00");
  }
  if (n == 1)
  {
    switch(flag)
    {
      case min_FIRST: avma=av0; return cgetg(1,t_VEC);
      case min_PERF:  avma=av0; return gzero;
    }
    res[1]=res[2]=zero;
    res[3]=lgetg(1,t_MAT); return res;
  }

  av = avma;
  minim_alloc(n, &q, &x, &y, &z, &v);
  av1 = avma;

  u = lllgramint(a);
  if (lg(u) != n)
    err(talker,"not a definite form in minim00");
  a = qf_base_change(a,u,1);

  n--;
  a = mat_to_MP(a, DEFAULTPREC); r = sqred1(a);
  if (DEBUGLEVEL>4) { fprintferr("minim: r = "); outerr(r); }
  for (j=1; j<=n; j++)
  {
    v[j] = rtodbl(gcoeff(r,j,j));
    for (i=1; i<j; i++) q[i][j] = rtodbl(gcoeff(r,i,j));
  }

  if (flag==min_PERF || gcmp0(BORNE))
  {
    double c, b = rtodbl(gcoeff(a,1,1));

    for (i=2; i<=n; i++)
      { c=rtodbl(gcoeff(a,i,i)); if (c<b) b=c; }
    BOUND = b+eps;
    BORNE = ground(dbltor(BOUND));
    maxnorm = -1.; /* don't update maxnorm */
  }
  else
  {
    BORNE = gfloor(BORNE);
    BOUND = gtodouble(BORNE)+eps;
    maxnorm = 0.;
  }

  switch(flag)
  {
    case min_ALL:
      maxrank=itos(STOCKMAX);
      liste = new_chunk(1+maxrank);
      break;
    case min_PERF:
      BORNE = gerepileupto(av1,BORNE);
      maxrank = (n*(n+1))>>1;
      liste = cgetg(1+maxrank, t_VECSMALL);
      V     = cgetg(1+maxrank, t_VECSMALL);
      for (i=1; i<=maxrank; i++) liste[i]=0;
  }

  s=0; av1=avma; lim = stack_lim(av1,1);
  k = n; y[n] = z[n] = 0;
  x[n] = (long) sqrt(BOUND/v[n]);
  if (flag == min_PERF) invp = idmat(maxrank);
  for(;;x[1]--)
  {
    do
    {
      if (k>1)
      {
        long l = k-1;
	z[l]=0;
	for (j=k; j<=n; j++) z[l] += q[l][j]*x[j];
	p = x[k]+z[k];
	y[l] = y[k] + p*p*v[k];
	x[l] = (long) floor(sqrt((BOUND-y[l])/v[l])-z[l]);
        k = l;
      }
      for(;;)
      {
	p = x[k]+z[k];
	if (y[k] + p*p*v[k] <= BOUND) break;
	k++; x[k]--;
      }
    }
    while (k>1);
    if (! x[1] && y[1]<=eps) break;
    p = x[1]+z[1]; p = y[1] + p*p*v[1]; /* norm(x) */
    if (maxnorm >= 0)
    {
      if (flag == min_FIRST)
      {
        gnorme = dbltor(p);
        tetpil=avma; gnorme = ground(gnorme); r = gmul_mati_smallvec(u,x);
        gptr[0]=&gnorme; gptr[1]=&r; gerepilemanysp(av,tetpil,gptr,2);
        res[1]=(long)gnorme;
        res[2]=(long)r; return res;
      }
      if (p > maxnorm) maxnorm = p;
    }
    else
    {
      pari_sp av2 = avma;
      gnorme = ground(dbltor(p));
      if (gcmp(gnorme,BORNE) >= 0) avma = av2;
      else
      {
        BOUND=gtodouble(gnorme)+eps; s=0;
        affii(gnorme,BORNE); avma=av1;
        if (flag == min_PERF) invp = idmat(maxrank);
      }
    }
    s++;

    switch(flag)
    {
      case min_ALL:
        if (s<=maxrank)
        {
          p1 = new_chunk(n+1); liste[s] = (long) p1;
          for (i=1; i<=n; i++) p1[i] = x[i];
        }
        break;

      case min_PERF:
      {
        long I=1;
        pari_sp av2=avma;

        for (i=1; i<=n; i++)
          for (j=i; j<=n; j++,I++) V[I] = x[i]*x[j];
        if (! addcolumntomatrix(V,invp,liste))
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
          if(DEBUGMEM>1) err(warnmem,"minim00, rank>=%ld",s);
          invp = gerepilecopy(av1, invp);
        }
      }
    }
  }
  switch(flag)
  {
    case min_FIRST:
      avma=av0; return cgetg(1,t_VEC);
    case min_PERF:
      if (DEBUGLEVEL>1) { fprintferr("\n"); flusherr(); }
      avma=av0; return stoi(s);
  }
  k = min(s,maxrank);
  r = (maxnorm >= 0) ? ground(dbltor(maxnorm)): BORNE;

  tetpil = avma; p1=cgetg(k+1,t_MAT);
  for (j=1; j<=k; j++)
    p1[j] = (long) gmul_mati_smallvec(u,(GEN)liste[j]);
  liste = p1;

  r=icopy(r); gptr[0]=&r; gptr[1]=&liste;
  gerepilemanysp(av,tetpil,gptr,2);
  res[1]=lstoi(s<<1);
  res[2]=(long)r;
  res[3]=(long)liste; return res;
}

GEN
qfminim0(GEN a, GEN borne, GEN stockmax, long flag, long prec)
{
  switch(flag)
  {
    case 0: return minim00(a,borne,stockmax,min_ALL);
    case 1: return minim00(a,borne,gzero   ,min_FIRST);
    case 2: return fincke_pohst(a,borne,itos(stockmax),0,prec,NULL);
    default: err(flagerr,"qfminim");
  }
  return NULL; /* not reached */
}

GEN
minim(GEN a, GEN borne, GEN stockmax)
{
  return minim00(a,borne,stockmax,min_ALL);
}

GEN
minim2(GEN a, GEN borne, GEN stockmax)
{
  return minim00(a,borne,stockmax,min_FIRST);
}

GEN
perf(GEN a)
{
  return minim00(a,gzero,gzero,min_PERF);
}

/* q is the Gauss reduction (sqred1) of the quadratic form */
/* general program for positive definit quadratic forms (real coeffs).
 * One needs BORNE != 0; LLL reduction done in fincke_pohst().
 * If (check != NULL consider only vectors passing the check [ assumes
 *   stockmax > 0 and we only want the smallest possible vectors ] */
static GEN
smallvectors(GEN q, GEN BORNE, long stockmax, FP_chk_fun *CHECK)
{
  long N, n, i, j, k, s, epsbit, prec, checkcnt = 1;
  pari_sp av, av1, lim;
  GEN u,S,x,y,z,v,norme1,normax1,borne1,borne2,eps,p1,alpha,norms,dummy;
  GEN (*check)(void *,GEN) = CHECK? CHECK->f: NULL;
  void *data = CHECK? CHECK->data: NULL;
  int skipfirst = CHECK? CHECK->skipfirst: 0;

  if (DEBUGLEVEL)
    fprintferr("smallvectors looking for norm <= %Z\n",gprec_w(BORNE,3));

  prec = gprecision(q);
  epsbit = bit_accuracy(prec) >> 1;
  eps = real2n(-epsbit, prec);
  alpha = dbltor(0.95);
  normax1 = gzero;
  borne1= gadd(BORNE,eps);
  borne2 = mpmul(borne1,alpha);
  N = lg(q); n = N-1;
  v = cgetg(N,t_VEC);
  dummy = cgetg(1,t_STR);

  av = avma; lim = stack_lim(av,2);
  if (check) norms = cgetg(stockmax+1,t_VEC);
  S = cgetg(stockmax+1,t_VEC);
  x = cgetg(N,t_COL);
  y = cgetg(N,t_COL);
  z = cgetg(N,t_COL);
  for (i=1; i<N; i++) { v[i] = coeff(q,i,i); x[i]=y[i]=z[i] = zero; }

  x[n] = lmpent(mpsqrt(gdiv(borne1,(GEN)v[n])));
  if (DEBUGLEVEL>3) { fprintferr("\nx[%ld] = %Z\n",n,x[n]); flusherr(); }

  s = 0; k = n;
  for(;; x[k] = laddis((GEN)x[k],-1)) /* main */
  {
    do
    {
      int fl = 0;
      if (k > 1)
      {
        av1=avma; k--; p1 = mpmul(gcoeff(q,k,k+1),(GEN)x[k+1]);
	for (j=k+2; j<N; j++)
	  p1 = mpadd(p1, mpmul(gcoeff(q,k,j),(GEN)x[j]));
        z[k] = (long)gerepileuptoleaf(av1,p1);

        av1=avma; p1 = gsqr(mpadd((GEN)x[k+1],(GEN)z[k+1]));
        p1 = mpadd((GEN)y[k+1], mpmul(p1,(GEN)v[k+1]));
	y[k] = (long)gerepileuptoleaf(av1, p1);
        /* reject the [x_1,...,x_skipfirst,0,...,0] */
        if (k <= skipfirst && !signe(y[skipfirst])) goto END;

        av1=avma; p1 = mpsub(borne1, (GEN)y[k]);
	if (signe(p1) < 0) { avma=av1; fl = 1; }
        else
        {
          p1 = mpadd(eps,mpsub(mpsqrt(gdiv(p1,(GEN)v[k])), (GEN)z[k]));
          x[k] = (long)gerepileuptoleaf(av1,mpent(p1));
        }
      }
      for(;; x[k] = laddis((GEN)x[k],-1))
      {
	if (!fl)
	{
          av1 = avma; /* p1 >= 0 */
	  p1 = mpmul((GEN)v[k], gsqr(mpadd((GEN)x[k],(GEN)z[k])));
	  i = mpcmp(mpsub(mpadd(p1,(GEN)y[k]), borne1), gmul2n(p1,-epsbit));
          avma = av1; if (i <= 0) break;
	}
        k++; fl=0;
      }

      if (low_stack(lim, stack_lim(av,2)))
      {
        int cnt = 4;
	if(DEBUGMEM>1) err(warnmem,"smallvectors");
	if (stockmax)
        { /* initialize to dummy values */
          GEN T = S;
          for (i=s+1; i<=stockmax; i++) S[i]=(long)dummy;
          S = gclone(S); if (isclone(T)) gunclone(T);
        }
        if (check)
        {
          cnt+=3;
          for (i=s+1; i<=stockmax; i++) norms[i]=(long)dummy;
        }
	gerepileall(av,cnt,&x,&y,&z,&normax1,&borne1,&borne2,&norms);
      }
      if (DEBUGLEVEL>3)
      {
	if (DEBUGLEVEL>5) fprintferr("%ld ",k);
	if (k==n) fprintferr("\nx[%ld] = %Z\n",n,x[n]);
	flusherr();
      }
    }
    while (k > 1);

    /* x = 0: we're done */
    if (!signe(x[1]) && !signe(y[1])) goto END;

    av1=avma; p1 = gsqr(mpadd((GEN)x[1],(GEN)z[1]));
    norme1 = mpadd((GEN)y[1], mpmul(p1, (GEN)v[1]));
    if (mpcmp(norme1,borne1) > 0) { avma=av1; continue; /* main */ }

    norme1 = gerepileupto(av1,norme1);
    if (check)
    {
      if (checkcnt < 5 && mpcmp(norme1, borne2) < 0)
      {
        if (!check(data,x)) { checkcnt++ ; continue; /* main */}
        borne1 = mpadd(norme1,eps);
        borne2 = mpmul(borne1,alpha);
        s = 0; checkcnt = 0;
      }
    }
    else if (mpcmp(norme1,normax1) > 0) normax1 = norme1;
    if (++s <= stockmax)
    {
      if (check) norms[s] = (long)norme1;
      S[s] = (long)dummycopy(x);
      if (s == stockmax)
      {
        pari_sp av2 = avma;
        GEN per;

        if (!check) goto END;
        per = sindexsort(norms);
        if (DEBUGLEVEL) fprintferr("sorting...\n");
        for (j=0,i=1; i<=s; i++)
        { /* let N be the minimal norm so far for x satisfying 'check'. Keep
           * all elements of norm N */
          long k = per[i];
          norme1 = (GEN)norms[k];
          if (j  && mpcmp(norme1, borne1) > 0) break;
          if (j  || check(data,(GEN)S[k]))
          {
            if (!j) borne1 = mpadd(norme1,eps);
            S[++j] = S[k];
          }
        }
        avma = av2; s = j;
        if (j)
        {
          checkcnt = 0;
          for (i=1; i<=s; i++) norms[i] = (long)norme1;
          borne1 = mpadd(norme1,eps);
          borne2 = mpmul(borne1,alpha);
        }
      }
    }
  }
END:
  if (s < stockmax) stockmax = s;
  if (check)
  {
    GEN per, alph, pols, p;
    if (DEBUGLEVEL) fprintferr("final sort & check...\n");
    s = stockmax;
    setlg(norms,s+1); per = sindexsort(norms);
    alph = cgetg(s+1,t_VEC);
    pols = cgetg(s+1,t_VEC);
    for (j=0,i=1; i<=s; i++)
    {
      long k = per[i];
      norme1 = (GEN)norms[k];
      if (j && mpcmp(norme1, borne1) > 0) break;
      if ((p = check(data,(GEN)S[k])))
      {
        if (!j) borne1 = gadd(norme1,eps);
        j++; pols[j]=(long)p; alph[j]=S[k];
      }
    }
    u = cgetg(3,t_VEC);
    setlg(pols,j+1); u[1] = (long)pols;
    setlg(alph,j+1); u[2] = (long)alph;
    if (isclone(S)) { u[2] = (long)forcecopy(alph); gunclone(S); }
    return u;
  }
  u = cgetg(4,t_VEC);
  u[1] = lstoi(s<<1);
  u[2] = (long)normax1;
  if (stockmax)
  {
    setlg(S,stockmax+1);
    settyp(S,t_MAT);
    if (isclone(S)) { p1 = S; S = forcecopy(S); gunclone(p1); }
  }
  else
    S = cgetg(1,t_MAT);
  u[3] = (long)S; return u;
}

/* solve q(x) = x~.a.x <= bound, a > 0.
 * If check is non-NULL keep x only if check(x).
 * If noer, return NULL in case of precision problems, raise an error otherwise.
 * If a is a vector, assume a[1] is the LLL-reduced Cholesky form of q */
static GEN
_fincke_pohst(GEN a,GEN B0,long stockmax,long noer, long PREC, FP_chk_fun *CHECK)
{
  pari_sp av = avma;
  VOLATILE long i,j,l, round = 0;
  VOLATILE GEN r,rinvtrans,u,v,res,z,vnorm,rperm,perm,uperm, bound = B0;

  if (DEBUGLEVEL>2) fprintferr("entering fincke_pohst\n");
  if (typ(a) == t_VEC)
  {
    r = (GEN)a[1];
    u = NULL;
  }
  else
  {
    long prec = PREC;
    l = lg(a);
    if (l == 1)
    {
      if (CHECK) err(talker, "dimension 0 in fincke_pohst");
      z = cgetg(4,t_VEC);
      z[1] = z[2] = zero;
      z[3] = lgetg(1,t_MAT); return z;
    }
    i = gprecision(a);
    if (i) prec = i; else { a = mat_to_MP(a, prec); round = 1; }
    if (DEBUGLEVEL>2) fprintferr("first LLL: prec = %ld\n", prec);
    u = lllgramintern(a,4,noer, (prec<<1)-2);
    if (!u) return NULL;
    r = qf_base_change(a,u,1);
    r = sqred1intern(r,noer);
    if (!r) return NULL;
    for (i=1; i<l; i++)
    {
      GEN s = gsqrt(gcoeff(r,i,i), prec);
      coeff(r,i,i) = (long)s;
      for (j=i+1; j<l; j++) coeff(r,i,j) = lmul(s, gcoeff(r,i,j));
    }
  }
  /* now r~ * r = a in LLL basis */
  rinvtrans = gtrans_i( invmat(r) );
  if (DEBUGLEVEL>2)
      fprintferr("final LLL: prec = %ld\n", gprecision(rinvtrans));
  v = lllintern(rinvtrans, 100, noer, 0);
  if (!v) return NULL;

  rinvtrans = gmul(rinvtrans, v);
  v = ZM_inv(gtrans_i(v),gun);
  r = gmul(r,v);
  u = u? gmul(u,v): v;

  l = lg(r);
  vnorm = cgetg(l,t_VEC);
  for (j=1; j<l; j++) vnorm[j] = lnorml2((GEN)rinvtrans[j]);
  rperm = cgetg(l,t_MAT);
  uperm = cgetg(l,t_MAT); perm = sindexsort(vnorm);
  for (i=1; i<l; i++) { uperm[l-i] = u[perm[i]]; rperm[l-i] = r[perm[i]]; }

  r = sqred1_from_QR(rperm, gprecision(rperm));
  if (!r) return NULL;

  res = NULL;
  CATCH(precer) { }
  TRY {
    if (CHECK && CHECK->f_init)
    {
      bound = CHECK->f_init(CHECK, r, uperm);
      if (!bound) err(precer,"fincke_pohst");
    }
    if (!bound) bound = QuickNormL2((GEN)r[1], DEFAULTPREC);
    res = smallvectors(r, bound, stockmax, CHECK);
  } ENDCATCH;
  if (DEBUGLEVEL>2) fprintferr("leaving fincke_pohst\n");
  if (CHECK) return res;

  z = cgetg(4,t_VEC);
  z[1] = lcopy((GEN)res[1]);
  z[2] = round? lround((GEN)res[2]): lcopy((GEN)res[2]);
  z[3] = lmul(uperm, (GEN)res[3]); return gerepileupto(av,z);
}

GEN
fincke_pohst(GEN a,GEN B0,long stockmax,long flag, long PREC, FP_chk_fun *CHECK)
{
  pari_sp av = avma;
  GEN z = _fincke_pohst(a,B0,stockmax,flag & 1,PREC,CHECK);
  if (!z)
  {
    if (!(flag & 1)) err(precer,"fincke_pohst");
    avma = av;
  }
  return z;
}
