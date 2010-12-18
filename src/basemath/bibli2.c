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

#include "pari.h"
#include "paripriv.h"

/*******************************************************************/
/**                                                               **/
/**                      SPECIAL POLYNOMIALS                      **/
/**                                                               **/
/*******************************************************************/
#ifdef LONG_IS_64BIT
static const long SQRTVERYBIGINT = 3037000500L;   /* ceil(sqrt(LONG_MAX)) */
#else
static const long SQRTVERYBIGINT = 46341L;
#endif

/* Tchebichev polynomial: T0=1; T1=X; T(n)=2*X*T(n-1)-T(n-2)
 * T(n) = (n/2) sum_{k=0}^{n/2} a_k x^(n-2k)
 *   where a_k = (-1)^k 2^(n-2k) (n-k-1)! / k!(n-2k)! is an integer
 *   and a_0 = 2^(n-1), a_k / a_{k-1} = - (n-2k+2)(n-2k+1) / 4k(n-k) */
GEN
polchebyshev1(long n, long v) /* Assume 4*n < LONG_MAX */
{
  long k, l;
  pari_sp av;
  GEN q,a,r;

  if (v<0) v = 0;
  /* polchebyshev(-n,1) = polchebyshev(n,1) */
  if (n < 0) n = -n;
  if (n==0) return pol_1(v);
  if (n==1) return pol_x(v);

  q = cgetg(n+3, t_POL); r = q + n+2;
  a = int2n(n-1);
  gel(r--,0) = a;
  gel(r--,0) = gen_0;
  if (n < SQRTVERYBIGINT)
    for (k=1,l=n; l>1; k++,l-=2)
    {
      av = avma;
      a = diviuexact(muliu(a, l*(l-1)), 4*k*(n-k));
      togglesign(a); a = gerepileuptoint(av, a);
      gel(r--,0) = a;
      gel(r--,0) = gen_0;
    }
  else
    for (k=1,l=n; l>1; k++,l-=2)
    {
      av = avma;
      a = diviiexact(mulii(a, muluu(l, l-1)), muluu(4*k, n-k));
      togglesign(a); a = gerepileuptoint(av, a);
      gel(r--,0) = a;
      gel(r--,0) = gen_0;
    }
  q[1] = evalsigne(1) | evalvarn(v);
  return q;
}
static void
polchebyshev1_eval_aux(long n, GEN x, GEN *pt1, GEN *pt2)
{
  GEN t1, t2, b;
  if (n == 1) { *pt1 = gen_1; *pt2 = x; return; }
  if (n == 0) { *pt1 = x; *pt2 = gen_1; return; }
  polchebyshev1_eval_aux((n+1) >> 1, x, &t1, &t2);
  b = gsub(gmul(gmul2n(t1,1), t2), x);
  if (odd(n)) { *pt1 = gadd(gmul2n(gsqr(t1), 1), gen_m1); *pt2 = b; }
  else        { *pt1 = b; *pt2 = gadd(gmul2n(gsqr(t2), 1), gen_m1); }
}
static GEN
polchebyshev1_eval(long n, GEN x)
{
  GEN t1, t2;
  long i, v;
  pari_sp av;

  if (n < 0) n = -n;
  if (n==0) return gen_1;
  if (n==1) return gcopy(x);
  av = avma;
  v = u_lvalrem(n, 2, (ulong*)&n);
  polchebyshev1_eval_aux((n+1)>>1, x, &t1, &t2);
  if (n != 1) t2 = gsub(gmul(gmul2n(t1,1), t2), x);
  for (i = 1; i <= v; i++) t2 = gadd(gmul2n(gsqr(t2), 1), gen_m1);
  return gerepileupto(av, t2);
}

/* Chebychev  polynomial of the second kind U(n,x): the coefficient in front of
 * x^(n-2*m) is (-1)^m * 2^(n-2m)*(n-m)!/m!/(n-2m)!  for m=0,1,...,n/2 */
GEN
polchebyshev2(long n, long v)
{
  pari_sp av;
  GEN q, a, r;
  long m;
  int neg = 0;

  if (v<0) v = 0;
  /* polchebyshev(-n,2) = -polchebyshev(n-2,2) */
  if (n < 0) {
    if (n == -1) return zeropol(v);
    neg = 1; n = -n-2;
  }
  if (n==0) return neg ? scalar_ZX_shallow(gen_m1, v): pol_1(v);

  q = cgetg(n+3, t_POL); r = q + n+2;
  a = int2n(n);
  if (neg) togglesign(a);
  gel(r--,0) = a;
  gel(r--,0) = gen_0;
  if (n < SQRTVERYBIGINT)
    for (m=1; 2*m<= n; m++)
    {
      av = avma;
      a = diviuexact(muliu(a, (n-2*m+2)*(n-2*m+1)), 4*m*(n-m+1));
      togglesign(a); a = gerepileuptoint(av, a);
      gel(r--,0) = a;
      gel(r--,0) = gen_0;
    }
  else
    for (m=1; 2*m<= n; m++)
    {
      av = avma;
      a = diviiexact(mulii(a, muluu(n-2*m+2, n-2*m+1)), muluu(4*m, n-m+1));
      togglesign(a); a = gerepileuptoint(av, a);
      gel(r--,0) = a;
      gel(r--,0) = gen_0;
    }
  q[1] = evalsigne(1) | evalvarn(v);
  return q;
}
static void
polchebyshev2_eval_aux(long n, GEN x, GEN *pu1, GEN *pu2)
{
  GEN u1, u2, u, mu1;
  if (n == 1) { *pu1 = gen_1; *pu2 = gmul2n(x,1); return; }
  if (n == 0) { *pu1 = gen_0; *pu2 = gen_1; return; }
  polchebyshev2_eval_aux(n >> 1, x, &u1, &u2);
  mu1 = gneg(u1);
  u = gmul(gadd(u2,u1), gadd(u2,mu1));
  if (odd(n)) { *pu1 = u; *pu2 = gmul(gmul2n(u2,1), gadd(gmul(x,u2), mu1)); }
  else        { *pu2 = u; *pu1 = gmul(gmul2n(u1,1), gadd(u2, gmul(x,mu1))); }
}
static GEN
polchebyshev2_eval(long n, GEN x)
{
  GEN u1, u2, mu1;
  long neg = 0;
  pari_sp av;

  if (n < 0) {
    if (n == -1) return gen_0;
    neg = 1; n = -n-2;
  }
  if (n==0) return neg ? gen_m1: gen_1;
  av = avma;
  polchebyshev2_eval_aux(n>>1, x, &u1, &u2);
  mu1 = gneg(u1);
  if (odd(n)) u2 = gmul(gmul2n(u2,1), gadd(gmul(x,u2), mu1));
  else        u2 = gmul(gadd(u2,u1), gadd(u2,mu1));
  if (neg) u2 = gneg(u2);
  return gerepileupto(av, u2);
}

GEN
polchebyshev(long n, long kind, long v)
{
  switch (kind)
  {
    case 1: return polchebyshev1(n, v);
    case 2: return polchebyshev2(n, v);
    default: pari_err(flagerr, "polchebyshev");
  }
  return NULL; /* not reached */
}
GEN
polchebyshev_eval(long n, long kind, GEN x)
{
  if (!x) return polchebyshev(n, kind, 0);
  if (gcmpX(x)) return polchebyshev(n, kind, varn(x));
  switch (kind)
  {
    case 1: return polchebyshev1_eval(n, x);
    case 2: return polchebyshev2_eval(n, x);
    default: pari_err(flagerr, "polchebyshev");
  }
  return NULL; /* not reached */
}

/* Hermite polynomial H(n,x):  H(n+1) = 2x H(n) - 2n H(n-1)
 * The coefficient in front of x^(n-2*m) is
 * (-1)^m * n! * 2^(n-2m)/m!/(n-2m)!  for m=0,1,...,n/2.. */
GEN
polhermite(long n, long v)
{
  long m;
  pari_sp av;
  GEN q,a,r;

  if (v<0) v = 0;
  if (n < 0) pari_err(talker,"negative degree in hermite");
  if (n==0) return pol_1(v);

  q = cgetg(n+3, t_POL); r = q + n+2;
  a = int2n(n);
  gel(r--,0) = a;
  gel(r--,0) = gen_0;
  if (n < SQRTVERYBIGINT)
    for (m=1; 2*m<= n; m++)
    {
      av = avma;
      a = diviuexact(muliu(a, (n-2*m+2)*(n-2*m+1)), 4*m);
      togglesign(a);
      gel(r--,0) = gerepileuptoint(av, a);
      gel(r--,0) = gen_0;
    }
  else
    for (m=1; 2*m<= n; m++)
    {
      av = avma;
      a = diviuexact(mulii(a, muluu(n-2*m+2, n-2*m+1)), 4*m);
      togglesign(a);
      gel(r--,0) = gerepileuptoint(av, a);
      gel(r--,0) = gen_0;
    }
  q[1] = evalsigne(1) | evalvarn(v);
  return q;
}
GEN
polhermite_eval(long n, GEN x)
{
  pari_sp av;
  long m;
  GEN a, x2, T;

  if (!x) return polhermite(n, 0);
  if (gcmpX(x)) return polhermite(n, varn(x));
  if (n==0) return gen_1;

  av = avma; x2 = gsqr(x);
  T = a = int2n(n);
  if (n < SQRTVERYBIGINT)
    for (m=1; 2*m<= n; m++)
    {
      T = gmul(T, x2);
      av = avma;
      a = diviuexact(muliu(a, (n-2*m+2)*(n-2*m+1)), 4*m);
      togglesign(a); T = gadd(T, a);
    }
  else
    for (m=1; 2*m<= n; m++)
    {
      T = gmul(T, x2);
      av = avma;
      a = diviuexact(mulii(a, muluu(n-2*m+2, n-2*m+1)), 4*m);
      togglesign(a); T = gadd(T, a);
    }
  if (odd(n)) T = gmul(T,x);
  return gerepileupto(av, T);
}

/* Legendre polynomial
 * L0=1; L1=X; (n+1)*L(n+1)=(2*n+1)*X*L(n)-n*L(n-1)
 * L(n) = 2^-n sum_{k=0}^{n/2} a_k x^(n-2k)
 *   where a_k = (-1)^k (2n-2k)! / k! (n-k)! (n-2k)! is an integer
 *   and a_0 = binom(2n,n), a_k / a_{k-1} = - (n-2k+1)(n-2k+2) / 2k (2n-2k+1) */
GEN
pollegendre(long n, long v)
{
  long k, l;
  pari_sp av;
  GEN a, r, q;

  if (v<0) v = 0;
  /* pollegendre(-n) = pollegendre(n-1) */
  if (n < 0) n = -n-1;
  if (n==0) return pol_1(v);
  if (n==1) return pol_x(v);

  av = avma;
  q = cgetg(n+3, t_POL); r = q + n+2;
  gel(r--,0) = a = binomialuu(n<<1,n);
  gel(r--,0) = gen_0;
  if (n < SQRTVERYBIGINT)
    for (k=1,l=n; l>1; k++,l-=2)
    { /* l = n-2*k+2 */
      av = avma;
      a = diviuexact(muliu(a, l*(l-1)), 2*k*(n+l-1));
      togglesign(a); a = gerepileuptoint(av, a);
      gel(r--,0) = a;
      gel(r--,0) = gen_0;
    }
  else
    for (k=1,l=n; l>1; k++,l-=2)
    { /* l = n-2*k+2 */
      av = avma;
      a = diviiexact(mulii(a, muluu(l, l-1)), muluu(2*k, n+l-1));
      togglesign(a); a = gerepileuptoint(av, a);
      gel(r--,0) = a;
      gel(r--,0) = gen_0;
    }
  q[1] = evalsigne(1) | evalvarn(v);
  return gerepileupto(av, gmul2n(q,-n));
}

GEN
pollegendre_eval(long n, GEN x)
{
  long k, l;
  pari_sp av;
  GEN T, a, x2;

  if (!x) return pollegendre(n, 0);
  if (gcmpX(x)) return pollegendre(n, varn(x));
  /* pollegendre(-n) = pollegendre(n-1) */
  if (n < 0) n = -n-1;
  if (n==0) return gen_1;
  if (n==1) return gcopy(x);

  av = avma; x2 = gsqr(x);
  T = a = binomialuu(n<<1,n);
  if (n < SQRTVERYBIGINT)
    for (k=1,l=n; l>1; k++,l-=2)
    { /* l = n-2*k+2 */
      T = gmul(T, x2);
      av = avma;
      a = diviuexact(muliu(a, l*(l-1)), 2*k*(n+l-1));
      togglesign(a); a = gerepileuptoint(av, a);
      T = gadd(T, a);
    }
  else
    for (k=1,l=n; l>1; k++,l-=2)
    { /* l = n-2*k+2 */
      T = gmul(T, x2);
      av = avma;
      a = diviiexact(mulii(a, muluu(l, l-1)), muluu(2*k, n+l-1));
      togglesign(a); a = gerepileuptoint(av, a);
      T = gadd(T, a);
    }
  if (odd(n)) T = gmul(T,x);
  return gerepileupto(av, gmul2n(T,-n));
}

/* polcyclo(p) = X^(p-1) + ... + 1 */
static GEN
polcyclo_prime(long p, long v)
{
  GEN T = cgetg(p+2, t_POL);
  long i;
  T[1] = evalsigne(1) | evalvarn(v);
  for (i = 2; i < p+2; i++) gel(T,i) = gen_1;
  return T;
}

/* cyclotomic polynomial */
GEN
polcyclo(long n, long v)
{
  long s, q, i, l;
  pari_sp av=avma;
  GEN T, P;

  if (n <= 0) pari_err(talker, "argument must be positive in polcyclo");
  if (v<0) v = 0;
  if (n == 1) return deg1pol_shallow(gen_1, gen_m1, v);
  P = gel(factoru(n), 1); l = lg(P);
  s = P[1]; T = polcyclo_prime(s, v);
  for (i = 2; i < l; i++)
  { /* Phi_{np}(X) = Phi_n(X^p) / Phi_n(X) */
    s *= P[i];
    T = RgX_div(RgX_inflate(T, P[i]), T);
  }
  /* s = squarefree part of n */
  q = n / s;
  if (q == 1) return gerepileupto(av, T);
  return gerepilecopy(av, RgX_inflate(T,q));
}

/* cyclotomic polynomial */
GEN
polcyclo_eval(long n, GEN x)
{
  pari_sp av= avma;
  GEN P, md, xd, yn, yd;
  long l, s, i, j, q, mu, tx;

  if (!x) return polcyclo(n, 0);
  tx = typ(x);
  if (gcmpX(x)) return polcyclo(n, varn(x));
  if (n <= 0) pari_err(talker, "argument must be positive in polcyclo");
  if (n == 1) return gsubgs(x, 1);
  /* n >= 2 */
  P = gel(factoru(n), 1); l = lg(P)-1;
  s = P[1]; for (i = 2; i <= l; i++) s *= P[i];
  q = n/s;
  if (tx == t_INT && is_pm1(x))
  {
    avma = av;
    if (signe(x) > 0 || !odd(q)) return l == 1? utoipos(P[1]): gen_1;
    /* return Phi_s(-1) */
    if (n == 2) return gen_0;
    if (!odd(n) && l == 2) return utoipos(P[2]);
    return gen_1;
  }
  if (q != 1) { x = gpowgs(x, q); n = s; } /* replace n by squarefree part */
  if (tx == t_POL || tx == t_MAT || lg(x) > n)
    return gerepileupto(av, poleval(polcyclo(n,0), x));

  xd = cgetg((1L<<l) + 1, t_VEC); /* the x^d, where d | n */
  md = cgetg((1L<<l) + 1, t_VECSMALL); /* the mu(d), where d | n */
  gel(xd, 1) = x;
  md[1] = 1;
  mu = odd(l)? -1: 1; /* mu(n) */
  if (mu == 1) { yd = gen_1; yn = gsubgs(x,1); }
  else         { yn = gen_1; yd = gsubgs(x,1); }
  for (i = 1; i <= l; i++) /* compute Prod_{d|n} (x^d-1)^mu(n/d) */
  {
    long ti = 1L<<(i-1), p = P[i];
    for (j = 1; j <= ti; j++) {
      GEN X = gpowgs(gel(xd,j), p);
      gel(xd,ti+j) = X;
      md[ti+j] = -md[j];
      if (mu == md[ti+j]) yn = gmul(yn, gsubgs(X,1));
      else                yd = gmul(yd, gsubgs(X,1));
    }
  }
  return gerepileupto(av, gdiv(yn,yd));
}
/********************************************************************/
/**                                                                **/
/**                  HILBERT & PASCAL MATRICES                     **/
/**                                                                **/
/********************************************************************/
GEN
mathilbert(long n) /* Hilbert matrix of order n */
{
  long i,j;
  GEN p;

  if (n < 0) pari_err(talker,"negative dimension in mathilbert");
  p = cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++)
  {
    gel(p,j) = cgetg(n+1,t_COL);
    for (i=1+(j==1); i<=n; i++)
      gcoeff(p,i,j) = mkfrac(gen_1, utoipos(i+j-1));
  }
  if (n) gcoeff(p,1,1) = gen_1;
  return p;
}

/* q-Pascal triangle = (choose(i,j)_q) (ordinary binomial if q = NULL) */
GEN
matqpascal(long n, GEN q)
{
  long i, j, I;
  pari_sp av = avma;
  GEN m, qpow = NULL; /* gcc -Wall */

  if (n < -1) pari_err(talker,"Pascal triangle of negative order in matpascal");
  n++; m = cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++) gel(m,j) = cgetg(n+1,t_COL);
  if (q)
  {
    I = (n+1)/2;
    if (I > 1) { qpow = new_chunk(I+1); gel(qpow,2)=q; }
    for (j=3; j<=I; j++) gel(qpow,j) = gmul(q, gel(qpow,j-1));
  }
  for (i=1; i<=n; i++)
  {
    I = (i+1)/2; gcoeff(m,i,1)= gen_1;
    if (q)
    {
      for (j=2; j<=I; j++)
        gcoeff(m,i,j) = gadd(gmul(gel(qpow,j),gcoeff(m,i-1,j)),
                             gcoeff(m,i-1,j-1));
    }
    else
    {
      for (j=2; j<=I; j++)
        gcoeff(m,i,j) = addii(gcoeff(m,i-1,j), gcoeff(m,i-1,j-1));
    }
    for (   ; j<=i; j++) gcoeff(m,i,j) = gcoeff(m,i,i+1-j);
    for (   ; j<=n; j++) gcoeff(m,i,j) = gen_0;
  }
  return gerepilecopy(av, m);
}

/******************************************************************/
/**                                                              **/
/**                       PRECISION CHANGES                      **/
/**                                                              **/
/******************************************************************/

GEN
gprec(GEN x, long l)
{
  long lx, i;
  GEN y;

  if (l <= 0) pari_err(talker,"precision<=0 in gprec");
  switch(typ(x))
  {
    case t_REAL:
      return rtor(x, ndec2prec(l));
    case t_COMPLEX:
      y = cgetg(3, t_COMPLEX);
      gel(y,1) = gprec(gel(x,1),l);
      gel(y,2) = gprec(gel(x,2),l);
      break;
    case t_PADIC:
      if (!signe(x[4])) return zeropadic(gel(x,2), l+precp(x));
      y=cgetg(5,t_PADIC);
      y[1]=x[1]; setprecp(y,l);
      gel(y,2) = icopy(gel(x,2));
      gel(y,3) = powiu(gel(x,2),l);
      gel(y,4) = modii(gel(x,4), gel(y,3));
      break;

    case t_SER:
      if (lg(x) == 2) return zeroser(varn(x), l);
      y=cgetg(l+2,t_SER); y[1]=x[1]; l++; i=l;
      lx = lg(x);
      if (l>=lx)
        for ( ; i>=lx; i--) gel(y,i) = gen_0;
      for ( ; i>=2; i--) gel(y,i) = gcopy(gel(x,i));
      break;
   case t_POL:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = gprec(gel(x,i),l);
      break;
    case t_POLMOD: case t_RFRAC: case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = gprec(gel(x,i),l);
      break;
    default: y = gcopy(x);
  }
  return y;
}

/* internal: precision given in word length (including codewords) */
GEN
gprec_w(GEN x, long pr)
{
  long lx, i;
  GEN y;

  switch(typ(x))
  {
    case t_REAL:
      if (signe(x)) return rtor(x,pr);
      i = -bit_accuracy(pr);
      if (i < expo(x)) return real_0_bit(i);
      y = cgetr(2); y[1] = x[1]; return y;
    case t_COMPLEX:
      y = cgetg(3, t_COMPLEX);
      gel(y,1) = gprec_w(gel(x,1),pr);
      gel(y,2) = gprec_w(gel(x,2),pr);
      break;
   case t_POL: case t_SER:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = gprec_w(gel(x,i),pr);
      break;
    case t_POLMOD: case t_RFRAC: case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = gprec_w(gel(x,i),pr);
      break;
    default: return x;
  }
  return y;
}

/* internal: precision given in word length (including codewords), truncate
 * mantissa to precision 'pr' but never _increase_ it */
GEN
gprec_wtrunc(GEN x, long pr)
{
  long lx, i;
  GEN y;

  switch(typ(x))
  {
    case t_REAL:
      return (signe(x) && lg(x) > pr)? rtor(x,pr): x;
    case t_COMPLEX:
      y = cgetg(3, t_COMPLEX);
      gel(y,1) = gprec_wtrunc(gel(x,1),pr);
      gel(y,2) = gprec_wtrunc(gel(x,2),pr);
      break;
    case t_POL:
    case t_SER:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = gprec_wtrunc(gel(x,i),pr);
      break;
    case t_POLMOD: case t_RFRAC: case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = gprec_wtrunc(gel(x,i),pr);
      break;
    default: return x;
  }
  return y;
}

/********************************************************************/
/**                                                                **/
/**                      SERIES TRANSFORMS                         **/
/**                                                                **/
/********************************************************************/
/**                  LAPLACE TRANSFORM (OF A SERIES)               **/
/********************************************************************/
GEN
laplace(GEN x)
{
  pari_sp av = avma;
  long i, l = lg(x), e = valp(x);
  GEN y, t;

  if (typ(x) != t_SER) pari_err(talker,"not a series in laplace");
  if (e < 0) pari_err(talker,"negative valuation in laplace");
  y = cgetg(l,t_SER);
  t = mpfact(e); y[1] = x[1];
  for (i=2; i<l; i++)
  {
    gel(y,i) = gmul(t, gel(x,i));
    e++; t = mului(e,t);
  }
  return gerepilecopy(av,y);
}

/********************************************************************/
/**              CONVOLUTION PRODUCT (OF TWO SERIES)               **/
/********************************************************************/
GEN
convol(GEN x, GEN y)
{
  long j, lx, ly, ex, ey, vx = varn(x);
  GEN z;

  if (typ(x) != t_SER || typ(y) != t_SER) pari_err(talker,"not a series in convol");
  if (varn(y) != vx) pari_err(talker,"different variables in convol");
  ex = valp(x); lx = lg(x) + ex; x -= ex;
  ey = valp(y); ly = lg(y) + ey; y -= ey;
  /* inputs shifted: x[i] and y[i] now correspond to monomials of same degree */
  if (ly < lx) lx = ly; /* min length */
  if (ex < ey) ex = ey; /* max valuation */
  if (lx - ex < 3) return zeroser(vx, lx-2);

  z = cgetg(lx - ex, t_SER);
  z[1] = evalvalp(ex) | evalvarn(vx);
  for (j = ex+2; j<lx; j++) gel(z,j-ex) = gmul(gel(x,j),gel(y,j));
  return normalize(z);
}

/***********************************************************************/
/*               OPERATIONS ON DIRICHLET SERIES: *, /                  */
/* (+, -, scalar multiplication are done on the corresponding vectors) */
/***********************************************************************/
static long
dirval(GEN x)
{
  long i = 1, lx = lg(x);
  while (i < lx && gequal0(gel(x,i))) i++;
  return i;
}

GEN
dirmul(GEN x, GEN y)
{
  pari_sp av = avma, lim = stack_lim(av, 1);
  long lx, ly, lz, dx, dy, i, j, k;
  GEN z;

  if (typ(x)!=t_VEC || typ(y)!=t_VEC) pari_err(typeer,"dirmul");
  dx = dirval(x); lx = lg(x);
  dy = dirval(y); ly = lg(y);
  if (ly-dy < lx-dx) { swap(x,y); lswap(lx,ly); lswap(dx,dy); }
  lz = minss(lx*dy,ly*dx);
  z = zerovec(lz-1);
  for (j=dx; j<lx; j++)
  {
    GEN c = gel(x,j);
    if (gequal0(c)) continue;
    if (gequal1(c))
      for (k=dy,i=j*dy; i<lz; i+=j,k++) gel(z,i) = gadd(gel(z,i),gel(y,k));
    else
    {
      if (gequalm1(c))
        for (k=dy,i=j*dy; i<lz; i+=j,k++) gel(z,i) = gsub(gel(z,i),gel(y,k));
      else
        for (k=dy,i=j*dy; i<lz; i+=j,k++) gel(z,i) = gadd(gel(z,i),gmul(c,gel(y,k)));
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGLEVEL) fprintferr("doubling stack in dirmul\n");
      z = gerepilecopy(av,z);
    }
  }
  return gerepilecopy(av,z);
}

GEN
dirdiv(GEN x, GEN y)
{
  pari_sp av = avma;
  long lx,ly,lz,dx,dy,i,j;
  GEN z,p1;

  if (typ(x)!=t_VEC || typ(y)!=t_VEC) pari_err(typeer,"dirmul");
  dx = dirval(x); lx = lg(x);
  dy = dirval(y); ly = lg(y);
  if (dy != 1 || ly == 1) pari_err(talker,"not an invertible dirseries in dirdiv");
  lz = minss(lx,ly*dx); p1 = gel(y,1);
  if (!gequal1(p1)) { y = gdiv(y,p1); x = gdiv(x,p1); } else x = leafcopy(x);
  z = zerovec(lz-1);
  for (j=dx; j<lz; j++)
  {
    p1=gel(x,j); gel(z,j) = p1;
    if (gequal0(p1)) continue;
    if (gequal1(p1))
      for (i=j+j; i<lz; i+=j) gel(x,i) = gsub(gel(x,i),gel(y,i/j));
    else
    {
      if (gequalm1(p1))
        for (i=j+j; i<lz; i+=j) gel(x,i) = gadd(gel(x,i),gel(y,i/j));
      else
        for (i=j+j; i<lz; i+=j) gel(x,i) = gsub(gel(x,i),gmul(p1,gel(y,i/j)));
    }
  }
  return gerepilecopy(av,z);
}

/*******************************************************************/
/**                                                               **/
/**                       COMBINATORICS                           **/
/**                                                               **/
/*******************************************************************/
/**                      BINOMIAL COEFFICIENTS                    **/
/*******************************************************************/
GEN
binomialuu(ulong n, ulong k)
{
  pari_sp ltop = avma;
  GEN z;
  if (k > n) return gen_0;
  k = minuu(k,n-k);
  if (!k) return gen_1;
  if (k == 1) return utoipos(n);
  z = diviiexact(mulu_interval(n-k+1, n), mulu_interval(2UL, k));
  return gerepileuptoint(ltop,z);
}

GEN
binomial(GEN n, long k)
{
  long i, prec;
  pari_sp av;
  GEN y;

  if (k <= 1)
  {
    if (is_noncalc_t(typ(n))) pari_err(typeer,"binomial");
    if (k < 0) return gen_0;
    if (k == 0) return gen_1;
    return gcopy(n);
  }
  av = avma;
  if (typ(n) == t_INT)
  {
    if (signe(n) > 0)
    {
      GEN z = subis(n,k);
      if (cmpis(z,k) < 0)
      {
        k = itos(z); avma = av;
        if (k <= 1)
        {
          if (k < 0) return gen_0;
          if (k == 0) return gen_1;
          return icopy(n);
        }
      }
    }
    /* k > 1 */
    if (lgefint(n) == 3 && signe(n) > 0)
    {
      y = binomialuu(itou(n),(ulong)k);
      return gerepileupto(av, y);
    }
    else
    {
      y = cgetg(k+1,t_VEC);
      for (i=1; i<=k; i++) gel(y,i) = subis(n,i-1);
      y = divide_conquer_prod(y,mulii);
    }
    y = diviiexact(y, mpfact(k));
    return gerepileuptoint(av, y);
  }

  prec = precision(n);
  if (prec && k > 200 + 0.8*bit_accuracy(prec)) {
    GEN A = mpfactr(k, prec), B = ggamma(gsubgs(n,k-1), prec);
    return gerepileupto(av, gdiv(ggamma(gaddgs(n,1), prec), gmul(A,B)));
  }

  y = cgetg(k+1,t_VEC);
  for (i=1; i<=k; i++) gel(y,i) = gsubgs(n,i-1);
  y = divide_conquer_prod(y,gmul);
  y = gdiv(y, mpfact(k));
  return gerepileupto(av, y);
}

/* Assume n >= 1, return bin, bin[k+1] = binomial(n, k) */
GEN
vecbinome(long n)
{
  long d = (n + 1)/2, k;
  GEN C = cgetg(n+2, t_VEC) + 1; /* C[k] = binomial(n, k) */
  gel(C,0) = gen_1;
  gel(C,1) = utoipos(n);
  for (k=2; k <= d; k++)
  {
    pari_sp av = avma;
    gel(C,k) = gerepileuptoint(av, diviuexact(mului(n-k+1, gel(C,k-1)), k));
  }
  for (   ; k <= n; k++) C[k] = C[n - k];
  return C - 1;
}

/********************************************************************/
/**                  STIRLING NUMBERS                              **/
/********************************************************************/
/* Stirling number of the 2nd kind. The number of ways of partitioning
   a set of n elements into m non-empty subsets. */
GEN
stirling2(ulong n, ulong m)
{
  pari_sp av = avma, lim = stack_lim(av, 2);
  GEN s, bmk;
  ulong k;
  if (n==0) return (m == 0)? gen_1: gen_0;
  if (m > n || m == 0) return gen_0;
  if (m==n) return gen_1;
  /* k = 0 */
  bmk = gen_1; s  = powuu(m, n);
  for (k = 1; k <= ((m-1)>>1); ++k)
  { /* bmk = binomial(m, k) */
    GEN c, kn, mkn;
    bmk = diviuexact(mului(m-k+1, bmk), k);
    kn  = powuu(k, n); mkn = powuu(m-k, n);
    c = odd(m)? subii(mkn,kn): addii(mkn,kn);
    c = mulii(bmk, c);
    s = odd(k)? subii(s, c): addii(s, c);
    if (low_stack(lim, stack_lim(av,2)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"stirling2");
      gerepileall(av, 2, &s, &bmk);
    }
  }
  /* k = m/2 */
  if (!odd(m))
  {
    GEN c;
    bmk = diviuexact(mului(k+1, bmk), k);
    c = mulii(bmk, powuu(k,n));
    s = odd(k)? subii(s, c): addii(s, c);
  }
  return gerepileuptoint(av, diviiexact(s, mpfact(m)));
}

/* Stirling number of the first kind. Up to the sign, the number of
   permutations of n symbols which have exactly m cycles. */
GEN
stirling1(ulong n, ulong m)
{
  pari_sp ltop=avma;
  ulong k;
  GEN s, t;
  if (n < m) return gen_0;
  else if (n==m) return gen_1;
  /* t = binomial(n-1+k, m-1) * binomial(2n-m, n-m-k) */
  /* k = n-m > 0 */
  t = binomialuu(2*n-m-1, m-1);
  s = mulii(t, stirling2(2*(n-m), n-m));
  if (odd(n-m)) togglesign(s);
  for (k = n-m-1; k > 0; --k)
  {
    GEN c;
    t = diviiexact(mulii(t, muluu(n-m+k+1, n+k+1)), muluu(n+k, n-m-k));
    c = mulii(t, stirling2(n-m+k, k));
    s = odd(k)? subii(s, c): addii(s, c);
    if ((k & 0x1f) == 0) {
      t = gerepileuptoint(ltop, t);
      s = gerepileuptoint(avma, s);
    }
  }
  return gerepileuptoint(ltop, s);
}

GEN
stirling(long n, long m, long flag)
{
  if (n<0 || m<0) pari_err(talker, "Negative arguments in stirling");
  switch (flag)
  {
    case 1: return stirling1((ulong)n,(ulong)m);
    case 2: return stirling2((ulong)n,(ulong)m);
    default: pari_err(flagerr,"stirling");
  }
  return NULL; /*NOT REACHED*/
}

/***********************************************************************/
/**                          PERMUTATIONS                             **/
/***********************************************************************/
GEN
numtoperm(long n, GEN x)
{
  pari_sp av;
  ulong i, r;
  GEN v;

  if (n < 0) pari_err(talker,"n too small (%ld) in numtoperm",n);
  if (typ(x) != t_INT) pari_err(arither1);
  v = cgetg(n+1, t_VEC);
  v[1] = 1; av = avma;
  if (signe(x) <= 0) x = modii(x, mpfact(n));
  for (r=2; r<=(ulong)n; r++)
  {
    ulong a;
    x = diviu_rem(x, r,&a);
    for (i=r; i>=a+2; i--) v[i] = v[i-1];
    v[i] = r;
    if ((r & 0x1f) == 0) x = gerepileuptoint(av, x);
  }
  avma = av;
  for (i=1; i<=(ulong)n; i++) gel(v,i) = utoipos(v[i]);
  return v;
}

GEN
permtonum(GEN x)
{
  long lx=lg(x)-1, n=lx, last, ind, tx = typ(x);
  pari_sp av=avma;
  GEN ary,res;

  if (!is_vec_t(tx)) pari_err(talker,"not a vector in permtonum");
  ary = cgetg(lx+1,t_VECSMALL);
  for (ind=1; ind<=lx; ind++)
  {
    res = gel(++x, 0);
    if (typ(res) != t_INT) pari_err(typeer,"permtonum");
    ary[ind] = itos(res);
  }
  ary++; res = gen_0;
  for (last=lx; last>0; last--)
  {
    lx--; ind = lx;
    while (ind>0 && ary[ind] != last) ind--;
    res = addis(muliu(res,last), ind);
    while (ind++ < lx) ary[ind-1] = ary[ind];
  }
  if (!signe(res)) res = mpfact(n);
  return gerepileuptoint(av, res);
}

/*******************************************************************/
/**                                                               **/
/**                     RECIPROCAL POLYNOMIAL                     **/
/**                                                               **/
/*******************************************************************/
/* return coefficients s.t x = x_0 X^n + ... + x_n */
GEN
polrecip(GEN x)
{
  if (typ(x) != t_POL) pari_err(typeer,"polrecip");
  return RgX_recip(x);
}

/********************************************************************/
/**                                                                **/
/**                  POLYNOMIAL INTERPOLATION                      **/
/**                                                                **/
/********************************************************************/
/* X,Y are "spec" GEN vectors with n > 1 components ( at X[0], ... X[n-1] ) */
GEN
polint_i(GEN X, GEN Y, GEN x, long n, GEN *ptdy)
{
  long i, m, ns = 0;
  pari_sp av = avma;
  GEN y, c, d, dy = NULL; /* gcc -Wall */
  int no_dy = 1;

  if (!X)
  {
    X = cgetg(n+1, t_VEC);
    for (i=1; i<=n; i++) gel(X,i) = utoipos(i);
    X++;
  }
  switch(typ(x)) /* FIXME: should only be done if x,X,Y contain t_REALs */
    case t_INT: case t_REAL: case t_FRAC: case t_COMPLEX: case t_QUAD:
    {
      GEN D = NULL;
      no_dy = 0;
      for (i=0; i<n; i++)
      {
        GEN t = gabs(gsub(x,gel(X,i)), DEFAULTPREC);
        if (!D || gcmp(t,D) < 0) { ns = i; D = t; }
      }
      /* X[ns] is closest to x */
    }
  c = new_chunk(n);
  d = new_chunk(n); for (i=0; i<n; i++) c[i] = d[i] = Y[i];
  y = gel(d,ns--);
  /* divided differences */
  for (m=1; m<n; m++)
  {
    for (i=0; i<n-m; i++)
    {
      GEN ho = gsub(gel(X,i),x), hp = gsub(gel(X,i+m),x), den = gsub(ho,hp);
      if (gequal0(den)) pari_err(talker,"two abcissas are equal in polint");
      den = gdiv(gsub(gel(c,i+1),gel(d,i)), den);
      gel(c,i) = gmul(ho,den);
      gel(d,i) = gmul(hp,den);
    }
    dy = (2*(ns+1) < n-m)? gel(c,ns+1): gel(d,ns--);
    y = gadd(y,dy);
  }
  if (!ptdy) return gerepileupto(av, y);
  if (no_dy) { *ptdy = gen_0; return gerepileupto(av, y); }
  *ptdy = dy;
  gerepileall(av, 2, &y, ptdy);
  return y;
}

GEN
polint(GEN X, GEN Y, GEN x, GEN *ptdy)
{
  long tx=typ(X), ty, lx=lg(X);

  if (Y) ty = typ(Y); else { Y = X; ty = tx; X = NULL; }

  if (! is_vec_t(tx) || ! is_vec_t(ty))
    pari_err(talker,"not vectors in polinterpolate");
  if (lx != lg(Y))
    pari_err(talker,"different lengths in polinterpolate");
  if (lx <= 2)
  {
    if (ptdy) *ptdy = gen_0;
    if (lx == 1) return zeropol(0);
    Y = gel(Y,1);
    if (gvar(Y) == 0)
      pari_err(talker,"polynomials in 'x in polinterpolate's data");
    return scalarpol(Y, 0);
  }
  if (!x) x = pol_x(0);
  return polint_i(X? X+1: NULL,Y+1,x,lx-1,ptdy);
}

/********************************************************************/
/**                                                                **/
/**                       MODREVERSE                               **/
/**                                                                **/
/********************************************************************/
/* return y such that Mod(y, charpoly(Mod(a,T)) = Mod(a,T) */
GEN
RgXQ_reverse(GEN a, GEN T)
{
  pari_sp av = avma;
  long n = degpol(T);
  GEN y;

  if (n <= 1) {
    if (n <= 0) return gcopy(a);
    return gerepileupto(av, gneg(gdiv(gel(T,2), gel(T,3))));
  }
  if (typ(a) != t_POL || !signe(a))
    pari_err(talker,"reverse polmod does not exist");

  y = RgXV_to_RgM(RgXQ_powers(a,n-1,T), n);
  y = RgM_solve(y, col_ei(n, 2));
  if (!y) pari_err(talker,"reverse polmod does not exist: Mod(%Ps, %Ps)", a,T);
  return gerepilecopy(av, RgV_to_RgX(y, varn(T)));
}
GEN
QXQ_reverse(GEN a, GEN T)
{
  pari_sp av = avma;
  long n = degpol(T);
  GEN y;

  if (n <= 1) {
    if (n <= 0) return gcopy(a);
    return gerepileupto(av, gneg(gdiv(gel(T,2), gel(T,3))));
  }
  if (typ(a) != t_POL || !signe(a))
    pari_err(talker,"reverse polmod does not exist");

  y = RgXV_to_RgM(QXQ_powers(a,n-1,T), n);
  y = RgM_solve(y, col_ei(n, 2));
  if (!y) pari_err(talker,"reverse polmod does not exist: Mod(%Ps, %Ps)", a,T);
  return gerepilecopy(av, RgV_to_RgX(y, varn(T)));
}

GEN
modreverse(GEN x)
{
  long v, n;
  GEN T, a, y;

  if (typ(x)!=t_POLMOD) pari_err(talker,"not a polmod in modreverse");
  T = gel(x,1); n = degpol(T); if (n <= 0) return gcopy(x);
  a = gel(x,2);
  v = varn(T);
  y = cgetg(3,t_POLMOD);
  gel(y,1) = (n==1)? gsub(pol_x(v), a): RgXQ_charpoly(a, T, v);
  gel(y,2) = RgXQ_reverse(a, T); return y;
}

/********************************************************************/
/**                                                                **/
/**                          MERGESORT                             **/
/**                                                                **/
/********************************************************************/
static int
cmp_small(GEN x, GEN y) {
  long a = (long)x, b = (long)y;
  return a>b? 1: (a<b? -1: 0);
}

struct veccmp_s
{
  GEN k;
  int (*cmp)(GEN,GEN);
};

static int
veccmp(void *data, GEN x, GEN y)
{
  struct veccmp_s *v=(struct veccmp_s *) data;
  long i, s, lk = lg(v->k);

  for (i=1; i<lk; i++)
  {
    s = v->cmp(gel(x,v->k[i]), gel(y,v->k[i]));
    if (s) return s;
  }
  return 0;
}

/* return permutation sorting v[1..n], removing duplicates. Assume n > 0 */
static GEN
gen_sortspec_uniq(GEN v, long n, void *E, int (*cmp)(void*,GEN,GEN))
{
  pari_sp av;
  long NX, nx, ny, m, ix, iy, i;
  GEN x, y, w, W;
  int s;
  switch(n)
  {
    case 1: return mkvecsmall(1);
    case 2:
      s = cmp(E,gel(v,1),gel(v,2));
      if      (s < 0) return mkvecsmall2(1,2);
      else if (s > 0) return mkvecsmall2(2,1);
      return mkvecsmall(1);
    case 3:
      s = cmp(E,gel(v,1),gel(v,2));
      if (s < 0) {
        s = cmp(E,gel(v,2),gel(v,3));
        if (s < 0) return mkvecsmall3(1,2,3);
        else if (s == 0) return mkvecsmall2(1,2);
        s = cmp(E,gel(v,1),gel(v,3));
        if      (s < 0) return mkvecsmall3(1,3,2);
        else if (s > 0) return mkvecsmall3(3,1,2);
        return mkvecsmall2(1,2);
      } else if (s > 0) {
        s = cmp(E,gel(v,1),gel(v,3));
        if (s < 0) return mkvecsmall3(2,1,3);
        else if (s == 0) return mkvecsmall2(2,1);
        s = cmp(E,gel(v,2),gel(v,3));
        if (s < 0) return mkvecsmall3(2,3,1);
        else if (s > 0) return mkvecsmall3(3,2,1);
        return mkvecsmall2(2,1);
      } else {
        s = cmp(E,gel(v,1),gel(v,3));
        if (s < 0) return mkvecsmall2(1,3);
        else if (s == 0) return mkvecsmall(1);
        return mkvecsmall2(3,1);
      }
  }
  NX = nx = n>>1; ny = n-nx;
  av = avma;
  x = gen_sortspec_uniq(v,   nx,E,cmp); nx = lg(x)-1;
  y = gen_sortspec_uniq(v+NX,ny,E,cmp); ny = lg(y)-1;
  w = cgetg(n+1, t_VECSMALL);
  m = ix = iy = 1;
  while (ix<=nx && iy<=ny)
  {
    s = cmp(E, gel(v,x[ix]), gel(v,y[iy]+NX));
    if (s < 0)
      w[m++] = x[ix++];
    else if (s > 0)
      w[m++] = y[iy++]+NX;
    else {
      w[m++] = x[ix++];
      iy++;
    }
  }
  while (ix<=nx) w[m++] = x[ix++];
  while (iy<=ny) w[m++] = y[iy++]+NX;
  avma = av;
  W = cgetg(m, t_VECSMALL);
  for (i = 1; i < m; i++) W[i] = w[i];
  return W;
}

/* return permutation sorting v[1..n]. Assume n > 0 */
static GEN
gen_sortspec(GEN v, long n, void *E, int (*cmp)(void*,GEN,GEN))
{
  long nx, ny, m, ix, iy;
  GEN x, y, w;
  switch(n)
  {
    case 1:
      (void)cmp(E,gel(v,1),gel(v,1)); /* check for type error */
      return mkvecsmall(1);
    case 2:
      return cmp(E,gel(v,1),gel(v,2)) <= 0? mkvecsmall2(1,2)
                                          : mkvecsmall2(2,1);
    case 3:
      if (cmp(E,gel(v,1),gel(v,2)) <= 0) {
        if (cmp(E,gel(v,2),gel(v,3)) <= 0) return mkvecsmall3(1,2,3);
        return (cmp(E,gel(v,1),gel(v,3)) <= 0)? mkvecsmall3(1,3,2)
                                              : mkvecsmall3(3,1,2);
      } else {
        if (cmp(E,gel(v,1),gel(v,3)) <= 0) return mkvecsmall3(2,1,3);
        return (cmp(E,gel(v,2),gel(v,3)) <= 0)? mkvecsmall3(2,3,1)
                                              : mkvecsmall3(3,2,1);
      }
  }
  nx = n>>1; ny = n-nx;
  w = cgetg(n+1,t_VECSMALL);
  x = gen_sortspec(v,   nx,E,cmp);
  y = gen_sortspec(v+nx,ny,E,cmp);
  m = ix = iy = 1;
  while (ix<=nx && iy<=ny)
    if (cmp(E, gel(v,x[ix]), gel(v,y[iy]+nx))<=0)
      w[m++] = x[ix++];
    else
      w[m++] = y[iy++]+nx;
  while (ix<=nx) w[m++] = x[ix++];
  while (iy<=ny) w[m++] = y[iy++]+nx;
  avma = (pari_sp)w; return w;
}

static void
init_sort(GEN *x, long *tx, long *lx)
{
  *tx = typ(*x);
  if (*tx == t_LIST) {
    *x = list_data(*x);
    *lx = *x? lg(*x): 1;
  } else {
    if (!is_matvec_t(*tx) && *tx != t_VECSMALL) pari_err(typeer,"gen_sort");
    *lx = lg(*x);
  }
}

/* (x o y)[1..lx-1], destroy y */
INLINE GEN
sort_extract(GEN x, GEN y, long tx, long lx)
{
  long i;
  switch(tx)
  {
    case t_VECSMALL:
      for (i=1; i<lx; i++) y[i] = x[y[i]];
      break;
    case t_LIST:
      settyp(y,t_VEC);
      for (i=1; i<lx; i++) gel(y,i) = gel(x,y[i]);
      return gtolist(y);
    default:
      settyp(y,tx);
      for (i=1; i<lx; i++) gel(y,i) = gcopy(gel(x,y[i]));
  }
  return y;
}

/* Sort the vector x, using cmp to compare entries. */
GEN
gen_sort_uniq(GEN x, void *E, int (*cmp)(void*,GEN,GEN))
{
  long tx, lx;
  GEN y;

  init_sort(&x, &tx, &lx);
  if (lx==1) return tx == t_LIST? listcreate(): cgetg(1, tx);
  y = gen_sortspec_uniq(x,lx-1,E,cmp);
  return sort_extract(x, y, tx, lg(y)); /* lg(y) <= lx */
}
/* Sort the vector x, using cmp to compare entries. */
GEN
gen_sort(GEN x, void *E, int (*cmp)(void*,GEN,GEN))
{
  long tx, lx;
  GEN y;

  init_sort(&x, &tx, &lx);
  if (lx==1) return tx == t_LIST? listcreate(): cgetg(1, tx);
  y = gen_sortspec(x,lx-1,E,cmp);
  return sort_extract(x, y, tx, lx);
}
/* indirect sort: return the permutation that would sort x */
GEN
gen_indexsort_uniq(GEN x, void *E, int (*cmp)(void*,GEN,GEN))
{
  long tx, lx;
  init_sort(&x, &tx, &lx);
  if (lx==1) return cgetg(1, t_VECSMALL);
  return gen_sortspec_uniq(x,lx-1,E,cmp);
}
/* indirect sort: return the permutation that would sort x */
GEN
gen_indexsort(GEN x, void *E, int (*cmp)(void*,GEN,GEN))
{
  long tx, lx;
  init_sort(&x, &tx, &lx);
  if (lx==1) return cgetg(1, t_VECSMALL);
  return gen_sortspec(x,lx-1,E,cmp);
}

/* Sort the vector x in place, using cmp to compare entries */
void
gen_sort_inplace(GEN x, void *E, int (*cmp)(void*,GEN,GEN), GEN *perm)
{
  long tx, lx, i;
  pari_sp av = avma;
  GEN y;

  init_sort(&x, &tx, &lx);
  if (lx<=2)
  {
    if (perm) *perm = lx == 1? cgetg(1, t_VECSMALL): mkvecsmall(1);
    return;
  }
  y = gen_sortspec(x,lx-1, E, cmp);
  if (perm)
  {
    GEN z = new_chunk(lx);
    for (i=1; i<lx; i++) gel(z,i) = gel(x,y[i]);
    for (i=1; i<lx; i++) gel(x,i) = gel(z,i);
    *perm = y;
    avma = (pari_sp)y;
  } else {
    for (i=1; i<lx; i++) gel(y,i) = gel(x,y[i]);
    for (i=1; i<lx; i++) gel(x,i) = gel(y,i);
    avma = av;
  }
}

static int
closurecmp(void *data, GEN x, GEN y)
{
  pari_sp av = avma;
  GEN z = closure_callgen2((GEN)data, x,y);
  if (typ(z) != t_INT)
    pari_err(talker,"comparison function must return an integer");
  avma = av; return signe(z);
}

#define cmp_IND 1
#define cmp_LEX 2
#define cmp_REV 4
#define cmp_UNIQ 8
GEN
vecsort0(GEN x, GEN k, long flag)
{
  int (*CMP)(void*,GEN,GEN);
  int (*cmp)(GEN,GEN) = (flag & cmp_LEX)? &lexcmp: &gcmp;
  void *E;

  if (flag < 0 || flag > (cmp_REV|cmp_LEX|cmp_IND|cmp_UNIQ))
    pari_err(flagerr,"vecsort");
  if (k) {
    long i, j, l, lk, tx, lx;
    struct veccmp_s v;
    GEN y;

    /* cf init_sort */
    tx = typ(x);
    if (tx == t_LIST) {
      y = list_data(x);
      if (!y || (lx = lg(y)) == 1)
        return flag & cmp_IND? cgetg(1, t_VECSMALL): listcreate();
    } else {
      if (!is_matvec_t(tx)) pari_err(typeer,"vecsort");
      y = x; lx = lg(y);
      if (lx == 1)
        return flag & cmp_IND? cgetg(1, t_VECSMALL): cgetg(1, tx);
    }
    switch(typ(k))
    {
      case t_INT: k = mkvecsmall(itos(k)); break;
      case t_VEC: case t_COL: k = ZV_to_zv(k); break;
      case t_VECSMALL: break;
      case t_CLOSURE:
       if (k[1] != 2)
         pari_err(talker,"comparison function needs exactly 2 arguments");
       E = (void*)k;
       CMP = &closurecmp;
       goto END;
      default: pari_err(typeer,"vecsort");
    }
    lk = lg(k);
    for (l=0,i=1; i<lk; i++)
    {
      j = k[i]; if (j<=0) pari_err(talker,"negative index in vecsort");
      if (j>l) l = j;
    }
    for (j=1; j<lx; j++)
    {
      GEN c = gel(y,j);
      long t = typ(c); if (! is_vec_t(t)) pari_err(typeer,"vecsort");
      if (lg(c) <= l) pari_err(talker,"index too large in vecsort");
    }
    v.cmp = cmp;
    v.k = k;
    E = (void*)&v;
    CMP = &veccmp;
  } else {
    E = (void*)((typ(x) == t_VECSMALL)? cmp_small: cmp);
    CMP = &cmp_nodata;
  }
END:
  if (flag & cmp_UNIQ)
    x = flag & cmp_IND? gen_indexsort_uniq(x, E, CMP): gen_sort_uniq(x, E, CMP);
  else
    x = flag & cmp_IND? gen_indexsort(x, E, CMP): gen_sort(x, E, CMP);
  if (flag & cmp_REV) { /* reverse order */
    long j, lx;
    GEN y = (typ(x) == t_LIST)? list_data(x): x;
    lx = lg(y);
    for (j=1; j<=(lx-1)>>1; j++) swap(gel(y,j), gel(y,lx-j));
  }
  return x;
}

GEN
indexsort(GEN x) { return gen_indexsort(x, (void*)&gcmp, cmp_nodata); }
GEN
indexlexsort(GEN x) { return gen_indexsort(x, (void*)&lexcmp, cmp_nodata); }
GEN
indexvecsort(GEN x, GEN k)
{
  struct veccmp_s v; v.cmp = &gcmp; v.k = k;
  if (typ(k) != t_VECSMALL) pari_err(typeer,"vecsort");
  return gen_indexsort(x, (void*)&v, &veccmp);
}

GEN
sort(GEN x) { return gen_sort(x, (void*)gcmp, cmp_nodata); }
GEN
lexsort(GEN x) { return gen_sort(x, (void*)lexcmp, cmp_nodata); }
GEN
vecsort(GEN x, GEN k)
{
  struct veccmp_s v; v.cmp = &gcmp; v.k = k;
  if (typ(k) != t_VECSMALL) pari_err(typeer,"vecsort");
  return gen_sort(x, (void*)&v, &veccmp);
}

GEN
ZV_indexsort(GEN L) { return gen_indexsort(L, (void*)&cmpii, &cmp_nodata); }
GEN
ZV_sort(GEN L) { return gen_sort(L, (void*)&cmpii, &cmp_nodata); }
GEN
ZV_sort_uniq(GEN L) { return gen_sort_uniq(L, (void*)&cmpii, &cmp_nodata); }

/********************************************************************/
/**                      SEARCH IN SORTED VECTOR                   **/
/********************************************************************/
/* index of x in table T, 0 otherwise */
long
tablesearch(GEN T, GEN x, int (*cmp)(GEN,GEN))
{
  long l = 1, u = lg(T)-1, i, s;

  while (u>=l)
  {
    i = (l+u)>>1; s = cmp(x, gel(T,i));
    if (!s) return i;
    if (s<0) u=i-1; else l=i+1;
  }
  return 0;
}

/* looks if x belongs to the set T and returns the index if yes, 0 if no */
long
gen_search(GEN T, GEN x, long flag, void *data, int (*cmp)(void*,GEN,GEN))
{
  long lx = lg(T), i, l, u, s;

  if (lx==1) return flag? 1: 0;
  l = 1; u = lx-1;
  do
  {
    i = (l+u)>>1; s = cmp(data, x, gel(T,i));
    if (!s) return flag? 0: i;
    if (s<0) u=i-1; else l=i+1;
  } while (u>=l);
  if (!flag) return 0;
  return (s<0)? i: i+1;
}

long
ZV_search(GEN x, GEN y) { return tablesearch(x, y, cmpii); }

/********************************************************************/
/**                   COMPARISON FUNCTIONS                         **/
/********************************************************************/
int
cmp_nodata(void *data, GEN x, GEN y)
{
  int (*cmp)(GEN,GEN)=(int (*)(GEN,GEN)) data;
  return cmp(x,y);
}

/* assume lg(x) = lg(y), x,y in Z^n */
int
ZV_cmp(GEN x, GEN y)
{
  long fl,i, lx = lg(x);
  for (i=1; i<lx; i++)
    if (( fl = cmpii(gel(x,i), gel(y,i)) )) return fl;
  return 0;
}
/* assume lg(x) = lg(y), x,y in Z^n */
int
ZV_abscmp(GEN x, GEN y)
{
  long fl,i, lx = lg(x);
  for (i=1; i<lx; i++)
    if (( fl = absi_cmp(gel(x,i), gel(y,i)) )) return fl;
  return 0;
}

/* assume x and y come from the same idealprimedec call (uniformizer unique) */
int
cmp_prime_over_p(GEN x, GEN y)
{
  GEN fx = gel(x,4), fy = gel(y,4);
  long k = fx[2] - fy[2]; /* diff. between residue degree */
  return k? ((k > 0)? 1: -1)
          : ZV_cmp(gel(x,2), gel(y,2));
}

int
cmp_prime_ideal(GEN x, GEN y)
{
  int k = cmpii(gel(x,1), gel(y,1));
  return k? k: cmp_prime_over_p(x,y);
}

/* assume x and y are t_POL in the same variable whose coeffs can be
 * compared (used to sort polynomial factorizations) */
int
gen_cmp_RgX(void *data, GEN x, GEN y)
{
  int (*coeff_cmp)(GEN,GEN)=(int(*)(GEN,GEN))data;
  long i, lx = lg(x), ly = lg(y);
  int fl;
  if (lx > ly) return  1;
  if (lx < ly) return -1;
  for (i=lx-1; i>1; i--)
    if ((fl = coeff_cmp(gel(x,i), gel(y,i)))) return fl;
  return 0;
}

static int
cmp_RgX_Rg(GEN x, GEN y)
{
  long lx = lg(x);
  if (lx > 3) return  1;
  if (lx < 3) return -1;
  return gcmp(gel(x,2), y);
}
int
cmp_RgX(GEN x, GEN y)
{
  if (typ(x) == t_POLMOD) x = gel(x,2);
  if (typ(y) == t_POLMOD) y = gel(y,2);
  if (typ(x) == t_POL) {
    if (typ(y) != t_POL) return cmp_RgX_Rg(x, y);
  } else {
    if (typ(y) != t_POL) return gcmp(x,y);
    return - cmp_RgX_Rg(y,x);
  }
  return gen_cmp_RgX((void*)&gcmp,x,y);
}

/********************************************************************/
/**                   MERGE & SORT FACTORIZATIONS                  **/
/********************************************************************/
/* merge fx, fy two factorizations, whose 1st column is sorted in strictly
 * increasing order wrt cmp. Keep 0 exponents. */
GEN
merge_factor(GEN fx, GEN fy, void *data, int (*cmp)(void *,GEN,GEN))
{
  GEN x = gel(fx,1), e = gel(fx,2), M, E;
  GEN y = gel(fy,1), f = gel(fy,2);
  long ix, iy, m, lx = lg(x), ly = lg(y), l = lx+ly-1;

  M = cgetg(l, t_COL);
  E = cgetg(l, t_COL);

  m = ix = iy = 1;
  while (ix<lx && iy<ly)
  {
    int s = cmp(data, gel(x,ix), gel(y,iy));
    if (s < 0)
    { M[m] = x[ix]; E[m] = e[ix]; ix++; }
    else if (s == 0)
    { M[m] = x[ix]; gel(E,m) = addii(gel(e,ix), gel(f,iy)); iy++; ix++; }
    else
    { M[m] = y[iy]; E[m] = f[iy]; iy++; }
    m++;
  }
  while (ix<lx) { M[m] = x[ix]; E[m] = e[ix]; ix++; m++; }
  while (iy<ly) { M[m] = y[iy]; E[m] = f[iy]; iy++; m++; }
  setlg(M, m);
  setlg(E, m); return mkmat2(M, E);
}

/* sort generic factorization, in place */
GEN
sort_factor(GEN y, void *data, int (*cmp)(void *,GEN,GEN))
{
  GEN a, b, A, B, w;
  pari_sp av;
  long n, i;

  a = gel(y,1); n = lg(a); if (n == 1) return y;
  b = gel(y,2); av = avma;
  A = new_chunk(n);
  B = new_chunk(n);
  w = gen_sortspec(a, n-1, data, cmp);
  for (i=1; i<n; i++) { long k = w[i]; A[i] = a[k]; B[i] = b[k]; }
  for (i=1; i<n; i++) { a[i] = A[i]; b[i] = B[i]; }
  avma = av; return y;
}
/* sort polynomial factorization, in place */
GEN
sort_factor_pol(GEN y,int (*cmp)(GEN,GEN))
{
  (void)sort_factor(y,(void*)cmp, &gen_cmp_RgX);
  return y;
}

/* assume f and g coprime integer factorizations */
GEN
merge_factor_i(GEN f, GEN g)
{
  if (lg(f) == 1) return g;
  if (lg(g) == 1) return f;
  return sort_factor(famat_mul_shallow(f,g), (void*)&cmpii, &cmp_nodata);
}

/***********************************************************************/
/*                                                                     */
/*                          SET OPERATIONS                             */
/*                                                                     */
/***********************************************************************/
static GEN
vectoset(GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx,t_VEC);
  if (lx == 1) return y;
  for (i=1; i<lx; i++) gel(y,i) = GENtoGENstr_nospace(simplify_shallow(gel(x,i)));
  return vecpermute(y, gen_sortspec_uniq(y, lx-1, (void*)&gcmp, cmp_nodata));
}

GEN
gtoset(GEN x)
{
  pari_sp av;
  long tx, lx;
  GEN y;

  if (!x) return cgetg(1, t_VEC);
  tx = typ(x); lx = lg(x);
  if (!is_vec_t(tx))
  {
    if (tx != t_LIST) {
      y = cgetg(2,t_VEC); av = avma;
      gel(y,1) = gerepileupto(av, GENtoGENstr_nospace(simplify_shallow(x)));
      return y;
    }
    x = list_data(x); lx = x? lg(x): 1;
  }
  if (lx==1) return cgetg(1,t_VEC);
  av = avma; return gerepilecopy(av, vectoset(x));
}

long
setisset(GEN x)
{
  long i, lx = lg(x);

  if (typ(x) != t_VEC) return 0;
  if (lx == 1) return 1;
  for (i=1; i<lx; i++)
    if (typ(x[i]) != t_STR) return 0;
  for (i=1; i<lx-1; i++)
    if (strcmp(GSTR(gel(x,i+1)), GSTR(gel(x,i))) <= 0) return 0;
  return 1;
}

long
setsearch(GEN T, GEN y, long flag)
{
  pari_sp av = avma;
  long lx, res;

  switch(typ(T))
  {
    case t_VEC: lx = lg(T); break;
    case t_LIST: T = list_data(T); lx = T? lg(T): 1; break;
    default: pari_err(talker,"not a set in setsearch");
      return 0; /*not reached*/
  }
  if (lx==1) return flag? 1: 0;
  if (typ(y) != t_STR && typ(gel(T,1)) == t_STR)
    y = GENtoGENstr_nospace(simplify_shallow(y));
  res = gen_search(T,y,flag,(void*)gcmp,cmp_nodata);
  avma = av; return res;
}

GEN
setunion(GEN x, GEN y)
{
  pari_sp av = avma;
  long i, j, k, lx = lg(x), ly = lg(y);
  GEN z = cgetg(lx + ly - 1, t_VEC);
  if (typ(x) != t_VEC || typ(y) != t_VEC) pari_err(typeer,"setunion");
  i = j = k = 1;
  while (i<lx && j<ly)
  {
    int s = gcmp(gel(x,i), gel(y,j));
    if (s < 0)
      z[k++] = x[i++];
    else if (s > 0)
      z[k++] = y[j++];
    else {
      z[k++] = x[i++];
      j++;
    }
  }
  while (i<lx) z[k++] = x[i++];
  while (j<ly) z[k++] = y[j++];
  setlg(z, k);
  return gerepilecopy(av, z);
}

GEN
setintersect(GEN x, GEN y)
{
  long ix = 1, iy = 1, iz = 1, lx = lg(x), ly = lg(y);
  pari_sp av = avma;
  GEN z = cgetg(lx,t_VEC);
  if (typ(x) != t_VEC || typ(y) != t_VEC) pari_err(typeer, "setintersect");
  while (ix < lx && iy < ly)
  {
    int c = gcmp(gel(x,ix), gel(y,iy));
    if      (c < 0) ix++;
    else if (c > 0) iy++;
    else { gel(z, iz++) = gel(x,ix); ix++; iy++; }
  }
  setlg(z,iz); return gerepilecopy(av,z);
}

GEN
gen_setminus(GEN A, GEN B, int (*cmp)(GEN,GEN))
{
  pari_sp ltop = avma;
  long i = 1, j = 1, k = 1, lx = lg(A), ly = lg(B);
  GEN  diff = cgetg(lx,t_VEC);
  while (i < lx && j < ly)
    switch ( cmp(gel(A,i),gel(B,j)) )
    {
      case -1: gel(diff,k++) = gel(A,i++); break;
      case 1: j++; break;
      case 0: i++; break;
    }
  while (i < lx) gel(diff,k++) = gel(A,i++);
  setlg(diff,k);
  return gerepilecopy(ltop,diff);
}

GEN
setminus(GEN x, GEN y)
{
  if (typ(x) != t_VEC || typ(y) != t_VEC) pari_err(typeer,"setminus");
  return gen_setminus(x,y,gcmp);
}
