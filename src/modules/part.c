/* $Id$

Copyright (C) 2002  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/* Original code contributed by: Ralf Stephan (ralf@ark.in-berlin.de).
 *
 * This program is basically the implementation of the script
 *
 * Psi(n, q) = my(a=sqrt(2/3)*Pi/q, b=n-1/24, c=sqrt(b));
 *             (sqrt(q)/(2*sqrt(2)*b*Pi))*(a*cosh(a*c)-(sinh(a*c)/c))
 * L(n,q)=if(q==1,1,sum(h=1,q-1,if(gcd(h,q)==1, cos((g(h,q)-24*h*n)*Pi/(12*q))))
 * g(h, q) = if(q>=3, 12*sum(k=1,q-1,k*(frac(h*k/q)-1/2)))
 *         \\ sumdedekind(h,q)*12*q
 * part(n) = round(sum(q=1,5 + 0.24*sqrt(n),L(n,q)*Psi(n,q)))
 *
 * only faster. It is a translation of the C/mpfr version at
 * http://www.ark.in-berlin.de/part.c
 *
 * ------------------------------------------------------------------
 *   The first restriction depends on Pari's maximum precision of floating
 * point reals, which is 268435454 bits in 2.2.4, since the algorithm needs
 * high precision exponentials. For that engine, the maximum possible argument
 * would be in [5*10^15,10^16], the computation of which would need days on
 * a ~1-GHz computer. */

#include "pari.h"
#include "paripriv.h"

/****************************************************************/

/* Given:  b = N-1/24;
 *   c = sqrt(2/3)*Pi*sqrt(b)
 *   d = 1 / ((2*b)^(3/2) * Pi);
 *
 * Psi(N, q) = my(a = c/q); sqrt(q) * (a*cosh(a) - sinh(a)) */
static GEN
psi(GEN c, ulong q, long prec)
{
  GEN a = divru(c, q), ea = mpexp(a), invea = invr(ea);
  GEN cha = shiftr(addrr(ea, invea), -1);  /* ch(a) */
  GEN sha = shiftr(subrr(ea, invea), -1);  /* sh(a) */
  return mulrr(sqrtr(stor(q,prec)), subrr(mulrr(a,cha), sha));
}

/* g(h, q) = if(q>=3, 12*sum(k=1,q-1,k*(frac(h*k/q)-1/2)))
 *   \\ this is an integer = sumdedekind(h,q)*12*q
 * assume h < q and (h,q) = 1. Not memory clean. */
static GEN
g(ulong h, ulong q)
{
  long s1, s2;
  GEN v;

  if (q < 3)  return gen_0;
  if (h == 1) return muluu(q-1,q-2);
  if (h == 2) return q == 3? gen_m2: muluu(q-1,(q-5)>>1);
  v = u_sumdedekind_coprime(h, q);
  s1 = v[1];
  s2 = v[2];
  return addis(mulss(q,s1), s2);
}

/* L(n,q)=if(q==1,1,sum(h=1,q-1,if(gcd(h,q)==1, cos((g(h,q)-24*h*n)*Pi/(12*q))))
 * Never called with q < 3, so ignore this case */
static GEN
L(GEN n, ulong q, long bitprec)
{
  long pr = nbits2prec(bitprec / q + q);
  ulong h, nmodq = umodiu(n, q), qov2 = q>>1, hn;
  GEN r, res = stor(0, pr), q12 = muluu(q,12), q24 = shifti(q12,1);
  GEN pi_q = divri(mppi(pr), q12);
  pari_sp av = avma;
  for (h = 1, hn = 0; h <= qov2; h++, avma = av) /* symmetry h <-> q-h */
  {
    GEN t;
    hn += nmodq; if (hn >= q) hn -= q;
    if (ugcd(q, h) > 1) continue;
    r = subii(g(h,q), muluu(hn, 24));
    r = centermodii(r, q24, q12);
    t = isintzero(r)? addrs(res, 1): addrr(res, mpcos(mulri(pi_q,r)));
    affrr(t, res);
  }
  return shiftr(res,1);
}

/* Return a low precision estimate of log p(n). */
static GEN
estim(GEN n)
{
  pari_sp av = avma;
  GEN p1, pi = mppi (DEFAULTPREC);

  p1 = divru( itor(shifti(n,1), DEFAULTPREC), 3 );
  p1 = mpexp( mulrr(pi, sqrtr(p1)) ); /* exp(Pi * sqrt(2N/3)) */
  p1 = divri (shiftr(p1,-2), n);
  p1 = divrr(p1, sqrtr( stor(3,DEFAULTPREC) ));
  return gerepileupto(av, mplog(p1));
}

static void
pinit(GEN n, GEN *c, GEN *d, ulong prec)
{
  GEN b = divru( itor( subis(muliu(n,24), 1), prec ), 24 ); /* n - 1/24 */
  GEN sqrtb = sqrtr(b), Pi = mppi(prec), pi2sqrt2, pisqrt2d3;


  pisqrt2d3 = mulrr(Pi, sqrtr( divru(stor(2, prec), 3) ));
  pi2sqrt2  = mulrr(Pi, sqrtr( stor(8, prec) ));
  *c = mulrr(pisqrt2d3, sqrtb);
  *d = invr( mulrr(pi2sqrt2, mulrr(b,sqrtb)) );
}

/* part(n) = round(sum(q=1,5 + 0.24*sqrt(n), L(n,q)*Psi(n,q))) */
GEN
numbpart(GEN n)
{
  pari_sp ltop = avma, av;
  GEN sum, est, C, D, p1, p2;
  long prec, bitprec;
  ulong q;

  if (typ(n) != t_INT) pari_err_TYPE("partition function",n);
  if (signe(n) < 0) return gen_0;
  if (cmpiu(n, 2) < 0) return gen_1;
  if (cmpii(n, uu32toi(0x38d7e, 0xa4c68000)) >= 0)
    pari_err_OVERFLOW("numbpart [n < 10^15]");
  est = estim(n);
  bitprec = (long)(rtodbl(est)/LOG2) + 32;
  prec = nbits2prec(bitprec);
  pinit(n, &C, &D, prec);
  sum = cgetr (prec); affsr(0, sum);
  /* Because N < 10^16 and q < sqrt(N), q fits into a long
   * In fact q < 2 LONG_MAX / 3 */
  av = avma; togglesign(est);
  for (q = (ulong)(sqrt(gtodouble(n))*0.24 + 5); q >= 3; q--, avma=av)
  {
    GEN t = L(n, q, bitprec);
    if (absr_cmp(t, mpexp(divru(est,q))) < 0) continue;

    t = mulrr(t, psi(gprec_w(C, nbits2prec(bitprec / q + 32)), q, prec));
    affrr(addrr(sum, t), sum);
  }
  p1 = addrr(sum, psi(C, 1, prec));
  p2 = psi(C, 2, prec);
  affrr(mod2(n)? subrr(p1,p2): addrr(p1,p2), sum);
  return gerepileuptoint (ltop, roundr(mulrr(D,sum)));
}

/* for loop over partitions of integer k.
 * nbounds can restrict partitions to have length between nmin and nmax
 * (the length is the number of non zero entries) and
 * abounds restrict to integers between amin and amax.
 *
 * Start from central partition.
 * By default, remove zero entries on the left.
 *
 * Algorithm:
 *
 * A partition of k is an increasing sequence v1,... vn with sum(vi)=k
 * The starting point is the minimal n-partition of k: a,...a,a+1,.. a+1
 * (a+1 is repeated r times with k = a * n + r).
 *
 * The procedure to obtain the next partition:
 * - find the last index i<n such that v{i-1} != v{i} (that is vi is the start
 * of the last constant range excluding vn).
 * - decrease vi by one, and set v{i+1},... v{n} to be a minimal partition (of
 * the right sum).
 *
 * Examples: we highlight the index i
 * 1 1 2 2 3
 *     ^
 * 1 1 1 3 3
 *       ^
 * 1 1 1 2 4
 *       ^
 * 1 1 1 1 5
 * ^
 * 0 2 2 2 3
 *   ^
 * This is recursive in nature. Restrictions on upper bounds of the vi or on
 * the length of the partitions are straightforward to take into account. */

static void
parse_interval(GEN a, long *amin, long *amax)
{
  switch (typ(a))
  {
  case t_INT:
    *amax = itos(a);
    break;
  case t_VEC:
    if (lg(a) != 3)
      pari_err_TYPE("forpart [expect vector of type [amin,amax]]",a);
    *amin = gtos(gel(a,1));
    *amax = gtos(gel(a,2));
    if (*amin>*amax || *amin<0 || *amax<=0)
      pari_err_TYPE("forpart [expect 0<=min<=max, 0<max]",a);
    break;
  default:
    pari_err_TYPE("forpart",a);
  }
}

void
forpart_init(forpart_t *T, long k, GEN abound, GEN nbound)
{
  long n;
  T->amin=1; T->nmin=1;
  if (abound) parse_interval(abound,&T->amin,&T->amax);
  else T->amax = k;
  if (T->amax<=0) T->amax = k;

  T->strip = (T->amin > 0) ? 1 : 0; /* remove leading zeros */

  if (nbound) parse_interval(nbound,&T->nmin,&n);
  else n = k;
  if (T->strip && n>k/T->amin)
    n=k/T->amin; /* strip implies amin>0 */

  T->v = zero_zv(n);
  T->k = k;
}

GEN
forpart_next(forpart_t *T)
{
  GEN v = T->v;
  long n = lg(v)-1;
  long j, ni, q, r;
  long i, s;
  if (n>0 && v[n])
  {
    /* find index to decrease */
    i = n-1; s = v[n];
    while (i>1 && (v[i-1]==v[i] || v[i+1]==T->amax))
      s+= v[i--];
    /* amax condition */
    if ( v[i+1] == T->amax ) return NULL;     /* above amax */
    /* amin condition: stop if below except if strip & try to remove */
    if (!i) return NULL;
    if (v[i] == T->amin) {
      if (!T->strip) return NULL;
      s += v[i]; v[i] = 0;
    } else {
      v[i]--; s++;
    }
    /* zero case... */
    if (v[i] == 0)
    {
      if (T->nmin > n-i) return NULL; /* need too many non zero coeffs */
      /* reduce size of v ? */
      if (T->strip) {
        i = 0; n--;
        setlg(v, n+1);
      }
    }
  } else
  {
    s = T->k;
    i = 0;
    if (s==0)
    {
      if (n==0 && T->nmin==0) {T->nmin++; return v;}
      return NULL;
    }
    if (n*T->amax < s || s < T->nmin*T->amin) return NULL;
  }
  /* set minimal partition of sum s starting from index i */
  ni = n-i;
  q = s / ni;
  r = s % ni;
  for(j=i+1;   j<=n-r; j++) v[j]=q;
  for(j=n-r+1; j<=n;   j++) v[j]=q + 1;
  return v;
}

static long
countpart(long k, GEN abound, GEN nbound)
{
  pari_sp av = avma;
  long n;
  forpart_t T;
  if (k<0) return 0;
  forpart_init(&T, k, abound, nbound);
  for (n=0; forpart_next(&T); n++)
  avma = av;
  return n;
}

GEN
partitions(long k, GEN abound, GEN nbound)
{
  GEN v;
  forpart_t T;
  long i, n = countpart(k,abound,nbound);
  if (n==0) return cgetg(1, t_VEC);
  forpart_init(&T, k, abound, nbound);
  v = cgetg(n+1, t_VEC);
  for (i=1; i<=n; i++)
    gel(v,i)=zv_copy(forpart_next(&T));
  return v;
}

void
forpart(void *E, long call(void*, GEN), long k, GEN abound, GEN nbound)
{
  GEN v;
  forpart_t T;
  forpart_init(&T, k, abound, nbound);
  while ((v=forpart_next(&T)))
    if (call(E, v)) break;
}

void
forpart0(GEN k, GEN code, GEN abound, GEN nbound)
{
  pari_sp av = avma;
  if (typ(k) != t_INT || signe(k)<0) pari_err_TYPE("forpart",k);
  push_lex(gen_0, code);
  forpart((void*)code, &gp_evalvoid, itos(k), abound, nbound);
  pop_lex(1);
  avma=av;
}
