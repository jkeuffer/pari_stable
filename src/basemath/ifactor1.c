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
/**                     INTEGER FACTORIZATION                      **/
/**                                                                **/
/********************************************************************/
#include "pari.h"

/*********************************************************************/
/**                                                                 **/
/**                        PSEUDO PRIMALITY                         **/
/**                                                                 **/
/*********************************************************************/
static GEN sqrt1, sqrt2, t1, t;
static long r1;

/* The following two internal routines don't restore avma -- the caller
   must do so at the end. */
static GEN
init_miller(GEN n)
{
  if (signe(n) < 0) n = absi(n);
  t=addsi(-1,n); r1=vali(t); t1 = shifti(t,-r1);
  sqrt1=cgeti(lg(t)); sqrt1[1]=evalsigne(0)|evallgefint(2);
  sqrt2=cgeti(lg(t)); sqrt2[1]=evalsigne(0)|evallgefint(2);
  return n;
}

/* is n strong pseudo-prime for base a ? `End matching' (check for square
 * roots of -1) added by GN */
/* TODO: If ends do mismatch, then we have factored n, and this information
   should somehow be made available to the factoring machinery. --GN */
static int
bad_for_base(GEN n, GEN a)
{
  long r;
  gpmem_t av=avma, lim=stack_lim(av, 1);
  GEN c2, c = powmodulo(a,t1,n);

  if (!is_pm1(c) && !egalii(t,c)) /* go fishing for -1, not for 1 */
  {
    for (r=r1-1; r; r--)	/* (this saves one squaring/reduction) */
    {
      c2=c; c=resii(sqri(c),n);
      if (egalii(t,c)) break;
      if (low_stack(lim, stack_lim(av,1)))
      {
	GEN *gsav[2]; gsav[0]=&c; gsav[1]=&c2;
	if(DEBUGMEM>1) err(warnmem,"miller(rabin)");
	gerepilemany(av, gsav, 2);
      }
    }
    if (!r) return 1;
    /* sqrt(-1) seen, compare or remember */
    if (signe(sqrt1))		/* we saw one earlier: compare */
    {
      /* check if too many sqrt(-1)s mod n */
      if (!egalii(c2,sqrt1) && !egalii(c2,sqrt2)) return 1;
    }
    else { affii(c2,sqrt1); affii(subii(n,c2),sqrt2); } /* remember */
  }
  return 0;
}

/* Miller-Rabin test for k random bases */
long
millerrabin(GEN n, long k)
{
  long r, i;
  gpmem_t av2, av = avma;

  if (!signe(n)) return 0;
  /* If |n| <= 3, check if n = +- 1 */
  if (lgefint(n)==3 && (ulong)(n[2])<=3) return (n[2] != 1);

  if (!mod2(n)) return 0;
  n = init_miller(n); av2=avma;
  for (i=1; i<=k; i++)
  {
    do r = smodsi(mymyrand(),n); while (!r);
    if (DEBUGLEVEL > 4)
      fprintferr("Miller-Rabin: testing base %ld\n",
		 r);
    if (bad_for_base(n, stoi(r))) { avma=av; return 0; }
    avma=av2;
  }
  avma=av; return 1;
}

/* As above for k bases taken in pr (i.e not random).
 * We must have |n|>2 and 1<=k<=11 (not checked) or k in {16,17} to select
 * some special sets of bases.
 *
 * By computations of Gerhard Jaeschke, `On strong pseudoprimes to several
 * bases', Math.Comp. 61 (1993), 915--926  (see also Chris Caldwell's Prime
 * Number Pages at http://www.utm.edu/research/primes/prove2.html),  we have:
 *
 * k == 4  (bases 2,3,5,7)  correctly detects all composites
 *    n <     118 670 087 467 == 172243 * 688969  with the single exception of
 *    n ==      3 215 031 751 == 151 * 751 * 28351,
 *
 * k == 5  (bases 2,3,5,7,11)  correctly detects all composites
 *    n <   2 152 302 898 747 == 6763 * 10627 * 29947,
 *
 * k == 6  (bases 2,3,...,13)  correctly detects all composites
 *    n <   3 474 749 660 383 == 1303 * 16927 * 157543,
 *
 * k == 7  (bases 2,3,...,17)  correctly detects all composites
 *    n < 341 550 071 728 321 == 10670053 * 32010157,
 * and even this limiting value is caught by an end mismatch between bases
 * 2 and 5 (or 5 and 17).
 *
 * Moreover, the four bases chosen at
 *
 * k == 16  (2,13,23,1662803)  will correctly detect all composites up
 * to at least 10^12, and the combination at
 *
 * k == 17  (31,73)  detects most odd composites without prime factors > 100
 * in the range  n < 2^36  (with less than 250 exceptions, indeed with fewer
 * than 1400 exceptions up to 2^42). --GN
 * (DATA TO BE COMPLETED)
 */
int				/* no longer static -- needed in mpqs.c */
miller(GEN n, long k)
{
  long r, i;
  gpmem_t av2, av = avma;
  static long pr[] =
    { 0, 2,3,5,7,11,13,17,19,23,29, 31,73, 2,13,23,1662803UL, };
  long *p;

  if (!mod2(n)) return 0;
  if (k==16)
  {				/* use smaller (faster) bases if possible */
    if (lgefint(n)==3 && (ulong)(n[2]) < 3215031751UL) p = pr; /* 2,3,5,7 */
    else p = pr+13;		/* 2,13,23,1662803 */
    k=4;
  }
  else if (k==17)
  {
    if (lgefint(n)==3 && (ulong)(n[2]) < 1373653) p = pr; /* 2,3 */
    else p = pr+11;		/* 31,73 */
    k=2;
  }
  else p = pr;			/* 2,3,5,... */
  n = init_miller(n); av2=avma;
  for (i=1; i<=k; i++)
  {
    r = smodsi(p[i],n); if (!r) break;
    if (bad_for_base(n, stoi(r))) { avma = av; return 0; }
    avma=av2;
  }
  avma=av; return 1;
}

/* compute n-th term of Lucas sequence modulo N.
 * v_{k+2} = P v_{k+1} - v_k, v_0 = 2, v_1 = P.
 * Assume n > 0 */
static GEN
LucasMod(GEN n, long P, GEN N)
{
  gpmem_t av = avma, lim = stack_lim(av, 1);
  GEN nd = n+2;
  long i, m = *nd, j = 1+bfffo((ulong)m);
  GEN v = stoi(P), v1 = stoi(P*P - 2);

  m <<= j; j = BITS_IN_LONG - j;
  for (i=lgefint(n)-2;;) /* cf. leftright_pow */
  {
    for (; j; m<<=1,j--)
    { /* v = v_k, v1 = v_{k+1} */
      if (m < 0)
      { /* set v = v_{2k+1}, v1 = v_{2k+2} */
        v = subis(mulii(v,v1), P);
        v1= subis(sqri(v1), 2);
      }
      else
      {/* set v = v_{2k}, v1 = v_{2k+1} */
        v1= subis(mulii(v,v1), P);
        v = subis(sqri(v), 2);
      }
      v = modii(v, N);
      v1= modii(v1,N);
      if (low_stack(lim,stack_lim(av,1)))
      {
        GEN *gptr[2]; gptr[0]=&v; gptr[1]=&v1;
        if(DEBUGMEM>1) err(warnmem,"LucasMod");
        gerepilemany(av,gptr,2);
      }
    }
    if (--i == 0) return v;
    j = BITS_IN_LONG;
    m = *++nd;
  }
}

/* check that N not a square first (taken care of here, but inefficient)
 * assume N > 3 */
static int
IsLucasPsP0(GEN N)
{
  long b, i, v;
  GEN N_2, m, z;

  for (b=3, i=0;; b+=2, i++)
  {
    if (i == 64 && carreparfait(N)) return 0; /* avoid oo loop if N = m^2 */
    if (krosg(b*b - 4, N) < 0) break;
  }

  m = addis(N,1); v = vali(m); m = shifti(m,-v);
  z = LucasMod(m, b, N);
  if (egalii(z, gdeux)) return 1;
  N_2 = subis(N,2);
  if (egalii(z, N_2)) return 1;
  for (i=1; i<v; i++)
  {
    if (!signe(z)) return 1;
    z = modii(subis(sqri(z), 2), N);
    if (egalii(z, gdeux)) return 0;
  }
  return 0;
}

long
IsLucasPsP(GEN N)
{
  gpmem_t av = avma;
  int k;
  GEN T;

  if (typ(N) != t_INT) err(arither1);
  if (signe(N) <= 0) return 0;
  if (!is_bigint(N))
    switch(itos(N))
    {
      case 1: return 0;
      case 2:
      case 3: return 1;
    }
  if (!mod2(N)) return 0;

  T = init_miller(N);
  k = bad_for_base(T,gdeux);
  avma = av;
  k = (!k && IsLucasPsP0(N));
  avma = av; return k;
}

/***********************************************************************/
/**                                                                   **/
/**                       Pocklington-Lehmer                          **/
/**                        P-1 primality test                         **/
/** Crude implementation  BA 2000Apr21                                **/
/***********************************************************************/

/*assume n>=2*/
static long pl831(GEN N, GEN p)
{
  gpmem_t ltop=avma, av;
  long a;
  GEN Nmun,Nmunp;
  Nmun=addis(N,-1);
  Nmunp=divii(Nmun,p);
  av=avma;
  for(a=2;;a++)
  {
    GEN b;
    b=powmodulo(stoi(a),Nmunp,N);
    if (gcmp1(powmodulo(b,p,N)))
    {
      GEN g;
      g=mppgcd(addis(b,-1),N);
      if (gcmp1(g)) { avma=ltop; return a; }
      if (!gegal(g,N)) { avma=ltop; return 0; }
    }
    else { avma=ltop; return 0; }
    avma=av;
  }
}
/*
 * flag 0: return gun (prime), gzero (composite)
 * flag 1: return gzero (composite), gun (small prime), matrix (large prime)
 *
 * The matrix has 3 columns, [a,b,c] with 
 * a[i] prime factor of N-1,
 * b[i] witness for a[i] as in pl831
 * c[i] plisprime(a[i])
 */
extern GEN decomp_limit(GEN n, GEN limit);
GEN
plisprime(GEN N, long flag)
{
  gpmem_t ltop=avma;
  long i;
  int eps;
  GEN C,F;
  if ( typ(N) != t_INT ) err(arither1);
  eps = absi_cmp(N,gdeux);
  if (eps<=0) return eps? gzero: gun;
  N = absi(N);
  /* Use Jaeschke results. See above */
  if (miller(N,7))
  { /* compare to 341550071728321 */
    if (cmpii(N, u2toi(0x136a3, 0x52b2c8c1)) < 0) { avma=ltop; return gun; }
  }
  else { avma=ltop; return gzero; }
  F=(GEN)decomp_limit(addis(N,-1),racine(N))[1];
  if (DEBUGLEVEL>=3) fprintferr("P.L.:factor O.K.\n");
  C=cgetg(4,t_MAT);
  C[1]=lgetg(lg(F),t_COL); 
  C[2]=lgetg(lg(F),t_COL);
  C[3]=lgetg(lg(F),t_COL);
  for(i=1;i<lg(F);i++)
  {
    long witness;
    GEN p;
    p=(GEN)F[i];
    witness=pl831(N,p);
    if (!witness) { avma=ltop; return gzero; }
    mael(C,1,i)=lcopy(p);
    mael(C,2,i)=lstoi(witness);
    mael(C,3,i)=(long)plisprime(p,flag);
    if (gmael(C,3,i)==gzero)
      err(talker,"Sorry false prime number %Z in plisprime",p);
  }
  if (!flag) { avma=ltop; return gun; }
  return gerepileupto(ltop,C);
}

/***********************************************************************/
/**                                                                   **/
/**                       PRIMES IN SUCCESSION                        **/
/** (abstracted by GN 1998Aug21 mainly for use in ellfacteur() below) **/
/**                                                                   **/
/***********************************************************************/

/* map from prime residue classes mod 210 to their numbers in {0...47}.
 * Subscripts into this array take the form ((k-1)%210)/2, ranging from
 * 0 to 104.  Unused entries are 128
 */
#define NPRC 128		/* non-prime residue class */

static
unsigned char prc210_no[] =
{
  0, NPRC, NPRC, NPRC, NPRC, 1, 2, NPRC, 3, 4, NPRC, /* 21 */
  5, NPRC, NPRC, 6, 7, NPRC, NPRC, 8, NPRC, 9, /* 41 */
  10, NPRC, 11, NPRC, NPRC, 12, NPRC, NPRC, 13, 14, NPRC, /* 63 */
  NPRC, 15, NPRC, 16, 17, NPRC, NPRC, 18, NPRC, 19, /* 83 */
  NPRC, NPRC, 20, NPRC, NPRC, NPRC, 21, NPRC, 22, 23, NPRC, /* 105 */
  24, 25, NPRC, 26, NPRC, NPRC, NPRC, 27, NPRC, NPRC, /* 125 */
  28, NPRC, 29, NPRC, NPRC, 30, 31, NPRC, 32, NPRC, NPRC, /* 147 */
  33, 34, NPRC, NPRC, 35, NPRC, NPRC, 36, NPRC, 37, /* 167 */
  38, NPRC, 39, NPRC, NPRC, 40, 41, NPRC, NPRC, 42, NPRC, /* 189 */
  43, 44, NPRC, 45, 46, NPRC, NPRC, NPRC, NPRC, 47, /* 209 */
};

/* map from prime residue classes mod 210 (by number) to their smallest
 * positive representatives
 */
static
unsigned char prc210_rp[] =
{
  1, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79,
  83, 89, 97, 101, 103, 107, 109, 113, 121, 127, 131, 137, 139, 143, 149,
  151, 157, 163, 167, 169, 173, 179, 181, 187, 191, 193, 197, 199, 209,
};

/* first differences of the preceding */
static
unsigned char prc210_d1[] =
{
  10, 2, 4, 2, 4, 6, 2, 6, 4, 2, 4, 6, 6, 2, 6, 4, 2, 6,
  4, 6, 8, 4, 2, 4, 2, 4, 8, 6, 4, 6, 2, 4, 6,
  2, 6, 6, 4, 2, 4, 6, 2, 6, 4, 2, 4, 2, 10, 2,
};

GEN
nextprime(GEN n)
{
  long rc, rc0, rcd, rcn;
  gpmem_t av1, av2, av = avma;

  if (typ(n) != t_INT) n=gceil(n); /* accept arguments in R --GN */
  if (typ(n) != t_INT) err(arither1);
  if (signe(n) <= 0) { avma=av; return gdeux; }
  if (lgefint(n) <= 3)
  { /* check if n <= 7 */
    ulong k = n[2];
    if (k <= 2) { avma=av; return gdeux; }
    if (k == 3) { avma = av; return stoi(3); }
    if (k <= 5) { avma = av; return stoi(5); }
    if (k <= 7) { avma = av; return stoi(7); }
  }
  /* here n > 7 */
  if (!(mod2(n))) n = addsi(1,n);
  rc = rc0 = smodis(n, 210);
  rcn = (long)(prc210_no[rc0>>1]);
  /* find next prime residue class mod 210 */
  while (rcn == NPRC)
  {
    rc += 2;			/* cannot wrap since 209 is coprime */
    rcn = (long)(prc210_no[rc>>1]);
  }
  if (rc > rc0) n = addsi(rc - rc0, n);
  /* now find an actual prime */
  av2 = av1 = avma;
  for(;;)
  {
    if (miller(n,10)) break;
    av1 = avma;
    rcd = prc210_d1[rcn];
    if (++rcn > 47) rcn = 0;
    n = addsi(rcd,n);
  }
  if (av1!=av2) return gerepile(av,av1,n);
  return (av1==av)? icopy(n): n;
}

GEN
precprime(GEN n)
{
  long rc, rc0, rcd, rcn;
  gpmem_t av1, av2, av = avma;

  if (typ(n) != t_INT) n=gfloor(n); /* accept arguments in R --GN */
  if (typ(n) != t_INT) err(arither1);
  if (signe(n)<=0) { avma=av; return gzero; }
  if (lgefint(n) <= 3)
  { /* check if n <= 10 */
    ulong k = n[2];
    if (k <= 1) { avma=av; return gzero; }
    if (k == 2) { avma=av; return gdeux; }
    if (k <= 4) { avma=av; return stoi(3); }
    if (k <= 6) { avma=av; return stoi(5); }
    if (k <= 10) { avma=av; return stoi(7); }
  }
  /* here n >= 11 */
  if (!(mod2(n))) n = addsi(-1,n);
  rc = rc0 = smodis(n, 210);
  rcn = (long)(prc210_no[rc0>>1]);
  /* find last prime residue class mod 210 */
  while (rcn == NPRC)
  {
    rc -= 2;			/* cannot wrap since 1 is coprime */
    rcn = (long)(prc210_no[rc>>1]);
  }
  if (rc < rc0) n = addsi(rc - rc0, n);
  /* now find an actual prime */
  av2 = av1 = avma;
  for(;;)
  {
    if (miller(n,10)) break;
    av1 = avma;
    if (rcn == 0)
    { rcd = 2; rcn = 47; }
    else
      rcd = prc210_d1[--rcn];
    n = addsi(-rcd,n);
  }
  if (av1!=av2) return gerepile(av,av1,n);
  return (av1==av)? icopy(n): n;
}

/* find next single-word prime strictly larger than p.  If **d is non-NULL,
 * this will be p + *(*d)++, using the diffptr table.  Otherwise imitate
 * nextprime().  Apart from *d, caller must supply a long variable to which
 * rcn points, initialized either to NPRC or to the correct residue class
 * number for the current p;  we'll use this to track the current prime
 * residue class mod 210 once we're out of range of the diffptr table, and
 * we'll update it before that if it isn't NPRC.  *q is incremented when-
 * ever q!=NULL and we wrap from 209 mod 210 to 1 mod 210;  this makes sense
 * only when *rcn already held the correct value.  Caller must also supply
 * the second argument for miller(). --GN1998Aug22
 */
ulong
snextpr(ulong p, byteptr *d, long *rcn, long *q, long k)
{
  static ulong pp[] =
    { evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3), 0 };
  static ulong *pp2 = pp + 2;
  static GEN gp = (GEN)pp;
  long d1 = **d, rcn0;

  if (d1)
  {
    if (*rcn != NPRC)
    {
      rcn0 = *rcn;
      while (d1 > 0)
      {
	d1 -= prc210_d1[*rcn];
	if (++*rcn > 47) { *rcn = 0; if (q) (*q)++; }
      }
      if (d1 < 0)
      {
	fprintferr("snextpr: prime %lu wasn\'t %lu mod 210\n",
		   p, (ulong)prc210_rp[rcn0]);
	err(bugparier, "[caller of] snextpr");
      }
    }
    return p + *(*d)++;
  }
  /* we are beyond the diffptr table */
  if (*rcn == NPRC)		/* we need to initialize this now */
  {
    *rcn = prc210_no[(p % 210) >> 1];
    if (*rcn == NPRC)
    {
      fprintferr("snextpr: %lu should have been prime but isn\'t\n", p);
      err(bugparier, "[caller of] snextpr");
    }
  }
  /* look for the next one */
  *pp2 = p;
  *pp2 += prc210_d1[*rcn];
  if (++*rcn > 47) *rcn = 0;
  while (!miller(gp, k))
  {
    *pp2 += prc210_d1[*rcn];
    if (++*rcn > 47) { *rcn = 0; if (q) (*q)++; }
    if (*pp2 <= 11)		/* wraparound mod 2^BITS_IN_LONG */
    {
      fprintferr("snextpr: integer wraparound after prime %lu\n", p);
      err(bugparier, "[caller of] snextpr");
    }
  }
  return *pp2;
}


/***********************************************************************/
/**                                                                   **/
/**                        FACTORIZATION (ECM)                        **/
/**   Integer factorization using the elliptic curves method (ECM).   **/
/**   ellfacteur() returns a non trivial factor of N, assuming N>0,   **/
/**   is composite, and has no prime divisor below 2^14 or so.        **/
/**   Extensively modified by GN Jul-Aug 1998, with much helpful      **/
/**   advice by Paul Zimmermann.  Thanks also to Guillaume Hanrot     **/
/**   and Igor Schein for providing many CPU cycles whilst testing.   **/
/**                                                                   **/
/***********************************************************************/

static GEN N, gl, *XAUX;
#define nbcmax 64		/* max number of simultaneous curves */
#define bstpmax 1024		/* max number of baby step table entries */

/* addition/doubling/multiplication of a point on an `elliptic curve'
 * mod N may result in one of three things:  a new bona fide point,
 * a point at infinity  (betraying itself by a denominator divisible
 * by N),  or a point which is at infinity mod some nontrivial factor
 * of N but finite mod some other factor  (betraying itself by a denom-
 * inator which has nontrivial gcd with N, and this is of course what
 * we want).
 */
/* (In the second case, addition/doubling will simply abort, copying one
 * of the summands to the destination array of points unless they coincide.
 * Multiplication will stop at some unpredictable intermediate stage:  The
 * destination will contain _some_ multiple of the input point, but not
 * necessarily the desired one, which doesn't matter.  As long as we're
 * multiplying (B1 phase) we simply carry on with the next multiplier.
 * During the B2 phase, the only additions are the giant steps, and the
 * worst that can happen here is that we lose one residue class mod 210
 * of prime multipliers on 4 of the curves, so again, we ignore the problem
 * and just carry on.) */
/* The idea is:  Select a handful of curves mod N and one point P on each of
 * them.  Try to compute, for each such point, the multiple [M]P = Q where
 * M is the product of all powers <= B2 of primes <= nextprime(B1), for some
 * suitably chosen B1 and B2.  Then check whether multiplying Q by one of the
 * primes < nextprime(B2) would betray a factor.  This second stage proceeds
 * by looking separately at the primes in each residue class mod 210, four
 * curves at a time, and stepping additively to ever larger multipliers,
 * by comparing X coordinates of points which we would need to add in order
 * to reach another prime multiplier in the same residue class.  `Comparing'
 * means that we accumulate a product of differences of X coordinates, and
 * from time to time take a gcd of this product with N.
 */
/* Montgomery's trick of hiding the cost of computing inverses mod N at a
 * price of three extra multiplications mod N, by working on up to 64 or
 * even 128 points in parallel, is used heavily. --GN
 */

/* *** auxiliary functions for ellfacteur: *** */

/* Parallel addition on nbc curves, assigning the result to locations at and
 * following *X3, *Y3.  Safe to be called with X3,Y3 equal to X2,Y2  (_not_
 * to X1,Y1).  It is also safe to overwrite Y2 with X3.  (If Y coords of
 * result not desired, set Y3=NULL.)  If nbc1 < nbc, the first summand is
 * assumed to hold only nbc1 distinct points, which are repeated as often
 * as we need them  (useful for adding one point on each of a few curves
 * to several other points on the same curves).
 * Return 0 when successful, 1 when we hit a denominator divisible by N,
 * and 2 when gcd(denominator, N) is a nontrivial factor of N, which will
 * be preserved in gl.
 * We use more stack space than the old code did, and thus run a bit of a
 * risk of overflowing it, but it's still bounded by a constant multiple
 * of lgefint(N)*nbc, as it was in the old version --GN1998Jul02,Aug12
 */
/* (Lessee:  Second phase creates 12 items on the stack, per iteration,
 * of which four are twice as long and one is thrice as long as N --
 * makes 18 units per iteration.  First phase creates 4 units.  Total
 * can be as large as about 4*nbcmax+18*8 units.  And elladd2() is just
 * as bad, and elldouble() comes to about 3*nbcmax+29*8 units.  A few
 * strategic garbage collections every 8 iterations should help when nbc
 * is large...) --GN1998Aug23
 */

static int
elladd0(long nbc, long nbc1,
	GEN *X1, GEN *Y1, GEN *X2, GEN *Y2, GEN *X3, GEN *Y3)
{
  GEN lambda;
  GEN W[2*nbcmax], *A=W+nbc;	/* W[0],A[0] never used */
  long i;
  gpmem_t av=avma, tetpil;
  ulong mask = ~0UL;

  /* actually, this is only ever called with nbc1==nbc or nbc1==4, so: */
  if (nbc1 == 4) mask = 3;
  else if (nbc1 < nbc) err(bugparier, "[caller of] elladd0");

  /* W[0] = gun; */
  W[1] = /* A[0] =*/ subii(X1[0], X2[0]);
  for (i=1; i<nbc; i++)
  {
    A[i] = subii(X1[i&mask], X2[i]); /* don't waste time reducing mod N here */
    W[i+1] = modii(mulii(A[i], W[i]), N);
  }
  tetpil = avma;

  /* if gl != N we have a factor */
  if (!invmod(W[nbc], N, &gl))
  {
    if (!egalii(N,gl)) { gl = gerepile(av,tetpil,gl); return 2; }
    if (X2 != X3)
    {
      long k;
      /* cannot add on one of the curves mod N:  make sure X3 contains
       * something useful before letting the caller proceed
       */
      for (k = 2*nbc; k--; ) affii(X2[k],X3[k]);
    }
    avma = av; return 1;
  }

  while (i--)			/* nbc times, actually */
  {
    lambda = modii(mulii(subii(Y1[i&mask], Y2[i]),
			 i?mulii(gl, W[i]):gl), N);
    modiiz(subii(sqri(lambda), addii(X2[i], X1[i&mask])), N, X3[i]);
    if (Y3)
      modiiz(subii(mulii(lambda, subii(X1[i&mask], X3[i])),
		   Y1[i&mask]),
	     N, Y3[i]);
    if (!i) break;
    gl = modii(mulii(gl, A[i]), N);
    if (!(i&7)) gl = gerepileupto(tetpil, gl);
  }
  avma=av; return 0;
}

/* Shortcut variant, for use in cases where Y coordinates follow their
 * corresponding X coordinates, and the first summand doesn't need to be
 * repeated
 */
static int
elladd(long nbc, GEN *X1, GEN *X2, GEN *X3)
{
  return elladd0(nbc, nbc, X1, X1+nbc, X2, X2+nbc, X3, X3+nbc);
}
/* this could perhaps become a macro --GN */

/* The next one is exactly the same except it does twice as many additions
 * (and thus hides even more of the cost of the modular inverse);  the net
 * effect is the same as elladd(nbc,X1,X2,X3) followed by elladd(nbc,X4,X5,X6).
 * Safe to have X2==X3 and/or X5==X6, and of course safe to have X1 or X2
 * coincide with X4 or X5, in any order.
 */

static int
elladd2(long nbc, GEN *X1, GEN *X2, GEN *X3, GEN *X4, GEN *X5, GEN *X6)
{
  GEN lambda, *Y1 = X1+nbc, *Y2 = X2+nbc, *Y3 = X3+nbc;
  GEN *Y4 = X4+nbc, *Y5 = X5+nbc, *Y6 = X6+nbc;
  GEN W[4*nbcmax], *A=W+2*nbc;	/* W[0],A[0] never used */
  long i, j;
  gpmem_t av=avma, tetpil;
  /* W[0] = gun; */
  W[1] = /* A[0] =*/ subii(X1[0], X2[0]);
  for (i=1; i<nbc; i++)
  {
    A[i] = subii(X1[i], X2[i]);	/* don't waste time reducing mod N here */
    W[i+1] = modii(mulii(A[i], W[i]), N);
  }
  for (j=0; j<nbc; i++,j++)
  {
    A[i] = subii(X4[j], X5[j]);
    W[i+1] = modii(mulii(A[i], W[i]), N);
  }
  tetpil = avma;

  /* if gl != N we have a factor */
  if (!invmod(W[2*nbc], N, &gl))
  {
    if (!egalii(N,gl)) { gl = gerepile(av,tetpil,gl); return 2; }
    if (X2 != X3)
    {
      long k;
      /* cannot add on one of the curves mod N:  make sure X3 contains
       * something useful before letting the caller proceed
       */
      for (k = 2*nbc; k--; ) affii(X2[k],X3[k]);
    }
    if (X5 != X6)
    {
      long k;
      /* same for X6 */
      for (k = 2*nbc; k--; ) affii(X5[k],X6[k]);
    }
    avma = av; return 1;
  }

  while (j--)			/* nbc times, actually */
  {
    i--;
    lambda = modii(mulii(subii(Y4[j], Y5[j]),
			 mulii(gl, W[i])), N);
    modiiz(subii(sqri(lambda), addii(X5[j], X4[j])), N, X6[j]);
    modiiz(subii(mulii(lambda, subii(X4[j], X6[j])), Y4[j]), N, Y6[j]);
    gl = modii(mulii(gl, A[i]), N);
    if (!(i&7)) gl = gerepileupto(tetpil, gl);
  }
  while (i--)			/* nbc times */
  {
    lambda = modii(mulii(subii(Y1[i], Y2[i]),
			 i?mulii(gl, W[i]):gl), N);
    modiiz(subii(sqri(lambda), addii(X2[i], X1[i])), N, X3[i]);
    modiiz(subii(mulii(lambda, subii(X1[i], X3[i])), Y1[i]), N, Y3[i]);
    if (!i) break;
    gl = modii(mulii(gl, A[i]), N);
    if (!(i&7)) gl = gerepileupto(tetpil, gl);
  }
  avma=av; return 0;
}

/* Parallel doubling on nbc curves, assigning the result to locations at
 * and following *X2.  Safe to be called with X2 equal to X1.  Return
 * value as for elladd() above.  If we find a point at infinity mod N,
 * and if X1 != X2, we copy the points at X1 to X2.
 * Use fewer assignments than the old code.  Strangely, whereas this gains
 * about 3% on my P133 with elladd(), it makes hardly any difference here
 * with elldouble() --GN
 */
static int
elldouble(long nbc, GEN *X1, GEN *X2)
{
  GEN lambda,v, *Y1 = X1+nbc, *Y2 = X2+nbc;
  GEN W[nbcmax+1];		/* W[0] never used */
  long i;
  gpmem_t av=avma, tetpil;
  /*W[0] = gun;*/ W[1] = Y1[0];
  for (i=1; i<nbc; i++)
    W[i+1] = modii(mulii(Y1[i], W[i]), N);
  tetpil = avma;

  if (!invmod(W[nbc], N, &gl))
  {
    if (!egalii(N,gl)) { gl = gerepile(av,tetpil,gl); return 2; }
    if (X1 != X2)
    {
      long k;
      /* cannot double on one of the curves mod N:  make sure X2 contains
       * something useful before letting the caller proceed
       */
      for (k = 2*nbc; k--; ) affii(X1[k],X2[k]);
    }
    avma = av; return 1;
  }

  while (i--)			/* nbc times, actually */
  {
    lambda = modii(mulii(addsi(1, mulsi(3, sqri(X1[i]))),
			 i?mulii(gl,W[i]):gl), N);
    if (signe(lambda))		/* half of zero is still zero */
      lambda = shifti(mod2(lambda)? addii(lambda, N): lambda, -1);
    v = modii(subii(sqri(lambda), shifti(X1[i],1)), N);
    if (i) gl = modii(mulii(gl, Y1[i]), N);
    modiiz(subii(mulii(lambda, subii(X1[i], v)), Y1[i]), N, Y2[i]);
    affii(v, X2[i]);
    if (!(i&7) && i) gl = gerepileupto(tetpil, gl);
  }
  avma = av; return 0;
}

/* Parallel multiplication by an odd prime k on nbc curves, storing the
 * result to locations at and following *X2.  Safe to be called with X2
 * equal to X1.  Return values as for elladd() and elldouble().
 * Uses (a simplified variant of) Peter Montgomery's PRAC (PRactical Addition
 * Chain) algorithm;  see ftp://ftp.cwi.nl/pub/pmontgom/Lucas.ps.gz .
 * With thanks to Paul Zimmermann for the reference.  --GN1998Aug13
 */

/* We use an array of GENs pointed at by XAUX as a scratchpad;  this will
 * have been set up by ellfacteur()  (so we don't need to reinitialize it
 * each time).
 */

static int
ellmult(long nbc, ulong k, GEN *X1, GEN *X2) /* k>2 prime, not checked */
{
  long i, d, e, e1, r;
  gpmem_t av=avma, tetpil;
  int res;
  GEN *A=X2, *B=XAUX, *S, *T=XAUX+2*nbc;

  for (i = 2*nbc; i--; ) { affii(X1[i],XAUX[i]); }
  tetpil = avma;

  /* first doubling picks up X1;  after this we'll be working in XAUX and
   * X2 only, mostly via A and B and T
   */
  if ((res = elldouble(nbc, X1, X2)) != 0)
  {
    if (res > 1) { gl = gerepile(av,tetpil,gl); } else avma = av;
    return res;
  }

  /* split the work at the golden ratio */
  r = (long)(k*0.61803398875 + .5);
  d = k - r; e = r - d;		/* NB d+e == r, so no danger of ofl below */

  while (d != e)
  {

    /* apply one of the nine transformations from PM's Table 4.  We first
     * figure out which, and then go into an eight-way switch, because
     * some of the transformations are similar enough to share code.
     */
    if (d <= e + (e>>2))	/* floor(1.25*e) */
    {
      if ((d+e)%3 == 0)
      { i = 0;	goto apply; }	/* Table 4, rule 1 */
      else if ((d-e)%6 == 0)
      { i = 1; goto apply; }	/* rule 2 */
      /* else fall through */
    }
    if ((d+3)>>2 <= e)		/* equiv to d <= 4*e but cannot ofl */
    { i = 2; goto apply; }	/* rule 3, the most common case */
    if ((d&1)==(e&1))
    { i = 1; goto apply; }	/* rule 4, which does the same as rule 2 */
    if (!(d&1))
    { i = 3; goto apply; }	/* rule 5 */
    if (d%3 == 0)
    { i = 4; goto apply; }	/* rule 6 */
    if ((d+e)%3 == 0)
    { i = 5; goto apply; }	/* rule 7 */
    if ((d-e)%3 == 0)
    { i = 6; goto apply; }	/* rule 8 */
    /* when we get here, e must be even, for otherwise one of rules 4,5
     * would have applied
     */
    i = 7;			/* rule 9 */

  apply:
    switch(i)			/* i takes values in {0,...,7} here */
    {
    case 0:			/* rule 1 */
      e1 = d - e; d = (d + e1)/3; e = (e - e1)/3;
      if ((res = elladd(nbc, A, B, T)) != 0)
      {
	if (res > 1) { gl = gerepile(av,tetpil,gl); } else avma = av;
	return res;
      }
      if ((res = elladd2(nbc, T, A, A, T, B, B)) != 0)
      {
	if (res > 1) { gl = gerepile(av,tetpil,gl); } else avma = av;
	return res;
      }
      break;			/* end of rule 1 */
    case 1:			/* rules 2 and 4, part 1 */
      d -= e;
      if ((res = elladd(nbc, A, B, B)) != 0)
      {
	if (res > 1) { gl = gerepile(av,tetpil,gl); } else avma = av;
	return res;
      }
      /* FALL THROUGH */
    case 3:			/* rule 5, and 2nd part of rules 2 and 4 */
      d >>= 1;
      if ((res = elldouble(nbc, A, A)) != 0)
      {
	if (res > 1) { gl = gerepile(av,tetpil,gl); } else avma = av;
	return res;
      }
      break;			/* end of rules 2, 4, and 5 */
    case 4:			/* rule 6 */
      d /= 3;
      if ((res = elldouble(nbc, A, T)) != 0)
      {
	if (res > 1) { gl = gerepile(av,tetpil,gl); } else avma = av;
	return res;
      }
      if ((res = elladd(nbc, T, A, A)) != 0)
      {
	if (res > 1) { gl = gerepile(av,tetpil,gl); } else avma = av;
	return res;
      }
      /* FALL THROUGH */
    case 2:			/* rule 3, and 2nd part of rule 6 */
      d -= e;
      if ((res = elladd(nbc, A, B, B)) != 0)
      {
	if (res > 1) { gl = gerepile(av,tetpil,gl); } else avma = av;
	return res;
      }
      break;			/* end of rules 3 and 6 */
    case 5:			/* rule 7 */
      d = (d - e - e)/3;
      if ((res = elldouble(nbc, A, T)) != 0)
      {
	if (res > 1) { gl = gerepile(av,tetpil,gl); } else avma = av;
	return res;
      }
      if ((res = elladd2(nbc, T, A, A, T, B, B)) != 0)
      {
	if (res > 1) { gl = gerepile(av,tetpil,gl); } else avma = av;
	return res;
      }
      break;			/* end of rule 7 */
    case 6:			/* rule 8 */
      d = (d - e)/3;
      if ((res = elladd(nbc, A, B, B)) != 0)
      {
	if (res > 1) { gl = gerepile(av,tetpil,gl); } else avma = av;
	return res;
      }
      if ((res = elldouble(nbc, A, T)) != 0)
      {
	if (res > 1) { gl = gerepile(av,tetpil,gl); } else avma = av;
	return res;
      }
      if ((res = elladd(nbc, T, A, A)) != 0)
      {
	if (res > 1) { gl = gerepile(av,tetpil,gl); } else avma = av;
	return res;
      }
      break;			/* end of rule 8 */
    case 7:			/* rule 9 */
      e >>= 1;
      if ((res = elldouble(nbc, B, B)) != 0)
      {
	if (res > 1) { gl = gerepile(av,tetpil,gl); } else avma = av;
	return res;
      }
      break;			/* end of rule 9 */
    default:			/* never reached */
      break;
    }
    /* end of Table 4 processing */

    /* swap d <-> e and A <-> B if necessary */
    if (d < e) { r = d; d = e; e = r; S = A; A = B; B = S; }
  } /* while */
  if ((res = elladd(nbc, XAUX, X2, X2)) != 0)
  {
    if (res > 1) { gl = gerepile(av,tetpil,gl); } else avma = av;
    return res;
  }
  avma = av; return 0;
}

/* PRAC implementation notes - main changes against the paper version:
 * (1) The general function  [m+n]P = f([m]P,[n]P,[m-n]P)  collapses  (for
 * m!=n)  to an elladd() which does not depend on the third argument;  and
 * thus all references to the third variable (C in the paper) can be elimi-
 * nated. (2) Since our multipliers are prime, the outer loop of the paper
 * version executes only once, and thus is invisible above. (3) The first
 * step in the inner loop of the paper version will always be rule 3, but
 * the addition requested by this rule amounts to a doubling, and it will
 * always be followed by a swap, so we have unrolled this first iteration.
 * (4) Some simplifications in rules 6 and 7 are possible given the above,
 * and we can save one addition in each of the two cases.  NB one can show
 * that none of the other elladd()s in the loop can ever turn out to de-
 * generate into an elldouble. (5) I tried to optimize for rule 3, which
 * is used far more frequently than all others together, but it didn't
 * improve things, so I removed the nested tight loop again.  --GN
 */

/* The main loop body of ellfacteur() runs slightly _slower_  under PRAC than
 * under a straightforward left-shift binary multiplication algorithm when
 * N has <30 digits and B1 is small;  PRAC wins when N and B1 get larger.
 * Weird. --GN
 */

/* memory layout in ellfacteur():  We'll have a large-ish array of GEN
 * pointers, and one huge chunk of memory containing all the actual GEN
 * (t_INT) objects.
 * nbc will be held constant throughout the invocation.
 */
/* The B1 stage of each iteration through the main loop needs little
 * space:  enough for the X and Y coordinates of the current points,
 * and twice as much again as scratchpad for ellmult().
 */
/* The B2 stage, starting from some current set of points Q, needs, in
 * succession:
 * - space for [2]Q, [4]Q, ..., [10]Q, and [p]Q for building the helix;
 * - space for 48*nbc X and Y coordinates to hold the helix.  Now this
 * could re-use [2]Q,...,[8]Q, but only with difficulty, since we don't
 * know in advance which residue class mod 210 our p is going to be in.
 * It can and should re-use [p]Q, though;
 * - space for (temporarily [30]Q and then) [210]Q, [420]Q, and several
 * further doublings until the giant step multiplier is reached.  This
 * _can_ re-use the remaining cells from above.  The computation of [210]Q
 * will have been the last call to ellmult() within this iteration of the
 * main loop, so the scratchpad is now also free to be re-used.  We also
 * compute [630]Q by a parallel addition;  we'll need it later to get the
 * baby-step table bootstrapped a little faster.
 */
/* Finally, for no more than 4 curves at a time, room for up to 1024 X
 * coordinates only  (the Y coordinates needed whilst setting up this baby
 * step table are temporarily stored in the upper half, and overwritten
 * during the last series of additions).
 */
/* Graphically:  after end of B1 stage  (X,Y are the coords of Q):
 * +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--
 * | X Y |  scratch  | [2]Q| [4]Q| [6]Q| [8]Q|[10]Q|    ...    | ...
 * +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--
 * *X    *XAUX *XT   *XD                                       *XB
 *
 * [30]Q is computed from [10]Q.  [210]Q can go into XY, etc:
 * +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--
 * |[210]|[420]|[630]|[840]|[1680,3360,6720,...,2048*210]      |bstp table...
 * +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--
 * *X    *XAUX *XT   *XD      [*XG, somewhere here]            *XB .... *XH
 *
 * So we need (13 + 48) * 2 * nbc slots here, and another 4096 slots for
 * the baby step table (not all of which will be used when we start with a
 * small B1, but it's better to allocate and initialize ahead of time all
 * the slots that might be needed later).
 */
/* Note on memory locality:  During the B2 phase, accesses to the helix
 * (once it has been set up)  will be clustered by curves  (4 out of nbc at
 * a time).  Accesses to the baby steps table will wander from one end of
 * the array to the other and back, one such cycle per giant step, and
 * during a full cycle we would expect on the order of 2E4 accesses when
 * using the largest giant step size.  Thus we shouldn't be doing too bad
 * with respect to thrashing a (512KBy) L2 cache.  However, we don't want
 * the baby step table to grow larger than this, even if it would reduce
 * the number of E.C. operations by a few more per cent for very large B2,
 * lest cache thrashing slow down everything disproportionally. --GN
 */

/* parameters for miller() via snextpr(), for use by ellfacteur() */
#define miller_k1 16		/* B1 phase, foolproof below 10^12 */
#define miller_k2 1		/* B2 phase, not foolproof, much faster */
/* (miller_k2 will let thousands of composites slip through, which doesn't
 * harm ECM, but ellmult() during the B1 phase should only be fed primes
 * which really are prime)
 */
/* ellfacteur() has been re-tuned to be useful as a first stage before
 * MPQS, especially for _large_ arguments, when insist is false, and now
 * also for the case when insist is true, vaguely following suggestions
 * by Paul Zimmermann  (see http://www.loria.fr/~zimmerma/ and especially
 * http://www.loria.fr/~zimmerma/records/ecmnet.html)  of INRIA/LORIA.
 * --GN 1998Jul,Aug
 */
GEN
ellfacteur(GEN n, int insist)
{
  static ulong TB1[] =
    {
      /* table revised, cf. below 1998Aug15 --GN */
      142,172,208,252,305,370,450,545,661,801,972,1180,1430,
      1735,2100,2550,3090,3745,4540,5505,6675,8090,9810,11900,
      14420,17490,21200,25700,31160,37780UL,45810UL,55550UL,67350UL,
      81660UL,99010UL,120050UL,145550UL,176475UL,213970UL,259430UL,
      314550UL,381380UL,462415UL,560660UL,679780UL,824220UL,999340UL,
      1211670UL,1469110UL,1781250UL,2159700UL,2618600UL,3175000UL,
      3849600UL,4667500UL,5659200UL,6861600UL,8319500UL,10087100UL,
      12230300UL,14828900UL,17979600UL,21799700UL,26431500UL,
      32047300UL,38856400UL,	/* 110 times that still fits into 32bits */
#ifdef LONG_IS_64BIT
      47112200UL,57122100UL,69258800UL,83974200UL,101816200UL,
      123449000UL,149678200UL,181480300UL,220039400UL,266791100UL,
      323476100UL,392204900UL,475536500UL,576573500UL,699077800UL,
      847610500UL,1027701900UL,1246057200UL,1510806400UL,1831806700UL,
      2221009800UL,2692906700UL,3265067200UL,3958794400UL,4799917500UL,
      /* the only reason to stop here is that I got bored  (and that users
       * will get bored watching their 64bit machines churning on such large
       * numbers for month after month).  Someone can extend this table when
       * the hardware has gotten 100 times faster than now --GN
       */
#endif
    };
  static ulong TB1_for_stage[] =
    {
      /* table revised 1998Aug11 --GN.  The idea is to start a little below
       * the optimal B1 for finding factors which would just have been missed
       * by pollardbrent(), and escalate gradually, changing curves suf-
       * ficiently frequently to give good coverage of the small factor
       * ranges.  The table entries grow a bit faster than what Paul says
       * would be optimal, but having a single table instead of a 2D array
       * keeps the code simple
       */
      500,520,560,620,700,800,900,1000,1150,1300,1450,1600,1800,2000,
      2200,2450,2700,2950,3250,3600,4000,4400,4850,5300,5800,6400,
      7100,7850,8700,9600,10600,11700,12900,14200,15700,17300,
      19000,21000,23200,25500,28000,31000,34500UL,38500UL,43000UL,
      48000UL,53800UL,60400UL,67750UL,76000UL,85300UL,95700UL,
      107400UL,120500UL,135400UL,152000UL,170800UL,191800UL,215400UL,
      241800UL,271400UL,304500UL,341500UL,383100UL,429700UL,481900UL,
      540400UL,606000UL,679500UL,761800UL,854100UL,957500UL,1073500UL,
    };
  long nbc,nbc2,dsn,dsnmax,rep,spc,gse,gss,rcn,rcn0,bstp,bstp0;
  long a, i, j, k, size = expi(n) + 1, tf = lgefint(n);
  gpmem_t av, av1, avtmp;
  ulong B1,B2,B2_p,B2_rt,m,p,p0,p2,dp;
  GEN w,w0,x,*X,*XT,*XD,*XG,*YG,*XH,*XB,*XB2,*Xh,*Yh,*Xb, res = cgeti(tf);
  int rflag, use_clones = 0;
  byteptr d, d0;

  av = avma;			/* taking res into account */
  N = n;			/* make n known to auxiliary functions */
  /* determine where we'll start, how long we'll persist, and how many
   * curves we'll use in parallel
   */
  if (insist)
  {
    dsnmax = (size >> 2) - 10;
    if (dsnmax < 0) dsnmax = 0;
#ifdef LONG_IS_64BIT
    else if (dsnmax > 90) dsnmax = 90;
#else
    else if (dsnmax > 65) dsnmax = 65;
#endif
    dsn = (size >> 3) - 5;
    if (dsn < 0) dsn = 0;
    else if (dsn > 47) dsn = 47;
    /* pick up the torch where non-insistent stage would have given up */
    nbc = dsn + (dsn >> 2) + 9;	/* 8 or more curves in parallel */
    nbc &= ~3;			/* nbc is always a multiple of 4 */
    if (nbc > nbcmax) nbc = nbcmax;
    a = 1 + (nbcmax<<7);	/* seed for choice of curves */
    rep = 0; /* gcc -Wall */
  }
  else
  {
    dsn = (size - 140) >> 3;
    if (dsn > 12) dsn = 12;
    dsnmax = 72;
    if (dsn < 0)		/* < 140 bits: decline the task */
    {
#ifdef __EMX__
      /* MPQS's disk access under DOS/EMX would be abysmally slow, so... */
      dsn = 0;
      rep = 20;
      nbc = 8;
#else
      if (DEBUGLEVEL >= 4)
      {
	fprintferr("ECM: number too small to justify this stage\n");
	flusherr();
      }
      avma = av; return NULL;
#endif
    }
    else
    {
      rep = (size <= 248 ?
	     (size <= 176 ? (size - 124) >> 4 : (size - 148) >> 3) :
	     (size - 224) >> 1);
      nbc = ((size >> 3) << 2) - 80;
      if (nbc < 8) nbc = 8;
      else if (nbc > nbcmax) nbc = nbcmax;
#ifdef __EMX__
      rep += 20;
#endif
    }

    /* it may be convenient to use disjoint sets of curves for the non-insist
     * and insist phases;  moreover, repeated non-insistent calls acting on
     * factors of the same original number should try to use fresh curves.
     * The following achieves this
     */
    a = 1 + (nbcmax<<3)*(size & 0xf);
  }
  if (dsn > dsnmax) dsn = dsnmax;

  if (DEBUGLEVEL >= 4)
  {
    (void) timer2();		/* clear timer */
    fprintferr("ECM: working on %ld curves at a time; initializing", nbc);
    if (!insist)
    {
      if (rep == 1)
	fprintferr(" for one round");
      else
	fprintferr(" for up to %ld rounds", rep);
    }
    fprintferr("...\n");
  }

  /* The auxiliary routines above need < (3*nbc+240)*tf words on the PARI
   * stack, in addition to the spc*(tf+1) words occupied by our main table.
   * If stack space is already tight, try the heap, using newbloc() and
   * killbloc()
   */
  nbc2 = nbc << 1;
  spc = (13 + 48) * nbc2 + bstpmax * 4;
  if ((long)((GEN)avma - (GEN)bot) < spc + 385 + (spc + 3*nbc + 240)*tf)
  {
    if (DEBUGLEVEL >= 5)
    {
      fprintferr("ECM: stack tight, using clone space on the heap\n");
    }
    use_clones = 1;
    x = newbloc(spc + 385);
  }
  else
    x = new_chunk(spc + 385);
  X = 1 + (GEN*)x;		/* B1 phase: current point */
  XAUX = X    + nbc2;		/* scratchpad for ellmult() */
  XT   = XAUX + nbc2;		/* ditto, will later hold [3*210]Q */
  XD   = XT   + nbc2;		/* room for various multiples */
  XB   = XD   + 20*nbc;		/* start of baby steps table */
  XB2  = XB   + 2 * bstpmax;	/* middle of baby steps table */
  XH   = XB2  + 2 * bstpmax;	/* end of bstps table, start of helix */
  Xh   = XH   + 96*nbc;		/* little helix, X coords */
  Yh   = XH   + 192;		/* ditto, Y coords */
  /* XG will be set later, inside the main loop, since it depends on B2 */

  {
    long tw = evallg(tf) | evaltyp(t_INT);

    if (use_clones)
      w = newbloc(spc*tf);
    else
      w = new_chunk(spc*tf);
    w0 = w;			/* remember this for later... */
    for (i = spc; i--; )
    {
      *w = tw; X[i] = w; w += tf; /* hack for: w = cgeti(tf) */
    }
    /* Xh range of 384 pointers not set;  these will later duplicate the
     * pointers in the XH range, 4 curves at a time.  Some of the cells
     * reserved here for the XB range will never be used, instead, we'll
     * warp the pointers to connect to (read-only) GENs in the X/XD range;
     * it would be complicated to skip them here to conserve merely a few
     * KBy of stack or heap space. --GN
     */
  }

  /* *** ECM MAIN LOOP *** */
  for(;;)
  {
    d = diffptr; rcn = NPRC;	/* multipliers begin at the beginning */

    /* pick curves */
    for (i = nbc2; i--; ) affsi(a++, X[i]);
    /* pick bounds */
    B1 = insist ? TB1[dsn] : TB1_for_stage[dsn];
    B2 = 110*B1;
    B2_rt = (ulong)(sqrt((double)B2));
    /* pick giant step exponent and size.
     * With 32 baby steps, a giant step corresponds to 32*420 = 13440, appro-
     * priate for the smallest B2s.  With 1024, a giant step will be 430080;
     * this will be appropriate for B1 >~ 42000, where 512 baby steps would
     * imply roughly the same number of E.C. additions.
     */
    gse = (B1 < 656 ?
	   (B1 < 200 ? 5 : 6) :
	   (B1 < 10500 ?
	    (B1 < 2625 ? 7 : 8) :
	    (B1 < 42000 ? 9 : 10)
	    )
	   );
    gss = 1UL << gse;
    XG = XT + gse*nbc2;		/* will later hold [2^(gse+1)*210]Q */
    YG = XG + nbc;

    if (DEBUGLEVEL >= 4)
    {
      fprintferr("ECM: time = %6ld ms\nECM: dsn = %2ld,\tB1 = %4lu,",
                 timer2(), dsn, B1);
      fprintferr("\tB2 = %6lu,\tgss = %4ld*420\n", B2, gss);
      flusherr();
    }
    p = *d++;

    /* ---B1 PHASE--- */
    /* treat p=2 separately */
    B2_p = B2 >> 1;
    for (m=1; m<=B2_p; m<<=1)
    {
      if ((rflag = elldouble(nbc, X, X)) > 1) goto fin;
      else if (rflag) break;
    }

    /* p=3,...,nextprime(B1) */
    while (p < B1 && p <= B2_rt)
    {
      p = snextpr(p, &d, &rcn, NULL, miller_k1);
      B2_p = B2/p;		/* beware integer overflow on 32-bit CPUs */
      for (m=1; m<=B2_p; m*=p)
      {
	if ((rflag = ellmult(nbc, p, X, X)) > 1) goto fin;
	else if (rflag) break;
      }
    }
    /* primes p larger than sqrt(B2) can appear only to the 1st power */
    while (p < B1)
    {
      p = snextpr(p, &d, &rcn, NULL, miller_k1);
      if (ellmult(nbc, p, X, X) > 1) goto fin; /* p^2 > B2: no loop */
    }

    if (DEBUGLEVEL >= 4)
    {
      fprintferr("ECM: time = %6ld ms, B1 phase done, ", timer2());
      fprintferr("p = %lu, setting up for B2\n", p);
    }

    /* ---B2 PHASE--- */
    /* compute [2]Q,...,[10]Q, which we need to build the helix */
    if (elldouble(nbc, X, XD) > 1)
      goto fin;			/* [2]Q */
    if (elldouble(nbc, XD, XD + nbc2) > 1)
      goto fin;			/* [4]Q */
    if (elladd(nbc, XD, XD + nbc2, XD + (nbc<<2)) > 1)
      goto fin;			/* [6]Q */
    if (elladd2(nbc,
		XD, XD + (nbc<<2), XT + (nbc<<3),
		XD + nbc2, XD + (nbc<<2), XD + (nbc<<3)) > 1)
      goto fin;			/* [8]Q and [10]Q */
    if (DEBUGLEVEL >= 7)
      fprintferr("\t(got [2]Q...[10]Q)\n");

    /* get next prime (still using the foolproof test) */
    p = snextpr(p, &d, &rcn, NULL, miller_k1);
    /* make sure we have the residue class number (mod 210) */
    if (rcn == NPRC)
    {
      rcn = prc210_no[(p % 210) >> 1];
      if (rcn == NPRC)
      {
	fprintferr("ECM: %lu should have been prime but isn\'t\n", p);
	err(bugparier, "ellfacteur");
      }
    }

    /* compute [p]Q and put it into its place in the helix */
    if (ellmult(nbc, p, X, XH + rcn*nbc2) > 1) goto fin;
    if (DEBUGLEVEL >= 7)
      fprintferr("\t(got [p]Q, p = %lu = %lu mod 210)\n",
		 p, (ulong)(prc210_rp[rcn]));

    /* save current p, d, and rcn;  we'll need them more than once below */
    p0 = p;
    d0 = d;
    rcn0 = rcn;			/* remember where the helix wraps */
    bstp0 = 0;			/* p is at baby-step offset 0 from itself */

    /* fill up the helix, stepping forward through the prime residue classes
     * mod 210 until we're back at the r'class of p0.  Keep updating p so
     * that we can print meaningful diagnostics if a factor shows up;  but
     * don't bother checking which of these p's are in fact prime
     */
    for (i = 47; i; i--)	/* 47 iterations */
    {
      p += (dp = (ulong)prc210_d1[rcn]);
      if (rcn == 47)
      {				/* wrap mod 210 */
	if (elladd(nbc, XT + dp*nbc, XH + rcn*nbc2, XH) > 1)
	  goto fin;
	rcn = 0;
	continue;
      }
      if (elladd(nbc, XT + dp*nbc, XH + rcn*nbc2, XH + rcn*nbc2 + nbc2) > 1)
	goto fin;
      rcn++;
    }
    if (DEBUGLEVEL >= 7)
      fprintferr("\t(got initial helix)\n");

    /* compute [210]Q etc, which will be needed for the baby step table */
    if (ellmult(nbc, 3, XD + (nbc<<3), X) > 1) goto fin;
    if (ellmult(nbc, 7, X, X) > 1) goto fin; /* [210]Q */
    /* this was the last call to ellmult() in the main loop body;  may now
     * overwrite XAUX and slots XD and following
     */
    if (elldouble(nbc, X, XAUX) > 1) goto fin; /* [420]Q */
    if (elladd(nbc, X, XAUX, XT) > 1) goto fin; /* [630]Q */
    if (elladd(nbc, X, XT, XD) > 1) goto fin; /* [840]Q */
    for (i=1; i <= gse; i++)	/* gse successive doublings */
    {
      if (elldouble(nbc, XT + i*nbc2, XD + i*nbc2) > 1) goto fin;
    }
    /* (the last iteration has initialized XG to [210*2^(gse+1)]Q) */

    if (DEBUGLEVEL >= 4)
    {
      fprintferr("ECM: time = %6ld ms, entering B2 phase, p = %lu\n",
		 timer2(), p);
    }

    /* inner loop over small sets of 4 curves at a time */
    for (i = nbc - 4; i >= 0; i -= 4)
    {
      if (DEBUGLEVEL >= 6)
	fprintferr("ECM: finishing curves %ld...%ld\n", i, i+3);
      /* copy relevant pointers from XH to Xh.  Recall memory layout in XH
       * is:  nbc X coordinates followed by nbc Y coordinates for residue
       * class 1 mod 210, then the same for r.c. 11 mod 210, etc.  Memory
       * layout for Xh is: four X coords for 1 mod 210, four for 11 mod 210,
       * etc, four for 209 mod 210, and then the corresponding Y coordinates
       * in the same order.  This will allow us to do a giant step on Xh
       * using just three calls to elladd0() each acting on 64 points in
       * parallel
       */
      for (j = 48; j--; )
      {
	k = nbc2*j + i;
	m = j << 2;		/* X coordinates */
	Xh[m]   = XH[k];   Xh[m+1] = XH[k+1];
	Xh[m+2] = XH[k+2]; Xh[m+3] = XH[k+3];
	k += nbc;		/* Y coordinates */
	Yh[m]   = XH[k];   Yh[m+1] = XH[k+1];
	Yh[m+2] = XH[k+2]; Yh[m+3] = XH[k+3];
      }
      /* build baby step table of X coords of multiples of [210]Q.  XB[4*j]
       * will point at X coords on four curves from [(j+1)*210]Q.  Until
       * we're done, we need some Y coords as well, which we keep in the
       * second half of the table, overwriting them at the end when gse==10.
       * Those multiples which we already have  (by 1,2,3,4,8,16,...,2^gse)
       * are entered simply by copying the pointers, ignoring the small
       * number of slots in w that were initially reserved for them.
       * Here are the initial entries...
       */
      for (Xb=XB,k=2,j=i; k--; Xb=XB2,j+=nbc) /* do first X, then Y coords */
      {
	Xb[0]  = X[j];      Xb[1]  = X[j+1]; /* [210]Q */
	Xb[2]  = X[j+2];    Xb[3]  = X[j+3];
	Xb[4]  = XAUX[j];   Xb[5]  = XAUX[j+1]; /* [420]Q */
	Xb[6]  = XAUX[j+2]; Xb[7]  = XAUX[j+3];
	Xb[8]  = XT[j];     Xb[9]  = XT[j+1]; /* [630]Q */
	Xb[10] = XT[j+2];   Xb[11] = XT[j+3];
	Xb += 4;		/* this points at [420]Q */
	/* ... entries at powers of 2 times 210 .... */
	for (m = 2; m < (ulong)gse+k; m++) /* omit Y coords of [2^gse*210]Q */
	{
	  long m2 = m*nbc2 + j;
	  Xb += (2UL<<m);	/* points now at [2^m*210]Q */
	  Xb[0] = XAUX[m2];   Xb[1] = XAUX[m2+1];
	  Xb[2] = XAUX[m2+2]; Xb[3] = XAUX[m2+3];
	}
      }
      if (DEBUGLEVEL >= 7)
	fprintferr("\t(extracted precomputed helix / baby step entries)\n");
      /* ... glue in between, up to 16*210 ... */
      if (elladd0(12, 4,	/* 12 pts + (4 pts replicated thrice) */
		  XB + 12, XB2 + 12,
		  XB,      XB2,
		  XB + 16, XB2 + 16)
	  > 1) goto fin;	/* 4 + {1,2,3} = {5,6,7} */
      if (elladd0(28, 4,	/* 28 pts + (4 pts replicated 7fold) */
		  XB + 28, XB2 + 28,
		  XB,      XB2,
		  XB + 32, XB2 + 32)
	  > 1) goto fin;	/* 8 + {1,...,7} = {9,...,15} */
      /* ... and the remainder of the lot */
      for (m = 5; m <= (ulong)gse; m++)
      {
	/* fill in from 2^(m-1)+1 to 2^m-1 in chunks of 64 and 60 points */
	ulong m2 = 2UL << m;	/* will point at 2^(m-1)+1 */
	for (j = 0; (ulong)j < m2-64; j+=64) /* executed 0 times when m == 5 */
	{
	  if (elladd0(64, 4,
		      XB + m2 - 4, XB2 + m2 - 4,
		      XB + j,      XB2 + j,
		      XB + m2 + j,
		      (m<(ulong)gse ? XB2 + m2 + j : NULL))
	      > 1) goto fin;
	} /* j == m2-64 here, 60 points left */
	if (elladd0(60, 4,
		    XB + m2 - 4, XB2 + m2 - 4,
		    XB + j,      XB2 + j,
		    XB + m2 + j,
		    (m<(ulong)gse ? XB2 + m2 + j : NULL))
	    > 1) goto fin;
	/* (when m==gse, drop Y coords of result, and when both equal 1024,
	 * overwrite Y coords of second argument with X coords of result)
	 */
      }
      if (DEBUGLEVEL >= 7)
	fprintferr("\t(baby step table complete)\n");
      /* initialize a few other things */
      bstp = bstp0;
      p = p0; d = d0; rcn = rcn0;
      gl = gun;
      av1 = avma;
      /* scratchspace for prod (x_i-x_j) */
      avtmp = (gpmem_t)new_chunk(8 * lgefint(n));
      /* the correct entry in XB to use depends on bstp and on where we are
       * on the helix.  As we skip from prime to prime, bstp will be incre-
       * mented by snextpr() each time we wrap around through residue class
       * number 0 (1 mod 210),  but the baby step should not be taken until
       * rcn>=rcn0  (i.e. until we pass again the residue class of p0).
       * The correct signed multiplier is thus k = bstp - (rcn < rcn0),
       * and the offset from XB is four times (|k| - 1).  When k==0, we may
       * ignore the current prime  (if it had led to a factorization, this
       * would have been noted during the last giant step, or -- when we
       * first get here -- whilst initializing the helix).  When k > gss,
       * we must do a giant step and bump bstp back by -2*gss.
       * The gcd of the product of X coord differences against N is taken just
       * before we do a giant step.
       */
      /* loop over probable primes p0 < p <= nextprime(B2),
       * inserting giant steps as necessary
       */
      while (p < B2)
      {
	/* save current p for diagnostics */
	p2 = p;
	/* get next probable prime */
	p = snextpr(p, &d, &rcn, &bstp, miller_k2);
	/* work out the corresponding baby-step multiplier */
	k = bstp - (rcn < rcn0 ? 1 : 0);
	/* check whether it's giant-step time */
	if (k > gss)
	{
	  /* take gcd */
	  gl = mppgcd(gl, n);
	  if (!is_pm1(gl) && !egalii(gl, n)) { p = p2; goto fin; }
	  gl = gun;
	  avma = av1;
	  while (k > gss)	/* hm, just how large are those prime gaps? */
	  {
	    /* giant step */
	    if (DEBUGLEVEL >= 7)
	      fprintferr("\t(giant step at p = %lu)\n", p);
	    if (elladd0(64, 4,
			XG + i, YG + i,
			Xh, Yh, Xh, Yh) > 1) goto fin;
	    if (elladd0(64, 4,
			XG + i, YG + i,
			Xh + 64, Yh + 64, Xh + 64, Yh + 64) > 1) goto fin;
	    if (elladd0(64, 4,
			XG + i, YG + i,
			Xh + 128, Yh + 128, Xh + 128, Yh + 128)
		> 1) goto fin;
	    bstp -= (gss << 1);
	    /* recompute multiplier */
	    k = bstp - (rcn < rcn0 ? 1 : 0);
	  }
	}
	if (!k) continue;	/* point of interest is already in Xh */
	if (k < 0) k = -k;
	m = ((ulong)k - 1) << 2;
	/* accumulate product of differences of X coordinates */
	j = rcn<<2;
        avma = avtmp; /* go to garbage zone */
	gl = modii(mulii(gl, subii(XB[m],   Xh[j])), n);
	gl = modii(mulii(gl, subii(XB[m+1], Xh[j+1])), n);
	gl = modii(mulii(gl, subii(XB[m+2], Xh[j+2])), n);
	gl = mulii(gl, subii(XB[m+3], Xh[j+3]));
        avma = av1;
        gl = modii(gl, n);
      }	/* loop over p */
      avma = av1;
    } /* for i (loop over sets of 4 curves) */

    /* continuation part of main loop */

    if (dsn < dsnmax)
    {
      dsn += insist ? 1 : 2;
      if (dsn > dsnmax) dsn = dsnmax;
    }

    if (!insist && !--rep)
    {
      if (DEBUGLEVEL >= 4)
      {
	fprintferr("ECM: time = %6ld ms,\tellfacteur giving up.\n",
		   timer2());
	flusherr();
      }
      avma = av;
      if (use_clones) { gunclone(w0); gunclone(x); }
      return NULL;
    }
  }
  /* *** END OF ECM MAIN LOOP *** */
fin:
  affii(gl, res);

  if (DEBUGLEVEL >= 4)
  {
    fprintferr("ECM: time = %6ld ms,\tp <= %6lu,\n\tfound factor = %Z\n",
	       timer2(), p, res);
    flusherr();
  }
  avma=av;
  if (use_clones) { gunclone(w0); gunclone(x); }
  return res;
}

/***********************************************************************/
/**                                                                   **/
/**                FACTORIZATION (Pollard-Brent rho)                  **/
/**  pollardbrent() returns a nontrivial factor of n, assuming n is   **/
/**  composite and has no small prime divisor, or NULL if going on    **/
/**  would take more time than we want to spend.  Sometimes it will   **/
/**  find more than one factor, and return a structure suitable for   **/
/**  interpretation by ifac_crack() below.  GN1998Jun18-26            **/
/**                 (Cf. Algorithm 8.5.2 in ACiCNT)                   **/
/**                                                                   **/
/***********************************************************************/

static void
rho_dbg(long c, long msg_mask)
{
  if (c & msg_mask) return;
  fprintferr("Rho: time = %6ld ms,\t%3ld round%s\n",
             timer2(), c, (c==1?"":"s"));
  flusherr();
}

/* Tuning parameter:  for input up to 64 bits long, we must not spend more
 * than a very short time, for fear of slowing things down on average.
 * With the current tuning formula, increase our efforts somewhat at 49 bit
 * input  (an extra round for each bit at first),  and go up more and more
 * rapidly after we pass 80 bits.-- Changed this (again...) to adjust for
 * the presence of squfof, which will finish input up to 59 bits quickly.
 */

#define tune_pb_min 14		/* even 15 seems too much. */

/* We return NULL when we run out of time, or a single t_INT containing a
 * nontrivial factor of n, or a vector of t_INTs, each triple of successive
 * entries containing a factor, an exponent  (equal to un),  and a factor
 * class  (NULL for unknown or zero for known composite),  matching the
 * internal representation used by the ifac_*() routines below.  Repeated
 * factors can arise and are legal;  the caller will be sorting the factors
 * anyway.
 */
GEN
pollardbrent(GEN n)
{
  long tf = lgefint(n), size = 0, delta, retries = 0, msg_mask;
  long c0, c, k, k1, l;
  gpmem_t GGG, avP, avx, av = avma;
  GEN x, x1, y, P, g, g1, res;

  if (DEBUGLEVEL >= 4) (void)timer2(); /* clear timer */

  if (tf >= 4)
    size = expi(n) + 1;
  else if (tf == 3)		/* try to keep purify happy...  */
    size = BITS_IN_LONG - bfffo((ulong)n[2]);

  if (size <= 28)
    c0 = 32;			/* amounts very nearly to `insist'.
				 * Now that we have squfof(), we don't insist
				 * any more when input is 2^29 ... 2^32
				 */
  else if (size <= 42)
    c0 = tune_pb_min;
  else if (size <= 59)		/* match squfof() cutoff point */
    c0 = tune_pb_min + ((size - 42)<<1);
  else if (size <= 72)
    c0 = tune_pb_min + size - 24;
  else if (size <= 301)
    /* nonlinear increase in effort, kicking in around 80 bits */
    /* 301 gives 48121 + tune_pb_min */
    c0 = tune_pb_min + size - 60 +
      ((size-73)>>1)*((size-70)>>3)*((size-56)>>4);
  else 
    c0 = 49152;			/* ECM is faster when it'd take longer */

  c = c0 << 5;			/* 32 iterations per round */
  msg_mask = (size >= 448? 0x1fff:
                           (size >= 192? (256L<<((size-128)>>6))-1: 0xff));
PB_RETRY:
 /* trick to make a `random' choice determined by n.  Don't use x^2+0 or
  * x^2-2, ever.  Don't use x^2-3 or x^2-7 with a starting value of 2.
  * x^2+4, x^2+9 are affine conjugate to x^2+1, so don't use them either.
  *
  * (the point being that when we get called again on a composite cofactor
  * of something we've already seen, we had better avoid the same delta)
  */
  switch ((size + retries) & 7)
  {
    case 0:  delta=  1; break;
    case 1:  delta= -1; break;
    case 2:  delta=  3; break;
    case 3:  delta=  5; break;
    case 4:  delta= -5; break;
    case 5:  delta=  7; break;
    case 6:  delta= 11; break;
    /* case 7: */
    default: delta=-11; break;
  }
  if (DEBUGLEVEL >= 4)
  {
    if (!retries)
    {
      if (size < 1536)
	fprintferr("Rho: searching small factor of %ld-bit integer\n", size);
      else
	fprintferr("Rho: searching small factor of %ld-word integer\n", tf-2);
    }
    else
      fprintferr("Rho: restarting for remaining rounds...\n");
    fprintferr("Rho: using X^2%+1ld for up to %ld rounds of 32 iterations\n",
               delta, c >> 5);
    flusherr();
  }
  x=gdeux; P=gun; g1 = NULL; k = 1; l = 1;
  (void)new_chunk(10 + 6 * tf); /* enough for cgetg(10) + 3 divii */
  y = cgeti(tf); affsi(2, y);
  x1= cgeti(tf); affsi(2, x1);
  avx = avma;
  avP = (gpmem_t)new_chunk(2 * tf); /* enough for x = addsi(tf+1) */
  GGG = (gpmem_t)new_chunk(4 * tf); /* enough for P = modii(2tf+1, tf) */

  for (;;)			/* terminated under the control of c */
  {
    /* use the polynomial  x^2 + delta */
#define one_iter() {\
    avma = GGG; x = resii(sqri(x), n); /* to garbage zone */\
    avma = avx; x = addsi(delta,x);    /* erase garbage */\
    avma = GGG; P = mulii(P, subii(x1, x));\
    avma = avP; P = modii(P,n); }

    one_iter();

    if ((--c & 0x1f)==0)	/* one round complete */
    {
      g = mppgcd(n, P);
      if (!is_pm1(g)) goto fin;	/* caught something */
      if (c <= 0)
      {				/* getting bored */
        if (DEBUGLEVEL >= 4)
        {
          fprintferr("Rho: time = %6ld ms,\tPollard-Brent giving up.\n",
                     timer2());
          flusherr();
        }
        avma=av; return NULL;
      }
      P = gun;			/* not necessary, but saves 1 mulii/round */
      if (DEBUGLEVEL >= 4) rho_dbg(c0-(c>>5), msg_mask);
      affii(x,y);
    }

    if (--k) continue;		/* normal end of loop body */

    if (c & 0x1f) /* otherwise, we already checked */
    {
      g = mppgcd(n, P);
      if (!is_pm1(g)) goto fin;
      P = gun;
    }

   /* Fast forward phase, doing l inner iterations without computing gcds.
    * Check first whether it would take us beyond the alloted time.
    * Fast forward rounds count only half  (although they're taking
    * more like 2/3 the time of normal rounds).  This to counteract the
    * nuisance that all c0 between 4096 and 6144 would act exactly as
    * 4096;  with the halving trick only the range 4096..5120 collapses
    * (similarly for all other powers of two)
    */
    if ((c-=(l>>1)) <= 0)
    {				/* got bored */
      if (DEBUGLEVEL >= 4)
      {
	fprintferr("Rho: time = %6ld ms,\tPollard-Brent giving up.\n",
		   timer2());
	flusherr();
      }
      avma=av; return NULL;
    }
    c &= ~0x1f;			/* keep it on multiples of 32 */

    /* Fast forward loop */
    affii(x, x1); k = l; l <<= 1;
    /* don't show this for the first several (short) fast forward phases. */
    if (DEBUGLEVEL >= 4 && (l>>7) > msg_mask)
    {
      fprintferr("Rho: fast forward phase (%ld rounds of 64)...\n", l>>7);
      flusherr();
    }
    for (k1=k; k1; k1--) one_iter();
    if (DEBUGLEVEL >= 4 && (l>>7) > msg_mask)
    {
      fprintferr("Rho: time = %6ld ms,\t%3ld rounds, back to normal mode\n",
		 timer2(), c0-(c>>5));
      flusherr();
    }

    affii(x,y);
  } /* forever */

fin:
  /* An accumulated gcd was > 1 */
  /* if it isn't n, and looks prime, return it */
  if  (!egalii(g,n))
  {
    if (miller(g,17))
    {
      if (DEBUGLEVEL >= 4)
      {
        rho_dbg(c0-(c>>5), 0);
	fprintferr("\tfound factor = %Z\n",g);
	flusherr();
      }
      avma=av; return icopy(g);
    }
    avma = avx; g1 = icopy(g);  /* known composite, keep it safe */
    avx = avma;
  }
  else g1 = n;			/* and work modulo g1 for backtracking */

  /* Here g1 is known composite */
  if (DEBUGLEVEL >= 4 && size > 192)
  {
    fprintferr("Rho: hang on a second, we got something here...\n");
    flusherr();
  }
  for(;;) /* backtrack until period recovered. Must terminate */
  {
    avma = GGG; y = resii(sqri(y), g1);
    avma = avx; y = addsi(delta,y);
    g = mppgcd(subii(x1, y), g1);
    if (!is_pm1(g)) break;

    if (DEBUGLEVEL >= 4 && (--c & 0x1f) == 0) rho_dbg(c0-(c>>5), msg_mask);
  }

  avma = av; /* safe */
  if (g1 == n || egalii(g,g1))
  {
    if (g1 == n && egalii(g,g1))
    { /* out of luck */
      if (DEBUGLEVEL >= 4)
      {
        rho_dbg(c0-(c>>5), 0);
        fprintferr("\tPollard-Brent failed.\n"); flusherr();
      }
      if (++retries >= 4) return NULL;
      goto PB_RETRY;
    }
    /* half lucky: we've split n, but g1 equals either g or n */
    if (DEBUGLEVEL >= 4)
    {
      rho_dbg(c0-(c>>5), 0);
      fprintferr("\tfound %sfactor = %Z\n",
                 (g1!=n ? "composite " : ""), g);
      flusherr();
    }
    res = cgetg(7, t_VEC);
    res[1] = licopy(g);         /* factor */
    res[2] = un;		/* exponent 1 */
    res[3] = (g1!=n? zero: (long)NULL); /* known composite when g1!=n */

    res[4] = ldivii(n,g);       /* cofactor */
    res[5] = un;		/* exponent 1 */
    res[6] = (long)NULL;	/* unknown */
    return res;
  }
  /* g < g1 < n : our lucky day -- we've split g1, too */
  res = cgetg(10, t_VEC);
  /* unknown status for all three factors */
  res[1] = licopy(g);    res[2] = un; res[3] = (long)NULL;
  res[4] = ldivii(g1,g); res[5] = un; res[6] = (long)NULL;
  res[7] = ldivii(n,g1); res[8] = un; res[9] = (long)NULL;
  if (DEBUGLEVEL >= 4)
  {
    rho_dbg(c0-(c>>5), 0);
    fprintferr("\tfound factors = %Z, %Z,\n\tand %Z\n",
               res[1], res[4], res[7]);
    flusherr();
  }
  return res;
}

/***********************************************************************/
/**                                                                   **/
/**                 FACTORIZATION (Shanks' SQUFOF)                    **/
/**  squfof() returns a nontrivial factor of n, assuming n is odd,    **/
/**  composite, not a pure square, and has no small prime divisor,    **/
/**  or NULL if it fails to find one.  It works on two discriminants  **/
/**  simultaneously  (n and 5n for n=1(4), 3n and 4n for n=3(4)).     **/
/**  The present implementation is limited to input <2^59, and will   **/
/**  work most of the time in signed arithmetic on integers <2^31 in  **/
/**  absolute size.  Occasionally, it may find a factor which is a    **/
/**  square.-- Since this will be used in the double-large-prime      **/
/**  variation of MPQS, we provide a way of suppressing debugging     **/
/**  output even at high debuglevels.  GN2000Sep30-Oct01              **/
/**                 (Cf. Algorithm 8.7.2 in ACiCNT)                   **/
/**                                                                   **/
/***********************************************************************/
extern ulong ucarrecomplet(ulong A);
static long squfof_ambig(long a, long B, long dd, GEN D, long *cntamb);

#define SQUFOF_BLACKLIST_SZ 64

GEN
squfof(GEN n, long quiet)
{
  long tf = lgefint(n), nm4, cnt = 0, cntamb;
  long a1, b1, c1, d1, dd1, L1, a2, b2, c2, d2, dd2, L2, a, q, c, qc, qcb;
  GEN D1, D2, Q, res;
  gpmem_t av = avma;
  static long blacklist1[SQUFOF_BLACKLIST_SZ], blacklist2[SQUFOF_BLACKLIST_SZ];
  long blp1 = 0, blp2 = 0;
  long mydebug = DEBUGLEVEL - quiet;
  int act1 = 1, act2 = 1;

  if (cmpis(n,5) <= 0) return NULL; /* input n <= 5 */

#ifdef LONG_IS_64BIT
  if (tf > 3 || (tf == 3 && bfffo((ulong)n[2]) < 5)) /* n too large */
    return NULL;
#else  /* 32 bits */
  if (tf > 4 || (tf == 4 && bfffo((ulong)n[2]) < 5)) /* n too large */
    return NULL;
#endif
  /* now we have 5 < n < 2^59 */

  nm4 = mod4(n);
  if (!(nm4 & 1)) return gdeux;	/* n even */

  if (nm4 == 1)
  { /* case n = 1 (mod4):  run one iteration on D1 = n, another on D2 = 5n */
    D1 = n;			/* no need to copy */
    Q = racine(D1); d1 = itos(Q); L1 = itos(racine(Q));
    dd1 = (d1>>1) + (d1&1);	/* rounding trick, see below */
    b1 = ((d1-1) & (~1UL)) + 1;	/* largest odd number not exceeding d1 */
    c1 = itos(shifti(subii(D1, sqri(stoi(b1))), -2));
    if (c1 == 0)		/* n was a square */
    {
      avma = av;
      res = cgetg(4, t_VEC);
      res[1] = lstoi(d1);	/* factor */
      res[2] = deux;		/* exponent 2 */
      res[3] = (long)NULL;	/* unknown whether prime or composite */
      return res;
    }
    D2 = mulsi(5,n);
    Q = racine(D2); d2 = itos(Q); L2 = itos(racine(Q));
    dd2 = (d2>>1) + (d2&1);
    b2 = ((d2-1) & (~1UL)) + 1;	/* b1, b2 will always stay odd */
    c2 = itos(shifti(subii(D2, sqri(stoi(b2))), -2));
    if (c2 == 0)		/* 5n is a square, caller should avoid this */
    {
      avma = av;
      res = cgetg(4, t_VEC);
      res[1] = lstoi(d2/5);	/* factor */
      res[2] = deux;		/* exponent 2 */
      res[3] = (long)NULL;	/* unknown whether prime or composite */
      return res;
    }
  }
  else
  { /* case n = 3 (mod4):  run one iteration on D1 = 3n, another on D2 = 4n */
    D1 = mulsi(3,n);
    Q = racine(D1); d1 = itos(Q); L1 = itos(racine(Q));
    dd1 = (d1>>1) + (d1&1);
    b1 = ((d1-1) & (~1UL)) + 1;	/* will always stay odd */
    c1 = itos(shifti(subii(D1, sqri(stoi(b1))), -2));
    if (c1 == 0)		/* 3n is a square, caller should avoid this */
    {
      avma = av;
      res = cgetg(4, t_VEC);
      res[1] = lstoi(d1/3);	/* factor */
      res[2] = deux;		/* exponent 2 */
      res[3] = (long)NULL;	/* unknown whether prime or composite */
      return res;
    }
    D2 = shifti(n,2);
    Q = racine(D2); d2 = itos(Q); L2 = itos(racine(Q));
    dd2 = d2>>1;		/* no rounding trick here */
    b2 = (d2 & (~1UL));		/* largest even below d2, will stay even */
    c2 = itos(shifti(subii(D2, sqri(stoi(b2))), -2));
    /* c2 cannot vanish -- n = 3(mod 4) cannot be a square */
  }
  a1 = a2 = 1;
  /* This completes the setup of the two (identity) forms (a1,b1,-c1) and
   * (a2,b2,-c2).
   *
   * Attentive readers will notice that a1 and c1 represent the absolute
   * values of the a,c coefficients;  we keep track of the sign separately,
   * in fact the sign info is contained in the rightmost bit of the iteration
   * counter cnt:  when cnt is even, c is understood to be negative, else c
   * is positive and a < 0.
   *
   * The quantities dd1, dd2 are used to compute floor((d1+b1)/2) etc., with-
   * out overflowing the 31bit signed integer size limit, as dd1+floor(b1/2)
   * etc.  This is the "rounding trick" alluded to above.
   *
   * L1, L2 are the limits for blacklisting small leading coefficients
   * on the principal cycle, to guarantee that when we find a square form,
   * its square root will belong to an ambiguous cycle  (i.e. won't be an
   * earlier form on the principal cycle).
   *
   * When n = 3(mod 4), D2 = 12(mod 16), and b^2 is always 0 or 4 mod 16.
   * It follows that 4*a*c must be 4 or 8 mod 16, respectively, so at most
   * one of a,c can be divisible by 2 at most to the first power.  This fact
   * is used a couple of times below.
   *
   * The flags act1, act2 remain true while the respective cycle is still
   * active;  we drop them to false when we return to the identity form with-
   * out having found a square form  (or when the blacklist overflows, which
   * shouldn't happen).
   */

  if (mydebug >= 4)
  {
    fprintferr("SQUFOF: entering main loop with forms\n"
	       "\t(1, %ld, %ld) and (1, %ld, %ld)\n\tof discriminants\n"
	       "\t%Z and %Z, respectively\n",
	       b1, -c1, b2, -c2, D1, D2);
    flusherr();
    (void)timer2();		/* clear timer */
  }

  /* MAIN LOOP:  walk around the principal cycle looking for a square form.
   * Blacklist small leading coefficients.
   *
   * The reduction operator can be computed entirely in 32-bit arithmetic:
   * Let q = floor(floor((d1+b1)/2)/c1)  (when c1>dd1, q=1, which happens
   * often enough to special-case it).  Then the new b1 = (q*c1-b1) + q*c1,
   * which can be computed without overflowing, and the new c1 equals
   * a1 - q*(q*c1-b1),  where the righthand term is bounded by d1 in abs
   * size since both the old and the new a1 are positive and bounded by d1.
   */
  while (act1 + act2 > 0)
  {
    /* send first form through reduction operator if active */
    if (act1)
    {
      c = c1;
      if (c > dd1)
	q = 1;
      else
	q = (dd1 + (b1>>1)) / c;
      if (q == 1)
      {
	qcb = c - b1; b1 = c + qcb; c1 = a1 - qcb;
      }
      else
      {
	qc = q*c; qcb = qc - b1; b1 = qc + qcb; c1 = a1 - q*qcb;
      }
      a1 = c;

      if (a1 <= L1)		/* blacklist this */
      {
	if (blp1 >= SQUFOF_BLACKLIST_SZ)
	  /* blacklist overflows: shouldn't happen */
	  act1 = 0;		/* silently */
	else
	{
	  if (mydebug >= 6)
	    fprintferr("SQUFOF: blacklisting a = %ld on first cycle\n", a1);
	  blacklist1[blp1++] = a1;
	}
      }
    }

    /* send second form through reduction operator if active */
    if (act2)
    {
      c = c2;
      if (c > dd2)
	q = 1;
      else
	q = (dd2 + (b2>>1)) / c;
      if (q == 1)
      {
	qcb = c - b2; b2 = c + qcb; c2 = a2 - qcb;
      }
      else
      {
	qc = q*c; qcb = qc - b2; b2 = qc + qcb; c2 = a2 - q*qcb;
      }
      a2 = c;

      if (a2 <= L2)		/* blacklist this */
      {
	if (blp2 >= SQUFOF_BLACKLIST_SZ)
	  /* blacklist overflows: shouldn't happen */
	  act2 = 0;		/* silently */
	else
	{
	  if (mydebug >= 6)
	    fprintferr("SQUFOF: blacklisting a = %ld on second cycle\n", a2);
	  blacklist2[blp2++] = a2;
	}
      }
    }

    /* bump counter, loop if this is an odd iteration (i.e. if the real
     * leading coefficients are negative)
     */
    if (++cnt & 1) continue;

    /* second half of main loop entered only when the leading coefficients
     * are positive (i.e., during even-numbered iterations)
     */

    /* examine first form if active */
    if (act1 && a1 == 1)	/* back to identity form */
    {
      act1 = 0;			/* drop this discriminant */
      if (mydebug >= 4)
      {
	fprintferr("SQUFOF: first cycle exhausted after %ld iterations,\n"
		   "\tdropping it\n",
		   cnt);
	flusherr();
      }
    }
    if (act1)
    {
      if ((a = ucarrecomplet(a1)) != 0) /* square form? */
      {
	if (mydebug >= 4)
	{
	  fprintferr("SQUFOF: square form (%ld^2, %ld, %ld) on first cycle\n"
		     "\tafter %ld iterations, time = %ld ms\n",
		     a, b1, -c1, cnt, timer2());
	  /* flusherr delayed until we've dealt with it */
	}
	/* blacklisted? */
	if (a <= L1)
	{
	  int j;
	  for (j = 0; j < blp1; j++)
	    if (a == blacklist1[j]) { a = 0; break; }
	}
	if (a > 0)		/* not blacklisted */
	{
	  /* imprimitive form? */
	  q = cgcd(a, b1);
	  if (nm4 == 3 && cgcd(q, 3) > 1) /* paranoia */
	  {
	    avma = av;
	    /* we really possess q^2/3 here, but let the caller sort this
	     * out.  His fault for calling us with a multiple of 3.  We
	     * cannot claim (q/3)^2 as a known factor here since q might
	     * equal 3, in which case 3 is the correct answer to return.
	     */
	    if (q == 3)
	    {
	      if (mydebug >= 4)
	      {
		fprintferr("SQUFOF: found factor 3\n");
		flusherr();
	      }
	      return stoi(3);
	    }
	    else q /= 3;	/* and fall through to the next conditional */
	  }
	  if (q > 1)	/* q^2 divides D1 and, in fact, n */
	  {
	    avma = av;
	    if (mydebug >= 4)
	    {
	      fprintferr("SQUFOF: found factor %ld^2\n", q);
	      flusherr();
	    }
	    res = cgetg(4, t_VEC);
	    res[1] = lstoi(q);	/* factor */
	    res[2] = deux;	/* exponent 2 */
	    res[3] = (long)NULL; /* unknown whether prime or composite */
	    return res;
	  }

	  /* chase the inverse root form back along the ambiguous cycle */
	  q = squfof_ambig(a, b1, dd1, D1, &cntamb);
	  if (mydebug >= 6)
	    fprintferr("SQUFOF: squfof_ambig returned %ld\n", q);
	  if (nm4 == 3) q /= cgcd(q, 3);

	  /* return if successful */
	  if (q > 1)
	  {
	    avma = av;
	    if (mydebug >= 4)
	    {
	      fprintferr("SQUFOF: found factor %ld from ambiguous form\n"
			 "\tafter %ld steps on the ambiguous cycle, "
			 "time = %ld ms\n",
			 q, cntamb, timer2());
	      flusherr();
	    }
	    res = stoi(q);
	    return res;
	  }
	  else if (mydebug >= 4) /* nothing found */
	  {
	    fprintferr("SQUFOF: ...found nothing useful on the ambiguous "
		       "cycle\n"
		       "\tafter %ld steps there, time = %ld ms\n",
		       cntamb, timer2());
	    flusherr();
	  }
	}
	else if (mydebug >= 4)	/* blacklisted */
	{
	  fprintferr("SQUFOF: ...but the root form seems to be on the "
		     "principal cycle\n");
	  flusherr();
	}
      }
      /* else proceed */
    }

    /* examine second form if active */
    if (act2 && a2 == 1)	/* back to identity form */
    {
      act2 = 0;			/* drop this discriminant */
      if (mydebug >= 4)
      {
	fprintferr("SQUFOF: second cycle exhausted after %ld iterations,\n"
		   "\tdropping it\n",
		   cnt);
	flusherr();
      }
    }
    if (act2)
    {
      if ((a = ucarrecomplet(a2)) != 0) /* square form? */
      {
	if (mydebug >= 4)
	{
	  fprintferr("SQUFOF: square form (%ld^2, %ld, %ld) on second cycle\n"
		     "\tafter %ld iterations, time = %ld ms\n",
		     a, b2, -c2, cnt, timer2());
	  flusherr();
	}
	/* blacklisted? */
	if (a <= L2)
	{
	  int j;
	  for (j = 0; j < blp2; j++)
	    if (a == blacklist2[j]) { a = 0; break; }
	}
	if (a > 0)		/* not blacklisted */
	{
	  /* imprimitive form? */
	  q = cgcd(a, b2);
	  /* NB if b2 is even, a is odd, so the gcd is always odd */
	  if (nm4 == 1 && cgcd(q, 5) > 1) /* paranoia */
	  {
	    avma = av;
	    /* we really possess q^2/5 here, but let the caller sort this
	     * out.  His fault for calling us with a multiple of 5.  We
	     * cannot claim (q/5)^2 as a known factor here since q might
	     * equal 5, in which case 5 is the correct answer to return.
	     */
	    if (q == 5)
	    {
	      if (mydebug >= 4)
	      {
		fprintferr("SQUFOF: found factor 5\n");
		flusherr();
	      }
	      return stoi(5);
	    }
	    else q /= 5;	/* and fall through to the next conditional */
	  }
	  if (q > 1)		/* q^2 divides D2 */
	  {
	    avma = av;
	    if (mydebug >= 4)
	    {
	      fprintferr("SQUFOF: found factor %ld^2\n", q);
	      flusherr();
	    }
	    res = cgetg(4, t_VEC);
	    res[1] = lstoi(q);	/* factor */
	    res[2] = deux;	/* exponent 2 */
	    res[3] = (long)NULL; /* unknown whether prime or composite */
	    return res;
	  }

	  /* chase the inverse root form along the ambiguous cycle */
	  q = squfof_ambig(a, b2, dd2, D2, &cntamb);
	  if (mydebug >= 6)
	    fprintferr("SQUFOF: squfof_ambig returned %ld\n", q);
	  if (nm4 == 1) q /= cgcd(q, 5);

	  /* return if successful */
	  if (q > 1)
	  {
	    avma = av;
	    if (mydebug >= 4)
	    {
	      fprintferr("SQUFOF: found factor %ld from ambiguous form\n"
			 "\tafter %ld steps on the ambiguous cycle, "
			 "time = %ld ms\n",
			 q, cntamb, timer2());
	      flusherr();
	    }
	    res = stoi(q);
	    return res;
	  }
	  else if (mydebug >= 4) /* nothing found */
	  {
	    fprintferr("SQUFOF: ...found nothing useful on the ambiguous "
		       "cycle\n"
		       "\tafter %ld steps there, time = %ld ms\n",
		       cntamb, timer2());
	    flusherr();
	  }
	}
	else if (mydebug >= 4)	/* blacklisted */
	{
	  fprintferr("SQUFOF: ...but the root form seems to be on the "
		     "principal cycle\n");
	  flusherr();
	}
      }
      /* else proceed */
    }

  } /* end main loop */

  /* when we get here, both discriminants have, alas, turned out to be
   * useless.
   */
  if (mydebug >= 4)
  {
    fprintferr("SQUFOF: giving up, time = %ld ms\n", timer2());
    flusherr();
  }

  avma = av;
  return NULL;
}

/* The following is invoked to walk back along the ambiguous cycle
 * until we hit an ambiguous form and thus the desired factor, which
 * it returns.  If it fails for any reason, it returns 0.  It doesn't
 * interfere with timing and diagnostics, which it leaves to squfof().
 *
 * Before we invoke this, we've found a form (A, B, -C) with A = a^2,
 * where a isn't blacklisted and where gcd(a, B) = 1.  According to
 * ACiCANT, we should now proceed reducing the form (a, -B, -aC), but
 * it is easy to show that the first reduction step always sends this
 * to (-aC, B, a), and the next one, with q computed as usual from B
 * and a (occupying the c position), gives a reduced form, whose third
 * member is easiest to recover by going back to D.  From this point
 * onwards, we're once again working with single-word numbers.
 * NB here there is no need to track signs, we just work with the abs
 * values of the coefficients.
 */
static
long
squfof_ambig(long a, long B, long dd, GEN D, long *cntamb)
{
  long b, c, q, qc, qcb;
  gpmem_t av = avma;
  long a0, b0, b1, c0;

  q = (dd + (B>>1)) / a; qc = q*a; qcb = qc - B;
  b = qc + qcb;
  c = itos(divis(shifti(subii(D, sqri(stoi(b))), -2), a));
#ifdef DEBUG_SQUFOF
  fprintferr("SQUFOF: ambigous cycle of discriminant %Z\n", D);
  fprintferr("SQUFOF: Form on ambigous cycle (%ld, %ld, %ld)\n",
	     a, b, c);
#endif

  avma = av;			/* no further stack operations follow */
  *cntamb = 0;			/* count reduction steps on the cycle */
  a0 = a; b0 = b1 = b;		/* end of loop detection and safeguard */

  for (;;)			/* reduced cycles are finite */
  {
    /* reduction step */
    c0 = c;
    if (c0 > dd)
      q = 1;
    else
      q = (dd + (b>>1)) / c0;
    if (q == 1)
    {
      qcb = c0 - b; b = c0 + qcb; c = a - qcb;
    }
    else
    {
      qc = q*c0; qcb = qc - b; b = qc + qcb; c = a - q*qcb;
    }
    a = c0;

    (*cntamb)++;

    /* check whether we're done */
    if (b == b1) return (a&1 ? a : a>>1);

    /* safeguard against infinite loop: recognize when we've walked
     * around the entire cycle in vain.  (I don't think this can
     * actually happen -- exercise.  But better safe than sorry.)
     */
    if (b == b0 && a == a0) return 0;

    /* prepare for next iteration */
    b1 = b;
  }
  /* NOT REACHED */
  return 0;
}

/***********************************************************************/
/**                                                                   **/
/**                      DETECTING ODD POWERS                         **/
/**  Factoring engines like MPQS which ultimately rely on computing   **/
/**  gcd(N, x^2-y^2) to find a nontrivial factor of N are fundamen-   **/
/**  tally incapable of splitting a proper power of an odd prime,     **/
/**  because of the cyclicity of the prime residue class group.  We   **/
/**  already have a square-detection function carrecomplet(), which   **/
/**  also returns the square root if appropriate.  Here's an analogue **/
/**  for cubes, fifth and 7th powers.  11th powers are a non-issue so **/
/**  long as mpqs() gives up beyond 100 decimal digits  (since ECM    **/
/**  easily finds a 10-digit prime factor of a 100-digit number).     **/
/**  GN1998Jun28                                                      **/
/**                                                                   **/
/***********************************************************************/

/* Use a multistage sieve.  First stages work mod 211, 209, 61, 203;
 * if the argument is larger than a word, we first reduce mod the product
 * of these and then take the remainder apart.  Second stages use 117,
 * 31, 43, 71 in this order.  Moduli which are no longer interesting are
 * skipped.  Everything is encoded in a single table of 106 24-bit masks.
 * We only need the first half of the residues.  Three bits per modulus
 * indicate which residues are 7th (bit 2), 5th (bit 1) powers or cubes
 * (bit 0);  the eight moduli above are assigned right-to-left.  The table
 * will err on the side of safety if one of the moduli divides the number
 * to be tested, but as this leads to inefficiency it should still be
 * avoided.
 */

static ulong powersmod[106] = {
  077777777ul,	/* 0 */
  077777777ul,	/* 1 */
  013562440ul,	/* 2 */
  012462540ul,	/* 3 */
  013562440ul,	/* 4 */
  052662441ul,	/* 5 */
  016663440ul,	/* 6 */
  016463450ul,	/* 7 */
  013573551ul,	/* 8 */
  012462540ul,	/* 9 */
  012462464ul,	/* 10 */
  013462771ul,	/* 11 */
  012466473ul,	/* 12 */
  012463641ul,	/* 13 */
  052463646ul,	/* 14 */
  012563446ul,	/* 15 */
  013762440ul,	/* 16 */
  052766440ul,	/* 17 */
  012772451ul,	/* 18 */
  012762454ul,	/* 19 */
  032763550ul,	/* 20 */
  013763664ul,	/* 21 */
  017763460ul,	/* 22 */
  037762565ul,	/* 23 */
  017762540ul,	/* 24 */
  057762441ul,	/* 25 */
  037772452ul,	/* 26 */
  017773551ul,	/* 27 */
  017767541ul,	/* 28 */
  017767640ul,	/* 29 */
  037766450ul,	/* 30 */
  017762752ul,	/* 31 */
  037762762ul,	/* 32 */
  017762742ul,	/* 33 */
  037763762ul,	/* 34 */
  017763740ul,	/* 35 */
  077763740ul,	/* 36 */
  077762750ul,	/* 37 */
  077762752ul,	/* 38 */
  077762750ul,	/* 39 */
  077762743ul,	/* 40 */
  077767740ul,	/* 41 */
  077763741ul,	/* 42 */
  077763762ul,	/* 43 */
  077772760ul,	/* 44 */
  077762770ul,	/* 45 */
  077766750ul,	/* 46 */
  077762740ul,	/* 47 */
  077763740ul,	/* 48 */
  077763750ul,	/* 49 */
  077763752ul,	/* 50 */
  077762740ul,	/* 51 */
  077762740ul,	/* 52 */
  077772740ul,	/* 53 */
  077762762ul,	/* 54 */
  077763765ul,	/* 55 */
  077763770ul,	/* 56 */
  077767750ul,	/* 57 */
  077766753ul,	/* 58 */
  077776740ul,	/* 59 */
  077772741ul,	/* 60 */
  077772744ul,	/* 61 */
  077773740ul,	/* 62 */
  077773743ul,	/* 63 */
  077773751ul,	/* 64 */
  077772771ul,	/* 65 */
  077772760ul,	/* 66 */
  077772763ul,	/* 67 */
  077772751ul,	/* 68 */
  077773750ul,	/* 69 */
  077777740ul,	/* 70 */
  077773745ul,	/* 71 */
  077772740ul,	/* 72 */
  077772742ul,	/* 73 */
  077772744ul,	/* 74 */
  077776750ul,	/* 75 */
  077773771ul,	/* 76 */
  077773774ul,	/* 77 */
  077773760ul,	/* 78 */
  077772741ul,	/* 79 */
  077772740ul,	/* 80 */
  077772740ul,	/* 81 */
  077772741ul,	/* 82 */
  077773754ul,	/* 83 */
  077773750ul,	/* 84 */
  077773740ul,	/* 85 */
  077776741ul,	/* 86 */
  077776771ul,	/* 87 */
  077776773ul,	/* 88 */
  077772761ul,	/* 89 */
  077773741ul,	/* 90 */
  077773740ul,	/* 91 */
  077773740ul,	/* 92 */
  077772740ul,	/* 93 */
  077772752ul,	/* 94 */
  077772750ul,	/* 95 */
  077772751ul,	/* 96 */
  077773741ul,	/* 97 */
  077773761ul,	/* 98 */
  077777760ul,	/* 99 */
  077772765ul,	/* 100 */
  077772742ul,	/* 101 */
  077777751ul,	/* 102 */
  077777750ul,	/* 103 */
  077777745ul,	/* 104 */
  077777770ul	/* 105 */
};

/* Returns 3, 5, or 7 if x is a cube (but not a 5th or 7th power),  a 5th
 * power (but not a 7th),  or a 7th power, and in this case creates the
 * base on the stack and assigns its address to *pt.  Otherwise returns 0.
 * x must be of type t_INT and nonzero;  this is not checked.  The *mask
 * argument tells us which things to check -- bit 0: 3rd, bit 1: 5th,
 * bit 2: 7th pwr;  set a bit to have the corresponding power examined --
 * and is updated appropriately for a possible follow-up call
 */

long				/* no longer static -- used in mpqs.c */
is_odd_power(GEN x, GEN *pt, long *mask)
{
  long lgx=lgefint(x), exponent=0, residue, resbyte;
  gpmem_t av=avma, tetpil;
  GEN y;

  *mask &= 7;			/* paranoia */
  if (!*mask) return 0;		/* useful when running in a loop */
  if (signe(x) < 0) x=absi(x);

  if (DEBUGLEVEL >= 5)
  {
    fprintferr("OddPwrs: is %Z\n\t...a", x);
    if (*mask&1) fprintferr(" 3rd%s",
			    (*mask==7?",":(*mask!=1?" or":"")));
    if (*mask&2) fprintferr(" 5th%s",
			    (*mask==7?", or":(*mask&4?" or":"")));
    if (*mask&4) fprintferr(" 7th");
    fprintferr(" power?\n");
  }
  if (lgx > 3) residue = smodis(x, 211*209*61*203);
  else residue = x[2];

  resbyte=residue%211; if (resbyte > 105) resbyte = 211 - resbyte;
  *mask &= powersmod[resbyte];
  if (DEBUGLEVEL >= 5)
  {
    fprintferr("\tmodulo: resid. (remaining possibilities)\n");
    fprintferr("\t   211:  %3ld   (3rd %ld, 5th %ld, 7th %ld)\n",
	       resbyte, *mask&1, (*mask>>1)&1, (*mask>>2)&1);
  }
  if (!*mask) { avma=av; return 0; }

  if (*mask & 3)
  {
    resbyte=residue%209; if (resbyte > 104) resbyte = 209 - resbyte;
    *mask &= (powersmod[resbyte] >> 3);
    if (DEBUGLEVEL >= 5)
      fprintferr("\t   209:  %3ld   (3rd %ld, 5th %ld, 7th %ld)\n",
		 resbyte, *mask&1, (*mask>>1)&1, (*mask>>2)&1);
    if (!*mask) { avma=av; return 0; }
  }
  if (*mask & 3)
  {
    resbyte=residue%61; if (resbyte > 30) resbyte = 61 - resbyte;
    *mask &= (powersmod[resbyte] >> 6);
    if (DEBUGLEVEL >= 5)
      fprintferr("\t    61:  %3ld   (3rd %ld, 5th %ld, 7th %ld)\n",
		 resbyte, *mask&1, (*mask>>1)&1, (*mask>>2)&1);
    if (!*mask) { avma=av; return 0; }
  }
  if (*mask & 5)
  {
    resbyte=residue%203; if (resbyte > 101) resbyte = 203 - resbyte;
    *mask &= (powersmod[resbyte] >> 9);
    if (DEBUGLEVEL >= 5)
      fprintferr("\t   203:  %3ld   (3rd %ld, 5th %ld, 7th %ld)\n",
		 resbyte, *mask&1, (*mask>>1)&1, (*mask>>2)&1);
    if (!*mask) { avma=av; return 0; }
  }

  if (lgx > 3) residue = smodis(x, 117*31*43*71);
  else residue = x[2];

  if (*mask & 1)
  {
    resbyte=residue%117; if (resbyte > 58) resbyte = 117 - resbyte;
    *mask &= (powersmod[resbyte] >> 12);
    if (DEBUGLEVEL >= 5)
      fprintferr("\t   117:  %3ld   (3rd %ld, 5th %ld, 7th %ld)\n",
		 resbyte, *mask&1, (*mask>>1)&1, (*mask>>2)&1);
    if (!*mask) { avma=av; return 0; }
  }
  if (*mask & 3)
  {
    resbyte=residue%31; if (resbyte > 15) resbyte = 31 - resbyte;
    *mask &= (powersmod[resbyte] >> 15);
    if (DEBUGLEVEL >= 5)
      fprintferr("\t    31:  %3ld   (3rd %ld, 5th %ld, 7th %ld)\n",
		 resbyte, *mask&1, (*mask>>1)&1, (*mask>>2)&1);
    if (!*mask) { avma=av; return 0; }
  }
  if (*mask & 5)
  {
    resbyte=residue%43; if (resbyte > 21) resbyte = 43 - resbyte;
    *mask &= (powersmod[resbyte] >> 18);
    if (DEBUGLEVEL >= 5)
      fprintferr("\t    43:  %3ld   (3rd %ld, 5th %ld, 7th %ld)\n",
		 resbyte, *mask&1, (*mask>>1)&1, (*mask>>2)&1);
    if (!*mask) { avma=av; return 0; }
  }
  if (*mask & 6)
  {
    resbyte=residue%71; if (resbyte > 35) resbyte = 71 - resbyte;
    *mask &= (powersmod[resbyte] >> 21);
    if (DEBUGLEVEL >= 5)
      fprintferr("\t    71:  %3ld   (3rd %ld, 5th %ld, 7th %ld)\n",
		 resbyte, *mask&1, (*mask>>1)&1, (*mask>>2)&1);
    if (!*mask) { avma=av; return 0; }
  }

  /* priority to higher powers -- if we have a 21st, it'll be easier to
   * rediscover that its 7th root is a cube than that its cube root is
   * a 7th power
   */
  if ((resbyte = *mask & 4))	/* assignment */
    exponent = 7;
  else if ((resbyte = *mask & 2))
    exponent = 5;
  else
    { resbyte = 1; exponent = 3; }
  /* leave that mask bit on for the moment, we might need it for a
   * subsequent call
   */

  /* precision in the following is one extra significant word (overkill) */
  y=ground(gpow(x, ginv(stoi(exponent)), lgx));
  if (!egalii(gpowgs(y, exponent), x))
  {
    if (DEBUGLEVEL >= 5)
    {
      if (exponent == 3)
	fprintferr("\tBut it nevertheless wasn't a cube.\n");
      else
	fprintferr("\tBut it nevertheless wasn't a %ldth power.\n",
		   exponent);
    }
    *mask &= ~resbyte;		/* _now_ turn the bit off */
    avma=av; return 0;
  }
  /* caller (ifac_crack() below) will report the final result if it was
   * a pure power, so no further diagnostics here
   */
  tetpil=avma;
  if (!pt) { avma=av; return exponent; } /* this branch not used */
  *pt=gerepile(av,tetpil,icopy(y));
  return exponent;
}

/***********************************************************************/
/**                                                                   **/
/**                FACTORIZATION  (master iteration)                  **/
/**      Driver for the various methods of finding large factors      **/
/**      (after trial division has cast out the very small ones).     **/
/**                        GN1998Jun24--30                            **/
/**                                                                   **/
/***********************************************************************/

/**  Direct use:
 **  ifac_start()  registers a number  (without prime factors < 100)
 **    with the iterative factorizer, and also registers whether or
 **    not we should terminate early if we find that the number is
 **    not squarefree, and a hint about which method(s) to use.  This
 **    must always be called first.  The input _must_ have been checked
 **    to be composite by the caller.  The routine immediately tries
 **    to decompose it nontrivially into a product of two factors,
 **    except in squarefreeness (`Moebius') mode.
 **  ifac_primary_factor()  returns a prime divisor  (not necessarily
 **    the smallest)  and the corresponding exponent. */

/**  Encapsulated user interface:
 **  ifac_decomp()  does the right thing for auxdecomp()  (put a succession
 **    of prime divisor / exponent pairs onto the stack, not necessarily
 **    sorted, although in practice they will tend not to be too far from
 **    the correct order).
 **
 **  For each of the additive/multiplicative arithmetic functions, there is
 **  a `contributor' below, to be called on any large composite cofactor
 **  left over after trial division by small primes, whose result can then
 **  be added to or multiplied with whatever we already have:
 **  ifac_moebius()  ifac_issquarefree()  ifac_totient()  ifac_omega()
 **  ifac_bigomega()  ifac_numdiv()  ifac_sumdiv()  ifac_sumdivk() */

/* We never test whether the input number is prime or composite, since
 * presumably it will have come out of the small factors finder stage
 * (which doesn't really exist yet but which will test the left-over
 * cofactor for primality once it does).
 */
/* The data structure in which we preserve whatever we know at any given
 * time about our number N is kept on the PARI stack, and updated as needed.
 * This makes the machinery re-entrant  (you can have more than one fac-
 * torization using ifac_start()/ifac_primary_factor() in progress simul-
 * taneously so long as you preserve the GEN across garbage collections),
 * and which avoids memory leaks when a lengthy factorization is interrupted.
 * We also make an effort to keep the whole affair connected, and the parent
 * object will always be older than its children.  This may in rare cases
 * lead to some extra copying around, and knowing what is garbage at any
 * given time is not entirely trivial.  See below for examples how to do
 * it right.  (Connectedness can be destroyed if callers of ifac_main()
 * create other stuff on the stack in between calls.  This is harmless
 * as long as ifac_realloc() is used to re-create a connected object at
 * the head of the stack just before collecting garbage.)
 */
/* Note that a PARI integer can have hundreds of millions of distinct prime
 * factors larger than 2^16, given enough memory.  And since there's no
 * guarantee that we will find factors in order of increasing size, we must
 * be prepared to drag a very large amount of data around  (although this
 * will _very_ rarely happen for random input!).  So we start with a small
 * structure and extend it when necessary.
 */
/* The idea of data structure and algorithm is:
 * Let N0 be whatever is currently left of N after dividing off all the
 * prime powers we have already returned to the caller.  Then we maintain
 * N0 as a product
 * (1)   N0 = \prod_i P_i^{e_i} * \prod_j Q_j^{f_j} * \prod_k C_k^{g_k}
 * where the P_i and Q_j are distinct primes, each C_k is known composite,
 * none of the P_i divides any C_k, and we also know the total ordering
 * of all the P_i, Q_j and C_k  (in particular, we will never try to divide
 * a C_k by a larger Q_j).  Some of the C_k may have common factors, although
 * this will not often be the case.
 */
/* Caveat implementor:  Taking gcds among C_k's is very likely to cost at
 * least as much time as dividing off any primes as we find them, and book-
 * keeping would be a nightmare  (since D=gcd(C_1,C_2) can still have common
 * factors with both C_1/D and C_2/D, and so on...).
 */
/* At startup, we just initialize the structure to
 * (2)        N = C_1^1   (composite).
 */
/* Whenever ifac_primary_factor() or ifac_decomp()  (or, mutatis mutandis,
 * one of the three arithmetic user interface routines)  needs a primary
 * factor, and the smallest thing in our list is P_1, we return that and
 * its exponent, and remove it from our list.
 * (When nothing is left, we return a sentinel value -- gun.  And in Moebius
 * mode, when we see something with exponent > 1, whether prime or composite,
 * we yell at our caller by returning gzero or 0, depending on the function).
 * In all other cases, ifac_main() iterates the following steps until we have
 * a P_1 in the smallest position.
 */
/* When the smallest item is C_1  (as it is initially):
 * (3.1) Crack C_1 into a nontrivial product  U_1 * U_2  by whatever method
 * comes to mind for this size.  (U for `unknown'.)  Cracking will detect
 * squares  (and biquadrates etc),  and it may detect odd powers, so we
 * might instead see a power of some U_1 here, or even something of the form
 * U_1^k*U_2^k.  (Of course the exponent already attached to C_1 is taken
 * into account in the following.)
 * (3.2) If we have U_1*U_2, sort the two factors;  convert to U_1^2 if they
 * happen to be equal  (which they shouldn't -- squares should have been
 * caught at the preceding stage).  Note that U_1 and  (if it exists)  U_2
 * are automatically smaller than anything else in our list.
 * (3.3) Check U_1  (and U_2)  for primality, and flag them accordingly.
 * (3.4) Iterate.
 */
/* When the smallest item is Q_1:
 * This is the potentially unpleasant case.  The idea is to go through the
 * entire list and try to divide Q_1 off each of the current C_k's, which
 * will usually fail, but may succeed several times.  When a division was
 * successful, the corresponding C_k is removed from our list, and the co-
 * factor becomes a U_l for the moment unless it is 1  (which happens when
 * C_k was a power of Q_1).  When we're through we upgrade Q_1 to P_1 status,
 * and then do a primality check on each U_l and sort it back into the list
 * either as a Q_j or as a C_k.  If during the insertion sort we discover
 * that some U_l equals some P_i or Q_j or C_k we already have, we just add
 * U_l's exponent to that of its twin.  (The sorting should therefore happen
 * before the primality test).
 * Note that this may produce one or more elements smaller than the P_1
 * we just confirmed, so we may have to repeat the iteration.
 */
/* There's a little trick that avoids some Q_1 instances.  Just after we do
 * a sweep to classify all current unknowns as either composites or primes,
 * we do another downward sweep beginning with the largest current factor
 * and stopping just above the largest current composite.  Every Q_j we
 * pass is turned into a P_i.  (Different primes are automatically coprime
 * among each other, and primes tend not to divide smaller composites.)
 */
/* (We have no use for comparing the square of a prime to N0.  Normally
 * we will get called after casting out only the smallest primes, and
 * since we cannot guarantee that we see the large prime factors in as-
 * cending order, we cannot stop when we find one larger than sqrt(N0).)
 */
/* Data structure:  We keep everything in a single t_VEC of t_INTs.  The
 * first component records whether we're doing full (NULL) or Moebius (un)
 * factorization;  in the latter case many subroutines return a sentinel
 * value as soon as they spot an exponent > 1.  The second component records
 * the hint from factorint()'s optional flag, for use by ifac_crack().
 * The remaining components  (initially 15)  are used in groups of three:
 * a GEN pointer at the t_INT value of the factor, a pointer at the t_INT
 * exponent  (usually gun or gdeux so we don't clutter up the stack too
 * much),  and another t_INT GEN pointer to record the class of the factor:
 * NULL for unknown, zero for known composite C_k, un for known prime Q_j
 * awaiting trial division, and deux for finished prime P_i.
 */
/* When during the division stage we re-sort a C_k-turned-U_l to a lower
 * position, we rotate any intervening material upward towards its old
 * slot.  When a C_k was divided down to 1, its slot is left empty at
 * first;  similarly when the re-sorting detects a repeated factor.
 * After the sorting phase, we de-fragment the list and squeeze all the
 * occupied slots together to the high end, so that ifac_crack() has room
 * for new factors.  When this doesn't suffice, we abandon the current
 * vector and allocate a somewhat larger one, defragmenting again during
 * copying.
 */
/* (For internal use, note that all exponents will fit into C longs, given
 * PARI's lgefint field size.  When we work with them, we sometimes read
 * out the GEN pointer, and sometimes do an itos, whatever is more con-
 * venient for the task at hand.)
 */

/*** Overview and forward declarations: ***/

/* The `*where' argument in the following points into *partial at the
 * first of the three fields of the first occupied slot.  It's there
 * because the caller would already know where `here' is, so we don't
 * want to search for it again, although it wouldn't take much time.
 * On the other hand, we do not preserve this from one user-interface
 * call to the next.
 */

static GEN
ifac_find(GEN *partial, GEN *where);
/* Return GEN pointing at the first nonempty slot strictly behind the
 * current *where, or NULL if such doesn't exist.  Can be used to skip
 * a range of vacant slots, or to initialize *where in the first place
 * (pass partial in both args).  Does not modify its argument pointers.
 */

void
ifac_realloc(GEN *partial, GEN *where, long new_lg);
/* Move to a larger main vector, updating *where if it points into it.
 * Certainly updates *partial.  Can be used as a specialized gcopy before
 * a gerepileupto()/gerepilemanysp()  (pass 0 as the new length).
 * Normally, one would pass new_lg=1 to let this function guess the
 * new size.  To be used sparingly.
 */

static long
ifac_crack(GEN *partial, GEN *where);
/* Split the first (composite) entry.  There _must_ already be room for
 * another factor below *where, and *where will be updated.  Factor and
 * cofactor will be inserted in the correct order, updating *where, or
 * factor^k will be inserted if such should be the case  (leaving *where
 * unchanged).  The factor or factors will be set to unknown, and inherit
 * the exponent  (or a multiple thereof)  of its/their ancestor.  Returns
 * number of factors written into the structure  (normally 2, but 1 if a
 * factor equalled its cofactor, and may be more than 1 if a factoring
 * engine returned a vector of factors instead of a single factor).  Can
 * reallocate the data structure in the vector-of-factors case  (but not
 * in the more common single-factor case)
 */

static long
ifac_insert_multiplet(GEN *partial, GEN *where, GEN facvec);
/* Gets called to complete ifac_crack()'s job when a factoring engine
 * splits the current factor into a product of three or more new factors.
 * Makes room for them if necessary, sorts them, gives them the right
 * exponents and class etc.  Also returns the number of factors actually
 * written, which may be less than the number of components in facvec
 * if there are duplicates.--- Vectors of factors  (cf pollardbrent()
 * above)  actually contain `slots' of three GENs per factor with the
 * three fields being interpreted exactly as in our partial factorization
 * data structure.  Thus `engines' can tell us what they already happen to
 * know about factors being prime or composite and/or appearing to a power
 * larger than the first
 */

static long
ifac_divide(GEN *partial, GEN *where);
/* Divide all current composites by first  (prime, class Q)  entry, updating
 * its exponent, and turning it into a finished prime  (class P).  Return 1
 * if any such divisions succeeded  (in Moebius mode, the update may then
 * not have been completed),  or 0 if none of them succeeded.  Doesn't
 * modify *where.
 */

static long
ifac_sort_one(GEN *partial, GEN *where, GEN washere);
/* re-sort one  (typically unknown)  entry from washere to a new position,
 * rotating intervening entries upward to fill the vacant space.  It may
 * happen (rarely) that the new position is the same as the old one, or
 * that the new value of the entry coincides with a value already occupying
 * a lower slot, in which latter case we just add exponents  (and use the
 * `more known' class, and return 1 immediately when in Moebius mode).
 * The slots between *where and washere must be in sorted order, so a
 * sweep using this to re-sort several unknowns must proceed upward  (see
 * ifac_resort() below).  Return 1 if we see an exponent > 1  (in Moebius
 * mode without completing the update),  0 otherwise.
 */

static long
ifac_resort(GEN *partial, GEN *where);
/* sort all current unknowns downward to where they belong.  Sweeps
 * in the upward direction.  Not needed after ifac_crack(), only when
 * ifac_divide() returned true.  May update *where.  Returns 1 when an
 * ifac_sort_one() call does so to indicate a repeated factor, or 0 if
 * any and all such calls returned 0
 */

static void
ifac_defrag(GEN *partial, GEN *where);
/* defragment: collect and squeeze out any unoccupied slots above *where
 * during a downward sweep.  Unoccupied slots arise when a composite factor
 * dissolves completely whilst dividing off a prime, or when ifac_resort()
 * spots a coincidence and merges two factors.  *where will be updated
 */

static void
ifac_whoiswho(GEN *partial, GEN *where, long after_crack);
/* determine primality or compositeness of all current unknowns, and set
 * class Q primes to finished (class P) if everything larger is already
 * known to be prime.  When after_crack is nonnegative, only look at the
 * first after_crack things in the list (do nothing when it's zero)
 */

static GEN
ifac_main(GEN *partial);
/* main loop:  iterate until smallest entry is a finished prime;  returns
 * a `where' pointer, or gun if nothing left, or gzero in Moebius mode if
 * we aren't squarefree
 */

/* NB In the most common cases, control flows from the user interface to
 * ifac_main() and then to a succession of ifac_crack()s and ifac_divide()s,
 * with (typically) none of the latter finding anything.
 */

/** user interface: **/
/* return initial data structure, see ifac_crack() below for semantics
 * of the hint argument
 */
GEN
ifac_start(GEN n, long moebius, long hint);

/* run main loop until primary factor is found, return the prime and
 * assign the exponent.  If nothing left, return gun and set exponent
 * to 0;  if in Moebius mode and a square factor is discovered, return
 * gzero and set exponent to 0
 */
GEN
ifac_primary_factor(GEN *partial, long *exponent);

/* call ifac_start() and run main loop until factorization is complete,
 * accumulating prime / exponent pairs on the PARI stack to be picked up
 * by aux_end().  Return number of distinct primes found
 */
long
ifac_decomp(GEN n, long hint);

/* completely encapsulated functions;  these call ifac_start() themselves,
 * and ensure proper stack housekeeping etc.  Call them on any large
 * composite left over after trial division, and multiply/add the result
 * onto whatever you already have from the small factors.  Don't call
 * them on large primes;  they will run into trouble
 */
long
ifac_moebius(GEN n, long hint);

long
ifac_issquarefree(GEN n, long hint);

long
ifac_omega(GEN n, long hint);

long
ifac_bigomega(GEN n, long hint);

GEN
ifac_totient(GEN n, long hint);	/* for gp's eulerphi() */

GEN
ifac_numdiv(GEN n, long hint);

GEN
ifac_sumdiv(GEN n, long hint);

GEN
ifac_sumdivk(GEN n, long k, long hint);

/*** implementation ***/

#define ifac_initial_length 24	/* codeword, moebius flag, hint, 7 slots */
/* (more than enough in most cases -- a 512-bit product of distinct 8-bit
 * primes needs at most 7 slots at a time)
 */

GEN
ifac_start(GEN n, long moebius, long hint)
{
  GEN part, here;

  if (typ(n) != t_INT) err(typeer, "ifac_start");
  if (signe(n) == 0)
    err(talker, "factoring 0 in ifac_start");

  part = cgetg(ifac_initial_length, t_VEC);
  here = part + ifac_initial_length;
  part[1] = moebius? un : (long)NULL;
  switch(hint)
  {
  case 0:
    part[2] = zero; break;
  case 1:
    part[2] = un; break;
  case 2:
    part[2] = deux; break;
  default:
    part[2] = (long)stoi(hint);
  }
  if (isonstack(n))
    n = absi(n);
  /* make copy, because we'll later want to mpdivis() into it in place.
   * If it's not on stack, then we assume it is a clone made for us by
   * auxdecomp0(), and we assume the sign has already been set positive
   */
  /* fill first slot at the top end */
  *--here = zero;		/* initially composite */
  *--here = un;			/* initial exponent 1 */
  *--here = (long) n;
  /* and NULL out the remaining slots */
  while (here > part + 3) *--here = (long)NULL;
  return part;
}

static GEN
ifac_find(GEN *partial, GEN *where)
{
  long lgp = lg(*partial);
  GEN end = *partial + lgp;
  GEN scan = *where + 3;

  if (DEBUGLEVEL >= 5)
  {
    if (!*partial || typ(*partial) != t_VEC)
      err(typeer, "ifac_find");
    if (lg(*partial) < ifac_initial_length)
      err(talker, "partial impossibly short in ifac_find");
    if (!(*where) ||
	*where > *partial + lgp - 3 ||
        *where < *partial)	/* sic */
      err(talker, "`*where\' out of bounds in ifac_find");
  }
  while (scan < end && !*scan) scan += 3;
  /* paranoia -- check completely NULLed ? nope -- we never inspect the
   * exponent field for deciding whether a slot is empty or occupied
   */
  if (scan < end)
  {
    if (DEBUGLEVEL >= 5)
    {
      if (!scan[1])
	err(talker, "factor has NULL exponent in ifac_find");
    }
    return scan;
  }
  return NULL;
}

/* simple defragmenter */
static void
ifac_defrag(GEN *partial, GEN *where)
{
  long lgp = lg(*partial);
  GEN scan_new = *partial + lgp - 3, scan_old = scan_new;

  while (scan_old >= *where)
  {
    if (*scan_old)		/* slot occupied? */
    {
      if (scan_old < scan_new)
      {
	scan_new[2] = scan_old[2];
	scan_new[1] = scan_old[1];
	*scan_new = *scan_old;
      }
      scan_new -= 3;		/* point at next slot to be written */
    }
    scan_old -= 3;
  }
  scan_new += 3;		/* back up to last slot written */
  *where = scan_new;
  while (scan_new > *partial + 3)
    *--scan_new = (long)NULL;	/* erase junk */
}

/* and complex version combined with reallocation.  If new_lg is 0, we
 * use the old length, so this acts just like gcopy except that the where
 * pointer is carried along;  if it is 1, we make an educated guess.
 * Exception:  If new_lg is 0, the vector is full to the brim, and the
 * first entry is composite, we make it longer to avoid being called again
 * a microsecond later  (at significant cost).
 * It is safe to call this with NULL for the where argument;  if it doesn't
 * point anywhere within the old structure, it will be left alone
 */
void
ifac_realloc(GEN *partial, GEN *where, long new_lg)
{
  long old_lg = lg(*partial);
  GEN newpart, scan_new, scan_old;

  if (DEBUGLEVEL >= 5)		/* none of these should ever happen */
  {
    if (!*partial || typ(*partial) != t_VEC)
      err(typeer, "ifac_realloc");
    if (lg(*partial) < ifac_initial_length)
      err(talker, "partial impossibly short in ifac_realloc");
  }

  if (new_lg == 1)
    new_lg = 2*old_lg - 6;	/* from 7 slots to 13 to 25... */
  else if (new_lg <= old_lg)	/* includes case new_lg == 0 */
  {
    new_lg = old_lg;
    if ((*partial)[3] &&	/* structure full */
	((*partial)[5]==zero || (*partial)[5]==(long)NULL))
				/* and first entry composite or unknown */
      new_lg += 6;		/* give it a little more breathing space */
  }
  newpart = cgetg(new_lg, t_VEC);
  if (DEBUGMEM >= 3)
  {
    fprintferr("IFAC: new partial factorization structure (%ld slots)\n",
	       (new_lg - 3)/3);
    flusherr();
  }
  newpart[1] = (*partial)[1];	/* moebius */
  newpart[2] = (*partial)[2];	/* hint */
  /* downward sweep through the old *partial, picking up where1 and carry-
   * ing it over if and when we pass it.  (This will only be useful if
   * it pointed at a non-empty slot.)  Factors are licopy()d so that we
   * again have a nice object  (parent older than children, connected),
   * except the one factor that may still be living in a clone where n
   * originally was;  exponents are similarly copied if they aren't global
   * constants;  class-of-factor fields are always global constants so we
   * need only copy them as pointers.  Caller may then do a gerepileupto()
   * or a gerepilemanysp()
   */
  scan_new = newpart + new_lg - 3;
  scan_old = *partial + old_lg - 3;
  for (; scan_old > *partial + 2; scan_old -= 3)
  {
    if (*where == scan_old) *where = scan_new;
    if (!*scan_old) continue;	/* skip empty slots */

    *scan_new =
      isonstack((GEN)(*scan_old)) ?
	licopy((GEN)(*scan_old)) : *scan_old;
    scan_new[1] =
      isonstack((GEN)(scan_old[1])) ?
	licopy((GEN)(scan_old[1])) : scan_old[1];
    scan_new[2] = scan_old[2];
    scan_new -= 3;
  }
  scan_new += 3;		/* back up to last slot written */
  while (scan_new > newpart + 3)
    *--scan_new = (long)NULL;
  *partial = newpart;
}

#define moebius_mode ((*partial)[1])

/* Bubble-sort-of-thing sort.  Won't be exercised frequently,
 * so this is ok.
 */
static long
ifac_sort_one(GEN *partial, GEN *where, GEN washere)
{
  GEN scan = washere - 3;
  GEN value, exponent, class0, class1;
  long cmp_res;

  if (DEBUGLEVEL >= 5)		/* none of these should ever happen */
  {
    long lgp;
    if (!*partial || typ(*partial) != t_VEC)
      err(typeer, "ifac_sort_one");
    if ((lgp = lg(*partial)) < ifac_initial_length)
      err(talker, "partial impossibly short in ifac_sort_one");
    if (!(*where) ||
	*where < *partial + 3 ||
	*where > *partial + lgp - 3)
      err(talker, "`*where\' out of bounds in ifac_sort_one");
    if (!washere ||
	washere < *where ||
	washere > *partial + lgp - 3)
      err(talker, "`washere\' out of bounds in ifac_sort_one");
  }
  value = (GEN)(*washere);
  exponent = (GEN)(washere[1]);
  if (exponent != gun && moebius_mode && cmpsi(1,exponent) < 0)
    return 1;			/* should have been detected by caller */
  class0 = (GEN)(washere[2]);

  if (scan < *where) return 0;	/* nothing to do, washere==*where */

  cmp_res = -1;			/* sentinel */
  while (scan >= *where)	/* therefore at least once */
  {
    if (*scan)			/* current slot nonempty */
    {
      /* check against where */
      cmp_res = cmpii(value, (GEN)(*scan));
      if (cmp_res >= 0) break;	/* have found where to stop */
    }
    /* copy current slot upward by one position and move pointers down */
    scan[5] = scan[2];
    scan[4] = scan[1];
    scan[3] = *scan;
    scan -= 3;
  }
  scan += 3;
  /* at this point there are the following possibilities:
   * (*) cmp_res == -1.  Either value is less than that at *where, or for
   * some reason *where was pointing at one or more vacant slots and any
   * factors we saw en route were larger than value.  At any rate,
   * scan == *where now, and scan is pointing at an empty slot, into
   * which we'll stash our entry.
   * (*) cmp_res == 0.  The entry at scan-3 is the one, we compare class0
   * fields and add exponents, and put it all into the vacated scan slot,
   * NULLing the one at scan-3  (and possibly updating *where).
   * (*) cmp_res == 1.  The slot at scan is the one to store our entry
   * into.
   */
  if (cmp_res != 0)
  {
    if (cmp_res < 0 && scan != *where)
      err(talker, "misaligned partial detected in ifac_sort_one");
    *scan = (long)value;
    scan[1] = (long)exponent;
    scan[2] = (long)class0;
    return 0;
  }
  /* case cmp_res == 0: repeated factor detected */
  if (DEBUGLEVEL >= 4)
  {
    fprintferr("IFAC: repeated factor %Z\n\tdetected in ifac_sort_one\n",
	       value);
    flusherr();
  }
  if (moebius_mode) return 1;	/* not squarefree */
  /* if old class0 was composite and new is prime, or vice versa,
   * complain  (and if one class0 was unknown and the other wasn't,
   * use the known one)
   */
  class1 = (GEN)(scan[-1]);
  if (class0)			/* should never be used */
  {
    if(class1)
    {
      if (class0 == gzero && class1 != gzero)
	err(talker, "composite equals prime in ifac_sort_one");
      else if (class0 != gzero && class1 == gzero)
	err(talker, "prime equals composite in ifac_sort_one");
      else if (class0 == gdeux)	/* should happen even less */
	scan[2] = (long)class0;	/* use it */
    }
    else			/* shouldn't happen either */
      scan[2] = (long)class0;	/* use it */
  }
  /* else stay with the existing known class0 */
  scan[2] = (long)class1;
  /* in any case, add exponents */
  if (scan[-2] == un && exponent == gun)
    scan[1] = deux;
  else
    scan[1] = laddii((GEN)(scan[-2]), exponent);
  /* move the value over */
  *scan = scan[-3];
  /* null out the vacated slot below */
  *--scan = (long)NULL;
  *--scan = (long)NULL;
  *--scan = (long)NULL;
  /* finally, see whether *where should be pulled in */
  if (scan == *where) *where += 3;
  return 0;
}

/* the following loop around the former doesn't need to check moebius_mode
 * because ifac_sort_one() never returns 1 in normal mode
 */
static long
ifac_resort(GEN *partial, GEN *where)
{
  long lgp = lg(*partial), res = 0;
  GEN scan = *where;

  for (; scan < *partial + lgp; scan += 3)
  {
    if (*scan &&		/* slot occupied */
	!scan[2])		/* with an unknown */
    {
      res |= ifac_sort_one(partial, where, scan);
      if (res) return res;	/* early exit */
    }
  }
  return res;
}

/* sweep downward so we can with luck turn some Qs into Ps */
static void
ifac_whoiswho(GEN *partial, GEN *where, long after_crack)
{
  long lgp = lg(*partial), larger_compos = 0;
  GEN scan, scan_end = *partial + lgp - 3;

  if (DEBUGLEVEL >= 5)
  {
    if (!*partial || typ(*partial) != t_VEC)
      err(typeer, "ifac_whoiswho");
    if (lg(*partial) < ifac_initial_length)
      err(talker, "partial impossibly short in ifac_whoiswho");
    if (!(*where) ||
	*where > scan_end ||
        *where < *partial + 3)
      err(talker, "`*where\' out of bounds in ifac_whoiswho");
  }

  if (after_crack == 0) return;
  if (after_crack > 0)
  {
    larger_compos = 1;		/* disable Q-to-P trick */
    scan = *where + 3*(after_crack - 1);
				/* check at most after_crack entries */
    if (scan > scan_end)	/* ooops... */
    {
      err(warner, "avoiding nonexistent factors in ifac_whoiswho");
      scan = scan_end;
    }
  }
  else { larger_compos = 0; scan = scan_end; }

  for (; scan >= *where; scan -= 3)
  {
    if (scan[2])		/* known class of factor */
    {
      if (scan[2] == zero) larger_compos = 1;
      else if (!larger_compos && scan[2] == un)
      {
	if (DEBUGLEVEL >= 3)
	{
	  fprintferr("IFAC: factor %Z\n\tis prime (no larger composite)\n",
		     **where);
	  fprintferr("IFAC: prime %Z\n\tappears with exponent = %ld\n",
		     **where, itos((GEN)(*where)[1]));
	}
	scan[2] = deux;
      }	/* no else case */
      continue;
    }
    scan[2] =
      (isprime((GEN)(*scan)) ?
       (larger_compos ? un : deux) : /* un- or finished prime */
       zero);			/* composite */

    if (scan[2] == zero) larger_compos = 1;
    if (DEBUGLEVEL >= 3)
    {
      fprintferr("IFAC: factor %Z\n\tis %s\n", *scan,
		 (scan[2] == zero ? "composite" : "prime"));
    }
  }
}

/* Here we normally do not check that the first entry is a not-finished
 * prime.  Stack management: we may allocate a new exponent
 */
static long
ifac_divide(GEN *partial, GEN *where)
{
  long lgp = lg(*partial);
  GEN scan = *where + 3;
  long res = 0, exponent, newexp, otherexp;

  if (DEBUGLEVEL >= 5)		/* none of these should ever happen */
  {
    if (!*partial || typ(*partial) != t_VEC)
      err(typeer, "ifac_divide");
    if (lg(*partial) < ifac_initial_length)
      err(talker, "partial impossibly short in ifac_divide");
    if (!(*where) ||
	*where > *partial + lgp - 3 ||
        *where < *partial + 3)
      err(talker, "`*where\' out of bounds in ifac_divide");
    if ((*where)[2] != un)
      err(talker, "division by composite or finished prime in ifac_divide");
  }
  if (!(**where))		/* always test just this one */
    err(talker, "division by nothing in ifac_divide");

  newexp = exponent = itos((GEN)((*where)[1]));
  if (exponent > 1 && moebius_mode) return 1;
  /* should've been caught by caller already */

  /* go for it */
  for (; scan < *partial + lgp; scan += 3)
  {
    if (scan[2] != zero) continue; /* the other thing ain't composite */
    otherexp = 0;
    /* let mpdivis divide the other factor in place to keep stack clutter
       minimal */
    while (mpdivis((GEN)(*scan), (GEN)(**where), (GEN)(*scan)))
    {
      if (moebius_mode) return 1; /* immediately */
      if (!otherexp) otherexp = itos((GEN)(scan[1]));
      newexp += otherexp;
    }
    if (newexp > exponent)	/* did anything happen? */
    {
      (*where)[1] = (newexp == 2 ? deux : (long)(stoi(newexp)));
      exponent = newexp;
      if (is_pm1((GEN)(*scan))) /* factor dissolved completely */
      {
	*scan = scan[1] = (long)NULL;
	if (DEBUGLEVEL >= 4)
	  fprintferr("IFAC: a factor was a power of another prime factor\n");
      }
      else if (DEBUGLEVEL >= 4)
      {
	fprintferr("IFAC: a factor was divisible by another prime factor,\n");
	fprintferr("\tleaving a cofactor = %Z\n", *scan);
      }
      scan[2] = (long)NULL;	/* at any rate it's Unknown now */
      res = 1;
      if (DEBUGLEVEL >= 5)
      {
	fprintferr("IFAC: prime %Z\n\tappears at least to the power %ld\n",
		   **where, newexp);
      }
    }
  } /* for */
  (*where)[2] = deux;		/* make it a finished prime */
  if (DEBUGLEVEL >= 3)
  {
    fprintferr("IFAC: prime %Z\n\tappears with exponent = %ld\n",
	       **where, newexp);
  }
  return res;
}


GEN mpqs(GEN N);		/* in src/modules/mpqs.c, maybe a dummy,
				 * returns a factor, or a vector of factors,
				 * or NULL
				 */

/* The following takes the place of 2.0.9.alpha's find_factor(). */

/* The meaning of the hint changes against 2.0.9.alpha to:
 * hint == 0 : Use our own strategy, and this should be the default
 * hint & 1  : Avoid mpqs(), use ellfacteur() after pollardbrent()
 * hint & 2  : Avoid first-stage ellfacteur() in favour of mpqs()
 * (which may still fall back to ellfacteur() if mpqs() is not installed
 * or gives up)
 * hint & 4  : Avoid even the pollardbrent() and squfof() stages
 * hint & 8  : Avoid final ellfacteur();  this may `declare' a composite
 * to be prime.
 */

/* stack housekeeping:  this routine may create one or more objects  (a new
 * factor, or possibly several, and perhaps one or more new exponents > 2)
 * Added squfof --GN2000Oct01
 */
static long
ifac_crack(GEN *partial, GEN *where)
{
  long hint, cmp_res, exp1 = 1, exp2 = 1;
  gpmem_t av;
  GEN factor = NULL, exponent;

  if (DEBUGLEVEL >= 5)		/* none of these should ever happen */
  {
    long lgp;
    if (!*partial || typ(*partial) != t_VEC)
      err(typeer, "ifac_crack");
    if ((lgp = lg(*partial)) < ifac_initial_length)
      err(talker, "partial impossibly short in ifac_crack");
    if (!(*where) ||
	*where < *partial + 6 || /* sic -- caller must realloc first */
	*where > *partial + lgp - 3)
      err(talker, "`*where\' out of bounds in ifac_crack");
    if (!(**where) || typ((GEN)(**where)) != t_INT)
      err(typeer, "ifac_crack");
    if ((*where)[2] != zero)
      err(talker, "operand not known composite in ifac_crack");
  }
  hint = itos((GEN)((*partial)[2])) & 15;
  exponent = (GEN)((*where)[1]);

  if (DEBUGLEVEL >= 3)
    fprintferr("IFAC: cracking composite\n\t%Z\n", **where);

  /* crack squares.  Quite fast due to the initial square residue test */
  if (DEBUGLEVEL >= 4)
    fprintferr("IFAC: checking for pure square\n");
  av = avma;
  while (carrecomplet((GEN)(**where), &factor))
  {
    if (DEBUGLEVEL >= 4)
      fprintferr("IFAC: found %Z =\n\t%Z ^2\n", **where, factor);
    affii(factor, (GEN)(**where)); avma = av; factor = NULL;
    if (exponent == gun)
      (*where)[1] = deux;
    else if (exponent == gdeux)
    { (*where)[1] = (long)stoi(4); av = avma; }
    else
    { affii(shifti(exponent, 1), (GEN)((*where)[1])); avma = av; }
    exponent = (GEN)((*where)[1]);
    if (moebius_mode) return 0;	/* no need to carry on... */
    exp1 = 2;
  } /* while carrecomplet */

  /* check whether our composite hasn't become prime */
  if (exp1 > 1 && hint != 15 && isprime((GEN)(**where)))
  {
    (*where)[2] = un;
    if (DEBUGLEVEL >= 4)
    {
      fprintferr("IFAC: factor %Z\n\tis prime\n",**where);
      flusherr();
    }
    return 0;			/* bypass subsequent ifac_whoiswho() call */
  }
  /* still composite -- carry on */

  /* MPQS cannot factor prime powers;  check for cubes/5th/7th powers.
   * Do this even if MPQS is blocked by hint -- it still serves a useful
   * purpose in bounded factorization
   */
  {
    long mask = 7;
    if (DEBUGLEVEL == 4)
      fprintferr("IFAC: checking for odd power\n");
    /* (At debug levels > 4, is_odd_power() itself prints something more
     * informative)
     */
    av = avma;
    while ((exp1 =		/* assignment */
	    is_odd_power((GEN)(**where), &factor, &mask)))
    {
      if (exp2 == 1) exp2 = exp1; /* remember this after the loop */
      if (DEBUGLEVEL >= 4)
	fprintferr("IFAC: found %Z =\n\t%Z ^%ld\n", **where, factor, exp1);
      affii(factor, (GEN)(**where)); avma = av; factor = NULL;
      if (exponent == gun)
      { (*where)[1] = (long)stoi(exp1); av = avma; }
      else if (exponent == gdeux)
      { (*where)[1] = (long)stoi(exp1<<1); av = avma; }
      else
      { affii(mulsi(exp1, exponent), (GEN)((*where)[1])); avma = av; }
      exponent = (GEN)((*where)[1]);
      if (moebius_mode) return 0; /* no need to carry on... */
    } /* while is_odd_power */

    if (exp2 > 1 && hint != 15 && isprime((GEN)(**where)))
    { /* Something nice has happened and our composite has become prime */
      (*where)[2] = un;
      if (DEBUGLEVEL >= 4)
      {
        fprintferr("IFAC: factor %Z\n\tis prime\n", **where);
        flusherr();
      }
      return 0;		/* bypass subsequent ifac_whoiswho() call */
    }
  } /* odd power stage */

  /* pollardbrent() Rho usually gets a first chance */
  if (!(hint & 4))
  {
    if (DEBUGLEVEL >= 4)
      fprintferr("IFAC: trying Pollard-Brent rho method first\n");
    factor = pollardbrent((GEN)(**where));
  } /* Rho stage */

  /* Shanks' squfof() is next.  It will pass up the chance silently when
   * the input number is too large.  We put this under the same governing
   * bit of the hint parameter, for no very good reason other than avoiding
   * a proliferation of further meaningful bits in all the wrong order.
   */
  if (!factor && !(hint & 4))
  {
    if (DEBUGLEVEL >= 4)
      fprintferr("IFAC: trying Shanks' SQUFOF, will fail silently if input\n"
		 "      is too large for it.\n");
    factor = squfof((GEN)(**where), 0);	/* allow squfof's own diagnostics */
  }

  /* if this didn't work, try one of our high-power beasties */
  if (!factor && !(hint & 2))
  {
    if (DEBUGLEVEL >= 4)
      fprintferr("IFAC: trying Lenstra-Montgomery ECM\n");
    factor = ellfacteur((GEN)(**where), 0); /* do not insist */
  } /* First ECM stage */

  if (!factor && !(hint & 1))
  {
    if (DEBUGLEVEL >= 4)
      fprintferr("IFAC: trying Multi-Polynomial Quadratic Sieve\n");
    factor = mpqs((GEN)(**where));
  } /* MPQS stage */

  if (!factor)
  {
    if (!(hint & 8))		/* still no luck?  force it */
    {
      if (DEBUGLEVEL >= 4)
	fprintferr("IFAC: forcing ECM, may take some time\n");
      factor = ellfacteur((GEN)(**where), 1);
    } /* final ECM stage, guaranteed to succeed */
    else			/* limited factorization */
    {
      if (DEBUGLEVEL >= 2)
      {
	err(warner, "IFAC: unfactored composite declared prime");
	/* don't print it out at level 3 or above, where it would appear
	 * several times before and after this message already
	 */
	if (DEBUGLEVEL == 2)
	{
	  fprintferr("\t%Z\n",**where);
	  flusherr();
	}
      }
      (*where)[2] = un;		/* might as well trial-divide by it... */
      return 1;
    }
  } /* Final ECM stage */

  if (DEBUGLEVEL >= 1)
  {
    if (!factor)		/* never reached */
      err(talker, "all available factoring methods failed in ifac_crack");
  }
  if (typ(factor) == t_VEC)	/* delegate this case */
    return ifac_insert_multiplet(partial, where, factor);

  else if (typ(factor) != t_INT)
  {
    fprintferr("IFAC: factorizer returned strange object to ifac_crack\n");
    outerr(factor);
    err(bugparier, "factoring");
  }

  /* got single integer back:  work out the cofactor (in place) */
  if (!mpdivis((GEN)(**where), factor, (GEN)(**where)))
  {
    fprintferr("IFAC: factoring %Z\n", **where);
    fprintferr("\tyielded `factor\' %Z\n\twhich isn't!\n", factor);
    err(bugparier, "factoring");
  }

  /* the factoring engines report the factor found when DEBUGLEVEL is
   * large enough;  let's tell about the cofactor
   */
  if (DEBUGLEVEL >= 4)
    fprintferr("IFAC: cofactor = %Z\n", **where);

  /* ok, now `factor' is one factor and **where is the other, find out
   * which is larger
   */
  cmp_res = cmpii(factor, (GEN)(**where));
  if (cmp_res < 0)		/* common case */
  {
    (*where)[2] = (long)NULL;	/* mark cofactor `unknown' */
    (*where)[-1] = (long)NULL;	/* mark factor `unknown' */
    (*where)[-2] =
      isonstack(exponent) ? licopy(exponent) : (long)exponent;
    *where -= 3;
    **where = (long)factor;
    return 2;
  }
  else if (cmp_res == 0)	/* hep, split a square in the middle */
  {
    err(warner,
	"square not found by carrecomplet, ifac_crack recovering");
    cgiv(factor);
    (*where)[2] = (long)NULL;	/* mark the sqrt `unknown' */
    if (exponent == gun)	/* double the exponent */
      (*where)[1] = deux;
    else if (exponent == gdeux)
      (*where)[1] = (long)stoi(4); /* make a new one */
    else			/* overwrite old exponent */
    {
      av = avma;
      affii(shifti(exponent, 1), (GEN)((*where)[1]));
      avma = av;
      /* leave *where unchanged */
    }
    if (moebius_mode) return 0;
    return 1;
  }
  else				/* factor > cofactor, rearrange */
  {
    (*where)[2] = (long)NULL;	/* mark factor `unknown' */
    (*where)[-1] = (long)NULL;	/* mark cofactor `unknown' */
    (*where)[-2] =
      isonstack(exponent) ? licopy(exponent) : (long)exponent;
    *where -= 3;
    **where = (*where)[3];	/* move cofactor pointer to lowest slot */
    (*where)[3] = (long)factor;	/* save factor */
    return 2;
  }
}

/* the following doesn't collect garbage;  caller's caller should do it
 * (which means ifac_main()).  No diagnostics either, the factoring engine
 * should have printed what it found when DEBUGLEVEL>=4 or so.  Note facvec
 * contains slots of three components per factor;  repeated factors are
 * expressly allowed  (and their classes shouldn't contradict each other
 * whereas their exponents will be added up)
 */
static long
ifac_insert_multiplet(GEN *partial, GEN *where, GEN facvec)
{
  long j,k=1, lfv=lg(facvec)-1, nf=lfv/3, room=(long)(*where-*partial);
  /* one of the factors will go into the *where slot, so room is now
   * 3 times the number of slots we can use
   */
  long needroom = lfv - room;
  GEN sorted, auxvec = cgetg(nf+1, t_VEC), factor;
  long exponent = itos((GEN)((*where)[1])); /* the old exponent */
  GEN newexp;

  if (DEBUGLEVEL >= 5)
    fprintferr("IFAC: incorporating set of %ld factor(s)%s\n",
	       nf, (DEBUGLEVEL >=6 ? "..." : ""));
  /* fixed: squfof may return a single, squared, factor as a set
   * --GN2000Oct01
   */
  if (needroom > 0)
    ifac_realloc(partial, where, lg(*partial) + needroom + 3);
  /* one extra slot for paranoia, errm, future use */

  /* create sort permutation from the values of the factors */
  for (j=nf; j; j--) auxvec[j] = facvec[3*j-2]; /* just the pointers */
  sorted = sindexsort(auxvec);
  /* and readjust the result for the triple spacing */
  for (j=nf; j; j--) sorted[j] = 3*sorted[j]-2;
  if (DEBUGLEVEL >= 6)
    fprintferr("\tsorted them...\n");

  /* store factors, beginning at *where, and catching any duplicates */
  **where = facvec[sorted[nf]];
  if ((newexp = (GEN)(facvec[sorted[nf]+1])) != gun) /* new exponent > 1 */
  {
    if (exponent == 1)
      (*where)[1] = isonstack(newexp) ? licopy(newexp) : (long)newexp;
    else
      (*where)[1] = lmulsi(exponent, newexp);
  } /* if new exponent is 1, the old exponent already in place will do */
  (*where)[2] = facvec[sorted[nf]+2]; /* copy class */
  if (DEBUGLEVEL >= 6)
    fprintferr("\tstored (largest) factor no. %ld...\n", nf);

  for (j=nf-1; j; j--)
  {
    factor = (GEN)(facvec[sorted[j]]);
    if (egalii(factor, (GEN)(**where)))
    {
      if (DEBUGLEVEL >= 6)
	fprintferr("\tfactor no. %ld is a duplicate%s\n",
		   j, (j>1 ? "..." : ""));
      /* update exponent, ignore class which would already have been set,
       * and then forget current factor
       */
      if ((newexp = (GEN)(facvec[sorted[j]+1])) != gun) /* new exp > 1 */
      {				/* now we have at least 3 */
	(*where)[1] = laddii((GEN)((*where)[1]),
			     mulsi(exponent, newexp));
      }
      else
      {
	if ((*where)[1] == un && exponent == 1)
	  (*where)[1] = deux;
	else
	  (*where)[1] = laddsi(exponent, (GEN)((*where)[1]));
	/* not safe to add 1 in place -- that might overwrite gdeux,
	 * with `interesting' consequences
	 */
      }
      if (moebius_mode) return 0; /* stop now, but with exponent updated */
      continue;
    }
    (*where)[-1] = facvec[sorted[j]+2];	/* class as given */
    if ((newexp = (GEN)(facvec[sorted[j]+1])) != gun) /* new exp > 1 */
    {
      if (exponent == 1 && newexp == gdeux)
	(*where)[-2] = deux;
      else			/* exponent*newexp > 2 */
	(*where)[-2] = lmulsi(exponent, newexp);
    }
    else
    {
      (*where)[-2] = (exponent == 1 ? un :
		      (exponent == 2 ? deux :
		       (long)stoi(exponent))); /* inherit parent's exponent */
    }
    (*where)[-3] = isonstack(factor) ? licopy(factor) : (long)factor;
				/* keep components younger than *partial */
    *where -= 3;
    k++;
    if (DEBUGLEVEL >= 6)
      fprintferr("\tfactor no. %ld was unique%s\n",
		 j, (j>1 ? " (so far)..." : ""));
  }
  /* make the `sorted' object safe for garbage collection  (probably not a
   * problem, since it should be in the garbage zone from everybody's
   * perspective, but it's easy to do it)
   */
  *sorted = evaltyp(t_INT) | evallg(nf+1);
  return k;
}

static GEN
ifac_main(GEN *partial)
{
  /* leave the basic error checking to ifac_find() */
  GEN here = ifac_find(partial, partial);
  long res, nf;

  /* if nothing left, return gun */
  if (!here) return gun;

  /* if we are in Moebius mode and have already detected a repeated factor,
   * stop right here.  Shouldn't really happen
   */
  if (moebius_mode && here[1] != un)
  {
    if (DEBUGLEVEL >= 3)
    {
      fprintferr("IFAC: main loop: repeated old factor\n\t%Z\n", *here);
      flusherr();
    }
    return gzero;
  }

  /* loop until first entry is a finished prime.  May involve reallocations
   * and thus updates of *partial
   */
  while (here[2] != deux)
  {
    /* if it's unknown, something has gone wrong;  try to recover */
    if (!(here[2]))
    {
      err(warner, "IFAC: unknown factor seen in main loop");
      res = ifac_resort(partial, &here);
      if (res) return gzero;	/* can only happen in Moebius mode */
      ifac_whoiswho(partial, &here, -1);
      /* defrag for good measure */
      ifac_defrag(partial, &here);
      continue;
    }
    /* if it's composite, crack it */
    if (here[2] == zero)
    {
      /* make sure there's room for another factor */
      if (here < *partial + 6)
      {				/* try defrag first */
	ifac_defrag(partial, &here);
	if (here < *partial + 6) /* no luck */
	{
	  ifac_realloc(partial, &here, 1); /* guaranteed to work */
	  /* Unfortunately, we can't do a garbage collection here since we
	   * know too little about where in the stack the old components
	   * were.
	   */
	}
      }
      nf = ifac_crack(partial, &here);
      if (moebius_mode && here[1] != un) /* that was a power */
      {
	if (DEBUGLEVEL >= 3)
	{
	  fprintferr("IFAC: main loop: repeated new factor\n\t%Z\n", *here);
	  flusherr();
	}
	return gzero;
      }
      /* deal with the new unknowns.  No resort, since ifac_crack will
       * already have sorted them
       */
      ifac_whoiswho(partial, &here, nf);
      continue;
    }
    /* if it's prime but not yet finished, finish it */
    if (here[2] == un)
    {
      res = ifac_divide(partial, &here);
      if (res)
      {
	if (moebius_mode)
	{
	  if (DEBUGLEVEL >= 3)
	  {
	    fprintferr("IFAC: main loop: another factor was divisible by\n");
	    fprintferr("\t%Z\n", *here); flusherr();
	  }
	  return gzero;
	}
	ifac_defrag(partial, &here);
	(void)(ifac_resort(partial, &here)); /* sort new cofactors down */
	/* it doesn't matter right now whether this finds a repeated factor,
	 * since we never get to this point in Moebius mode
	 */
	ifac_defrag(partial, &here); /* resort may have created new gaps */
	ifac_whoiswho(partial, &here, -1);
      }
      continue;
    }
    /* there are no other cases, never reached */
    err(talker, "non-existent factor class in ifac_main");
  } /* while */
  if (moebius_mode && here[1] != un)
  {
    if (DEBUGLEVEL >= 3)
    {
      fprintferr("IFAC: after main loop: repeated old factor\n\t%Z\n", *here);
      flusherr();
    }
    return gzero; /* just a safety net */
  }
  if (DEBUGLEVEL >= 4)
  {
    long nf = (*partial + lg(*partial) - here - 3)/3;
    if (nf)
      fprintferr("IFAC: main loop: %ld factor%s left\n",
		 nf, (nf>1 ? "s" : ""));
    else
      fprintferr("IFAC: main loop: this was the last factor\n");
    flusherr();
  }
  return here;
}

/* Caller of the following should worry about stack management, it makes
 * a rather shameless mess :^)
 */
GEN
ifac_primary_factor(GEN *partial, long *exponent)
{
  GEN here = ifac_main(partial);
  GEN res;

  if (here == gun) { *exponent = 0; return gun; }
  else if (here == gzero) { *exponent = 0; return gzero; }

  res = icopy((GEN)(*here));
  *exponent = itos((GEN)(here[1]));
  here[2] = here[1] = *here = (long)NULL;
  return res;
}

/* encapsulated routines */

/* prime/exponent pairs need to appear contiguously on the stack, but we
 * also need to have our data structure somewhere, and we don't know in
 * advance how many primes will turn up.  The following discipline achieves
 * this:  When ifac_decomp() is called, n should point at an object older
 * than the oldest small prime/exponent pair  (auxdecomp0() guarantees
 * this easily since it mpdivis()es any divisors it discovers off its own
 * copy of the original N).  We allocate sufficient space to accommodate
 * several pairs -- eleven pairs ought to fit in a space not much larger
 * than n itself -- before calling ifac_start().  If we manage to complete
 * the factorization before we run out of space, we free the data structure
 * and cull the excess reserved space before returning.  When we do run out,
 * we have to leapfrog to generate more  (guesstimating the requirements
 * from what is left in the partial factorization structure);  room for
 * fresh pairs is allocated at the head of the stack, followed by an
 * ifac_realloc() to reconnect the data structure and move it out of the
 * way, followed by a few pointer tweaks to connect the new pairs space
 * to the old one.-- This whole affair translates into a surprisingly
 * compact little routine.
 */

#define ifac_overshoot 64	/* lgefint(n)+64 words reserved */
/* ifac_decomp_break: 
 *
 * Find primary factors of n until ifac_break return true, or n is
 * factored if ifac_break is NULL.
 */
/* ifac_break:
 *
 * state is for state management of the function, and depend of the
 * function.  ifac_break is called initially in decomp_break with
 * here=NULL.  This allows the function to see the new value of n.
 * return 1: stop factoring, 0 continue.  If ifac_break is NULL,
 * assumed to always return 0. ifac_break must not let anything on the
 * stack. However data can be stored in state
 */

long
ifac_decomp_break(GEN n, long (*ifac_break)(GEN n,GEN pairs,GEN here,GEN state),
		  GEN state, long hint)
{
  long tf=lgefint(n);
  gpmem_t av=avma, lim=stack_lim(av, 1);
  long nb=0;
  GEN part, here, workspc = new_chunk(tf + ifac_overshoot), pairs = (GEN)av;
  /* workspc will be doled out by us in pairs of smaller t_INTs */
  gpmem_t tetpil = avma;		/* remember head of workspc zone */;

  if (!n || typ(n) != t_INT) err(typeer, "ifac_decomp");
  if (!signe(n) || tf < 3) err(talker, "factoring 0 in ifac_decomp");

  part = ifac_start(n, 0, hint);
  here = ifac_main(&part);

  while (here != gun)
  {
    long lf=lgefint((GEN)(*here));
    if (pairs - workspc < lf + 3) /* out of room, leapfrog */
    {
      /* the ifac_realloc() below will clear tetpil - avma words
       * on the stack, which should be about enough for the extra
       * primes we're going to see, and we'll want several more to
       * accommodate further exponents.  In most cases, the lf + 3
       * below is pure paranoia, but the factor we're about to copy
       * might be the one sitting off the stack in the original n,
       * so let's play safe
       */
      workspc = new_chunk(lf + 3 + ifac_overshoot);
      ifac_realloc(&part, &here, 0);
      here = ifac_find(&part, &part);
      tetpil = (gpmem_t)workspc;
    }
    /* room enough now */
    nb++;
    pairs -= lf;
    *pairs = evaltyp(t_INT) | evallg(lf);
    affii((GEN)(*here), pairs);
    pairs -= 3;
    *pairs = evaltyp(t_INT) | evallg(3);
    affii((GEN)(here[1]), pairs);
    if (ifac_break && (*ifac_break)(n,pairs,here,state))
    {
      if (DEBUGLEVEL >= 3)
	fprintferr("IFAC: (Partial fact.)Stop requested.\n");
      break;
    }
    here[2] = here[1] = *here = (long)NULL;
    here = ifac_main(&part);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"[2] ifac_decomp");
      ifac_realloc(&part, &here, 0);
      part = gerepileupto(tetpil, part);
    }
  }
  avma = (gpmem_t)pairs;
  if (DEBUGLEVEL >= 3)
  {
    fprintferr("IFAC: found %ld large prime (power) factor%s.\n",
	       nb, (nb>1? "s": ""));
    flusherr();
  }
  return nb;
}

long
ifac_decomp(GEN n, long hint)
{
  return ifac_decomp_break(n, NULL, gzero, hint);
}

long
ifac_moebius(GEN n, long hint)
{
  long mu=1;
  gpmem_t av=avma, lim=stack_lim(av, 1);
  GEN part = ifac_start(n, 1, hint);
  GEN here = ifac_main(&part);

  while (here != gun && here != gzero)
  {
    if (itos((GEN)(here[1])) > 1)
    { here = gzero; break; }	/* shouldn't happen */
    mu = -mu;
    here[2] = here[1] = *here = (long)NULL;
    here = ifac_main(&part);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"ifac_moebius");
      ifac_realloc(&part, &here, 0);
      part = gerepileupto(av, part);
    }
  }
  avma = av;
  return (here == gun ? mu : 0);
}

long
ifac_issquarefree(GEN n, long hint)
{
  gpmem_t av=avma, lim=stack_lim(av, 1);
  GEN part = ifac_start(n, 1, hint);
  GEN here = ifac_main(&part);

  while (here != gun && here != gzero)
  {
    if (itos((GEN)(here[1])) > 1)
    { here = gzero; break; }	/* shouldn't happen */
    here[2] = here[1] = *here = (long)NULL;
    here = ifac_main(&part);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"ifac_issquarefree");
      ifac_realloc(&part, &here, 0);
      part = gerepileupto(av, part);
    }
  }
  avma = av;
  return (here == gun ? 1 : 0);
}

long
ifac_omega(GEN n, long hint)
{
  long omega=0;
  gpmem_t av=avma, lim=stack_lim(av, 1);
  GEN part = ifac_start(n, 0, hint);
  GEN here = ifac_main(&part);

  while (here != gun)
  {
    omega++;
    here[2] = here[1] = *here = (long)NULL;
    here = ifac_main(&part);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"ifac_omega");
      ifac_realloc(&part, &here, 0);
      part = gerepileupto(av, part);
    }
  }
  avma = av;
  return omega;
}

long
ifac_bigomega(GEN n, long hint)
{
  long Omega=0;
  gpmem_t av=avma, lim=stack_lim(av, 1);
  GEN part = ifac_start(n, 0, hint);
  GEN here = ifac_main(&part);

  while (here != gun)
  {
    Omega += itos((GEN)(here[1]));
    here[2] = here[1] = *here = (long)NULL;
    here = ifac_main(&part);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"ifac_bigomega");
      ifac_realloc(&part, &here, 0);
      part = gerepileupto(av, part);
    }
  }
  avma = av;
  return Omega;
}

GEN
ifac_totient(GEN n, long hint)
{
  GEN res = cgeti(lgefint(n));
  long exponent;
  gpmem_t av=avma, tetpil, lim=stack_lim(av, 1);
  GEN phi = gun;
  GEN part = ifac_start(n, 0, hint);
  GEN here = ifac_main(&part);

  while (here != gun)
  {
    phi = mulii(phi, addsi(-1, (GEN)(*here)));
    if (here[1] != un)
    {
      if (here[1] == deux)
      {
	phi = mulii(phi, (GEN)(*here));
      }
      else
      {
	exponent = itos((GEN)(here[1]));
	phi = mulii(phi, gpowgs((GEN)(*here), exponent-1));
      }
    }
    here[2] = here[1] = *here = (long)NULL;
    here = ifac_main(&part);
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gsav[2];
      if(DEBUGMEM>1) err(warnmem,"ifac_totient");
      tetpil = avma;
      ifac_realloc(&part, &here, 0);
      phi = icopy(phi);
      gsav[0] = &phi; gsav[1] = &part;
      gerepilemanysp(av, tetpil, gsav, 2);
      /* don't try to preserve here, safer to pick it up again
       * (and ifac_find does a lot of sanity checking at high
       * debuglevels)
       */
      here = ifac_find(&part, &part);
    }
  }
  affii(phi, res);
  avma = av;
  return res;
}

GEN
ifac_numdiv(GEN n, long hint)
{
  /* we don't preallocate since it's too hard to guess the right
   * size here
   */
  GEN res;
  gpmem_t av=avma, tetpil, lim=stack_lim(av, 1);
  GEN exponent, tau = gun;
  GEN part = ifac_start(n, 0, hint);
  GEN here = ifac_main(&part);

  while (here != gun)
  {
    exponent = (GEN)(here[1]);
    tau = mulii(tau, addsi(1, exponent));
    here[2] = here[1] = *here = (long)NULL;
    here = ifac_main(&part);
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gsav[2];
      if(DEBUGMEM>1) err(warnmem,"ifac_numdiv");
      tetpil = avma;
      ifac_realloc(&part, &here, 0);
      tau = icopy(tau);
      gsav[0] = &tau; gsav[1] = &part;
      gerepilemanysp(av, tetpil, gsav, 2);
      /* (see ifac_totient()) */
      here = ifac_find(&part, &part);
    }
  }
  tetpil = avma;
  res = icopy(tau);
  return gerepile(av, tetpil, res);
}

GEN
ifac_sumdiv(GEN n, long hint)
{
  /* don't preallocate */
  GEN res;
  long exponent;
  gpmem_t av=avma, tetpil, lim=stack_lim(av, 1);
  GEN contrib, sigma = gun;
  GEN part = ifac_start(n, 0, hint);
  GEN here = ifac_main(&part);

  while (here != gun)
  {
    exponent = itos((GEN)(here[1]));
    contrib = addsi(1, (GEN)(*here));
    for (; exponent > 1; exponent--)
      contrib = addsi(1, mulii((GEN)(*here), contrib));
    sigma = mulii(sigma, contrib);
    here[2] = here[1] = *here = (long)NULL;
    here = ifac_main(&part);
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gsav[2];
      if(DEBUGMEM>1) err(warnmem,"ifac_sumdiv");
      tetpil = avma;
      ifac_realloc(&part, &here, 0);
      sigma = icopy(sigma);
      gsav[0] = &sigma; gsav[1] = &part;
      gerepilemanysp(av, tetpil, gsav, 2);
      /* (see ifac_totient()) */
      here = ifac_find(&part, &part);
    }
  }
  tetpil = avma;
  res = icopy(sigma);
  return gerepile(av, tetpil, res);
}

/* k should be positive, and indeed it had better be > 1  (not checked).
 * The calling function knows what to do with the other cases.
 */
GEN
ifac_sumdivk(GEN n, long k, long hint)
{
  /* don't preallocate */
  GEN res;
  long exponent;
  gpmem_t av=avma, tetpil, lim=stack_lim(av, 1);
  GEN contrib, q, sigma = gun;
  GEN part = ifac_start(n, 0, hint);
  GEN here = ifac_main(&part);

  while (here != gun)
  {
    exponent = itos((GEN)(here[1]));
    q = gpowgs((GEN)(*here), k);
    contrib = addsi(1, q);
    for (; exponent > 1; exponent--)
      contrib = addsi(1, mulii(q, contrib));
    sigma = mulii(sigma, contrib);
    here[2] = here[1] = *here = (long)NULL;
    here = ifac_main(&part);
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gsav[2];
      if(DEBUGMEM>1) err(warnmem,"ifac_sumdivk");
      tetpil = avma;
      ifac_realloc(&part, &here, 0);
      sigma = icopy(sigma);
      gsav[0] = &sigma; gsav[1] = &part;
      gerepilemanysp(av, tetpil, gsav, 2);
      /* (see ifac_totient()) */
      here = ifac_find(&part, &part);
    }
  }
  tetpil = avma;
  res = icopy(sigma);
  return gerepile(av, tetpil, res);
}
