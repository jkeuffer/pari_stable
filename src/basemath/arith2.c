/*********************************************************************/
/**                                                                 **/
/**                     ARITHMETIC FUNCTIONS                        **/
/**                        (second part)                            **/
/**                                                                 **/
/*********************************************************************/
/* $Id$ */
#include "pari.h"

GEN arith_proto(long f(GEN), GEN x, int do_error);
GEN garith_proto(GEN f(GEN), GEN x, int do_error);
GEN garith_proto2gs(GEN f(GEN,long), GEN x, long y);
static long court_p[]={evaltyp(t_INT)|m_evallg(3),evalsigne(1)|evallgefint(3),0};

/***********************************************************************/
/**                                                                   **/
/**                          PRIME NUMBERS                            **/
/**                                                                   **/
/***********************************************************************/

GEN
prime(long n)
{
  byteptr p = diffptr;
  long c, prime = 0;

  if (n <= 0) err(talker, "n-th prime meaningless if n = %ld",n);
  while (n--)
  {
    c = *p++; if (!c) err(primer1);
    prime += c;
  }
  return stoi(prime);
}

GEN
primes(long n)
{
  byteptr p = diffptr;
  long c, prime = 0;
  GEN y,z;

  if (n < 0) n = 0;
  z = y = cgetg(n+1,t_VEC);
  while (n--)
  {
    c = *p++; if (!c) err(primer1);
    prime += c; *++z = lstoi(prime);
  }
  return y;
}

/* Building/Rebuilding the diffptr table. Incorporates Ilya Zakharevich's
 * block sweep algorithm  (see pari-dev-111, 25 April 1998).  The actual work
 * is done by the following two subroutines;  the user entry point is the
 * function initprimes() below.  initprimes1() is the old algorithm, called
 * when maxnum (size) is moderate.
 */
static byteptr
initprimes1(long size, long *lenp, long *lastp)
{
  long k;
  byteptr q,r,s,fin, p = (byteptr) gpmalloc(size+2);

  memset(p, 0, size + 2); fin = p + size;
  for (r=q=p,k=1; r<=fin; )
  {
    do { r+=k; k+=2; r+=k; } while (*++q);
    for (s=r; s<=fin; s+=k) *s=1;
  }
  r=p; *r++=2; *r++=1; /* 2 and 3 */
  for (s=q=r-1; ; s=q)
  {
    do q++; while (*q);
    if (q>fin) break;
    *r++ = (q-s) << 1;
  }
  *r++=0;
  *lenp = r - p;
  *lastp = ((s - p) << 1) + 1;
#if 0
  fprintferr("initprimes1: q = %ld, len = %ld, last = %ld\n",
	     q, *lenp, *lastp);
#endif
  return (byteptr) gprealloc(p,r-p,size + 2);
}

#define PRIME_ARENA (512 * 1024)

/* Here's the workhorse.  This is recursive, although normally the first
   recursive call will bottom out and invoke initprimes1() at once.
   (Not static;  might conceivably be useful to someone in library mode) */
byteptr
initprimes0(ulong maxnum, long *lenp, long *lastp)
{
  long k, size, alloced, asize, psize, rootnum, curlow, last, remains, need;
  byteptr q,r,s,fin, p, p1, fin1, plast, curdiff;

#if 0
  fprintferr("initprimes0: called for maxnum = %lu\n", maxnum);
#endif
  if (maxnum <= 1ul<<17)	/* Arbitrary. */
    return initprimes1(maxnum>>1, lenp, lastp);

  maxnum |= 1;			/* make it odd. */

  /* Checked to be enough up to 40e6, attained at 155893 */
  size = (long) (1.09 * maxnum/log((double)maxnum)) + 145;
  p1 = (byteptr) gpmalloc(size);
  rootnum = (long) sqrt((double)maxnum); /* cast it back to a long */
  rootnum |= 1;
#if 0
  fprintferr("initprimes0: rootnum = %ld\n", rootnum);
#endif
  {
    byteptr p2 = initprimes0(rootnum, &psize, &last); /* recursive call */
    memcpy(p1, p2, psize); free(p2);
  }
  fin1 = p1 + psize - 1;
  remains = (maxnum - rootnum) >> 1; /* number of odd numbers to check */

  need = 100 * rootnum;		/* Make % overhead negligeable. */
  if (need < PRIME_ARENA) need = PRIME_ARENA;
  if (avma - bot < need>>1) {	/* need to do our own allocation */
    alloced = 1; asize = need;
  } else {			/* scratch area is free part of PARI stack */
    alloced = 0; asize = avma - bot;
  }
  if (asize > remains) asize = remains + 1;/* + room for a sentinel byte */
  if (alloced)
    p = (byteptr) gpmalloc(asize);
  else
    p = (byteptr) bot;
  fin = p + asize - 1;		/* the 0 sentinel goes at fin. */
  curlow = rootnum + 2;		/* We know all primes up to rootnum (odd). */
  curdiff = fin1;

  /* During each iteration p..fin-1 represents a range of odd
     numbers.  plast is a pointer which represents the last prime seen,
     it may point before p..fin-1. */
  plast = p - ((rootnum - last) >> 1) - 1;
  while (remains)
  {
    if (asize > remains)
    {
      asize = remains + 1;
      fin = p + asize - 1;
    }
    memset(p, 0, asize);
    /* p corresponds to curlow.  q runs over primediffs.  */
    for (q = p1+2, k = 3; q <= fin1; k += *q++)
    {
      /* The first odd number which is >= curlow and divisible by p
       equals (if curlow > p)
	 the last odd number which is <= curlow + 2p - 1 and 0 (mod p)
       which equals
	 p + the last even number which is <= curlow + p - 1 and 0 (mod p)
       which equals
	 p + the last even number which is <= curlow + p - 2 and 0 (mod p)
       which equals
	 p + curlow + p - 2 - (curlow + p - 2)) % 2p.
       */
      long k2 = k*k - curlow;

      if (k2 > 0)
      {
	r = p + (k2 >>= 1);
	if (k2 > remains) break; /* Guard against an address wrap. */
      } else
	r = p - (((curlow+k-2) % (2*k)) >> 1) + k - 1;
      for (s = r; s < fin; s += k) *s = 1;
    }
    /* now q runs over addresses corresponding to primes */
    for (q = p; ; plast = q++)
    {
      while (*q) q++;		/* use 0-sentinel at end */
      if (q >= fin) break;
      *curdiff++ = (q - plast) << 1;
    }
    plast -= asize - 1;
    remains -= asize - 1;
    curlow += ((asize - 1)<<1);
  } /* while (remains) */
  last = curlow - ((p - plast) << 1);
  *curdiff++ = 0;		/* sentinel */
  *lenp = curdiff - p1;
  *lastp = last;
  if (alloced) free(p);
  return (byteptr) gprealloc(p1, *lenp, size);
}
#if 0 /* not yet... GN */
/* The diffptr table will contain at least 6548 entries (up to and including
   the 6547th prime, 65557, and the terminal null byte), because the isprime/
   small-factor-extraction machinery wants to depend on everything up to 65539
   being in the table, and we might as well go to a multiple of 4 Bytes.--GN */

void
init_tinyprimes_tridiv(byteptr p);	/* in ifactor2.c */
#endif
byteptr
initprimes(long maxnum)
{
  long len, last;
  byteptr p;
  /* The algorithm must see the next prime beyond maxnum, whence the +257. */
  /* switch to unsigned: adding the 257 _could_ wrap to a negative number. */
  ulong maxnum1 = ((maxnum<65302?65302:maxnum)+257ul);

  if (maxnum1 > 436273000)
    err(talker,"impossible to have prestored primes > 436273009");

  p = initprimes0(maxnum1, &len, &last);
#if 0 /* not yet... GN */
  static int build_the_tables = 1;
  if (build_the_tables) { init_tinyprimes_tridiv(p); build_the_tables=0; }
#endif
  return p;
}

static void
cleanprimetab(void)
{
  long i,j, lp = lg(primetab);

  for (i=j=1; i < lp; i++)
    if (primetab[i]) primetab[j++] = primetab[i];
  setlg(primetab,j);
}

/* primes is a single element or a row vector with "primes" to add to
 * primetab. If the "prime" shares a non-trivial factor with another element
 * in primetab, it is taken into account.
 */
GEN
addprimes(GEN prime)
{
  long i,tx, av = avma, lp = lg(primetab);
  GEN p1,p2;

  if (!prime) return primetab;
  tx = typ(prime);
  if (is_vec_t(tx))
  {
    for (i=1; i < lg(prime); i++) addprimes((GEN) prime[i]);
    return primetab;
  }
  if (tx != t_INT) err(typeer,"addprime");
  if (is_pm1(prime)) return primetab;
  i = signe(prime);
  if (i == 0) err(talker,"can't accept 0 in addprimes");
  if (i < 0) prime=absi(prime); 

  p1=cgetg(1,t_VEC);
  for (i=1; i < lp; i++)
  {
    p2 = mppgcd((GEN) primetab[i], prime);
    if (! gcmp1(p2))
    {
      if (!egalii(prime,p2)) p1=concatsp(p1,p2);
      p1 = concatsp(p1,divii((GEN)primetab[i],p2));
      gunclone((GEN)primetab[i]); primetab[i]=0;
    }
  }
  if (i == NUMPRTBELT+1 && lg(p1) == 1)
    err(talker,"extra primetable overflows");
  primetab[i] = lclone(prime); setlg(primetab, lp+1);
  cleanprimetab();
  if (lg(p1) > 1) addprimes(p1);
  avma=av; return primetab;
}

static GEN
removeprime(GEN prime)
{
  long i;

  if (typ(prime) != t_INT) err(typeer,"removeprime");
  for (i=lg(primetab) - 1; i; i--)
    if (absi_equal((GEN) primetab[i], prime))
    {
      gunclone((GEN)primetab[i]); primetab[i]=0;
      cleanprimetab(); break;
    }
  if (!i) err(talker,"prime %Z is not in primetable", prime);
  return primetab;
}

GEN
removeprimes(GEN prime)
{
  long i,tx;

  if (!prime) return primetab;
  tx = typ(prime);
  if (is_vec_t(tx))
  {
    if (prime == primetab)
    {
      for (i=1; i < lg(prime); i++) gunclone((GEN)prime[i]);
      setlg(prime, 1);
    }
    else
    {
      for (i=1; i < lg(prime); i++) removeprime((GEN) prime[i]);
    }
    return primetab;
  }
  return removeprime(prime);
}

/***********************************************************************/
/**                                                                   **/
/**       COMPUTING THE MATRIX OF PRIME DIVISORS AND EXPONENTS        **/
/**                                                                   **/
/***********************************************************************/

/* Configure may/should define this to 1 if MPQS is not installed --GN */
#ifndef decomp_default_hint
#define decomp_default_hint 0
#endif

/* Some overkill removed from this  (15 spsp for an integer < 2^32 ?!).
   Should really revert to isprime() once the new primality tester is ready
   --GN */
#define pseudoprime(p) millerrabin(p,3*lgefint(p))

/* where to stop trial dividing in factorization */

static long
tridiv_bound(GEN n, long all)
{
  long size = expi(n) + 1;
  if (all > 1)			/* bounded factoring */
    return all;			/* use the given limit */
  if (all == 0)
    return VERYBIGINT;		/* smallfact() case */
  if (size <= 32)
    return 16384;
  else if (size <= 512)
    return (size-16) << 10;
  return 1L<<19;		/* Rho will generally be faster above this */
}

/********** about to become obsolete --GN **********/
#if 0
/* If flag != 1, use the new MPQS code: Try to factor N using ECM if flag = 2
 * and N is not too small, followed by MPQS, or just MPQS otherwise.
 */
static GEN
find_fact(GEN N, long *flag)
{
  GEN f;

  if (*flag == 2)
  {
    if ((f = pollardbrent(N)))	/* assignment */
      return f;
    f = ellfacteur(N, 0);
    if (!f)
    {
      /* *flag = 0; */
      f = mpqs(N);
    }
  }
  else if (*flag == 1)
  {
    if ((f = pollardbrent(N)))	/* assignment */
      return f;
    f = ellfacteur(N, 1);
  }
  else
    f = mpqs(N);		/* may bail out and call ellfacteur(_,1) */
				/* (this is to be changed) */

  return f;
}
#endif
/***************************************************/

/* function imported from ifactor1.c */
long
ifac_decomp(GEN n, long hint);

static GEN
aux_end(GEN n, long nb)
{
  GEN p,p1,p2, z = (GEN)avma;
  long i;

  if (n) gunclone(n);
  p1=cgetg(nb+1,t_COL);
  p2=cgetg(nb+1,t_COL);
  for (i=nb; i; i--)
  {
    p2[i] = (long)z; z += lg(z);
    p1[i] = (long)z; z += lg(z);
  }
  z[1]=(long)p1;
  z[2]=(long)p2;
  if (nb)
  {
    long av = avma;
    GEN p1old = dummycopy(p1), p2old = dummycopy(p2);
    p=sindexsort(p1);
    for (i=1;i<=nb; i++)
    {
      p1[i]=p1old[p[i]];
      p2[i]=p2old[p[i]];
    }
    avma = av;
  }
  return z;
}

static GEN
auxdecomp0(GEN n, long all, long hint)
{
  long pp[] = { evaltyp(t_INT)|m_evallg(3), evalsigne(1)|evallgefint(3),2,0 };
  long nb = 0,i,k,lim1,av,lp;
  byteptr d=diffptr+1;

  if (typ(n) != t_INT) err(arither1);
  i=signe(n); if (!i) err(arither2);
  cgetg(3,t_MAT);
  if (i<0) { stoi(-1); stoi(1); nb++; }
  if (is_pm1(n)) return aux_end(NULL,nb);

  n = gclone(n);  setsigne(n,1);
  i = vali(n);
  if (i)
  {
    stoi(2); stoi(i); nb++;
    av=avma; affii(shifti(n,-i), n); avma=av;
  }
  if (is_pm1(n)) return aux_end(n,nb);
  lim1 = tridiv_bound(n, all);

  /* trial division */
  while (*d && pp[2] <= lim1)
  {
    pp[2] += *d++;
    if (mpdivis(n,pp,n))
    {
      nb++; k=1; while (mpdivis(n,pp,n)) k++;
      icopy(pp); stoi(k);
      if (is_pm1(n)) return aux_end(n,nb);
    }
  }

  /* pp = square of biggest p tried so far */
  av=avma; setlg(pp,4); affii(sqri(pp),pp); avma=av;
  if (cmpii(pp,n) > 0)
  {
    nb++;
    icopy(n); stoi(1); return aux_end(n,nb);
  }

  /* trial divide by the "special primes" (usually huge composites...) */
  lp = lg(primetab); k=0;
  for (i=1; i<lp; i++)
    if (mpdivis(n,(GEN) primetab[i],n))
    {
      nb++; k=1; while (mpdivis(n,(GEN) primetab[i],n)) k++;
      icopy((GEN) primetab[i]); stoi(k);
      if (is_pm1(n)) return aux_end(n,nb);
    }

  /* test primality */
  if ((k && cmpii(pp,n) > 0) || pseudoprime(n))
  {
    nb++;
    icopy(n); stoi(1); return aux_end(n,nb);
  }

  /* now we have a large composite.  Use hint as is if all==1 */
  if (all!=1) hint = 15; /* turn off everything except pure powers */
  nb += ifac_decomp(n, hint);

  return aux_end(n, nb);
}

GEN
auxdecomp(GEN n, long all)
{
  return auxdecomp0(n,all,decomp_default_hint);
}

/* see before ifac_crack() in ifactor1.c for current semantics of `hint'
   (factorint's `flag') */
GEN
factorint(GEN n, long flag)
{
  return auxdecomp0(n,1,flag);
}

GEN
decomp(GEN n)
{
  return auxdecomp0(n,1,decomp_default_hint);
}

GEN
smallfact(GEN n)
{
  return boundfact(n,0);
}

GEN
gboundfact(GEN n, long lim)
{
  return garith_proto2gs(boundfact,n,lim);
}

GEN
boundfact(GEN n, long lim)
{
  GEN p1,p2,p3,p4,p5,y;
  long av,tetpil;

  if (lim<=1) lim=0;
  switch(typ(n))
  {
    case t_INT:
      return auxdecomp(n,lim);
    case t_FRACN:
      av=avma; n=gred(n); /* fall through */
    case t_FRAC:
      if (typ(n)==t_FRAC) av=avma;
      p1=auxdecomp((GEN)n[1],lim);
      p2=auxdecomp((GEN)n[2],lim);
      p4=concatsp((GEN)p1[1],(GEN)p2[1]);
      p5=concatsp((GEN)p1[2],gneg((GEN)p2[2]));
      p3=indexsort(p4);

      tetpil=avma; y=cgetg(3,t_MAT);
      y[1]=(long)extract(p4,p3);
      y[2]=(long)extract(p5,p3);
      return gerepile(av,tetpil,y);
  }
  err(arither1);
  return NULL; /* not reached */
}

/***********************************************************************/
/**                                                                   **/
/**                    BASIC ARITHMETIC FUNCTIONS                     **/
/**                                                                   **/
/***********************************************************************/

/* functions imported from ifactor1.c */
long
ifac_moebius(GEN n, long hint);

long
ifac_issquarefree(GEN n, long hint);

long
ifac_omega(GEN n, long hint);

long
ifac_bigomega(GEN n, long hint);

GEN
ifac_totient(GEN n, long hint);

GEN
ifac_numdiv(GEN n, long hint);

GEN
ifac_sumdiv(GEN n, long hint);

GEN
ifac_sumdivk(GEN n, long k, long hint);

GEN
gmu(GEN n)
{
  return arith_proto(mu,n,1);
}

long
mu(GEN n)
{
  byteptr d = diffptr+1;	/* point at 3 - 2 */
  GEN p;
  long av = avma, lim1, s, v;

  if (typ(n) != t_INT) err(arither1);
  if (!signe(n)) err(arither2);
  if (is_pm1(n)) return 1;
  v = vali(n);
  if (v>1) return 0;
  s = v ? -1 : 1;
  n=absi(shifti(n,-v)); p=court_p; p[2]=2;
  if (is_pm1(n)) return s;
  lim1 = tridiv_bound(n,1);

  while (*d && p[2] < lim1)
  {
    p[2] += *d++;
    if (mpdivis(n,p,n))
    {
      if (divise(n,p)) { avma=av; return 0; }
      s = -s; if (is_pm1(n)) { avma=av; return s; }
    }
  }
  /* we normally get here with p==nextprime(PRE_TUNE), which will already
     have been tested against n, so p^2 >= n  (instead of p^2 > n)  is
     enough to guarantee n is prime */
  if (cmpii(sqri(p),n) >= 0 || pseudoprime(n)) { avma=av; return -s; }
  /* large composite without small factors */
  v = ifac_moebius(n, decomp_default_hint);
  avma=av;
  return (s<0 ? -v : v);	/* correct also if v==0 */
}

GEN
gissquarefree(GEN x)
{
  return arith_proto(issquarefree,x,0);
}

long
issquarefree(GEN x)
{
  long av=avma,lim1,tx;
  GEN p;

  if (gcmp0(x)) return 0;
  tx=typ(x);
  if (tx == t_INT)
  {
    long v;
    byteptr d=diffptr+1;
    if (is_pm1(x)) return 1;
    if((v = vali(x)) > 1) return 0;
    x=absi(shifti(x,-v)); p=court_p; p[2]=2;
    if (is_pm1(x)) return 1;
    lim1 = tridiv_bound(x,1);

    while (*d && p[2] < lim1)
    {
      p[2] += *d++;
      if (mpdivis(x,p,x))
      {
	if (divise(x,p)) { avma=av; return 0; }
	if (is_pm1(x)) { avma=av; return 1; }
      }
    }
    if (cmpii(sqri(p),x) >= 0 || pseudoprime(x)) { avma=av; return 1; }
    v = ifac_issquarefree(x, decomp_default_hint);
    avma=av;
    return v;
  }
  if (tx != t_POL) err(typeer,"issquarefree");
  p = ggcd(x, derivpol(x));
  avma=av; return (lgef(p)==3);
}

GEN
gomega(GEN n)
{
  return arith_proto(omega,n,1);
}

long
omega(GEN n)
{
  byteptr d=diffptr+1;
  GEN p;
  long nb,av=avma,lim1,v;

  if (typ(n) != t_INT) err(arither1);
  if (!signe(n)) err(arither2);
  if (is_pm1(n)) return 0;
  v=vali(n);
  nb = v ? 1 : 0;
  n=absi(shifti(n,-v)); p=court_p; p[2]=2;
  if (is_pm1(n)) return nb;
  lim1 = tridiv_bound(n,1);

  while (*d && p[2] < lim1)
  {
    p[2] += *d++;
    if (mpdivis(n,p,n))
    {
      nb++; while (mpdivis(n,p,n)); /* empty */
      if (is_pm1(n)) { avma = av; return nb; }
    }
  }
  if (cmpii(sqri(p),n) >= 0 || pseudoprime(n)) { avma = av; return nb+1; }
  /* large composite without small factors */
  nb += ifac_omega(n, decomp_default_hint);
  avma=av; return nb;
}

GEN
gbigomega(GEN n)
{
  return arith_proto(bigomega,n,1);
}

long
bigomega(GEN n)
{
  byteptr d=diffptr+1;
  GEN p;
  long nb,av=avma,lim1,v;

  if (typ(n) != t_INT) err(arither1);
  if (!signe(n)) err(arither2);
  if (is_pm1(n)) return 0;
  nb=v=vali(n);
  n=absi(shifti(n,-v)); p=court_p; p[2]=2;
  if (is_pm1(n)) { avma = av; return nb; }
  lim1 = tridiv_bound(n,1);

  while (*d && p[2] < lim1)
  {
    p[2] += *d++;
    if (mpdivis(n,p,n))
    {
      do nb++; while (mpdivis(n,p,n));
      if (is_pm1(n)) { avma = av; return nb; }
    }
  }
  if (cmpii(sqri(p),n) >= 0 || pseudoprime(n)) { avma = av; return nb+1; }
  nb += ifac_bigomega(n, decomp_default_hint);
  avma=av; return nb;
}

GEN
gphi(GEN n)
{
  return garith_proto(phi,n,1);
}

GEN
phi(GEN n)
{
  byteptr d = diffptr+1;
  GEN p,m;
  long av = avma, lim1, v;

  if (typ(n) != t_INT) err(arither1);
  if (!signe(n)) err(arither2);
  if (is_pm1(n)) return gun;
  v=vali(n);
  n=absi(shifti(n,-v)); p=court_p; p[2]=2;
  m = (v > 1 ? shifti(gun,v-1) : stoi(1));
  if (is_pm1(n)) { return gerepileupto(av,m); }
  lim1 = tridiv_bound(n,1);

  while (*d && p[2] < lim1)
  {
    court_p[2] += *d++;
    if (mpdivis(n,p,n))
    {
      m = mulii(m,addsi(-1,p));
      while (mpdivis(n,p,n)) m = mulii(m,p);
      if (is_pm1(n)) { return gerepileupto(av,m); }
    }
  }
  if (cmpii(sqri(p),n) >= 0 || pseudoprime(n))
  {
    m = mulii(m,addsi(-1,n));
    return gerepileupto(av,m);
  }
  m = mulii(m, ifac_totient(n, decomp_default_hint));
  return gerepileupto(av,m);
}

GEN
gnumbdiv(GEN n)
{
  return garith_proto(numbdiv,n,1);
}

GEN
numbdiv(GEN n)
{
  byteptr d=diffptr+1;
  GEN p,m;
  long l, av=avma, lim1, v;

  if (typ(n) != t_INT) err(arither1);
  if (!signe(n)) err(arither2);
  if (is_pm1(n)) return gun;
  v=vali(n);
  n=absi(shifti(n,-v)); p=court_p; p[2]=2;
  m = stoi(v+1);
  if (is_pm1(n)) { return gerepileupto(av,m); }
  lim1 = tridiv_bound(n,1);

  while (*d && p[2] < lim1)
  {
    p[2] += *d++;
    l=1; while (mpdivis(n,p,n)) l++;
    m = mulsi(l,m); if (is_pm1(n)) { return gerepileupto(av,m); }
  }
  if(cmpii(sqri(p),n) >= 0 || pseudoprime(n))
  {
    m = shifti(m,1);
    return gerepileupto(av,m);
  }
  m = mulii(m, ifac_numdiv(n, decomp_default_hint));
  return gerepileupto(av,m);
}

GEN
gsumdiv(GEN n)
{
  return garith_proto(sumdiv,n,1);
}

GEN
sumdiv(GEN n)
{
  byteptr d=diffptr+1;
  GEN p,m,m1;
  long av=avma,lim1,v;

  if (typ(n) != t_INT) err(arither1);
  if (!signe(n)) err(arither2);
  if (is_pm1(n)) return gun;
  v=vali(n);
  n=absi(shifti(n,-v)); p=court_p; p[2]=2;
  m = (v ? addsi(-1,shifti(gun,v+1)) : stoi(1));
  if (is_pm1(n)) { return gerepileupto(av,m); }
  lim1 = tridiv_bound(n,1);

  while (*d && p[2] < lim1)
  {
    p[2] += *d++;
    if (mpdivis(n,p,n))
    {
      m1=addsi(1,p);
      while (mpdivis(n,p,n)) m1=addsi(1,mulii(p,m1));
      m = mulii(m1,m); if (is_pm1(n)) { return gerepileupto(av,m); }
    }
  }
  if(cmpii(sqri(p),n) >= 0 || pseudoprime(n))
  {
    m = mulii(m,addsi(1,n));
    return gerepileupto(av,m);
  }
  m = mulii(m, ifac_sumdiv(n, decomp_default_hint));
  return gerepileupto(av,m);
}

GEN
gsumdivk(GEN n, long k)
{
  return garith_proto2gs(sumdivk,n,k);
}

GEN
sumdivk(GEN n, long k)
{
  byteptr d=diffptr+1;
  GEN p,p1,m,m1,pk;
  long av=avma,tetpil,k1,lim1,v;

  if (!k) return numbdiv(n);
  if (k==1) return sumdiv(n);
  if (typ(n) != t_INT) err(arither1);
  if (!signe(n)) err(arither2);
  if (is_pm1(n)) return gun;
  k1=k;
  if (k==-1) { p1=ginv(n); m=sumdiv(n); goto fin; }
  if (k<0) { k= -k; p1=gpuigs(n,k1); }
  v=vali(n);
  n=absi(shifti(n,-v));
  p = court_p; p[2]=2; m=stoi(1);
  while (v--) { m=addsi(1,shifti(m,k)); }
  if (is_pm1(n)) goto fin;
  lim1 = tridiv_bound(n,1);

  while (*d && p[2] < lim1)
  {
    p[2] += *d++;
    if (mpdivis(n,p,n))
    {
      pk=gpuigs(p,k); m1=addsi(1,pk);
      while (mpdivis(n,p,n)) m1=addsi(1,mulii(pk,m1));
      m = mulii(m1,m); if (is_pm1(n)) goto fin;
    }
  }
  if(cmpii(sqri(p),n) >= 0 || pseudoprime(n))
  {
    pk=gpuigs(n,k);
    m = mulii(m,addsi(1,pk));
    goto fin;
  }
  m = mulii(m, ifac_sumdivk(n, k, decomp_default_hint));
 fin:
  if (k1>=0) return gerepileupto(av,m);
  tetpil=avma; return gerepile(av,tetpil,gmul(p1,m));
}

/***********************************************************************/
/**                                                                   **/
/**                MISCELLANEOUS ARITHMETIC FUNCTIONS                 **/
/**         (all of these ultimately depend on auxdecomp())           **/
/**                                                                   **/
/***********************************************************************/

GEN
divisors(GEN n)
{
  long tetpil,av=avma,i,j,l;
  GEN *d,*t,*t1,*t2,*t3, nbdiv,e;
  
  if (typ(n) != t_MAT || lg(n) != 3) n = auxdecomp(n,1);

  e = (GEN) n[2], n = (GEN) n[1]; l = lg(n);
  if (l>1 && signe(n[1]) < 0) { e++; n++; l--; } /* skip -1 */
  nbdiv = gun;
  for (i=1; i<l; i++) 
  {
    e[i] = itos((GEN)e[i]);
    nbdiv = mulis(nbdiv,1+e[i]);
  }
  if (is_bigint(nbdiv) || (itos(nbdiv) & ~LGBITS))
    err(talker, "too many divisors (more than %ld)", LGBITS - 1);
  d = t = (GEN*) cgetg(itos(nbdiv)+1,t_VEC);
  *++d = gun;
  for (i=1; i<l; i++)
    for (t1=t,j=e[i]; j; j--,t1=t2)
      for (t2=d,t3=t1; t3<t2; )
	*++d = mulii(*++t3, (GEN)n[i]);
  tetpil=avma; return gerepile(av,tetpil,sort((GEN)t));
}

GEN
core(GEN n)
{
  long av=avma,tetpil,i;
  GEN fa,p1,p2,res=gun;

  fa=auxdecomp(n,1); p1=(GEN)fa[1]; p2=(GEN)fa[2];
  for (i=1; i<lg(p1); i++)
    if (mod2((GEN)p2[i])) res = mulii(res,(GEN)p1[i]);
  tetpil=avma; return gerepile(av,tetpil,icopy(res));
}

GEN
core2(GEN n)
{
  long av=avma,tetpil,i;

  GEN fa,p1,p2,p3,res=gun,res2=gun,y;

  fa=auxdecomp(n,1); p1=(GEN)fa[1]; p2=(GEN)fa[2];
  for (i=1; i<lg(p1); i++)
  {
    p3=(GEN)p2[i];
    if (mod2(p3)) res=mulii(res,(GEN)p1[i]);
    if (!gcmp1(p3)) res2=mulii(res2,gpui((GEN)p1[i],shifti(p3,-1),0));
  }
  tetpil=avma; y=cgetg(3,t_VEC);
  y[1]=(long)icopy(res); y[2]=(long)icopy(res2);
  return gerepile(av,tetpil,y);
}

GEN
core0(GEN n,long flag)
{
  return flag? core2(n): core(n);
}

GEN
coredisc(GEN n)
{
  long av=avma,tetpil,r;
  GEN p1=core(n);

  r=mod4(p1); if (signe(p1)<0) r = 4-r;
  if (r==1 || r==4) return p1;
  tetpil=avma; return gerepile(av,tetpil,shifti(p1,2));
}

GEN
coredisc2(GEN n)
{
  long av=avma,tetpil,r;
  GEN y,p1,p2=core2(n);

  p1=(GEN)p2[1]; r=mod4(p1); if (signe(p1)<0) r=4-r;
  if (r==1 || r==4) return p2;
  tetpil=avma; y=cgetg(3,t_VEC);
  y[1]=lshifti(p1,2); y[2]=lmul2n((GEN)p2[2],-1);
  return gerepile(av,tetpil,y);
}

GEN
coredisc0(GEN n,long flag)
{
  return flag? coredisc2(n): coredisc(n);
}

/***********************************************************************/
/**                                                                   **/
/**                      BINARY QUADRATIC FORMS                       **/
/**                                                                   **/
/***********************************************************************/

GEN
qf_disc(GEN x, GEN y, GEN z)
{
  if (!y) { y=(GEN)x[2]; z=(GEN)x[3]; x=(GEN)x[1]; }
  return subii(sqri(y), shifti(mulii(x,z),2));
}

static GEN
qf_create(GEN x, GEN y, GEN z, long s)
{
  GEN t;
  if (typ(x)!=t_INT || typ(y)!=t_INT || typ(z)!=t_INT) err(typeer,"Qfb");
  if (!s)
  {
    long av=avma; s = signe(qf_disc(x,y,z)); avma=av;
    if (!s) err(talker,"zero discriminant in Qfb");
  }
  t = (s>0)? cgetg(5,t_QFR): cgetg(4,t_QFI);
  t[1]=(long)icopy(x); t[2]=(long)icopy(y); t[3]=(long)icopy(z);
  return t;
}

GEN
qfi(GEN x, GEN y, GEN z)
{
  return qf_create(x,y,z,-1);
}

GEN
qfr(GEN x, GEN y, GEN z, GEN d)
{
  GEN t = qf_create(x,y,z,1);
  if (typ(d) != t_REAL)
    err(talker,"Shanks distance should be a t_REAL (in qfr)");
  t[4]=lrcopy(d); return t;
}

GEN
Qfb0(GEN x, GEN y, GEN z, GEN d, long prec)
{
  GEN t = qf_create(x,y,z,0);
  if (lg(t)==4) return t;
  if (!d) d = gzero;
  if (typ(d) == t_REAL)
    t[4] = lrcopy(d);
  else
    { t[4]=lgetr(prec); gaffect(d,(GEN)t[4]); }
  return t;
}

/* composition */

static void
comp_gen(GEN z,GEN x,GEN y)
{
  GEN s,n,d,d1,x1,x2,y1,y2,v1,v2,v3,b3,c3,m,p1,r;

  s=shifti(addii((GEN)x[2],(GEN)y[2]),-1);
  n=subii((GEN)y[2],s);
  d = bezout((GEN)y[1],(GEN)x[1],&y1,&x1);
  d1 = bezout(s,d,&x2,&y2);
  if (gcmp1(d1))
  {
    v3 = (GEN)x[1];
    v2 = (GEN)y[1];
  }
  else
  {
    v1=divii((GEN)x[1],d1);
    v2=divii((GEN)y[1],d1);
    v3 = mulii(v1, mppgcd(d1,mppgcd((GEN)x[3],mppgcd((GEN)y[3],n))));
  }
  m = addii(mulii(mulii(y1,y2),n), mulii((GEN)y[3],x2));
  setsigne(m,-signe(m));
  r=modii(m,v3); p1=mulii(v2,r); b3=shifti(p1,1);
  c3=addii(mulii((GEN)y[3],d1),mulii(r,addii((GEN)y[2],p1)));
  z[1]=lmulii(v3,v2);
  z[2]=laddii((GEN)y[2],b3);
  z[3]=ldivii(c3,v3);
}

static GEN
compimag0(GEN x, GEN y, int raw)
{
  long tx = typ(x), av = avma, tetpil;
  GEN z;

  if (typ(y) != tx || tx!=t_QFI) err(typeer,"composition");
  if (cmpii((GEN)x[1],(GEN)y[1]) > 0) { z=x; x=y; y=z; }
  z=cgetg(4,t_QFI); comp_gen(z,x,y); tetpil=avma;
  return gerepile(av,tetpil,raw? gcopy(z): redimag(z));
}

static GEN
compreal0(GEN x, GEN y, int raw)
{
  long tx = typ(x), av = avma, tetpil;
  GEN z;

  if (typ(y) != tx || tx!=t_QFR) err(typeer,"composition");
  z=cgetg(5,t_QFR); comp_gen(z,x,y);
  z[4]=laddrr((GEN)x[4],(GEN)y[4]); tetpil=avma;
  return gerepile(av,tetpil, raw? gcopy(z): redreal(z));
}

GEN
compreal(GEN x, GEN y) { return compreal0(x,y,0); }

GEN
comprealraw(GEN x, GEN y) { return compreal0(x,y,1); }

GEN
compimag(GEN x, GEN y) { return compimag0(x,y,0); }

GEN
compimagraw(GEN x, GEN y) { return compimag0(x,y,1); }

GEN
compraw(GEN x, GEN y)
{
  return (typ(x)==t_QFI)? compimagraw(x,y): comprealraw(x,y);
}

static void
sq_gen(GEN z, GEN x)
{
  GEN d1,x2,y2,v1,v3,b3,c3,m,p1,r;

  d1 = bezout((GEN)x[2],(GEN)x[1],&x2,&y2);
  if (gcmp1(d1)) v1 = v3 = (GEN)x[1];
  else
  {
    v1 = divii((GEN)x[1],d1);
    v3 = mulii(v1,mppgcd(d1,(GEN)x[3]));
  }
  m=mulii((GEN)x[3],x2); setsigne(m,-signe(m));
  r=modii(m,v3); p1=mulii(v1,r); b3=shifti(p1,1);
  c3=addii(mulii((GEN)x[3],d1),mulii(r,addii((GEN)x[2],p1)));
  z[1]=lmulii(v3,v1);
  z[2]=laddii((GEN)x[2],b3);
  z[3]=ldivii(c3,v3);
}

GEN
sqcompimag0(GEN x, long raw)
{
  long av = avma, tetpil;
  GEN z = cgetg(4,t_QFI);

  if (typ(x)!=t_QFI) err(typeer,"composition");
  sq_gen(z,x); tetpil=avma;
  return gerepile(av,tetpil,raw? gcopy(z): redimag(z));
}

static GEN
sqcompreal0(GEN x, long raw)
{
  long av = avma, tetpil;
  GEN z = cgetg(5,t_QFR);

  if (typ(x)!=t_QFR) err(typeer,"composition");
  sq_gen(z,x); z[4]=lshiftr((GEN)x[4],1); tetpil=avma;
  return gerepile(av,tetpil,raw? gcopy(z): redreal(z));
}

GEN
sqcompreal(GEN x) { return sqcompreal0(x,0); }

GEN
sqcomprealraw(GEN x) { return sqcompreal0(x,1); }

GEN
sqcompimag(GEN x) { return sqcompimag0(x,0); }

GEN
sqcompimagraw(GEN x) { return sqcompimag0(x,1); }

GEN
real_unit_form(GEN x)
{
  long av = avma, tetpil,prec;
  GEN p1,p2, y = cgetg(5,t_QFR);

  y[1]=un; p1=qf_disc(x,NULL,NULL); p2=racine(p1);
  /* we know that p1 and p2 are non-zero */
  if (mod2(p1) != mod2(p2)) p2=addsi(-1,p2);
  y[2]=(long)p2;
  y[3]=lshifti(subii(sqri(p2),p1),-2);
  prec = precision((GEN)x[4]);
  if (!prec)
    err(talker,"not a type real in 4th component of a t_QFR");
  y[4]=(long)realzero(prec); tetpil=avma;
  return gerepile(av,tetpil,gcopy(y));
}

GEN
imag_unit_form(GEN x)
{
  long av,tetpil;
  GEN p1,p2, y = cgetg(4,t_QFI);
  y[1]=un;
  y[2]=mpodd((GEN)x[2])? un: zero;
  av=avma; p1=mulii((GEN)x[1],(GEN)x[3]);
  p2=shifti(sqri((GEN)x[2]),-2); tetpil=avma;
  y[3]=lpile(av,tetpil,subii(p1,p2));
  return y;
}

GEN
powrealraw(GEN x, long n)
{
  long av = avma, m;
  GEN y;

  if (typ(x) != t_QFR)
    err(talker,"not a real quadratic form in powreal");
  if (!n) return real_unit_form(x);
  if (n== 1) return gcopy(x);
  if (n==-1) return ginv(x);

  y = NULL; m=labs(n);
  for (; m>1; m>>=1)
  {
    if (m&1) y = y? comprealraw(y,x): x;
    x=sqcomprealraw(x);
  }
  y = y? comprealraw(y,x): x;
  if (n<0) y = ginv(y);
  return gerepileupto(av,y);
}

GEN
powimagraw(GEN x, long n)
{
  long av = avma, m;
  GEN y;

  if (typ(x) != t_QFI)
    err(talker,"not an imaginary quadratic form in powimag");
  if (!n) return imag_unit_form(x);
  if (n== 1) return gcopy(x);
  if (n==-1) return ginv(x);

  y = NULL; m=labs(n);
  for (; m>1; m>>=1)
  {
    if (m&1) y = y? compimagraw(y,x): x;
    x=sqcompimagraw(x);
  }
  y = y? compimagraw(y,x): x;
  if (n<0) y = ginv(y);
  return gerepileupto(av,y);
}

GEN
powraw(GEN x, long n)
{
  return (typ(x)==t_QFI)? powimagraw(x,n): powrealraw(x,n);
}

/* composition: Shanks' NUCOMP & NUDUPL */
/* l = floor((|d|/4)^(1/4)) */
GEN
nucomp(GEN x, GEN y, GEN l)
{
  long av=avma,tetpil,cz;
  GEN a,a1,a2,b,b2,d,d1,e,g,n,p1,p2,p3,q1,q2,q3,q4,s,t2,t3,u,u1,v,v1,v2,v3,z;

  if (x==y) return nudupl(x,l);
  if (typ(x) != t_QFI || typ(y) != t_QFI)
    err(talker,"not an imaginary quadratic form in nucomp");

  if (cmpii((GEN)x[1],(GEN)y[1]) < 0) { s=x; x=y; y=s; }
  s=shifti(addii((GEN)x[2],(GEN)y[2]),-1); n=subii((GEN)y[2],s);
  a1=(GEN)x[1]; a2=(GEN)y[1]; d=bezout(a2,a1,&u,&v);
  if (gcmp1(d)) { a=negi(gmul(u,n)); d1=d; }
  else
    if (divise(s,d))
    {
      a=negi(gmul(u,n)); d1=d; a1=divii(a1,d1);
      a2=divii(a2,d1); s=divii(s,d1);
    }
    else
    {
      d1=bezout(s,d,&u1,&v1);
      if (!gcmp1(d1))
      {
	a1=divii(a1,d1); a2=divii(a2,d1);
	s=divii(s,d1); d=divii(d,d1);
      }
      p1=resii((GEN)x[3],d); p2=resii((GEN)y[3],d);
      p3=modii(negi(mulii(u1,addii(mulii(u,p1),mulii(v,p2)))),d);
      a=subii(mulii(p3,divii(a1,d)),mulii(u,divii(n,d)));
    }
  a=modii(a,a1); p1=subii(a1,a); if (cmpii(a,p1)>0) a=negi(p1);
  v=gzero; d=a1; v2=gun; v3=a;
  for (cz=0; absi_cmp(v3,l) > 0; cz++)
  {
    p1=dvmdii(d,v3,&t3); t2=subii(v,mulii(p1,v2));
    v=v2; d=v3; v2=t2; v3=t3;
  }
  z=cgetg(4,t_QFI);
  if (!cz)
  {
    q1=mulii(a2,v3); q2=addii(q1,n);
    g=divii(addii(mulii(v3,s),(GEN)y[3]),d);
    z[1]=lmulii(d,a2);
    z[2]=laddii(shifti(q1,1),(GEN)y[2]);
    z[3]=laddii(mulii(v3,divii(q2,d)), mulii(g,d1));
  }
  else
  {
    if (cz&1) { v3=negi(v3); v2=negi(v2); }
    b=divii(addii(mulii(a2,d),mulii(n,v)),a1);
    q1=mulii(b,v3); q2=addii(q1,n);
    e=divii(addii(mulii(s,d),mulii((GEN)y[3],v)),a1);
    q3=mulii(e,v2); q4=subii(q3,s);
    g=divii(q4,v); b2=addii(q3,q4);
    if (!gcmp1(d1)) { v2=mulii(d1,v2); v=mulii(d1,v); b2=mulii(d1,b2); }
    z[1]=laddii(mulii(d,b),mulii(e,v));
    z[2]=laddii(b2,addii(q1,q2));
    z[3]=laddii(mulii(v3,divii(q2,d)), mulii(g,v2));
  }
  tetpil=avma; return gerepile(av,tetpil,redimag(z));
}

GEN
nudupl(GEN x, GEN l)
{
  long av=avma,tetpil,cz;
  GEN u,v,d,d1,p1,a,b,c,b2,z,v2,v3,t2,t3,e,g;

  if (typ(x) != t_QFI)
    err(talker,"not an imaginary quadratic form in nudupl");
  d1=bezout((GEN)x[2],(GEN)x[1],&u,&v);
  a=divii((GEN)x[1],d1); b=divii((GEN)x[2],d1);
  c=modii(negi(mulii(u,(GEN)x[3])),a); p1=subii(a,c);
  if (cmpii(c,p1)>0) c=negi(p1);
  v=gzero; d=a; v2=gun; v3=c;
  for (cz=0; absi_cmp(v3,l) > 0; cz++)
  {
    p1=dvmdii(d,v3,&t3); t2=subii(v,mulii(p1,v2));
    v=v2; d=v3; v2=t2; v3=t3;
  }
  z=cgetg(4,t_QFI);
  if (!cz)
  {
    g=divii(addii(mulii(v3,b),(GEN)x[3]),d);
    z[1]=(long)sqri(d);
    z[2]=laddii((GEN)x[2],shifti(mulii(d,v3),1));
    z[3]=laddii(sqri(v3),mulii(g,d1));
  }
  else
  {
    if (cz&1) { v=negi(v); d=negi(d); }
    e=divii(addii(mulii((GEN)x[3],v),mulii(b,d)),a);
    g=divii(subii(mulii(e,v2),b),v);
    b2=addii(mulii(e,v2),mulii(v,g));
    if (!gcmp1(d1)) { v2=mulii(d1,v2); v=mulii(d1,v); b2=mulii(d1,b2); }
    z[1]=laddii(sqri(d),mulii(e,v));
    z[2]=laddii(b2,shifti(mulii(d,v3),1));
    z[3]=laddii(sqri(v3),mulii(g,v2));
  }
  tetpil=avma; return gerepile(av,tetpil,redimag(z));
}

GEN
nupow(GEN x, GEN n)
{
  long av,tetpil,i,j;
  unsigned long m;
  GEN y,l;

  if (typ(n) != t_INT) err(talker,"not an integer exponent in nupow");
  if (gcmp1(n)) return gcopy(x);
  av=avma; y = imag_unit_form(x);
  if (!signe(n)) return y;

  l = racine(shifti(racine((GEN)y[3]),1));
  for (i=lgefint(n)-1; i>2; i--)
    for (m=n[i],j=0; j<BITS_IN_LONG; j++,m>>=1)
    {
      if (m&1) y=nucomp(y,x,l);
      x=nudupl(x,l);
    }
  for (m=n[2]; m>1; m>>=1)
  {
    if (m&1) y=nucomp(y,x,l);
    x=nudupl(x,l);
  }
  tetpil=avma; y=nucomp(y,x,l);
  if (signe(n)<0 && !egalii((GEN)y[1],(GEN)y[2])
                 && !egalii((GEN)y[1],(GEN)y[3]))
    setsigne(y[2],-signe(y[2]));
  return gerepile(av,tetpil,y);
}

/* reduction */

static GEN
abs_dvmdii(GEN b, GEN p1, GEN *pt, long s)
{
  if (s<0) setsigne(b, 1); p1 = dvmdii(b,p1,pt);
  if (s<0) setsigne(b,-1); return p1;
}

static GEN
rhoimag0(GEN x, long *flag)
{
  GEN p1,b,d,z;
  long fl, s = signe(x[2]);

  fl = cmpii((GEN)x[1], (GEN)x[3]);
  if (fl <= 0)
  {
    long fg = absi_cmp((GEN)x[1], (GEN)x[2]);
    if (fg >= 0)
    {
      *flag = (s<0 && (!fl || !fg))? 2 /* set x[2] = negi(x[2]) in caller */
                                   : 1;
      return x;
    }
  }
  p1=shifti((GEN)x[3],1); d = abs_dvmdii((GEN)x[2],p1,&b,s);
  if (s>=0)
  {
    setsigne(d,-signe(d));
    if (cmpii(b,(GEN)x[3])<=0) setsigne(b,-signe(b));
    else { d=addsi(-1,d); b=subii(p1,b); }
  }
  else if (cmpii(b,(GEN)x[3])>=0) { d=addsi(1,d); b=subii(b,p1); }

  z=cgetg(4,t_QFI);
  z[1] = x[3];
  z[3] = laddii((GEN)x[1], mulii(d,shifti(subii((GEN)x[2],b),-1)));
  if (signe(b)<0 && !fl) setsigne(b,1);
  z[2] = (long)b; *flag = 0; return z;
}

/* if sqrtD != NULL, compute Shanks' distance as well */
static GEN
rhoreal0(GEN x, GEN D, GEN isqrtD, GEN sqrtD)
{
  long s = signe(x[3]);
  GEN p1,p2, z = cgetg(5,t_QFR);

  if (!sqrtD)
    z[4] = x[4];
  else
  {
    p1 = divrr(addir((GEN)x[2],sqrtD), subir((GEN)x[2],sqrtD));
    if (signe(p1)<0) setsigne(p1,1); /* p1 = |(b+sqrtD) / (b-sqrtD)| */
    z[4] = laddrr(shiftr(mplog(p1),-1), (GEN) x[4]);
  }
  z[1] = x[3]; setsigne(z[1],1);
  p1=shifti((GEN)z[1],1);
  p2 = (cmpii(isqrtD,(GEN)z[1]) >= 0)? isqrtD: (GEN)z[1];
  p2 = divii(addii(p2,(GEN)x[2]),p1);
  z[2] = lsubii(mulii(p2,p1), (GEN)x[2]);

  setsigne(z[1],s);
  p1=shifti(subii(sqri((GEN)z[2]),D),-2);
  z[3] = ldivii(p1,(GEN)z[1]); return z;
}

static GEN
redreal0(GEN x, long flag, GEN D, GEN isqrtD, GEN sqrtD)
{
  long av=avma,l,step, use_d;

  if (typ(x) != t_QFR) err(talker,"not a real quadratic form in redreal");
  switch(flag)
  {
    case 0: use_d=1; step=0; break;
    case 1: use_d=1; step=1; break;
    case 2: use_d=0; step=0; break;
    case 3: use_d=0; step=1; break;
    default: err(flagerr,"qfbred");
  }

  if (!D) D = qf_disc(x,NULL,NULL);
  else if (typ(D) != t_INT) err(arither1);

  if (!isqrtD || (use_d && !sqrtD))
  {
    l=max(lg(x[4]),3);
    l=max(l,((BITS_IN_LONG-1-expo(x[4]))>>TWOPOTBITS_IN_LONG)+2);
    sqrtD=gsqrt(D,l); isqrtD=mptrunc(sqrtD);
  }
  else
  {
    if (typ(isqrtD) != t_INT) err(arither1);
    if (sqrtD)
    {
      l=typ(sqrtD); if (!is_intreal_t(l)) err(arither1);
    }
  }
  if (step)
    x = rhoreal0(x,D,isqrtD,sqrtD);
  else
    for(;;)
    {
      if (signe(x[2]) > 0 && cmpii((GEN)x[2],isqrtD) <= 0 )
      {
        GEN p1=subii(isqrtD, shifti(absi((GEN)x[1]),1));

        l = absi_cmp((GEN)x[2],p1);
        if (l>0 || (l==0 && signe(p1)<0)) break;
      }
      x = rhoreal0(x,D,isqrtD,sqrtD);
    }
  l=avma; return gerepile(av,l,gcopy(x));
}

GEN
redimag(GEN x)
{
  long av=avma, tetpil, fl;
  do x = rhoimag0(x, &fl); while (fl == 0);
  tetpil=avma; x = gerepile(av,tetpil,gcopy(x));
  if (fl == 2) setsigne(x[2], -signe(x[2]));
  return x;
}

GEN
redreal(GEN x)
{
  return redreal0(x,0,NULL,NULL,NULL);
}

GEN
rhoreal(GEN x)
{
  return redreal0(x,1,NULL,NULL,NULL);
}

GEN
redrealnod(GEN x, GEN isqrtD)
{
  return redreal0(x,2,NULL,isqrtD,NULL);
}

GEN
rhorealnod(GEN x, GEN isqrtD)
{
  return redreal0(x,3,NULL,isqrtD,NULL);
}

GEN
qfbred0(GEN x, long flag, GEN D, GEN isqrtD, GEN sqrtD)
{
  long tx=typ(x),av,tetpil,fl;

  if (!is_qf_t(tx)) err(talker,"not a quadratic form in qfbred");
  if (!D) D = qf_disc(x,NULL,NULL);
  switch(signe(D))
  {
    case 1 :
      return redreal0(x,flag,D,isqrtD,sqrtD);

    case -1:
      if (!flag) return  redimag(x);
      if (flag !=1) err(flagerr,"qfbred");
      av=avma; x = rhoimag0(x,&fl); tetpil=avma;
      x = gerepile(av,tetpil,gcopy(x));
      if (fl == 2) setsigne(x[2], -signe(x[2]));
      return x;
  }
  err(redpoler,"qfbred");
  return NULL; /* not reached */
}

GEN
primeform(GEN x, GEN p, long prec)
{
  long av,tetpil,s=signe(x);
  GEN y,b;

  if (typ(x) != t_INT || !s) err(arither1);
  if (typ(p) != t_INT || signe(p) <= 0) err(arither1);
  if (s < 0)
  {
    y = cgetg(4,t_QFI); s = 8-mod8(x);
  }
  else
  {
    y = cgetg(5,t_QFR); s = mod8(x);
    y[4]=(long)realzero(prec);
  }
  switch(s&3)
  {
    case 2: case 3: err(funder2,"primeform");
  }
  y[1] = (long)icopy(p); av=avma;
  if (egalii(p,gdeux))
  {
    switch(s)
    {
      case 0: y[2]=zero; break;
      case 8: s=0; y[2]=zero; break;
      case 1: s=1; y[2]=un; break;
      case 4: s=4; y[2]=deux; break;
      default: err(sqrter5);
    }
    b=subsi(s,x); tetpil=avma; b=shifti(b,-3);
  }
  else
  {
    b = mpsqrtmod(x,p); if (!b) err(sqrter5);
    if (mod2(b) == mod2(x)) y[2] = (long)b;
    else
    { tetpil = avma; y[2] = lpile(av,tetpil,subii(p,b)); }

    av=avma; b=shifti(subii(sqri((GEN)y[2]),x),-2);
    tetpil=avma; b=divii(b,p);
  }
  y[3]=lpile(av,tetpil,b); return y;
}
