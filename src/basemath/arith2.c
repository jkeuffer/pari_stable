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

/*********************************************************************/
/**                                                                 **/
/**                     ARITHMETIC FUNCTIONS                        **/
/**                        (second part)                            **/
/**                                                                 **/
/*********************************************************************/
#include "pari.h"

extern GEN arith_proto(long f(GEN), GEN x, int do_error);
extern GEN arith_proto2(long f(GEN,GEN), GEN x, GEN n);
extern GEN garith_proto(GEN f(GEN), GEN x, int do_error);
extern GEN garith_proto2gs(GEN f(GEN,long), GEN x, long y);
extern GEN garith_proto3ggs(GEN f(GEN,GEN,long), GEN x, GEN y, long z);

#define sqru(i) (muluu((i),(i)))

/***********************************************************************/
/**                                                                   **/
/**                          PRIME NUMBERS                            **/
/**                                                                   **/
/***********************************************************************/

GEN
prime(long n)
{
  byteptr p = diffptr;
  long prime = 0;

  if (n <= 0) err(talker, "n-th prime meaningless if n = %ld",n);
  while (n--)
  {
    NEXT_PRIME_VIADIFF_CHECK(prime,p);
  }
  return stoi(prime);
}

long
pith(long n)
{
  byteptr p = diffptr;
  ulong prime = 0, res = 0;

  if (n <= 0) err(talker, "pith meaningless if n = %ld",n);
  maxprime_check((ulong)n);
  while (prime<=(ulong)n) {
    NEXT_PRIME_VIADIFF(prime,p);
    res++;
  }
  return res-1;
}

GEN
primes(long n)
{
  byteptr p = diffptr;
  long prime = 0;
  GEN y,z;

  if (n < 0) n = 0;
  z = y = cgetg(n+1,t_VEC);
  while (n--)
  {
    NEXT_PRIME_VIADIFF_CHECK(prime,p);
    *++z = lstoi(prime);
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
initprimes1(ulong size, long *lenp, long *lastp)
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
  return (byteptr) gprealloc(p,r-p);
}

/*  Timing in ms (Athlon/850; reports 512M of secondary cache; looks
    like there is 64K of quickier cache too).

    The algorithm of allocation starts to work regularly from
    2pi(sqrt(lim)); we skip or double-quote what is less than this.

     arena| 10m   30m   100m   300m   1000m   2000m    4000m
     =================================================================
        1K  360
       1.5  250  1150
        2K  210   840
        3K  180   660   3160
        4K  160   580   2530  11930  "36680" "84730" "262850"
       12K  150   460   1730   5590   26010   65500  "184520"
       20K  150   430   1500   4900   25450   56420   143220
     ...
       64K  140   410   1400   4360   22150   32850   122820

    Timing relative to 64K:

     20K    1.071  1.049  1.071  1.124  1.149  1.718  1.166
     28K    1.071  1.000  1.043  1.067  1.115  1.256  1.326
     36K    1.000  1.024  1.029  1.034  0.946  1.075  1.087
     44K    1.000  1.049  1.007  1.016  1.006  1.056  0.974
     52K    1.000  0.976  1.007  1.009  1.023  1.035  0.910
     56K    0.929  1.024  1.000  1.002  1.023  1.022  0.893
     58K    1.143  0.976  1.000  1.002  0.995  1.016  0.888
     60K    1.000  1.024  1.000  0.998  1.016  1.010  0.865
     62K    1.000  1.000  1.000  0.995  1.023  1.004  0.922
     64K    1.000  1.000  1.000  1.000  1.000  1.000  1.000
     66K    1.071  1.049  1.014  0.993  1.025  0.995  0.938
     68K    1.071  1.098  1.086  1.050  0.939  0.991  0.926
     70K    1.214  1.171  1.164  1.124  1.061  1.023  0.860
     72K    1.214  1.244  1.221  1.181  1.070  1.081  0.852
     76K    1.357  1.415  1.371  1.305  1.154  1.260  0.841
     84K    1.643  1.610  1.614  1.546  1.340  1.426  0.954
     92K    1.857  1.878  1.850  1.773  1.475  1.640  1.063
     96K    2.000  2.073  2.057  2.016  1.380  1.710  1.127
    128K    2.214  2.341  2.371  2.328  1.624  2.118  1.429
    192K    2.500  2.707  2.743  2.729  1.901  2.495  1.626
    256K    2.786  2.902  2.979  2.977  2.077  2.680  1.791
    384K    3.143  3.293  3.371  3.392  2.344  3.050  1.906
    512K    3.286  3.488  3.521  3.537  2.445  3.441  2.130
    768K    3.857  4.171  4.264  4.319  2.977  4.045  2.490
   1024K    4.429  4.707  4.879  4.947  3.435  4.900  2.941
   1536K    5.071  5.659  6.029  6.197  4.393  6.237  3.662
   2048K    5.357  6.195  6.593  6.995  4.857  6.886  4.039
   3072K    5.786  6.488  7.029  7.356  5.264  7.425  4.402

    Values after 92K are from different run...  Matters much for 4000m
    one, when swapping starts; also 1000m run looks not very much
    reproducible...

    The stats for small arena lead to the value of ARENA_IN_ROOTS for i386.

    Similar data for Sparc leads to 10.

    TODO: need to create macro for (small) OVERHEAD_100_IN_ROOTS where the
    overhead of subdivision is 100%; likewise one needs to estimate
    the overhead of having the arena larger than the cache size.  Then
    one can intelligently optimize the arena size taking both effects
    into the account...
*/

#ifndef ARENA_IN_ROOTS
#  ifdef i386           /* gcc defines this? */
#    define ARENA_IN_ROOTS      1.5
#  else
#    define ARENA_IN_ROOTS      10
#  endif
#endif
#ifndef PRIME_ARENA
#  ifdef i386           /* gcc defines this? */
   /* Due to smaller ARENA_IN_ROOTS, smaller arena is OK; fit L1 cache */
#    define PRIME_ARENA (63 * 1024) /* No slowdown even with 64K L1 cache */
#  else
#    define PRIME_ARENA (200 * 1024) /* No slowdown even with 256K L2 cache */
#  endif
#endif

static long prime_arena = PRIME_ARENA;
static double arena_in_roots = ARENA_IN_ROOTS;

long
good_arena_size(long rootnum, ulong remains, ulong primes)
{
  /* ARENA_IN_ROOTS below 12: some slowdown starts to be noticable
   * when things fit into the cache.
   * XXX The choice of 10 gives a slowdown of 1-2% on UltraSparcII,
   * but makes calculations even for (the current) maximum of 436273009
   * fit into 256K cache (still common for some architectures).
   *
   * One may change it when small caches become uncommon, but the gain
   * is not going to be very noticable... */

  long asize = arena_in_roots * rootnum; /* Make % overhead negligeable. */
  if (asize < prime_arena) asize = prime_arena - 1;
  if (asize > remains) asize = remains; /* + room for a sentinel byte */
  if (2 * primes < asize)               /* XXXX Better substitutes for 2? */
    asize -= primes;                    /* We access arena AND primes */
  return asize;
}

/* Use as in
    install(set_internal,lLDG)          \\ Through some M too?
    set_internal(2,100) \\ disable dependence on limit

    { time_primes_arena(ar,limit) =
        set_internal(1,floor(ar*1024));
        default(primelimit, 200 000);   \\ 100000 results in *larger* malloc()!
        gettime;
        default(primelimit, limit);
        if(ar >= 1, ar=floor(ar));
        print("arena "ar"K => "gettime"ms");
    }
*/
long
set_internal(long what, GEN g)
{
  long ret = 0;

  if (what == 1)
    ret = prime_arena;
  else if (what == 2)
    ret = arena_in_roots * 1000;
  else
    err(talker, "panic: set_internal");
  if (g != NULL) {
    long val = itos(g);

    if (what == 1)
      prime_arena = val;
    else if (what == 2)
      arena_in_roots = val / 1000.;
  }
  return ret;
}

/* Here's the workhorse.  This is recursive, although normally the first
   recursive call will bottom out and invoke initprimes1() at once.
   (Not static;  might conceivably be useful to someone in library mode) */
byteptr
initprimes0(ulong maxnum, long *lenp, ulong *lastp)
{
  long k, size, alloced, asize, psize, rootnum;
  byteptr q,r,s,fin, p, p1, fin1, plast, curdiff;
  ulong last, remains, curlow;

  if (maxnum <= 1ul<<17)        /* Arbitrary. */
    return initprimes1(maxnum>>1, lenp, (long*)lastp);

  maxnum |= 1;                  /* make it odd. */

  /* Checked to be enough up to 40e6, attained at 155893 */
  size = (long) (1.09 * maxnum/log((double)maxnum)) + 145;
  p1 = (byteptr) gpmalloc(size);
  rootnum = (long) sqrt((double)maxnum); /* cast it back to a long */
  rootnum |= 1;
  {
    byteptr p2 = initprimes0(rootnum, &psize, &last); /* recursive call */
    memcpy(p1, p2, psize); free(p2);
  }
  fin1 = p1 + psize - 1;
  remains = (maxnum - rootnum) >> 1; /* number of odd numbers to check */

  asize = good_arena_size(rootnum, remains, psize);
  /* enough room on the stack ? */
  alloced = (((byteptr)avma) - ((byteptr)bot) <= (size_t)asize);
  if (alloced)
    p = (byteptr) gpmalloc(asize + 1);
  else
    p = (byteptr) bot;
  fin = p + asize;              /* the 0 sentinel goes at fin. */
  curlow = rootnum + 2; /* First candidate: know primes up to rootnum (odd). */
  curdiff = fin1;

  /* During each iteration p..fin-1 represents a range of odd
     numbers.  plast is a pointer which represents the last prime seen,
     it may point before p..fin-1. */
  plast = p - ((rootnum - last) >> 1) - 1;
  while (remains)
  {
    if (asize > remains)
    {
      asize = remains;
      fin = p + asize;
    }
    memset(p, 0, asize + 1);
    /* p corresponds to curlow.  q runs over primediffs.  */
    /* Don't care about DIFFPTR_SKIP: false positives provide no problem */
    for (q = p1+2, k = 3; q <= fin1; k += *q++)
    {/* first odd number which is >= curlow > p and divisible by p
      = last odd number which is <= curlow + 2p - 1 and 0 (mod p)
      = p + the last even number which is <= curlow + p - 1 and 0 (mod p)
      = p + the last even number which is <= curlow + p - 2 and 0 (mod p)
      = p + curlow + p - 2 - (curlow + p - 2) % 2p. */
      long k2 = k*k - curlow;
  
#if 0                                   /* XXXX Check which one is quickier! */
      if (k2 > 0) {                     /* May be due to ulong==>long wrap */
        k2 >>= 1;
        if (k2 >= asize) {
          if (k2 > remains) {
            /* Can happen due to a conversion wrap only, so . */
            goto small_k;
          } else
            break;                      /* All primes up to sqrt(top) checked */
        }
        r = p + k2;
      } else {
       small_k:
        r = p - (((curlow+k-2) % (2*k)) >> 1) + k - 1;
      }
#else
      if (k2 > 0) {
        r = p + (k2 >>= 1);
        if (k2 <= remains) goto finish; /* Guard against an address wrap. */
      }
      r = p - (((curlow+k-2) % (2*k)) >> 1) + k - 1;
    finish:
#endif
      for (s = r; s < fin; s += k) *s = 1;
    }
    /* now q runs over addresses corresponding to primes */
    for (q = p; ; plast = q++)
    {
      long d;

      while (*q) q++;           /* use 0-sentinel at end */
      if (q >= fin) break;
      d = (q - plast) << 1;
      while (d >= DIFFPTR_SKIP)
        *curdiff++ = DIFFPTR_SKIP, d -= DIFFPTR_SKIP;
      *curdiff++ = d;
    }
    plast -= asize;
    remains -= asize;
    curlow += (asize<<1);
  } /* while (remains) */
  last = curlow - ((p - plast) << 1);
  *curdiff++ = 0;               /* sentinel */
  *lenp = curdiff - p1;
  *lastp = last;
  if (alloced) free(p);
  return (byteptr) gprealloc(p1, *lenp);
}
#if 0 /* not yet... GN */
/* The diffptr table will contain at least 6548 entries (up to and including
   the 6547th prime, 65557, and the terminal null byte), because the isprime/
   small-factor-extraction machinery wants to depend on everything up to 65539
   being in the table, and we might as well go to a multiple of 4 Bytes.--GN */

void
init_tinyprimes_tridiv(byteptr p);      /* in ifactor2.c */
#endif

static ulong _maxprime = 0;

ulong
maxprime(void) { return _maxprime; }

void
maxprime_check(ulong c)
{
  if (_maxprime < c) err(primer2, c);
}

byteptr
initprimes(ulong maxnum)
{
  long len;
  ulong last;
  byteptr p;
  /* The algorithm must see the next prime beyond maxnum, whence the +512. */
  ulong maxnum1 = ((maxnum<65302?65302:maxnum)+512ul);

  if ((maxnum>>1) > VERYBIGINT - 1024)
      err(talker, "Too large primelimit");
  p = initprimes0(maxnum1, &len, &last);
#if 0 /* not yet... GN */
  static int build_the_tables = 1;
  if (build_the_tables) { init_tinyprimes_tridiv(p); build_the_tables=0; }
#endif
  _maxprime = last; return p;
}

static void
cleanprimetab(void)
{
  long i,j, lp = lg(primetab);

  for (i=j=1; i < lp; i++)
    if (primetab[i]) primetab[j++] = primetab[i];
  setlg(primetab,j);
}

/* p is a single element or a row vector with "primes" to add to primetab.
 * If p shares a non-trivial factor with another element in primetab, take it
 * into account. */
GEN
addprimes(GEN p)
{
  pari_sp av;
  long i,k,tx,lp;
  GEN L;

  if (!p) return primetab;
  tx = typ(p);
  if (is_vec_t(tx))
  {
    for (i=1; i < lg(p); i++) (void)addprimes((GEN) p[i]);
    return primetab;
  }
  if (tx != t_INT) err(typeer,"addprime");
  if (is_pm1(p)) return primetab;
  av = avma; i = signe(p);
  if (i == 0) err(talker,"can't accept 0 in addprimes");
  if (i < 0) p = absi(p); 

  lp = lg(primetab);
  L = cgetg(2*lp,t_VEC); k = 1;
  for (i=1; i < lp; i++)
  {
    GEN n = (GEN)primetab[i], d = mppgcd(n, p);
    if (! is_pm1(d))
    {
      if (!egalii(p,d)) L[k++] = (long)d;
      L[k++] = ldivii(n,d);
      gunclone(n); primetab[i] = 0;
    }
  }
  primetab = (GEN) gprealloc(primetab, (lp+1)*sizeof(long));
  primetab[i] = lclone(p); setlg(primetab, lp+1);
  if (k > 1) { cleanprimetab(); setlg(L,k); (void)addprimes(L); }
  avma = av; return primetab;
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
      for (i=1; i < lg(prime); i++) (void)removeprime((GEN) prime[i]);
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
#if 0
#define pseudoprime(p) millerrabin(p,3*lgefint(p))
#else /* remove further overkill :-)  --KB */
#define pseudoprime(p) BSW_psp(p)
#endif

/* where to stop trial dividing in factorization */

static long
tridiv_bound(GEN n, long all)
{
  long size = expi(n) + 1;
  if (all > 1)                  /* bounded factoring */
    return all;                 /* use the given limit */
  if (all == 0)
    return VERYBIGINT;          /* smallfact() case */
  if (size <= 32)
    return 16384;
  else if (size <= 512)
    return (size-16) << 10;
  return 1L<<19;                /* Rho will generally be faster above this */
}

/* function imported from ifactor1.c */
extern long ifac_decomp(GEN n, long hint);
extern long ifac_decomp_break(GEN n, long (*ifac_break)(GEN,GEN,GEN,GEN),
                  GEN state, long hint);
static GEN
aux_end(GEN n, long nb)
{
  GEN p1,p2, z = (GEN)avma;
  long i;

  if (n) gunclone(n);
  p1=cgetg(nb+1,t_COL);
  p2=cgetg(nb+1,t_COL);
  for (i=nb; i; i--)
  {
    p2[i] = (long)z; z += lg(z);
    p1[i] = (long)z; z += lg(z);
  }
  z[1] = (long)p1;
  z[2] = (long)p2;
  if (nb) (void)sort_factor_gen(z,cmpii);
  return z;
}

GEN 
auxdecomp1(GEN n, long (*ifac_break)(GEN n, GEN pairs, GEN here, GEN state),
                  GEN state, long all, long hint)
{
  pari_sp av;
  long pp[] = { evaltyp(t_INT)|_evallg(4), 0,0,0 };
  long nb = 0,i,k,lp,p,lim1;
  byteptr d=diffptr+1;

  if (typ(n) != t_INT) err(arither1);
  i=signe(n); if (!i) err(arither2);
  (void)cgetg(3,t_MAT);
  if (i<0) { (void)stoi(-1); (void)stoi(1); nb++; }
  if (is_pm1(n)) return aux_end(NULL,nb);

  n = gclone(n);  setsigne(n,1);
  i = vali(n);
  if (i)
  {
    (void)stoi(2); (void)stoi(i); nb++;
    av=avma; affii(shifti(n,-i), n); avma=av;
  }
  if (is_pm1(n)) return aux_end(n,nb);
  lim1 = tridiv_bound(n, all);

  /* trial division */
  p = 2;
  while (*d && p <= lim1)
  {
    NEXT_PRIME_VIADIFF(p,d);
    if (mpdivisis(n,p,n))
    {
      nb++; k=1; while (mpdivisis(n,p,n)) k++;
      (void)utoi(p); (void)stoi(k);
      if (is_pm1(n)) return aux_end(n,nb);
    }
  }

  /* pp = square of biggest p tried so far */
  av=avma; affii(muluu(p,p),pp); avma=av;
  if (cmpii(pp,n) > 0)
  {
    nb++;
    (void)icopy(n); (void)stoi(1); return aux_end(n,nb);
  }

  /* trial divide by the "special primes" (usually huge composites...) */
  lp = lg(primetab); k=0;
  for (i=1; i<lp; i++)
    if (mpdivis(n,(GEN) primetab[i],n))
    {
      nb++; k=1; while (mpdivis(n,(GEN) primetab[i],n)) k++;
      (void)icopy((GEN) primetab[i]); (void)stoi(k);
      if (is_pm1(n)) return aux_end(n,nb);
    }

  /* test primality (unless all != 1 (i.e smallfact))*/
  if ((k && cmpii(pp,n) > 0) || (all==1 && pseudoprime(n)))
  {
    nb++;
    (void)icopy(n); (void)stoi(1); return aux_end(n,nb);
  }

  /* now we have a large composite.  Use hint as is if all==1 */
  if (all!=1) hint = 15; /* turn off everything except pure powers */
  if (ifac_break && (*ifac_break)(n,NULL,NULL,state))
    /*Initialize ifac_break*/
  {
    if (DEBUGLEVEL >= 3)
      fprintferr("IFAC: (Partial fact.) Initial stop requested.\n");
  }
  else
    nb += ifac_decomp_break(n, ifac_break, state, hint);

  return aux_end(n, nb);
}

/* state[1]: current unfactored part.
 * state[2]: limit. */
static long
ifac_break_limit(GEN n, GEN pairs/*unused*/, GEN here, GEN state)
{
  pari_sp ltop = avma;
  int res;
  if (!here) /* initial call */
   /* Small prime have been removed since start, n is the new unfactored part.
    * Result is affect()ed to state[1] to preserve stack. */
    affii(n, (GEN)state[1]);
  else
  {
    GEN q = powgi((GEN)here[0],(GEN)here[1]); /* primary factor found.*/
    if (DEBUGLEVEL>2) fprintferr("IFAC: Stop: Primary factor: %Z\n",q);
    /* divide unfactored part by q and assign the result to state[1] */
    diviiz((GEN)state[1],q, (GEN)state[1]);
  }
  if (DEBUGLEVEL>=3) fprintferr("IFAC: Stop: remaining %Z\n",state[1]);
  /* check the stopping criterion, then restore stack */ 
  res = cmpii((GEN)state[1],(GEN)state[2]) <= 0;
  avma = ltop; return res;
}

static GEN
auxdecomp0(GEN n, long all, long hint)
{
  return auxdecomp1(n, NULL, gzero, all, hint);
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

/* Factor until the unfactored part is smaller than limit. */
GEN
decomp_limit(GEN n, GEN limit)
{
  GEN state = cgetg(3,t_VEC);
 /* icopy is mainly done to allocate memory for affect().
  * Currently state[1] value is discarded in initial call to ifac_break_limit */
  state[1] = licopy(n);
  state[2] = lcopy(limit);
  return auxdecomp1(n, &ifac_break_limit, state, 1, decomp_default_hint);
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
  pari_sp av = avma,tetpil;

  if (lim<=1) lim=0;
  switch(typ(n))
  {
    case t_INT:
      return auxdecomp(n,lim);
    case t_FRACN:
      n=gred(n);
      if (typ(n) == t_INT)
        return gerepileupto(av, boundfact(n,lim));
      /* fall through */
    case t_FRAC:
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
/**                    SIMPLE FACTORISATIONS                          **/
/**                                                                   **/
/***********************************************************************/

/*Factorize n and output [fp,fe] where
 * fp and fe are vecsmall and n=prod{fp[i]^fe[i]}
 */

GEN
decomp_small(long n)
{
  pari_sp ltop=avma;
  GEN F = factor(stoi(n));
  long i, l=lg(F[1]);
  GEN f=cgetg(3,t_VEC);
  GEN fp=cgetg(l,t_VECSMALL);
  GEN fe=cgetg(l,t_VECSMALL);
  f[1] = (long) fp;
  f[2] = (long) fe;
  for(i = 1; i < l; i++)
  {
    fp[i]=itos(gcoeff(F,i,1));
    fe[i]=itos(gcoeff(F,i,2));
  }
  return gerepileupto(ltop,f);
}

/*Return the primary factors of a small integer as a vecsmall*/
GEN
decomp_primary_small(long n)
{
  pari_sp ltop=avma;
  GEN F = factor(stoi(n));
  GEN fc = cgetg(lg(F[1]), t_VECSMALL);
  pari_sp av=avma;
  long i;
  for (i = 1; i < lg(fc); i++)
    fc[i] = itos(powgi(gmael(F,1,i), gmael(F,2,i)));
  avma=av;
  return gerepileupto(ltop,fc);
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
  byteptr d = diffptr+1;        /* point at 3 - 2 */
  pari_sp av = avma;
  ulong p;
  long s, v, lim1;

  if (typ(n) != t_INT) err(arither1);
  if (!signe(n)) err(arither2);
  if (is_pm1(n)) return 1;
  v = vali(n);
  if (v>1) return 0;
  s = v ? -1 : 1;
  n=absi(shifti(n,-v)); p = 2;
  if (is_pm1(n)) return s;
  lim1 = tridiv_bound(n,1);

  while (*d && p < lim1)
  {
    NEXT_PRIME_VIADIFF(p,d);
    if (mpdivisis(n,p,n))
    {
      if (smodis(n,p) == 0) { avma=av; return 0; }
      s = -s; if (is_pm1(n)) { avma=av; return s; }
    }
  }
  /* we normally get here with p==nextprime(PRE_TUNE), which will already
     have been tested against n, so p^2 >= n  (instead of p^2 > n)  is
     enough to guarantee n is prime */
  if (cmpii(sqru(p),n) >= 0 || pseudoprime(n)) { avma=av; return -s; }
  /* large composite without small factors */
  v = ifac_moebius(n, decomp_default_hint);
  avma=av;
  return (s<0 ? -v : v);        /* correct also if v==0 */
}

GEN
gissquarefree(GEN x)
{
  return arith_proto(issquarefree,x,0);
}

long
issquarefree(GEN x)
{
  ulong p;
  pari_sp av = avma;
  long tx, lim1;
  GEN d;

  if (gcmp0(x)) return 0;
  tx = typ(x);
  if (tx == t_INT)
  {
    long v;
    byteptr d=diffptr+1;
    if (is_pm1(x)) return 1;
    if((v = vali(x)) > 1) return 0;
    x = absi(shifti(x,-v));
    if (is_pm1(x)) return 1;
    lim1 = tridiv_bound(x,1);

    p = 2;
    while (*d && p < lim1)
    {
      NEXT_PRIME_VIADIFF(p,d);
      if (mpdivisis(x,p,x))
      {
        if (smodis(x,p) == 0) { avma = av; return 0; }
        if (is_pm1(x)) { avma = av; return 1; }
      }
    }
    if (cmpii(sqru(p),x) >= 0 || pseudoprime(x)) { avma = av; return 1; }
    v = ifac_issquarefree(x, decomp_default_hint);
    avma = av; return v;
  }
  if (tx != t_POL) err(typeer,"issquarefree");
  d = ggcd(x, derivpol(x));
  avma = av; return (lgef(d) == 3);
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
  pari_sp av = avma;
  long p,nb,v, lim1;

  if (typ(n) != t_INT) err(arither1);
  if (!signe(n)) err(arither2);
  if (is_pm1(n)) return 0;
  v=vali(n);
  nb = v ? 1 : 0;
  n = absi(shifti(n,-v)); p = 2;
  if (is_pm1(n)) return nb;
  lim1 = tridiv_bound(n,1);

  while (*d && p < lim1)
  {
    NEXT_PRIME_VIADIFF(p,d);
    if (mpdivisis(n,p,n))
    {
      nb++; while (mpdivisis(n,p,n)); /* empty */
      if (is_pm1(n)) { avma = av; return nb; }
    }
  }
  if (cmpii(sqru(p),n) >= 0 || pseudoprime(n)) { avma = av; return nb+1; }
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
  ulong p;
  pari_sp av = avma;
  long nb,v, lim1;

  if (typ(n) != t_INT) err(arither1);
  if (!signe(n)) err(arither2);
  if (is_pm1(n)) return 0;
  nb=v=vali(n);
  n=absi(shifti(n,-v)); p = 2;
  if (is_pm1(n)) { avma = av; return nb; }
  lim1 = tridiv_bound(n,1);

  while (*d && p < lim1)
  {
    NEXT_PRIME_VIADIFF(p,d);
    if (mpdivisis(n,p,n))
    {
      do nb++; while (mpdivisis(n,p,n));
      if (is_pm1(n)) { avma = av; return nb; }
    }
  }
  if (cmpii(sqru(p),n) >= 0 || pseudoprime(n)) { avma = av; return nb+1; }
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
  GEN m;
  ulong p;
  pari_sp av = avma;
  long v, lim1;

  if (typ(n) != t_INT) err(arither1);
  if (!signe(n)) err(arither2);
  if (is_pm1(n)) return gun;
  v = vali(n);
  n = absi(shifti(n,-v)); p = 2;
  m = (v > 1 ? shifti(gun,v-1) : stoi(1));
  if (is_pm1(n)) { return gerepileupto(av,m); }
  lim1 = tridiv_bound(n,1);

  while (*d && p < lim1)
  {
    NEXT_PRIME_VIADIFF(p,d);
    if (mpdivisis(n,p,n))
    {
      m = mulis(m, p-1);
      while (mpdivisis(n,p,n)) m = mulis(m,p);
      if (is_pm1(n)) { return gerepileupto(av,m); }
    }
  }
  if (cmpii(sqru(p),n) >= 0 || pseudoprime(n))
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
  GEN m;
  long l, v, lim1;
  ulong p;
  pari_sp av = avma;

  if (typ(n) != t_INT) err(arither1);
  if (!signe(n)) err(arither2);
  if (is_pm1(n)) return gun;
  v = vali(n);
  n = absi(shifti(n,-v)); p = 2;
  m = stoi(v+1);
  if (is_pm1(n)) return gerepileupto(av,m);
  lim1 = tridiv_bound(n,1);

  while (*d && p < lim1)
  {
    NEXT_PRIME_VIADIFF(p,d);
    l=1; while (mpdivisis(n,p,n)) l++;
    m = mulsi(l,m); if (is_pm1(n)) { return gerepileupto(av,m); }
  }
  if(cmpii(sqru(p),n) >= 0 || pseudoprime(n))
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
  GEN m,m1;
  ulong p;
  pari_sp av=avma;
  long v, lim1;

  if (typ(n) != t_INT) err(arither1);
  if (!signe(n)) err(arither2);
  if (is_pm1(n)) return gun;
  v = vali(n);
  n = absi(shifti(n,-v)); p = 2;
  m = (v ? addsi(-1,shifti(gun,v+1)) : stoi(1));
  if (is_pm1(n)) { return gerepileupto(av,m); }
  lim1 = tridiv_bound(n,1);

  while (*d && p < lim1)
  {
    NEXT_PRIME_VIADIFF(p,d);
    if (mpdivisis(n,p,n))
    {
      m1 = utoi(p+1);
      while (mpdivisis(n,p,n)) m1 = addsi(1, mului(p,m1));
      m = mulii(m1,m); if (is_pm1(n)) { return gerepileupto(av,m); }
    }
  }
  if(cmpii(sqru(p),n) >= 0 || pseudoprime(n))
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
  GEN n1,m,m1,pk;
  ulong p;
  pari_sp av = avma;
  long k1,v, lim1;

  if (!k) return numbdiv(n);
  if (k==1) return sumdiv(n);
  if (typ(n) != t_INT) err(arither1);
  if (!signe(n)) err(arither2);
  if (is_pm1(n)) return gun;
  k1 = k; n1 = n;
  if (k==-1) { m=sumdiv(n); k = 1; goto fin; }
  if (k<0)  k = -k;
  v=vali(n);
  n=absi(shifti(n,-v));
  p = 2; m = stoi(1);
  while (v--)  m = addsi(1,shifti(m,k));
  if (is_pm1(n)) goto fin;
  lim1 = tridiv_bound(n,1);

  while (*d && p < lim1)
  {
    NEXT_PRIME_VIADIFF(p,d);
    if (mpdivisis(n,p,n))
    {
      pk = gpowgs(utoi(p),k); m1 = addsi(1,pk);
      while (mpdivisis(n,p,n)) m1 = addsi(1, mulii(pk,m1));
      m = mulii(m1,m); if (is_pm1(n)) goto fin;
    }
  }
  if(cmpii(sqru(p),n) >= 0 || pseudoprime(n))
  {
    pk = gpuigs(n,k);
    m = mulii(m,addsi(1,pk));
    goto fin;
  }
  m = mulii(m, ifac_sumdivk(n, k, decomp_default_hint));
 fin:
  if (k1 < 0) m = gdiv(m, gpowgs(n1,k));
  return gerepileupto(av,m);
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
  pari_sp tetpil,av=avma;
  long i,j,l;
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

static GEN
do_core(GEN n, int all)
{
  pari_sp av = avma;
  long i;
  GEN fa,p1,p2,c = gun;

  fa = auxdecomp(n,all);
  p1 = (GEN)fa[1];
  p2 = (GEN)fa[2];
  for (i=1; i<lg(p1); i++)
    if (mod2((GEN)p2[i])) c = mulii(c,(GEN)p1[i]);
  return gerepileuptoint(av, c);
}

static GEN
do_core2(GEN n, int all)
{
  pari_sp av = avma;
  long i;
  GEN fa,p1,p2,e,c=gun,f=gun,y;

  fa = auxdecomp(n,all);
  p1 = (GEN)fa[1];
  p2 = (GEN)fa[2];
  for (i=1; i<lg(p1); i++)
  {
    e = (GEN)p2[i];
    if (mod2(e))   c = mulii(c, (GEN)p1[i]);
    if (!gcmp1(e)) f = mulii(f, powgi((GEN)p1[i], shifti(e,-1)));
  }
  y = cgetg(3,t_VEC);
  y[1] = (long)c;
  y[2] = (long)f; return gerepilecopy(av, y);
}

GEN core(GEN n)        { return do_core(n,1); }
GEN corepartial(GEN n) { return do_core(n,0); }
GEN core2(GEN n)       { return do_core2(n,1); }
GEN core2partial(GEN n){ return do_core2(n,0); }

GEN
core0(GEN n,long flag) { return flag? core2(n): core(n); }

static long
_mod4(GEN c) { long r = mod4(c); if (signe(c) < 0) r = 4-r; return r; }

GEN
coredisc(GEN n)
{
  pari_sp av = avma;
  GEN c = core(n);
  long r = _mod4(c);
  if (r==1 || r==4) return c;
  return gerepileuptoint(av, shifti(c,2));
}

GEN
coredisc2(GEN n)
{
  pari_sp av = avma;
  GEN y = core2(n);
  GEN c = (GEN)y[1], f = (GEN)y[2];
  long r = _mod4(c);
  if (r==1 || r==4) return y;
  y = cgetg(3,t_VEC);
  y[1] = lshifti(c,2);
  y[2] = lmul2n(f,-1); return gerepileupto(av, y);
}

GEN
coredisc0(GEN n,long flag) { return flag? coredisc2(n): coredisc(n); }

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
    pari_sp av=avma; s = signe(qf_disc(x,y,z)); avma=av;
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
sq_gen(GEN z, GEN x)
{
  GEN d1,x2,y2,v1,v2,c3,m,p1,r;

  d1 = bezout((GEN)x[2],(GEN)x[1],&x2,&y2);
  if (gcmp1(d1)) v1 = v2 = (GEN)x[1];
  else
  {
    v1 = divii((GEN)x[1],d1);
    v2 = mulii(v1,mppgcd(d1,(GEN)x[3]));
  }
  m = mulii((GEN)x[3],x2); setsigne(m,-signe(m));
  r = modii(m,v2); p1 = mulii(v1,r);
  c3 = addii(mulii((GEN)x[3],d1), mulii(r,addii((GEN)x[2],p1)));
  z[1] = lmulii(v1,v2);
  z[2] = laddii((GEN)x[2], shifti(p1,1));
  z[3] = ldivii(c3,v2);
}

void
comp_gen(GEN z,GEN x,GEN y)
{
  GEN s,n,d,d1,x1,x2,y1,y2,v1,v2,c3,m,p1,r;

  if (x == y) { sq_gen(z,x); return; }
  s = shifti(addii((GEN)x[2],(GEN)y[2]),-1);
  n = subii((GEN)y[2],s);
  d = bezout((GEN)y[1],(GEN)x[1],&y1,&x1);
  d1 = bezout(s,d,&x2,&y2);
  if (gcmp1(d1))
  {
    v1 = (GEN)x[1];
    v2 = (GEN)y[1];
  }
  else
  {
    v1 = divii((GEN)x[1],d1);
    v2 = divii((GEN)y[1],d1);
    v1 = mulii(v1, mppgcd(d1,mppgcd((GEN)x[3],mppgcd((GEN)y[3],n))));
  }
  m = addii(mulii(mulii(y1,y2),n), mulii((GEN)y[3],x2));
  setsigne(m,-signe(m));
  r = modii(m,v1); p1 = mulii(v2,r); 
  c3 = addii(mulii((GEN)y[3],d1), mulii(r,addii((GEN)y[2],p1)));
  z[1] = lmulii(v1,v2);
  z[2] = laddii((GEN)y[2], shifti(p1,1));
  z[3] = ldivii(c3,v1);
}

static GEN
compimag0(GEN x, GEN y, int raw)
{
  pari_sp av = avma;
  long tx = typ(x);
  GEN z;

  if (typ(y) != tx || tx!=t_QFI) err(typeer,"composition");
  if (cmpii((GEN)x[1],(GEN)y[1]) > 0) { z=x; x=y; y=z; }
  z=cgetg(4,t_QFI); comp_gen(z,x,y);
  if (raw) return gerepilecopy(av,z);
  return gerepileupto(av, redimag(z));
}

static GEN
compreal0(GEN x, GEN y, int raw)
{
  pari_sp av = avma;
  long tx = typ(x);
  GEN z;

  if (typ(y) != tx || tx!=t_QFR) err(typeer,"composition");
  z=cgetg(5,t_QFR); comp_gen(z,x,y);
  z[4]=laddrr((GEN)x[4],(GEN)y[4]);
  if (raw) return gerepilecopy(av,z);
  return gerepileupto(av,redreal(z));
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

GEN
sqcompimag0(GEN x, long raw)
{
  pari_sp av = avma;
  GEN z = cgetg(4,t_QFI);

  if (typ(x)!=t_QFI) err(typeer,"composition");
  sq_gen(z,x);
  if (raw) return gerepilecopy(av,z);
  return gerepileupto(av,redimag(z));
}

static GEN
sqcompreal0(GEN x, long raw)
{
  pari_sp av = avma;
  GEN z = cgetg(5,t_QFR);

  if (typ(x)!=t_QFR) err(typeer,"composition");
  sq_gen(z,x); z[4]=lshiftr((GEN)x[4],1);
  if (raw) return gerepilecopy(av,z);
  return gerepileupto(av,redreal(z));
}

GEN
sqcompreal(GEN x) { return sqcompreal0(x,0); }

GEN
sqcomprealraw(GEN x) { return sqcompreal0(x,1); }

GEN
sqcompimag(GEN x) { return sqcompimag0(x,0); }

GEN
sqcompimagraw(GEN x) { return sqcompimag0(x,1); }

static GEN
real_unit_form_by_disc(GEN D, long prec)
{
  GEN y = cgetg(5,t_QFR), isqrtD;
  pari_sp av = avma;

  if (typ(D) != t_INT || signe(D) <= 0) err(typeer,"real_unit_form_by_disc");
  switch(mod4(D))
  {
    case 2:
    case 3: err(funder2,"real_unit_form_by_disc");
  }
  y[1]=un; isqrtD = racine(D);
  /* we know that D and isqrtD are non-zero */
  if (mod2(D) != mod2(isqrtD))
    isqrtD = gerepileuptoint(av, addsi(-1,isqrtD));
  y[2] = (long)isqrtD; av = avma;
  y[3] = lpileuptoint(av, shifti(subii(sqri(isqrtD),D),-2));
  y[4] = (long)realzero(prec); return y;
}

GEN
real_unit_form(GEN x)
{
  pari_sp av = avma;
  long prec;
  GEN D;
  if (typ(x) != t_QFR) err(typeer,"real_unit_form");
  prec = precision((GEN)x[4]);
  if (!prec) err(talker,"not a t_REAL in 4th component of a t_QFR");
  D = qf_disc(x,NULL,NULL);
  return gerepileupto(av, real_unit_form_by_disc(D,prec));
}

static GEN
imag_unit_form_by_disc(GEN D)
{
  GEN y = cgetg(4,t_QFI);
  long isodd;

  if (typ(D) != t_INT || signe(D) >= 0) err(typeer,"real_unit_form_by_disc");
  switch(4 - mod4(D))
  {
    case 2:
    case 3: err(funder2,"imag_unit_form_by_disc");
  }
  y[1] = un; isodd = mpodd(D);
  y[2] = isodd? un: zero;
  /* y[3] = (1-D) / 4 or -D / 4, whichever is an integer */
  y[3] = lshifti(D,-2); setsigne(y[3],1);
  if (isodd)
  {
    pari_sp av = avma;
    y[3] = lpileuptoint(av, addis((GEN)y[3],1));
  }
  return y;
}

GEN
imag_unit_form(GEN x)
{
  GEN p1,p2, y = cgetg(4,t_QFI);
  pari_sp av;
  if (typ(x) != t_QFI) err(typeer,"imag_unit_form");
  y[1] = un;
  y[2] = mpodd((GEN)x[2])? un: zero;
  av = avma; p1 = mulii((GEN)x[1],(GEN)x[3]);
  p2 = shifti(sqri((GEN)x[2]),-2);
  y[3] = lpileuptoint(av, subii(p1,p2));
  return y;
}

GEN
powrealraw(GEN x, long n)
{
  pari_sp av = avma;
  long m;
  GEN y;

  if (typ(x) != t_QFR)
    err(talker,"not a real quadratic form in powrealraw");
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
  pari_sp av = avma;
  long m;
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
  pari_sp av=avma,tetpil;
  long cz;
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
  pari_sp av=avma,tetpil;
  long cz;
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
  pari_sp av,tetpil;
  long i,j;
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

static void
fix_expo(GEN x)
{
  long e = expo(x[5]);
  if (e >= EXP220)
  {
    x[4] = laddsi(1,(GEN)x[4]);
    setexpo(x[5], e - EXP220);
  }
}

GEN
rhoreal_aux(GEN x, GEN D, GEN sqrtD, GEN isqrtD)
{
  GEN p1,p2, y = cgetg(6,t_VEC);
  GEN b = (GEN)x[2];
  GEN c = (GEN)x[3];

  y[1] = (long)c;
  p2 = (absi_cmp(isqrtD,c) >= 0)? isqrtD: absi(c);
  p1 = shifti(c,1);
  if (p1 == gzero) err(talker, "reducible form in rhoreal");
  setsigne(p1,1); /* |2c| */
  p2 = divii(addii(p2,b), p1);
  y[2] = lsubii(mulii(p2,p1), b);

  p1 = shifti(subii(sqri((GEN)y[2]),D),-2);
  y[3] = ldivii(p1,(GEN)y[1]);

  if (lg(x) <= 5) setlg(y,4);
  else
  {
    y[4] = x[4];
    y[5] = x[5];
    if (signe(b))
    {
      p1 = divrr(addir(b,sqrtD), subir(b,sqrtD));
      y[5] = lmulrr(p1, (GEN)y[5]);
      fix_expo(y);
    }
  }
  return y;
}

#define qf_NOD  2
#define qf_STEP 1

GEN
codeform5(GEN x, long prec)
{
  GEN y = cgetg(6,t_VEC);
  y[1] = x[1];
  y[2] = x[2];
  y[3] = x[3];
  y[4] = zero;
  y[5] = (long)realun(prec); return y;
}

static GEN
add_distance(GEN x, GEN d0)
{
  GEN y = cgetg(5, t_QFR);
  y[1] = licopy((GEN)x[1]);
  y[2] = licopy((GEN)x[2]);
  y[3] = licopy((GEN)x[3]);
  y[4] = lcopy(d0); return y;
}

/* d0 = initial distance, assume |n| > 1 */
static GEN
decodeform(GEN x, GEN d0)
{
  GEN p1,p2;
  
  if (lg(x) < 6) return add_distance(x,d0);
  /* x = (a,b,c, expo(d), d), d = exp(2*distance) */
  p1 = absr((GEN)x[5]);
  p2 = (GEN)x[4];
  if (signe(p2))
  {
    long e = expo(p1);
    p1 = shiftr(p1,-e);
    p2 = addis(mulsi(EXP220,p2), e);
    p1 = mplog(p1);
    p1 = mpadd(p1, mulir(p2, mplog2(lg(d0))));
  }
  else
  { /* to avoid loss of precision */
    p1 = gcmp1(p1)? NULL: mplog(p1);
  }
  if (p1)
    d0 = addrr(d0, shiftr(p1,-1));
  return add_distance(x, d0);
}

static long
get_prec(GEN d)
{
  long k = lg(d);
  long l = ((BITS_IN_LONG-1-expo(d))>>TWOPOTBITS_IN_LONG)+2;
  if (l < k) l = k;
  if (l < 3) l = 3;
  return l;
}

static int
real_isreduced(GEN x, GEN isqrtD)
{
  GEN a = (GEN)x[1];
  GEN b = (GEN)x[2];
  if (signe(b) > 0 && cmpii(b,isqrtD) <= 0 )
  {
    GEN p1 = subii(isqrtD, shifti(absi(a),1));
    long l = absi_cmp(b, p1);
    if (l > 0 || (l == 0 && signe(p1) < 0)) return 1;
  }
  return 0;
}

GEN
redrealform5(GEN x, GEN D, GEN sqrtD, GEN isqrtD)
{
  while (!real_isreduced(x,isqrtD))
    x = rhoreal_aux(x,D,sqrtD,isqrtD);
  return x;
}

static GEN
redreal0(GEN x, long flag, GEN D, GEN isqrtD, GEN sqrtD)
{
  pari_sp av = avma;
  long prec;
  GEN d0;

  if (typ(x) != t_QFR) err(talker,"not a real quadratic form in redreal");

  if (!D)
    D = qf_disc(x,NULL,NULL);
  else
    if (typ(D) != t_INT) err(arither1);

  d0 = (GEN)x[4]; prec = get_prec(d0);
  x = codeform5(x,prec);
  if ((flag & qf_NOD)) setlg(x,4);
  else
  {
    if (!sqrtD)
      sqrtD = gsqrt(D,prec);
    else
    {
      long l = typ(sqrtD);
      if (!is_intreal_t(l)) err(arither1);
    }
  }
  if (!isqrtD)
    isqrtD = sqrtD? mptrunc(sqrtD): racine(D);
  else
    if (typ(isqrtD) != t_INT) err(arither1);

  if (flag & qf_STEP)
    x = rhoreal_aux(x,D,sqrtD,isqrtD);
  else
    x = redrealform5(x,D,sqrtD,isqrtD);
  return gerepileupto(av, decodeform(x,d0));
}

GEN
comprealform5(GEN x, GEN y, GEN D, GEN sqrtD, GEN isqrtD)
{
  pari_sp av = avma;
  GEN z = cgetg(6,t_VEC); comp_gen(z,x,y);
  if (x == y)
  {
    z[4] = lshifti((GEN)x[4],1);
    z[5] = lsqr((GEN)x[5]);
  }
  else
  {
    z[4] = laddii((GEN)x[4],(GEN)y[4]);
    z[5] = lmulrr((GEN)x[5],(GEN)y[5]);
  }
  fix_expo(z); z = redrealform5(z,D,sqrtD,isqrtD);
  return gerepilecopy(av,z);
}

/* assume n!=0 */
GEN
powrealform(GEN x, GEN n)
{
  pari_sp av = avma;
  long i,m;
  GEN y,D,sqrtD,isqrtD,d0;

  if (typ(x) != t_QFR)
    err(talker,"not a real quadratic form in powreal");
  if (gcmp1(n)) return gcopy(x);
  if (gcmp_1(n)) return ginv(x);

  d0 = (GEN)x[4];
  D = qf_disc(x,NULL,NULL);
  sqrtD = gsqrt(D, get_prec(d0));
  isqrtD = mptrunc(sqrtD);
  if (signe(n) < 0) { x = ginv(x); d0 = (GEN)x[4]; }
  n = absi(n);
  x = codeform5(x, lg(d0)); y = NULL;
  for (i=lgefint(n)-1; i>1; i--)
  {
    m = n[i];
    for (; m; m>>=1)
    {
      if (m&1) y = y? comprealform5(y,x,D,sqrtD,isqrtD): x;
      if (m == 1 && i == 2) break;
      x = comprealform5(x,x,D,sqrtD,isqrtD); 
    }
  }
  d0 = mulri(d0,n);
  return gerepileupto(av, decodeform(y,d0));
}

GEN
redimag(GEN x)
{
  pari_sp av=avma;
  long fl;
  do x = rhoimag0(x, &fl); while (fl == 0);
  x = gerepilecopy(av,x);
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
  return redreal0(x,qf_STEP,NULL,NULL,NULL);
}

GEN
redrealnod(GEN x, GEN isqrtD)
{
  return redreal0(x,qf_NOD,NULL,isqrtD,NULL);
}

GEN
rhorealnod(GEN x, GEN isqrtD)
{
  return redreal0(x,qf_STEP|qf_NOD,NULL,isqrtD,NULL);
}

GEN
qfbred0(GEN x, long flag, GEN D, GEN isqrtD, GEN sqrtD)
{
  long tx=typ(x),fl;
  pari_sp av;

  if (!is_qf_t(tx)) err(talker,"not a quadratic form in qfbred");
  if (!D) D = qf_disc(x,NULL,NULL);
  switch(signe(D))
  {
    case 1 :
      return redreal0(x,flag,D,isqrtD,sqrtD);

    case -1:
      if (!flag) return  redimag(x);
      if (flag !=1) err(flagerr,"qfbred");
      av=avma; x = rhoimag0(x,&fl);
      x = gerepilecopy(av,x);
      if (fl == 2) setsigne(x[2], -signe(x[2]));
      return x;
  }
  err(redpoler,"qfbred");
  return NULL; /* not reached */
}

/* special case: p = 1 return unit form */
GEN
primeform(GEN x, GEN p, long prec)
{
  pari_sp av;
  long s, sx = signe(x);
  GEN y, b, c;

  if (typ(x) != t_INT || !sx) err(arither1);
  if (typ(p) != t_INT || signe(p) <= 0) err(arither1);
  if (is_pm1(p))
    return sx<0? imag_unit_form_by_disc(x)
               : real_unit_form_by_disc(x,prec);
  s = mod8(x);
  if (sx < 0)
  {
    if (s) s = 8-s;
    y = cgetg(4, t_QFI);
  }
  else
  {
    y = cgetg(5, t_QFR);
    y[4] = (long)realzero(prec);
  }
  switch(s&3)
  {
    case 2: case 3: err(funder2,"primeform");
  }
  av = avma;
  if (egalii(p, gdeux))
  {
    switch(s)
    {
      case 0: b = gzero; break;
      case 1: b = gun;   break;
      case 4: b = gdeux; break;
      default: err(sqrter5); b = NULL; /* -Wall */
    }
    c = shifti(subsi(s,x), -3);
  }
  else
  {
    b = mpsqrtmod(x,p); if (!b) err(sqrter5);
    s &= 1; /* s = x mod 2 */
    /* mod(b) != mod2(x) ? [Warning: we may have b == 0] */
    if ((!signe(b) && s) || mod2(b) != s) b = gerepileuptoint(av, subii(p,b));

    av = avma;
    c = diviiexact(shifti(subii(sqri(b), x), -2), p);
  }
  y[3] = lpileuptoint(av, c);
  y[2] = (long)b;
  y[1] = licopy(p); return y;
}

/*********************************************************************/
/**                                                                 **/
/**                       BINARY DECOMPOSITION                      **/
/**                                                                 **/
/*********************************************************************/

GEN
binaire(GEN x)
{
  ulong m,u;
  long i,lx,ex,ly,tx=typ(x);
  GEN y,p1,p2;

  switch(tx)
  {
    case t_INT:
      lx=lgefint(x);
      if (lx==2) { y=cgetg(2,t_VEC); y[1]=zero; return y; }
      ly = BITS_IN_LONG+1; m=HIGHBIT; u=x[2];
      while (!(m & u)) { m>>=1; ly--; }
      y = cgetg(ly+((lx-3)<<TWOPOTBITS_IN_LONG),t_VEC); ly=1;
      do { y[ly] = m & u ? un : zero; ly++; } while (m>>=1);
      for (i=3; i<lx; i++)
      {
        m=HIGHBIT; u=x[i];
        do { y[ly] = m & u ? un : zero; ly++; } while (m>>=1);
      }
      break;

    case t_REAL:
      ex=expo(x);
      if (!signe(x))
      {
        lx=1+max(-ex,0); y=cgetg(lx,t_VEC);
        for (i=1; i<lx; i++) y[i]=zero;
        return y;
      }

      lx=lg(x); y=cgetg(3,t_VEC);
      if (ex > bit_accuracy(lx)) err(precer,"binary");
      p1 = cgetg(max(ex,0)+2,t_VEC);
      p2 = cgetg(bit_accuracy(lx)-ex,t_VEC);
      y[1] = (long) p1; y[2] = (long) p2;
      ly = -ex; ex++; m = HIGHBIT;
      if (ex<=0)
      {
        p1[1]=zero; for (i=1; i <= -ex; i++) p2[i]=zero;
        i=2;
      }
      else
      {
        ly=1;
        for (i=2; i<lx && ly<=ex; i++)
        {
          m=HIGHBIT; u=x[i];
          do
            { p1[ly] = (m & u) ? un : zero; ly++; }
          while ((m>>=1) && ly<=ex);
        }
        ly=1;
        if (m) i--; else m=HIGHBIT;
      }
      for (; i<lx; i++)
      {
        u=x[i];
        do { p2[ly] = m & u ? un : zero; ly++; } while (m>>=1);
        m=HIGHBIT;
      }
      break;

    case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); y=cgetg(lx,tx);
      for (i=1; i<lx; i++) y[i]=(long)binaire((GEN)x[i]);
      break;
    default: err(typeer,"binaire");
      return NULL; /* not reached */
  }
  return y;
}

/* return 1 if bit n of x is set, 0 otherwise */
long
bittest(GEN x, long n)
{
  long l;

  if (!signe(x) || n<0) return 0;
  l = lgefint(x)-1 - (n>>TWOPOTBITS_IN_LONG);
  if (l < 2) return 0;
  n = (1L << (n & (BITS_IN_LONG-1))) & x[l];
  return n? 1: 0;
}

GEN
bittest_many(GEN x, GEN gn, long c)
{
  long lx = lgefint(x), l1, l2, b1, b2, two_adic = 0, l_res, skip;
  ulong *p, *pnew;
  long n = itos(gn), extra_words = 0, partial_bits;
  GEN res;

  if (c == 1)                           /* Shortcut */
      return bittest(x,n) ? gun : gzero;
  /* Negative n with n+c>0 are too hairy to implement... */
  if (!signe(x) || c == 0)
      return gzero;
  if (c < 0) {                          /* Negative x means 2s complemenent */
      c = -c;
      if (signe(x) < 0)
          two_adic = 1;                 /* treat x 2-adically... */
  }
  if (n < 0) {
      pari_sp oa, na;

      if (n + c <= 0)
          return gzero;
      oa = avma;
      res = bittest_many(x, gzero, two_adic? -(n+c) : n+c);
      na = avma;
      res = shifti3(res,-n,0);
      return gerepile(oa,na,res);
  }
  partial_bits = (c & (BITS_IN_LONG-1));
  l2 = lx-1 - (n>>TWOPOTBITS_IN_LONG); /* Last=least-significant word */
  l1 = lx-1 - ((n + c - 1)>>TWOPOTBITS_IN_LONG); /* First word */
  b2 = (n & (BITS_IN_LONG-1));          /* Last bit, skip less-signifant */
  b1 = ((n + c - 1) & (BITS_IN_LONG-1)); /* First bit, skip more-significant */
  if (l2 < 2) {                         /* always: l1 <= l2 */
      if (!two_adic)
          return gzero;
      /* x is non-zero, so it behaves as -1.  */
      return gbitneg(gzero,c);
  }
  if (l1 < 2) {
      if (two_adic)     /* If b1 < b2, bits are set by prepend in shift_r */
          extra_words = 2 - l1 - (b1 < b2);
      else        
          partial_bits = b2 ? BITS_IN_LONG - b2 : 0;
      l1 = 2;
      b1 = (BITS_IN_LONG-1);            /* Include all bits in this word */
  }
  skip = (b1 < b2);                     /* Skip the first word of the shift */
  l_res = l2 - l1 + 1 + 2 - skip + extra_words; /* A coarse estimate */
  p = (ulong*) (new_chunk(l_res) + 2 + extra_words);
  shift_r(p - skip, (ulong*)x + l1, (ulong*)x + l2 + 1, 0, b2);
  if (two_adic) {                       /* Check the low bits of x */
        int i = lx, nonzero = 0;

        /* Flip the bits */
        pnew = p + l_res - 2 - extra_words;
        while (--pnew >= p)
            *pnew = MAXULONG - *pnew;
        /* Fill the extra words */
        while (extra_words--)
            *--p = MAXULONG;
        /* The result is one less than 2s-complement if the lower-bits
           of x were all 0. */
        while (--i > l2) {
            if (x[i]) {
                nonzero = 1;
                break;
            }
        }
        if (!nonzero && b2)             /* Check the partial word too */
            nonzero = x[l2] & ((1<<b2) - 1);
        if (!nonzero) { /* Increment res.  Do not underflow to before p */
            pnew = p + l_res - 2;
            while (--pnew >= p)
                if (++*pnew)
                    break;
        }
  }
  if (partial_bits)
      *p &= (1<<partial_bits) - 1;
  pnew = p;
  while ((pnew < p + l_res - 2) && !*pnew) /* Skip 0 words */
      pnew++;
  avma = (pari_sp)(pnew - 2);
  if (pnew >= p - 2 + l_res)
      return gzero;
  l_res -= (pnew - p);
  res = (GEN)(pnew - 2);
  res[1] = evalsigne(1)|evallgefint(l_res);
  res[0] = evaltyp(t_INT)|evallg(l_res);
  return res;
}

static long
bittestg(GEN x, GEN n)
{
  return bittest(x,itos(n));
}

GEN
gbittest(GEN x, GEN n)
{
  return arith_proto2(bittestg,x,n);
}

GEN
gbittest3(GEN x, GEN n, long c)
{
  return garith_proto3ggs(bittest_many,x,n,c);
}

/***********************************************************************/
/**                                                                   **/
/**                          BITMAP OPS                               **/
/** x & y (and), x | y (or), x ^ y (xor), ~x (neg), x & ~y (negimply) **/
/**                                                                   **/
/***********************************************************************/

/* Normalize a non-negative integer.  */
static void
inormalize(GEN x, long known_zero_words)
{
    int xl = lgefint(x);
    int i, j;

    /* Normalize */
    i = 2 + known_zero_words;
    while (i < xl) {
        if (x[i])
            break;
        i++;
    }
    j = 2;
    while (i < xl)
        x[j++] = x[i++];
    xl -= i - j;
    setlgefint(x, xl);
    if (xl == 2)
        setsigne(x,0);
}

/* Truncate a non-negative integer to a number of bits.  */
static void
ibittrunc(GEN x, long bits, long normalized)
{
    int xl = lgefint(x);
    int len_out = ((bits + BITS_IN_LONG - 1) >> TWOPOTBITS_IN_LONG) + 2;
    int known_zero_words, i = 2 + xl - len_out;

    if (xl < len_out && normalized)
        return;
        /* Check whether mask is trivial */
    if (!(bits & (BITS_IN_LONG - 1))) {
        if (xl == len_out && normalized)
            return;
    } else if (len_out <= xl) {
        /* Non-trival mask is given by a formula, if x is not
           normalized, this works even in the exceptional case */
        x[i] = x[i] & ((1 << (bits & (BITS_IN_LONG - 1))) - 1);
        if (x[i] && xl == len_out)
            return;
    }
    /* Normalize */
    if (xl <= len_out)                  /* Not normalized */
        known_zero_words = 0;
    else
        known_zero_words = xl - len_out;
    inormalize(x, known_zero_words);
}

/* Increment/decrement absolute value of non-zero integer in place.
   It is assumed that the increment will not increase the length.
   Decrement may result in a non-normalized value.
   Returns 1 if the increment overflows (thus the result is 0). */
static int
incdec(GEN x, long incdec)
{
    long *xf = x + 2, *xl;
    long len = lgefint(x);
    const ulong uzero = 0;

    xl = x + len;
    if (incdec == 1) {
        while (--xl >= xf) {
            if ((ulong)*xl != ~uzero) {
                (*xl)++;
                return 0;
            }
            *xl = 0;
        }
        return 1;
    } else {
        while (--xl >= xf) {
            if (*xl != 0) {
                (*xl)--;
                return 0;
            }
            *xl = (long)~uzero;
        }
        return 0;
    }
}

GEN
gbitneg(GEN x, long bits)
{
    long xl, len_out, i;
    const ulong uzero = 0;
    
    if (typ(x) != t_INT)
        err(typeer, "bitwise negation");
    if (bits < -1)
        err(talker, "negative exponent in bitwise negation");
    if (bits == -1)
        return gsub(gneg(gun),x);
    if (bits == 0)
        return gzero;
    if (signe(x) == -1) {               /* Consider as if mod big power of 2 */
        x = gcopy(x);
        setsigne(x, 1);
        incdec(x, -1);
        /* Now truncate this! */
        ibittrunc(x, bits, x[2]);
        return x;
    }
    xl = lgefint(x);
    len_out = ((bits + BITS_IN_LONG - 1) >> TWOPOTBITS_IN_LONG) + 2;
    if (len_out > xl) {                 /* Need to grow */
        GEN out = cgeti(len_out);
        int j = 2;

        if (!(bits & (BITS_IN_LONG - 1)))
            out[2] = ~uzero;
        else
            out[2] = (1 << (bits & (BITS_IN_LONG - 1))) - 1;
        for (i = 3; i < len_out - xl + 2; i++)
            out[i] = ~uzero;
        while (i < len_out)
            out[i++] = ~x[j++];
        setlgefint(out, len_out);
        setsigne(out,1);
        return out;
    }
    x = gcopy(x);
    for (i = 2; i < xl; i++)
        x[i] = ~x[i];
    ibittrunc(x, bits, x[2]);
    return x;
}

/* bitwise 'and' of two positive integers (any integers, but we ignore sign).
 * Inputs are not necessary normalized. */
static GEN
ibitand(GEN x, GEN y)
{
  long lx, ly, lout;
  long *xp, *yp, *outp, *xlim;
  GEN out;

  lx=lgefint(x); ly=lgefint(y);
  if (lx > ly)
      lout = ly;
  else
      lout = lx;
  xlim = x + lx;
  xp = xlim + 2 - lout;
  yp = y + 2 + ly - lout;
  out = cgeti(lout);
  outp = out + 2;
  while (xp < xlim)
      *outp++ = (*xp++) & (*yp++);
  setsigne(out,1);
  setlgefint(out,lout);
  if (lout == 2)
      setsigne(out,0);
  else if ( !out[2] )
      inormalize(out, 1);
  return out;
}

#define swaplen(x,y, nx,ny) {long _a=nx;GEN _z=x; nx=ny; ny=_a; x=y; y=_z;}

/* bitwise 'or' of two positive integers (any integers, but we ignore sign).
 * Inputs are not necessary normalized. */
static GEN
ibitor(GEN x, GEN y, long exclusive)
{
  long lx, ly, lout;
  long *xp, *yp, *outp, *xlim, *xprep;
  GEN out;

  lx=lgefint(x); ly=lgefint(y);
  if (lx < ly)
      swaplen(x,y,lx,ly);
  lout = lx;
  xlim = x + lx;
  xp = xlim + 2 - ly;
  yp = y + 2;
  out = cgeti(lout);
  outp = out + 2;
  if (lx > ly) {
      xprep = x + 2;
      while (xprep < xp)
          *outp++ = *xprep++;
  }
  if (exclusive) {
      while (xp < xlim)
          *outp++ = (*xp++) ^ (*yp++);
  } else {
      while (xp < xlim)
          *outp++ = (*xp++) | (*yp++);
  }
  setsigne(out,1);
  setlgefint(out,lout);
  if (lout == 2)
      setsigne(out,0);
  else if ( !out[2] )
      inormalize(out, 1);
  return out;
}

/* bitwise negated 'implies' of two positive integers (any integers, but we
 * ignore sign).  "Neg-Implies" is x & ~y unless "negated".
 * Inputs are not necessary normalized. */
static GEN
ibitnegimply(GEN x, GEN y)
{
  long lx, ly, lout, inverted = 0;
  long *xp, *yp, *outp, *xlim, *xprep;
  GEN out;

  lx=lgefint(x); ly=lgefint(y);
  if (lx < ly) {
      inverted = 1;
      swaplen(x,y,lx,ly);
  }  
  /* x is longer than y */
  lout = lx;
  xlim = x + lx;
  xp = xlim + 2 - ly;
  yp = y + 2;
  out = cgeti(lout);
  outp = out + 2;
  if (lx > ly) {
      xprep = x + 2;
      if (!inverted) {                  /* x & ~y */
          while (xprep < xp)
              *outp++ = *xprep++;
      } else {                          /* ~x & y */
          while (xprep++ < xp)
              *outp++ = 0;
      }
  }
  if (inverted) {                       /* ~x & y */
     while (xp < xlim)
        *outp++ = ~(*xp++) & (*yp++);
  } else {
     while (xp < xlim)
        *outp++ = (*xp++) & ~(*yp++);
  }
  setsigne(out,1);
  setlgefint(out,lout);
  if (lout == 2)
      setsigne(out,0);
  else if ( !out[2] )
      inormalize(out, 1);
  return out;
}

static GEN
inegate_inplace(GEN z, pari_sp ltop)
{
  long o;

  /* Negate z */
  o = incdec(z, 1);                     /* Can overflow z... */
  setsigne(z, -1);
  if (!o)
      return z;
  else if (lgefint(z) == 2)
      setsigne(z, 0);      
  incdec(z,-1);                 /* Restore a normalized value */
  return gerepileupto(ltop, subis(z,1));
}

GEN
gbitor(GEN x, GEN y)
{
  pari_sp ltop;
  long sx,sy;
  GEN z;

  if (typ(x) != t_INT || typ(y) != t_INT)
      err(typeer, "bitwise or");
  sx=signe(x); if (!sx) return icopy(y);
  sy=signe(y); if (!sy) return icopy(x);
  if (sx == 1) {
      if (sy == 1)
          return ibitor(x,y,0);
      goto posneg;
  } else if (sy == -1) {
      ltop = avma;
      incdec(x, -1); incdec(y, -1);
      z = ibitand(x,y);
      incdec(x, 1); incdec(y, 1);       /* Restore x and y... */
  } else {
      z = x; x = y; y = z;
      /* x is positive, y is negative.  The result will be negative. */
    posneg:
      ltop = avma;
      incdec(y, -1);
      z = ibitnegimply(y,x);            /* ~x & y */
      incdec(y, 1);
  }
  return inegate_inplace(z, ltop);
}

GEN
gbitand(GEN x, GEN y)
{
  pari_sp ltop;
  long sx,sy;
  GEN z;

  if (typ(x) != t_INT || typ(y) != t_INT)
      err(typeer, "bitwise and");
  sx=signe(x); if (!sx) return gzero;
  sy=signe(y); if (!sy) return gzero;
  if (sx == 1) {
      if (sy == 1)
          return ibitand(x,y);
      goto posneg;
  } else if (sy == -1) {
      ltop = avma;
      incdec(x, -1); incdec(y, -1);
      z = ibitor(x,y,0);
      incdec(x, 1); incdec(y, 1);       /* Restore x and y... */
      return inegate_inplace(z, ltop);
  } else {
      z = x; x = y; y = z;
      /* x is positive, y is negative.  The result will be positive. */
    posneg:
      ltop = avma;
      incdec(y, -1);
      /* x & ~y */
      z = ibitnegimply(x,y);            /* x & ~y */
      incdec(y, 1);
      return z;
  }
}

GEN
gbitxor(GEN x, GEN y)
{
  pari_sp ltop;
  long sx,sy;
  GEN z;

  if (typ(x) != t_INT || typ(y) != t_INT)
      err(typeer, "bitwise xor");
  sx=signe(x); if (!sx) return icopy(y);
  sy=signe(y); if (!sy) return icopy(x);
  if (sx == 1) {
      if (sy == 1)
          return ibitor(x,y,1);
      goto posneg;
  } else if (sy == -1) {
      incdec(x, -1); incdec(y, -1);
      z = ibitor(x,y,1);
      incdec(x, 1); incdec(y, 1);       /* Restore x and y... */
      return z;
  } else {
      z = x; x = y; y = z;
      /* x is positive, y is negative.  The result will be negative. */
    posneg:
      ltop = avma;
      incdec(y, -1);
      /* ~(x ^ ~y) == x ^ y */
      z = ibitor(x,y,1);
      incdec(y, 1);
  }
  return inegate_inplace(z, ltop);
}

GEN
gbitnegimply(GEN x, GEN y)              /* x & ~y */
{
  pari_sp ltop;
  long sx,sy;
  GEN z;

  if (typ(x) != t_INT || typ(y) != t_INT)
      err(typeer, "bitwise negated imply");
  sx=signe(x); if (!sx) return gzero;
  sy=signe(y); if (!sy) return icopy(x);
  if (sx == 1) {
      if (sy == 1)
          return ibitnegimply(x,y);
      /* x is positive, y is negative.  The result will be positive. */
      incdec(y, -1);
      z = ibitand(x,y);
      incdec(y, 1);
      return z;
  } else if (sy == -1) {
      /* both negative.  The result will be positive. */
      incdec(x, -1); incdec(y, -1);
      /* ((~x) & ~(~y)) == ~x & y */
      z = ibitnegimply(y,x);
      incdec(x, 1); incdec(y, 1);       /* Restore x and y... */
      return z;
  } else {
      /* x is negative, y is positive.  The result will be negative. */
      ltop = avma;
      incdec(x, -1);
      /* ~((~x) & ~y) == x | y */
      z = ibitor(x,y,0);
      incdec(x, 1);
  }
  return inegate_inplace(z, ltop);
}
