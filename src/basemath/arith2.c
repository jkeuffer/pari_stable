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
#include "paripriv.h"

/* Building/Rebuilding the diffptr table. The actual work is done by the
 * following two subroutines;  the user entry point is the function
 * initprimes() below.  initprimes1() is the old algorithm, called when
 * maxnum (size) is moderate. */
static byteptr
initprimes1(ulong size, long *lenp, long *lastp)
{
  long k;
  byteptr q, r, s, p = (byteptr)pari_calloc(size+2), fin = p + size;

  for (r=q=p,k=1; r<=fin; )
  {
    do { r+=k; k+=2; r+=k; } while (*++q);
    for (s=r; s<=fin; s+=k) *s = 1;
  }
  r = p; *r++ = 2; *r++ = 1; /* 2 and 3 */
  for (s=q=r-1; ; s=q)
  {
    do q++; while (*q);
    if (q > fin) break;
    *r++ = (unsigned char) ((q-s) << 1);
  }
  *r++ = 0;
  *lenp = r - p;
  *lastp = ((s - p) << 1) + 1;
  return (byteptr) pari_realloc(p,r-p);
}

/*  Timing in ms (Athlon/850; reports 512K of secondary cache; looks
    like there is 64K of quickier cache too).

      arena|    30m     100m    300m    1000m    2000m  <-- primelimit
      =================================================
      16K       1.1053  1.1407  1.2589  1.4368   1.6086
      24K       1.0000  1.0625  1.1320  1.2443   1.3095
      32K       1.0000  1.0469  1.0761  1.1336   1.1776
      48K       1.0000  1.0000  1.0254  1.0445   1.0546
      50K       1.0000  1.0000  1.0152  1.0345   1.0464
      52K       1.0000  1.0000  1.0203  1.0273   1.0362
      54K       1.0000  1.0000  1.0812  1.0216   1.0281
      56K       1.0526  1.0000  1.0051  1.0144   1.0205
      58K       1.0000  1.0000  1.0000  1.0086   1.0123
      60K       0.9473  0.9844  1.0051  1.0014   1.0055
      62K       1.0000  0.9844  0.9949  0.9971   0.9993
      64K       1.0000  1.0000  1.0000  1.0000   1.0000
      66K       1.2632  1.2187  1.2183  1.2055   1.1953
      68K       1.4211  1.4844  1.4721  1.4425   1.4188
      70K       1.7368  1.7188  1.7107  1.6767   1.6421
      72K       1.9474  1.9531  1.9594  1.9023   1.8573
      74K       2.2105  2.1875  2.1827  2.1207   2.0650
      76K       2.4211  2.4219  2.4010  2.3305   2.2644
      78K       2.5789  2.6250  2.6091  2.5330   2.4571
      80K       2.8421  2.8125  2.8223  2.7213   2.6380
      84K       3.1053  3.1875  3.1776  3.0819   2.9802
      88K       3.5263  3.5312  3.5228  3.4124   3.2992
      92K       3.7895  3.8438  3.8375  3.7213   3.5971
      96K       4.0000  4.1093  4.1218  3.9986   3.9659
      112K      4.3684  4.5781  4.5787  4.4583   4.6115
      128K      4.7368  4.8750  4.9188  4.8075   4.8997
      192K      5.5263  5.7188  5.8020  5.6911   5.7064
      256K      6.0000  6.2187  6.3045  6.1954   6.1033
      384K      6.7368  6.9531  7.0405  6.9181   6.7912
      512K      7.3158  7.5156  7.6294  7.5000   7.4654
      768K      9.1579  9.4531  9.6395  9.5014   9.1075
      1024K    10.368  10.7497 10.9999 10.878   10.8201
      1536K    12.579  13.3124 13.7660 13.747   13.4739
      2048K    13.737  14.4839 15.0509 15.151   15.1282
      3076K    14.789  15.5780 16.2993 16.513   16.3365

    Now the same number relative to the model

    (1 + 0.36*sqrt(primelimit)/arena) * (arena <= 64 ? 1.05 : (arena-64)**0.38)

     [SLOW2_IN_ROOTS = 0.36, ALPHA = 0.38]

      arena|    30m     100m    300m    1000m    2000m  <-- primelimit
      =================================================
	16K    1.014    0.9835  0.9942  0.9889  1.004
	24K    0.9526   0.9758  0.9861  0.9942  0.981
	32K    0.971    0.9939  0.9884  0.9849  0.9806
	48K    0.9902   0.9825  0.996   0.9945  0.9885
	50K    0.9917   0.9853  0.9906  0.9926  0.9907
	52K    0.9932   0.9878  0.9999  0.9928  0.9903
	54K    0.9945   0.9902  1.064   0.9939  0.9913
	56K    1.048    0.9924  0.9925  0.993   0.9921
	58K    0.9969   0.9945  0.9909  0.9932  0.9918
	60K    0.9455   0.9809  0.9992  0.9915  0.9923
	62K    0.9991   0.9827  0.9921  0.9924  0.9929
	64K    1        1       1       1       1
	66K    1.02     0.9849  0.9857  0.9772  0.9704
	68K    0.8827   0.9232  0.9176  0.9025  0.8903
	70K    0.9255   0.9177  0.9162  0.9029  0.8881
	72K    0.9309   0.936   0.9429  0.9219  0.9052
	74K    0.9715   0.9644  0.967   0.9477  0.9292
	76K    0.9935   0.9975  0.9946  0.9751  0.9552
	78K    0.9987   1.021   1.021   1.003   0.9819
	80K    1.047    1.041   1.052   1.027   1.006
	84K    1.052    1.086   1.092   1.075   1.053
	88K    1.116    1.125   1.133   1.117   1.096
	92K    1.132    1.156   1.167   1.155   1.134
	96K    1.137    1.177   1.195   1.185   1.196
       112K    1.067    1.13    1.148   1.15    1.217
       128K    1.04     1.083   1.113   1.124   1.178
       192K    0.9368   0.985   1.025   1.051   1.095
       256K    0.8741   0.9224  0.9619  0.995   1.024
       384K    0.8103   0.8533  0.8917  0.9282  0.9568
       512K    0.7753   0.8135  0.8537  0.892   0.935
       768K    0.8184   0.8638  0.9121  0.9586  0.9705
      1024K    0.8241   0.8741  0.927   0.979   1.03
      1536K    0.8505   0.9212  0.9882  1.056   1.096
      2048K    0.8294   0.8954  0.9655  1.041   1.102

*/

#ifndef SLOW2_IN_ROOTS
  /* SLOW2_IN_ROOTS below 3: some slowdown starts to be noticable
   * when things fit into the cache on Sparc.
   * The choice of 2.6 gives a slowdown of 1-2% on UltraSparcII,
   * but makes calculations for "maximum" of 436273009 (not applicable anymore)
   * fit into 256K cache (still common for some architectures).
   *
   * One may change it when small caches become uncommon, but the gain
   * is not going to be very noticable... */
#  ifdef i386           /* gcc defines this? */
#    define SLOW2_IN_ROOTS      0.36
#  else
#    define SLOW2_IN_ROOTS      2.6
#  endif
#endif
#ifndef CACHE_ARENA
#  ifdef i386           /* gcc defines this? */
   /* Due to smaller SLOW2_IN_ROOTS, smaller arena is OK; fit L1 cache */
#    define CACHE_ARENA (63 * 1024UL) /* No slowdown even with 64K L1 cache */
#  else
#    define CACHE_ARENA (200 * 1024UL) /* No slowdown even with 256K L2 cache */
#  endif
#endif

#define CACHE_ALPHA     (0.38)          /* Cache performance model parameter */
#define CACHE_CUTOFF    (0.018)         /* Cache performance not smooth here */

static double slow2_in_roots = SLOW2_IN_ROOTS;

typedef struct {
    ulong arena;
    double power;
    double cutoff;
} cache_model_t;

static cache_model_t cache_model = { CACHE_ARENA, CACHE_ALPHA, CACHE_CUTOFF };

/* Assume that some calculation requires a chunk of memory to be
   accessed often in more or less random fashion (as in sieving).
   Assume that the calculation can be done in steps by subdividing the
   chunk into smaller subchunks (arenas) and treathing them
   separately.  Assume that the overhead of subdivision is equivalent
   to the number of arenas.

   Find an optimal size of the arena taking into account the overhead
   of subdivision, and the overhead of arena not fitting into the
   cache.  Assume that arenas of size slow2_in_roots slows down the
   calculation 2x (comparing to very big arenas; when cache hits do
   not matter).  Since cache performance varies wildly with
   architecture, load, and wheather (especially with cache coloring
   enabled), use an idealized cache model based on benchmarks above.

   Assume that an independent region of FIXED_TO_CACHE bytes is accessed
   very often concurrently with the arena access.
 */
static ulong
good_arena_size(ulong slow2_size, ulong total, ulong fixed_to_cache,
		cache_model_t *cache_model, long model_type)
{
  ulong asize, cache_arena = cache_model->arena;
  double Xmin, Xmax, A, B, C1, C2, D, V;
  double alpha = cache_model->power, cut_off = cache_model->cutoff;

  /* Estimated relative slowdown,
     with overhead = max((fixed_to_cache+arena)/cache_arena - 1, 0):

     1 + slow2_size/arena due to initialization overhead;

     max(1, 4.63 * overhead^0.38 ) due to footprint > cache size.

     [The latter is hard to substantiate theoretically, but this
     function describes benchmarks pretty close; it does not hurt that
     one can minimize it explicitly too ;-).  The switch between
     diffenent choices of max() happens whe overhead=0.018.]

     Thus the problem is minimizing (1 + slow2_size/arena)*overhead**0.29.
     This boils down to F=((X+A)/(X+B))X^alpha, X=overhead,
     B = (1 - fixed_to_cache/cache_arena), A = B +
     slow2_size/cache_arena, alpha = 0.38, and X>=0.018, X>-B.  It
     turns out that the minimization problem is not very nasty.  (As
     usual with minimization problems which depend on parameters,
     different values of A,B lead to different algorithms.  However,
     the boundaries between the domains in (A,B) plane where different
     algorithms work are explicitly calculatable.)

     Thus we need to find the rightmost root of (X+A)*(X+B) -
     alpha(A-B)X to the right of 0.018 (if such exists and is below
     Xmax).  Then we manually check the remaining region [0, 0.018].

     Since we cannot trust the purely-experimental cache-hit slowdown
     function, as a sanity check always prefer fitting into the
     cache (or "almost fitting") if F-law predicts that the larger
     value of the arena provides less than 10% speedup.

   */

  if (model_type != 0)
      pari_err(talker, "unsupported type of cache model"); /* Future expansion */

  /* The simplest case: we fit into cache */
  if (total + fixed_to_cache <= cache_arena)
      return total;
  /* The simple case: fitting into cache doesn't slow us down more than 10% */
  if (cache_arena - fixed_to_cache > 10 * slow2_size) {
      asize = cache_arena - fixed_to_cache;
      if (asize > total) asize = total; /* Automatically false... */
      return asize;
  }
  /* Slowdown of not fitting into cache is significant.  Try to optimize.
     Do not be afraid to spend some time on optimization - in trivial
     cases we do not reach this point; any gain we get should
     compensate the time spent on optimization.  */

  B = (1 - ((double)fixed_to_cache)/cache_arena);
  A = B + ((double)slow2_size)/cache_arena;
  C2 = A*B;
  C1 = (A + B - 1/alpha*(A - B))/2;
  D = C1*C1 - C2;
  if (D > 0)
      V = cut_off*cut_off + 2*C1*cut_off + C2; /* Value at CUT_OFF */
  else
      V = 0;                            /* Peacify the warning */
  Xmin = cut_off;
  Xmax = ((double)total - fixed_to_cache)/cache_arena; /* Two candidates */

  if ( D <= 0 || (V >= 0 && C1 + cut_off >= 0) ) /* slowdown increasing */
      Xmax = cut_off;                   /* Only one candidate */
  else if (V >= 0 &&                    /* slowdown concave down */
	   ((Xmax + C1) <= 0 || (Xmax*Xmax + 2*C1*Xmax + C2) <= 0))
      /* DO NOTHING */;                 /* Keep both candidates */
  else if (V <= 0 && (Xmax*Xmax + 2*C1*Xmax + C2) <= 0) /* slowdown decreasing */
      Xmin = cut_off;                   /* Only one candidate */
  else /* Now we know: 2 roots, the largest is in CUT_OFF..Xmax */
      Xmax = sqrt(D) - C1;
  if (Xmax != Xmin) {   /* Xmin == CUT_OFF; Check which one is better */
      double v1 = (cut_off + A)/(cut_off + B);
      double v2 = 2.33 * (Xmax + A)/(Xmax + B) * pow(Xmax, alpha);

      if (1.1 * v2 >= v1) /* Prefer fitting into the cache if slowdown < 10% */
	  V = v1;
      else {
	  Xmin = Xmax;
	  V = v2;
      }
  } else if (B > 0)                     /* We need V */
      V = 2.33 * (Xmin + A)/(Xmin + B) * pow(Xmin, alpha);
  if (B > 0 && 1.1 * V > A/B)  /* Now Xmin is the minumum.  Compare with 0 */
      Xmin = 0;

  asize = (ulong)((1 + Xmin)*cache_arena - fixed_to_cache);
  if (asize > total) asize = total;     /* May happen due to approximations */
  return asize;
}

/* Use as in
    install(set_optimize,lLDG)          \\ Through some M too?
    set_optimize(2,1) \\ disable dependence on limit
    \\ 1: how much cache usable, 2: slowdown of setup, 3: alpha, 4: cutoff
    \\ 2,3,4 are in units of 0.001

    { time_primes_arena(ar,limit) =     \\ ar = arena size in K
	set_optimize(1,floor(ar*1024));
	default(primelimit, 200 000);   \\ 100000 results in *larger* malloc()!
	gettime;
	default(primelimit, floor(limit));
	if(ar >= 1, ar=floor(ar));
	print("arena "ar"K => "gettime"ms");
    }
*/
long
set_optimize(long what, GEN g)
{
  long ret = 0;

  switch (what) {
  case 1:
    ret = (long)cache_model.arena;
    break;
  case 2:
    ret = (long)(slow2_in_roots * 1000);
    break;
  case 3:
    ret = (long)(cache_model.power * 1000);
    break;
  case 4:
    ret = (long)(cache_model.cutoff * 1000);
    break;
  default:
    pari_err(talker, "panic: set_optimize");
    break;
  }
  if (g != NULL) {
    ulong val = itou(g);

    switch (what) {
    case 1: cache_model.arena = val; break;
    case 2: slow2_in_roots     = (double)val / 1000.; break;
    case 3: cache_model.power  = (double)val / 1000.; break;
    case 4: cache_model.cutoff = (double)val / 1000.; break;
    }
  }
  return ret;
}

static void
sieve_chunk(byteptr known_primes, ulong s, byteptr data, ulong count)
{   /* start must be odd;
       prime differences (starting from (5-3)=2) start at known_primes[2],
       are terminated by a 0 byte;

       Checks cnt odd numbers starting at 'start', setting bytes
       starting at data to 0 or 1 depending on whether the
       corresponding odd number is prime or not */
    ulong p;
    byteptr q;
    register byteptr write_to = data;   /* Better code with gcc 2.8.1 */
    register ulong   cnt      = count;  /* Better code with gcc 2.8.1 */
    register ulong   start    = s;      /* Better code with gcc 2.8.1 */
    register ulong   delta    = 1;      /* Better code with gcc 2.8.1 */

    memset(data, 0, cnt);
    start >>= 1;                        /* (start - 1)/2 */
    start += cnt;                       /* Corresponds to the end */
    cnt -= 1;
    /* data corresponds to start.  q runs over primediffs.  */
    /* Don't care about DIFFPTR_SKIP: false positives provide no problem */
    for (q = known_primes + 1, p = 3; delta; delta = *++q, p += delta) {
	/* first odd number which is >= start > p and divisible by p
	   = last odd number which is <= start + 2p - 1 and 0 (mod p)
	   = p + the last even number which is <= start + p - 1 and 0 (mod p)
	   = p + the last even number which is <= start + p - 2 and 0 (mod p)
	   = p + start + p - 2 - (start + p - 2) % 2p
	   = start + 2(p - 1 - ((start-1)/2 + (p-1)/2) % p). */
      long off = cnt - ((start+(p>>1)) % p);

      while (off >= 0) {
	  write_to[off] = 1;
	  off -= p;
      }
    }
}

/* Do not inline sieve_chunk()!  It fits into registers in ix86 non-inlined */
void (*sieve_chunk_p)(byteptr known_primes, ulong s, byteptr data, ulong count)
    = sieve_chunk;

/* Here's the workhorse.  This is recursive, although normally the first
   recursive call will bottom out and invoke initprimes1() at once.
   (Not static;  might conceivably be useful to someone in library mode) */
byteptr
initprimes0(ulong maxnum, long *lenp, ulong *lastp)
{
  long size, alloced, psize;
  byteptr q, fin, p, p1, fin1, plast, curdiff;
  ulong last, remains, curlow, rootnum, asize;
  ulong prime_above = 3;
  byteptr p_prime_above;

  if (maxnum <= 1ul<<17)        /* Arbitrary. */
    return initprimes1(maxnum>>1, lenp, (long*)lastp); /* Break recursion */

  maxnum |= 1;                  /* make it odd. */

  /* Checked to be enough up to 40e6, attained at 155893 */
  /* Due to multibyte representation of large gaps, this estimate will
     be broken by large enough maxnum.  However, assuming exponential
     distribution of gaps with the average log(n), we are safe up to
     circa exp(-256/log(1/0.09)) = 1.5e46.  OK with LONG_BITS <= 128. ;-) */
  size = (long) (1.09 * maxnum/log((double)maxnum)) + 146;
  p1 = (byteptr) pari_malloc(size);
  rootnum = (ulong) sqrt((double)maxnum); /* cast it back to a long */
  rootnum |= 1;
  {
    byteptr p2 = initprimes0(rootnum, &psize, &last); /* recursive call */
    memcpy(p1, p2, psize); pari_free(p2);
  }
  fin1 = p1 + psize - 1;
  remains = (maxnum - rootnum) >> 1; /* number of odd numbers to check */

  /* Actually, we access primes array of psize too; but we access it
     consequently, thus we do not include it in fixed_to_cache */
  asize = good_arena_size((ulong)(rootnum * slow2_in_roots), remains + 1, 0,
			  &cache_model, 0) - 1;
  /* enough room on the stack ? */
  alloced = (((byteptr)avma) <= ((byteptr)bot) + asize);
  if (alloced)
    p = (byteptr) pari_malloc(asize + 1);
  else
    p = (byteptr) bot;
  fin = p + asize;              /* the 0 sentinel goes at fin. */
  curlow = rootnum + 2; /* First candidate: know primes up to rootnum (odd). */
  curdiff = fin1;

  /* During each iteration p..fin-1 represents a range of odd
     numbers.  plast is a pointer which represents the last prime seen,
     it may point before p..fin-1. */
  plast = p - ((rootnum - last) >> 1) - 1;
  p_prime_above = p1 + 2;
  while (remains)       /* Cycle over arenas.  Performance is not crucial */
  {
    unsigned char was_delta;

    if (asize > remains) {
      asize = remains;
      fin = p + asize;
    }
    /* Fake the upper limit appropriate for the given arena */
    while (prime_above*prime_above <= curlow + (asize << 1) && *p_prime_above)
	prime_above += *p_prime_above++;
    was_delta = *p_prime_above;
    *p_prime_above = 0;                 /* Put a 0 sentinel for sieve_chunk */

    (*sieve_chunk_p)(p1, curlow, p, asize);

    *p_prime_above = was_delta;         /* Restore */
    p[asize] = 0;                       /* Put a 0 sentinel for ZZZ */
    /* now q runs over addresses corresponding to primes */
    for (q = p; ; plast = q++)
    {
      long d;

      while (*q) q++;                   /* use ZZZ 0-sentinel at end */
      if (q >= fin) break;
      d = (q - plast) << 1;
      while (d >= DIFFPTR_SKIP)
	*curdiff++ = DIFFPTR_SKIP, d -= DIFFPTR_SKIP;
      *curdiff++ = (unsigned char)d;
    }
    plast -= asize;
    remains -= asize;
    curlow += (asize<<1);
  } /* while (remains) */
  last = curlow - ((p - plast) << 1);
  *curdiff++ = 0;               /* sentinel */
  *lenp = curdiff - p1;
  *lastp = last;
  if (alloced) pari_free(p);
  return (byteptr) pari_realloc(p1, *lenp);
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
  if (_maxprime < c) pari_err(primer2, c);
}

/* assume ptr is the address of a diffptr containing the succesive
 * differences between primes, and p = current prime (up to *ptr excluded)
 * return smallest prime >= a, update ptr */
ulong
init_primepointer(ulong a, ulong p, byteptr *ptr)
{
  byteptr diff = *ptr;
  if (a <= 0) a = 2;
  maxprime_check((ulong)a);
  while (a > p) NEXT_PRIME_VIADIFF(p,diff);
  *ptr = diff; return p;
}

byteptr
initprimes(ulong maxnum)
{
  long len;
  ulong last;
  byteptr p;
  /* The algorithm must see the next prime beyond maxnum, whence the +512. */
  ulong maxnum1 = ((maxnum<65302?65302:maxnum)+512ul);

  if ((maxnum>>1) > LONG_MAX - 1024)
      pari_err(talker, "Too large primelimit");
  p = initprimes0(maxnum1, &len, &last);
#if 0 /* not yet... GN */
  static int build_the_tables = 1;
  if (build_the_tables) { init_tinyprimes_tridiv(p); build_the_tables=0; }
#endif
  _maxprime = last; return p;
}

/***********************************************************************/
/**                                                                   **/
/**       COMPUTING THE MATRIX OF PRIME DIVISORS AND EXPONENTS        **/
/**                                                                   **/
/***********************************************************************/
static const long decomp_default_hint = 0;

/* where to stop trial dividing in factorization */
static ulong
default_bound(GEN n)
{
  ulong l = (ulong)expi(n) + 1;
  if (l <= 32)  return 1UL<<14;
  if (l <= 512) return (l-16) << 10;
  return 1UL<<19; /* Rho is generally faster above this */
}

static ulong
tridiv_bound(GEN n)
{
  ulong p = maxprime(), l = default_bound(n);
  return min(p, l);
}

static ulong
utridiv_bound(ulong n)
{
#ifdef LONG_IS_64BIT
  if (n & HIGHMASK)
  {
    ulong p = maxprime(), l;
    l = ((ulong)expu(n) + 1 - 16) << 10;
    return min(p, l);
  }
#endif
  return 1UL<<14;
}

static GEN
aux_end(GEN n, long nb)
{
  GEN P,E, z = (GEN)avma;
  long i;

  if (n) gunclone(n);
  P = cgetg(nb+1,t_COL);
  E = cgetg(nb+1,t_COL);
  for (i=nb; i; i--)
  {
    gel(E,i) = z; z += lg(z);
    gel(P,i) = z; z += lg(z);
  }
  gel(z,1) = P;
  gel(z,2) = E;
  return sort_factor(z, (void*)&absi_cmp, cmp_nodata);
}

static GEN
ifactor(GEN n, long (*ifac_break)(GEN n, GEN pairs, GEN here, GEN state),
	GEN state, ulong all, long hint)
{
  pari_sp av;
  long pp[] = { evaltyp(t_INT)|_evallg(4), 0,0,0 };
  long nb = 0, i, lp;
  ulong p, k, lim;
  byteptr d = diffptr+1; /* start at p = 3 */
#define STORE(x,e) { nb++; (void)x; (void)utoipos(e); }
#define STOREu(x,e) STORE(utoipos(x), e)
#define STOREi(x,e) STORE(icopy(x),   e)

  i = signe(n); if (!i) pari_err(talker, "zero argument in factorint");
  (void)cgetg(3,t_MAT);
  if (i < 0) STORE(utoineg(1), 1);
  if (is_pm1(n)) return aux_end(NULL,nb);

  n = gclone(n); setsigne(n,1);
  i = vali(n);
  if (i)
  {
    STOREu(2, i);
    av = avma; affii(shifti(n,-i), n); avma = av;
  }
  if (is_pm1(n)) return aux_end(n,nb);

  /* trial division bound */
  p = maxprime();
  if (!all) lim = p; /* smallfact() */
  else if (all > 1) lim = min(all, p); /* use supplied limit */
  else { lim = tridiv_bound(n); if (lim > p) lim = p; }

  /* trial division */
  p = 2;
  for(;;)
  {
    int stop;
    NEXT_PRIME_VIADIFF(p,d);
    if (p >= lim) break;

    k = Z_lvalrem_stop(n, p, &stop);
    if (k) STOREu(p, k);
    if (stop)
    {
      if (!is_pm1(n)) STOREi(n, 1);
      return aux_end(n,nb);
    }
  }

  /* pp = square of biggest p tried so far */
  av = avma; affii(muluu(p,p), pp); avma = av;

  /* trial divide by the "special primes" (usually huge composites) */
  lp = lg(primetab);
  for (i=1; i<lp; i++)
    if (dvdiiz(n,gel(primetab,i), n))
    {
      long k = 1; while (dvdiiz(n,gel(primetab,i), n)) k++;
      STOREi(gel(primetab,i), k);
      if (absi_cmp(pp, n) > 0)
      {
	if (!is_pm1(n)) STOREi(n, 1);
	return aux_end(n,nb);
      }
    }

  if (all != 1)
  { /* smallfact: look for easy pure powers then stop. Cf Z_isanypower */
    GEN x = n, y;
    ulong mask = 7, ex0 = 11;
    long ex, k = 1;
    av = avma;
    while (Z_issquareall(x, &y)) { k <<= 1; x = y; }
    while ( (ex = is_357_power(x, &y, &mask)) ) { k *= ex; x = y; }
    /* stop when x^(1/k) < 2^14 */
    while ( (ex = is_odd_power(x, &y, &ex0, 15)) ) { k *= ex; x = y; }
    if (k > 1) affii(x, n);
    avma = av; STOREi(n, k);
    if (DEBUGLEVEL >= 2) {
      pari_warn(warner, "IFAC: untested integer declared prime");
      fprintferr("\t%Ps\n", n);
    }
    return aux_end(n,nb);
  }

  /* test primality */
  if (BPSW_psp_nosmalldiv(n)) { STOREi(n, 1); return aux_end(n,nb); }

  /* now we have a large composite */
  if (ifac_break && (*ifac_break)(n,NULL,NULL,state)) /*initialize ifac_break*/
  {
    if (DEBUGLEVEL>2)
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
  GEN N;
  int res;
  (void)pairs;
  if (!here) /* initial call */
   /*Small primes have been removed, n is the new unfactored part.*/
    N = n;
  else
  {
    GEN q = powii(gel(here,0),gel(here,1)); /* primary factor found.*/
    if (DEBUGLEVEL>2) fprintferr("IFAC: Stop: Primary factor: %Ps\n",q);
    N = diviiexact(gel(state,1),q); /* divide unfactored part by q */
  }
  affii(N, gel(state,1)); /* affect()ed to state[1] to preserve stack. */
  if (DEBUGLEVEL>2) fprintferr("IFAC: Stop: remaining %Ps\n",state[1]);
  /* check the stopping criterion, then restore stack */
  res = cmpii(gel(state,1),gel(state,2)) <= 0;
  avma = ltop; return res;
}

/* see before ifac_crack() in ifactor1.c for current semantics of 'hint'
   (factorint's 'flag') */
GEN
factorint(GEN n, long flag)
{
  if (typ(n) != t_INT) pari_err(arither1);
  return ifactor(n,NULL,NULL, 1,flag);
}

GEN
Z_factor_limit(GEN n, long all)
{ return ifactor(n,NULL,NULL, all,decomp_default_hint); }
GEN
Z_factor(GEN n)
{ return ifactor(n,NULL,NULL, 1,decomp_default_hint); }

/* Factor until the unfactored part is smaller than limit. Return the
 * factored part. Hence factorback(output) may be smaller than n */
GEN
Z_factor_until(GEN n, GEN limit)
{
  GEN state = cgetg(3,t_VEC);
 /* icopy is mainly done to allocate memory for affect().
  * Currently state[1] is discarded in initial call to ifac_break_limit */
  gel(state,1) = icopy(n);
  gel(state,2) = gcopy(limit);
  return ifactor(n, &ifac_break_limit, state, 1, decomp_default_hint);
}

GEN
boundfact(GEN n, long lim)
{
  GEN p1, p2;
  pari_sp av = avma;

  if (lim <= 1) lim = 0;
  switch(typ(n))
  {
    case t_INT: return Z_factor_limit(n,lim);
    case t_FRAC:
      p1 = Z_factor_limit(gel(n,1),lim);
      p2 = Z_factor_limit(gel(n,2),lim); gel(p2,2) = gneg_i(gel(p2,2));
      return gerepilecopy(av, merge_factor_i(p1,p2));
  }
  pari_err(arither1);
  return NULL; /* not reached */
}
/***********************************************************************/
/**                                                                   **/
/**                    SIMPLE FACTORISATIONS                          **/
/**                                                                   **/
/***********************************************************************/

/* Factor n and output [p,e] where
 * p, e are vecsmall with n = prod{p[i]^e[i]} */
GEN
factoru(ulong n)
{
  pari_sp ltop = avma;
  GEN F = Z_factor(utoi(n)), P = gel(F,1), E = gel(F,2);
  long i, l = lg(P);
  GEN f = cgetg(3,t_VEC);
  GEN p = cgetg(l,t_VECSMALL);
  GEN e = cgetg(l,t_VECSMALL);
  gel(f,1) = p;
  gel(f,2) = e;
  for (i = 1; i < l; i++)
  {
    p[i] = itou(gel(P,i));
    e[i] = itou(gel(E,i));
  }
  return gerepileupto(ltop,f);
}
/* Factor n and output [p,e,c] where
 * p, e and c are vecsmall with n = prod{p[i]^e[i]} and c[i] = p[i]^e[i] */
GEN
factoru_pow(ulong n)
{
  pari_sp ltop = avma;
  GEN F = Z_factor(utoi(n)), P = gel(F,1), E = gel(F,2);
  long i, l = lg(P);
  GEN f = cgetg(4,t_VEC);
  GEN p = cgetg(l,t_VECSMALL);
  GEN e = cgetg(l,t_VECSMALL);
  GEN c = cgetg(l,t_VECSMALL);
  pari_sp lbot = avma;
  gel(f,1) = p;
  gel(f,2) = e;
  gel(f,3) = c;
  for(i = 1; i < l; i++)
  {
    p[i] = itou(gel(P,i));
    e[i] = itou(gel(E,i));
    c[i] = itou(powiu(gel(P,i), e[i]));
  }
  avma = lbot; return gerepileupto(ltop,f);
}

/* factor p^n - 1, assuming p prime */
GEN
factor_pn_1(GEN p, long n)
{
  pari_sp av = avma;
  GEN A = Z_factor(subis(p,1)), d = divisorsu(n);
  long i, pp = itos_or_0(p);
  for(i=2; i<lg(d); i++)
  {
    GEN B;
    if (pp && d[i]%pp==0 && (
       ((pp&3)==1 && (d[i]&1)) ||
       ((pp&3)==3 && (d[i]&3)==2) ||
       (pp==2 && (d[i]&7)==4)))
    {
      GEN f=factor_Aurifeuille_prime(p,d[i]);
      B = Z_factor(f);
      A = merge_factor(A, B, (void*)&cmpii, cmp_nodata);
      B = Z_factor(diviiexact(polcyclo_eval(d[i],p), f));
    }
    else
      B = Z_factor(polcyclo_eval(d[i],p));
    A = merge_factor(A, B, (void*)&cmpii, cmp_nodata);
  }
  return gerepilecopy(av, A);
}

#if 0
static GEN
to_mat(GEN p, long e) {
  GEN B = cgetg(3, t_MAT);
  gel(B,1) = mkcol(p);
  gel(B,2) = mkcol(utoipos(e)); return B;
}
/* factor phi(n) */
GEN
factor_eulerphi(GEN n)
{
  pari_sp av = avma;
  GEN B = NULL, A, P, E, AP, AE;
  long i, l, v = vali(n);

  l = lg(n);
  /* result requires less than this: at most expi(n) primes */
  (void)new_chunk(bit_accuracy(l) * (l /*p*/ + 3 /*e*/ + 2 /*vectors*/) + 3+2);
  if (v) { n = shifti(n, -v); v--; }
  A = Z_factor(n); P = gel(A,1); E = gel(A,2); l = lg(P);
  for(i = 1; i < l; i++)
  {
    GEN p = gel(P,i), q = subis(p,1), fa;
    long e = itos(gel(E,i)), w;

    w = vali(q); v += w; q = shifti(q,-w);
    if (! is_pm1(q))
    {
      fa = Z_factor(q);
      B = B? merge_factor(B, fa, (void*)&cmpii, cmp_nodata): fa;
    }
    if (e > 1) {
      if (B) {
	gel(B,1) = shallowconcat(gel(B,1), p);
	gel(B,2) = shallowconcat(gel(B,2), utoipos(e-1));
      } else
	B = to_mat(p, e-1);
    }
  }
  avma = av;
  if (!B) return v? to_mat(gen_2, v): trivfact();
  A = cgetg(3, t_MAT);
  P = gel(B,1); E = gel(B,2); l = lg(P);
  AP = cgetg(l+1, t_COL); gel(A,1) = AP; AP++;
  AE = cgetg(l+1, t_COL); gel(A,2) = AE; AE++;
  /* prepend "2^v" */
  gel(AP,0) = gen_2;
  gel(AE,0) = utoipos(v);
  for (i = 1; i < l; i++)
  {
    gel(AP,i) = icopy(gel(P,i));
    gel(AE,i) = icopy(gel(E,i));
  }
  return A;
}
#endif

/***********************************************************************/
/**                                                                   **/
/**                    BASIC ARITHMETIC FUNCTIONS                     **/
/**                                                                   **/
/***********************************************************************/

GEN
gmoebius(GEN n) { return map_proto_lG(moebius,n); }

INLINE void
chk_arith(GEN n) {
  if (typ(n) != t_INT) pari_err(arither1);
  if (!signe(n)) pari_err(talker, "zero argument in an arithmetic function");
}

long
moebius(GEN n)
{
  byteptr d = diffptr+1; /* point at 3 - 2 */
  pari_sp av = avma;
  ulong p, lim;
  long s, v;

  chk_arith(n); if (is_pm1(n)) return 1;
  if (equaliu(n, 2)) return -1;
  p = mod4(n); if (!p) return 0;
  if (p == 2) { s = -1; n = shifti(n, -1); } else { s = 1; n = icopy(n); }
  setsigne(n, 1);

  lim = tridiv_bound(n);
  p = 2;
  while (p < lim)
  {
    int stop;
    NEXT_PRIME_VIADIFF(p,d);
    v = Z_lvalrem_stop(n, p, &stop);
    if (v > 1) { avma = av; return 0; }
    if (v) s = -s;
    if (stop) { avma = av; return is_pm1(n)? s: -s; }
  }
  if (BPSW_psp_nosmalldiv(n)) { avma=av; return -s; }
  /* large composite without small factors */
  v = ifac_moebius(n, decomp_default_hint);
  avma = av; return (s<0 ? -v : v); /* correct also if v==0 */
}

GEN
gissquarefree(GEN x) { return map_proto_lG(issquarefree,x); }

long
Z_issquarefree(GEN x)
{
  byteptr d = diffptr+1;
  pari_sp av = avma;
  ulong p, lim;
  long v;

  if (!signe(x)) return 0;
  if (cmpiu(x, 2) <= 0) return 1;
  p = mod4(x); if (!p) return 0;
  x = (p == 2)? shifti(x, -1): icopy(x);
  setsigne(x, 1);

  lim = tridiv_bound(x);
  p = 2;
  while (p < lim)
  {
    int stop;
    NEXT_PRIME_VIADIFF(p,d);
    v = Z_lvalrem_stop(x, p, &stop);
    if (v > 1) { avma = av; return 0; }
    if (stop) { avma = av; return 1; }
  }
  if (BPSW_psp_nosmalldiv(x)) { avma = av; return 1; }
  v = ifac_issquarefree(x, decomp_default_hint);
  avma = av; return v;
}

long
issquarefree(GEN x)
{
  pari_sp av;
  GEN d;
  switch(typ(x))
  {
    case t_INT: return Z_issquarefree(x);
    case t_POL:
      if (!signe(x)) return 0;
      av = avma; d = RgX_gcd(x, RgX_deriv(x));
      avma = av; return (lg(d) == 3);
    default: pari_err(typeer,"issquarefree");
      return 0; /* not reached */
  }
}

GEN
gomega(GEN n) { return map_proto_lG(omega,n); }

long
omega(GEN n)
{
  byteptr d = diffptr+1;
  pari_sp av = avma;
  long nb,v;
  ulong p, lim;

  chk_arith(n); if (is_pm1(n)) return 0;
  v = vali(n); nb = v ? 1 : 0;
  n = shifti(n, -v);
  if (is_pm1(n)) return nb;
  setsigne(n, 1);

  lim = tridiv_bound(n);
  p = 2;
  while (p < lim)
  {
    int stop;
    NEXT_PRIME_VIADIFF(p,d);
    v = Z_lvalrem_stop(n, p, &stop);
    if (v) nb++;
    if (stop) { avma = av; return is_pm1(n)? nb: nb+1; }
  }
  if (BPSW_psp_nosmalldiv(n)) { avma = av; return nb+1; }
  /* large composite without small factors */
  nb += ifac_omega(n, decomp_default_hint);
  avma = av; return nb;
}

GEN
gbigomega(GEN n) { return map_proto_lG(bigomega,n); }

long
bigomega(GEN n)
{
  byteptr d=diffptr+1;
  pari_sp av = avma;
  ulong p, lim;
  long nb,v;

  chk_arith(n); if (is_pm1(n)) return 0;
  nb = v = vali(n); n = shifti(n, -v);
  if (is_pm1(n)) { avma = av; return nb; }
  setsigne(n, 1);

  lim = tridiv_bound(n);
  p = 2;
  while (p < lim)
  {
    int stop;
    NEXT_PRIME_VIADIFF(p,d);
    v = Z_lvalrem_stop(n, p, &stop);
    nb += v;
    if (stop) { avma = av; return is_pm1(n)? nb: nb+1; }
  }
  if (BPSW_psp_nosmalldiv(n)) { avma = av; return nb+1; }
  nb += ifac_bigomega(n, decomp_default_hint);
  avma = av; return nb;
}

GEN
geulerphi(GEN n) { return map_proto_G(eulerphi,n); }

ulong
eulerphiu(ulong n)
{
  byteptr d = diffptr+1;
  pari_sp av;
  ulong p, lim, m;
  long v;

  if (n == 1) return 1;
  v = vals(n); n >>= v;
  m = v > 1 ? 1 << (v-1) : 1;
  if (n == 1) return m;

  lim = utridiv_bound(n);
  p = 2;
  while (p < lim)
  {
    int stop;
    NEXT_PRIME_VIADIFF(p,d);
    v = u_lvalrem_stop(&n, p, &stop);
    if (v) {
      m *= p-1;
      if (v > 1) m *= upowuu(p, v-1);
    }
    if (stop) {
      if (n != 1) m *= n-1;
      return m;
    }
  }
  if (uisprime_nosmalldiv(n)) return m*(n-1);
  av = avma;
  m *= itou( ifac_totient(utoipos(n), decomp_default_hint) );
  avma = av; return m;
}

GEN
eulerphi(GEN n)
{
  byteptr d = diffptr+1;
  pari_sp av = avma;
  GEN m;
  ulong p, lim;
  long v;

  chk_arith(n);
  if (lgefint(n) == 3) return utoipos(eulerphiu((ulong)n[2]));
  v = vali(n); n = shifti(n,-v); setsigne(n, 1);
  m = v > 1 ? int2n(v-1) : gen_1;
  if (is_pm1(n)) return gerepileuptoint(av,m);

  lim = tridiv_bound(n);
  p = 2;
  while (p < lim)
  {
    int stop;
    NEXT_PRIME_VIADIFF(p,d);
    v = Z_lvalrem_stop(n, p, &stop);
    if (v) {
      m = muliu(m, p-1);
      if (v > 2) m = mulii(m, powuu(p, v-1));
      else if (v == 2) m = muliu(m, p);
    }
    if (stop) {
      if (!is_pm1(n)) m = mulii(m, addis(n,-1));
      return gerepileuptoint(av,m);
    }
  }
  if (BPSW_psp_nosmalldiv(n)) return gerepileuptoint(av, mulii(m, addis(n,-1)));
  m = mulii(m, ifac_totient(n, decomp_default_hint));
  return gerepileuptoint(av,m);
}

GEN
gnumbdiv(GEN n) { return map_proto_G(numbdiv,n); }

GEN
numbdiv(GEN n)
{
  byteptr d = diffptr+1;
  pari_sp av = avma;
  GEN m;
  long v;
  ulong p, lim;

  chk_arith(n); if (is_pm1(n)) return gen_1;
  v = vali(n); n = shifti(n,-v); setsigne(n,1);
  m = utoipos(v+1);
  if (is_pm1(n)) return gerepileuptoint(av,m);

  lim = tridiv_bound(n);
  p = 2;
  while (p < lim)
  {
    int stop;
    NEXT_PRIME_VIADIFF(p,d);
    v = Z_lvalrem_stop(n, p, &stop);
    if (v) m = muliu(m, v+1);
    if (stop)
    {
      if (!is_pm1(n)) m = shifti(m,1);
      return gerepileuptoint(av,m);
    }
  }
  if(BPSW_psp_nosmalldiv(n)) return gerepileuptoint(av, shifti(m,1));
  m = mulii(m, ifac_numdiv(n, decomp_default_hint));
  return gerepileuptoint(av,m);
}

GEN
gsumdiv(GEN n) { return map_proto_G(sumdiv,n); }

GEN
sumdiv(GEN n)
{
  byteptr d = diffptr+1;
  pari_sp av = avma, av2, limit;
  GEN m;
  ulong p, lim;
  long v;

  chk_arith(n); if (is_pm1(n)) return gen_1;
  v = vali(n); n = shifti(n,-v); setsigne(n,1);
  m = v ? addsi(-1, int2n(v+1)) : gen_1;
  if (is_pm1(n)) return gerepileuptoint(av,m);

  lim = tridiv_bound(n);
  p = 2; av2 = avma; limit = stack_lim(av2,3);
  while (p < lim)
  {
    int stop;
    NEXT_PRIME_VIADIFF(p,d);
    v = Z_lvalrem_stop(n, p, &stop);
    if (v)
    {
      GEN m1 = utoipos(p+1);
      long i;
      for (i = 1; i < v; i++) m1 = addsi(1, mului(p,m1));
      m = mulii(m1,m);
    }
    if (low_stack(limit, stack_lim(av2,3)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"sumdiv");
      m = gerepileuptoint(av2, m);
    }
    if (stop)
    {
      if (!is_pm1(n)) m = mulii(m,addis(n,1));
      return gerepileuptoint(av, m);
    }
  }
  if(BPSW_psp_nosmalldiv(n)) return gerepileuptoint(av, mulii(m,addsi(1,n)));
  m = mulii(m, ifac_sumdivk(n, 1, decomp_default_hint));
  return gerepileuptoint(av,m);
}

GEN
gsumdivk(GEN n, long k) { return map_proto_GL(sumdivk,n,k); }

GEN
sumdivk(GEN n, long k)
{
  byteptr d = diffptr+1;
  pari_sp av = avma, av2, limit;
  GEN n1, m;
  ulong p, lim;
  long k1,v;

  if (!k) return numbdiv(n);
  if (k == 1) return sumdiv(n);
  chk_arith(n); if (is_pm1(n)) return gen_1;
  k1 = k; n1 = n;
  if (k < 0)  k = -k;
  if (k == 1) { m = sumdiv(n); goto fin; }
  v = vali(n); n = shifti(n,-v); setsigne(n,1);
  m = gen_1;
  while (v--)  m = addsi(1,shifti(m,k));
  if (is_pm1(n)) goto fin;

  lim = tridiv_bound(n);
  p = 2; av2 = avma; limit = stack_lim(av2,3);
  while (p < lim)
  {
    int stop;
    NEXT_PRIME_VIADIFF(p,d);
    v = Z_lvalrem_stop(n, p, &stop);
    if (v)
    {
      long i;
      GEN pk = powuu(p,k), m1 = addsi(1,pk);
      for (i = 1; i < v; i++) m1 = addsi(1, mulii(pk,m1));
      m = mulii(m1,m);
    }
    if (low_stack(limit, stack_lim(av2,3)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"sumdiv");
      m = gerepileuptoint(av2, m);
    }
    if (stop)
    {
      if (!is_pm1(n)) m = mulii(m, addsi(1, powiu(n,k)));
      goto fin;
    }
  }
  if (BPSW_psp_nosmalldiv(n)) { m = mulii(m, addsi(1, powiu(n,k))); goto fin; }
  m = mulii(m, ifac_sumdivk(n, k, decomp_default_hint));
 fin:
  if (k1 < 0) m = gdiv(m, powiu(n1,k));
  return gerepileupto(av,m);
}

/***********************************************************************/
/**                                                                   **/
/**                MISCELLANEOUS ARITHMETIC FUNCTIONS                 **/
/**                (ultimately depend on Z_factor())                  **/
/**                                                                   **/
/***********************************************************************/

GEN
divisors(GEN n)
{
  pari_sp av = avma;
  long i, j, l, tn = typ(n);
  ulong nbdiv;
  int isint = 1;
  GEN *d, *t, *t1, *t2, *t3, P, E, e;

  if (tn == t_MAT && lg(n) == 3)
  {
    P = gel(n,1); l = lg(P);
    for (i = 1; i < l; i++)
      if (typ(gel(P,i)) != t_INT) { isint = 0; break; }
  }
  else
  {
    if (tn == t_INT)
      n = Z_factor(n);
    else {
      if (is_matvec_t(tn)) pari_err(typeer,"divisors");
      isint = 0;
      n = factor(n);
    }
    P = gel(n,1); l = lg(P);
  }
  E = gel(n,2);
  if (isint && l>1 && signe(P[1]) < 0) { E++; P++; l--; } /* skip -1 */
  e = cgetg(l, t_VECSMALL);
  nbdiv = 1;
  for (i=1; i<l; i++)
  {
    e[i] = itos(gel(E,i));
    if (e[i] < 0) pari_err(talker, "denominators not allowed in divisors");
    nbdiv = itou_or_0( muluu(nbdiv, 1+e[i]) );
  }
  if (!nbdiv || nbdiv & ~LGBITS)
    pari_err(talker, "too many divisors (more than %ld)", LGBITS - 1);
  d = t = (GEN*) cgetg(nbdiv+1,t_VEC);
  *++d = gen_1;
  if (isint)
  {
    for (i=1; i<l; i++)
      for (t1=t,j=e[i]; j; j--,t1=t2)
	for (t2=d, t3=t1; t3<t2; ) *++d = mulii(*++t3, gel(P,i));
    e = sort((GEN)t);
  } else {
    for (i=1; i<l; i++)
      for (t1=t,j=e[i]; j; j--,t1=t2)
	for (t2=d, t3=t1; t3<t2; ) *++d = gmul(*++t3, gel(P,i));
    e = (GEN)t;
  }
  return gerepileupto(av, e);
}

GEN
divisorsu(ulong n)
{
  pari_sp av = avma;
  long i, j, l;
  ulong nbdiv;
  GEN d, t, t1, t2, t3, P, e, fa = factoru(n);

  P = gel(fa,1); l = lg(P);
  e = gel(fa,2);
  nbdiv = 1;
  for (i=1; i<l; i++) nbdiv *= 1+e[i];
  d = t = cgetg(nbdiv+1,t_VECSMALL);
  *++d = 1;
  for (i=1; i<l; i++)
    for (t1=t,j=e[i]; j; j--,t1=t2)
      for (t2=d, t3=t1; t3<t2; ) *(++d) = *(++t3) * P[i];
  vecsmall_sort(t);
  return gerepileupto(av, t);
}

GEN
corepartial(GEN n, long all)
{
  pari_sp av = avma;
  long i;
  GEN fa, P, E, c = gen_1;

  if (typ(n) != t_INT) pari_err(typeer,"corepartial");
  fa = Z_factor_limit(n,all);
  P = gel(fa,1);
  E = gel(fa,2);
  for (i=1; i<lg(P); i++)
    if (mod2(gel(E,i))) c = mulii(c,gel(P,i));
  return gerepileuptoint(av, c);
}

GEN
core2partial(GEN n, long all)
{
  pari_sp av = avma;
  long i;
  GEN fa, P, E, c = gen_1, f = gen_1;

  if (typ(n) != t_INT) pari_err(typeer,"core2partial");
  fa = Z_factor_limit(n,all);
  P = gel(fa,1);
  E = gel(fa,2);
  for (i=1; i<lg(P); i++)
  {
    long e = itos(gel(E,i));
    if (e & 1)  c = mulii(c, gel(P,i));
    if (e != 1) f = mulii(f, gpowgs(gel(P,i), e >> 1));
  }
  return gerepilecopy(av, mkvec2(c,f));
}

GEN core(GEN n)  { return corepartial(n,1); }
GEN core2(GEN n) { return core2partial(n,1); }

GEN
core0(GEN n,long flag) { return flag? core2(n): core(n); }

static long
_mod4(GEN c) { long r = mod4(c); if (signe(c) < 0) r = 4-r; return r; }

GEN
coredisc(GEN n)
{
  pari_sp av = avma;
  GEN c = core(n);
  if (_mod4(c)==1) return c;
  return gerepileuptoint(av, shifti(c,2));
}

GEN
coredisc2(GEN n)
{
  pari_sp av = avma;
  GEN y = core2(n);
  GEN c = gel(y,1), f = gel(y,2);
  if (_mod4(c)==1) return y;
  y = cgetg(3,t_VEC);
  gel(y,1) = shifti(c,2);
  gel(y,2) = gmul2n(f,-1); return gerepileupto(av, y);
}

GEN
coredisc0(GEN n,long flag) { return flag? coredisc2(n): coredisc(n); }

