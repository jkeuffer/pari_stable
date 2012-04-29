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

static ulong _maxprime = 0;
static ulong diffptrlen;

/* Building/Rebuilding the diffptr table. The actual work is done by the
 * following two subroutines;  the user entry point is the function
 * initprimes() below.  initprimes1() is the old algorithm, called when
 * maxnum (size) is moderate. Must be called after pari_init_stack() )*/
static byteptr
initprimes1(ulong size, long *lenp, long *lastp, byteptr p1)
{
  pari_sp av = avma;
  long k;
  byteptr q, r, s, p = (byteptr)stack_calloc(size+2), fin = p + size;

  for (r=q=p,k=1; r<=fin; )
  {
    do { r+=k; k+=2; r+=k; } while (*++q);
    for (s=r; s<=fin; s+=k) *s = 1;
  }
  r = p1; *r++ = 2; *r++ = 1; /* 2 and 3 */
  for (s=q=p+1; ; s=q)
  {
    do q++; while (*q);
    if (q > fin) break;
    *r++ = (unsigned char) ((q-s) << 1);
  }
  *r++ = 0;
  *lenp = r - p1;
  *lastp = ((s - p) << 1) + 1;
  avma = av; return p1;
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
      pari_err(e_MISC, "unsupported type of cache model"); /* Future expansion */

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
    pari_err(e_MISC, "panic: set_optimize");
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

/* Here's the workhorse.  This is recursive, although normally the first
   recursive call will bottom out and invoke initprimes1() at once.
   (Not static;  might conceivably be useful to someone in library mode) */
static byteptr
initprimes0_i(ulong maxnum, long *lenp, ulong *lastp, byteptr p1)
{
  long alloced, psize;
  byteptr q, fin, p, fin1, plast, curdiff;
  ulong last, remains, curlow, rootnum, asize, maxpr = maxprime();
  ulong prime_above = 3;
  byteptr p_prime_above;

  maxnum |= 1;                  /* make it odd. */
  if (maxnum > maxpr && maxnum <= maxpr+512) maxnum = uprecprime(maxnum);
  if (maxnum <= maxpr)
  {
    long size;
    ulong prime, lastprime = 0;
    byteptr d;
    if (maxnum == maxpr)
    {
      memcpy(p1, diffptr, diffptrlen);
      *lastp = maxnum;
      *lenp = diffptrlen;
      return p1;
    }
    p = diffptr; lastprime = 0; /* -Wall */
    for (prime = 2, d = diffptr+1; prime < maxnum; )
    {
      p = d; lastprime = prime;
      NEXT_PRIME_VIADIFF(prime,d);
    }
    if (prime == maxnum) { p = d; lastprime = prime; }
    size = p-diffptr+1;
    memcpy(p1, diffptr, size-1);
    p1[size] = 0;
    *lastp = lastprime;
    *lenp = size;
    return p1;
  }
  if (maxnum <= 1ul<<17)        /* Arbitrary. */
    return initprimes1(maxnum>>1, lenp, (long*)lastp, p1); /* Break recursion */

  /* Checked to be enough up to 40e6, attained at 155893 */
  rootnum = (ulong) sqrt((double)maxnum); /* cast it back to a long */
  rootnum |= 1;
  /* recursive call (remember that maxnum > maxpr) */
  (void) initprimes0_i(maxss(rootnum, maxpr), &psize, &last, p1);
  fin1 = p1 + psize - 1;
  remains = (maxnum - last) >> 1; /* number of odd numbers to check */

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
  curlow = last + 2; /* First candidate: know primes up to last (odd). */
  curdiff = fin1;

  /* During each iteration p..fin-1 represents a range of odd
     numbers.  plast is a pointer which represents the last prime seen,
     it may point before p..fin-1. */
  plast = p - 1;
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

    sieve_chunk(p1, curlow, p, asize);

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
  return p1;
}
byteptr
initprimes0(ulong maxnum, long *lenp, ulong *lastp)
{
  /* Due to multibyte representation of large gaps, this estimate will
     be broken by large enough maxnum.  However, assuming exponential
     distribution of gaps with the average log(n), we are safe up to
     circa exp(-256/log(1/0.09)) = 1.5e46.  OK with LONG_BITS <= 128. ;-) */
  long size = (long) (1.09 * maxnum/log((double)maxnum)) + 146;
  byteptr p1 = initprimes0_i(maxnum, lenp, lastp, (byteptr)pari_malloc(size));
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

ulong
maxprime(void) { return diffptr ? _maxprime : 0; }

void
maxprime_check(ulong c)
{
  if (_maxprime < c) pari_err_MAXPRIME(c);
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

static byteptr
initprimes_i(ulong maxnum, long *lenp, ulong *lastp)
{
  byteptr p;
  /* The algorithm must see the next prime beyond maxnum, whence the +512. */
  ulong maxnum1 = ((maxnum<65302?65302:maxnum)+512ul);

  if ((maxnum>>1) > LONG_MAX - 1024)
    pari_err_OVERFLOW("initprimes [primelimit]");
  p = initprimes0(maxnum1, lenp, lastp);
#if 0 /* not yet... GN */
  static int build_the_tables = 1;
  if (build_the_tables) { init_tinyprimes_tridiv(p); build_the_tables=0; }
#endif
  return p;
}

byteptr
initprimes(ulong maxnum)
{
  long len;
  ulong last;
  return initprimes_i(maxnum, &len, &last);
}

void
initprimetable(ulong maxnum)
{
  long len;
  ulong last;
  byteptr p = initprimes_i(maxnum, &len, &last), old = diffptr;
  diffptrlen = minss(diffptrlen, len);
  _maxprime  = minss(_maxprime,last); /*Protect against ^C*/
  diffptr = p; diffptrlen = len; _maxprime = last;
  if (old) free(old);
}

GEN
boundfact(GEN n, ulong lim)
{
  switch(typ(n))
  {
    case t_INT: return Z_factor_limit(n,lim);
    case t_FRAC: {
      pari_sp av = avma;
      GEN a = Z_factor_limit(gel(n,1),lim);
      GEN b = Z_factor_limit(gel(n,2),lim);
      gel(b,2) = ZC_neg(gel(b,2));
      return gerepilecopy(av, merge_factor_i(a,b));
    }
  }
  pari_err_TYPE("boundfact",n);
  return NULL; /* not reached */
}

/* NOT memory clean */
GEN
Z_smoothen(GEN N, GEN L, GEN *pP, GEN *pe)
{
  long i, j, l = lg(L);
  GEN e = new_chunk(l), P = new_chunk(l);
  for (i = j = 1; i < l; i++)
  {
    ulong p = (ulong)L[i];
    long v = Z_lvalrem(N, p, &N);
    if (v) { P[j] = p; e[j] = v; j++; if (is_pm1(N)) { N = NULL; break; } }
  }
  P[0] = evaltyp(t_VECSMALL) | evallg(j); *pP = P;
  e[0] = evaltyp(t_VECSMALL) | evallg(j); *pe = e; return N;
}
/***********************************************************************/
/**                                                                   **/
/**                    SIMPLE FACTORISATIONS                          **/
/**                                                                   **/
/***********************************************************************/
/* Factor n and output [p,e,c] where
 * p, e and c are vecsmall with n = prod{p[i]^e[i]} and c[i] = p[i]^e[i] */
GEN
factoru_pow(ulong n)
{
  GEN f = cgetg(4,t_VEC);
  pari_sp av = avma;
  GEN F, P, E, p, e, c;
  long i, l;
  /* enough room to store <= 15 * [p,e,p^e] (OK if n < 2^64) */
  (void)new_chunk((15 + 1)*3);
  F = factoru(n);
  P = gel(F,1);
  E = gel(F,2); l = lg(P);
  avma = av;
  gel(f,1) = p = cgetg(l,t_VECSMALL);
  gel(f,2) = e = cgetg(l,t_VECSMALL);
  gel(f,3) = c = cgetg(l,t_VECSMALL);
  for(i = 1; i < l; i++)
  {
    p[i] = P[i];
    e[i] = E[i];
    c[i] = upowuu(p[i], e[i]);
  }
  return f;
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
  if (!B) return v? to_mat(gen_2, v): trivial_fact();
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
      if (is_matvec_t(tn)) pari_err_TYPE("divisors",n);
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
    if (e[i] < 0) pari_err(e_MISC, "denominators not allowed in divisors");
    nbdiv = itou_or_0( muluu(nbdiv, 1+e[i]) );
  }
  if (!nbdiv || nbdiv & ~LGBITS)
    pari_err(e_MISC, "too many divisors (more than %ld)", LGBITS - 1);
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

static GEN
corefa(GEN fa)
{
  GEN P = gel(fa,1), E = gel(fa,2), c = gen_1;
  long i;
  for (i=1; i<lg(P); i++)
    if (mod2(gel(E,i))) c = mulii(c,gel(P,i));
  return c;
}
static GEN
core2fa(GEN fa)
{
  GEN P = gel(fa,1), E = gel(fa,2), c = gen_1, f = gen_1;
  long i;
  for (i=1; i<lg(P); i++)
  {
    long e = itos(gel(E,i));
    if (e & 1)  c = mulii(c, gel(P,i));
    if (e != 1) f = mulii(f, powiu(gel(P,i), e >> 1));
  }
  return mkvec2(c,f);
}
GEN
corepartial(GEN n, long all)
{
  pari_sp av = avma;
  if (typ(n) != t_INT) pari_err_TYPE("corepartial",n);
  return gerepileuptoint(av, corefa(Z_factor_limit(n,all)));
}
GEN
core2partial(GEN n, long all)
{
  pari_sp av = avma;
  if (typ(n) != t_INT) pari_err_TYPE("core2partial",n);
  return gerepilecopy(av, core2fa(Z_factor_limit(n,all)));
}
static GEN
core2_i(GEN n)
{
  GEN f = core(n);
  if (!signe(f)) return mkvec2(gen_0, gen_1);
  return mkvec2(f, sqrtint(diviiexact(n, f)));
}
GEN
core2(GEN n) { pari_sp av = avma; return gerepilecopy(av, core2_i(n)); }

GEN
core0(GEN n,long flag) { return flag? core2(n): core(n); }

static long
_mod4(GEN c) {
  long r, s = signe(c);
  if (!s) return 0;
  r = mod4(c); if (s < 0) r = 4-r;
  return r;
}

GEN
coredisc(GEN n)
{
  pari_sp av = avma;
  GEN c = core(n);
  if (_mod4(c)<=1) return c; /* c = 0 or 1 mod 4 */
  return gerepileuptoint(av, shifti(c,2));
}

GEN
coredisc2(GEN n)
{
  pari_sp av = avma;
  GEN y = core2_i(n);
  GEN c = gel(y,1), f = gel(y,2);
  if (_mod4(c)<=1) return y;
  y = cgetg(3,t_VEC);
  gel(y,1) = shifti(c,2);
  gel(y,2) = gmul2n(f,-1); return gerepileupto(av, y);
}

GEN
coredisc0(GEN n,long flag) { return flag? coredisc2(n): coredisc(n); }

