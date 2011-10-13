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
/*********************************************************************/
/**                                                                 **/
/**               PSEUDO PRIMALITY (MILLER-RABIN)                   **/
/**                                                                 **/
/*********************************************************************/
typedef struct {
  ulong n, sqrt1, sqrt2, t1, t;
  long r1;
} Fl_MR_Jaeschke_t;

typedef struct {
  GEN n, sqrt1, sqrt2, t1, t;
  long r1;
} MR_Jaeschke_t;

static void
init_MR_Jaeschke(MR_Jaeschke_t *S, GEN n)
{
  if (signe(n) < 0) n = absi(n);
  S->n = n;
  S->t = addsi(-1,n);
  S->r1 = vali(S->t);
  S->t1 = shifti(S->t, -S->r1);
  S->sqrt1 = cgeti(lg(n)); S->sqrt1[1] = evalsigne(0)|evallgefint(2);
  S->sqrt2 = cgeti(lg(n)); S->sqrt2[1] = evalsigne(0)|evallgefint(2);
}
static void
Fl_init_MR_Jaeschke(Fl_MR_Jaeschke_t *S, ulong n)
{
  S->n = n;
  S->t = n-1;
  S->r1 = vals(S->t);
  S->t1 = S->t >> S->r1;
  S->sqrt1 = 0;
  S->sqrt2 = 0;
}

/* c = sqrt(-1) seen in bad_for_base. End-matching: compare or remember
 * If ends do mismatch, then we have factored n, and this information
 * should somehow be made available to the factoring machinery. But so
 * exceedingly rare... besides we use BSPW now. */
static int
MR_Jaeschke_ok(MR_Jaeschke_t *S, GEN c)
{
  if (signe(S->sqrt1))
  { /* saw one earlier: compare */
    if (!equalii(c, S->sqrt1) && !equalii(c, S->sqrt2))
    { /* too many sqrt(-1)s mod n */
      if (DEBUGLEVEL) {
        GEN z = gcdii(addii(c, S->sqrt1), S->n);
        pari_warn(warner,"found factor\n\t%Ps\ncurrently lost to the factoring machinery", z);
      }
      return 1;
    }
  } else { /* remember */
    affii(c, S->sqrt1);
    affii(subii(S->n, c), S->sqrt2);
  }
  return 0;
}
static int
Fl_MR_Jaeschke_ok(Fl_MR_Jaeschke_t *S, ulong c)
{
  if (S->sqrt1)
  { /* saw one earlier: compare */
    if (c != S->sqrt1 && c != S->sqrt2) return 1;
  } else { /* remember */
    S->sqrt1 = c;
    S->sqrt2 = S->n - c;
  }
  return 0;
}

/* is n strong pseudo-prime for base a ? 'End matching' (check for square
 * roots of -1) added by GN */
static int
bad_for_base(MR_Jaeschke_t *S, GEN a)
{
  long r, lim, av = avma;
  GEN c2, c = Fp_pow(a, S->t1, S->n);

  if (is_pm1(c) || equalii(S->t, c)) return 0;

  lim = stack_lim(av,1);
  /* go fishing for -1, not for 1 (saves one squaring) */
  for (r = S->r1 - 1; r; r--) /* r1 - 1 squarings */
  {
    c2 = c; c = remii(sqri(c), S->n);
    if (equalii(S->t, c)) return MR_Jaeschke_ok(S, c2);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"Rabin-Miller");
      c = gerepileuptoint(av, c);
    }
  }
  return 1;
}
static int
Fl_bad_for_base(Fl_MR_Jaeschke_t *S, ulong a)
{
  long r;
  ulong c2, c = Fl_powu(a, S->t1, S->n);

  if (c == 1 || c == S->t) return 0;

  /* go fishing for -1, not for 1 (saves one squaring) */
  for (r = S->r1 - 1; r; r--) /* r1 - 1 squarings */
  {
    c2 = c; c = Fl_sqr(c, S->n);
    if (c == S->t) return Fl_MR_Jaeschke_ok(S, c2);
  }
  return 1;
}

/* Miller-Rabin test for k random bases */
long
millerrabin(GEN n, long k)
{
  pari_sp av2, av = avma;
  ulong r;
  long i;
  MR_Jaeschke_t S;

  if (typ(n) != t_INT) pari_err_TYPE("millerrabin",n);
  if (signe(n)<=0) return 0;
  /* If |n| <= 3, check if n = +- 1 */
  if (lgefint(n)==3 && (ulong)(n[2])<=3) return (n[2] != 1);

  if (!mod2(n)) return 0;
  init_MR_Jaeschke(&S, n); av2 = avma;
  for (i=1; i<=k; i++)
  {
    do r = umodui(pari_rand(), n); while (!r);
    if (DEBUGLEVEL > 4) err_printf("Miller-Rabin: testing base %ld\n", r);
    if (bad_for_base(&S, utoipos(r))) { avma = av; return 0; }
    avma = av2;
  }
  avma = av; return 1;
}

GEN
gispseudoprime(GEN x, long flag)
{ return flag? map_proto_lGL(millerrabin, x, flag): map_proto_lG(BPSW_psp,x); }

long
ispseudoprime(GEN x, long flag)
{ return flag? millerrabin(x, flag): BPSW_psp(x); }

/* As above for k bases taken in pr (i.e not random). We must have |n|>2 and
 * 1<=k<=11 (not checked) or k in {16,17} to select some special sets of bases.
 *
 * From Jaeschke, 'On strong pseudoprimes to several bases', Math.Comp. 61
 * (1993), 915--926  (see also http://www.utm.edu/research/primes/prove2.html),
 * we have:
 *
 * k == 4  (bases 2,3,5,7)  detects all composites
 *    n <     118 670 087 467 == 172243 * 688969  with the single exception of
 *    n ==      3 215 031 751 == 151 * 751 * 28351,
 *
 * k == 5  (bases 2,3,5,7,11)  detects all composites
 *    n <   2 152 302 898 747 == 6763 * 10627 * 29947,
 *
 * k == 6  (bases 2,3,...,13)  detects all composites
 *    n <   3 474 749 660 383 == 1303 * 16927 * 157543,
 *
 * k == 7  (bases 2,3,...,17)  detects all composites
 *    n < 341 550 071 728 321 == 10670053 * 32010157,
 * Even this limiting value is caught by an end mismatch between bases 5 and 17
 *
 * Moreover, the four bases chosen at
 *
 * k == 16  (2,13,23,1662803)  detects all composites up
 * to at least 10^12, and the combination at
 *
 * k == 17  (31,73)  detects most odd composites without prime factors > 100
 * in the range  n < 2^36  (with less than 250 exceptions, indeed with fewer
 * than 1400 exceptions up to 2^42). --GN */
int
Fl_MR_Jaeschke(ulong n, long k)
{
  const ulong pr[] =
    { 0, 2,3,5,7,11,13,17,19,23,29, 31,73, 2,13,23,1662803UL, };
  const ulong *p;
  ulong r;
  long i;
  Fl_MR_Jaeschke_t S;

  if (!(n & 1)) return 0;
  if (k == 16)
  { /* use smaller (faster) bases if possible */
    p = (n < 3215031751UL)? pr: pr+13;
    k = 4;
  }
  else if (k == 17)
  {
    p = (n < 1373653UL)? pr: pr+11;
    k = 2;
  }
  else p = pr; /* 2,3,5,... */
  Fl_init_MR_Jaeschke(&S, n);
  for (i=1; i<=k; i++)
  {
    r = p[i] % n; if (!r) break;
    if (Fl_bad_for_base(&S, r)) return 0;
  }
  return 1;
}

int
MR_Jaeschke(GEN n, long k)
{
  pari_sp av2, av = avma;
  const ulong pr[] =
    { 0, 2,3,5,7,11,13,17,19,23,29, 31,73, 2,13,23,1662803UL, };
  const ulong *p;
  long i;
  MR_Jaeschke_t S;

  if (lgefint(n) == 3) return Fl_MR_Jaeschke((ulong)n[2], k);

  if (!mod2(n)) return 0;
  if      (k == 16) { p = pr+13; k = 4; } /* 2,13,23,1662803 */
  else if (k == 17) { p = pr+11; k = 2; } /* 31,73 */
  else p = pr; /* 2,3,5,... */
  init_MR_Jaeschke(&S, n); av2 = avma;
  for (i=1; i<=k; i++)
  {
    if (bad_for_base(&S, utoipos(p[i]))) { avma = av; return 0; }
    avma = av2;
  }
  avma = av; return 1;
}

/*********************************************************************/
/**                                                                 **/
/**                      PSEUDO PRIMALITY (LUCAS)                   **/
/**                                                                 **/
/*********************************************************************/
/* compute n-th term of Lucas sequence modulo N.
 * v_{k+2} = P v_{k+1} - v_k, v_0 = 2, v_1 = P.
 * Assume n > 0 */
static GEN
LucasMod(GEN n, ulong P, GEN N)
{
  pari_sp av = avma, lim = stack_lim(av, 1);
  GEN nd = int_MSW(n);
  long i, m = *nd, j = 1+bfffo((ulong)m);
  GEN v = utoipos(P), v1 = utoipos(P*P - 2);

  m <<= j; j = BITS_IN_LONG - j;
  for (i=lgefint(n)-2;;) /* cf. leftright_pow */
  {
    for (; j; m<<=1,j--)
    { /* v = v_k, v1 = v_{k+1} */
      if (m < 0)
      { /* set v = v_{2k+1}, v1 = v_{2k+2} */
        v = subis(mulii(v,v1), (long)P);
        v1= subis(sqri(v1), 2);
      }
      else
      {/* set v = v_{2k}, v1 = v_{2k+1} */
        v1= subis(mulii(v,v1), (long)P);
        v = subis(sqri(v), 2);
      }
      v = modii(v, N);
      v1= modii(v1,N);
      if (low_stack(lim,stack_lim(av,1)))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"LucasMod");
        gerepileall(av, 2, &v,&v1);
      }
    }
    if (--i == 0) return v;
    j = BITS_IN_LONG;
    nd=int_precW(nd);
    m = *nd;
  }
}
/* compute n-th term of Lucas sequence modulo N.
 * v_{k+2} = P v_{k+1} - v_k, v_0 = 2, v_1 = P.
 * Assume n > 0 */
static ulong
u_LucasMod(ulong n, ulong P, ulong N)
{
  long j = 1 + bfffo(n);
  ulong v = P, v1 = P*P - 2, mP = N - P, m2 = N - 2, m = n << j;

  j = BITS_IN_LONG - j;
  for (; j; m<<=1,j--)
  { /* v = v_k, v1 = v_{k+1} */
    if (((long)m) < 0)
    { /* set v = v_{2k+1}, v1 = v_{2k+2} */
      v = Fl_add(Fl_mul(v,v1,N), mP, N);
      v1= Fl_add(Fl_mul(v1,v1,N),m2, N);
    }
    else
    {/* set v = v_{2k}, v1 = v_{2k+1} */
      v1= Fl_add(Fl_mul(v,v1,N),mP, N);
      v = Fl_add(Fl_mul(v,v,N), m2, N);
    }
  }
  return v;
}

static int
u_IsLucasPsP(ulong n)
{
  long i, v;
  ulong b, z, m2, m = n + 1;

  for (b=3, i=0;; b+=2, i++)
  {
    ulong c = b*b - 4; /* = 1 mod 4 */
    if (krouu(n % c, c) < 0) break;
    if (i == 64 && uissquareall(n, &c)) return 0; /* oo loop if N = m^2 */
  }
  if (!m) return 0; /* neither 2^32-1 nor 2^64-1 are Lucas-pp */
  v = vals(m); m >>= v;
  z = u_LucasMod(m, b, n);
  if (z == 2) return 1;
  m2 = n - 2;
  if (z == m2) return 1;
  for (i=1; i<v; i++)
  {
    if (!z) return 1;
    z = Fl_add(Fl_mul(z,z, n), m2, n);
    if (z == 2) return 0;
  }
  return 0;
}
/* check that N not a square first (taken care of here, but inefficient)
 * assume N > 3 */
static int
IsLucasPsP(GEN N)
{
  GEN N_2, m, z;
  long i, v;
  ulong b;

  for (b=3, i=0;; b+=2, i++)
  {
    ulong c = b*b - 4; /* = 1 mod 4 */
    if (i == 64 && Z_issquare(N)) return 0; /* avoid oo loop if N = m^2 */
    if (krouu(umodiu(N,c), c) < 0) break;
  }
  m = addis(N,1); v = vali(m); m = shifti(m,-v);
  z = LucasMod(m, b, N);
  if (equaliu(z, 2)) return 1;
  N_2 = subis(N,2);
  if (equalii(z, N_2)) return 1;
  for (i=1; i<v; i++)
  {
    if (!signe(z)) return 1;
    z = modii(subis(sqri(z), 2), N);
    if (equaliu(z, 2)) return 0;
  }
  return 0;
}

/* assume u odd, u > 1 */
static int
iu_coprime(GEN N, ulong u)
{
  const ulong n = umodiu(N, u);
  return (n == 1 || gcduodd(n, u) == 1);
}
/* assume u odd, u > 1 */
static int
uu_coprime(ulong n, ulong u)
{
  return gcduodd(n, u) == 1;
}

/* Fl_BPSW_psp */
int
uisprime(ulong n)
{
  Fl_MR_Jaeschke_t S;
  if (n < 103)
    switch(n)
    {
      case 2:
      case 3:
      case 5:
      case 7:
      case 11:
      case 13:
      case 17:
      case 19:
      case 23:
      case 29:
      case 31:
      case 37:
      case 41:
      case 43:
      case 47:
      case 53:
      case 59:
      case 61:
      case 67:
      case 71:
      case 73:
      case 79:
      case 83:
      case 89:
      case 97:
      case 101: return 1;
      default: return 0;
    }
  if (!(n & 1)) return 0;
#ifdef LONG_IS_64BIT
  /* 16294579238595022365 = 3*5*7*11*13*17*19*23*29*31*37*41*43*47*53
   *  7145393598349078859 = 59*61*67*71*73*79*83*89*97*101 */
  if (!uu_coprime(n, 16294579238595022365UL) ||
      !uu_coprime(n,  7145393598349078859UL)) return 0;
#else
  /* 4127218095 = 3*5*7*11*13*17*19*23*37
   * 3948078067 = 29*31*41*43*47*53
   * 4269855901 = 59*83*89*97*101
   * 1673450759 = 61*67*71*73*79 */
  if (!uu_coprime(n, 4127218095UL) ||
      !uu_coprime(n, 3948078067UL) ||
      !uu_coprime(n, 1673450759UL) ||
      !uu_coprime(n, 4269855901UL)) return 0;
#endif
  if (n < 10427) return 1;
  Fl_init_MR_Jaeschke(&S, n);
  if (Fl_bad_for_base(&S, 2)) return 0;
  if (n < 1016801) switch(n) {
  /* strong 2-pseudoprimes without prime divisors < 103. All have 2 prime
   * divisor, one of which is <= 661 */
    case 42799:
    case 49141:
    case 88357:
    case 90751:
    case 104653:
    case 130561:
    case 196093:
    case 220729:
    case 253241:
    case 256999:
    case 271951:
    case 280601:
    case 357761:
    case 390937:
    case 458989:
    case 486737:
    case 489997:
    case 514447:
    case 580337:
    case 741751:
    case 838861:
    case 873181:
    case 877099:
    case 916327:
    case 976873:
    case 983401: return 0;
    default: return 1;
  }
  return u_IsLucasPsP(n);
}

/* assume no prime divisor <= 661 */
int
uisprime_nosmalldiv(ulong n)
{
  Fl_MR_Jaeschke_t S;
  Fl_init_MR_Jaeschke(&S, n);
  if (Fl_bad_for_base(&S, 2)) return 0;
  return u_IsLucasPsP(n);
}

long
BPSW_psp(GEN N)
{
  pari_sp av;
  MR_Jaeschke_t S;
  int k;

  if (typ(N) != t_INT) pari_err_TYPE("BPSW_psp",N);
  if (signe(N) <= 0) return 0;
  if (lgefint(N) == 3) return uisprime((ulong)N[2]);
  if (!mod2(N)) return 0;
#ifdef LONG_IS_64BIT
  /* 16294579238595022365 = 3*5*7*11*13*17*19*23*29*31*37*41*43*47*53
   *  7145393598349078859 = 59*61*67*71*73*79*83*89*97*101 */
  if (!iu_coprime(N, 16294579238595022365UL) ||
      !iu_coprime(N,  7145393598349078859UL)) return 0;
#else
  /* 4127218095 = 3*5*7*11*13*17*19*23*37
   * 3948078067 = 29*31*41*43*47*53
   * 4269855901 = 59*83*89*97*101
   * 1673450759 = 61*67*71*73*79 */
  if (!iu_coprime(N, 4127218095UL) ||
      !iu_coprime(N, 3948078067UL) ||
      !iu_coprime(N, 1673450759UL) ||
      !iu_coprime(N, 4269855901UL)) return 0;
#endif
  /* no prime divisor < 103 */
  av = avma;
  init_MR_Jaeschke(&S, N);
  k = (!bad_for_base(&S, gen_2) && IsLucasPsP(N));
  avma = av; return k;
}

/* can we write n = x^k ? Assume N has no prime divisor <= 2^14.
 * Not memory clean */
long
isanypower_nosmalldiv(GEN N, GEN *px)
{
  GEN x = N, y;
  ulong mask = 7, ex0 = 11;
  long ex, k = 1;
  while (Z_issquareall(x, &y)) { k <<= 1; x = y; }
  while ( (ex = is_357_power(x, &y, &mask)) ) { k *= ex; x = y; }
  /* stop when x^(1/k) < 2^14 */
  while ( (ex = is_pth_power(x, &y, &ex0, 15)) ) { k *= ex; x = y; }
  *px = x; return k;
}

/* no prime divisor <= 2^14 (> 661) */
long
BPSW_psp_nosmalldiv(GEN N)
{
  pari_sp av;
  MR_Jaeschke_t S;
  long l = lgefint(N);
  int k;

  if (l == 3) return uisprime_nosmalldiv((ulong)N[2]);
  av = avma;
  /* N large: test for pure power, rarely succeeds, but requires < 1% of
   * compositeness test times */
  if (bit_accuracy(l) > 512 && isanypower_nosmalldiv(N, &N) != 1)
  {
    avma = av; return 0;
  }
  init_MR_Jaeschke(&S, N);
  k = (!bad_for_base(&S, gen_2) && IsLucasPsP(N));
  avma = av; return k;
}

/***********************************************************************/
/**                                                                   **/
/**                       Pocklington-Lehmer                          **/
/**                        P-1 primality test                         **/
/**                                                                   **/
/***********************************************************************/
/* Assume x BPSW pseudoprime. Check whether it's small enough to be certified
 * prime (< 2^64). Reference for strong 2-pseudoprimes:
 *   http://www.cecm.sfu.ca/Pseudoprimes/index-2-to-64.html */
static int
BPSW_isprime_small(GEN x)
{
  long l = lgefint(x);
#ifdef LONG_IS_64BIT
  return (l == 3);
#else
  return (l <= 4);
#endif
}

/* Brillhart, Lehmer, Selfridge test (Crandall & Pomerance, Th 4.1.5)
 * N^(1/3) <= f fully factored, f | N-1 */
static int
BLS_test(GEN N, GEN f)
{
  GEN c1, c2, r, q;
  if (cmpii(sqri(f), N) < 0) return 1; /* Pocklington case */
  q = dvmdii(N, f, &r);
  if (!is_pm1(r)) return 0;
  c2 = dvmdii(q, f, &c1);
  if (Z_issquare(subii(c2, shifti(c1,2)))) return 0;
  return 1;
}

/*assume n>=2*/
static ulong
pl831(GEN N, GEN p)
{
  pari_sp ltop = avma, av;
  ulong a;
  GEN Nmunp = diviiexact(addis(N,-1), p);
  av = avma;
  for(a = 2;; a++, avma = av)
  {
    GEN b = Fp_pow(utoipos(a), Nmunp, N);
    GEN c = Fp_pow(b,p,N), g = gcdii(addis(b,-1), N);
    if (!is_pm1(c)) return 0;
    if (is_pm1(g)) { avma=ltop; return a; }
    if (!equalii(g,N)) return 0;
  }
}
/* Assume N is a strong BPSW pseudoprime, Pocklington-Lehmer primality proof.
 *
 * flag 0: return gen_1 (prime), gen_0 (composite)
 * flag 1: return gen_0 (composite), gen_1 (small prime), matrix (large prime)
 *
 * The matrix has 3 columns, [a,b,c] with
 * a[i] prime factor of N-1,
 * b[i] witness for a[i] as in pl831
 * c[i] isprimePL(a[i]) */
static GEN
isprimePL(GEN N, long flag)
{
  pari_sp ltop = avma;
  long i, l, t = typ(N);
  int eps;
  GEN C, F = NULL;

  if (t == t_VEC)
  { /* [ N, [p1,...,pk] ], (p_i) list of pseudoprime divisors of N-1 */
    F = gel(N,2);
    N = gel(N,1); t = typ(N);
  }
  if (t != t_INT) pari_err_TYPE("isprimePL",N);
  eps = cmpis(N,2);
  if (eps<=0) return eps? gen_0: gen_1;

  if (DEBUGLEVEL>3)
    err_printf("Pocklington-Lehmer: proving primality of N = %Ps\n", N);
  N = absi(N);
  if (!F)
  {
    GEN cbrtN = gsqrtn(N, utoi(3), NULL, nbits2prec((expi(N)+2)/3));
    GEN N_1 = addis(N,-1), f;
    F = Z_factor_until(N_1, sqri(floorr(cbrtN)));
    f = factorback(F); F = gel(F,1);
    if (!equalii(f, N_1) && !BLS_test(N,f)) {
      if (DEBUGLEVEL>3)
        err_printf("Pocklington-Lehmer: N-1 not smooth enough --> Failure. Factored up to %Ps (%.3Ps%%)\n", f, divri(itor(f,LOWDEFAULTPREC), N));
      avma = ltop; return gen_0;
    }
    if (DEBUGLEVEL>3)
      err_printf("Pocklington-Lehmer: N-1 factored up to %Ps! (%.3Ps%%)\n", f, divri(itor(f,LOWDEFAULTPREC), N));
  }
  if (DEBUGLEVEL>3)
    err_printf("Pocklington-Lehmer: N-1 smooth enough! Computing certificate\n");
  C = cgetg(4,t_MAT); l = lg(F);
  gel(C,1) = cgetg(l,t_COL);
  gel(C,2) = cgetg(l,t_COL);
  gel(C,3) = cgetg(l,t_COL);
  for(i=1; i<l; i++)
  {
    GEN p = gel(F,i), r;
    ulong witness = pl831(N,p);

    if (!witness) { avma = ltop; return gen_0; }
    gmael(C,1,i) = icopy(p);
    gmael(C,2,i) = utoi(witness);
    if (DEBUGLEVEL>3)
      err_printf("Pocklington-Lehmer: recursively proving primality of p = %Ps\n", p);
    if (!flag) r = BPSW_isprime(p)? gen_1: gen_0;
    else
    {
      if (BPSW_isprime_small(p)) r = gen_1;
      else if (expi(p) > 250)   r = isprimeAPRCL(p)? gen_2: gen_0;
      else                      r = isprimePL(p,flag);
    }
    gmael(C,3,i) = r;
    if (r == gen_0) pari_err(e_MISC,"False prime number %Ps in isprimePL", p);
  }
  if (!flag) { avma = ltop; return gen_1; }
  return gerepileupto(ltop,C);
}
static long
isprimeSelfridge(GEN x) { return (isprimePL(x,0)==gen_1); }

/* assume x a BPSW pseudoprime */
long
BPSW_isprime(GEN N)
{
  pari_sp av = avma;
  long l, res;
  GEN fa, P, F, p, N_1;

  if (BPSW_isprime_small(N)) return 1;
  N_1 = subis(N,1); fa = Z_factor_limit(N_1, minss(1L<<19, maxprime()));
  l = lg(gel(fa,1))-1; p = gcoeff(fa,l,1);
  F = diviiexact(N_1,  powii(p, gcoeff(fa,l,2)));
  P = gel(fa,1);
  /* N-1 = F U, F factored, U possibly composite */
  if (cmpii(powiu(F, 3), N) >= 0) /* half-smooth, F >= N^(1/3) */
    res = BLS_test(N, F)
          && isprimeSelfridge(mkvec2(N,vecslice(P,1,l-1)));
  else if (BPSW_psp_nosmalldiv(p)) /* smooth */
    res = isprimeSelfridge(mkvec2(N,P));
  else
    res = isprimeAPRCL(N);
  avma = av; return res;
}

GEN
gisprime(GEN x, long flag)
{
  switch (flag)
  {
    case 0: return map_proto_lG(isprime,x);
    case 1: return map_proto_GL(isprimePL,x,1);
    case 2: return map_proto_lG(isprimeAPRCL,x);
  }
  pari_err_FLAG("gisprime");
  return NULL;
}

long
isprime(GEN x) { return BPSW_psp(x) && BPSW_isprime(x); }

/***********************************************************************/
/**                                                                   **/
/**                          PRIME NUMBERS                            **/
/**                                                                   **/
/***********************************************************************/

/* assume all primes up to 59359 are precomputed */
ulong
uprime(long n)
{
  byteptr p;
  ulong prime;

  if (n <= 0) pari_err(e_MISC, "n-th prime meaningless if n = %ld",n);
  if (n < 1000) {
    p = diffptr;
    prime = 0;
  } else if (n < 2000) {
    n -= 1000; p = diffptr+1000;
    prime = 7919;
  } else if (n < 3000) {
    n -= 2000; p = diffptr+2000;
    prime = 17389;
  } else if (n < 4000) {
    n -= 3000; p = diffptr+3000;
    prime = 27449;
  } else if (n < 5000) {
    n -= 4000; p = diffptr+4000;
    prime = 37813;
  } else if (n < 6000) {
    n -= 5000; p = diffptr+5000;
    prime = 48611;
  } else if (n < 10000 || maxprime() < 500000) {
    n -= 6000; p = diffptr+6000;
    prime = 59359;
  } else if (n < 20000) {
    n -= 10000; p = diffptr+10000;
    prime = 104729;
  } else if (n < 30000) {
    n -= 20000; p = diffptr+20000;
    prime = 224737;
  } else if (n < 40000) {
    n -= 30000; p = diffptr+30000;
    prime = 350377;
  } else {
    n -= 40000; p = diffptr+40000;
    prime = 479909;
  }
  while (n--) NEXT_PRIME_VIADIFF_CHECK(prime,p);
  return prime;
}
GEN
prime(long n) { return utoipos(uprime(n)); }

ulong
uprimepi(ulong n)
{
  byteptr p = diffptr+1;
  ulong prime = 2, res = 0;
  maxprime_check(n);
  while (prime < n) { res++; NEXT_PRIME_VIADIFF(prime,p); }
  return prime == n? res+1: res;
}

GEN
primepi(GEN x)
{
  pari_sp av = avma;
  GEN N = typ(x) == t_INT? x: gfloor(x);
  if (typ(N) != t_INT) pari_err_TYPE( "primepi",N);
  if (signe(N) <= 0) return gen_0;
  avma = av; return utoi(uprimepi(itou(N)));
}

GEN
primes(long m)
{
  byteptr p = diffptr;
  ulong prime = 0;
  long n = (m < 0)? 0: m;
  GEN y, z;

  z = y = cgetg(n+1,t_VEC);
  while (n--)
  {
    NEXT_PRIME_VIADIFF(prime,p);
    if (!*p) /* use something close to Dusart's bound */
      maxprime_check((ulong)(m*( log((double)m*log((double)m))-0.948 )));
    gel(++z, 0) = utoipos(prime);
  }
  return y;
}
GEN
primes_zv(long m)
{
  byteptr p = diffptr;
  ulong prime = 0;
  long n = (m < 0)? 0: m;
  GEN y, z;

  z = y = cgetg(n+1,t_VECSMALL);
  while (n--)
  {
    NEXT_PRIME_VIADIFF(prime,p);
    if (!*p) /* use something close to Dusart's bound */
      maxprime_check((ulong)(m*( log((double)m*log((double)m))-0.948 )));
    *++z = prime;
  }
  return y;
}

/***********************************************************************/
/**                                                                   **/
/**                       PRIVATE PRIME TABLE                         **/
/**                                                                   **/
/***********************************************************************/
/* delete dummy NULL entries */
static void
cleanprimetab(GEN T)
{
  long i,j, l = lg(T);
  for (i = j = 1; i < l; i++)
    if (T[i]) T[j++] = T[i];
  setlg(T,j);
}
/* remove p from T */
static void
rmprime(GEN T, GEN p)
{
  long i;
  if (typ(p) != t_INT) pari_err_TYPE("rmprime",p);
  i = ZV_search(T, p);
  if (!i) pari_err(e_MISC,"prime %Ps is not in primetable", p);
  gunclone(gel(T,i)); gel(T,i) = NULL;
  cleanprimetab(T);
}

/*stolen from ZV_union_shallow() : clone entries from y */
static GEN
addp_union(GEN x, GEN y)
{
  long i, j, k, lx = lg(x), ly = lg(y);
  GEN z = cgetg(lx + ly - 1, t_VEC);
  i = j = k = 1;
  while (i<lx && j<ly)
  {
    int s = cmpii(gel(x,i), gel(y,j));
    if (s < 0)
      gel(z,k++) = gel(x,i++);
    else if (s > 0)
      gel(z,k++) = gclone(gel(y,j++));
    else {
      gel(z,k++) = gel(x,i++);
      j++;
    }
  }
  while (i<lx) gel(z,k++) = gel(x,i++);
  while (j<ly) gel(z,k++) = gclone(gel(y,j++));
  setlg(z, k); return z;
}

/* p is NULL, or a single element or a row vector with "primes" to add to
 * prime table. */
static GEN
addp(GEN *T, GEN p)
{
  pari_sp av = avma;
  long i, l;
  GEN v;

  if (!p || lg(p) == 1) return *T;
  if (!is_vec_t(typ(p))) p = mkvec(p);

  RgV_check_ZV(p, "addprimes");
  v = gen_indexsort_uniq(p, (void*)&cmpii, &cmp_nodata);
  p = vecpermute(p, v);
  if (cmpii(gel(p,1), gen_1) <= 0)
    pari_err(e_MISC,"entries must be > 1 in addprimes");
  p = addp_union(*T, p);
  l = lg(p);
  if (l != lg(*T))
  {
    GEN old = *T, t = cgetalloc(t_VEC, l);
    for (i = 1; i < l; i++) gel(t,i) = gel(p,i);
    *T = t; free(old);
  }
  avma = av; return *T;
}
GEN
addprimes(GEN p) { return addp(&primetab, p); }

static GEN
rmprimes(GEN T, GEN prime)
{
  long i,tx;

  if (!prime) return T;
  tx = typ(prime);
  if (is_vec_t(tx))
  {
    if (prime == T)
    {
      for (i=1; i < lg(prime); i++) gunclone(gel(prime,i));
      setlg(prime, 1);
    }
    else
    {
      for (i=1; i < lg(prime); i++) rmprime(T, gel(prime,i));
    }
    return T;
  }
  rmprime(T, prime); return T;
}
GEN
removeprimes(GEN prime) { return rmprimes(primetab, prime); }
