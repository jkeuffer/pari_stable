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
/********************************************************************/
/**                                                                **/
/**              INSERT PERMANENT OBJECT IN STRUCTURE              **/
/**                                                                **/
/********************************************************************/
static const long OBJMAX = 2; /* maximum number of insertable objects */

/* insert O in S [last position] */
static void
obj_insert(GEN S, GEN O, long K)
{
  long l = lg(S)-1;
  GEN v = gel(S,l);
  if (typ(v) != t_VEC)
  {
    GEN w = zerovec(OBJMAX); gel(w,K) = O;
    gel(S,l) = gclone(w);
  }
  else
    gel(v,K) = gclone(O);
}

static GEN
get_extra_obj(GEN S, long K)
{
  GEN v = gel(S,lg(S)-1);
  if (typ(v) == t_VEC)
  {
    GEN O = gel(v,K);
    if (typ(O) != t_INT || signe(O)) return O;
  }
  return NULL;
}

GEN
check_and_build_obj(GEN S, long tag, GEN (*build)(GEN))
{
  GEN O = get_extra_obj(S, tag);
  if (!O)
  {
    pari_sp av = avma;
    obj_insert(S, build(S), tag); avma = av;
    O = get_extra_obj(S, tag);
  }
  return O;
}
/*******************************************************************/
/*                                                                 */
/*         CLASS GROUP AND REGULATOR (McCURLEY, BUCHMANN)          */
/*                    GENERAL NUMBER FIELDS                        */
/*                                                                 */
/*******************************************************************/
static const long SFB_MAX = 3;
static const long RANDOM_BITS = 4;
static const long MAXRELSUP = 50;

typedef struct FACT {
    long pr, ex;
} FACT;

/* a factor base contains only non-inert primes
 * KC = # of P in factor base (p <= n, NP <= n2)
 * KC2= # of P assumed to generate class group (NP <= n2)
 *
 * KCZ = # of rational primes under ideals counted by KC
 * KCZ2= same for KC2 */

typedef struct powFB_t {
  GEN id2; /* id2[1] = P */
  GEN alg; /* alg[1] = 1, (id2[i],alg[i]) = red( id2[i-1] * P ) */
  GEN ord; /* ord[i] = known exponent of P in Cl(K) */
  GEN arc; /* arc[i] = multiplicative arch component of x
	      such that id2[i] = x P^(i-1) */
  struct powFB_t *prev; /* previously used powFB */
} powFB_t;

typedef struct FB_t {
  GEN FB; /* FB[i] = i-th rational prime used in factor base */
  GEN LP; /* vector of all prime ideals in FB */
  GEN *LV; /* LV[p] = vector of P|p, NP <= n2
	    * isclone() is set for LV[p] iff all P|p are in FB
	    * LV[i], i not prime or i > n2, is undefined! */
  GEN iLP; /* iLP[p] = i such that LV[p] = [LP[i],...] */
  long KC, KCZ, KCZ2;
  GEN subFB; /* LP o subFB =  part of FB used to build random relations */
  int sfb_chg; /* need to change subFB ? */
  int newpow; /* need to compute powFB */
  powFB_t *pow;/* array of [P^0,...,P^{k_P}], P in LP o subFB */
  GEN perm; /* permutation of LP used to represent relations [updated by
	       hnfspec/hnfadd: dense rows come first] */
  GEN vecG, G0;
} FB_t;

enum { sfb_UNSUITABLE = -1, sfb_CHANGE = 1, sfb_INCREASE = 2 };

typedef struct REL_t {
  GEN R; /* relation vector as t_VECSMALL */
  long nz; /* index of first non-zero elt in R (hash) */
  GEN m; /* pseudo-minimum yielding the relation */
  GEN ex; /* exponents of subFB elts used to find R */
  powFB_t *pow; /* powsubFB associated to ex [ shared between rels ] */
} REL_t;

typedef struct RELCACHE_t {
  REL_t *chk; /* last checkpoint */
  REL_t *base; /* first rel found */
  REL_t *last; /* last rel found so far */
  REL_t *end; /* target for last relation. base <= last <= end */
  size_t len; /* number of rels pre-allocated in base */
} RELCACHE_t;

static void
delete_cache(RELCACHE_t *M)
{
  REL_t *rel;
  for (rel = M->base+1; rel <= M->last; rel++)
  {
    pari_free((void*)rel->R);
    if (!rel->m) continue;
    gunclone(rel->m);
    if (!rel->ex) continue;
    gunclone(rel->ex);
  }
  pari_free((void*)M->base); M->base = NULL;
}

static void
delete_FB(FB_t *F)
{
  powFB_t *S = F->pow;
  while (S)
  {
    powFB_t *T = S;
    gunclone(S->id2);
    gunclone(S->alg);
    gunclone(S->ord);
    if (S->arc) gunclone(S->arc);
    S = S->prev; pari_free((void*)T);
  }
  gunclone(F->subFB);
}

INLINE GEN
col_0(long n)
{
   GEN c = (GEN)calloc(n + 1, sizeof(long));
   if (!c) pari_err(memer);
   c[0] = evaltyp(t_VECSMALL) | evallg(n + 1);
   return c;
}

static void
reallocate(RELCACHE_t *M, long len)
{
  REL_t *old = M->base;
  M->len = len;
  M->base = (REL_t*)pari_realloc((void*)old, (len+1) * sizeof(REL_t));
  if (old)
  {
    size_t last = M->last - old, chk = M->chk - old, end = M->end - old;
    M->last = M->base + last;
    M->chk  = M->base + chk;
    M->end  = M->base + end;
  }
}

#define pr_get_smallp(pr) gel(pr,1)[2]

/* don't take P|p if P ramified, or all other Q|p already there */
static int
ok_subFB(FB_t *F, long t, GEN D)
{
  GEN LP, P = gel(F->LP,t);
  long p = pr_get_smallp(P);
  LP = F->LV[p];
  return (!isclone(LP) || t != F->iLP[p] + lg(LP)-1);
}

/* set subFB, reset F->pow
 * Fill F->perm (if != NULL): primes ideals sorted by increasing norm (except
 * the ones in subFB come first [dense rows for hnfspec]) */
static int
subFBgen(FB_t *F, GEN nf, double PROD, long minsFB)
{
  GEN y, perm, yes, no, D = gel(nf,3);
  long i, j, k, iyes, ino, lv = F->KC + 1;
  double prod;
  pari_sp av;

  F->LP   = cgetg(lv, t_VEC);
  F->perm = cgetg(lv, t_VECSMALL);
  av = avma;
  y = cgetg(lv,t_COL); /* Norm P */
  for (k=0, i=1; i <= F->KCZ; i++)
  {
    GEN LP = F->LV[F->FB[i]];
    long l = lg(LP);
    for (j = 1; j < l; j++)
    {
      GEN P = gel(LP,j);
      k++;
      gel(y,k) = pr_norm(P);
      gel(F->LP,k) = P;
    }
  }
  /* perm sorts LP by increasing norm */
  perm = indexsort(y);
  no  = cgetg(lv, t_VECSMALL); ino  = 1;
  yes = cgetg(lv, t_VECSMALL); iyes = 1;
  prod = 1.0;
  for (i = 1; i < lv; i++)
  {
    long t = perm[i];
    if (!ok_subFB(F, t, D)) { no[ino++] = t; continue; }

    yes[iyes++] = t;
    prod *= (double)itos(gel(y,t));
    if (iyes > minsFB && prod > PROD) break;
  }
  if (i == lv) return 0;
  setlg(yes, iyes);
  for (j=1; j<iyes; j++)     F->perm[j] = yes[j];
  for (i=1; i<ino; i++, j++) F->perm[j] =  no[i];
  for (   ; j<lv; j++)       F->perm[j] =  perm[j];
  F->subFB = gclone(yes);
  F->newpow = 1;
  F->pow = NULL;
  if (DEBUGLEVEL)
    msgtimer("sub factorbase (%ld elements)",lg(F->subFB)-1);
  avma = av; return 1;
}
static int
subFB_change(FB_t *F, GEN nf, GEN L_jid)
{
  GEN yes, D = gel(nf,3);
  long i, iyes, minsFB, chg = F->sfb_chg, lv = F->KC + 1, l = lg(F->subFB)-1;
  pari_sp av = avma;

  switch (chg)
  {
    case sfb_INCREASE: minsFB = l + 1; break;
    default: minsFB = l; break;
  }

  if (DEBUGLEVEL) fprintferr("*** Changing sub factor base\n");
  yes = cgetg(minsFB+1, t_VECSMALL); iyes = 1;
  if (L_jid)
  {
    for (i = 1; i < lg(L_jid); i++)
    {
      long t = L_jid[i];
      if (!ok_subFB(F, t, D)) continue;

      yes[iyes++] = t;
      if (iyes > minsFB) break;
    }
  }
  else i = 1;
  if (iyes <= minsFB)
  {
    for ( ; i < lv; i++)
    {
      long t = F->perm[i];
      if (!ok_subFB(F, t, D)) continue;

      yes[iyes++] = t;
      if (iyes > minsFB) break;
    }
    if (i == lv) return 0;
  }
  if (zv_equal(F->subFB, yes))
  {
    if (chg != sfb_UNSUITABLE) F->sfb_chg = 0;
  }
  else
  {
    gunclone(F->subFB);
    F->subFB = gclone(yes);
    F->sfb_chg = 0;
  }
  F->newpow = 1; avma = av; return 1;
}

static GEN
init_famat(GEN x) { return mkvec2(x, cgetg(1,t_MAT)); }

static GEN
red(GEN nf, GEN I, GEN G0, GEN *pm)
{
  GEN m, y;
  y = idealred0(nf, init_famat(I), G0);
  m = gel(y,2);
  y = gel(y,1); *pm = lg(m)==1? gen_1: gmael(m, 1, 1);
  return is_pm1(gcoeff(y,1,1))? NULL: idealtwoelt(nf,y);
}

/* make sure enough room to store n more relations */
static void
pre_allocate(RELCACHE_t *cache, size_t n)
{
  size_t len = (cache->last - cache->base) + n;
  if (len >= cache->len) reallocate(cache, len << 1);
}
/* x,y are or the form [Z, ZV]. Are they equal ? */
static int
ZZV_equal(GEN x, GEN y) {
  return equalii(gel(x,1),gel(y,1)) && ZV_equal(gel(x,2), gel(y,2));
}

/* Compute powers of prime ideals (P^0,...,P^a) in subFB (a > 1) */
static void
powFBgen(FB_t *F, RELCACHE_t *cache, GEN nf)
{
  const long a = 1<<RANDOM_BITS;
  pari_sp av = avma;
  long i, j, c = 1, n = lg(F->subFB);
  GEN Id2, Alg, Ord;
  powFB_t *old = F->pow, *New;

  if (DEBUGLEVEL) fprintferr("Computing powers for subFB: %Ps\n",F->subFB);
  F->pow = New = (powFB_t*) pari_malloc(sizeof(powFB_t));
  Id2 = cgetg(n, t_VEC);
  Alg = cgetg(n, t_VEC);
  Ord = cgetg(n, t_VECSMALL);
  New->arc = NULL;
  if (cache) pre_allocate(cache, n);
  for (i=1; i<n; i++)
  {
    GEN M, m, alg, id2, vp = gel(F->LP, F->subFB[i]);
    id2 = cgetg(a+1,t_VEC); gel(Id2,i) = id2;
    gel(id2,1) = mkvec2(pr_get_p(vp), pr_get_gen(vp));
    alg = cgetg(a+1,t_VEC); gel(Alg,i) = alg; gel(alg,1) = gen_1;
    vp = idealhnf_two(nf,vp);
    for (j=2; j<=a; j++)
    {
      GEN J = red(nf, idealmul_HNF(nf,vp,gel(id2,j-1)), F->G0, &m);
      if (DEBUGLEVEL>1) fprintferr(" %ld",j);
      if (!J)
      {
	if (j == 2 && !red(nf, vp, F->G0, &M)) { j = 1; m = M; }
	break;
      }
      if (ZZV_equal(J, gel(id2,j-1))) { j = 1; break; }
      gel(id2,j) = J;
      gel(alg,j) = m;
    }
    if (cache && j <= a)
    { /* vp^j principal */
      long k;
      REL_t *rel = cache->last + 1;
      rel->R = col_0(F->KC); rel->nz = F->subFB[i];
      rel->R[ rel->nz ] = j;
      for (k = 2; k < j; k++) m = nfmul(nf, m, gel(alg,k));
      rel->m = gclone(m);
      rel->ex = NULL;
      rel->pow = New;
      cache->last = rel;
    }
    /* trouble with subFB: include ideal even though it's principal */
    if (j == 1 && F->sfb_chg == sfb_UNSUITABLE) j = 2;
    setlg(id2, j);
    setlg(alg, j); Ord[i] = j; if (c < 64) c *= j;
    if (DEBUGLEVEL>1) fprintferr("\n");
  }
  New->prev = old;
  New->id2 = gclone(Id2);
  New->ord = gclone(Ord);
  New->alg = gclone(Alg); avma = av;
  if (DEBUGLEVEL) msgtimer("powFBgen");
  /* if c too small we'd better change the subFB soon */
  F->sfb_chg = (c < 6)? sfb_UNSUITABLE: 0;
  F->newpow = 0;
}

static GEN
countf(GEN LP)
{
  long i, l = lg(LP);
  GEN Pmaxf = gel(LP, l-1);
  GEN nbf = const_vecsmall(itou(gel(Pmaxf,4)), 0);

  for (i = 1; i < l; i++)
  {
    GEN P = gel(LP,i);
    ulong f = itou(gel(P,4));
    nbf[f]++;
  }
  return nbf;
}

void
init_GRHcheck(GRHcheck_t *S, long N, long R1, double LOGD)
{
  const double c1 = PI*PI/2;
  const double c2 = 3.663862376709;
  const double c3 = 3.801387092431; /* Euler + log(8*Pi)*/
  S->cN = R1*c2 + N*c1;
  S->cD = LOGD - N*c3 - R1*PI/2;
}

int
GRHok(GRHcheck_t *S, double L, double SA, double SB)
{
  if (!S || S->cD + (S->cN + 2*SB) / L - 2*SA < -1e-8) return 1;
  if (DEBUGLEVEL) fprintferr("*** GRH check negative! ***\n");
  return 0;
}

/* Compute FB, LV, iLP + KC*. Reset perm
 * n2: bound for norm of tested prime ideals (includes be_honest())
 * n : bound for p, such that P|p (NP <= n2) used to build relations

 * Return prod_{p<=n2} (1-1/p) / prod_{Norm(P)<=n2} (1-1/Norm(P)),
 * close to residue of zeta_K at 1 = 2^r1 (2pi)^r2 h R / (w D) */
static GEN
FBgen(FB_t *F, GEN nf, long N, long C2, long C1, GRHcheck_t *S)
{
  byteptr delta = diffptr;
  long i, p, ip;
  GEN prim, Res;
  double L = log((double)C2), SA = 0, SB = 0;

  maxprime_check((ulong)C2);
  F->sfb_chg = 0;
  F->FB  = cgetg(C2+1, t_VECSMALL);
  F->iLP = cgetg(C2+1, t_VECSMALL);
  F->LV = (GEN*)new_chunk(C2+1);

  Res = real_1(DEFAULTPREC);
  prim = icopy(gen_1);
  i = ip = 0;
  F->KC = F->KCZ = 0;
  for (p = 0;;) /* p <= C2 */
  {
    pari_sp av = avma, av1;
    long f, k, l, m;
    GEN LP, a, b, nbf;

    NEXT_PRIME_VIADIFF(p, delta);
    if (!F->KC && p > C1) { F->KCZ = i; F->KC = ip; }
    if (p > C2) break;

    if (DEBUGLEVEL>1) { fprintferr(" %ld",p); flusherr(); }
    prim[2] = p; LP = idealprimedec(nf,prim);

    av1 = avma; a = b = NULL;
    nbf = countf(LP); l = lg(nbf); k = 0;
    /* a/b := (p-1)/p * prod_{LP|p, NP <= C2} NP / (NP-1) */
    a = utoi(p-1); b = prim;
    for (f=1; f<l; f++)
    {
      long nor, nb = nbf[f];

      if (!nb) continue;
      if (f == 1) nor = p;
      else
      {
	nor = itos_or_0(powiu(prim, f));
	if (!nor || nor > C2) break;
      }
      k += nb;
      a = mulii(a, powuu(nor,   nb));
      b = mulii(b, powuu(nor-1, nb));
      if (S)
      {
	double logp = log((double)p);
	double logNP = f*logp, q = 1/sqrt((double)nor);
	double A = logNP * q, B = logNP * A;
	long M = (long)(L/logNP);
	if (M > 1)
	{
	  double inv1_q = 1 / (1-q);
	  A *= (1 - pow(q, M)) * inv1_q;
	  B *= (1 - pow(q, M)*(M+1 - M*q)) * inv1_q * inv1_q;
	}
	SA += nb * A;
	SB += nb * B;
      }
    }
    a = a? divri(mulir(a,Res),b): divru(mulsr(p-1,Res),p);
    affrr(a, Res);
    avma = av1;
    if (l == N+1) continue; /* p inert */

    /* keep non-inert ideals with Norm <= C2 */
    for (m = 1; m <= k; m++)
    {
      GEN t = gel(LP,m);
      gel(t,5) = zk_scalar_or_multable(nf, gel(t,5));
    }
    if (f == l)
      setisclone(LP); /* flag it: all prime divisors in FB */
    else
      { setlg(LP,k+1); LP = gerepilecopy(av,LP); }
    F->FB[++i]= p;
    F->LV[p]  = LP;
    F->iLP[p] = ip; ip += k;
  }
  if (! F->KC) return NULL;
  setlg(F->FB, F->KCZ+1); F->KCZ2 = i;
  if (DEBUGLEVEL)
  {
    if (DEBUGLEVEL>1) fprintferr("\n");
    if (DEBUGLEVEL>6)
    {
      fprintferr("########## FACTORBASE ##########\n\n");
      fprintferr("KC2=%ld, KC=%ld, KCZ=%ld, KCZ2=%ld\n",
		  ip, F->KC, F->KCZ, F->KCZ2);
      for (i=1; i<=F->KCZ; i++) fprintferr("++ LV[%ld] = %Ps",i,F->LV[F->FB[i]]);
    }
    msgtimer("factor base");
  }
  if (!GRHok(S, L, SA, SB)) return NULL;
  F->perm = NULL; return Res;
}

/*  SMOOTH IDEALS */
static void
store(long i, long e, FACT *fact)
{
  ++fact[0].pr;
  fact[fact[0].pr].pr = i; /* index */
  fact[fact[0].pr].ex = e; /* exponent */
}

/* divide out x by all P|p, where x as in can_factor().  k = v_p(Nx) */
static int
divide_p_elt(FB_t *F, long p, long k, GEN nf, GEN m, FACT *fact)
{
  GEN P, LP = F->LV[p];
  long j, v, l = lg(LP), ip = F->iLP[p];
  for (j=1; j<l; j++)
  {
    P = gel(LP,j);
    v = int_elt_val(nf, m, pr_get_p(P), gel(P,5), NULL); /* v_P(m) */
    if (!v) continue;
    store(ip + j, v, fact); /* v = v_P(m) > 0 */
    k -= v * itos(gel(P,4));
    if (!k) return 1;
  }
  return 0;
}
static int
divide_p_id(FB_t *F, long p, long k, GEN nf, GEN I, FACT *fact)
{
  GEN P, LP = F->LV[p];
  long j, v, l = lg(LP), ip = F->iLP[p];
  for (j=1; j<l; j++)
  {
    P = gel(LP,j);
    v = idealval(nf,I, P);
    if (!v) continue;
    store(ip + j, v, fact); /* v = v_P(I) > 0 */
    k -= v * itos(gel(P,4));
    if (!k) return 1;
  }
  return 0;
}
static int
divide_p_quo(FB_t *F, long p, long k, GEN nf, GEN I, GEN m, FACT *fact)
{
  GEN P, LP = F->LV[p];
  long j, v, l = lg(LP), ip = F->iLP[p];
  for (j=1; j<l; j++)
  {
    P = gel(LP,j);
    v = int_elt_val(nf, m, pr_get_p(P), gel(P,5), NULL); /* v_P(m) */
    if (!v) continue;
    v -= idealval(nf,I, P);
    if (!v) continue;
    store(ip + j, v, fact); /* v = v_P(m / I) > 0 */
    k -= v * itos(gel(P,4));
    if (!k) return 1;
  }
  return 0;
}

/* is *N > 0 a smooth rational integer wrt F ? (put the exponents in *ex) */
static int
smooth_int(FB_t *F, GEN *N, GEN *ex)
{
  GEN FB = F->FB;
  const long KCZ = F->KCZ;
  const ulong limp = (ulong)FB[KCZ]; /* last p in FB */
  long i;

  *ex = new_chunk(KCZ+1);
  for (i=1; ; i++)
  {
    int stop;
    (*ex)[i] = Z_lvalrem_stop(*N, (ulong)FB[i], &stop);
    if (stop) break;
    if (i == KCZ) return 0;
  }
  (*ex)[0] = i;
  return (cmpiu(*N,limp) <= 0);
}

static int
divide_p(FB_t *F, long p, long k, GEN nf, GEN I, GEN m, FACT *fact)
{
  if (!m) return divide_p_id (F,p,k,nf,I,fact);
  if (!I) return divide_p_elt(F,p,k,nf,m,fact);
  return divide_p_quo(F,p,k,nf,I,m,fact);
}

/* Let x = m if I == NULL,
 *         I if m == NULL,
 *         m/I otherwise.
 * Can we factor the integral ideal x ? N = Norm x > 0 [DESTROYED] */
static long
can_factor(FB_t *F, GEN nf, GEN I, GEN m, GEN N, FACT *fact)
{
  GEN ex;
  long i;
  fact[0].pr = 0;
  if (is_pm1(N)) return 1;
  if (!smooth_int(F, &N, &ex)) return 0;
  for (i=1; i<=ex[0]; i++)
    if (ex[i] && !divide_p(F, F->FB[i], ex[i], nf, I, m, fact)) return 0;
  return is_pm1(N) || divide_p(F, itos(N), 1, nf, I, m, fact);
}

/* can we factor m/I ? [m in I from pseudomin], NI = norm I */
static long
factorgen(FB_t *F, GEN nf, GEN I, GEN NI, GEN m, FACT *fact)
{
  GEN T = gel(nf,1);
  GEN Nm = absi( ZX_QX_resultant(T, coltoliftalg(nf,m)) ); /* |Nm| */
  GEN N  = diviiexact(Nm, NI); /* N(m / I) */
  return can_factor(F, nf, I, m, N, fact);
}

/*  FUNDAMENTAL UNITS */

/* a, m real. Return  (Re(x) + a) + I * (Im(x) % m) */
static GEN
addRe_modIm(GEN x, GEN a, GEN m)
{
  GEN re, im, z;
  if (typ(x) == t_COMPLEX)
  {
    im = modr_safe(gel(x,2), m);
    if (!im) return NULL;
    re = gadd(gel(x,1), a);
    z = gcmp0(im)? re: mkcomplex(re, im);
  }
  else
    z = gadd(x, a);
  return z;
}

/* clean archimedean components */
static GEN
cleanarch(GEN x, long N, long prec)
{
  long i, R1, RU, tx = typ(x);
  GEN s, y, pi2;

  if (tx == t_MAT)
  {
    y = cgetg(lg(x), tx);
    for (i=1; i < lg(x); i++) {
      gel(y,i) = cleanarch(gel(x,i), N, prec);
      if (!gel(y,i)) return NULL;
    }
    return y;
  }
  if (!is_vec_t(tx)) pari_err(talker,"not a vector/matrix in cleanarch");
  RU = lg(x)-1; R1 = (RU<<1)-N;
  s = gdivgs(RgV_sum(real_i(x)), -N); /* -log |norm(x)| / N */
  y = cgetg(RU+1,tx);
  pi2 = Pi2n(1, prec);
  for (i=1; i<=R1; i++) {
    gel(y,i) = addRe_modIm(gel(x,i), s, pi2);
    if (!gel(y,i)) return NULL;
  }
  if (i <= RU)
  {
    GEN pi4 = Pi2n(2, prec), s2 = gmul2n(s, 1);
    for (   ; i<=RU; i++) {
      gel(y,i) = addRe_modIm(gel(x,i), s2, pi4);
      if (!gel(y,i)) return NULL;
    }
  }
  return y;
}

static GEN
not_given(long force, long reason)
{
  switch(reason)
  {
    case fupb_LARGE:
      pari_warn(warner,"fundamental units too large, not given");
      break;
    case fupb_PRECI:
      if (!force)
        pari_warn(warner,"insufficient precision for fundamental units, not given");
      break;
  }
  return cgetg(1,t_MAT);
}

/* check whether exp(x) will get too big */
static long
expgexpo(GEN x)
{
  long i,j,e, E = - (long)HIGHEXPOBIT;
  GEN p1;

  for (i=1; i<lg(x); i++)
    for (j=1; j<lg(x[1]); j++)
    {
      p1 = gmael(x,i,j);
      if (typ(p1)==t_COMPLEX) p1 = gel(p1,1);
      e = gexpo(p1); if (e>E) E=e;
    }
  return E;
}

static GEN
getfu(GEN nf, GEN *ptA, long force, long *pte, long prec)
{
  GEN p1, p2, u, y, matep, A, vec, T = gel(nf,1), M = gmael(nf,5,1);
  long e, i, j, R1, RU, N = degpol(T);

  if (DEBUGLEVEL) fprintferr("\n#### Computing fundamental units\n");
  R1 = nf_get_r1(nf); RU = (N+R1)>>1;
  if (RU==1) { *pte=LONG_MAX; return cgetg(1,t_VEC); }

  *pte = 0; A = *ptA;
  matep = cgetg(RU,t_MAT);
  for (j=1; j<RU; j++)
  {
    GEN c = cgetg(RU+1,t_COL), Aj = gel(A,j);
    GEN s = gdivgs(RgV_sum(real_i(Aj)), -N); /* -log |norm(Aj)| / N */
    gel(matep,j) = c;
    for (i=1; i<=R1; i++) gel(c,i) = gadd(s, gel(Aj,i));
    for (   ; i<=RU; i++) gel(c,i) = gadd(s, gmul2n(gel(Aj,i),-1));
  }
  u = lll(real_i(matep));
  if (typ(u) != t_MAT) return not_given(force, fupb_PRECI);

  y = RgM_mul(matep,u);
  if (expgexpo(y) > 20) {
    if (force) pari_err(talker, "bnfinit: fundamental units too large");
    *pte = LONG_MAX; return not_given(force, fupb_LARGE);
  }

  if (prec <= 0) prec = gprecision(A);
  y = RgM_solve_realimag(M, gexp(y,prec));
  if (!y) return not_given(force, fupb_PRECI);
  y = grndtoi(y, &e);
  *pte = -e;
  if (e >= 0) return not_given(force, fupb_PRECI);
  for (j=1; j<RU; j++)
    if (!gcmp1(idealnorm(nf, gel(y,j)))) break;
  if (j < RU) { *pte = 0; return not_given(force, fupb_PRECI); }
  A = RgM_mul(A,u);

  /* y[i] are unit generators. Normalize: smallest L2 norm + lead coeff > 0 */
  y = coltoliftalg(nf, y);
  vec = cgetg(RU+1,t_COL);
  p1 = PiI2n(0,prec); for (i=1; i<=R1; i++) gel(vec,i) = p1;
  p2 = PiI2n(1,prec); for (   ; i<=RU; i++) gel(vec,i) = p2;
  for (j=1; j<RU; j++)
  {
    p1 = gel(y,j); p2 = QXQ_inv(p1, T);
    if (gcmp(QuickNormL2(p2,DEFAULTPREC),
	     QuickNormL2(p1,DEFAULTPREC)) < 0)
    {
      gel(A,j) = gneg(gel(A,j));
      p1 = p2;
    }
    if (gsigne(leading_term(p1)) < 0)
    {
      gel(A,j) = gadd(gel(A,j), vec);
      p1 = gneg(p1);
    }
    gel(y,j) = p1;
  }
  if (DEBUGLEVEL) msgtimer("getfu");
  *ptA = A; return y;
}

GEN
init_units(GEN BNF)
{
  GEN bnf = checkbnf(BNF), res = gel(bnf,8), v, funits;
  long i, l;
  if (lg(res) == 5)
  {
    pari_sp av = avma;
    GEN nf = gel(bnf,7), A = gel(bnf,3);
    if (lg(res)==6 && lg(res[5])==lg(nf[6])-1) return gcopy(gel(res,5));
    funits = gerepilecopy(av, getfu(nf, &A, nf_FORCE, &l, 0));
  } 
  else
  {
    if (lg(res) != 6) pari_err(talker,"incorrect big number field");
    funits = gel(res,5);
  }
  l = lg(funits) + 1;
  v = cgetg(l, t_VEC); gel(v,1) = gmael(res, 4, 2);
  for (i = 2; i < l; i++) v[i] = funits[i-1];
  return v;
}

/*******************************************************************/
/*                                                                 */
/*           PRINCIPAL IDEAL ALGORITHM (DISCRETE LOG)              */
/*                                                                 */
/*******************************************************************/

/* G: prime ideals, E: vector of non-negative exponents.
 * C = possible extra prime (^1) or NULL
 * Return Norm (product) */
static GEN
get_norm_fact_primes(GEN G, GEN E, GEN C)
{
  GEN N = gen_1, P, p;
  long i, c = lg(E);
  for (i=1; i<c; i++)
  {
    GEN ex = gel(E,i);
    long s = signe(ex);
    if (!s) continue;

    P = gel(G,i); p = pr_get_p(P);
    N = mulii(N, powgi(p, mulii(gel(P,4), ex)));
  }
  if (C) N = mulii(N, pr_norm(C));
  return N;
}

/* gen: HNF ideals */
static GEN
get_norm_fact(GEN gen, GEN ex, GEN *pd)
{
  long i, c = lg(ex);
  GEN d,N,I,e,n,ne,de;
  d = N = gen_1;
  for (i=1; i<c; i++)
    if (signe(ex[i]))
    {
      I = gel(gen,i); e = gel(ex,i); n = ZM_det_triangular(I);
      ne = powgi(n,e);
      de = equalii(n, gcoeff(I,1,1))? ne: powgi(gcoeff(I,1,1), e);
      N = mulii(N, ne);
      d = mulii(d, de);
    }
  *pd = d; return N;
}

static GEN
get_pr_lists(GEN FB, long N, int list_pr)
{
  GEN pr, L;
  long i, l = lg(FB), p, pmax;

  pmax = 0;
  for (i=1; i<l; i++)
  {
    pr = gel(FB,i); p = pr_get_smallp(pr);
    if (p > pmax) pmax = p;
  }
  L = const_vec(pmax, NULL);
  if (list_pr)
  {
    for (i=1; i<l; i++)
    {
      pr = gel(FB,i); p = pr_get_smallp(pr);
      if (!L[p]) gel(L,p) = cget1(N+1, t_VEC);
      appendL(gel(L,p), pr);
    }
    for (p=1; p<=pmax; p++)
      if (L[p]) gen_sort_inplace(gel(L,p), (void*)&cmp_prime_over_p,
				 &cmp_nodata, NULL);
  }
  else
  {
    for (i=1; i<l; i++)
    {
      pr = gel(FB,i); p = pr_get_smallp(pr);
      if (!L[p]) gel(L,p) = cget1(N+1, t_VECSMALL);
      appendL(gel(L,p), (GEN)i);
    }
  }
  return L;
}

/* recover FB, LV, iLP, KCZ from Vbase */
static GEN
recover_partFB(FB_t *F, GEN Vbase, long N)
{
  GEN FB, LV, iLP, L = get_pr_lists(Vbase, N, 0);
  long l = lg(L), p, ip, i;

  i = ip = 0;
  FB = cgetg(l, t_VECSMALL);
  iLP= cgetg(l, t_VECSMALL);
  LV = cgetg(l, t_VEC);
  for (p = 2; p < l; p++)
  {
    if (!L[p]) continue;
    FB[++i] = p;
    gel(LV,p) = vecpermute(Vbase, gel(L,p));
    iLP[p]= ip; ip += lg(L[p])-1;
  }
  F->KCZ = i;
  F->KC = ip;
  F->FB = FB; setlg(FB, i+1);
  F->LV = (GEN*)LV;
  F->iLP= iLP; return L;
}

/* add v^e to factorization */
static void
add_to_fact(long v, long e, FACT *fact)
{
  long i, l = fact[0].pr;
  for (i=1; i<=l && fact[i].pr < v; i++)/*empty*/;
  if (i <= l && fact[i].pr == v) fact[i].ex += e; else store(v, e, fact);
}

/* L (small) list of primes above the same p including pr. Return pr index */
static int
pr_index(GEN L, GEN pr)
{
  long j, l = lg(L);
  GEN al = pr_get_gen(pr);
  for (j=1; j<l; j++)
    if (ZV_equal(al, pr_get_gen(gel(L,j)))) return j;
  pari_err(bugparier,"codeprime");
  return 0; /* not reached */
}

static long
Vbase_to_FB(FB_t *F, GEN pr)
{
  long p = pr_get_smallp(pr);
  return F->iLP[p] + pr_index(F->LV[p], pr);
}

/* return famat y (principal ideal) such that y / x is smooth [wrt Vbase] */
static GEN
SPLIT(FB_t *F, GEN nf, GEN x, GEN Vbase, FACT *fact)
{
  GEN vdir, z, ex, y, x0, Nx = ZM_det_triangular(x);
  long nbtest_lim, nbtest, bou, i, ru, lgsub;
  int flag = (gexpo(gcoeff(x,1,1)) < 100);

  /* try without reduction if x is small.
   * N.B can_factor destroys its NI argument */
  if (flag && can_factor(F, nf, x, NULL, icopy(Nx), fact)) return NULL;

  /* if reduction fails (y scalar), do not retry can_factor */
  y = idealred_elt(nf,x);
  if ((!flag || !ZV_isscalar(y)) && factorgen(F, nf, x, Nx, y, fact)) return y;

  /* reduce in various directions */
  ru = lg(nf[6]);
  vdir = cgetg(ru,t_VECSMALL);
  for (i=2; i<ru; i++) vdir[i]=0;
  for (i=1; i<ru; i++)
  {
    vdir[i] = 10;
    y = idealred_elt0(nf,x,vdir);
    if (factorgen(F, nf, x, Nx, y, fact)) return y;
    vdir[i] = 0;
  }

  /* tough case, multiply by random products */
  lgsub = 3;
  ex = cgetg(lgsub, t_VECSMALL);
  z  = init_famat(NULL);
  x0 = init_famat(x);
  nbtest = 1; nbtest_lim = 4;
  for(;;)
  {
    pari_sp av = avma;
    GEN I, NI, id = x0;
    if (DEBUGLEVEL>2) fprintferr("# ideals tried = %ld\n",nbtest);
    for (i=1; i<lgsub; i++)
    {
      ex[i] = random_bits(RANDOM_BITS);
      if (ex[i])
      { /* avoid prec pb: don't let id become too large as lgsub increases */
	if (id != x0) id = idealred0(nf,id,NULL);
	z[1] = Vbase[i];
	id = extideal_HNF_mul(nf, id, idealpowred(nf,z,utoipos(ex[i])));
      }
    }
    if (id == x0) continue;

    I = gel(id,1); NI = ZM_det_triangular(I);
    for (i=1; i<ru; i++) vdir[i] = random_bits(RANDOM_BITS);
    for (bou=1; bou<ru; bou++)
    {
      y = idealred_elt0(nf, I, vdir);
      if (factorgen(F, nf, I, NI, y, fact))
      {
	for (i=1; i<lgsub; i++)
	  if (ex[i]) add_to_fact(Vbase_to_FB(F,gel(Vbase,i)), ex[i], fact);
	return famat_mul(gel(id,2), y);
      }
      for (i=1; i<ru; i++) vdir[i] = 0;
      vdir[bou] = 10;
    }
    avma = av;
    if (++nbtest > nbtest_lim)
    {
      nbtest = 0;
      if (++lgsub < 7)
      {
	nbtest_lim <<= 1;
	ex = cgetg(lgsub, t_VECSMALL);
      }
      else nbtest_lim = LONG_MAX; /* don't increase further */
      if (DEBUGLEVEL>2) fprintferr("SPLIT: increasing factor base [%ld]\n",lgsub);
    }
  }
}

/* return principal y such that y / x is smooth. Store factorization of latter*/
static GEN
split_ideal(GEN nf, FB_t *F, GEN x, GEN Vbase, GEN L, FACT *fact)
{
  GEN y = SPLIT(F, nf, x, Vbase, fact);
  long p,j, i, l = lg(F->FB);

  p = j = 0; /* -Wall */
  for (i=1; i<=fact[0].pr; i++)
  { /* decode index C = ip+j --> (p,j) */
    long q,k,t, C = fact[i].pr;
    for (t=1; t<l; t++)
    {
      q = F->FB[t];
      k = C - F->iLP[q];
      if (k <= 0) break;
      p = q;
      j = k;
    }
    fact[i].pr = gel(L, p)[j];
  }
  return y;
}

/* return sorted vectbase [sorted in bnf since version 2.2.4] */
static GEN
get_Vbase(GEN bnf)
{
  GEN vectbase = gel(bnf,5), perm = gel(bnf,6), Vbase;
  long i, l, tx = typ(perm);

  if (tx == t_INT) return vectbase;
  /* old format */
  l = lg(vectbase); Vbase = cgetg(l,t_VEC);
  for (i=1; i<l; i++) Vbase[i] = vectbase[itos(gel(perm,i))];
  return Vbase;
}

/* all primes up to Minkowski bound factor on factorbase ? */
void
testprimes(GEN bnf, GEN BOUND)
{
  pari_sp av0 = avma, av;
  ulong p, pmax, bound = itou_or_0(BOUND);
  FACT *fact;
  GEN nf = gel(bnf,7), f = gel(nf,4), dK = gel(nf,3), Vbase, fb, gp;
  byteptr d = diffptr + 1;
  FB_t F;

  if (!is_pm1(f))
  {
    GEN D = gmael(nf,5,5), L;
    if (DEBUGLEVEL>1) fprintferr("**** Testing Different = %Ps\n",D);
    L = bnfisprincipal0(bnf, D, nf_FORCE);
    if (DEBUGLEVEL>1) fprintferr("     is %Ps\n", L);
  }
  /* sort factorbase for tablesearch */
  fb = gen_sort(gel(bnf,5), (void*)&cmp_prime_ideal, cmp_nodata);
  pmax = itou(gmael(fb, lg(fb)-1, 1)); /* largest p in factorbase */
  Vbase = get_Vbase(bnf);
  (void)recover_partFB(&F, Vbase, degpol(nf[1]));
  fact = (FACT*)stackmalloc((F.KC+1)*sizeof(FACT));

  if (!bound) bound = maxprime();
  for (av=avma, p=2; p < bound; avma=av)
  {
    GEN vP = idealprimedec(bnf, utoipos(p));
    long i, l = lg(vP);
    if (DEBUGLEVEL>1) fprintferr("*** p = %lu\n",p);
    /* loop through all P | p if ramified, all but one otherwise */
    if (umodiu(dK,p)) l--;
    for (i=1; i<l; i++)
    {
      GEN P = gel(vP,i);
      long k;
      if (DEBUGLEVEL>1) fprintferr("  Testing P = %Ps\n",P);
      if (cmpii(pr_norm(P), BOUND) >= 0)
      {
	if (DEBUGLEVEL>1) fprintferr("    Norm(P) > Zimmert bound\n");
	break;
      }
      if (p <= pmax && (k = tablesearch(fb, P, &cmp_prime_ideal)))
      { if (DEBUGLEVEL>1) fprintferr("    #%ld in factor base\n",k); }
      else if (DEBUGLEVEL>1)
	fprintferr("    is %Ps\n", isprincipal(bnf,P));
      else /* faster: don't compute result */
	(void)SPLIT(&F, nf, idealhnf_two(nf,P), Vbase, fact);
    }
    NEXT_PRIME_VIADIFF(p, d);
  }
  if (lgefint(BOUND) == 3) { avma = av0; return; }

  pari_warn(warner,"Zimmert's bound is large (%Pd), certification will take a long time", BOUND);
  gp = utoipos(bound);
  for (av=avma;; gp = gerepileuptoint(av, nextprime(addis(gp,1))))
  {
    GEN vP = idealprimedec(bnf, gp);
    long i, l = lg(vP);
    if (DEBUGLEVEL>1) fprintferr("*** p = %Pu\n",gp);
    /* loop through all P | p if ramified, all but one otherwise */
    if (!dvdii(dK,gp)) l--;
    for (i=1; i<l; i++)
    {
      GEN P = gel(vP,i);
      if (DEBUGLEVEL>1) fprintferr("  Testing P = %Ps\n",P);
      if (cmpii(pr_norm(P), BOUND) >= 0)
      {
	if (DEBUGLEVEL>1) fprintferr("    Norm(P) > Zimmert bound\n");
	break;
      }
      if (DEBUGLEVEL>1)
	fprintferr("    is %Ps\n", isprincipal(bnf,P));
      else /* faster: don't compute result */
	(void)SPLIT(&F, nf, idealhnf_two(nf,P), Vbase, fact);
    }
  }
  avma = av0;
}

/**** logarithmic embeddings ****/

static GEN
famat_to_arch(GEN nf, GEN fa, long prec)
{
  GEN g,e, y = NULL;
  long i,l;

  if (typ(fa) != t_MAT) return get_arch(nf, fa, prec);
  if (lg(fa) == 1) return zerovec(lg(nf[6])-1);
  g = gel(fa,1);
  e = gel(fa,2); l = lg(e);
  for (i=1; i<l; i++)
  {
    GEN t, x = nf_to_scalar_or_basis(nf, gel(g,i));
    /* multiplicative arch would be better (save logs), but exponents overflow
     * [ could keep track of expo separately, but not worth it ] */
    t = get_arch(nf,x,prec); if (gel(t,1) == gen_0) continue; /* rational */
    t = RgV_Rg_mul(t, gel(e,i));
    y = y? RgV_add(y,t): t;
  }
  return y ? y: zerovec(lg(nf[6])-1);
}

static GEN
mylog(GEN x, long prec)
{
  if (gcmp0(x)) pari_err(precer,"get_arch");
  return glog(x,prec);
}

/* For internal use. Get archimedean components: [e_i Log( sigma_i(X) )],
 * where X = primpart(x), and e_i = 1 (resp 2.) for i <= R1 (resp. > R1) */
GEN
get_arch(GEN nf,GEN x,long prec)
{
  long i, R1, RU;
  GEN v;
  if (typ(x) == t_MAT) return famat_to_arch(nf,x,prec);
  x = nf_to_scalar_or_basis(nf,x);
  RU = lg(nf[6]) - 1;
  if (typ(x) != t_COL) return zerovec(RU);
  x = RgM_RgC_mul(gmael(nf,5,1), Q_primpart(x));
  v = cgetg(RU+1,t_VEC); R1 = nf_get_r1(nf);
  for (i=1; i<=R1; i++) gel(v,i) = mylog(gel(x,i),prec);
  for (   ; i<=RU; i++) gel(v,i) = gmul2n(mylog(gel(x,i),prec),1);
  return v;
}

GEN get_arch_real(GEN nf,GEN x,GEN *emb,long prec);

static GEN
famat_get_arch_real(GEN nf,GEN x,GEN *emb,long prec)
{
  GEN A, T, a, t, g = gel(x,1), e = gel(x,2);
  long i, l = lg(e);

  if (l <= 1)
    return get_arch_real(nf, gen_1, emb, prec);
  A = T = NULL; /* -Wall */
  for (i=1; i<l; i++)
  {
    a = get_arch_real(nf, gel(g,i), &t, prec);
    if (!a) return NULL;
    a = RgC_Rg_mul(a, gel(e,i));
    t = vecpow(t, gel(e,i));
    if (i == 1) { A = a;          T = t; }
    else        { A = gadd(A, a); T = vecmul(T, t); }
  }
  *emb = T; return A;
}

static GEN
scalar_get_arch_real(long R1, long RU, GEN u, GEN *emb, long prec)
{
  GEN v, x, p1;
  long i, s;

  s = gsigne(u);
  if (!s) pari_err(talker,"0 in get_arch_real");
  x = cgetg(RU+1, t_COL);
  for (i=1; i<=RU; i++) gel(x,i) = u;

  v = cgetg(RU+1, t_COL);
  if (s < 0) u = gneg(u);
  p1 = glog(u,prec);
  for (i=1; i<=R1; i++) gel(v,i) = p1;
  if (i <= RU)
  {
    p1 = gmul2n(p1,1);
    for (   ; i<=RU; i++) gel(v,i) = p1;
  }
  *emb = x; return v;
}

static int
low_prec(GEN x) { return gcmp0(x) || (typ(x) == t_REAL && lg(x) == 3); }

/* For internal use. Get archimedean components: [e_i log( | sigma_i(x) | )],
 * with e_i = 1 (resp 2.) for i <= R1 (resp. > R1)
 * Return NULL if precision problem, and set *emb to the embeddings of x */
GEN
get_arch_real(GEN nf, GEN x, GEN *emb, long prec)
{
  long i, RU, R1;
  GEN v, t;

  if (typ(x) == t_MAT) return famat_get_arch_real(nf,x,emb,prec);
  x = nf_to_scalar_or_basis(nf,x);
  RU = lg(nf[6])-1;
  R1 = nf_get_r1(nf);
  if (typ(x) != t_COL) return scalar_get_arch_real(R1, RU, x, emb, prec);
  x = RgM_RgC_mul(gmael(nf,5,1), x);
  v = cgetg(RU+1,t_COL);
  for (i=1; i<=R1; i++)
  {
    t = gabs(gel(x,i),prec); if (low_prec(t)) return NULL;
    gel(v,i) = glog(t,prec);
  }
  for (   ; i<=RU; i++)
  {
    t = gnorm(gel(x,i)); if (low_prec(t)) return NULL;
    gel(v,i) = glog(t,prec);
  }
  *emb = x; return v;
}


GEN
init_red_mod_units(GEN bnf, long prec)
{
  GEN s = gen_0, p1,s1,mat, matunit = gel(bnf,3);
  long i,j, RU = lg(matunit);

  if (RU == 1) return NULL;
  mat = cgetg(RU,t_MAT);
  for (j=1; j<RU; j++)
  {
    p1 = cgetg(RU+1,t_COL); gel(mat,j) = p1;
    s1 = gen_0;
    for (i=1; i<RU; i++)
    {
      gel(p1,i) = real_i(gcoeff(matunit,i,j));
      s1 = mpadd(s1, gsqr(gel(p1,i)));
    }
    gel(p1,RU) = gen_0; if (mpcmp(s1,s) > 0) s = s1;
  }
  s = gsqrt(gmul2n(s,RU),prec);
  if (expo(s) < 27) s = utoipos(1UL << 27);
  return mkvec2(mat, s);
}

/* z computed above. Return unit exponents that would reduce col (arch) */
GEN
red_mod_units(GEN col, GEN z, long prec)
{
  long i,RU;
  GEN x,mat,N2;

  if (!z) return NULL;
  mat= gel(z,1);
  N2 = gel(z,2);
  RU = lg(mat); x = cgetg(RU+1,t_COL);
  for (i=1; i<RU; i++) gel(x,i) = real_i(gel(col,i));
  gel(x,RU) = N2;
  x = lll(shallowconcat(mat,x));
  if (typ(x) != t_MAT) return NULL;
  x = gel(x,RU);
  if (signe(x[RU]) < 0) x = gneg_i(x);
  if (!gcmp1(gel(x,RU))) pari_err(bugparier,"red_mod_units");
  setlg(x,RU); return x;
}

/* [x] archimedian components, A column vector. return [x] A
 * x may be a translated GEN (y + k) */
static GEN
act_arch(GEN A, GEN x)
{
  GEN a;
  long i,l = lg(A), tA = typ(A);
  if (tA == t_MAT)
  { /* assume lg(x) >= l */
    a = cgetg(l, t_VEC);
    for (i=1; i<l; i++) gel(a,i) = act_arch(gel(A,i), x);
    return a;
  }
  if (l==1) return cgetg(1, t_VEC);
  if (tA == t_VECSMALL)
  {
    a = gmulsg(A[1], gel(x,1));
    for (i=2; i<l; i++)
      if (A[i]) a = gadd(a, gmulsg(A[i], gel(x,i)));
  }
  else
  { /* A a t_COL of t_INT. Assume lg(A)==lg(x) */
    a = gmul(gel(A,1), gel(x,1));
    for (i=2; i<l; i++)
      if (signe(A[i])) a = gadd(a, gmul(gel(A,i), gel(x,i)));
  }
  settyp(a, t_VEC); return a;
}

static long
prec_arch(GEN bnf)
{
  GEN a = gel(bnf,4);
  long i, l = lg(a), prec;

  for (i=1; i<l; i++)
    if ( (prec = gprecision(gel(a,i))) ) return prec;
  return DEFAULTPREC;
}

/* col = archimedian components of x, Nx = kNx^e its norm (e > 0, usually = 1),
 * dx a bound for its denominator. Return x or NULL (fail) */
GEN
isprincipalarch(GEN bnf, GEN col, GEN kNx, GEN e, GEN dx, long *pe)
{
  GEN nf, x, matunit, s, M;
  long N, R1, RU, i, prec = gprecision(col);
  bnf = checkbnf(bnf); nf = gel(bnf,7); M = gmael(nf,5,1);
  if (!prec) prec = prec_arch(bnf);
  matunit = gel(bnf,3);
  N = degpol(nf[1]);
  R1 = nf_get_r1(nf);
  RU = (N + R1)>>1;
  col = cleanarch(col,N,prec); settyp(col, t_COL);
  if (!col) pari_err(precer, "isprincipalarch");
  if (RU > 1)
  { /* reduce mod units */
    GEN u, z = init_red_mod_units(bnf,prec);
    u = red_mod_units(col,z,prec);
    if (!u && z) return NULL;
    if (u) col = RgC_add(col, RgM_RgC_mul(matunit, u));
  }
  s = divrs(mpmul(e, glog(kNx,prec)), N);
  for (i=1; i<=R1; i++) gel(col,i) = gexp(gadd(s, gel(col,i)),prec);
  for (   ; i<=RU; i++) gel(col,i) = gexp(gadd(s, gmul2n(gel(col,i),-1)),prec);
  /* d.alpha such that x = alpha \prod gj^ej */
  x = RgM_solve_realimag(M,col); if (!x) return NULL;
  x = grndtoi(RgC_Rg_mul(x, dx), pe);
  return (*pe > -5)? NULL: RgC_Rg_div(x, dx);
}

/* y = C \prod g[i]^e[i] ? */
static int
fact_ok(GEN nf, GEN y, GEN C, GEN g, GEN e)
{
  pari_sp av = avma;
  long i, c = lg(e);
  GEN z = C? C: gen_1;
  for (i=1; i<c; i++)
    if (signe(e[i])) z = idealmul(nf, z, idealpow(nf, gel(g,i), gel(e,i)));
  if (typ(z) != t_MAT) z = idealhnf_shallow(nf,z);
  if (typ(y) != t_MAT) y = idealhnf_shallow(nf,y);
  i = ZM_equal(y, z); avma = av; return i;
}

/* assume x in HNF. cf class_group_gen for notations.
 * Return NULL iff flag & nf_FORCE and computation of principal ideal generator
 * fails */
static GEN
isprincipalall(GEN bnf, GEN x, long *ptprec, long flag)
{
  long i,lW,lB,e,c, prec = *ptprec;
  GEN Q,xar,Wex,Bex,U,p1,gen,cyc,xc,ex,d,col,A;
  GEN W    = gel(bnf,1);
  GEN B    = gel(bnf,2);
  GEN WB_C = gel(bnf,4);
  GEN nf   = gel(bnf,7);
  GEN clg2 = gel(bnf,9);
  FB_t F;
  GEN Vbase = get_Vbase(bnf);
  GEN L = recover_partFB(&F, Vbase, lg(x)-1);
  FACT *fact;

  U = gel(clg2,1);
  cyc = gmael3(bnf,8,1,2); c = lg(cyc)-1;
  gen = gmael3(bnf,8,1,3);
  ex = cgetg(c+1,t_COL);
  if (c == 0 && !(flag & (nf_GEN|nf_GENMAT|nf_GEN_IF_PRINCIPAL))) return ex;

  /* factor x */
  x = Q_primitive_part(x, &xc);
  fact = (FACT*)stackmalloc((F.KC+1)*sizeof(FACT));
  xar = split_ideal(nf, &F, x, Vbase, L, fact);
  lW = lg(W)-1; Wex = const_vecsmall(lW, 0);
  lB = lg(B)-1; Bex = const_vecsmall(lB, 0);
  for (i=1; i<=fact[0].pr; i++)
  {
    long k = fact[i].pr;
    long l = k - lW;
    if (l <= 0) Wex[k] = fact[i].ex;
    else        Bex[l] = fact[i].ex;
  }

  /* x = -g_W Wex - g_B Bex + [xar]  | x = g_W Wex + g_B Bex if xar = NULL
   *   = g_W A + [xar] - [C_B]Bex    |   = g_W A + [C_B]Bex
   * since g_W B + g_B = [C_B] */
  if (xar)
  {
    A = ZC_sub(ZM_zc_mul(B,Bex), zc_to_ZC(Wex));
    Bex = zv_neg(Bex);
  }
  else
    A = ZC_sub(zc_to_ZC(Wex), ZM_zc_mul(B,Bex));
  Q = ZM_ZC_mul(U, A);
  for (i=1; i<=c; i++)
    gel(Q,i) = truedvmdii(gel(Q,i), gel(cyc,i), (GEN*)(ex+i));
  if ((flag & nf_GEN_IF_PRINCIPAL))
    { if (!gcmp0(ex)) return gen_0; }
  else if (!(flag & (nf_GEN|nf_GENMAT)))
    return gcopy(ex);

  /* compute arch component of the missing principal ideal */
  { /* g A = G Ur A + [ga]A, Ur A = D Q + R as above (R = ex)
	   = G R + [GD]Q + [ga]A */
    GEN ga = gel(clg2,2), GD = gel(clg2,3);
    if (lB) col = act_arch(Bex, WB_C + lW); else col = zerovec(1); /* nf=Q ! */
    if (lW) col = gadd(col, act_arch(A, ga));
    if (c)  col = gadd(col, act_arch(Q, GD));
  }
  if (xar) col = gadd(col, famat_to_arch(nf, xar, prec));

  /* find coords on Zk; Q = N (x / \prod gj^ej) = N(alpha), denom(alpha) | d */
  Q = gdiv(ZM_det_triangular(x), get_norm_fact(gen, ex, &d));
  col = isprincipalarch(bnf, col, Q, gen_1, d, &e);
  if (col && !fact_ok(nf,x, col,gen,ex)) col = NULL;
  if (!col && !ZV_cmp0(ex))
  {
    p1 = isprincipalfact(bnf, x, gen, ZC_neg(ex), flag);
    if (typ(p1) != t_VEC) return p1;
    col = gel(p1,2);
  }
  if (col)
  { /* add back missing content */
    if (xc) col = (typ(col)==t_MAT)? famat_mul(col,xc): RgC_Rg_mul(col,xc);
  }
  else
  {
    if (e < 0) e = 0;
    *ptprec = prec + divsBIL(e) + (MEDDEFAULTPREC-2);
    if (flag & nf_FORCE)
    {
      if (DEBUGLEVEL) pari_warn(warner,"precision too low for generators, e = %ld",e);
      return NULL;
    }
    pari_warn(warner,"precision too low for generators, not given");
    col = cgetg(1, t_COL);
  }
  return (flag & nf_GEN_IF_PRINCIPAL)? col: mkvec2(ex, col);
}

static GEN
triv_gen(GEN bnf, GEN x, long flag)
{
  GEN y, nf = gel(bnf,7);
  long c;
  if (flag & nf_GEN_IF_PRINCIPAL) return algtobasis(nf,x);
  c = lg(mael3(bnf,8,1,2)) - 1;
  if (!(flag & (nf_GEN|nf_GENMAT))) return zerocol(c);
  y = cgetg(3,t_VEC);
  gel(y,1) = zerocol(c);
  gel(y,2) = algtobasis(nf,x); return y;
}

GEN
bnfisprincipal0(GEN bnf,GEN x,long flag)
{
  GEN arch, c;
  long pr;
  pari_sp av = avma;

  bnf = checkbnf(bnf);
  switch( idealtyp(&x, &arch) )
  {
    case id_PRINCIPAL:
      if (gcmp0(x)) pari_err(talker,"zero ideal in isprincipal");
      return triv_gen(bnf, x, flag);
    case id_PRIME:
      if (pr_is_inert(x))
        return gerepileupto(av, triv_gen(bnf, gel(x,1), flag));
      x = idealhnf_two(gel(bnf,7), x);
      break;
    case id_MAT:
      if (lg(x)==1) pari_err(talker,"zero ideal in isprincipal");
  }
  pr = prec_arch(bnf); /* precision of unit matrix */
  c = getrand();
  for (;;)
  {
    pari_sp av1 = avma;
    GEN y = isprincipalall(bnf,x,&pr,flag);
    if (y) return gerepilecopy(av, y);

    if (DEBUGLEVEL) pari_warn(warnprec,"isprincipal",pr);
    avma = av1; bnf = bnfnewprec_shallow(bnf,pr); setrand(c);
  }
}
GEN
isprincipal(GEN bnf,GEN x) { return bnfisprincipal0(bnf,x,0); }

/* FIXME: OBSOLETE */
GEN
isprincipalgen(GEN bnf,GEN x)
{ return bnfisprincipal0(bnf,x,nf_GEN); }
GEN
isprincipalforce(GEN bnf,GEN x)
{ return bnfisprincipal0(bnf,x,nf_FORCE); }
GEN
isprincipalgenforce(GEN bnf,GEN x)
{ return bnfisprincipal0(bnf,x,nf_GEN | nf_FORCE); }

static GEN
add_principal_part(GEN nf, GEN u, GEN v, long flag)
{
  if (flag & nf_GENMAT)
    return (typ(u) == t_COL && RgV_isscalar(u) && gcmp1(gel(u,1)))? v: famat_mul(v,u);
  else
    return nfmul(nf, v, u);
}

#if 0
/* compute C prod P[i]^e[i],  e[i] >=0 for all i. C may be NULL (omitted)
 * e destroyed ! */
static GEN
expand(GEN nf, GEN C, GEN P, GEN e)
{
  long i, l = lg(e), done = 1;
  GEN id = C;
  for (i=1; i<l; i++)
  {
    GEN ei = gel(e,i);
    if (signe(ei))
    {
      if (mod2(ei)) id = id? idealmul(nf, id, gel(P,i)): gel(P,i);
      ei = shifti(ei,-1);
      if (signe(ei)) done = 0;
      gel(e,i) = ei;
    }
  }
  if (id != C) id = idealred0(nf, id, NULL);
  if (done) return id;
  return idealmulred(nf, id, idealsqr(nf, expand(nf,id,P,e)));
}
/* C is an extended ideal, possibly with C[1] = NULL */
static GEN
expandext(GEN nf, GEN C, GEN P, GEN e)
{
  long i, l = lg(e), done = 1;
  GEN A = gel(C,1);
  for (i=1; i<l; i++)
  {
    GEN ei = gel(e,i);
    if (signe(ei))
    {
      if (mod2(ei)) A = A? idealmul(nf, A, gel(P,i)): gel(P,i);
      ei = shifti(ei,-1);
      if (signe(ei)) done = 0;
      gel(e,i) = ei;
    }
  }
  if (A == gel(C,1))
    A = C;
  else
    A = idealred0(nf, mkvec2(A, gel(C,2)), NULL);
  if (done) return A;
  return idealmulred(nf, A, idealsqr(nf, expand(nf,A,P,e)));
}
#endif

static GEN
expand(GEN nf, GEN C, GEN P, GEN e)
{
  long i, l = lg(e);
  GEN B, A = C;
  for (i=1; i<l; i++) /* compute prod P[i]^e[i] */
    if (signe(e[i]))
    {
      B = idealpowred(nf, gel(P,i), gel(e,i));
      A = A? idealmulred(nf,A,B): B;
    }
  return A;
}
static GEN
expandext(GEN nf, GEN C, GEN P, GEN e)
{
  long i, l = lg(e);
  GEN B, A = gel(C,1), C1 = A;
  for (i=1; i<l; i++) /* compute prod P[i]^e[i] */
    if (signe(e[i]))
    {
      gel(C,1) = gel(P,i);
      B = idealpowred(nf, C, gel(e,i));
      A = A? idealmulred(nf,A,B): B;
    }
  return A == C1? C: A;
}

/* isprincipal for C * \prod P[i]^e[i] (C omitted if NULL) */
GEN
isprincipalfact(GEN bnf, GEN C, GEN P, GEN e, long flag)
{
  const long gen = flag & (nf_GEN|nf_GENMAT|nf_GEN_IF_PRINCIPAL);
  long prec;
  pari_sp av = avma;
  GEN C0, Cext, c, id, nf = checknf(bnf);

  if (gen)
  {
    Cext = (flag & nf_GENMAT)? cgetg(1, t_MAT): mkpolmod(gen_1,gel(nf,1));
    C0 = mkvec2(C, Cext);
    id = expandext(nf, C0, P, e);
  } else {
    Cext = NULL;
    C0 = C;
    id = expand(nf, C, P, e);
  }
  if (id == C0) /* e = 0 */
  {
    if (!C) return bnfisprincipal0(bnf, gen_1, flag);
    C = idealhnf_shallow(nf,C);
  }
  else
  {
    if (gen) { C = gel(id,1); Cext = gel(id,2); } else C = id;
  }
  prec = prec_arch(bnf);
  c = getrand();
  for (;;)
  {
    pari_sp av1 = avma;
    GEN y = isprincipalall(bnf, C, &prec, flag);
    if (y)
    {
      if (flag & nf_GEN_IF_PRINCIPAL)
      {
	if (typ(y) == t_INT) { avma = av; return NULL; }
	y = add_principal_part(nf, y, Cext, flag);
      }
      else
      {
	GEN u = gel(y,2);
	if (!gen || typ(y) != t_VEC) return gerepileupto(av,y);
	if (lg(u) != 1) gel(y,2) = add_principal_part(nf, u, Cext, flag);
      }
      return gerepilecopy(av, y);
    }
    if (DEBUGLEVEL) pari_warn(warnprec,"isprincipal",prec);
    avma = av1; bnf = bnfnewprec_shallow(bnf,prec); setrand(c);
  }
}
GEN
isprincipalfact_or_fail(GEN bnf, GEN C, GEN P, GEN e)
{
  const long flag = nf_GENMAT|nf_FORCE;
  long prec;
  pari_sp av = avma;
  GEN u, y, id, C0, Cext, nf = gel(bnf,7);

  Cext = cgetg(1, t_MAT);
  C0 = mkvec2(C, Cext);
  id = expandext(nf, C0, P, e);
  if (id == C0) /* e = 0 */
    C = idealhnf_shallow(nf,C);
  else {
    C = gel(id,1); Cext = gel(id,2);
  }
  prec = prec_arch(bnf);
  y = isprincipalall(bnf, C, &prec, flag);
  if (!y) { avma = av; return utoipos(prec); }
  u = gel(y,2);
  if (lg(u) != 1) gel(y,2) = add_principal_part(nf, u, Cext, flag);
  return gerepilecopy(av, y);
}

/* if x a famat, assume it is an algebraic integer (very costly to check) */
GEN
bnfisunit(GEN bnf,GEN x)
{
  long tx = typ(x), i, R1, RU, e, n, prec;
  pari_sp av = avma;
  GEN tu, p1, v, rlog, logunit, ex, nf, z, pi2_sur_w, emb;

  bnf = checkbnf(bnf);
  nf = gel(bnf,7);
  logunit = gel(bnf,3); RU = lg(logunit);
  tu = gmael(bnf,8,4);
  n = itou(gel(tu,1)); /* # { roots of 1 } */
  z = algtobasis(nf, gel(tu,2)); /* primitive root of 1 */
  if (tx == t_MAT)
  { /* famat, assumed integral */
    if (lg(x) != 3 || lg(x[1]) != lg(x[2]))
      pari_err(talker, "not a factorization matrix in bnfisunit");
  } else {
    x = nf_to_scalar_or_basis(nf,x);
    if (typ(x) != t_COL)
    { /* rational unit ? */
      long s;
      if (typ(x) != t_INT || !is_pm1(x)) return cgetg(1,t_COL);
      s = signe(x); avma = av; v = zerocol(RU);
      gel(v,RU) = mkintmodu((s > 0)? 0: n>>1, n);
      return v;
    }
    if (!gcmp1(Q_denom(x))) { avma = av; return cgetg(1,t_COL); }
  }

  R1 = nf_get_r1(nf); v = cgetg(RU+1,t_COL);
  for (i=1; i<=R1; i++) gel(v,i) = gen_1;
  for (   ; i<=RU; i++) gel(v,i) = gen_2;
  logunit = shallowconcat(logunit, v);
  /* ex = fundamental units exponents */
  rlog = real_i(logunit);
  prec = nf_get_prec(nf);
  for (i=1;; i++)
  {
    GEN rx = get_arch_real(nf,x,&emb, MEDDEFAULTPREC);
    if (rx)
    {
      GEN logN = RgV_sum(rx); /* log(Nx), should be ~ 0 */
      if (gexpo(logN) > -20)
      {
	long p = 2 + max(1, (nf_get_prec(nf)-2) / 2);
	if (typ(logN) != t_REAL || gprecision(rx) > p)
	  { avma = av; return cgetg(1,t_COL); } /* not a precision problem */
      }
      else
      {
        ex = RgM_solve(rlog, rx);
        if (ex)
        {
          ex = grndtoi(ex, &e);
          if (gcmp0(gel(ex,RU)) && e < -4) break;
        }
      }
    }
    if (i == 1)
      prec = MEDDEFAULTPREC + divsBIL( gexpo(x) );
    else
    {
      if (i > 4) pari_err(precer,"bnfisunit");
      prec = (prec-1)<<1;
    }
    if (DEBUGLEVEL) pari_warn(warnprec,"bnfisunit",prec);
    nf = nfnewprec_shallow(nf, prec);
  }

  setlg(ex, RU); /* ZC */
  p1 = imag_i( row_i(logunit,1, 1,RU-1) );
  p1 = RgV_dotproduct(p1, ex); if (!R1) p1 = gmul2n(p1, -1);
  p1 = gsub(garg(gel(emb,1),prec), p1);
  /* p1 = arg(the missing root of 1) */

  pi2_sur_w = divru(mppi(prec), n>>1); /* 2pi / n */
  e = umodiu(roundr(divrr(p1, pi2_sur_w)), n);
  if (n > 2)
  {
    GEN ro = RgV_dotproduct(row(gmael(nf,5,1), 1), z);
    GEN p2 = roundr(divrr(garg(ro, prec), pi2_sur_w));
    e *= Fl_inv(umodiu(p2,n), n);
    e %= n;
  }

  gel(ex,RU) = mkintmodu(e, n);
  setlg(ex, RU+1); return gerepilecopy(av, ex);
}

GEN
nfsign_from_logarch(GEN LA, GEN invpi, GEN archp)
{
  long l = lg(archp), i;
  GEN y = cgetg(l, t_VECSMALL);
  pari_sp av = avma;

  for (i=1; i<l; i++)
  {
    GEN c = ground( gmul(imag_i(gel(LA,archp[i])), invpi) );
    y[i] = mpodd(c)? 1: 0;
  }
  avma = av; return y;
}

GEN
nfsign_units(GEN bnf, GEN archp, int add_zu)
{
  GEN y, A = gel(bnf,3), invpi = ginv( mppi(DEFAULTPREC) );
  long j = 1, RU = lg(A);

  if (!archp) archp = identity_perm( nf_get_r1(gel(bnf,7)) );
  if (add_zu) { RU++; A--; }
  y = cgetg(RU,t_MAT);
  if (add_zu)
  {
    GEN w = gmael3(bnf,8,4,1);
    gel(y, j++) = equaliu(w,2)? const_vecsmall(lg(archp)-1, 1)
                              : cgetg(1, t_VECSMALL);
  }
  for ( ; j < RU; j++) gel(y,j) = nfsign_from_logarch(gel(A,j), invpi, archp);
  return y;
}

/* obsolete */
GEN
signunits(GEN bnf)
{
  pari_sp av;
  GEN S, y, nf;
  long i, j, r1, r2;

  bnf = checkbnf(bnf);
  nf = gel(bnf,7); nf_get_sign(nf, &r1,&r2);
  S = zeromatcopy(r1, r1+r2-1); av = avma;
  y = nfsign_units(bnf, NULL, 0);
  for (j = 1; j < lg(y); j++)
  {
    GEN Sj = gel(S,j), yj = gel(y,j);
    for (i = 1; i <= r1; i++) gel(Sj,i) = yj[i]? gen_m1: gen_1;
  }
  avma = av; return S;
}

/* LLL-reduce ideal and return Cholesky for T2 | ideal */
static GEN
red_ideal(GEN *ideal, GEN G0, GEN G, long prec)
{
  GEN u = lllint(ZM_mul(G0, *ideal));
  *ideal = ZM_mul(*ideal,u); /* approximate LLL reduction */
  return Q_from_QR(RgM_mul(G, *ideal), prec);
}

static GEN
get_log_embed(REL_t *rel, GEN M, long RU, long R1, long prec)
{
  GEN arch, C;
  long i;
  if (!rel->m) return zerocol(RU);
  arch = RgM_RgC_mul(M, rel->m);
  if (rel->ex)
  {
    GEN t, ex = rel->ex, x = NULL;
    long l = lg(ex);
    for (i=1; i<l; i++)
      if (ex[i])
      {
	t = gmael(rel->pow->arc, i, ex[i]);
	x = x? vecmul(x, t): t; /* arch components in MULTIPLICATIVE form */
      }
    if (x) arch = vecmul(x, arch);
  }
  C = cgetg(RU+1, t_COL); arch = glog(arch, prec);
  for (i=1; i<=R1; i++) C[i] = arch[i];
  for (   ; i<=RU; i++) gel(C,i) = gmul2n(gel(arch,i), 1);
  return C;
}

static void
powFB_fill(RELCACHE_t *cache, GEN M)
{
  powFB_t *old = NULL, *pow;
  pari_sp av = avma;
  REL_t *rel;
  for (rel = cache->base + 1; rel <= cache->last; rel++)
  {
    long i, j, l;
    GEN Alg, Arc;
    if (!rel->ex) continue;
    pow = rel->pow; if (pow == old) continue;
    old = pow;
    if (pow->arc) gunclone(pow->arc);
    Alg = pow->alg; l = lg(Alg); Arc = cgetg(l, t_VEC);
    for (i = 1; i < l; i++)
    {
      GEN z, t = gel(Alg,i);
      long lt = lg(t);
      z = cgetg(lt, t_VEC);
      gel(Arc,i) = z; if (lt == 1) continue;
      z[1] = M[1];  /* leave t[1] = 1 alone ! */
      for (j = 2; j < lt; j++)
	gel(z,j) = typ(t[j]) == t_COL? RgM_RgC_mul(M, gel(t,j))
                                     : RgC_Rg_mul(gel(M,1), gel(t,j));
      for (j = 3; j < lt; j++)
	gel(z,j) = vecmul(gel(z,j), gel(z,j-1));
    }
    pow->arc = gclone(Arc);
  }
  avma = av;
}

static void
set_fact(REL_t *rel, FB_t *F, FACT *fact)
{
  long i;
  GEN c = rel->R = col_0(F->KC); rel->nz = fact[1].pr;
  for (i=1; i<=fact[0].pr; i++) c[fact[i].pr] = fact[i].ex;
}

/* If V depends linearly from the columns of the matrix, return 0.
 * Otherwise, update INVP and L and return 1. Compute mod p (much faster)
 * so some kernel vector might not be genuine. */
static int
addcolumn_mod(GEN V, GEN invp, GEN L, ulong p)
{
  pari_sp av = avma;
  GEN a = Flm_Flc_mul(invp, V, p);
  long i,j,k, n = lg(invp);
  ulong invak;

  if (DEBUGLEVEL>6)
  {
    fprintferr("adding vector = %Ps\n",V);
    fprintferr("vector in new basis = %Ps\n",a);
    fprintferr("list = %Ps\n",L);
    fprintferr("base change =\n%Ps\n", invp);
  }
  k = 1; while (k<n && (L[k] || !a[k])) k++;
  if (k == n) { avma = av; return 0; }
  invak = Fl_inv((ulong)a[k], p);
  L[k] = 1;
  for (i=k+1; i<n; i++)
    if (a[i]) a[i] = p - ((a[i] * invak) % p);
  for (j=1; j<=k; j++)
  {
    GEN c = gel(invp,j);
    ulong ck = (ulong)c[k];
    if (!ck) continue;
    c[k] = (ck * invak) % p;
    if (j==k)
      for (i=k+1; i<n; i++) c[i] = (a[i] * ck) % p;
    else
      for (i=k+1; i<n; i++) c[i] = (c[i] + a[i] * ck) % p;
  }
  avma = av; return 1;
}

/* Check if we already have a column mat[i] equal to mat[s]
 * General check for colinearity useless since exceedingly rare */
static int
already_known(RELCACHE_t *cache, REL_t *rel)
{
  REL_t *r;
  GEN cols = rel->R;
  long bs, l = lg(cols);

  bs = 1; while (bs < l && !cols[bs]) bs++;
  if (bs == l) return -1; /* zero relation */

  for (r = rel - 1; r > cache->base; r--)
  {
    if (bs == r->nz) /* = index of first non zero elt in cols */
    {
      GEN coll = r->R;
      long b = bs;
      do b++; while (b < l && cols[b] == coll[b]);
      if (b == l) return 1;
    }
  }
  rel->nz = bs; return 0;
}

/* compute the rank of A in M_n,r(Z) (C long), where rank(A) = r <= n.
 * Starting from the identity (canonical basis of Q^n), we obtain a base
 * change matrix P by taking the independent columns of A and vectors from
 * the canonical basis. Update invp = 1/P, and L in {0,1}^n, with L[i] = 0
 * if P[i] = e_i, and 1 if P[i] = A_i (i-th column of A)
 */
static GEN
relationrank(RELCACHE_t *cache, GEN L, ulong p)
{
  GEN invp = matid_Flm(lg(L) - 1);
  REL_t *rel = cache->base + 1;
  for (; rel <= cache->last; rel++) (void)addcolumn_mod(rel->R, invp, L, p);
  return invp;
}

static void
small_norm(RELCACHE_t *cache, FB_t *F, GEN nf, long nbrelpid,
	   double LOGD, double LIMC2, FACT *fact)
{
  const long BMULT = 8;
  const ulong mod_p = 27449UL;
  const long maxtry_DEP  = 20, maxtry_FACT = 500;
  double *y,*z,**q,*v, BOUND;
  pari_sp av;
  long nbsmallnorm, nbfact, j, k, noideal = F->KC, precbound;
  long N = degpol(nf[1]), R1 = nf_get_r1(nf), prec = nf_get_prec(nf);
  GEN x, gx, r, M = gmael(nf,5,1), G = gmael(nf,5,2);
  GEN L = const_vecsmall(F->KC, 0), invp = relationrank(cache, L, mod_p);
  REL_t *rel = cache->last;

  if (DEBUGLEVEL)
    fprintferr("\n#### Looking for %ld relations (small norms)\n",
	       cache->end - cache->base);
  gx = NULL; /* gcc -Wall */
  nbsmallnorm = nbfact = 0;

 /* LLL reduction produces v0 in I such that
  *     T2(v0) <= (4/3)^((n-1)/2) NI^(2/n) disc(K)^(1/n)
  * We consider v with T2(v) <= BMULT * T2(v0)
  * Hence Nv <= ((4/3)^((n-1)/2) * BMULT / n)^(n/2) NI sqrt(disc(K)) */
  precbound = 3 + (long)ceil(
    (N/2. * ((N-1)/2.* log(4./3) + log(BMULT/(double)N)) + log(LIMC2) + LOGD/2)
      / (BITS_IN_LONG * LOG2)); /* enough to compute norms */
  if (precbound < prec) M = gprec_w(M, precbound);

  minim_alloc(N+1, &q, &x, &y, &z, &v);
  for (av = avma; noideal; noideal--, avma = av)
  {
    long nbrelideal = 0, dependent = 0, try_factor = 0;
    GEN IDEAL, ideal;
    pari_sp av2;

    ideal = gel(F->LP,noideal);
    if (DEBUGLEVEL>1)
      fprintferr("\n*** Ideal no %ld: [%Ps, %Ps, %Ps, %Ps]\n",
		 noideal, ideal[1], ideal[2], ideal[3], ideal[4]);
#if 1 /* slower but seems to find more relations this way... */
    IDEAL = ZM_lll(idealhnf_two(nf,ideal), 0.75, LLL_INPLACE);
#else
    IDEAL = idealhnf_two(nf,ideal);
#endif
    r = red_ideal(&IDEAL, F->G0, G, prec);
    if (!r) pari_err(bugparier, "small_norm (precision too low)");

    for (k=1; k<=N; k++)
    {
      v[k] = gtodouble(gcoeff(r,k,k));
      for (j=1; j<k; j++) q[j][k] = gtodouble(gcoeff(r,j,k));
      if (DEBUGLEVEL>3) fprintferr("v[%ld]=%.4g ",k,v[k]);
    }

#if 1 /* larger BOUND than alternative, but finds more intersting vectors */
    BOUND = v[2] + v[1] * q[1][2] * q[1][2];
    if (BOUND < v[1]) BOUND = v[1];
    BOUND *= 2;
    if (BOUND > v[1] * BMULT) BOUND = v[1] * BMULT;
#else
    BOUND = v[2] + v[1] * q[1][2] * q[1][2];
    if (BOUND > v[1]) BOUND = v[1];
    BOUND *= BMULT;
#endif
    /* BOUND at most BMULT x smallest known vector */
    if (DEBUGLEVEL>1)
    {
      if (DEBUGLEVEL>3) fprintferr("\n");
      fprintferr("BOUND = %.4g\n",BOUND); flusherr();
    }
    BOUND *= 1 + 1e-6;
    k = N; y[N] = z[N] = 0; x[N] = (long)sqrt(BOUND/v[N]);
    for (av2 = avma;; x[1]--, avma = av2)
    {
      for(;;) /* look for primitive element of small norm, cf minim00 */
      {
	double p;
	if (k>1)
	{
	  long l = k-1;
	  z[l] = 0;
	  for (j=k; j<=N; j++) z[l] += q[l][j]*x[j];
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
	if (k != 1) continue;

	/* element complete */
	if (y[1]<=1e-6) goto ENDIDEAL; /* skip all scalars: [*,0...0] */
	if (zv_content(x)==1) /* primitive */
	{
	  gx = ZM_zc_mul(IDEAL,x);
	  if (!ZV_isscalar(gx))
	  {
	    GEN Nx, xembed = RgM_RgC_mul(M, gx);
	    long e;
	    nbsmallnorm++;
	    if (++try_factor > maxtry_FACT) goto ENDIDEAL;
	    Nx = grndtoi(norm_by_embed(R1,xembed), &e);
	    if (e < 0)
	    {
	      setsigne(Nx, 1);
	      if (can_factor(F, nf, NULL, gx, Nx, fact)) break;
	    }
	    if (DEBUGLEVEL > 1) { fprintferr("."); flusherr(); }
	  }
	}
	x[1]--;
      }
      set_fact(++rel, F, fact);
      /* make sure we get maximal rank first, then allow all relations */
      if (rel - cache->base > 1 && rel - cache->base <= F->KC
				&& ! addcolumn_mod(rel->R,invp,L, mod_p))
      { /* Q-dependent from previous ones: forget it */
	pari_free((void*)rel->R); rel--;
	if (DEBUGLEVEL>1) fprintferr("*");
	if (++dependent > maxtry_DEP) break;
	continue;
      }
      rel->m = gclone(gx);
      rel->ex= NULL;
      dependent = 0;

      if (DEBUGLEVEL) { nbfact++; dbg_rel(rel - cache->base, rel->R); }
      if (rel >= cache->end) goto END; /* we have enough */
      if (++nbrelideal == nbrelpid) break;
    }
ENDIDEAL:
    if (DEBUGLEVEL>1) msgtimer("for this ideal");
  }
END:
  cache->last = rel;
  if (DEBUGLEVEL)
  {
    fprintferr("\n"); msgtimer("small norm relations");
    fprintferr("  small norms gave %ld relations.\n",
	       cache->last - cache->base);
    if (nbsmallnorm)
      fprintferr("  nb. fact./nb. small norm = %ld/%ld = %.3f\n",
		  nbfact,nbsmallnorm,((double)nbfact)/nbsmallnorm);
  }
}

/* I assumed to be integral, G the Cholesky form of a weighted T2 matrix.
 * Return an irrational m in I with T2(m) small */
static GEN
pseudomin(GEN I, GEN G)
{
  GEN m, u = lllint(ZM_mul(G, I));
  m = ZM_ZC_mul(I, gel(u,1));
  if (ZV_isscalar(m) && lg(u) > 2) m = ZM_ZC_mul(I, gel(u,2));
  if (DEBUGLEVEL>5) fprintferr("\nm = %Ps\n",m);
  return m;
}

static void
dbg_newrel(RELCACHE_t *cache, long jid, long jdir)
{
  fprintferr("\n++++ cglob = %ld: new relation (need %ld)",
	     cache->last - cache->base, cache->end - cache->base);
  wr_rel(cache->last->R); msgtimer("for this relation");
}

static void
dbg_cancelrel(long jid, long jdir, GEN col)
{
  fprintferr("relation cancelled: ");
  if (DEBUGLEVEL>3) fprintferr("(jid=%ld,jdir=%ld)",jid,jdir);
  wr_rel(col); flusherr();
}

/* I integral ideal in HNF form */
static GEN
remove_content(GEN I)
{
  long N = lg(I)-1;
  if (!gcmp1(gcoeff(I,N,N))) I = Q_primpart(I);
  return I;
}

static int
rnd_rel(RELCACHE_t *cache, FB_t *F, GEN nf, GEN L_jid, long *pjid, FACT *fact)
{
  long nbG = lg(F->vecG)-1, lgsub = lg(F->subFB), jlist = 1, jid = *pjid;
  long i, j, cptlist = 0, cptzer = 0;
  pari_sp av, av1;
  GEN ideal, Nideal, m, ex = cgetg(lgsub, t_VECSMALL);

  if (DEBUGLEVEL) {
    long d = cache->end - cache->last;
    fprintferr("\n(more relations needed: %ld)\n", d > 0? d: 1);
    if (L_jid) fprintferr("looking hard for %Ps\n",L_jid);
  }
  for (av = avma;;)
  {
    REL_t *rel = cache->last;
    GEN P;
    if (L_jid && jlist < lg(L_jid))
    {
      if (++cptlist > 3)
      {
	jid = L_jid[jlist];
	jlist++;
	cptlist = 0;
      }
      if (!jid) jid = 1;
    }
    else
    {
      if (jid == F->KC) jid = 1; else jid++;
    }
    avma = av;
    ideal = P = idealhnf_two(nf, gel(F->LP,jid));
    do {
      for (i=1; i<lgsub; i++)
      { /* reduce mod apparent order */
	ex[i] = random_bits(RANDOM_BITS) % F->pow->ord[i];
	if (ex[i]) ideal = idealmul_HNF(nf,ideal, gmael(F->pow->id2,i,ex[i]));
      }
    } while (ideal == P); /* If ex  = 0, try another */
    ideal = remove_content(ideal);
    if (gcmp1(gcoeff(ideal,1,1))) continue;

    Nideal = ZM_det_triangular(ideal);
    if (DEBUGLEVEL>1) fprintferr("(%ld)", jid);
    for (av1 = avma, j = 1; j <= nbG; j++, avma = av1)
    { /* reduce along various directions */
      m = pseudomin(ideal, gel(F->vecG,j));
      if (!factorgen(F,nf,ideal,Nideal,m,fact))
      {
	if (DEBUGLEVEL>1) { fprintferr("."); flusherr(); }
	continue;
      }
      /* can factor ideal, record relation */
      set_fact(++rel, F, fact); rel->R[jid]++;
      for (i=1; i<lgsub; i++) rel->R[ F->subFB[i] ] += ex[i];
      if (already_known(cache, rel))
      { /* forget it */
	if (DEBUGLEVEL>1) dbg_cancelrel(jid,j,rel->R);
	pari_free((void*)rel->R); rel--;
	if (++cptzer > MAXRELSUP)
	{
	  if (L_jid) { cptzer = 0; L_jid = NULL; break; } /* second chance */
	  *pjid = jid; return 0;
	}
	continue;
      }
      rel->m = gclone(m);
      rel->ex = gclone(ex);
      rel->pow = F->pow; cache->last = rel;
      if (DEBUGLEVEL) dbg_newrel(cache, jid, j);
      /* Need more, try next prime ideal */
      if (rel < cache->end) { cptzer = 0; break; }
      /* We have found enough. Return */
      avma = av; *pjid = jid;
      return 1;
    }
  }
}

/* remark: F->KCZ changes if be_honest() fails */
static int
be_honest(FB_t *F, GEN nf, FACT *fact)
{
  GEN P, ideal, Nideal, m;
  long ex, i, j, J, k, iz, nbtest, ru;
  long nbG = lg(F->vecG)-1, lgsub = lg(F->subFB), KCZ0 = F->KCZ;
  pari_sp av;

  if (DEBUGLEVEL) {
    fprintferr("Be honest for %ld primes from %ld to %ld\n", F->KCZ2 - F->KCZ,
	       F->FB[ F->KCZ+1 ], F->FB[ F->KCZ2 ]);
  }
  ru = lg(nf[6]);
  av = avma;
  for (iz=F->KCZ+1; iz<=F->KCZ2; iz++, avma = av)
  {
    long p = F->FB[iz];
    if (DEBUGLEVEL>1) fprintferr("%ld ", p);
    P = F->LV[p]; J = lg(P);
    /* all P|p in FB + last is unramified --> check all but last */
    if (isclone(P) && itou(gmael(P,J-1,3)) == 1UL /* e = 1 */) J--;

    for (j=1; j<J; j++)
    {
      GEN ideal0 = idealhnf_two(nf,gel(P,j));
      pari_sp av1, av2 = avma;
      for(nbtest=0;;)
      {
	ideal = ideal0;
	for (i=1; i<lgsub; i++)
	{
	  ex = random_bits(RANDOM_BITS) % F->pow->ord[i];
	  if (ex) ideal = idealmul_HNF(nf,ideal, gmael(F->pow->id2,i,ex));
	}
	ideal = remove_content(ideal);
        Nideal = ZM_det_triangular(ideal);
	for (av1 = avma, k = 1; k <= nbG; k++, avma = av1)
	{
	  m = pseudomin(ideal, gel(F->vecG,k));
	  if (factorgen(F,nf,ideal,Nideal, m,fact)) break;
	}
	avma = av2; if (k < ru) break;
	if (++nbtest > 50)
	{
	  pari_warn(warner,"be_honest() failure on prime %Ps\n", P[j]);
	  return 0;
	}
      }
    }
    F->KCZ++; /* SUCCESS, "enlarge" factorbase */
  }
  if (DEBUGLEVEL)
  {
    if (DEBUGLEVEL>1) fprintferr("\n");
    msgtimer("be honest");
  }
  F->KCZ = KCZ0; avma = av; return 1;
}

/* A = complex logarithmic embeddings of units (u_j) found so far */
static GEN
compute_multiple_of_R(GEN A,long RU,long N,GEN *ptL)
{
  GEN T,v,mdet,mdet2,Im_mdet,kR,xreal,L;
  long i, R1 = 2*RU - N;
  pari_sp av = avma;

  if (RU == 1)
  {
    *ptL = zeromat(0, lg(A)-1);
    return gen_1;
  }
  if (DEBUGLEVEL) fprintferr("\n#### Computing regulator multiple\n");
  xreal = real_i(A); /* = (log |sigma_i(u_j)|) */
  T = cgetg(RU+1,t_COL);
  for (i=1; i<=R1; i++) gel(T,i) = gen_1;
  for (   ; i<=RU; i++) gel(T,i) = gen_2;
  mdet = shallowconcat(xreal,T); /* det(Span(mdet)) = N * R */

  i = gprecision(mdet); /* truncate to avoid "near dependent" vectors */
  mdet2 = (i <= 4)? mdet: gprec_w(mdet,i-1);
  v = gel(indexrank(mdet2),2); /* list of independent column indices */
  /* check we have full rank for units */
  if (lg(v) != RU+1) { avma=av; return NULL; }

  Im_mdet = vecpermute(mdet,v);
  /* integral multiple of R: the cols we picked form a Q-basis, they have an
   * index in the full lattice. Last column is T */
  kR = divrs(det2(Im_mdet), N);
  /* R > 0.2 uniformly */
  if (!signe(kR) || expo(kR) < -3) { avma=av; return NULL; }

  setsigne(kR,1);
  L = RgM_solve(Im_mdet,NULL); /* Im_mdet^(-1) */
  if (!L) { *ptL = NULL; return kR; }

  L = RgM_mul(rowslice(L, 1, RU-1), xreal); /* approximate rational entries */
  gerepileall(av,2, &L, &kR);
  *ptL = L; return kR;
}

static GEN
bestappr_noer(GEN x, GEN k)
{
  GEN y;
  CATCH(precer) { y = NULL; }
  TRY { y = bestappr(x,k); } ENDCATCH;
  return y;
}

/* Input:
 * lambda = approximate rational entries: coords of units found so far on a
 * sublattice of maximal rank (sublambda)
 * *ptkR = regulator of sublambda = multiple of regulator of lambda
 * Compute R = true regulator of lambda.
 *
 * If c := Rz ~ 1, by Dirichlet's formula, then lambda is the full group of
 * units AND the full set of relations for the class group has been computed.
 *
 * In fact z is a very rough approximation and we only expect 0.75 < Rz < 1.3
 *
 * Output: *ptkR = R, *ptU = basis of fundamental units (in terms lambda) */
static int
compute_R(GEN lambda, GEN z, GEN *ptL, GEN *ptkR)
{
  pari_sp av = avma;
  long r;
  GEN L,H,D,den,R;
  double c;

  if (DEBUGLEVEL) { fprintferr("\n#### Computing check\n"); flusherr(); }
  D = gmul2n(mpmul(*ptkR,z), 1); /* bound for denom(lambda) */
  if (expo(D) < 0 && rtodbl(D) < 0.95) return fupb_BACH;
  lambda = bestappr_noer(lambda,D);
  if (!lambda)
  {
    if (DEBUGLEVEL) fprintferr("truncation error in bestappr\n");
    return fupb_PRECI;
  }
  den = Q_denom(lambda);
  if (mpcmp(den,D) > 0)
  {
    if (DEBUGLEVEL) fprintferr("D = %Ps\nden = %Ps\n",D,
		    lgefint(den) <= DEFAULTPREC? den: itor(den,3));
    return fupb_PRECI;
  }
  L = Q_muli_to_int(lambda, den);
  H = ZM_hnf(L); r = lg(H)-1;

  /* tentative regulator */
  R = gmul(*ptkR, gdiv(ZM_det_triangular(H), powiu(den, r)));
  c = gtodouble(gmul(R,z)); /* should be n (= 1 if we are done) */
  if (DEBUGLEVEL)
  {
    msgtimer("bestappr/regulator");
    fprintferr("\n#### Tentative regulator : %Ps\n", gprec_w(R,3));
    fprintferr("\n ***** check = %f\n",c);
  }
  if (c < 0.55) { avma = av; return fupb_BACH; }
  if (c < 0.75 || c > 1.3) { avma = av; return fupb_RELAT; }
  *ptkR = R; *ptL = L; return fupb_NONE;
}

/* find the smallest (wrt norm) among I, I^-1 and red(I^-1) */
static GEN
inverse_if_smaller(GEN nf, GEN I)
{
  GEN J, d, dmin, I1;

  J = gel(I,1);
  dmin = ZM_det_triangular(J); I1 = idealinv(nf,I);
  J = gel(I1,1); J = Q_remove_denom(J, NULL); gel(I1,1) = J;
  d = ZM_det_triangular(J); if (cmpii(d,dmin) < 0) {I=I1; dmin=d;}
  /* try reducing (often _increases_ the norm) */
  I1 = idealred0(nf,I1,NULL);
  J = gel(I1,1);
  d = ZM_det_triangular(J); if (cmpii(d,dmin) < 0) I=I1;
  return I;
}

/* in place */
static void
neg_row(GEN U, long i)
{
  GEN c = U + lg(U)-1;
  for (; c>U; c--) gcoeff(c,i,0) = negi(gcoeff(c,i,0));
}

static void
setlg_col(GEN U, long l)
{
  GEN c = U + lg(U)-1;
  for (; c>U; c--) setlg(*c, l);
}

/* compute class group (clg1) + data for isprincipal (clg2) */
static void
class_group_gen(GEN nf,GEN W,GEN C,GEN Vbase,long prec, GEN nf0,
		GEN *ptclg1,GEN *ptclg2)
{
  GEN z,G,Ga,ga,GD,cyc,X,Y,D,U,V,Ur,Ui,Uir,I,J;
  long i,j,lo,lo0;

  if (DEBUGLEVEL)
    { fprintferr("\n#### Computing class group generators\n"); (void)timer2(); }
  D = ZM_snfall(W,&U,&V); /* UWV = D, D diagonal, G = g Ui (G=new gens, g=old) */
  Ui = ginv(U);
  lo0 = lo = lg(D);
 /* we could set lo = lg(cyc) and truncate all matrices below
  *   setlg_col(D && U && Y, lo) + setlg(D && V && X && Ui, lo)
  * but it's not worth the complication:
  * 1) gain is negligible (avoid computing z^0 if lo < lo0)
  * 2) when computing ga, the products XU and VY use the original matrices
  */
  Ur  = ZM_hnfremdiv(U, D, &Y);
  Uir = ZM_hnfremdiv(Ui,W, &X);
 /* [x] = logarithmic embedding of x (arch. component)
  * NB: z = idealred(I) --> I = y z[1], with [y] = - z[2]
  * P invertible diagonal matrix (\pm 1) which is only implicitly defined
  * G = g Uir P + [Ga],  Uir = Ui + WX
  * g = G P Ur  + [ga],  Ur  = U + DY */
  G = cgetg(lo,t_VEC);
  Ga= cgetg(lo,t_VEC);
  z = init_famat(NULL);
  if (!nf0) nf0 = nf;
  for (j=1; j<lo; j++)
  {
    GEN p1 = gcoeff(Uir,1,j);
    z[1]=Vbase[1]; I = idealpowred(nf0,z,p1);
    for (i=2; i<lo0; i++)
    {
      p1 = gcoeff(Uir,i,j);
      if (signe(p1))
      {
	z[1]=Vbase[i]; 
	I = extideal_HNF_mul(nf0, I, idealpowred(nf0,z,p1));
	I = idealred0(nf0,I,NULL);
      }
    }
    J = inverse_if_smaller(nf0, I);
    if (J != I)
    { /* update wrt P */
      neg_row(Y ,j); gel(V,j) = ZC_neg(gel(V,j));
      neg_row(Ur,j); gel(X,j) = ZC_neg(gel(X,j));
    }
    G[j] = J[1]; /* generator, order cyc[j] */
    gel(Ga,j) = gneg(famat_to_arch(nf, gel(J,2), prec));
  }
  /* at this point Y = PY, Ur = PUr, V = VP, X = XP */

  /* G D =: [GD] = g (UiP + W XP) D + [Ga]D = g W (VP + XP D) + [Ga]D
   * NB: DP = PD and Ui D = W V. gW is given by (first lo0-1 cols of) C
   */
  GD = gadd(act_arch(ZM_add(V, ZM_mul(X,D)), C),
	    act_arch(D, Ga));
  /* -[ga] = [GD]PY + G PU - g = [GD]PY + [Ga] PU + gW XP PU
			       = gW (XP PUr + VP PY) + [Ga]PUr */
  ga = gadd(act_arch(ZM_add(ZM_mul(X,Ur), ZM_mul(V,Y)), C),
	    act_arch(Ur, Ga));
  ga = gneg(ga);
  /* TODO: could (LLL)reduce ga and GD mod units ? */

  cyc = cgetg(lo,t_VEC); /* elementary divisors */
  for (j=1; j<lo; j++)
  {
    gel(cyc,j) = gcoeff(D,j,j);
    if (gcmp1(gel(cyc,j)))
    { /* strip useless components */
      lo = j; setlg(cyc,lo); setlg_col(Ur,lo);
      setlg(G,lo); setlg(Ga,lo); setlg(GD,lo); break;
    }
  }
  *ptclg1 = mkvec3(ZM_det_triangular(W), cyc, G);
  *ptclg2 = mkvec3(Ur, ga,GD);
  if (DEBUGLEVEL) msgtimer("classgroup generators");
}

/* SMALLBUCHINIT */

static GEN
decode_pr_lists(GEN nf, GEN pfc)
{
  long i, p, pmax, n = degpol(nf[1]), l = lg(pfc);
  GEN t, L;

  pmax = 0;
  for (i=1; i<l; i++)
  {
    t = gel(pfc,i); p = itos(t) / n;
    if (p > pmax) pmax = p;
  }
  L = const_vec(pmax, NULL);
  for (i=1; i<l; i++)
  {
    t = gel(pfc,i); p = itos(t) / n;
    if (!L[p]) gel(L,p) = idealprimedec(nf, utoipos(p));
  }
  return L;
}

static GEN
decodeprime(GEN T, GEN L, long n)
{
  long t = itos(T);
  return gmael(L, t/n, t%n + 1);
}
static GEN
codeprime(GEN L, long N, GEN pr)
{
  long p = pr_get_smallp(pr);
  return utoipos( N*p + pr_index(gel(L,p), pr)-1 );
}

static GEN
codeprimes(GEN Vbase, long N)
{
  GEN v, L = get_pr_lists(Vbase, N, 1);
  long i, l = lg(Vbase);
  v = cgetg(l, t_VEC);
  for (i=1; i<l; i++) gel(v,i) = codeprime(L, N, gel(Vbase,i));
  return v;
}

/* compute principal ideals corresponding to (gen[i]^cyc[i]) */
static GEN
makecycgen(GEN bnf)
{
  GEN cyc,gen,h,nf,y,GD,D;
  long e,i,l;

  if (DEBUGLEVEL) pari_warn(warner,"completing bnf (building cycgen)");
  nf = checknf(bnf);
  cyc = gmael3(bnf,8,1,2); D = diagonal_i(cyc);
  gen = gmael3(bnf,8,1,3); GD = gmael(bnf,9,3);
  l = lg(gen); h = cgetg(l, t_VEC);
  for (i=1; i<l; i++)
  {
    if (cmpiu(gel(cyc,i), 5) < 0)
    {
      GEN N = ZM_det_triangular(gel(gen,i));
      y = isprincipalarch(bnf,gel(GD,i), N, gel(cyc,i), gen_1, &e);
      if (y && !fact_ok(nf,y,NULL,gen,gel(D,i))) y = NULL;
      if (y) { gel(h,i) = to_famat_shallow(y,gen_1); continue; }
    }
    y = isprincipalfact(bnf, NULL, gen, gel(D,i), nf_GENMAT|nf_FORCE);
    h[i] = y[2];
  }
  return h;
}

/* compute principal ideals corresponding to bnf relations */
static GEN
makematal(GEN bnf)
{
  GEN W,B,pFB,nf,ma, WB_C;
  long lW,lma,j,prec;

  if (DEBUGLEVEL) pari_warn(warner,"completing bnf (building matal)");
  W   = gel(bnf,1);
  B   = gel(bnf,2);
  WB_C= gel(bnf,4);
  nf  = gel(bnf,7);
  lW=lg(W)-1; lma=lW+lg(B);
  pFB = get_Vbase(bnf);
  ma = cgetg(lma,t_MAT);

  prec = prec_arch(bnf);
  for (j=1; j<lma; j++)
  {
    long e;
    GEN c = getrand();
    GEN ex = (j<=lW)? gel(W,j): gel(B,j-lW);
    GEN C = (j<=lW)? NULL: gel(pFB,j);
    GEN Nx = get_norm_fact_primes(pFB, ex, C);
    GEN y = isprincipalarch(bnf,gel(WB_C,j), Nx,gen_1, gen_1, &e);
    if (y && fact_ok(nf,y,C,pFB,ex))
    {
      if (DEBUGLEVEL>1) fprintferr("*%ld ",j);
      gel(ma,j) = y; continue;
    }
    y = isprincipalfact_or_fail(bnf, C, pFB, ex);
    if (typ(y) != t_INT)
    {
      if (DEBUGLEVEL>1) fprintferr("%ld ",j);
      gel(ma,j) = gel(y,2); continue;
    }

    prec = itos(y);
    j--; /* will retry the same element in next loop */
    if (DEBUGLEVEL) pari_warn(warnprec,"makematal",prec);
    nf = nfnewprec_shallow(nf,prec);
    bnf = bnfinit0(nf,1,NULL,prec); setrand(c);
  }
  if (DEBUGLEVEL>1) fprintferr("\n");
  return ma;
}

#define MATAL  1
#define CYCGEN 2
GEN
check_and_build_cycgen(GEN bnf) {
  return check_and_build_obj(bnf, CYCGEN, &makecycgen);
}
GEN
check_and_build_matal(GEN bnf) {
  return check_and_build_obj(bnf, MATAL, &makematal);
}

static GEN
get_regulator(GEN mun)
{
  pari_sp av = avma;
  GEN R;

  if (lg(mun) == 1) return gen_1;
  R = det( rowslice(real_i(mun), 1, lg(mun[1])-2) );
  setsigne(R, 1); return gerepileupto(av, R);
}

/* return corrected archimedian components for elts of x (vector)
 * (= log(sigma_i(x)) - log(|Nx|) / [K:Q]) */
static GEN
get_archclean(GEN nf, GEN x, long prec, int units)
{
  long k,N, la = lg(x);
  GEN M = cgetg(la,t_MAT);

  if (la == 1) return M;
  N = degpol(nf[1]);
  for (k=1; k<la; k++)
  {
    GEN c = get_arch(nf, gel(x,k), prec);
    if (!units) {
      c = cleanarch(c, N, prec);
      if (!c) return NULL;
    }
    gel(M,k) = c;
  }
  return M;
}

static void
my_class_group_gen(GEN bnf, long prec, GEN nf0, GEN *ptcl, GEN *ptcl2)
{
  GEN W=gel(bnf,1), C=gel(bnf,4), nf=gel(bnf,7);
  class_group_gen(nf,W,C,get_Vbase(bnf),prec,nf0, ptcl,ptcl2);
}

GEN
bnfnewprec_shallow(GEN bnf, long prec)
{
  GEN nf0 = gel(bnf,7), nf, res, funits, mun, matal, clgp, clgp2, y;
  long r1, r2, prec1;

  nf_get_sign(nf0, &r1, &r2);
  funits = matalgtobasis(nf0, check_units(bnf,"bnfnewprec"));

  prec1 = prec;
  if (r2 > 1 || r1 != 0)
    prec += nbits2nlong( gexpo(funits) );
  nf = nfnewprec_shallow(nf0,prec);
  mun = get_archclean(nf,funits,prec,1);
  if (!mun) pari_err(precer,"bnfnewprec");
  if (prec != prec1) { mun = gprec_w(mun,prec1); prec = prec1; }
  matal = check_and_build_matal(bnf);

  y = shallowcopy(bnf);
  gel(y,3) = mun;
  gel(y,4) = get_archclean(nf,matal,prec,0);
  if (!gel(y,4)) pari_err(precer,"bnfnewprec");
  gel(y,7) = nf;
  my_class_group_gen(y,prec,nf0, &clgp,&clgp2);
  res = shallowcopy(gel(bnf,8));
  gel(res,1) = clgp;
  gel(res,2) = get_regulator(mun);
  gel(y,8) = res;
  gel(y,9) = clgp2; return y;
}
GEN
bnfnewprec(GEN bnf, long prec)
{
  pari_sp av = avma;
  return gerepilecopy(av, bnfnewprec_shallow(checkbnf(bnf), prec));
}

GEN
bnrnewprec_shallow(GEN bnr, long prec)
{
  GEN y = shallowcopy(bnr);
  gel(y,1) = bnfnewprec_shallow(gel(bnr,1), prec);
  return y;
}
GEN
bnrnewprec(GEN bnr, long prec)
{
  GEN y = cgetg(7,t_VEC);
  long i;
  checkbnr(bnr);
  gel(y,1) = bnfnewprec(gel(bnr,1),prec);
  for (i=2; i<7; i++) gel(y,i) = gcopy(gel(bnr,i));
  return y;
}

static void
nfbasic_from_sbnf(GEN sbnf, nfbasic_t *T)
{
  T->x    = gel(sbnf,1);
  T->dK   = gel(sbnf,3);
  T->bas  = gel(sbnf,4);
  T->index= get_nfindex(T->bas);
  T->r1   = itos(gel(sbnf,2));
  T->dx   = NULL;
  T->lead = NULL;
  T->basden = NULL;
}

static GEN
get_clfu(GEN clgp, GEN reg, GEN zu, GEN fu)
{ return mkvec5(clgp, reg, gen_1/*DUMMY*/, zu, fu); }

static GEN
buchall_end(GEN nf,GEN res, GEN clg2, GEN W, GEN B, GEN A, GEN C,GEN Vbase)
{
  GEN z = cgetg(11,t_VEC);
  gel(z,1) = W;
  gel(z,2) = B;
  gel(z,3) = A;
  gel(z,4) = C;
  gel(z,5) = Vbase;
  gel(z,6) = gen_0;
  gel(z,7) = nf;
  gel(z,8) = res;
  gel(z,9) = clg2;
  gel(z,10) = gen_0; /* dummy: we MUST have lg(bnf) != lg(nf) */
  return z;
}

static GEN
bnftosbnf(GEN bnf)
{
  GEN y = cgetg(13,t_VEC), nf  = gel(bnf,7), T = gel(nf,1), res = gel(bnf,8);

  gel(y,1) = T;
  gel(y,2) = gmael(nf,2,1);
  gel(y,3) = gel(nf,3);
  gel(y,4) = gel(nf,7);
  gel(y,5) = gel(nf,6);
  gel(y,6) = gen_0; /* FIXME: unused */
  gel(y,7) = gel(bnf,1);
  gel(y,8) = gel(bnf,2);
  gel(y,9) = codeprimes(gel(bnf,5), degpol(T));
  gel(y,10) = mkvec2(gmael(res,4,1), nf_to_scalar_or_basis(nf,gmael(res,4,2)));
  gel(y,11) = matalgtobasis(bnf, gel(res,5));
  (void)check_and_build_matal(bnf);
  gel(y,12) = gel(bnf,10); return y;
}
GEN
bnfcompress(GEN bnf)
{
  pari_sp av = avma;
  bnf = checkbnf(bnf);
  return gerepilecopy(av, bnftosbnf( checkbnf(bnf) ));
}

static GEN
sbnf2bnf(GEN sbnf, long prec)
{
  long j, k, l, n;
  pari_sp av = avma;
  GEN bas, ro, nf, A, fu, FU, L;
  GEN pfc, C, clgp, clgp2, res, y, W, zu, matal, Vbase;
  nfbasic_t T;

  if (typ(sbnf) != t_VEC || lg(sbnf) != 13) pari_err(typeer,"bnfmake");
  if (prec < DEFAULTPREC) prec = DEFAULTPREC;

  nfbasic_from_sbnf(sbnf, &T);
  ro = gel(sbnf,5);
  fu = gel(sbnf,11);
  if (prec > gprecision(ro)) ro = get_roots(T.x,T.r1,prec);
  nf = nfbasic_to_nf(&T, ro, prec);
  bas = gel(nf,7);

  A = get_archclean(nf, fu, prec, 1);
  if (!A) pari_err(precer, "bnfmake");

  prec = gprecision(ro);
  matal = check_and_build_matal(sbnf);
  C = get_archclean(nf,matal,prec,0);
  if (!C) pari_err(precer, "bnfmake");

  pfc = gel(sbnf,9);
  l = lg(pfc);
  Vbase = cgetg(l,t_COL);
  L = decode_pr_lists(nf, pfc);
  n = degpol(nf[1]);
  for (j=1; j<l; j++) gel(Vbase,j) = decodeprime(gel(pfc,j), L, n);
  W = gel(sbnf,7);
  class_group_gen(nf,W,C,Vbase,prec,NULL, &clgp,&clgp2);

  zu = gel(sbnf,10);
  zu = mkvec2(gel(zu,1), nf_to_scalar_or_alg(nf, gel(zu,2)));

  l = lg(fu); FU = cgetg(l, t_VEC);
  for (k=1; k < l; k++) gel(FU,k) = coltoliftalg(nf, gel(fu,k));
  res = get_clfu(clgp, get_regulator(A), zu, FU);
  y = buchall_end(nf,res,clgp2,W,gel(sbnf,8),A,C,Vbase);
  y[10] = sbnf[12]; return gerepilecopy(av,y);
}

GEN
bnfinit0(GEN P, long flag, GEN data, long prec)
{
  double c1 = 0.3, c2 = 0.3;
  long fl, nbrelpid = 4;

  if (typ(P) == t_VEC && lg(P) == 13) return sbnf2bnf(P, prec); /* sbnf */
  if (data)
  {
    long lx = lg(data);
    if (typ(data) != t_VEC || lx > 5) pari_err(typeer,"bnfinit");
    switch(lx)
    {
      case 4: nbrelpid = itos(gel(data,3));
      case 3: c2 = gtodouble( gel(data,2));
      case 2: c1  = gtodouble( gel(data,1));
    }
  }
  switch(flag)
  {
    case 2:
    case 0: fl = 0; break;
    case 1: fl = nf_FORCE; break;
    default: pari_err(flagerr,"bnfinit");
      return NULL; /* not reached */
  }
  return Buchall(P, c1, c2, nbrelpid, fl, prec);
}

static GEN
Buchall_deg1(GEN nf)
{
  GEN v = cgetg(1,t_VEC), m = cgetg(1,t_MAT);
  GEN W, A, B, C, Vbase, res;
  GEN fu = v, R = gen_1, zu = mkvec2(gen_2, gen_m1);
  GEN clg1 = mkvec3(gen_1,v,v), clg2 = mkvec3(m,v,v);

  W = A = B = C = m;
  Vbase = cgetg(1,t_COL);
  res = get_clfu(clg1, R, zu, fu);
  return buchall_end(nf,res,clg2,W,B,A,C,Vbase);
}

/* return (small set of) indices of columns generating the same lattice as x.
 * Assume HNF(x) is inexpensive (few rows, many columns).
 * Dichotomy approach since interesting columns may be at the very end */
GEN
extract_full_lattice(GEN x)
{
  long dj, j, k, l = lg(x);
  GEN h, h2, H, v;

  if (l < 200) return NULL; /* not worth it */

  v = cget1(l, t_VECSMALL);
  H = ZM_hnf(x);
  h = cgetg(1, t_MAT);
  dj = 1;
  for (j = 1; j < l; )
  {
    pari_sp av = avma;
    long lv = lg(v);

    for (k = 0; k < dj; k++) v[lv+k] = j+k;
    setlg(v, lv + dj);
    h2 = ZM_hnf(vecpermute(x, v));
    if (ZM_equal(h, h2))
    { /* these dj columns can be eliminated */
      avma = av; setlg(v, lv);
      j += dj;
      if (j >= l) break;
      dj <<= 1;
      if (j + dj >= l) { dj = (l - j) >> 1; if (!dj) dj = 1; }
    }
    else if (dj > 1)
    { /* at least one interesting column, try with first half of this set */
      avma = av; setlg(v, lv);
      dj >>= 1; /* > 0 */
    }
    else
    { /* this column should be kept */
      if (ZM_equal(h2, H)) break;
      h = h2; j++;
    }
  }
  return v;
}

static void
init_rel(RELCACHE_t *cache, FB_t *F, long RU)
{
  const long RELSUP = 5;
  const long n = F->KC + RU-1 + RELSUP; /* expected # of needed relations */
  long i, j, k, p;
  GEN c, P;
  REL_t *rel;

  if (DEBUGLEVEL) fprintferr("KCZ = %ld, KC = %ld, n = %ld\n", F->KCZ,F->KC,n);
  reallocate(cache, 10*n + 50); /* make room for lots of relations */
  cache->chk = cache->base;
  cache->end = cache->base + n;
  for (rel = cache->base + 1, i = 1; i <= F->KCZ; i++)
  { /* trivial relations (p) = prod P^e */
    p = F->FB[i]; P = F->LV[p];
    if (!isclone(P)) continue;

    /* all prime divisors in FB */
    c = col_0(F->KC); k = F->iLP[p];
    rel->nz = k+1;
    rel->R  = c; c += k;
    rel->ex = NULL;
    rel->m  = NULL;
    rel->pow= NULL; /* = F->pow */
    for (j = lg(P)-1; j; j--) c[j] = itos(gmael(P,j,3));
    rel++;
  }
  cache->last = rel - 1;
  if (DEBUGLEVEL)
    for (i = 1, rel = cache->base + 1; rel <= cache->last; rel++, i++)
      dbg_rel(i, rel->R);
}

static void
shift_embed(GEN G, GEN Gtw, long a, long r1)
{
  long j, k, l = lg(G);
  if (a <= r1)
    for (j=1; j<l; j++) gcoeff(G,a,j) = gcoeff(Gtw,a,j);
  else
  {
    k = (a<<1) - r1;
    for (j=1; j<l; j++)
    {
      gcoeff(G,k-1,j) = gcoeff(Gtw,k-1,j);
      gcoeff(G,k  ,j) = gcoeff(Gtw,k,  j);
    }
  }
}

/* G where embeddings a and b are multiplied by 2^10 */
static GEN
shift_G(GEN G, GEN Gtw, long a, long b, long r1)
{
  GEN g = shallowcopy(G);
  if (a != b) shift_embed(g,Gtw,a,r1);
  shift_embed(g,Gtw,b,r1); return g;
}

static void
compute_vecG(GEN nf, FB_t *F, long n)
{
  GEN G0, Gtw0, vecG, G = gmael(nf,5,2);
  long e, i, j, ind, r1 = nf_get_r1(nf), r = lg(G)-1;
  if (n == 1) { F->G0 = G0 = ground(G); F->vecG = mkvec( G0 ); return; }
  for (e = 32;;)
  {
    G = gmul2n(G, e);
    G0 = ground(G); if (rank(G0) == r) break; /* maximal rank ? */
  }
  Gtw0 = ground(gmul2n(G, 10));
  vecG = cgetg(1 + n*(n+1)/2,t_VEC);
  for (ind=j=1; j<=n; j++)
    for (i=1; i<=j; i++) gel(vecG,ind++) = shift_G(G0,Gtw0,i,j,r1);
  if (DEBUGLEVEL) msgtimer("weighted G matrices");
  F->G0 = G0; F->vecG = vecG;
}

GEN
Buchall(GEN P, double cbach, double cbach2, long nbrelpid, long flun, long prec)
{
  pari_sp av0 = avma, av, av2;
  long PRECREG, N, R1, R2, RU, LIMC, LIMC2, lim, zc, i, jid;
  long nreldep, sfb_trials, need, precdouble = 0, precadd = 0;
  double drc, LOGD, LOGD2;
  GEN fu, zu, nf, D, A, W, R, Res, z, h, L_jid, PERM;
  GEN res, L, resc, B, C, C0, lambda, dep, clg1, clg2, Vbase;
  const char *precpb = NULL;
  const long minsFB = 3;
  int FIRST = 1;
  RELCACHE_t cache;
  FB_t F;
  GRHcheck_t G, *GRHcheck = &G;
  FACT *fact;

  if (DEBUGLEVEL) (void)timer2();
  P = get_nfpol(P, &nf);
  if (nf)
    PRECREG = nf_get_prec(nf);
  else
  {
    PRECREG = max(prec, MEDDEFAULTPREC);
    nf = nfinit(P, PRECREG);
    if (lg(nf)==3) { /* P non-monic and nfinit CHANGEd it ? */
      pari_warn(warner,"non-monic polynomial. Change of variables discarded");
      nf = gel(nf,1);
    }
  }
  N = degpol(P);
  if (N <= 1) return gerepilecopy(av0, Buchall_deg1(nf));
  zu = rootsof1(nf);
  gel(zu,2) = coltoliftalg(nf, gel(zu,2));
  if (DEBUGLEVEL) msgtimer("nfinit & rootsof1");

  nf_get_sign(nf, &R1, &R2); RU = R1+R2;
  compute_vecG(nf, &F, min(RU, 9));
  D = absi(gel(nf,3)); drc = gtodouble(D);
  if (DEBUGLEVEL) fprintferr("R1 = %ld, R2 = %ld\nD = %Ps\n",R1,R2, D);
  LOGD = log(drc); LOGD2 = LOGD*LOGD;
  lim = (long) (exp(-N + R2 * log(4/PI)) * sqrt(2*PI*N*drc));
  if (lim < 3) lim = 3;
  if (cbach > 12.) {
    if (cbach2 < cbach) cbach2 = cbach;
    cbach = 12.;
  }
  if (cbach <= 0.) pari_err(talker,"Bach constant <= 0 in buch");

  /* resc ~ sqrt(D) w / 2^r1 (2pi)^r2 = hR / Res(zeta_K, s=1) */
  resc = gdiv(mulri(gsqrt(D,DEFAULTPREC), gel(zu,1)),
	      gmul2n(gpowgs(mppi(DEFAULTPREC), R2), RU));
  av = avma; cache.base = NULL; F.subFB = NULL;
  init_GRHcheck(GRHcheck, N, R1, LOGD);

START:
  if (!FIRST) cbach = check_bach(cbach,12.);
  FIRST = 0; avma = av;
  if (cache.base) delete_cache(&cache);
  if (F.subFB) delete_FB(&F);
  LIMC = (long)(cbach*LOGD2);
  if (LIMC < 20) { LIMC = 20; cbach = (double)LIMC / LOGD2; }
  LIMC2 = max(3 * N, (long)(cbach2*LOGD2));
  if (LIMC2 < LIMC) LIMC2 = LIMC;
  if (DEBUGLEVEL) { fprintferr("LIMC = %ld, LIMC2 = %ld\n",LIMC,LIMC2); }

  Res = FBgen(&F, nf, N, LIMC2, LIMC, GRHcheck);
  fact = (FACT*)stackmalloc((F.KC+1)*sizeof(FACT));
  if (!Res) goto START;
  GRHcheck = NULL;
  if (!subFBgen(&F, nf, min(lim,LIMC2) + 0.5, minsFB)) goto START;
  PERM = shallowcopy(F.perm); /* to be restored in case of precision increase */
  av2 = avma;
  init_rel(&cache, &F, RU); /* trivial relations */
  if (nbrelpid > 0) {
    small_norm(&cache, &F, nf, nbrelpid, LOGD, LIMC2, fact);
    avma = av2;
  }

  /* Random relations */
  W = L_jid = NULL;
  jid = sfb_trials = nreldep = 0;
  need = cache.end - cache.last;
  if (need > 0)
  {
    if (DEBUGLEVEL) fprintferr("\n#### Looking for random relations\n");
MORE:
    pre_allocate(&cache, need); cache.end = cache.last + need;
    if (++nreldep > MAXRELSUP) {
      if (++sfb_trials <= SFB_MAX)
	F.sfb_chg = sfb_INCREASE;
      else if (cbach < 4)
	goto START;
    }
    if (F.sfb_chg) {
      if (!subFB_change(&F, nf, L_jid)) goto START;
      jid = nreldep = 0;
    }
    if (F.newpow) powFBgen(&F, &cache, nf);
    if (!F.sfb_chg && !rnd_rel(&cache,&F, nf, L_jid, &jid, fact)) goto START;
    L_jid = NULL;
  }
PRECPB:
  if (precpb)
  {
    pari_sp av3 = avma;
    GEN nf0 = nf;
    if (precadd) { PRECREG += precadd; precadd = 0; }
    else           PRECREG = (PRECREG<<1)-2;
    if (DEBUGLEVEL)
    {
      char str[64]; sprintf(str,"Buchall (%s)",precpb);
      pari_warn(warnprec,str,PRECREG);
    }
    nf = gclone( nfnewprec_shallow(nf, PRECREG) );
    if (precdouble) gunclone(nf0);
    avma = av3; precdouble++; precpb = NULL;

    if (F.pow && F.pow->arc) { gunclone(F.pow->arc); F.pow->arc = NULL; }
    for (i = 1; i < lg(PERM); i++) F.perm[i] = PERM[i];
    cache.chk = cache.base; W = NULL; /* recompute arch components + reduce */
  }
  { /* Reduce relation matrices */
    long l = cache.last - cache.chk + 1, j;
    GEN M = gmael(nf, 5, 1), mat = cgetg(l, t_VEC), emb = cgetg(l, t_MAT);
    int first = (W == NULL); /* never reduced before */
    REL_t *rel;

    if (F.pow && !F.pow->arc) powFB_fill(&cache, M);
    for (j=1,rel = cache.chk + 1; rel <= cache.last; rel++,j++)
    {
      gel(mat,j) = rel->R;
      gel(emb,j) = get_log_embed(rel, M, RU, R1, PRECREG);
    }
    if (first) {
      C = emb;
      W = hnfspec_i(mat, F.perm, &dep, &B, &C, lg(F.subFB)-1);
    }
    else
      W = hnfadd_i(W, F.perm, &dep, &B, &C, mat, emb);
    gerepileall(av2, 4, &W,&C,&B,&dep);
    cache.chk = cache.last;
    need = lg(dep)>1? lg(dep[1])-1: lg(B[1])-1;
    if (need)
    { /* dependent rows */
      if (need > 5)
      {
        if (need > 20 && !first) F.sfb_chg = sfb_CHANGE;
        L_jid = vecslice(F.perm, 1, need);
        vecsmall_sort(L_jid); jid = 0;
      }
      goto MORE;
    }
  }
  need = 1;
  zc = (cache.last - cache.base) - (lg(B)-1) - (lg(W)-1);
  A = vecslice(C, 1, zc); /* cols corresponding to units */
  R = compute_multiple_of_R(A, RU, N, &lambda);
  if (!R)
  { /* not full rank for units */
    if (DEBUGLEVEL) fprintferr("regulator is zero.\n");
    goto MORE;
  }
  if (!lambda) { precpb = "bestappr"; goto PRECPB; }

  h = ZM_det_triangular(W);
  if (DEBUGLEVEL) fprintferr("\n#### Tentative class number: %Ps\n", h);

  z = mulrr(Res, resc); /* ~ hR if enough relations, a multiple otherwise */
  switch (compute_R(lambda, divir(h,z), &L, &R))
  {
    case fupb_RELAT: goto MORE; /* not enough relations */
    case fupb_PRECI: /* prec problem unless we cheat on Bach constant */
      if ((precdouble&7) < 7 || cbach>2) { precpb = "compute_R"; goto PRECPB; }
    /* fall through */
    case fupb_BACH: goto START;
  }
  /* DONE */

  if (F.KCZ2 > F.KCZ)
  {
    if (F.newpow) powFBgen(&F, NULL, nf);
    if (F.sfb_chg) {
      if (!subFB_change(&F, nf, L_jid)) goto START;
      powFBgen(&F, NULL, nf);
    }
    if (!be_honest(&F, nf, fact)) goto START;
  }
  F.KCZ2 = 0; /* be honest only once */

  /* fundamental units */
  {
    pari_sp av3 = avma;
    GEN AU, U, H, v = extract_full_lattice(L); /* L may be very large */
    long e;
    if (v)
    {
      A = vecpermute(A, v);
      L = vecpermute(L, v);
    }
    /* arch. components of fund. units */
    H = ZM_hnflll(L, &U, 1); U = vecslice(U, lg(U)-(RU-1), lg(U)-1);
    U = ZM_mul(U, lllint(H));
    AU = RgM_mul(A, U);
    A = cleanarch(AU, N, PRECREG);
    if (DEBUGLEVEL) msgtimer("cleanarch");
    if (!A) {
      precadd = (DEFAULTPREC-2) + divsBIL( gexpo(AU) ) - gprecision(AU);
      if (precadd <= 0) precadd = 1;
      precpb = "cleanarch"; goto PRECPB;
    }
    fu = getfu(nf, &A, flun & nf_FORCE, &e, PRECREG);
    if (e <= 0 && (flun & nf_FORCE))
    {
      if (e < 0) precadd = (DEFAULTPREC-2) + divsBIL( (-e) );
      avma = av3; precpb = "getfu"; goto PRECPB;
    }
  }
  /* class group generators */
  i = lg(C)-zc; C += zc; C[0] = evaltyp(t_MAT)|evallg(i);
  C0 = C; C = cleanarch(C, N, PRECREG);
  if (!C) {
    precadd = (DEFAULTPREC-2) + divsBIL( gexpo(C0) ) - gprecision(C0);
    if (precadd <= 0) precadd = 1;
    precpb = "cleanarch"; goto PRECPB;
  }

  delete_cache(&cache); delete_FB(&F);
  Vbase = vecpermute(F.LP, F.perm);
  class_group_gen(nf,W,C,Vbase,PRECREG,NULL, &clg1, &clg2);
  res = get_clfu(clg1, R, zu, fu);
  res = buchall_end(nf,res,clg2,W,B,A,C,Vbase);
  res = gerepilecopy(av0, res); if (precdouble) gunclone(nf);
  return res;
}
