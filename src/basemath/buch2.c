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
    if (!isintzero(O)) return O;
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

typedef struct subFB_t {
  GEN subFB;
  struct subFB_t *old;
} subFB_t;

/* a factor base contains only non-inert primes
 * KC = # of P in factor base (p <= n, NP <= n2)
 * KC2= # of P assumed to generate class group (NP <= n2)
 *
 * KCZ = # of rational primes under ideals counted by KC
 * KCZ2= same for KC2 */

typedef struct FB_t {
  GEN FB; /* FB[i] = i-th rational prime used in factor base */
  GEN LP; /* vector of all prime ideals in FB */
  GEN *LV; /* LV[p] = vector of P|p, NP <= n2
            * isclone() is set for LV[p] iff all P|p are in FB
            * LV[i], i not prime or i > n2, is undefined! */
  GEN iLP; /* iLP[p] = i such that LV[p] = [LP[i],...] */
  GEN id2; /* id2[i] = powers of ideal i */
  GEN L_jid; /* indexes of "useful" prime ideals for rnd_rel */
  long KC, KCZ, KCZ2;
  GEN subFB; /* LP o subFB =  part of FB used to build random relations */
  int sfb_chg; /* need to change subFB ? */
  int newpow; /* need to compute powFB */
  int newarc; /* need to compute archimedean components */
  GEN perm; /* permutation of LP used to represent relations [updated by
               hnfspec/hnfadd: dense rows come first] */
  GEN vecG, G0;
  GEN idealperm; /* permutation of ideals under field automorphisms */
  GEN minidx; /* minidx[i] min ideal in orbit of LP[i] under field autom */
  long orbits; /* number of ideal orbits */
  subFB_t *allsubFB; /* all subFB's used */
  GEN embperm; /* permutations of the complex embeddings */
  GEN invs; /* inverse of automorphism */
} FB_t;

enum { sfb_CHANGE = 1, sfb_INCREASE = 2 };

typedef struct REL_t {
  GEN R; /* relation vector as t_VECSMALL; clone */
  long nz; /* index of first non-zero elt in R (hash) */
  GEN m; /* pseudo-minimum yielding the relation; clone */
  long relorig; /* relation this one is an image of */
  long relaut; /* automorphim used to compute this relation from the original */
  GEN junk[1]; /*make sure sizeof(struct) is a power of two.*/
} REL_t;

typedef struct RELCACHE_t {
  REL_t *chk; /* last checkpoint */
  REL_t *base; /* first rel found */
  REL_t *last; /* last rel found so far */
  REL_t *end; /* target for last relation. base <= last <= end */
  size_t len; /* number of rels pre-allocated in base */
  long relsup; /* how many linearly dependent relations to we allow */
  GEN basis; /* mod p basis (generating family actually) */
  ulong missing; /* missing vectors in generating family above */
} RELCACHE_t;

static void
wr_rel(GEN col)
{
  long i, l = lg(col);
  fprintferr("\nrel = ");
  for (i=1; i<l; i++)
    if (col[i]) fprintferr("%ld^%ld ",i,col[i]);
  fprintferr("\n");
}
static void
dbg_rel(long s, GEN col)
{
  if (DEBUGLEVEL == 1) fprintferr("%ld ",s);
  else { fprintferr("cglob = %ld. ", s); wr_rel(col); }
  flusherr();
}
static void
dbg_newrel(RELCACHE_t *cache)
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


static void
delete_cache(RELCACHE_t *M)
{
  REL_t *rel;
  for (rel = M->base+1; rel <= M->last; rel++)
  {
    gunclone(rel->R);
    if (!rel->m) continue;
    gunclone(rel->m);
  }
  pari_free((void*)M->base); M->base = NULL;
}

static void
unclone_subFB(FB_t *F)
{
  subFB_t *sub = F->allsubFB;
  GEN id2 = F->id2;
  long id;

  while(sub) { subFB_t *s = sub; sub = s->old; pari_free(s); }
  /* can't do it in a simple way above because of the Galois action,
     see WARNING in powFBgen */
  for (id = 1; id <= F->KC; id++)
    if (gel(id2, id) != gen_0)
    {
      gunclone(gel(id2, id));
      gel(id2, id) = gen_0;
    }
}

static void
delete_FB(FB_t *F)
{
  unclone_subFB(F);
  gunclone(F->minidx);
  gunclone(F->idealperm);
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

/* don't take P|p all other Q|p are already there */
static int
bad_subFB(FB_t *F, long t)
{
  GEN LP, P = gel(F->LP,t);
  long p = pr_get_smallp(P);
  LP = F->LV[p];
  return (isclone(LP) && t == F->iLP[p] + lg(LP)-1);
}

static void
assign_subFB(FB_t *F, GEN yes, long iyes)
{
  subFB_t *sub;
  long i, lv;

  /* single malloc for struct + GEN */
  lv = sizeof(subFB_t) + iyes*sizeof(long);
  sub = (subFB_t *)pari_malloc(lv);
  sub->subFB = (GEN)&sub[1];
  sub->old = F->allsubFB;
  F->allsubFB = sub;
  for (i = 0; i < iyes; i++) sub->subFB[i] = yes[i];
  F->subFB = sub->subFB;
  F->newpow = 1;
  F->newarc = 1;
}

/*
 * Determine the permutation of the ideals made by each field automorphism.
 */
static void
FB_aut_perm(FB_t *F, GEN nf, GEN auts, GEN cyclic)
{
  pari_sp av0 = avma;
  long i, KC = F->KC, nauts = lg(auts);
  GEN minidx = zero_Flv(KC), perm = zero_Flm_copy(KC, nauts-1);

  if (nauts == 1)
  {
    for (i = 1; i <= KC; i++) minidx[i] = i;
    F->orbits = KC;
  }
  else
  {
    long j, m;
    F->orbits = 0;
    for (m = 1; m < lg(cyclic); m++)
    {
      GEN thiscyc = gel(cyclic, m);
      long k0 = thiscyc[1];
      GEN aut = gel(auts, k0), permk0 = gel(perm, k0), ppermk;
      i = 1;
      while (i <= KC)
      {
        pari_sp av2 = avma;
        GEN seen = zero_Flv(KC), P = gel(F->LP, i);
        long imin = i, p, f, l;
        p = pr_get_p(P)[2];
        f = pr_get_f(P);
        do
        {
          if (++i > KC) break;
          P = gel(F->LP, i);
        }
        while (p == pr_get_p(P)[2] && f == pr_get_f(P));
        for (j = imin; j < i; j++)
        {
          GEN img = ZM_ZC_mul(aut, pr_get_gen(gel(F->LP, j)));
          for (l = imin; l < i; l++)
            if (!seen[l] && nfval(nf, img, gel(F->LP, l)))
            {
              seen[l] = 1; permk0[j] = l; break;
            }
        }
        avma = av2;
      }
      for (ppermk = permk0, i = 2; i < lg(thiscyc); i++)
      {
        GEN permk = gel(perm, thiscyc[i]);
        for (j = 1; j <= KC; j++) permk[j] = permk0[ppermk[j]];
        ppermk = permk;
      }
    }
    for (j = 1; j <= KC; j++)
    {
      if (minidx[j]) continue;
      F->orbits++;
      minidx[j] = j;
      for (i = 1; i < nauts; i++) minidx[coeff(perm, j, i)] = j;
    }
  }
  F->minidx = gclone(minidx);
  F->idealperm = gclone(perm);
  avma = av0;
}

/* set subFB.
 * Fill F->perm (if != NULL): primes ideals sorted by increasing norm (except
 * the ones in subFB come first [dense rows for hnfspec]) */
static int
subFBgen(FB_t *F, GEN nf, GEN auts, GEN cyclic, double PROD, long minsFB)
{
  GEN y, perm, yes, no;
  long i, j, k, iyes, ino, lv = F->KC + 1;
  double prod;
  pari_sp av;

  F->LP   = cgetg(lv, t_VEC);
  F->L_jid = F->perm = cgetg(lv, t_VECSMALL);
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
    if (bad_subFB(F, t)) { no[ino++] = t; continue; }

    yes[iyes++] = t;
    prod *= (double)itos(gel(y,t));
    if (iyes > minsFB && prod > PROD) break;
  }
  if (i == lv) return 0;
  setlg(yes, iyes);
  for (j=1; j<iyes; j++)     F->perm[j] = yes[j];
  for (i=1; i<ino; i++, j++) F->perm[j] =  no[i];
  for (   ; j<lv; j++)       F->perm[j] =  perm[j];
  F->allsubFB = NULL;
  FB_aut_perm(F, nf, auts, cyclic);
  assign_subFB(F, yes, iyes);
  if (DEBUGLEVEL)
    msgtimer("sub factorbase (%ld elements) and ideal permutations",lg(F->subFB)-1);
  avma = av; return 1;
}
static int
subFB_change(FB_t *F)
{
  long i, iyes, minsFB, lv = F->KC + 1, l = lg(F->subFB)-1;
  pari_sp av = avma;
  GEN yes, L_jid = F->L_jid;

  switch (F->sfb_chg)
  {
    case sfb_INCREASE: minsFB = l + 1; break;
    default: minsFB = l; break;
  }

  yes = cgetg(minsFB+1, t_VECSMALL); iyes = 1;
  if (L_jid)
  {
    for (i = 1; i < lg(L_jid); i++)
    {
      yes[iyes++] = L_jid[i];
      if (iyes > minsFB) break;
    }
  }
  else i = 1;
  if (iyes <= minsFB)
  {
    for ( ; i < lv; i++)
    {
      yes[iyes++] = F->perm[i];
      if (iyes > minsFB) break;
    }
    if (i == lv) return 0;
  }
  if (zv_equal(F->subFB, yes))
  {
    if (DEBUGLEVEL) fprintferr("*** NOT Changing sub factor base\n");
  }
  else
  {
    if (DEBUGLEVEL) fprintferr("*** Changing sub factor base\n");
    assign_subFB(F, yes, iyes);
  }
  F->sfb_chg = 0;
  avma = av; return 1;
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

static GEN
countf(GEN LP)
{
  long i, nP = lg(LP)-1, maxf = pr_get_f(gel(LP, nP));
  GEN nbf = const_vecsmall(maxf, 0);
  nbf[maxf] = 1;
  for (i = 1; i < nP; i++)
  {
    long f = pr_get_f( gel(LP,i) );
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
  S->checkok = 0;
}

int
GRHok(GRHcheck_t *S, double L, double SA, double SB)
{
  if (S->checkok || S->cD + (S->cN + 2*SB) / L - 2*SA < -1e-8) return 1;
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
      if (!S->checkok)
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
    a = a? divri(mulir(a,Res),b): divru(mulur(p-1,Res),p);
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
  F->perm = NULL;
  F->L_jid = NULL; S->checkok = 1; return Res;
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

/* can we factor m/I ? [m in I from idealpseudomin_nonscalar], NI = norm I */
static long
factorgen(FB_t *F, GEN nf, GEN I, GEN NI, GEN m, FACT *fact)
{
  long e, r1 = nf_get_r1(nf);
  GEN M = nf_get_M(nf);
  GEN N = divri(norm_by_embed(r1, RgM_RgC_mul(M,m)), NI); /* ~ N(m/I) */
  N = grndtoi(N, &e);
  if (e > -1) return 0;
  return can_factor(F, nf, I, m, absi(N), fact);
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
    z = gequal0(im)? re: mkcomplex(re, im);
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
not_given(long reason)
{
  if (DEBUGLEVEL)
    switch(reason)
    {
      case fupb_LARGE:
        pari_warn(warner,"fundamental units too large, not given");
        break;
      case fupb_PRECI:
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
getfu(GEN nf, GEN *ptA, long *pte, long prec)
{
  GEN p1, p2, u, y, matep, A, vec, T = nf_get_pol(nf), M = nf_get_M(nf);
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
  if (typ(u) != t_MAT) return not_given(fupb_PRECI);

  y = RgM_mul(matep,u);
  if (expgexpo(y) > 20) { *pte = LONG_MAX; return not_given(fupb_LARGE); }

  if (prec <= 0) prec = gprecision(A);
  y = RgM_solve_realimag(M, gexp(y,prec));
  if (!y) return not_given(fupb_PRECI);
  y = grndtoi(y, &e);
  *pte = -e;
  if (e >= 0) return not_given(fupb_PRECI);
  for (j=1; j<RU; j++)
    if (!gequal1(idealnorm(nf, gel(y,j)))) break;
  if (j < RU) { *pte = 0; return not_given(fupb_PRECI); }
  A = RgM_mul(A,u);

  /* y[i] are unit generators. Normalize: smallest L2 norm + lead coeff > 0 */
  y = coltoliftalg(nf, y);
  vec = cgetg(RU+1,t_COL);
  p1 = PiI2n(0,prec); for (i=1; i<=R1; i++) gel(vec,i) = p1;
  p2 = PiI2n(1,prec); for (   ; i<=RU; i++) gel(vec,i) = p2;
  for (j=1; j<RU; j++)
  {
    GEN u = gel(y,j), v = QXQ_inv(u, T);
    if (gcmp(RgX_fpnorml2(v,DEFAULTPREC),
             RgX_fpnorml2(u,DEFAULTPREC)) < 0)
    {
      gel(A,j) = RgC_neg(gel(A,j));
      u = v;
    }
    if (gsigne(leading_term(u)) < 0)
    {
      gel(A,j) = RgC_add(gel(A,j), vec);
      u = RgX_neg(u);
    }
    gel(y,j) = u;
  }
  if (DEBUGLEVEL) msgtimer("getfu");
  *ptA = A; return y;
}

GEN
init_units(GEN BNF)
{
  GEN bnf = checkbnf(BNF), funits = bnf_get_fu_nocheck(bnf), v;
  long i, l;
  if (typ(funits) == t_MAT)
  {
    pari_sp av = avma;
    GEN nf = bnf_get_nf(bnf), A = bnf_get_logfu(bnf);
    funits = gerepilecopy(av, getfu(nf, &A, &l, 0));
    if (typ(funits) == t_MAT)
      pari_err(talker, "bnf accuracy too low to compute units on the fly");
  }
  l = lg(funits) + 1;
  v = cgetg(l, t_VEC); gel(v,1) = bnf_get_tuU(bnf);
  for (i = 2; i < l; i++) gel(v,i) = gel(funits,i-1);
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
  pari_sp av=avma;
  GEN N = gen_1, P, p;
  long i, c = lg(E);
  for (i=1; i<c; i++)
  {
    GEN ex = gel(E,i);
    long s = signe(ex);
    if (!s) continue;

    P = gel(G,i); p = pr_get_p(P);
    N = mulii(N, powii(p, mului(pr_get_f(P), ex)));
  }
  if (C) N = mulii(N, pr_norm(C));
  return gerepileuptoint(av, N);
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
      ne = powii(n,e);
      de = equalii(n, gcoeff(I,1,1))? ne: powii(gcoeff(I,1,1), e);
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
      if (!L[p]) gel(L,p) = vectrunc_init(N+1);
      vectrunc_append(gel(L,p), pr);
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
      if (!L[p]) gel(L,p) = vecsmalltrunc_init(N+1);
      vecsmalltrunc_append(gel(L,p), i);
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
  GEN vecG, z, ex, y, x0, Nx = ZM_det_triangular(x);
  long nbtest_lim, nbtest, i, j, ru, lgsub;
  pari_sp av;

  /* try without reduction if x is small.
   * N.B. can_factor() destroys its NI argument */
  if (gexpo(gcoeff(x,1,1)) < 100 &&
      can_factor(F, nf, x, NULL, icopy(Nx), fact)) return NULL;

  av = avma;
  y = idealpseudomin_nonscalar(x, nf_get_roundG(nf));
  if (factorgen(F, nf, x, Nx, y, fact)) return y;
  avma = av;

  /* reduce in various directions */
  ru = lg(nf_get_roots(nf));
  vecG = cgetg(ru, t_VEC);
  for (j=1; j<ru; j++)
  {
    gel(vecG,j) = nf_get_Gtwist1(nf, j);
    av = avma;
    y = idealpseudomin_nonscalar(x, gel(vecG,j));
    if (factorgen(F, nf, x, Nx, y, fact)) return y;
    avma = av;
  }

  /* tough case, multiply by random products */
  lgsub = 3;
  ex = cgetg(lgsub, t_VECSMALL);
  z  = init_famat(NULL);
  x0 = init_famat(x);
  nbtest = 1; nbtest_lim = 4;
  for(;;)
  {
    GEN I, NI, id = x0;
    av = avma;
    if (DEBUGLEVEL>2) fprintferr("# ideals tried = %ld\n",nbtest);
    for (i=1; i<lgsub; i++)
    {
      ex[i] = random_bits(RANDOM_BITS);
      if (ex[i])
      { /* avoid prec pb: don't let id become too large as lgsub increases */
        if (id != x0) id = idealred(nf,id);
        z[1] = Vbase[i];
        id = extideal_HNF_mul(nf, id, idealpowred(nf,z,utoipos(ex[i])));
      }
    }
    if (id == x0) continue;

    I = gel(id,1); NI = ZM_det_triangular(I);
    for (j=1; j<ru; j++)
    {
      pari_sp av2 = avma;
      y = idealpseudomin_nonscalar(I, gel(vecG,j));
      if (factorgen(F, nf, I, NI, y, fact))
      {
        for (i=1; i<lgsub; i++)
          if (ex[i]) add_to_fact(Vbase_to_FB(F,gel(Vbase,i)), ex[i], fact);
        return famat_mul(gel(id,2), y);
      }
      avma = av2;
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
  ulong p, pmax, bound, boundp = itou_or_0(BOUND);
  FACT *fact;
  GEN nf = bnf_get_nf(bnf), f = nf_get_index(nf), dK = nf_get_disc(nf);
  GEN Vbase, fb, gp;
  byteptr d = diffptr + 1;
  FB_t F;

  bound = maxprime();
  if (boundp && boundp < bound) bound = boundp;

  if (!is_pm1(f))
  {
    GEN D = nf_get_diff(nf), L;
    if (DEBUGLEVEL>1) fprintferr("**** Testing Different = %Ps\n",D);
    L = bnfisprincipal0(bnf, D, nf_FORCE);
    if (DEBUGLEVEL>1) fprintferr("     is %Ps\n", L);
  }
  /* sort factorbase for tablesearch */
  fb = gen_sort(gel(bnf,5), (void*)&cmp_prime_ideal, cmp_nodata);
  pmax = itou( pr_get_p(gel(fb, lg(fb)-1)) ); /* largest p in factorbase */
  Vbase = get_Vbase(bnf);
  (void)recover_partFB(&F, Vbase, nf_get_degree(nf));
  fact = (FACT*)stackmalloc((F.KC+1)*sizeof(FACT));

  /* loop up to min(maxprime, BOUND) */
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
  if (boundp == bound) { avma = av0; return; }

  /* finish looping up to BOUND */
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
static GEN famat_to_arch(GEN nf, GEN fa, long prec);
static GEN
triv_arch(GEN nf) { return zerovec(lg(nf_get_roots(nf))-1); }

/* Get archimedean components: [e_i Log( sigma_i(X) )], where X = primpart(x),
 * and e_i = 1 (resp 2.) for i <= R1 (resp. > R1) */
static GEN
get_arch(GEN nf, GEN x, long prec)
{
  long i, l, R1;
  GEN v;
  if (typ(x) == t_MAT) return famat_to_arch(nf,x,prec);
  x = nf_to_scalar_or_basis(nf,x);
  if (typ(x) != t_COL) return triv_arch(nf);
  x = RgM_RgC_mul(nf_get_M(nf), Q_primpart(x));
  l = lg(x);
  for (i=1; i < l; i++) if (gequal0(gabs(gel(x,i),prec))) return NULL;
  v = cgetg(l,t_VEC); R1 = nf_get_r1(nf);
  for (i=1; i<=R1; i++) gel(v,i) = glog(gel(x,i),prec);
  for (   ; i < l; i++) gel(v,i) = gmul2n(glog(gel(x,i),prec),1);
  return v;
}
static GEN
famat_to_arch(GEN nf, GEN fa, long prec)
{
  GEN g,e, y = NULL;
  long i,l;

  if (typ(fa) != t_MAT) pari_err(typeer,"famat_to_arch");
  if (lg(fa) == 1) return triv_arch(nf);
  g = gel(fa,1);
  e = gel(fa,2); l = lg(e);
  for (i=1; i<l; i++)
  {
    GEN t, x = nf_to_scalar_or_basis(nf, gel(g,i));
    /* multiplicative arch would be better (save logs), but exponents overflow
     * [ could keep track of expo separately, but not worth it ] */
    t = get_arch(nf,x,prec); if (!t) return NULL;
    if (gel(t,1) == gen_0) continue; /* rational */
    t = RgV_Rg_mul(t, gel(e,i));
    y = y? RgV_add(y,t): t;
  }
  return y ? y: triv_arch(nf);
}

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
scalar_get_arch_real(GEN nf, GEN u, GEN *emb)
{
  GEN v, logu;
  long i, s = signe(u), RU = lg(nf_get_roots(nf))-1, R1 = nf_get_r1(nf);

  if (!s) pari_err(talker,"0 in get_arch_real");
  v = cgetg(RU+1, t_COL);
  logu = logr_abs(u);
  for (i=1; i<=R1; i++) gel(v,i) = logu;
  if (i <= RU)
  {
    GEN logu2 = shiftr(logu,1);
    for (   ; i<=RU; i++) gel(v,i) = logu2;
  }
  *emb = const_col(RU, u); return v;
}

static int
low_prec(GEN x) { return gequal0(x) || (typ(x) == t_REAL && lg(x) == 3); }

/* For internal use. Get archimedean components: [e_i log( | sigma_i(x) | )],
 * with e_i = 1 (resp 2.) for i <= R1 (resp. > R1)
 * Return NULL if precision problem, and set *emb to the embeddings of x */
GEN
get_arch_real(GEN nf, GEN x, GEN *emb, long prec)
{
  long i, lx, R1;
  GEN v, t;

  if (typ(x) == t_MAT) return famat_get_arch_real(nf,x,emb,prec);
  x = nf_to_scalar_or_basis(nf,x);
  if (typ(x) != t_COL) return scalar_get_arch_real(nf, gtofp(x,prec), emb);
  R1 = nf_get_r1(nf);
  x = RgM_RgC_mul(nf_get_M(nf), x);
  lx = lg(x);
  v = cgetg(lx,t_COL);
  for (i=1; i<=R1; i++)
  {
    t = gabs(gel(x,i),prec); if (low_prec(t)) return NULL;
    gel(v,i) = glog(t,prec);
  }
  for (   ; i< lx; i++)
  {
    t = gnorm(gel(x,i)); if (low_prec(t)) return NULL;
    gel(v,i) = glog(t,prec);
  }
  *emb = x; return v;
}


GEN
init_red_mod_units(GEN bnf, long prec)
{
  GEN s = gen_0, p1,s1,mat, logfu = bnf_get_logfu(bnf);
  long i,j, RU = lg(logfu);

  if (RU == 1) return NULL;
  mat = cgetg(RU,t_MAT);
  for (j=1; j<RU; j++)
  {
    p1 = cgetg(RU+1,t_COL); gel(mat,j) = p1;
    s1 = gen_0;
    for (i=1; i<RU; i++)
    {
      gel(p1,i) = real_i(gcoeff(logfu,i,j));
      s1 = mpadd(s1, mpsqr(gel(p1,i)));
    }
    gel(p1,RU) = gen_0; if (mpcmp(s1,s) > 0) s = s1;
  }
  s = gsqrt(gmul2n(s,RU),prec);
  if (expo(s) < 27) s = utoipos(1UL << 27);
  return mkvec2(mat, s);
}

/* z computed above. Return unit exponents that would reduce col (arch) */
GEN
red_mod_units(GEN col, GEN z)
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
  if (!gequal1(gel(x,RU))) pari_err(bugparier,"red_mod_units");
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

static long
needed_bitprec(GEN x)
{
  long i, e = 0, l = lg(x);
  for (i = 1; i < l; i++)
  {
    GEN c = gel(x,i);
    long f = gexpo(c) - bit_accuracy(gprecision(c));
    if (f > e) e = f;
  }
  return e;
}

/* col = archimedian components of x, Nx = kNx^e its norm (e > 0, usually = 1),
 * dx a bound for its denominator. Return x or NULL (fail) */
GEN
isprincipalarch(GEN bnf, GEN col, GEN kNx, GEN e, GEN dx, long *pe)
{
  GEN nf, x, y, logfu, s, M;
  long N, R1, RU, i, prec = gprecision(col);
  bnf = checkbnf(bnf); nf = bnf_get_nf(bnf); M = nf_get_M(nf);
  if (!prec) prec = prec_arch(bnf);
  logfu = bnf_get_logfu(bnf);
  N = nf_get_degree(nf);
  R1 = nf_get_r1(nf);
  RU = (N + R1)>>1;
  col = cleanarch(col,N,prec); settyp(col, t_COL);
  if (!col) pari_err(precer, "isprincipalarch");
  if (RU > 1)
  { /* reduce mod units */
    GEN u, z = init_red_mod_units(bnf,prec);
    u = red_mod_units(col,z);
    if (!u && z) return NULL;
    if (u) col = RgC_add(col, RgM_RgC_mul(logfu, u));
  }
  s = divru(mulir(e, glog(kNx,prec)), N);
  for (i=1; i<=R1; i++) gel(col,i) = gexp(gadd(s, gel(col,i)),prec);
  for (   ; i<=RU; i++) gel(col,i) = gexp(gadd(s, gmul2n(gel(col,i),-1)),prec);
  /* d.alpha such that x = alpha \prod gj^ej */
  x = RgM_solve_realimag(M,col); if (!x) return NULL;
  x = RgC_Rg_mul(x, dx);
  y = grndtoi(x, pe);
  if (*pe > -5)
  {
    *pe = needed_bitprec(x);
    return NULL;
  }
  return RgC_Rg_div(y, dx);
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
  GEN nf   = bnf_get_nf(bnf);
  GEN clg2 = gel(bnf,9);
  FB_t F;
  GEN Vbase = get_Vbase(bnf);
  GEN L = recover_partFB(&F, Vbase, lg(x)-1);
  pari_sp av;
  FACT *fact;

  U = gel(clg2,1);
  cyc = bnf_get_cyc(bnf); c = lg(cyc)-1;
  gen = bnf_get_gen(bnf);
  ex = cgetg(c+1,t_COL);
  if (c == 0 && !(flag & (nf_GEN|nf_GENMAT|nf_GEN_IF_PRINCIPAL))) return ex;

  /* factor x */
  x = Q_primitive_part(x, &xc);
  av = avma;

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
    { if (!ZV_equal0(ex)) return gen_0; }
  else if (!(flag & (nf_GEN|nf_GENMAT)))
    return ZC_copy(ex);

  /* compute arch component of the missing principal ideal */
  { /* g A = G Ur A + [ga]A, Ur A = D Q + R as above (R = ex)
           = G R + [GD]Q + [ga]A */
    GEN ga = gel(clg2,2), GD = gel(clg2,3);
    if (lB) col = act_arch(Bex, WB_C + lW); else col = zerovec(1); /* nf=Q ! */
    if (lW) col = gadd(col, act_arch(A, ga));
    if (c)  col = gadd(col, act_arch(Q, GD));
  }
  if (xar)
  {
    GEN t = get_arch(nf, xar, prec);
    col = t? gadd(col, t):NULL;
  }

  /* find coords on Zk; Q = N (x / \prod gj^ej) = N(alpha), denom(alpha) | d */
  Q = gdiv(ZM_det_triangular(x), get_norm_fact(gen, ex, &d));
  col = col?isprincipalarch(bnf, col, Q, gen_1, d, &e):NULL;
  if (col && !fact_ok(nf,x, col,gen,ex)) col = NULL;
  if (!col && !ZV_equal0(ex))
  {
    /* in case isprincipalfact calls bnfinit() due to prec trouble...*/
    ex = gerepilecopy(av, ex);
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
  GEN y, nf = bnf_get_nf(bnf);
  long c;
  if (flag & nf_GEN_IF_PRINCIPAL) return algtobasis(nf,x);
  c = lg(bnf_get_cyc(bnf)) - 1;
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
      if (gequal0(x)) pari_err(talker,"zero ideal in isprincipal");
      return triv_gen(bnf, x, flag);
    case id_PRIME:
      if (pr_is_inert(x))
        return gerepileupto(av, triv_gen(bnf, gel(x,1), flag));
      x = idealhnf_two(bnf_get_nf(bnf), x);
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
    return (typ(u) == t_COL && RgV_isscalar(u) && gequal1(gel(u,1)))? v: famat_mul(v,u);
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
  if (id != C) id = idealred(nf, id);
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
    A = idealred(nf, mkvec2(A, gel(C,2)));
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
    Cext = (flag & nf_GENMAT)? cgetg(1, t_MAT): mkpolmod(gen_1,nf_get_pol(nf));
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
  GEN u, y, id, C0, Cext, nf = bnf_get_nf(bnf);

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
  GEN p1, v, rlog, logunit, ex, nf, pi2_sur_w, emb;

  bnf = checkbnf(bnf); nf = bnf_get_nf(bnf);
  logunit = bnf_get_logfu(bnf); RU = lg(logunit);
  n = bnf_get_tuN(bnf); /* # { roots of 1 } */
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
    if (!gequal1(Q_denom(x))) { avma = av; return cgetg(1,t_COL); }
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
        long p = 2 + maxss(1, (nf_get_prec(nf)-2) / 2);
        if (typ(logN) != t_REAL || gprecision(rx) > p)
          { avma = av; return cgetg(1,t_COL); } /* not a precision problem */
      }
      else
      {
        ex = RgM_solve(rlog, rx);
        if (ex)
        {
          ex = grndtoi(ex, &e);
          if (gequal0(gel(ex,RU)) && e < -4) break;
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
    GEN z = algtobasis(nf, bnf_get_tuU(bnf)); /* primitive root of 1 */
    GEN ro = RgV_dotproduct(row(nf_get_M(nf), 1), z);
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
  GEN y, A = bnf_get_logfu(bnf), invpi = invr( mppi(DEFAULTPREC) );
  long j = 1, RU = lg(A);

  if (!archp) archp = identity_perm( nf_get_r1(bnf_get_nf(bnf)) );
  if (add_zu) { RU++; A--; }
  y = cgetg(RU,t_MAT);
  if (add_zu)
  {
    long w = bnf_get_tuN(bnf);
    gel(y, j++) = (w == 2)? const_vecsmall(lg(archp)-1, 1)
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

  bnf = checkbnf(bnf); nf = bnf_get_nf(bnf);
  nf_get_sign(nf, &r1,&r2);
  S = zeromatcopy(r1, r1+r2-1); av = avma;
  y = nfsign_units(bnf, NULL, 0);
  for (j = 1; j < lg(y); j++)
  {
    GEN Sj = gel(S,j), yj = gel(y,j);
    for (i = 1; i <= r1; i++) gel(Sj,i) = yj[i]? gen_m1: gen_1;
  }
  avma = av; return S;
}

static GEN
get_log_embed(FB_t *F, REL_t *rel, GEN M, long RU, long R1, long prec)
{
  GEN arch, C, z = rel->m;
  long i;
  if (!z) return zerocol(RU);
  arch = typ(z) == t_COL? RgM_RgC_mul(M, z): RgC_Rg_mul(gel(M,1), z);
  C = cgetg(RU+1, t_COL); arch = glog(arch, prec);
  for (i=1; i<=R1; i++) C[i] = arch[i];
  for (   ; i<=RU; i++) gel(C,i) = gmul2n(gel(arch,i), 1);
  return C;
}

static GEN
perm_log_embed(GEN C, GEN perm)
{
  long i, n;
  GEN Cnew = cgetg_copy(C, &n);
  for (i = 1; i < n; i++)
  {
    long v = perm[i];
    if (v > 0)
      gel(Cnew, i) = gel(C, v);
    else
      gel(Cnew, i) = gconj(gel(C, -v));
  }
  return Cnew;
}

static GEN
set_fact(FB_t *F, FACT *fact, GEN ex, long *pnz)
{
  long i, n = fact[0].pr;
  long nz;
  GEN c = zero_Flv(F->KC);
  if (!n) /* trivial factorization */
    *pnz = F->KC;
  else {
    nz = fact[1].pr;
    if (fact[n].pr < nz) /* Possible with jid in rnd_rel */
      nz = fact[n].pr;
    for (i=1; i<=n; i++) c[fact[i].pr] = fact[i].ex;
    if (ex)
    {
      for (i=1; i<lg(ex); i++)
        if (ex[i]) {
          long v = F->subFB[i];
          c[v] += ex[i];
          if (v < nz) nz = v;
        }
    }
    *pnz = nz;
  }
  return c;
}

/* Is cols already in the cache ? bs = index of first non zero coeff in cols
 * General check for colinearity useless since exceedingly rare */
static int
already_known(RELCACHE_t *cache, long bs, GEN cols)
{
  REL_t *r;
  long l = lg(cols);
  for (r = cache->last; r > cache->base; r--)
    if (bs == r->nz)
    {
      GEN coll = r->R;
      long b = bs;
      while (b < l && cols[b] == coll[b]) b++;
      if (b == l) return 1;
    }
  return 0;
}

/* Add relation R to cache, nz = index of first non zero coeff in R.
 * If relation is a linear combination of the previous ones, return 0.
 * Otherwise, update basis and return > 0. Compute mod p (much faster)
 * so some kernel vector might not be genuine. */
static int
add_rel_i(RELCACHE_t *cache, GEN R, long nz, GEN m, long orig, long aut, REL_t **relp, long prnewrel)
{
  const ulong p = 27449UL;
  long i, k, n = lg(R)-1;

  if (already_known(cache, nz, R)) return -1;
  if (cache->last >= cache->base + cache->len) return 0;
  if (DEBUGLEVEL>6)
  {
    fprintferr("adding vector = %Ps\n",R);
    fprintferr("generators =\n%Ps\n", cache->basis);
  }
  if (cache->missing)
  {
    GEN a = leafcopy(R), basis = cache->basis;
    k = lg(a);
    do --k; while (!a[k]);
    while (k)
    {
      GEN c = gel(basis, k);
      if (c[k])
      {
        long ak = a[k];
        for (i=1; i < k; i++) if (c[i]) a[i] = (a[i] + ak*(p-c[i])) % p;
        a[k] = 0;
        do --k; while (!a[k]); /* k cannot go below 0: codeword is a sentinel */
      }
      else
      {
        ulong invak = Fl_inv((ulong)a[k], p);
        /* Cleanup a */
        for (i = k; i-- > 1; )
        {
          long j, ai = a[i];
          c = gel(basis, i);
          if (!ai || !c[i]) continue;
          ai = p-ai;
          for (j = 1; j < i; j++) if (c[j]) a[j] = (a[j] + ai*c[j]) % p;
          a[i] = 0;
        }
        /* Insert a/a[k] as k-th column */
        c = gel(basis, k);
        for (i = 1; i<k; i++) if (a[i]) c[i] = (a[i] * invak) % p;
        c[k] = 1; a = c;
        /* Cleanup above k */
        for (i = k+1; i<n; i++)
        {
          long j, ck;
          c = gel(basis, i);
          ck = c[k];
          if (!ck) continue;
          ck = p-ck;
          for (j = 1; j < k; j++) if (a[j]) c[j] = (c[j] + ck*a[j]) % p;
          c[k] = 0;
        }
        cache->missing--;
        break;
      }
    }
  }
  else
    k = (cache->last - cache->base) + 1;
  if (k || cache->relsup > 0)
  {
    REL_t *rel;

    rel = ++cache->last;
    if (!k)
    {
      cache->relsup--;
      k = (rel - cache->base) + cache->missing;
    }
    rel->R  = gclone(R);
    rel->m  =  m ? gclone(m) : NULL;
    rel->nz = nz;
    if (aut)
    {
      rel->relorig = (rel - cache->base) - orig;
      rel->relaut = aut;
    }
    else
      rel->relaut = 0;
    if (relp) *relp = rel;
    if (DEBUGLEVEL)
    {
      if (prnewrel)
        dbg_newrel(cache);
      else
        dbg_rel(rel - cache->base, R);
    }
  }
  return k;
}

static int
add_rel(RELCACHE_t *cache, FB_t *F, GEN R, long nz, GEN m)
{
  REL_t *rel;
  long k, l, prnewrel = nz < 0, reln;
  const long nauts = lg(F->idealperm), KC = F->KC;

  if (prnewrel) nz = -nz;
  k = add_rel_i(cache, R, nz, m, 0, 0, &rel, prnewrel);
  if (k > 0 && m)
  {
    GEN Rl = cgetg(KC+1, t_VECSMALL);
    reln = rel - cache->base;
    for (l = 1; l < nauts; l++)
    {
      GEN perml = gel(F->idealperm, l);
      long i, nzl = perml[nz];

      for (i = 1; i <= KC; i++) Rl[i] = 0;
      for (i = nz; i <= KC; i++)
        if (R[i])
        {
          long v = perml[i];

          if (v < nzl) nzl = v;
          Rl[v] = R[i];
        }
      (void)add_rel_i(cache, Rl, nzl, NULL, reln, l, NULL, prnewrel);
    }
  }
  return k;
}

/* Compute powers of prime ideal (P^0,...,P^a) (a > 1) */
static void
powPgen(FB_t *F, GEN nf, GEN vp, GEN *ppowP, long a)
{
  GEN id2, J;
  long j;

  id2 = cgetg(a+1,t_VEC);
  J = mkvec2(pr_get_p(vp), zk_scalar_or_multable(nf,pr_get_gen(vp)));
  gel(id2,1) = J;
  vp = idealhnf_two(nf,vp);
  for (j=2; j<=a; j++)
  {
    if (DEBUGLEVEL>1) fprintferr(" %ld", j);
    J = idealtwoelt(nf, idealmul_HNF(nf, vp, J));
    gel(J, 2) = zk_scalar_or_multable(nf, gel(J,2));
    gel(id2,j) = J;
  }
  setlg(id2, j);
  *ppowP = id2;
  if (DEBUGLEVEL>1) fprintferr("\n");
}


/* Compute powers of prime ideals (P^0,...,P^a) in subFB (a > 1) */
static void
powFBgen(RELCACHE_t *cache, FB_t *F, GEN nf, GEN auts)
{
  const long a = 1L<<RANDOM_BITS;
  pari_sp av = avma;
  GEN subFB = F->subFB, idealperm = F->idealperm;
  long i, k, l, id, n = lg(F->subFB), naut = lg(auts);

  if (DEBUGLEVEL) fprintferr("Computing powers for subFB: %Ps\n",subFB);
  if (cache) pre_allocate(cache, n*naut);
  for (i=1; i<n; i++)
  {
    id = subFB[i];
    if (gel(F->id2, id) == gen_0)
    {
      GEN id2;

      if (DEBUGLEVEL>1) fprintferr("%ld: 1", id);
      powPgen(F, nf, gel(F->LP, id), &id2, a);
      gel(F->id2, id) = gclone(id2);
      for (k = 1; k < naut; k++)
      {
        long sigmaid = coeff(idealperm, id, k);
        GEN aut = gel(auts, k), invaut = gel(auts, F->invs[k]);

        if (gel(F->id2, sigmaid) == gen_0)
        {
          long lid2;
          GEN sigmaid2 = cgetg_copy(id2, &lid2);

          if (DEBUGLEVEL>1) fprintferr("%ld: automorphism\n", sigmaid);
          for (l = 1; l < lid2; l++)
          {
            GEN id2l = gel(id2, l);
            gel(sigmaid2, l) =
              mkvec2(gel(id2l, 1), ZM_mul(ZM_mul(aut, gel(id2l, 2)), invaut));
          }
          /* WARNING: to be freed also in unclone_subFB */
          gel(F->id2, sigmaid) = gclone(sigmaid2);
        }
      }
    }
  }
  avma = av;
  if (DEBUGLEVEL) msgtimer("powFBgen");
  F->sfb_chg = 0;
  F->newpow = 0;
}

INLINE void
step(GEN x, double *y, GEN inc, long k)
{
  if (!y[k])
    x[k]++; /* leading coeff > 0 */
  else
  {
    long i = inc[k];
    x[k] += i;
    inc[k] = (i > 0)? -1-i: 1-i;
  }
}

static void
small_norm(RELCACHE_t *cache, FB_t *F, GEN nf, GEN auts, long nbrelpid,
           double LOGD, double LIMC2, FACT *fact, GEN p0)
{
  const long N = nf_get_degree(nf), R1 = nf_get_r1(nf), prec = nf_get_prec(nf);
  const long BMULT = 8;
  const long maxtry_DEP  = 20, maxtry_FACT = 500;
  double *y, *z, **q, *v, BOUND;
  pari_sp av;
  GEN x, M = nf_get_M(nf), G = nf_get_G(nf), L_jid = F->L_jid;
  long nbsmallnorm, nbfact, precbound, noideal = lg(L_jid);
  REL_t *last = cache->last;

  if (DEBUGLEVEL)
    fprintferr("\n#### Looking for %ld relations (small norms)\n",
               cache->end - last);
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
  for (av = avma; --noideal; avma = av)
  {
    GEN r, u, gx, ideal=gel(F->LP,L_jid[noideal]), inc=const_vecsmall(N, 1);
    long j, k, skipfirst, nbrelideal = 0, dependent = 0, try_factor = 0;
    pari_sp av2;

    if (DEBUGLEVEL>1)
      fprintferr("\n*** Ideal no %ld: %Ps\n", L_jid[noideal], vecslice(ideal,1,4));
    if (p0)
      ideal = idealmul(nf, p0, ideal);
    else
      ideal = idealhnf_two(nf, ideal);
    u = ZM_lll(ZM_mul(F->G0, ideal), 0.99, LLL_IM);
    ideal = ZM_mul(ideal,u); /* approximate T2-LLL reduction */
    r = Q_from_QR(RgM_mul(G, ideal), prec); /* Cholesky for T2 | ideal */
    if (!r) pari_err(bugparier, "small_norm (precision too low)");

    skipfirst = ZV_isscalar(gel(ideal,1))? 1: 0; /* 1 probable */
    for (k=1; k<=N; k++)
    {
      v[k] = gtodouble(gcoeff(r,k,k));
      for (j=1; j<k; j++) q[j][k] = gtodouble(gcoeff(r,j,k));
      if (DEBUGLEVEL>3) fprintferr("v[%ld]=%.4g ",k,v[k]);
    }
    BOUND = maxdd(v[1], v[2] + v[1]*q[1][2]*q[1][2]);
    BOUND *= BMULT;
    /* BOUND at most BMULT x smallest known vector */
    if (DEBUGLEVEL>1)
    {
      if (DEBUGLEVEL>3) fprintferr("\n");
      fprintferr("BOUND = %.4g\n",BOUND); flusherr();
    }
    BOUND *= 1 + 1e-6;
    k = N; y[N] = z[N] = 0; x[N] = 0;
    for (av2 = avma;; avma = av2, step(x,y,inc,k))
    {
      GEN R;
      long nz;
      do
      { /* look for primitive element of small norm, cf minim00 */
        int fl = 0;
        double p;
        if (k > 1)
        {
          long l = k-1;
          z[l] = 0;
          for (j=k; j<=N; j++) z[l] += q[l][j]*x[j];
          p = (double)x[k] + z[k];
          y[l] = y[k] + p*p*v[k];
          if (l <= skipfirst && !y[1]) fl = 1;
          x[l] = (long)floor(-z[l] + 0.5);
          k = l;
        }
        for(;; step(x,y,inc,k))
        {
          if (!fl)
          {
            p = (double)x[k] + z[k];
            if (y[k] + p*p*v[k] <= BOUND) break;

            step(x,y,inc,k);

            p = (double)x[k] + z[k];
            if (y[k] + p*p*v[k] <= BOUND) break;
          }
          fl = 0; inc[k] = 1;
          if (++k > N) goto ENDIDEAL;
        }
      } while (k > 1);

      /* element complete */
      if (zv_content(x) !=1) continue; /* not primitive */
      gx = ZM_zc_mul(ideal,x);
      if (ZV_isscalar(gx)) continue;

      {
        GEN Nx, xembed = RgM_RgC_mul(M, gx);
        long e;
        nbsmallnorm++;
        if (++try_factor > maxtry_FACT) goto ENDIDEAL;
        Nx = grndtoi(norm_by_embed(R1,xembed), &e);
        if (e >= 0) {
          if (DEBUGLEVEL > 1) { fprintferr("+"); flusherr(); }
          continue;
        }
        setabssign(Nx);
        if (!can_factor(F, nf, NULL, gx, Nx, fact)) {
          if (DEBUGLEVEL > 1) { fprintferr("."); flusherr(); }
          continue;
        }
      }

      /* smooth element */
      R = set_fact(F, fact, NULL, &nz);
      /* make sure we get maximal rank first, then allow all relations */
      if (add_rel(cache, F, R, nz, gx) <= 0)
      { /* probably Q-dependent from previous ones: forget it */
        if (DEBUGLEVEL>1) fprintferr("*");
        if (++dependent > maxtry_DEP) break;
        continue;
      }
      dependent = 0;

      if (DEBUGLEVEL) nbfact++;
      if (cache->last >= cache->end) goto END; /* we have enough */
      if (++nbrelideal == nbrelpid) break;
    }
ENDIDEAL:
    if (DEBUGLEVEL>1) msgtimer("for this ideal");
  }
END:
  if (DEBUGLEVEL)
  {
    if (cache->last != last) fprintferr("\n");
    msgtimer("small norm relations");
    fprintferr("  small norms gave %ld relations.\n",
               cache->last - last);
    if (nbsmallnorm)
      fprintferr("  nb. fact./nb. small norm = %ld/%ld = %.3f\n",
                  nbfact,nbsmallnorm,((double)nbfact)/nbsmallnorm);
  }
}

/* I integral ideal in HNF form */
static GEN
remove_content(GEN I)
{
  long N = lg(I)-1;
  if (!is_pm1(gcoeff(I,N,N))) I = Q_primpart(I);
  return I;
}

static GEN
get_random_ideal(FB_t *F, GEN nf, GEN ex)
{
  long l = lg(ex);
  for (;;) {
    GEN ideal = idealhnf_principal(nf, gen_1);
    long i;
    for (i=1; i<l; i++)
    {
      long id = F->subFB[i];
      ex[i] = random_bits(RANDOM_BITS);
      if (ex[i])
      {
        GEN a = gmael(F->id2,id,ex[i]);
        ideal = ideal? idealmul_HNF(nf,ideal, a): idealhnf_two(nf,a);
      }
    }
    if (ideal) { /* ex  != 0 */
      ideal = remove_content(ideal);
      if (!is_pm1(gcoeff(ideal,1,1))) return ideal; /* ideal != Z_K */
    }
  }
}

static void
rnd_rel(RELCACHE_t *cache, FB_t *F, GEN nf, GEN auts, FACT *fact)
{
  GEN L_jid = F->L_jid;
  GEN ex, baseideal, m1, M = nf_get_M(nf);
  const long nbG = lg(F->vecG)-1, lgsub = lg(F->subFB), l_jid = lg(L_jid);
  long jlist;
  pari_sp av;

  /* will compute P[ L_jid[i] ] * (random product from subFB) */
  if (DEBUGLEVEL) {
    long d = cache->end - cache->last;
    fprintferr("\n(more relations needed: %ld)\n", d > 0? d: 1);
    if (l_jid <= F->orbits) fprintferr("looking hard for %Ps\n",L_jid);
  }
  ex = cgetg(lgsub, t_VECSMALL);
  baseideal = get_random_ideal(F, nf, ex);
  baseideal = red(nf, baseideal, F->G0, &m1);
  m1 = gdiv(m1, content(m1));
  if (baseideal)
    baseideal = idealhnf_two(nf, baseideal);
  else
    baseideal = scalarmat_shallow(gen_1, lg(M) - 1);
  for (av = avma, jlist = 1; jlist < l_jid; jlist++, avma = av)
  {
    long jid = L_jid[jlist];
    GEN Nideal, ideal;
    pari_sp av1;
    long j, l;

    if (DEBUGLEVEL>1) fprintferr("(%ld)", jid);
    /* If subFB is not Galois-stable, all ideals in the orbit of jid are not
     * equivalent (subFB is probably not Galois stable) */
    l = random_Fl(lg(auts));
    if (l) jid = coeff(F->idealperm, jid, l);
    ideal = idealmul(nf, baseideal, idealhnf_two(nf, gel(F->LP,jid)));
    Nideal = ZM_det_triangular(ideal);
    for (av1 = avma, j = 1; j <= nbG; j++, avma = av1)
    { /* reduce along various directions */
      GEN m = idealpseudomin_nonscalar(ideal, gel(F->vecG,j));
      GEN R;
      long nz;
      if (!factorgen(F,nf,ideal,Nideal,m,fact))
      {
        if (DEBUGLEVEL>1) { fprintferr("."); flusherr(); }
        continue;
      }
      /* can factor ideal, record relation */
      add_to_fact(jid, 1, fact);
      R = set_fact(F, fact, ex, &nz);
      /* If relation is linearly dependent of the previous ones, we do not
       * include it (to speed up hnfspec/add). However we just go to the next
       * ideal as if we had included it (to finish rnd_rel earlier and make an
       * hnfspec/add round). */
      switch (add_rel(cache, F, R, -nz, nfmul(nf, m, m1)))
      {
        case -1: /* forget it */
          if (DEBUGLEVEL>1) dbg_cancelrel(jid,j,R);
          continue;
        case 0:
          break;
      }
      /* Need more, try next prime ideal */
      if (cache->last < cache->end) break;
      /* We have found enough. Return */
      avma = av; return;
    }
  }
  if (DEBUGLEVEL) msgtimer("for remaining ideals");
}

/* remark: F->KCZ changes if be_honest() fails */
static int
be_honest(FB_t *F, GEN nf, FACT *fact)
{
  GEN P, ideal, Nideal, m;
  long ex, i, j, J, k, iz, nbtest;
  long nbG = lg(F->vecG)-1, lgsub = lg(F->subFB), KCZ0 = F->KCZ;
  pari_sp av;

  if (DEBUGLEVEL) {
    fprintferr("Be honest for %ld primes from %ld to %ld\n", F->KCZ2 - F->KCZ,
               F->FB[ F->KCZ+1 ], F->FB[ F->KCZ2 ]);
  }
  av = avma;
  for (iz=F->KCZ+1; iz<=F->KCZ2; iz++, avma = av)
  {
    long p = F->FB[iz];
    if (DEBUGLEVEL>1) fprintferr("%ld ", p);
    P = F->LV[p]; J = lg(P);
    /* all P|p in FB + last is unramified --> check all but last */
    if (isclone(P) && pr_get_e(gel(P,J-1)) == 1) J--;

    for (j=1; j<J; j++)
    {
      GEN ideal0 = idealhnf_two(nf,gel(P,j));
      pari_sp av1, av2 = avma;
      for(nbtest=0;;)
      {
        ideal = ideal0;
        for (i=1; i<lgsub; i++)
        {
          long id = F->subFB[i];
          ex = random_bits(RANDOM_BITS);
          if (ex) ideal = idealmul_HNF(nf,ideal, gmael(F->id2,id,ex));
        }
        ideal = remove_content(ideal);
        Nideal = ZM_det_triangular(ideal);
        for (av1 = avma, k = 1; k <= nbG; k++, avma = av1)
        {
          m = idealpseudomin_nonscalar(ideal, gel(F->vecG,k));
          if (factorgen(F,nf,ideal,Nideal, m,fact)) break;
        }
        avma = av2; if (k <= nbG) break;
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

/* A t_MAT of complex floats, in fact reals. Extract a submatrix B
 * whose columns are definitely non-0, i.e. gexpo(A[j]) >= -2
 *
 * If possible precision problem (t_REAL 0 with large exponent), set
 * *precpb to 1 */
static GEN
clean_cols(GEN A, int *precpb)
{
  long l = lg(A), h, i, j, k;
  GEN B;
  *precpb = 0;
  if (l == 1) return A;
  h = lg(gel(A,1));;
  B = cgetg(l, t_MAT);
  for (i = k = 1; i < l; i++)
  {
    GEN Ai = gel(A,i);
    int non0 = 0;
    for (j = 1; j < h; j++)
    {
      GEN c = gel(Ai,j);
      if (gexpo(c) >= -2)
      {
        if (gequal0(c)) *precpb = 1; else non0 = 1;
      }
    }
    if (non0) gel(B, k++) = Ai;
  }
  setlg(B, k); return B;
}

static long
compute_multiple_of_R_pivot(GEN X, GEN x0/*unused*/, long ix, GEN c)
{
  GEN x = gel(X,ix);
  long i, k = 0, ex = - (long)HIGHEXPOBIT, lx = lg(x);
  (void)x0;
  for (i=1; i<lx; i++)
    if (!c[i] && !gequal0(gel(x,i)))
    {
      long e = gexpo(gel(x,i));
      if (e > ex) { ex = e; k = i; }
    }
  return (k && ex > -32)? k: lx;
}

/* A = complex logarithmic embeddings of units (u_j) found so far,
 * RU = R1+R2 = unit rank, N = field degree
 * need = unit rank defect
 * L = NULL (prec problem) or B^(-1) * A with approximate rational entries
 * (as t_REAL), B a submatrix of A, with (probably) maximal rank RU */
static GEN
compute_multiple_of_R(GEN A, long RU, long N, long *pneed, GEN *ptL)
{
  GEN T, d, mdet, Im_mdet, Im_expo, kR, xreal, L;
  long i, j, r, R1 = 2*RU - N;
  int precpb;
  pari_sp av = avma;

  if (RU == 1) { *ptL = zeromat(0, lg(A)-1); return gen_1; }

  if (DEBUGLEVEL) fprintferr("\n#### Computing regulator multiple\n");
  xreal = real_i(A); /* = (log |sigma_i(u_j)|) */
  mdet = clean_cols(xreal, &precpb);
  /* will cause precision to increase on later failure, but we may succeed! */
  *ptL = precpb? NULL: gen_1;
  if (lg(mdet) < RU)
  {
    if (DEBUGLEVEL)
      fprintferr("Unit group rank <= %ld < %ld\n",lg(mdet)-1, RU);
    *pneed = RU - (lg(mdet)-1);
    avma = av; return NULL;
  }
  T = cgetg(RU+1,t_COL);
  for (i=1; i<=R1; i++) gel(T,i) = gen_1;
  for (   ; i<=RU; i++) gel(T,i) = gen_2;
  mdet = shallowconcat(T, mdet); /* det(Span(mdet)) = N * R */

  /* could be using indexrank(), but need custom "get_pivot" function */
  d = RgM_pivots(mdet, NULL, &r, &compute_multiple_of_R_pivot);
  /* # of independent columns == unit rank ? */
  if (lg(mdet)-1 - r != RU)
  {
    if (DEBUGLEVEL)
      fprintferr("Unit group rank  = %ld < %ld\n",lg(mdet)-1 - r, RU);
    *pneed = RU - (lg(mdet)-1-r);
    avma = av; return NULL;
  }

  Im_mdet = cgetg(RU+1, t_MAT); /* extract independent columns */
  Im_expo = cgetg(RU+1, t_VECSMALL); /* ... and exponents (from renormalize) */
  /* N.B: d[1] = 1, corresponding to T above */
  gel(Im_mdet, 1) = T;
  Im_expo[1] = 0;
  for (i = j = 2; i <= RU; j++)
    if (d[j]) gel(Im_mdet, i++) = gel(mdet,j);

  /* integral multiple of R: the cols we picked form a Q-basis, they have an
   * index in the full lattice. First column is T */
  kR = divru(det2(Im_mdet), N);
  /* R > 0.2 uniformly */
  if (!signe(kR) || expo(kR) < -3) { avma=av; *pneed = 0; return NULL; }

  setabssign(kR);
  L = RgM_inv(Im_mdet);
  if (!L) { *ptL = NULL; return kR; }

  L = rowslice(L, 2, RU); /* remove first line */
  L = RgM_mul(L, xreal); /* approximate rational entries */
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
  long r, ec;
  GEN L, H, D, den, R, c;

  if (DEBUGLEVEL) { fprintferr("\n#### Computing check\n"); flusherr(); }
  D = gmul2n(mpmul(*ptkR,z), 1); /* bound for denom(lambda) */
  if (expo(D) < 0 && rtodbl(D) < 0.95) return fupb_PRECI;
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
  c = gmul(R,z); /* should be n (= 1 if we are done) */
  if (DEBUGLEVEL)
  {
    msgtimer("bestappr/regulator");
    fprintferr("\n#### Tentative regulator : %Ps\n", gprec_w(R,3));
    fprintferr("\n ***** check = %Ps\n",gprec_w(c,3));
  }
  ec = gexpo(c);
  /* safe check for c < 0.75 : avoid underflow in gtodouble() */
  if (ec < -1 || (ec == -1 && gtodouble(c) < 0.75)) {
    avma = av; return fupb_PRECI;
  }
  /* safe check for c > 1.3 : avoid overflow */
  if (ec > 0 || (ec == 0 && gtodouble(c) > 1.3)) {
    avma = av; return fupb_RELAT;
  }
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
  I1 = idealred(nf,I1);
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
  GEN z,G,Ga,ga,GD,cyc,X,Y,D,U,V,Ur,Ui,Uir,I,J,arch;
  long i,j,lo,lo0;

  D = ZM_snfall(W,&U,&V); /* UWV = D, D diagonal, G = g Ui (G=new gens, g=old) */
  Ui = RgM_inv(U);
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
        I = idealred(nf0,I);
      }
    }
    J = inverse_if_smaller(nf0, I);
    if (J != I)
    { /* update wrt P */
      neg_row(Y ,j); gel(V,j) = ZC_neg(gel(V,j));
      neg_row(Ur,j); gel(X,j) = ZC_neg(gel(X,j));
    }
    G[j] = J[1]; /* generator, order cyc[j] */
    arch = famat_to_arch(nf, gel(J,2), prec);
    if (!arch) pari_err(precer,"class_group_gen");
    gel(Ga,j) = gneg(arch);
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
    if (gequal1(gel(cyc,j)))
    { /* strip useless components */
      lo = j; setlg(cyc,lo); setlg_col(Ur,lo);
      setlg(G,lo); setlg(Ga,lo); setlg(GD,lo); break;
    }
  }
  *ptclg1 = mkvec3(ZM_det_triangular(W), cyc, G);
  *ptclg2 = mkvec3(Ur, ga,GD);
}

/* SMALLBUCHINIT */

static GEN
decode_pr_lists(GEN nf, GEN pfc)
{
  long i, p, pmax, n = nf_get_degree(nf), l = lg(pfc);
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
  nf = bnf_get_nf(bnf);
  cyc = bnf_get_cyc(bnf); D = diagonal_shallow(cyc);
  gen = bnf_get_gen(bnf); GD = gmael(bnf,9,3);
  h = cgetg_copy(gen, &l);
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
  nf  = bnf_get_nf(bnf);
  lW=lg(W)-1; lma=lW+lg(B);
  pFB = get_Vbase(bnf);
  ma = cgetg(lma,t_VEC);

  for (j=1; j<lma; j++)
  {
    pari_sp btop = avma;
    long e;
    GEN c = getrand();
    GEN ex = (j<=lW)? gel(W,j): gel(B,j-lW);
    GEN C = (j<=lW)? NULL: gel(pFB,j);
    GEN Nx = get_norm_fact_primes(pFB, ex, C);
    GEN y = isprincipalarch(bnf,gel(WB_C,j), Nx,gen_1, gen_1, &e);
    if (y && fact_ok(nf,y,C,pFB,ex))
    {
      if (DEBUGLEVEL>1) fprintferr("*%ld ",j);
      gel(ma,j) = gerepileupto(btop, y); continue;
    }
    y = isprincipalfact_or_fail(bnf, C, pFB, ex);
    if (typ(y) != t_INT)
    {
      if (DEBUGLEVEL>1) fprintferr("%ld ",j);
      gel(ma,j) = gerepileupto(btop,gel(y,2)); continue;
    }

    prec = itos(y);
    j--; /* will retry the same element in next loop */
    if (DEBUGLEVEL) pari_warn(warnprec,"makematal",prec);
    nf = nfnewprec_shallow(nf,prec);
    bnf = Buchall(nf, nf_FORCE, prec); setrand(c);
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
  setabssign(R); return gerepileuptoleaf(av, R);
}

/* return corrected archimedian components for elts of x (vector)
 * (= log(sigma_i(x)) - log(|Nx|) / [K:Q]) */
static GEN
get_archclean(GEN nf, GEN x, long prec, int units)
{
  long k,N, la = lg(x);
  GEN M = cgetg(la,t_MAT);

  if (la == 1) return M;
  N = nf_get_degree(nf);
  for (k=1; k<la; k++)
  {
    pari_sp av = avma;
    GEN c = get_arch(nf, gel(x,k), prec);
    if (!c) return NULL;
    if (!units) {
      c = cleanarch(c, N, prec);
      if (!c) return NULL;
    }
    gel(M,k) = gerepilecopy(av, c);
  }
  return M;
}

static void
my_class_group_gen(GEN bnf, long prec, GEN nf0, GEN *ptcl, GEN *ptcl2)
{
  GEN W = gel(bnf,1), C = gel(bnf,4), nf = bnf_get_nf(bnf);
  class_group_gen(nf,W,C,get_Vbase(bnf),prec,nf0, ptcl,ptcl2);
}

GEN
bnfnewprec_shallow(GEN bnf, long prec)
{
  GEN nf0 = bnf_get_nf(bnf), nf, res, funits, mun, gac, matal, clgp, clgp2, y;
  long r1, r2, prec1;

  nf_get_sign(nf0, &r1, &r2);
  funits = matalgtobasis(nf0, bnf_get_fu(bnf));

  prec1 = prec;
  if (r1 + r2 > 1) {
    long e = gexpo(bnf_get_logfu(bnf)) + 1 - TWOPOTBITS_IN_LONG;
    if (e >= 0) prec += (e>>TWOPOTBITS_IN_LONG);
  }
  if (DEBUGLEVEL && prec1!=prec) pari_warn(warnprec,"bnfnewprec",prec);
  matal = check_and_build_matal(bnf);
  for(;;)
  {
    pari_sp av = avma;
    nf = nfnewprec_shallow(nf0,prec);
    mun = get_archclean(nf,funits,prec,1);
    if (mun)
    {
      gac = get_archclean(nf,matal,prec,0);
      if (gac) break;
    }
    avma = av; prec = (prec-1)<<1;
    if (DEBUGLEVEL) pari_warn(warnprec,"bnfnewprec(extra)",prec);
  }
  y = leafcopy(bnf);
  gel(y,3) = mun;
  gel(y,4) = gac;
  gel(y,7) = nf;
  my_class_group_gen(y,prec,nf0, &clgp,&clgp2);
  res = leafcopy(gel(bnf,8));
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
  GEN y = cgetg(7,t_VEC);
  long i;
  gel(y,1) = bnfnewprec_shallow(bnr_get_bnf(bnr), prec);
  for (i=2; i<7; i++) gel(y,i) = gel(bnr,i);
  return y;
}
GEN
bnrnewprec(GEN bnr, long prec)
{
  GEN y = cgetg(7,t_VEC);
  long i;
  checkbnr(bnr);
  gel(y,1) = bnfnewprec(bnr_get_bnf(bnr), prec);
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
  GEN nf = bnf_get_nf(bnf), T = nf_get_pol(nf);
  GEN y = cgetg(13,t_VEC);

  gel(y,1) = T;
  gel(y,2) = gmael(nf,2,1);
  gel(y,3) = nf_get_disc(nf);
  gel(y,4) = nf_get_zk(nf);
  gel(y,5) = nf_get_roots(nf);
  gel(y,6) = gen_0; /* FIXME: unused */
  gel(y,7) = gel(bnf,1);
  gel(y,8) = gel(bnf,2);
  gel(y,9) = codeprimes(gel(bnf,5), degpol(T));
  gel(y,10) = mkvec2(utoipos(bnf_get_tuN(bnf)),
                     nf_to_scalar_or_basis(nf, bnf_get_tuU(bnf)));
  gel(y,11) = matalgtobasis(bnf, bnf_get_fu_nocheck(bnf));
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
  GEN ro, nf, A, fu, FU, L;
  GEN pfc, C, clgp, clgp2, res, y, W, zu, matal, Vbase;
  nfbasic_t T;

  if (typ(sbnf) != t_VEC || lg(sbnf) != 13) pari_err(typeer,"bnfmake");
  if (prec < DEFAULTPREC) prec = DEFAULTPREC;

  nfbasic_from_sbnf(sbnf, &T);
  ro = gel(sbnf,5);
  fu = gel(sbnf,11);
  if (prec > gprecision(ro)) ro = get_roots(T.x,T.r1,prec);
  nf = nfbasic_to_nf(&T, ro, prec);

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
  n = nf_get_degree(nf);
  for (j=1; j<l; j++) gel(Vbase,j) = decodeprime(gel(pfc,j), L, n);
  W = gel(sbnf,7);
  class_group_gen(nf,W,C,Vbase,prec,NULL, &clgp,&clgp2);

  zu = gel(sbnf,10);
  zu = mkvec2(gel(zu,1), nf_to_scalar_or_alg(nf, gel(zu,2)));

  FU = cgetg_copy(fu, &l);
  for (k=1; k < l; k++) gel(FU,k) = coltoliftalg(nf, gel(fu,k));
  res = get_clfu(clgp, get_regulator(A), zu, FU);
  y = buchall_end(nf,res,clgp2,W,gel(sbnf,8),A,C,Vbase);
  y[10] = sbnf[12]; return gerepilecopy(av,y);
}

static const double BNF_C1 = 0.3, BNF_C2 = 0.3;
static const long BNF_RELPID = 4;

GEN
bnfinit0(GEN P, long flag, GEN data, long prec)
{
  double c1 = BNF_C1, c2 = BNF_C2;
  long fl, relpid = BNF_RELPID;

  if (typ(P) == t_VEC && lg(P) == 13) return sbnf2bnf(P, prec); /* sbnf */
  if (data)
  {
    long lx = lg(data);
    if (typ(data) != t_VEC || lx > 5) pari_err(typeer,"bnfinit");
    switch(lx)
    {
      case 4: relpid = itos(gel(data,3));
      case 3: c2 = gtodouble(gel(data,2));
      case 2: c1 = gtodouble(gel(data,1));
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
  return Buchall_param(P, c1, c2, relpid, fl, prec);
}
GEN
Buchall(GEN P, long flag, long prec)
{ return Buchall_param(P, BNF_C1, BNF_C2, BNF_RELPID, flag, prec); }

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

  v = vecsmalltrunc_init(l);
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
init_rel(RELCACHE_t *cache, FB_t *F, long add_need)
{
  const long n = F->KC + add_need; /* expected # of needed relations */
  long i, j, k, p;
  GEN c, P;
  GEN R;

  if (DEBUGLEVEL) fprintferr("KCZ = %ld, KC = %ld, n = %ld\n", F->KCZ,F->KC,n);
  reallocate(cache, 10*n + 50); /* make room for lots of relations */
  cache->chk = cache->base;
  cache->end = cache->base + n;
  cache->relsup = add_need;
  cache->last = cache->base;
  cache->missing = lg(cache->basis) - 1;
  for (i = 1; i <= F->KCZ; i++)
  { /* trivial relations (p) = prod P^e */
    p = F->FB[i]; P = F->LV[p];
    if (!isclone(P)) continue;

    /* all prime divisors in FB */
    c = zero_Flv(F->KC); k = F->iLP[p];
    R = c; c += k;
    for (j = lg(P)-1; j; j--) c[j] = pr_get_e(gel(P,j));
    add_rel(cache, F, R, k+1, /*m*/NULL);
  }
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
  GEN g = RgM_shallowcopy(G);
  if (a != b) shift_embed(g,Gtw,a,r1);
  shift_embed(g,Gtw,b,r1); return g;
}

static void
compute_vecG(GEN nf, FB_t *F, long n)
{
  GEN G0, Gtw0, vecG, G = nf_get_G(nf);
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

static GEN
automorphism_perms(GEN M, GEN auts, GEN cyclic, long N)
{
  pari_sp av;
  const long r1plusr2 = lg(gel(M, 1)), r1 = 2*r1plusr2-N-2, r2 = r1plusr2-r1-1;
  long nauts = lg(auts), ncyc = lg(cyclic), i, j, l, m;
  GEN Mt, perms = cgetg(nauts, t_VEC);

  for (l = 1; l < nauts; l++)
    gel(perms, l) = cgetg(r1plusr2, t_VECSMALL);
  av = avma;
  Mt = shallowtrans(M);
  Mt = shallowconcat(Mt, gconj(vecslice(Mt, r1+1, r1+r2)));
  for (l = 1; l < ncyc; l++)
  {
    GEN thiscyc = gel(cyclic, l);
    long k = thiscyc[1];
    GEN Nt = RgM_mul(shallowtrans(gel(auts, k)), Mt);
    GEN perm = gel(perms, k), permprec;
    for (i = 1; i < r1plusr2; i++)
    {
      GEN vec = gel(Nt, i), minnorm;
      minnorm = gnorml2(gsub(vec, gel(Mt, 1)));
      perm[i] = 1;
      for (j = 2; j <= N; j++)
      {
        GEN thisnorm = gnorml2(gsub(vec, gel(Mt, j)));
        if (gcmp(thisnorm, minnorm) < 0)
        {
          minnorm = thisnorm;
          perm[i] = j >= r1plusr2 ? r2-j : j;
        }
      }
    }
    for (permprec = perm, m = 2; m < lg(thiscyc); m++)
    {
      GEN thisperm = gel(perms, thiscyc[m]);
      for (i = 1; i < r1plusr2; i++)
      {
        long pp = labs(permprec[i]);
        thisperm[i] = permprec[i] < 0 ? -perm[pp] : perm[pp];
      }
      permprec = thisperm;
    }
  }
  avma = av;
  return perms;
}

/* Determine the field automorphisms and its matrix in the integral basis. */
static GEN
automorphism_matrices(GEN nf, long v, long N, GEN *invp, GEN *cycp)
{
  pari_sp av = avma;
  GEN auts = galoisconj(nf, NULL), mats, cyclic, cyclicidx;
  GEN invs;
  long nauts = lg(auts)-1, i, j, k, l;

  cyclic = cgetg(nauts+1, t_VEC);
  cyclicidx = zero_Flv(nauts);
  invs = zero_Flv(nauts-1);
  for (l = 1; l <= nauts; l++)
  {
    GEN aut = gel(auts, l);
    if (degpol(aut) == 1 && isint1(leading_term(aut)) &&
        isintzero(constant_term(aut)))
    {
      swap(gel(auts, l), gel(auts, nauts));
      break;
    }
  }
  for (l = 1; l <= nauts; l++) gel(auts, l) = algtobasis(nf, gel(auts, l));
  /* Compute maximal cyclic subgroups */
  for (l = nauts; --l > 0; )
    if (!cyclicidx[l])
    {
      GEN elt = gel(auts, l), aut = elt, cyc = cgetg(nauts+1, t_VECSMALL);
      cyclicidx[l] = l;
      cyc[1] = l;
      j = 1;
      do
      {
        elt = galoisapply(nf, elt, aut);
        for (k = 1; k <= nauts; k++) if (gequal(elt, gel(auts, k))) break;
        cyclicidx[k] = l;
        cyc[++j] = k;
      }
      while (k != nauts);
      setlg(cyc, j);
      gel(cyclic, l) = cyc;
      /* Store the inverses */
      for (i = 1; i <= j/2; i++)
      {
        invs[cyc[i]] = cyc[j-i];
        invs[cyc[j-i]] = cyc[i];
      }
    }
  for (i = j = 1; i < nauts; i++)
    if (cyclicidx[i] == i) cyclic[j++] = cyclic[i];
  setlg(cyclic, j);
  mats = cgetg(nauts, t_VEC);
  while (--j > 0)
  {
    GEN cyc = gel(cyclic, j);
    long id = cyc[1];
    GEN M, Mi, aut = gel(auts, id);

    gel(mats, id) = Mi = M = nfgaloismatrix(nf, aut);
    for (i = 2; i < lg(cyc); i++)
    {
      Mi = ZM_mul(Mi, M);
      gel(mats, cyc[i]) = Mi;
    }
  }
  gerepileall(av, 3, &mats, &invs, &cyclic);
  *invp = invs;
  *cycp = cyclic;
  return mats;
}

static GEN
trim_list(FB_t *F)
{
  pari_sp av = avma;
  GEN list = F->L_jid ? F->L_jid : F->perm, present = zero_Flv(F->KC);
  long i, j, imax = lg(F->L_jid);
  GEN minidx = F->minidx, idx = cgetg(lg(list), t_VECSMALL);

  for (i = j = 1; i < imax; i++)
  {
    long id = minidx[list[i]];

    if (!present[id])
    {
      idx[j++] = id;
      present[id] = 1;
    }
  }
  setlg(idx, j);
  return gerepileuptoleaf(av, idx);
}

GEN
Buchall_param(GEN P, double cbach, double cbach2, long nbrelpid, long flun, long prec)
{
  pari_sp av0 = avma, av, av2;
  long PRECREG, N, R1, R2, RU, LIMC, LIMC2, zc, i;
  long nreldep, sfb_trials, need, old_need = -1, precdouble = 0, precadd = 0;
  long done_small;
  double lim, drc, LOGD, LOGD2;
  GEN zu, nf, D, A, W, R, Res, z, h, PERM, fu = NULL /*-Wall*/;
  GEN res, L, resc, B, C, C0, lambda, dep, clg1, clg2, Vbase;
  GEN auts, cyclic, small_mult;
  const char *precpb = NULL;
  const long minsFB = 3, RELSUP = 5;
  int FIRST = 1;
  RELCACHE_t cache;
  FB_t F;
  GRHcheck_t GRHcheck;
  FACT *fact;

  if (DEBUGLEVEL) (void)timer2();
  P = get_nfpol(P, &nf);
  if (nf)
    PRECREG = nf_get_prec(nf);
  else
  {
    PRECREG = maxss(prec, MEDDEFAULTPREC);
    nf = nfinit(P, PRECREG);
    if (lg(nf)==3) { /* P non-monic and nfinit CHANGEd it ? */
      pari_warn(warner,"non-monic polynomial. Change of variables discarded");
      nf = gel(nf,1);
    }
  }
  N = degpol(P);
  if (N <= 1) return gerepilecopy(av0, Buchall_deg1(nf));
  zu = rootsof1(nf);
  gel(zu,2) = nf_to_scalar_or_alg(nf, gel(zu,2));
  if (DEBUGLEVEL) msgtimer("nfinit & rootsof1");

  auts = automorphism_matrices(nf, varn(P), N, &F.invs, &cyclic);
  if (DEBUGLEVEL) msgtimer("automorphisms");
  F.embperm = automorphism_perms(nf_get_M(nf), auts, cyclic, N);
  if (DEBUGLEVEL) msgtimer("complex embedding permutations");

  nf_get_sign(nf, &R1, &R2); RU = R1+R2;
  compute_vecG(nf, &F, minss(RU, 9));
  D = absi(nf_get_disc(nf)); drc = gtodouble(D);
  if (DEBUGLEVEL) fprintferr("R1 = %ld, R2 = %ld\nD = %Ps\n",R1,R2, D);
  LOGD = log(drc); LOGD2 = LOGD*LOGD;
  lim = exp(-N + R2 * log(4/PI)) * sqrt(2*PI*N*drc);
  if (lim < 3.) lim = 3.;
  if (cbach > 12.) {
    if (cbach2 < cbach) cbach2 = cbach;
    cbach = 12.;
  }
  if (cbach <= 0.) pari_err(talker,"Bach constant <= 0 in buch");

  /* resc ~ sqrt(D) w / 2^r1 (2pi)^r2 = hR / Res(zeta_K, s=1) */
  resc = gdiv(mulri(gsqrt(D,DEFAULTPREC), gel(zu,1)),
              gmul2n(powru(mppi(DEFAULTPREC), R2), RU));
  av = avma; cache.base = NULL; F.subFB = NULL;
  init_GRHcheck(&GRHcheck, N, R1, LOGD);

START:
  do
  {
    if (!FIRST) cbach = check_bach(cbach,12.);
    FIRST = 0; avma = av;
    if (cache.base) delete_cache(&cache);
    if (F.subFB) delete_FB(&F);
    LIMC = (long)(cbach*LOGD2);
    if (LIMC < 20) { LIMC = 20; cbach = (double)LIMC / LOGD2; }
    LIMC2 = maxss(3 * N, (long)(cbach2*LOGD2));
    if (LIMC2 < LIMC) LIMC2 = LIMC;
    if (DEBUGLEVEL) { fprintferr("LIMC = %ld, LIMC2 = %ld\n",LIMC,LIMC2); }

    Res = FBgen(&F, nf, N, LIMC2, LIMC, &GRHcheck);
  }
  while (!Res || !subFBgen(&F,nf,auts,cyclic,mindd(lim,LIMC2) + 0.5,minsFB));
  fact = (FACT*)stackmalloc((F.KC+1)*sizeof(FACT));
  PERM = leafcopy(F.perm); /* to be restored in case of precision increase */
  cache.basis = zero_Flm_copy(F.KC,F.KC);
  F.id2 = zerovec(F.KC);
  small_mult = zero_Flv(F.KC);
  done_small = 0;
  R = NULL;
  av2 = avma;
  init_rel(&cache, &F, RELSUP + RU-1); /* trivial relations */
  need = cache.end - cache.last;

  W = NULL;
  sfb_trials = nreldep = 0;
  do
  {
    do
    {
      if (need > 0)
      {
        long oneed = cache.end - cache.last;
        /* Test below can be true if elts != NULL */
        if (need < oneed) need = oneed;
        pre_allocate(&cache, need+lg(auts)-1+(R ? lg(W)-1 : 0));
        cache.end = cache.last + need;
        F.L_jid = trim_list(&F);
      }
      if (need > 0 && nbrelpid > 0 && done_small <= F.KC && (!R || lg(W)>1) &&
          cache.last < cache.base + 2*F.KC /* heuristic */)
      {
        pari_sp av3 = avma;
        GEN p0 = NULL, L_jid = F.L_jid, aut0 = auts;
        if (R)
        {
          /*
           * We have full rank for class group and unit, however those
           * lattices are too small. The following tries to improve the
           * prime group lattice: it specifically looks for relations
           * involving the primes generating the class group.
           */
          long l;
          /* We need lg(W)-1 relations. */
          F.L_jid = vecslice(F.perm, 1, lg(W) - 1);
          cache.end = cache.last + lg(W) - 1;
          /* We lie to the add_rel subsystem, telling it we miss relations
           * involving the primes generating the class group (and only those).
           */
          cache.missing = lg(W) - 1;
          for (l = 1; l < lg(W); l++)
            mael(cache.basis, F.perm[l], F.perm[l]) = 0;
          /* We lie to the small_norm subsystem, telling it there are no
           * automorphisms (automorphisms tend to create lattices that are
           * twice the size of the full lattice: if a relation is p1+p2=0
           * where p1 and p2 are in the same odd-sized orbit, then the images
           * of this relation will lead to p1=...=pn and 2p1=0). */
          auts = cgetg(1, t_VEC);
        }
        if (done_small)
        {
          long j = 0, lim;
          for (i = F.KC; i >= 1; i--) if (!small_mult[j = F.perm[i]]) break;
          small_mult[j]++;
          p0 = gel(F.LP, j);
          lim = F.minidx[j];
          if (!R)
          {
            /* Prevent considering both P_iP_j and P_jP_i in small_norm */
            for (i = j = 1; i < lg(F.L_jid); i++)
              if (F.L_jid[i] >= lim) F.L_jid[j++] = F.L_jid[i];
            setlg(F.L_jid, j);
          }
        }
        if (lg(F.L_jid) > 1)
          small_norm(&cache, &F, nf, auts, nbrelpid, LOGD, LIMC2, fact, p0);
        avma = av3;
        if (R)
        {
          long l;
          auts = aut0;
          F.L_jid = L_jid;
          cache.end = cache.last + need;
          for (l = 1; l < lg(W); l++)
            mael(cache.basis, F.perm[l], F.perm[l]) = 1;
          cache.missing = 0;
        }
        else
        {
          F.L_jid = F.perm;
          need = 0;
        }
        done_small++;
        F.sfb_chg = 0;
      }
      if (need > 0)
      {
        /* Random relations */
        if (DEBUGLEVEL) fprintferr("\n#### Looking for random relations\n");
        if (++nreldep > MAXRELSUP) {
          if (++sfb_trials > SFB_MAX && cbach < 2) goto START;
          F.sfb_chg = sfb_INCREASE;
        }
        if (F.sfb_chg) {
          if (!subFB_change(&F)) goto START;
          nreldep = 0;
        }
        if (F.newpow) powFBgen(&cache, &F, nf, auts);
        if (!F.sfb_chg) rnd_rel(&cache, &F, nf, auts, fact);
        F.L_jid = F.perm;
      }
      if (precpb)
      {
        pari_sp av3 = avma;
        GEN nf0 = nf;
        if (precadd) { PRECREG += precadd; precadd = 0; }
        else           PRECREG = (PRECREG<<1)-2;
        if (DEBUGLEVEL)
        {
          char str[64]; sprintf(str,"Buchall_param (%s)",precpb);
          pari_warn(warnprec,str,PRECREG);
        }
        nf = gclone( nfnewprec_shallow(nf, PRECREG) );
        if (precdouble) gunclone(nf0);
        avma = av3; precdouble++; precpb = NULL;

        F.newarc = 1;
        for (i = 1; i < lg(PERM); i++) F.perm[i] = PERM[i];
        cache.chk = cache.base; W = NULL; /* recompute arch components + reduce */
      }
      { /* Reduce relation matrices */
        long l = cache.last - cache.chk + 1, j;
        GEN M = nf_get_M(nf), mat = cgetg(l, t_MAT), emb = cgetg(l, t_MAT);
        int first = (W == NULL); /* never reduced before */
        REL_t *rel;

        for (j=1,rel = cache.chk + 1; j < l; rel++,j++)
        {
          gel(mat,j) = rel->R;
          if (!rel->relaut)
            gel(emb,j) = get_log_embed(&F, rel, M, RU, R1, PRECREG);
          else
            gel(emb,j) = perm_log_embed(gel(emb, j-rel->relorig),
                                        gel(F.embperm, rel->relaut));
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
        /* FIXME: replace by err(bugparier,"") */
        if (!need && cache.missing)
        { /* The test above will never be true, but add_rel implicitely assumes
           * that if we have maximal rank for the ideal lattice, then
           * cache.missing == 0. Better safe than sorry. */
          for (i = 1; cache.missing; i++)
            if (!mael(cache.basis, i, i))
            {
              mael(cache.basis, i, i) = 1;
              cache.missing--;
              for (j = i+1; j <= F.KC; j++) mael(cache.basis, j, i) = 0;
            }
        }
        zc = (lg(C)-1) - (lg(B)-1) - (lg(W)-1);
        if (zc < RU-1)
        {
          /* need more columns for units */
          need += RU-1 - zc;
          if (need > F.KC) need = F.KC;
        }
        if (need)
        { /* dependent rows */
          F.L_jid = vecslice(F.perm, 1, need);
          vecsmall_sort(F.L_jid);
          if (need == old_need && !F.newpow) F.sfb_chg = sfb_CHANGE;
          old_need = need;
        }
        else
        {
          /* If the relation lattice is too small, check will be > 1 and we
           * will do a new run of small_norm/rnd_rel asking for 1 relation.
           * However they tend to give a relation involving the first element
           * of L_jid. We thus permute which element is the first of L_jid in
           * order to increase the probability of finding a good relation, i.e.
           * one that increases the relation lattice. */
          if (lg(W) > 2)
          {
            F.L_jid = gcopy(F.perm);
            lswap(F.L_jid[1], F.L_jid[1+(nreldep%(lg(W) - 1))]);
          }
          else
            F.L_jid = F.perm;
        }
      }
    }
    while (need);
    A = vecslice(C, 1, zc); /* cols corresponding to units */
    R = compute_multiple_of_R(A, RU, N, &need, &lambda);
    if (!lambda) { precpb = "bestappr"; continue; }
    if (!R)
    { /* not full rank for units */
      if (DEBUGLEVEL) fprintferr("regulator is zero.\n");
      if (!need) precpb = "regulator";
      continue;
    }

    h = ZM_det_triangular(W);
    if (DEBUGLEVEL) fprintferr("\n#### Tentative class number: %Ps\n", h);

    z = mulrr(Res, resc); /* ~ hR if enough relations, a multiple otherwise */
    switch (compute_R(lambda, divir(h,z), &L, &R))
    {
      case fupb_RELAT:
        need = 1; /* not enough relations */
        continue;
      case fupb_PRECI: /* prec problem unless we cheat on Bach constant */
        if ((precdouble&7) == 7 && cbach<=2) goto START;
        precpb = "compute_R";
        continue;
    }
    /* DONE */

    if (F.KCZ2 > F.KCZ)
    {
      if (F.newpow) powFBgen(NULL, &F, nf, auts);
      if (F.sfb_chg) {
        if (!subFB_change(&F)) goto START;
        if (F.newpow) powFBgen(NULL, &F, nf, auts);
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
      U = ZM_mul(U, ZM_lll(H, 0.99, LLL_IM));
      AU = RgM_mul(A, U);
      A = cleanarch(AU, N, PRECREG);
      if (DEBUGLEVEL) msgtimer("cleanarch");
      if (!A) {
        precadd = (DEFAULTPREC-2) + divsBIL( gexpo(AU) ) - gprecision(AU);
        if (precadd <= 0) precadd = 1;
        precpb = "cleanarch"; continue;
      }
      fu = getfu(nf, &A, &e, PRECREG);
      if ((flun & nf_FORCE) && typ(fu) == t_MAT)
      { /* units not found but we want them */
        if (e > 0)
          pari_err(talker, "bnfinit: fundamental units too large");
        if (e < 0) precadd = (DEFAULTPREC-2) + divsBIL( (-e) );
        avma = av3; precpb = "getfu"; continue;
      }
    }
    /* class group generators */
    i = lg(C)-zc; C += zc; C[0] = evaltyp(t_MAT)|evallg(i);
    C0 = C; C = cleanarch(C, N, PRECREG);
    if (!C) {
      precadd = (DEFAULTPREC-2) + divsBIL( gexpo(C0) ) - gprecision(C0);
      if (precadd <= 0) precadd = 1;
      precpb = "cleanarch";
    }
  } while (need || precpb);

  delete_cache(&cache); delete_FB(&F);
  Vbase = vecpermute(F.LP, F.perm);
  if (DEBUGLEVEL)
    { fprintferr("\n#### Computing class group generators\n"); (void)timer2(); }
  class_group_gen(nf,W,C,Vbase,PRECREG,NULL, &clg1, &clg2);
  if (DEBUGLEVEL) msgtimer("classgroup generators");
  res = get_clfu(clg1, R, zu, fu);
  res = buchall_end(nf,res,clg2,W,B,A,C,Vbase);
  res = gerepilecopy(av0, res); if (precdouble) gunclone(nf);
  return res;
}
