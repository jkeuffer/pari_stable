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
#include "parinf.h"
/********************************************************************/
/**                                                                **/
/**              INSERT PERMANENT OBJECT IN STRUCTURE              **/
/**                                                                **/
/********************************************************************/
static const int OBJMAX = 2; /* maximum number of insertable objects */

/* insert O in S [last position] */
static void
obj_insert(GEN S, GEN O, long K)
{
  long l = lg(S)-1;
  GEN v = (GEN)S[l];
  if (typ(v) != t_VEC)
  {
    GEN w = zerovec(OBJMAX); w[K] = (long)O;
    S[l] = lclone(w);
  }
  else
    v[K] = lclone(O);
}

static GEN
get_extra_obj(GEN S, long K)
{
  GEN v = (GEN)S[lg(S)-1];
  if (typ(v) == t_VEC)
  {
    GEN O = (GEN)v[K];
    if (typ(O) != t_INT) return O;
  }
  return NULL;
}

GEN
check_and_build_obj(GEN S, int tag, GEN (*build)(GEN))
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
extern GEN nfbasic_to_nf(nfbasic_t *T, GEN ro, long prec);
extern GEN get_nfindex(GEN bas);
extern GEN sqred1_from_QR(GEN x, long prec);
extern GEN computeGtwist(GEN nf, GEN vdir);
extern GEN famat_mul(GEN f, GEN g);
extern GEN famat_to_arch(GEN nf, GEN fa, long prec);
extern GEN to_famat_all(GEN x, GEN y);
extern int addcolumntomatrix(GEN V, GEN invp, GEN L);
extern double check_bach(double cbach, double B);
extern GEN gmul_mat_smallvec(GEN x, GEN y);
extern GEN gmul_mati_smallvec(GEN x, GEN y);
extern GEN get_arch(GEN nf,GEN x,long prec);
extern GEN get_arch_real(GEN nf,GEN x,GEN *emb,long prec);
extern GEN get_roots(GEN x,long r1,long prec);
extern long int_elt_val(GEN nf, GEN x, GEN p, GEN b, GEN *t);
extern GEN norm_by_embed(long r1, GEN x);
extern void minim_alloc(long n,double ***q,long **x,double **y,double **z,double **v);
extern GEN arch_mul(GEN x, GEN y);
extern void wr_rel(GEN col);
extern void dbg_rel(long s, GEN col);

#define SFB_MAX 2
#define SFB_STEP 2
#define MIN_EXTRA 1

#define RANDOM_BITS 4
static const int CBUCHG = (1<<RANDOM_BITS) - 1;

/* used by factor[elt|gen|gensimple] to return factorizations of smooth elts
 * HACK: MAX_FACTOR_LEN never checked, we assume default value is enough
 * (since elts have small norm) */
static long primfact[500], exprimfact[500];

/* a factor base contains only non-inert primes
 * KC = # of P in factor base (p <= n, NP <= n2)
 * KC2= # of P assumed to generate class group (NP <= n2)
 *
 * KCZ = # of rational primes under ideals counted by KC
 * KCZ2= same for KC2 */
typedef struct {
  GEN id2;
  GEN alg;
  GEN arc;
  GEN ord;
} powFB_t;

typedef struct {
  GEN FB; /* FB[i] = i-th rational prime used in factor base */
  GEN LP; /* vector of all prime ideals in FB */
  GEN *LV; /* LV[p] = vector of P|p, NP <= n2
            * isclone() is set for LV[p] iff all P|p are in FB
            * LV[i], i not prime or i > n2, is undefined! */
  GEN iLP; /* iLP[p] = i such that LV[p] = [LP[i],...] */
  long KC, KCZ, KCZ2;
  GEN subFB; /* LP o subFB =  part of FB used to build random relations */
  powFB_t *pow;/* array of [P^0,...,P^CBUCHG], P in LP o subFB */
  GEN perm; /* permutation of LP used to represent relations [updated by
               hnfspec/hnfadd: dense rows come first] */
} FB_t;

typedef struct {
  GEN R; /* relation vector as t_VECSMALL */
  int nz; /* index of first non-zero elt in R (hash) */
  GEN m; /* pseudo-minimum yielding the relation */
  GEN ex; /* exponents of subFB elts used to find R */
  powFB_t *pow; /* powsubFB associated to ex [ shared between rels ] */
} REL_t;

typedef struct {
  REL_t *base; /* first rel found */
  REL_t *last; /* last rel found so far */
  REL_t *end; /* target for last relation. base <= last <= end */
  size_t len; /* number of rels pre-allocated in base */
} RELCACHE_t;

/* x a t_VECSMALL */
static long
ccontent(GEN x)
{
  long i, l = lg(x), s = labs(x[1]);
  for (i=2; i<l && s!=1; i++) s = cgcd(x[i],s);
  return s;
}

static void
desallocate(RELCACHE_t *M)
{
  REL_t *rel = M->base;
  powFB_t *old = NULL;
  if (!rel) return;
  for (rel++; rel <= M->last; rel++)
  {
    free((void*)rel->R);
    if (!rel->m) continue;
    gunclone(rel->m); 
    if (!rel->ex) continue;
    gunclone(rel->ex); 
    /* powsubFB shared by consecutive rels: unclone it once */
    if (rel->pow != old)
    {
      gunclone(rel->pow->id2);
      gunclone(rel->pow->alg);
      gunclone(rel->pow->ord);
      if (rel->pow->arc) gunclone(rel->pow->arc);
      old = rel->pow; free((void*)old);
    }
  }
  free((void*)M->base);
  M->last = M->base = NULL;
}

GEN
cgetalloc(GEN x, size_t l, long t)
{
  x = (GEN)gprealloc((void*)x, l * sizeof(long));
  x[0] = evaltyp(t) | evallg(l); return x;
}

static void
reallocate(RELCACHE_t *M, long max)
{
  size_t l = max+1, gap = M->last - M->base;
  M->base = (REL_t*)gprealloc((void*)M->base, l * sizeof(REL_t));
  M->last = M->base + gap;
}

/* don't take P|p if P ramified, or all other Q|p already there */
static int
ok_subFB(FB_t *F, long t, GEN D)
{
  GEN LP, P = (GEN)F->LP[t];
  long p = itos((GEN)P[1]);
  LP = F->LV[p];
  return smodis(D,p) && (!isclone(LP) || t != F->iLP[p] + lg(LP)-1);
}

/* set subFB, reset F->pow
 * Fill F->perm (if != NULL): primes ideals sorted by increasing norm (except
 * the ones in subFB come first [dense rows for hnfspec]) */
static int
subFBgen(FB_t *F, GEN nf, double PROD, long minsFB)
{
  GEN y, perm, yes, no, D = (GEN)nf[3];
  long i, j, k, iyes, ino, lv = F->KC + 1;
  double prod;
  const int init = (F->perm == NULL);
  pari_sp av;

  if (init)
  {
    F->LP   = cgetg(lv, t_VEC);
    F->perm = cgetg(lv, t_VECSMALL);
  }

  av = avma;
  y = cgetg(lv,t_COL); /* Norm P */
  for (k=0, i=1; i <= F->KCZ; i++)
  {
    GEN LP = F->LV[F->FB[i]];
    long l = lg(LP);
    for (j = 1; j < l; j++)
    {
      GEN P = (GEN)LP[j];
      k++;
      y[k]     = (long)powgi((GEN)P[1], (GEN)P[4]);
      F->LP[k] = (long)P; /* noop if init = 1 */
    }
  }
  /* perm sorts LP by increasing norm */
  perm = sindexsort(y);
  no  = cgetg(lv, t_VECSMALL); ino  = 1;
  yes = cgetg(lv, t_VECSMALL); iyes = 1;
  prod = 1.0;
  for (i = 1; i < lv; i++)
  {
    long t = perm[i];
    if (!ok_subFB(F, t, D)) { no[ino++] = t; continue; }

    yes[iyes++] = t;
    prod *= (double)itos((GEN)y[t]);
    if (iyes > minsFB && prod > PROD) break;
  }
  if (i == lv) return 0;
  avma = av; /* HACK: gcopy(yes) still safe */
  if (init)
  {
    GEN p = F->perm;
    for (j=1; j<iyes; j++)     p[j] = yes[j];
    for (i=1; i<ino; i++, j++) p[j] =  no[i];
    for (   ; j<lv; j++)       p[j] =  perm[j];
  }
  setlg(yes, iyes);
  F->subFB = gcopy(yes);
  F->pow = NULL; return 1;
}
static int
subFBgen_increase(FB_t *F, GEN nf, long step)
{
  GEN yes, D = (GEN)nf[3];
  long i, iyes, lv = F->KC + 1, minsFB = lg(F->subFB)-1 + step;

  yes = cgetg(minsFB+1, t_VECSMALL); iyes = 1;
  for (i = 1; i < lv; i++)
  {
    long t = F->perm[i];
    if (!ok_subFB(F, t, D)) continue;

    yes[iyes++] = t;
    if (iyes > minsFB) break;
  }
  if (i == lv) return 0;
  F->subFB = yes;
  F->pow = NULL; return 1;
}

static GEN
mulred(GEN nf, GEN x, GEN I, GEN *pm)
{
  GEN m, y = cgetg(3,t_VEC);
  y[1] = (long)idealmulh(nf, I, x);
  y[2] = lgetg(1, t_MAT);
  y = ideallllred(nf, y, NULL, 0);
  m = (GEN)y[2];
  y = (GEN)y[1]; *pm = lg(m)==1? gun: gmael(m, 1, 1);
  return is_pm1(gcoeff(y,1,1))? NULL: ideal_two_elt(nf,y);
}

/* Compute powers of prime ideals (P^0,...,P^a) in subFB (a > 1) */
static void
powFBgen(FB_t *F, GEN nf, long a)
{
  pari_sp av = avma;
  long i, j, n = lg(F->subFB);
  GEN Id2, Alg, Ord;

  if (DEBUGLEVEL) fprintferr("Computing powers for sub-factor base:\n");
  F->pow = (powFB_t*) gpmalloc(sizeof(powFB_t));
  Id2 = cgetg(n, t_VEC);
  Alg = cgetg(n, t_VEC);
  Ord = cgetg(n, t_VECSMALL);
  F->pow->arc = NULL;
  for (i=1; i<n; i++)
  {
    GEN m, alg, id2, vp = (GEN)F->LP[ F->subFB[i] ];
    GEN z = cgetg(3,t_VEC); z[1] = vp[1]; z[2] = vp[2];
    id2 = cgetg(a+1,t_VEC); Id2[i] = (long)id2; id2[1] = (long)z;
    alg = cgetg(a+1,t_VEC); Alg[i] = (long)alg; alg[1] = un;
    vp = prime_to_ideal(nf,vp);
    for (j=2; j<=a; j++)
    {
      GEN J = mulred(nf, (GEN)id2[j-1], vp, &m);
      if (!J) break; /* id2[j] = 1. Use it to reduce exponents later */
      id2[j] = (long)J;
      alg[j] = (long)m;
      if (DEBUGLEVEL>1) fprintferr(" %ld",j);
    }
    setlg(id2, j);
    setlg(alg, j); Ord[i] = j - 1;
    if (DEBUGLEVEL>1) fprintferr("\n");
  }
  F->pow->id2 = gclone(Id2);
  F->pow->ord = gclone(Ord);
  F->pow->alg = gclone(Alg); avma = av;
  if (DEBUGLEVEL) msgtimer("powFBgen");
}

/* Compute FB, LV, iLP + KC*. Reset perm
 * n2: bound for norm of tested prime ideals (includes be_honest())
 * n : bound for p, such that P|p (NP <= n2) used to build relations

 * Return prod_{p<=n2} (1-1/p) / prod_{Norm(P)<=n2} (1-1/Norm(P)),
 * close to residue of zeta_K at 1 = 2^r1 (2pi)^r2 h R / (w D) */
static GEN
FBgen(FB_t *F, GEN nf,long n2,long n)
{
  byteptr delta = diffptr;
  long i, p, ip;
  GEN prim, Res;

  maxprime_check((ulong)n2);
  F->FB  = cgetg(n2+1, t_VECSMALL);
  F->iLP = cgetg(n2+1, t_VECSMALL);
  F->LV = (GEN*)new_chunk(n2+1);

  Res = realun(DEFAULTPREC);
  prim = icopy(gun);
  i = ip = 0;
  F->KC = F->KCZ = 0;
  for (p = 0;;) /* p <= n2 */
  {
    pari_sp av = avma, av1;
    long k, l;
    GEN P, a, b;

    NEXT_PRIME_VIADIFF(p, delta);
    if (!F->KC && p > n) { F->KCZ = i; F->KC = ip; }
    if (p > n2) break;

    if (DEBUGLEVEL>1) { fprintferr(" %ld",p); flusherr(); }
    prim[2] = p; P = primedec(nf,prim); l = lg(P);

    /* a/b := (p-1)/p * prod_{P|p, NP <= n2} NP / (NP-1) */
    av1 = avma; a = b = NULL;
    for (k=1; k<l; k++)
    {
      GEN NormP = powgi(prim, gmael(P,k,4));
      long nor;
      if (is_bigint(NormP) || (nor=NormP[2]) > n2) break;

      if (a) { a = mului(nor, a); b = mului(nor-1, b); }
      else   { a = utoi(nor / p); b = utoi((nor-1) / (p-1)); }
    }
    if (a) affrr(divri(mulir(a,Res),b),   Res);
    else   affrr(divrs(mulsr(p-1,Res),p), Res);
    avma = av1;
    if (l == 2 && itos(gmael(P,1,3)) == 1) continue; /* p inert */

    /* keep non-inert ideals with Norm <= n2 */
    if (k == l)
      setisclone(P); /* flag it: all prime divisors in FB */
    else
      { setlg(P,k); P = gerepilecopy(av,P); }
    F->FB[++i]= p;
    F->LV[p]  = P;
    F->iLP[p] = ip; ip += k-1;
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
      for (i=1; i<=F->KCZ; i++) fprintferr("++ LV[%ld] = %Z",i,F->LV[F->FB[i]]);
    }
    msgtimer("factor base");
  }
  F->perm = NULL; return Res;
}

/*  SMOOTH IDEALS */
static void
store(long i, long e)
{
  primfact[++primfact[0]] = i; /* index */
  exprimfact[primfact[0]] = e; /* exponent */
}

/* divide out x by all P|p, where x as in can_factor().  k = v_p(Nx) */
static int
divide_p_elt(FB_t *F, long p, long k, GEN nf, GEN m)
{
  GEN P, LP = F->LV[p];
  long j, v, l = lg(LP), ip = F->iLP[p];
  for (j=1; j<l; j++)
  {
    P = (GEN)LP[j];
    v = int_elt_val(nf, m, (GEN)P[1], (GEN)P[5], NULL); /* v_P(m) */
    if (!v) continue;
    store(ip + j, v); /* v = v_P(m) > 0 */
    k -= v * itos((GEN)P[4]);
    if (!k) return 1;
  }
  return 0;
}
static int
divide_p_id(FB_t *F, long p, long k, GEN nf, GEN I)
{
  GEN P, LP = F->LV[p];
  long j, v, l = lg(LP), ip = F->iLP[p];
  for (j=1; j<l; j++)
  {
    P = (GEN)LP[j];
    v = idealval(nf,I, P);
    if (!v) continue;
    store(ip + j, v); /* v = v_P(I) > 0 */
    k -= v * itos((GEN)P[4]);
    if (!k) return 1;
  }
  return 0;
}
static int
divide_p_quo(FB_t *F, long p, long k, GEN nf, GEN I, GEN m)
{
  GEN P, LP = F->LV[p];
  long j, v, l = lg(LP), ip = F->iLP[p];
  for (j=1; j<l; j++)
  {
    P = (GEN)LP[j];
    v = int_elt_val(nf, m, (GEN)P[1], (GEN)P[5], NULL); /* v_P(m) */
    if (!v) continue;
    v = idealval(nf,I, P) - v;
    if (!v) continue;
    store(ip + j, v); /* v = v_P(I / m) < 0 */
    k += v * itos((GEN)P[4]);
    if (!k) return 1;
  }
  return 0;
}

/* is *N > 0 a smooth rational integer wrt F ? (put the exponents in *ex) */
static int
smooth_int(FB_t *F, GEN *N, GEN *ex)
{
  GEN q, r, FB = F->FB;
  const long KCZ = F->KCZ;
  const long limp = FB[KCZ]; /* last p in FB */
  long i, p, k;

  *ex = new_chunk(KCZ+1);
  for (i=1; ; i++)
  {
    p = FB[i]; q = dvmdis(*N,p,&r);
    for (k=0; !signe(r); k++) { *N = q; q = dvmdis(*N, p, &r); }
    (*ex)[i] = k;
    if (cmpis(q,p) <= 0) break;
    if (i == KCZ) return 0;
  }
  (*ex)[0] = i;
  return (cmpis(*N,limp) <= 0);
}

static int
divide_p(FB_t *F, long p, long k, GEN nf, GEN I, GEN m)
{
  if (!m) return divide_p_id (F,p,k,nf,I);
  if (!I) return divide_p_elt(F,p,k,nf,m);
  return divide_p_quo(F,p,k,nf,I,m);
}

/* Let x = m if I == NULL,
 *         I if m == NULL,
 *         I/m otherwise. [ FIXME: should be m / I. More natural, and
 *                          simplifies get_log_embed ]
 * Can we factor x ? N = Norm x > 0 */
static long
can_factor(FB_t *F, GEN nf, GEN I, GEN m, GEN N)
{
  GEN ex;
  long i;
  primfact[0] = 0;
  if (is_pm1(N)) return 1;
  if (!smooth_int(F, &N, &ex)) return 0;
  for (i=1; i<=ex[0]; i++)
    if (ex[i] && !divide_p(F, F->FB[i], ex[i], nf, I, m)) return 0;
  return is_pm1(N) || divide_p(F, itos(N), 1, nf, I, m);
}

/* can we factor I/m ? [m in I from pseudomin] */
static long
factorgen(FB_t *F, GEN nf, GEN I, GEN m)
{
  GEN Nm = absi( subres(gmul((GEN)nf[7],m), (GEN)nf[1]) ); /* |Nm| */
  GEN N  = diviiexact(Nm, dethnf_i(I)); /* N(m / I) */
  return can_factor(F, nf, I, m, N);
}

/*  FUNDAMENTAL UNITS */

/* a, m real. Return  (Re(x) + a) + I * (Im(x) % m) */
static GEN
addRe_modIm(GEN x, GEN a, GEN m)
{
  GEN re, im, z;
  if (typ(x) == t_COMPLEX)
  {
    re = gadd((GEN)x[1], a);
    im = gmod((GEN)x[2], m);
    if (gcmp0(im)) z = re;
    else
    {
      z = cgetg(3,t_COMPLEX);
      z[1] = (long)re;
      z[2] = (long)im;
    }
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
    for (i=1; i < lg(x); i++)
      y[i] = (long)cleanarch((GEN)x[i], N, prec);
    return y;
  }
  if (!is_vec_t(tx)) err(talker,"not a vector/matrix in cleanarch");
  RU = lg(x)-1; R1 = (RU<<1)-N;
  s = gdivgs(sum(greal(x), 1, RU), -N); /* -log |norm(x)| / N */
  y = cgetg(RU+1,tx);
  pi2 = Pi2n(1, prec);
  for (i=1; i<=R1; i++) y[i] = (long)addRe_modIm((GEN)x[i], s, pi2);
  if (i <= RU)
  {
    GEN pi4 = Pi2n(2, prec), s2 = gmul2n(s, 1);
    for (   ; i<=RU; i++) y[i] = (long)addRe_modIm((GEN)x[i], s2, pi4);
  }
  return y;
}

static GEN
not_given(pari_sp av, long fl, long reason)
{
  if (! (fl & nf_FORCE))
  {
    char *s;
    switch(reason)
    {
      case fupb_LARGE: s="fundamental units too large"; break;
      case fupb_PRECI: s="insufficient precision for fundamental units"; break;
      default: s="unknown problem with fundamental units";
    }
    err(warner,"%s, not given",s);
  }
  avma = av; return cgetg(1,t_MAT);
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
      if (typ(p1)==t_COMPLEX) p1 = (GEN)p1[1];
      e = gexpo(p1); if (e>E) E=e;
    }
  return E;
}

static GEN
split_realimag_col(GEN z, long r1, long r2)
{
  long i, ru = r1+r2;
  GEN a, x = cgetg(ru+r2+1,t_COL), y = x + r2;
  for (i=1; i<=r1; i++) { a = (GEN)z[i]; x[i] = lreal(a); }
  for (   ; i<=ru; i++) { a = (GEN)z[i]; x[i] = lreal(a); y[i] = limag(a); }
  return x;
}

GEN
split_realimag(GEN x, long r1, long r2)
{
  long i,l; GEN y;
  if (typ(x) == t_COL) return split_realimag_col(x,r1,r2);
  l = lg(x); y = cgetg(l, t_MAT);
  for (i=1; i<l; i++) y[i] = (long)split_realimag_col((GEN)x[i], r1, r2);
  return y;
}

/* assume x = (r1+r2) x (r1+2r2) matrix and y compatible vector
 * r1 first lines of x,y are real. Solve the system obtained by splitting
 * real and imaginary parts. If x is of nf type, use M instead.
 */
GEN
gauss_realimag(GEN x, GEN y)
{
  GEN M = (typ(x)==t_VEC)? gmael(checknf(x),5,1): x;
  long l = lg(M), r2 = l - lg(M[1]), r1 = l-1 - 2*r2;
  M = split_realimag(M,r1,r2);
  y = split_realimag(y,r1,r2); return gauss(M, y);
}

GEN
getfu(GEN nf,GEN *ptA,long fl,long *pte,long prec)
{
  long e, i, j, R1, RU, N=degpol(nf[1]);
  pari_sp av = avma;
  GEN p1,p2,u,y,matep,s,A,vec;

  if (DEBUGLEVEL) fprintferr("\n#### Computing fundamental units\n");
  R1 = itos(gmael(nf,2,1)); RU = (N+R1)>>1;
  if (RU==1) { *pte=BIGINT; return cgetg(1,t_VEC); }

  *pte = 0; A = *ptA;
  matep = cgetg(RU,t_MAT);
  for (j=1; j<RU; j++)
  {
    s = gzero; for (i=1; i<=RU; i++) s = gadd(s,greal(gcoeff(A,i,j)));
    s = gdivgs(s, -N);
    p1=cgetg(RU+1,t_COL); matep[j]=(long)p1;
    for (i=1; i<=R1; i++) p1[i] = ladd(s, gcoeff(A,i,j));
    for (   ; i<=RU; i++) p1[i] = ladd(s, gmul2n(gcoeff(A,i,j),-1));
  }
  if (prec <= 0) prec = gprecision(A);
  u = lllintern(greal(matep),100,1,prec);
  if (!u) return not_given(av,fl,fupb_PRECI);

  p1 = gmul(matep,u);
  if (expgexpo(p1) > 20) { *pte = BIGINT; return not_given(av,fl,fupb_LARGE); }
  matep = gexp(p1,prec);
  y = grndtoi(gauss_realimag(nf,matep), &e);
  *pte = -e;
  if (e >= 0) return not_given(av,fl,fupb_PRECI);
  for (j=1; j<RU; j++)
    if (!gcmp1(idealnorm(nf, (GEN)y[j]))) break;
  if (j < RU) { *pte = 0; return not_given(av,fl,fupb_PRECI); }
  A = gmul(A,u);

  /* y[i] are unit generators. Normalize: smallest L2 norm + lead coeff > 0 */
  y = gmul((GEN)nf[7], y);
  vec = cgetg(RU+1,t_COL);
  p1 = PiI2n(0,prec); for (i=1; i<=R1; i++) vec[i] = (long)p1;
  p2 = PiI2n(1,prec); for (   ; i<=RU; i++) vec[i] = (long)p2;
  for (j=1; j<RU; j++)
  {
    p1 = (GEN)y[j]; p2 = QX_invmod(p1, (GEN)nf[1]);
    if (gcmp(QuickNormL2(p2,DEFAULTPREC),
             QuickNormL2(p1,DEFAULTPREC)) < 0)
    {
      A[j] = lneg((GEN)A[j]);
      p1 = p2;
    }
    if (gsigne(leading_term(p1)) < 0)
    {
      A[j] = ladd((GEN)A[j], vec);
      p1 = gneg(p1);
    }
    y[j] = (long)p1;
  }
  if (DEBUGLEVEL) msgtimer("getfu");
  gerepileall(av,2, &A, &y);
  *ptA = A; return y;
}

GEN
buchfu(GEN bnf)
{
  long c;
  pari_sp av = avma;
  GEN nf,A,res, y = cgetg(3,t_VEC);

  bnf = checkbnf(bnf); A = (GEN)bnf[3]; nf = (GEN)bnf[7];
  res = (GEN)bnf[8];
  if (lg(res)==7 && lg(res[5])==lg(nf[6])-1)
  {
    y[1] = lcopy((GEN)res[5]);
    y[2] = lcopy((GEN)res[6]); return y;
  }
  y[1] = (long)getfu(nf, &A, nf_UNITS, &c, 0);
  y[2] = lstoi(c); return gerepilecopy(av, y);
}

/*******************************************************************/
/*                                                                 */
/*           PRINCIPAL IDEAL ALGORITHM (DISCRETE LOG)              */
/*                                                                 */
/*******************************************************************/

/* gen: prime ideals, return Norm (product), bound for denominator.
 * C = possible extra prime (^1) or NULL */
static GEN
get_norm_fact_primes(GEN gen, GEN ex, GEN C, GEN *pd)
{
  GEN N,d,P,p,e;
  long i,s,c = lg(ex);
  d = N = gun;
  for (i=1; i<c; i++)
    if ((s = signe(ex[i])))
    {
      P = (GEN)gen[i]; e = (GEN)ex[i]; p = (GEN)P[1];
      N = gmul(N, powgi(p, mulii((GEN)P[4], e)));
      if (s < 0)
      {
        e = gceil(gdiv(negi(e), (GEN)P[3]));
        d = mulii(d, powgi(p, e));
      }
    }
  if (C)
  {
    P = C; p = (GEN)P[1];
    N = gmul(N, powgi(p, (GEN)P[4]));
  }
  *pd = d; return N;
}

/* gen: HNF ideals */
static GEN
get_norm_fact(GEN gen, GEN ex, GEN *pd)
{
  long i, c = lg(ex);
  GEN d,N,I,e,n,ne,de;
  d = N = gun;
  for (i=1; i<c; i++)
    if (signe(ex[i]))
    {
      I = (GEN)gen[i]; e = (GEN)ex[i]; n = dethnf_i(I);
      ne = powgi(n,e);
      de = egalii(n, gcoeff(I,1,1))? ne: powgi(gcoeff(I,1,1), e);
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
    pr = (GEN)FB[i]; p = itos((GEN)pr[1]);
    if (p > pmax) pmax = p;
  }
  L = cgetg(pmax+1, t_VEC);
  for (p=1; p<=pmax; p++) L[p] = 0;
  if (list_pr)
  {
    for (i=1; i<l; i++)
    {
      pr = (GEN)FB[i]; p = itos((GEN)pr[1]);
      if (!L[p]) L[p] = (long)cget1(N+1, t_VEC);
      appendL((GEN)L[p], pr);
    }
    for (p=1; p<=pmax; p++)
      if (L[p]) L[p] = (long)gen_sort((GEN)L[p],0,cmp_prime_over_p);
  }
  else
  {
    for (i=1; i<l; i++)
    {
      pr = (GEN)FB[i]; p = itos((GEN)pr[1]);
      if (!L[p]) L[p] = (long)cget1(N+1, t_VECSMALL);
      appendL((GEN)L[p], (GEN)i);
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
#if 1 /* for debugging */
  for (p=1;p<l;p++) FB[p]=iLP[p]=LV[p]=0;
#endif
  for (p = 2; p < l; p++)
  {
    if (!L[p]) continue;
    FB[++i] = p;
    LV[p] = (long)vecextract_p(Vbase, (GEN)L[p]);
    iLP[p]= ip; ip += lg(L[p])-1;
  }
  F->KCZ = i;
  F->FB = FB; setlg(FB, i+1);
  F->LV = (GEN*)LV;
  F->iLP= iLP; return L;
}

static GEN
init_famat(GEN x)
{
  GEN y = cgetg(3, t_VEC);
  y[1] = (long)x;
  y[2] = lgetg(1,t_MAT); return y;
}

/* add v^e to factorization */
static void
add_to_fact(long v, long e)
{
  long i, l = primfact[0];
  for (i=1; i<=l && primfact[i] < v; i++)/*empty*/;
  if (i <= l && primfact[i] == v) exprimfact[i] += e; else store(v, e);
}

/* L (small) list of primes above the same p including pr. Return pr index */
static int
pr_index(GEN L, GEN pr)
{
  long j, l = lg(L);
  GEN al = (GEN)pr[2];
  for (j=1; j<l; j++)
    if (gegal(al, gmael(L,j,2))) return j;
  err(bugparier,"codeprime");
  return 0; /* not reached */
}

static long
Vbase_to_FB(FB_t *F, GEN pr)
{
  long p = itos((GEN)pr[1]);
  return F->iLP[p] + pr_index(F->LV[p], pr);
}

/* return famat y (principal ideal) such that x / y is smooth [wrt Vbase] */
static GEN
SPLIT(FB_t *F, GEN nf, GEN x, GEN Vbase)
{
  GEN vdir, id, z, ex, y, x0;
  long nbtest_lim, nbtest, bou, i, ru, lgsub;
  int flag = (gexpo(gcoeff(x,1,1)) < 100);

  /* try without reduction if x is small */
  if (flag && can_factor(F, nf, x, NULL, dethnf_i(x))) return NULL;

  /* if reduction fails (y scalar), do not retry can_factor */
  y = idealred_elt(nf,x);
  if ((!flag || !isnfscalar(y)) && factorgen(F, nf, x, y)) return y;

  /* reduce in various directions */
  ru = lg(nf[6]);
  vdir = cgetg(ru,t_VECSMALL);
  for (i=2; i<ru; i++) vdir[i]=0;
  for (i=1; i<ru; i++)
  {
    vdir[i] = 10;
    y = ideallllred_elt(nf,x,vdir);
    if (factorgen(F, nf, x, y)) return y;
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
    if (DEBUGLEVEL>2) fprintferr("# ideals tried = %ld\n",nbtest);
    id = x0;
    for (i=1; i<lgsub; i++)
    {
      ex[i] = random_bits(RANDOM_BITS);
      if (ex[i])
      { /* avoid prec pb: don't let id become too large as lgsub increases */
        if (id != x0) id = ideallllred(nf,id,NULL,0);
        z[1] = Vbase[i];
        id = idealmulh(nf, id, idealpowred(nf,z,stoi(ex[i]),0));
      }
    }
    if (id == x0) continue;

    for (i=1; i<ru; i++) vdir[i] = random_bits(RANDOM_BITS);
    for (bou=1; bou<ru; bou++)
    {
      y = ideallllred_elt(nf, (GEN)id[1], vdir);
      if (factorgen(F, nf, (GEN)id[1], y))
      {
        for (i=1; i<lgsub; i++)
          if (ex[i]) add_to_fact(Vbase_to_FB(F,(GEN)Vbase[i]), -ex[i]);
        return famat_mul((GEN)id[2], y);
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
      else nbtest_lim = VERYBIGINT; /* don't increase further */
      if (DEBUGLEVEL) fprintferr("SPLIT: increasing factor base [%ld]\n",lgsub);
    }
  }
}

static GEN
split_ideal(GEN nf, GEN x, GEN Vbase)
{
  FB_t F;
  GEN L = recover_partFB(&F, Vbase, lg(x)-1);
  GEN y = SPLIT(&F, nf, x, Vbase);
  long p,j, i, l = lg(F.FB);

  p = j = 0; /* -Wall */
  for (i=1; i<=primfact[0]; i++)
  { /* decode index C = ip+j --> (p,j) */
    long q,k,t, C = primfact[i];
    for (t=1; t<l; t++)
    {
      q = F.FB[t];
      k = C - F.iLP[q];
      if (k <= 0) break;
      p = q;
      j = k;
    }
    primfact[i] = mael(L, p, j);
  }
  return y;
}

/* return sorted vectbase [sorted in bnf since version 2.2.4] */
static GEN
get_Vbase(GEN bnf)
{
  GEN vectbase = (GEN)bnf[5], perm = (GEN)bnf[6], Vbase;
  long i, l, tx = typ(perm);

  if (tx == t_INT) return vectbase;
  /* old format */
  l = lg(vectbase); Vbase = cgetg(l,t_VEC);
  for (i=1; i<l; i++) Vbase[i] = vectbase[itos((GEN)perm[i])];
  return Vbase;
}

/* all primes up to Minkowski bound factor on factorbase ? */
void
testprimes(GEN bnf, long bound)
{
  pari_sp av0 = avma, av;
  long p,i,nbideal,k,pmax;
  GEN f, dK, p1, Vbase, vP, fb, nf=checknf(bnf);
  byteptr d = diffptr;
  FB_t F;

  if (DEBUGLEVEL>1)
    fprintferr("PHASE 1: check primes to Zimmert bound = %ld\n\n",bound);
  dK= (GEN)nf[3];
  f = (GEN)nf[4];
  if (!gcmp1(f))
  {
    GEN D = gmael(nf,5,5);
    if (DEBUGLEVEL>1) fprintferr("**** Testing Different = %Z\n",D);
    p1 = isprincipalall(bnf, D, nf_FORCE);
    if (DEBUGLEVEL>1) fprintferr("     is %Z\n", p1);
  }
  /* sort factorbase for tablesearch */
  fb = gen_sort((GEN)bnf[5], 0, &cmp_prime_ideal);
  p1 = gmael(fb, lg(fb)-1, 1); /* largest p in factorbase */
  pmax = is_bigint(p1)? VERYBIGINT: itos(p1);
  maxprime_check((ulong)bound);
  Vbase = get_Vbase(bnf);
  (void)recover_partFB(&F, Vbase, degpol(nf[1]));
  for (av=avma, p=0; p < bound; avma=av)
  {
    NEXT_PRIME_VIADIFF(p, d);
    if (DEBUGLEVEL>1) fprintferr("*** p = %ld\n",p);
    vP = primedec(bnf, stoi(p));
    nbideal = lg(vP)-1;
    /* loop through all P | p if ramified, all but one otherwise */
    if (!smodis(dK,p)) nbideal++;
    for (i=1; i<nbideal; i++)
    {
      GEN P = (GEN)vP[i];
      if (DEBUGLEVEL>1) fprintferr("  Testing P = %Z\n",P);
      if (cmpis(idealnorm(bnf,P), bound) >= 0)
      {
        if (DEBUGLEVEL>1) fprintferr("    Norm(P) > Zimmert bound\n");
        continue;
      }
      if (p <= pmax && (k = tablesearch(fb, P, &cmp_prime_ideal)))
      { if (DEBUGLEVEL>1) fprintferr("    #%ld in factor base\n",k); }
      else if (DEBUGLEVEL>1)
        fprintferr("    is %Z\n", isprincipal(bnf,P));
      else /* faster: don't compute result */
        (void)SPLIT(&F, nf, prime_to_ideal(nf,P), Vbase);
    }
  }
  if (DEBUGLEVEL>1) { fprintferr("End of PHASE 1.\n\n"); flusherr(); }
  avma = av0;
}

GEN
init_red_mod_units(GEN bnf, long prec)
{
  GEN z, s = gzero, p1,s1,mat, matunit = (GEN)bnf[3];
  long i,j, RU = lg(matunit);

  if (RU == 1) return NULL;
  mat = cgetg(RU,t_MAT);
  for (j=1; j<RU; j++)
  {
    p1=cgetg(RU+1,t_COL); mat[j]=(long)p1;
    s1=gzero;
    for (i=1; i<RU; i++)
    {
      p1[i] = lreal(gcoeff(matunit,i,j));
      s1 = gadd(s1, gsqr((GEN)p1[i]));
    }
    p1[RU]=zero; if (gcmp(s1,s) > 0) s = s1;
  }
  s = gsqrt(gmul2n(s,RU),prec);
  if (gcmpgs(s,100000000) < 0) s = stoi(100000000);
  z = cgetg(3,t_VEC);
  z[1] = (long)mat;
  z[2] = (long)s; return z;
}

/* z computed above. Return unit exponents that would reduce col (arch) */
GEN
red_mod_units(GEN col, GEN z, long prec)
{
  long i,RU;
  GEN x,mat,N2;

  if (!z) return NULL;
  mat= (GEN)z[1];
  N2 = (GEN)z[2];
  RU = lg(mat); x = cgetg(RU+1,t_COL);
  for (i=1; i<RU; i++) x[i]=lreal((GEN)col[i]);
  x[RU] = (long)N2;
  x = lllintern(concatsp(mat,x),100, 1,prec);
  if (!x) return NULL;
  x = (GEN)x[RU];
  if (signe(x[RU]) < 0) x = gneg_i(x);
  if (!gcmp1((GEN)x[RU])) err(bugparier,"red_mod_units");
  setlg(x,RU); return x;
}

/* clg2 format changed for version 2.0.21 (contained ideals, now archs)
 * Compatibility mode: old clg2 format */
static GEN
get_Garch(GEN nf, GEN gen, GEN clg2, long prec)
{
  long i,c;
  GEN g,z,J,Garch, clorig = (GEN)clg2[3];

  c = lg(gen); Garch = cgetg(c,t_MAT);
  for (i=1; i<c; i++)
  {
    g = (GEN)gen[i];
    z = (GEN)clorig[i]; J = (GEN)z[1];
    if (!gegal(g,J))
    {
      z = idealinv(nf,z); J = (GEN)z[1];
      J = gmul(J,denom(J));
      if (!gegal(g,J))
      {
        z = ideallllred(nf,z,NULL,prec); J = (GEN)z[1];
        if (!gegal(g,J))
          err(bugparier,"isprincipal (incompatible bnf generators)");
      }
    }
    Garch[i] = z[2];
  }
  return Garch;
}

/* [x] archimedian components, A column vector. return [x] A
 * x may be a translated GEN (y + k) */
static GEN
act_arch(GEN A, GEN x)
{
  GEN a;
  long i,l = lg(A), tA = typ(A);
  if (tA == t_MAT)
  {
    /* assume lg(x) >= l */
    a = cgetg(l, t_VEC);
    for (i=1; i<l; i++) a[i] = (long)act_arch((GEN)A[i], x);
    return a;
  }
  if (l==1) return cgetg(1, t_VEC);
  if (tA == t_VECSMALL)
  {
    a = gmulsg(A[1], (GEN)x[1]);
    for (i=2; i<l; i++)
      if (A[i]) a = gadd(a, gmulsg(A[i], (GEN)x[i]));
  }
  else
  { /* A a t_COL of t_INT. Assume lg(A)==lg(x) */
    a = gmul((GEN)A[1], (GEN)x[1]);
    for (i=2; i<l; i++)
      if (signe(A[i])) a = gadd(a, gmul((GEN)A[i], (GEN)x[i]));
  }
  settyp(a, t_VEC); return a;
}

static long
prec_arch(GEN bnf)
{
  GEN a = (GEN)bnf[4];
  long i, l = lg(a), prec;

  for (i=1; i<l; i++)
    if ( (prec = gprecision((GEN)a[i])) ) return prec;
  return DEFAULTPREC;
}

/* col = archimedian components of x, Nx = kNx^e its norm, dx a bound for its
 * denominator. Return x or NULL (fail) */
GEN
isprincipalarch(GEN bnf, GEN col, GEN kNx, GEN e, GEN dx, long *pe)
{
  GEN nf, x, matunit, s;
  long N, R1, RU, i, prec = gprecision(col);
  bnf = checkbnf(bnf); nf = checknf(bnf);
  if (!prec) prec = prec_arch(bnf);
  matunit = (GEN)bnf[3];
  N = degpol(nf[1]);
  R1 = itos(gmael(nf,2,1));
  RU = (N + R1)>>1;
  col = cleanarch(col,N,prec); settyp(col, t_COL);
  if (RU > 1)
  { /* reduce mod units */
    GEN u, z = init_red_mod_units(bnf,prec);
    u = red_mod_units(col,z,prec);
    if (!u && z) return NULL;
    if (u) col = gadd(col, gmul(matunit, u));
  }
  s = gdivgs(gmul(e, glog(kNx,prec)), N);
  for (i=1; i<=R1; i++) col[i] = lexp(gadd(s, (GEN)col[i]),prec);
  for (   ; i<=RU; i++) col[i] = lexp(gadd(s, gmul2n((GEN)col[i],-1)),prec);
  /* d.alpha such that x = alpha \prod gj^ej */
  x = grndtoi(gmul(dx, gauss_realimag(nf,col)), pe);
  return (*pe > -5)? NULL: gdiv(x, dx);
}

/* y = C \prod g[i]^e[i] ? */
static int
fact_ok(GEN nf, GEN y, GEN C, GEN g, GEN e)
{
  pari_sp av = avma;
  long i, c = lg(e);
  GEN z = C? C: gun;
  for (i=1; i<c; i++)
    if (signe(e[i])) z = idealmul(nf, z, idealpow(nf, (GEN)g[i], (GEN)e[i]));
  if (typ(z) != t_MAT) z = idealhermite(nf,z);
  if (typ(y) != t_MAT) y = idealhermite(nf,y);
  i = gegal(y, z); avma = av; return i;
}

/* assume x in HNF. cf class_group_gen for notations */
static GEN
_isprincipal(GEN bnf, GEN x, long *ptprec, long flag)
{
  long i,lW,lB,e,c, prec = *ptprec;
  GEN Q,xar,Wex,Bex,U,y,p1,gen,cyc,xc,ex,d,col,A;
  GEN W       = (GEN)bnf[1];
  GEN B       = (GEN)bnf[2];
  GEN WB_C    = (GEN)bnf[4];
  GEN nf      = (GEN)bnf[7];
  GEN clg2    = (GEN)bnf[9];
  int old_format = (typ(clg2[2]) == t_MAT);

  U = (GEN)clg2[1]; if (old_format) U = ginv(U);
  cyc = gmael3(bnf,8,1,2); c = lg(cyc)-1;
  gen = gmael3(bnf,8,1,3);
  ex = cgetg(c+1,t_COL);
  if (c == 0 && !(flag & (nf_GEN|nf_GENMAT|nf_GEN_IF_PRINCIPAL))) return ex;

  /* factor x */
  x = Q_primitive_part(x, &xc);
  xar = split_ideal(nf,x,get_Vbase(bnf));
  lW = lg(W)-1; Wex = vecsmall_const(lW, 0);
  lB = lg(B)-1; Bex = vecsmall_const(lB, 0);
  for (i=1; i<=primfact[0]; i++)
  {
    long k = primfact[i];
    long l = k - lW;
    if (l <= 0) Wex[k] = exprimfact[i];
    else        Bex[l] = exprimfact[i];
  }

  /* x = g_W Wex + g_B Bex - [xar]
   *   = g_W A - [xar] + [C_B]Bex  since g_W B + g_B = [C_B] */
  A = gsub(small_to_col(Wex), gmul_mati_smallvec(B,Bex));
  Q = gmul(U, A);
  for (i=1; i<=c; i++)
    Q[i] = (long)truedvmdii((GEN)Q[i], (GEN)cyc[i], (GEN*)(ex+i));
  if ((flag & nf_GEN_IF_PRINCIPAL))
    { if (!gcmp0(ex)) return gzero; }
  else if (!(flag & (nf_GEN|nf_GENMAT)))
    return gcopy(ex);

  /* compute arch component of the missing principal ideal */
  if (old_format)
  {
    GEN Garch, V = (GEN)clg2[2];
    Bex = small_to_col(Bex);
    p1 = c? concatsp(gmul(V,Q), Bex): Bex;
    col = act_arch(p1, WB_C);
    if (c)
    {
      Garch = get_Garch(nf,gen,clg2,prec);
      col = gadd(col, act_arch(ex, Garch));
    }
  }
  else
  { /* g A = G Ur A + [ga]A, Ur A = D Q + R as above (R = ex)
           = G R + [GD]Q + [ga]A */
    GEN ga = (GEN)clg2[2], GD = (GEN)clg2[3];
    if (lB) col = act_arch(Bex, WB_C + lW); else col = zerovec(1); /* nf=Q ! */
    if (lW) col = gadd(col, act_arch(A, ga));
    if (c)  col = gadd(col, act_arch(Q, GD));
  }
  if (xar) col = gadd(col, famat_to_arch(nf, xar, prec));

  /* find coords on Zk; Q = N (x / \prod gj^ej) = N(alpha), denom(alpha) | d */
  Q = gdiv(dethnf_i(x), get_norm_fact(gen, ex, &d));
  col = isprincipalarch(bnf, col, Q, gun, d, &e);
  if (col && !fact_ok(nf,x, col,gen,ex)) col = NULL;
  if (!col && !gcmp0(ex))
  {
    p1 = isprincipalfact(bnf, gen, gneg(ex), x, flag);
    if (typ(p1) != t_VEC) return p1;
    col = (GEN)p1[2];
  }
  if (!col)
  {
    *ptprec = prec + (e >> TWOPOTBITS_IN_LONG) + (MEDDEFAULTPREC-2);
    if (flag & nf_FORCE)
    {
      if (DEBUGLEVEL) err(warner,"precision too low for generators, e = %ld",e);
      return NULL;
    }
    err(warner,"precision too low for generators, not given");
  }
  y = cgetg(3,t_VEC);
  if (xc && col) col = gmul(xc, col);
  if (!col) col = cgetg(1, t_COL);
  if (flag & nf_GEN_IF_PRINCIPAL) return col;
  y[1] = (long)ex;
  y[2] = (long)col; return y;
}

static GEN
triv_gen(GEN nf, GEN x, long c, long flag)
{
  GEN y;
  if (flag & nf_GEN_IF_PRINCIPAL) return _algtobasis_cp(nf,x);
  if (!(flag & (nf_GEN|nf_GENMAT))) return zerocol(c);
  y = cgetg(3,t_VEC);
  y[1] = (long)zerocol(c);
  y[2] = (long)_algtobasis_cp(nf,x); return y;
}

GEN
isprincipalall(GEN bnf,GEN x,long flag)
{
  long c, pr, tx = typ(x);
  pari_sp av = avma;
  GEN nf;

  bnf = checkbnf(bnf); nf = (GEN)bnf[7];
  if (tx == t_POLMOD)
  {
    if (!gegal((GEN)x[1],(GEN)nf[1]))
      err(talker,"not the same number field in isprincipal");
    x = (GEN)x[2]; tx = t_POL;
  }
  if (tx == t_POL || tx == t_COL || tx == t_INT || tx == t_FRAC)
  {
    if (gcmp0(x)) err(talker,"zero ideal in isprincipal");
    return triv_gen(nf, x, lg(mael3(bnf,8,1,2))-1, flag);
  }
  x = idealhermite(nf,x);
  if (lg(x)==1) err(talker,"zero ideal in isprincipal");
  if (degpol(nf[1]) == 1)
    return gerepileupto(av, triv_gen(nf, gcoeff(x,1,1), 0, flag));

  pr = prec_arch(bnf); /* precision of unit matrix */
  c = getrand();
  for (;;)
  {
    pari_sp av1 = avma;
    GEN y = _isprincipal(bnf,x,&pr,flag);
    if (y) return gerepilecopy(av, y);

    if (DEBUGLEVEL) err(warnprec,"isprincipal",pr);
    avma = av1; bnf = bnfnewprec(bnf,pr); (void)setrand(c);
  }
}

static GEN
add_principal_part(GEN nf, GEN u, GEN v, long flag)
{
  if (flag & nf_GENMAT)
    return (isnfscalar(u) && gcmp1((GEN)u[1]))? v: arch_mul(v,u);
  else
    return element_mul(nf, v, u);
}

/* isprincipal for C * \prod P[i]^e[i] (C omitted if NULL) */
GEN
isprincipalfact(GEN bnf,GEN P, GEN e, GEN C, long flag)
{
  long l = lg(e), i, prec, c;
  pari_sp av = avma;
  GEN id,id2, nf = checknf(bnf), z = NULL; /* gcc -Wall */
  int gen = flag & (nf_GEN|nf_GENMAT|nf_GEN_IF_PRINCIPAL);

  prec = prec_arch(bnf);
  if (gen)
  {
    z = cgetg(3,t_VEC);
    z[2] = (flag & nf_GENMAT)? lgetg(1, t_MAT): lmodulcp(gun,(GEN)nf[1]);
  }
  id = C;
  for (i=1; i<l; i++) /* compute prod P[i]^e[i] */
    if (signe(e[i]))
    {
      if (gen) z[1] = P[i]; else z = (GEN)P[i];
      id2 = idealpowred(bnf,z, (GEN)e[i],prec);
      id = id? idealmulred(nf,id,id2,prec): id2;
    }
  if (id == C) /* e = 0 */
  {
    if (!C) return isprincipalall(bnf, gun, flag);
    C = idealhermite(nf,C); id = z;
    if (gen) id[1] = (long)C; else id = C;
  }
  c = getrand();
  for (;;)
  {
    pari_sp av1 = avma;
    GEN y = _isprincipal(bnf, gen? (GEN)id[1]: id,&prec,flag);
    if (y)
    {
      if (flag & nf_GEN_IF_PRINCIPAL)
      {
        if (typ(y) == t_INT) { avma = av; return NULL; }
        y = add_principal_part(nf, y, (GEN)id[2], flag);
      }
      else
      {
        GEN u = (GEN)y[2];
        if (!gen || typ(y) != t_VEC) return gerepileupto(av,y);
        y[2] = (long)add_principal_part(nf, u, (GEN)id[2], flag);
      }
      return gerepilecopy(av, y);
    }

    if (flag & nf_GIVEPREC)
    {
      if (DEBUGLEVEL)
        err(warner,"insufficient precision for generators, not given");
      avma = av; return stoi(prec);
    }
    if (DEBUGLEVEL) err(warnprec,"isprincipal",prec);
    avma = av1; bnf = bnfnewprec(bnf,prec); (void)setrand(c);
  }
}

GEN
isprincipal(GEN bnf,GEN x)
{
  return isprincipalall(bnf,x,0);
}

GEN
isprincipalgen(GEN bnf,GEN x)
{
  return isprincipalall(bnf,x,nf_GEN);
}

GEN
isprincipalforce(GEN bnf,GEN x)
{
  return isprincipalall(bnf,x,nf_FORCE);
}

GEN
isprincipalgenforce(GEN bnf,GEN x)
{
  return isprincipalall(bnf,x,nf_GEN | nf_FORCE);
}

static GEN
rational_unit(GEN x, long n, long RU)
{
  GEN y;
  if (!gcmp1(x) && !gcmp_1(x)) return cgetg(1,t_COL);
  y = zerocol(RU);
  y[RU] = (long)gmodulss((gsigne(x)>0)? 0: n>>1, n);
  return y;
}

/* if x a famat, assume it is an algebraic integer (very costly to check) */
GEN
isunit(GEN bnf,GEN x)
{
  long tx = typ(x), i, R1, RU, n, prec;
  pari_sp av = avma;
  GEN p1, v, rlog, logunit, ex, nf, z, pi2_sur_w, gn, emb;

  bnf = checkbnf(bnf); nf=(GEN)bnf[7];
  logunit = (GEN)bnf[3]; RU = lg(logunit);
  p1 = gmael(bnf,8,4); /* roots of 1 */
  gn = (GEN)p1[1]; n = itos(gn);
  z  = algtobasis(nf, (GEN)p1[2]);
  switch(tx)
  {
    case t_INT: case t_FRAC: case t_FRACN:
      return rational_unit(x, n, RU);

    case t_MAT: /* famat */
      if (lg(x) != 3 || lg(x[1]) != lg(x[2]))
        err(talker, "not a factorization matrix in isunit");
      break;

    case t_COL:
      if (degpol(nf[1]) != lg(x)-1)
        err(talker,"not an algebraic number in isunit");
      break;

    default: x = algtobasis(nf, x);
      break;
  }
  /* assume a famat is integral */
  if (tx != t_MAT && !gcmp1(denom(x))) { avma = av; return cgetg(1,t_COL); }
  if (isnfscalar(x)) return gerepileupto(av, rational_unit((GEN)x[1],n,RU));

  R1 = nf_get_r1(nf); v = cgetg(RU+1,t_COL);
  for (i=1; i<=R1; i++) v[i] = un;
  for (   ; i<=RU; i++) v[i] = deux;
  logunit = concatsp(logunit, v);
  /* ex = fundamental units exponents */
  rlog = greal(logunit);
  prec = nfgetprec(nf);
  for (i=1;;)
  {
    GEN logN, rx = get_arch_real(nf,x,&emb, MEDDEFAULTPREC);
    long e;
    if (rx)
    {
      logN = sum(rx, 1, RU); /* log(Nx), should be ~ 0 */
      if (gexpo(logN) > -20)
      {
        long p = 2 + max(1, (nfgetprec(nf)-2) / 2);
        if (typ(logN) != t_REAL || gprecision(rx) > p)
          { avma = av; return cgetg(1,t_COL); } /* not a precision problem */
        rx = NULL;
      }
    }
    if (rx)
    {
      ex = grndtoi(gauss(rlog, rx), &e);
      if (gcmp0((GEN)ex[RU]) && e < -4) break;
    }
    if (i == 1)
      prec = MEDDEFAULTPREC + (gexpo(x) >> TWOPOTBITS_IN_LONG);
    else
    {
      if (i > 4) err(precer,"isunit");
      prec = (prec-1)<<1;
    }
    i++;
    if (DEBUGLEVEL) err(warnprec,"isunit",prec);
    nf = nfnewprec(nf, prec);
  }

  setlg(ex, RU);
  p1 = row_i(logunit,1, 1,RU-1);
  p1 = gneg(gimag(gmul(p1,ex))); if (!R1) p1 = gmul2n(p1, -1);
  p1 = gadd(garg((GEN)emb[1],prec), p1);
  /* p1 = arg(the missing root of 1) */

  pi2_sur_w = divrs(mppi(prec), n>>1); /* 2pi / n */
  p1 = ground(gdiv(p1, pi2_sur_w));
  if (n > 2)
  {
    GEN ro = gmul(row(gmael(nf,5,1), 1), z);
    GEN p2 = ground(gdiv(garg(ro, prec), pi2_sur_w));
    p1 = mulii(p1,  mpinvmod(p2, gn));
  }

  ex[RU] = lmodulcp(p1, gn);
  setlg(ex, RU+1); return gerepilecopy(av, ex);
}

GEN
signunits(GEN bnf)
{
  long i, j, R1, RU;
  GEN matunit, y, nf, mun, pi = mppi(MEDDEFAULTPREC);

  bnf = checkbnf(bnf); nf = (GEN)bnf[7];
  matunit = (GEN)bnf[3];
  RU = lg(matunit);
  R1 = nf_get_r1(nf);
  y = cgetg(RU,t_MAT);
  mun = negi(gun);
  for (j=1; j<RU; j++)
  {
    GEN c = cgetg(R1+1,t_COL);
    pari_sp av = avma;
    y[j] = (long)c;
    for (i=1; i<=R1; i++)
    {
      GEN p1 = ground( gdiv(gimag(gcoeff(matunit,i,j)), pi) );
      c[i] = mpodd(p1)? (long)mun: un;
    }
    avma = av;
  }
  return y;
}

/* LLL-reduce ideal and return Cholesky for T2 | ideal */
static GEN
red_ideal(GEN *ideal,GEN Gvec,GEN prvec)
{
  long i;
  for (i=1; i<lg(Gvec); i++)
  {
    GEN p1,u, G = (GEN)Gvec[i];
    long prec = prvec[i];

    p1 = gmul(G, *ideal);
    u = lllintern(p1,100,1,prec);
    if (u)
    {
      p1 = gmul(p1, u);
      p1 = sqred1_from_QR(p1, prec);
      if (p1) { *ideal = gmul(*ideal,u); return p1; }
    }
    if (DEBUGLEVEL) err(warner, "prec too low in red_ideal[%ld]: %ld",i,prec);
  }
  return NULL;
}

static GEN
get_log_embed(REL_t *rel, GEN M, long RU, long R1, long prec)
{
  GEN arch, C, t;
  long i;
  if (!rel->m) return zerocol(RU);
  if (!rel->ex) 
    arch = glog( gmul(M, rel->m), prec );
  else
  {
    GEN t, ex = rel->ex, x = NULL;
    long l = lg(ex);
    for (i=1; i<l; i++)
      if (ex[i])
      {
        t = gmael(rel->pow->arc, i, ex[i]);
        x = x? vecmul(x, t): t; /* arch components in MULTIPLICATIVE form */
      }
    arch = gneg( glog(vecmul(x, gmul(M, rel->m)), prec) );
  }
  C = cgetg(RU+1, t_COL);
  for (i=1; i<=R1; i++)
  {
    t = cgetc(prec); C[i] = (long)t;
    gaffect((GEN)arch[i], t);
  }
  for (   ; i<=RU; i++)
  {
    t = cgetc(prec); C[i] = (long)t;
    gaffect(gmul2n((GEN)arch[i], 1), t);
  }
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
      GEN z, t = (GEN)Alg[i]; 
      long lt = lg(t);
      z = cgetg(lt, t_VEC);
      Arc[i] = (long)z; z[1] = M[1];  /* leave t[1] = 1 alone ! */
      for (j = 2; j < lt; j++)
        z[j] = lmul(typ(t[j]) == t_COL? M: (GEN)M[1], (GEN)t[j]);
      for (j = 3; j < lt; j++)
        z[j] = (long)vecmul((GEN)z[j], (GEN)z[j-1]);
    }
    pow->arc = gclone(Arc);
  }
  avma = av;
}

static void
set_fact(REL_t *rel)
{
  long i;
  GEN c = rel->R; rel->nz = primfact[1];
  for (i=1; i<=primfact[0]; i++) c[primfact[i]] = exprimfact[i];
}

static void
unset_fact(GEN c)
{
  long i;
  for (i=1; i<=primfact[0]; i++) c[primfact[i]] = 0;
}

static void
small_norm_for_buchall(RELCACHE_t *cache, FB_t *F, long PRECREG, double LOGD,
                       GEN nf,long nbrelpid,GEN invp,GEN L,double LIMC2)
{
  const int maxtry_DEP  = 20;
  const int maxtry_FACT = 500;
  const double eps = 0.000001;
  double *y,*z,**q,*v, BOUND;
  pari_sp av = avma, av1, av2, limpile;
  long nbsmallnorm, nbfact, j, k, noideal, precbound;
  long N = degpol(nf[1]), R1 = nf_get_r1(nf);
  GEN x, xembed, gx, Mlow, M, G, r, Gvec, prvec;
  REL_t *rel = cache->last;

  if (DEBUGLEVEL)
    fprintferr("\n#### Looking for %ld relations (small norms)\n",
               cache->end - cache->base);
  xembed = gx = NULL; /* gcc -Wall */
  nbsmallnorm = nbfact = 0;
  M = gmael(nf,5,1);
  G = gmael(nf,5,2);
 /* LLL reduction produces v0 in I such that
  *     T2(v0) <= (4/3)^((n-1)/2) NI^(2/n) disc(K)^(1/n)
  * We consider v with T2(v) <= 2 T2(v0)
  * Hence Nv <= ((4/3)^((n-1)/2) * 2 / n)^(n/2) NI sqrt(disc(K)) */
  precbound = 3 + (long)ceil(
    (N/2. * ((N-1)/2.* log(4./3) + log(2./N)) + log(LIMC2) + LOGD / 2)
      / (BITS_IN_LONG * log(2.))); /* enough to compute norms */
  if (precbound < nfgetprec(nf))
    Mlow = gprec_w(M, precbound);
  else
    Mlow = M;

  prvec = cgetg(3,t_VECSMALL); Gvec = cgetg(3,t_VEC);
  prvec[1] = MEDDEFAULTPREC;   Gvec[1] = (long)gprec_w(G,prvec[1]);
  prvec[2] = PRECREG;          Gvec[2] = (long)G;
  minim_alloc(N+1, &q, &x, &y, &z, &v);
  av1 = avma;
  for (noideal=F->KC; noideal; noideal--)
  {
    pari_sp av0 = avma;
    long nbrelideal=0, dependent = 0, try_factor = 0;
    GEN IDEAL, ideal = (GEN)F->LP[noideal];
    REL_t *oldrel = rel;

    if (DEBUGLEVEL>1) fprintferr("\n*** Ideal no %ld: %Z\n", noideal, ideal);
    ideal = prime_to_ideal(nf,ideal);
    IDEAL = lllint_ip(ideal,4); /* should be almost T2-reduced */
    r = red_ideal(&IDEAL,Gvec,prvec);
    if (!r) err(bugparier, "precision too low in small_norm");

    for (k=1; k<=N; k++)
    {
      v[k] = gtodouble(gcoeff(r,k,k));
      for (j=1; j<k; j++) q[j][k] = gtodouble(gcoeff(r,j,k));
      if (DEBUGLEVEL>3) fprintferr("v[%ld]=%.4g ",k,v[k]);
    }

    BOUND = v[2] + v[1] * q[1][2] * q[1][2];
    if (BOUND < v[1]) BOUND = v[1];
    BOUND *= 2; /* at most twice larger than smallest known vector */
    if (DEBUGLEVEL>1)
    {
      if (DEBUGLEVEL>3) fprintferr("\n");
      fprintferr("BOUND = %.4g\n",BOUND); flusherr();
    }
    BOUND *= 1 + eps; av2=avma; limpile = stack_lim(av2,1);
    k = N; y[N] = z[N] = 0; x[N] = (long)sqrt(BOUND/v[N]);
    for(;; x[1]--)
    {
      pari_sp av3 = avma;
      double p;

      for(;;) /* looking for primitive element of small norm */
      { /* cf minim00 */
	if (k>1)
	{
	  long l = k-1;
	  z[l] = 0;
	  for (j=k; j<=N; j++) z[l] += q[l][j]*x[j];
	  p = (double)x[k] + z[k];
	  y[l] = y[k] + p*p*v[k];
	  x[l] = (long) floor(sqrt((BOUND-y[l])/v[l])-z[l]);
          k = l;
	}
	for(;;)
	{
	  p = (double)x[k] + z[k];
	  if (y[k] + p*p*v[k] <= BOUND) break;
	  k++; x[k]--;
	}
	if (k==1) /* element complete */
	{
	  if (y[1]<=eps) goto ENDIDEAL; /* skip all scalars: [*,0...0] */
	  if (ccontent(x)==1) /* primitive */
	  {
            GEN Nx;
            pari_sp av4;
            gx = gmul_mati_smallvec(IDEAL,x);
            if (!isnfscalar(gx))
            {
              xembed = gmul(Mlow, gx); av4 = avma; nbsmallnorm++;
              if (++try_factor > maxtry_FACT) goto ENDIDEAL;
              Nx = ground( norm_by_embed(R1,xembed) );
              setsigne(Nx, 1);
              if (can_factor(F, nf, NULL, gx, Nx)) { avma = av4; break; }
              if (DEBUGLEVEL > 1) { fprintferr("."); flusherr(); }
            }
	    avma = av3;
	  }
	  x[1]--;
	}
      }
      rel++; set_fact(rel);
      /* make sure we get maximal rank first, then allow all relations */
      if (rel - cache->base > 1 && rel - cache->base <= F->KC
                                && ! addcolumntomatrix(rel->R,invp,L))
      { /* Q-dependent from previous ones: forget it */
        unset_fact(rel->R);
        if (DEBUGLEVEL>1) { fprintferr("*"); flusherr(); }
        rel--;
        if (++dependent > maxtry_DEP) break;
        avma = av3; continue;
      }
      rel->m = gclone(gx);
      rel->ex= NULL;
      dependent = 0;

      if (DEBUGLEVEL) { nbfact++; dbg_rel(rel - cache->base, rel->R); }
      if (rel >= cache->end) goto END; /* we have enough */
      if (++nbrelideal == nbrelpid) break;

      if (low_stack(limpile, stack_lim(av2,1)))
      {
	if(DEBUGMEM>1) err(warnmem,"small_norm");
        invp = gerepilecopy(av2, invp);
      }
    }
ENDIDEAL:
    if (rel == oldrel) avma = av0; else invp = gerepilecopy(av1, invp);
    if (DEBUGLEVEL>1) msgtimer("for this ideal");
  }
END:
  cache->last = rel; avma = av;
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
  GEN m, y = lllintern(gmul(G, I), 100,1, 0);
  if (!y) return NULL;

  m = gmul(I,(GEN)y[1]);
  if (isnfscalar(m)) m = gmul(I,(GEN)y[2]);
  if (DEBUGLEVEL>5) fprintferr("\nm = %Z\n",m);
  return m;
}

static void
dbg_newrel(RELCACHE_t *cache, long jideal, long jdir)
{
  fprintferr("\n++++ cglob = %ld: new relation (need %ld)", 
             cache->last - cache->base, cache->end - cache->base);
  wr_rel(cache->last->R);
  if (DEBUGLEVEL>3)
  {
    fprintferr("(jideal=%ld,jdir=%ld)", jideal,jdir);
    msgtimer("for this relation");
  }
  flusherr() ;
}

static void
dbg_cancelrel(long jideal, long jdir, GEN col)
{
  fprintferr("relation cancelled: ");
  if (DEBUGLEVEL>3) fprintferr("(jideal=%ld,jdir=%ld)",jideal,jdir);
  wr_rel(col); flusherr();
}

static void
dbg_outrel(RELCACHE_t *cache)
{
  REL_t *rel; fprintferr("relations = \n");
  for (rel = cache->base + 1; rel <= cache->last; rel++) wr_rel(rel->R);
  flusherr();
}

/* Check if we already have a column mat[i] equal to mat[s]
 * General check for colinearity useless since exceedingly rare */
static int
already_known(RELCACHE_t *cache)
{
  REL_t *r;
  GEN cols = cache->last->R;
  long bs, l = lg(cols);

  bs = 1; while (bs < l && !cols[bs]) bs++;
  if (bs == l) return -1; /* zero relation */

  for (r = cache->last - 1; r > cache->base; r--)
  {
    if (bs == r->nz) /* = index of first non zero elt in cols */
    {
      GEN coll = r->R;
      long b = bs;
      do b++; while (b < l && cols[b] == coll[b]);
      if (b == l) return 1;
    }
  }
  cache->last->nz = bs; return 0;
}

/* I integral ideal in HNF form */
static GEN
remove_content(GEN I)
{
  long N = lg(I)-1;
  if (!gcmp1(gcoeff(I,N,N))) I = Q_primpart(I);
  return I;
}

/* if phase != 1 re-initialize static variables. If <0 return immediately */
static int
random_relation(long phase, RELCACHE_t *cache, long PRECREG,long MAXRELSUP,
                GEN nf,GEN vecG, GEN list_jideal, FB_t *F)
{
  static long jideal, jdir;
  long i, cptlist, cptzer, nbG, lgsub, r1, jlist = 1;
  pari_sp av, av1;
  GEN col, ideal, IDEAL, m, P, ex;

  if (phase != 1) { jideal=jdir=1; if (phase < 0) return 0; }

  r1 = nf_get_r1(nf);
  nbG = lg(vecG)-1;
  lgsub = lg(F->subFB); ex = cgetg(lgsub, t_VECSMALL);
  cptzer = cptlist = 0;
  if (DEBUGLEVEL && list_jideal)
    fprintferr("looking hard for %Z\n",list_jideal);
  P = NULL; /* gcc -Wall */
  for (av = avma;;)
  {
    if (list_jideal && jlist < lg(list_jideal) && jdir <= nbG)
    {
      jideal = list_jideal[jlist++]; cptlist = 0;
    }
    if (!list_jideal || jdir <= nbG)
    {
      avma = av;
      P = prime_to_ideal(nf, (GEN)F->LP[jideal]);
    }
    else
    { if (++cptlist > 300) return 0; }
    ideal = P;
    do {
      for (i=1; i<lgsub; i++)
      { /* reduce mod apparent order */
        ex[i] = random_bits(RANDOM_BITS) % F->pow->ord[i];
        if (ex[i]) ideal = idealmulh(nf,ideal, gmael(F->pow->id2,i,ex[i]));
      }
    }
    while (ideal == P); /* If ex  = 0, try another */
    ideal = remove_content(ideal);
    IDEAL = lllint_ip(ideal, 4);

    if (phase != 1) jdir = 1; else phase = 2;
    for (av1 = avma; jdir <= nbG; jdir++, avma = av1)
    { /* reduce along various directions */
      if (DEBUGLEVEL>2)
        fprintferr("jideal=%ld,jdir=%ld,rand=%ld\n", jideal,jdir,getrand());
      m = pseudomin(IDEAL, (GEN)vecG[jdir]);
      if (!m) err(bugparier, "precision too low in random_relation");
      if (!factorgen(F,nf,ideal,m))
      {
        if (DEBUGLEVEL>1) { fprintferr("."); flusherr(); }
        continue;
      }
      /* can factor ideal, record relation */
      cache->last++; set_fact(cache->last);
      col = cache->last->R; col[jideal]--;
      for (i=1; i<lgsub; i++) col[ F->subFB[i] ] -= ex[i];
      if (already_known(cache))
      { /* forget it */
        if (DEBUGLEVEL>1) dbg_cancelrel(jideal,jdir,col);
        cache->last--; unset_fact(col); col[jideal] = 0;
        for (i=1; i<lgsub; i++) col[ F->subFB[i] ] = 0;

        if (++cptzer > MAXRELSUP)
        {
          if (list_jideal) { cptzer -= 10; break; }
          return 0;
        }
        continue;
      }
      cache->last->m = gclone(m);
      cache->last->ex = gclone(ex);
      cache->last->pow= F->pow;
      if (DEBUGLEVEL) dbg_newrel(cache, jideal, jdir);
      /* Need more, try next P */
      if (cache->last < cache->end) { cptzer = 0; break; }

      /* We have found enough. Return */
      if (phase)
      {
        jdir = 1;
        if (jideal == F->KC) jideal=1; else jideal++;
      }
      if (DEBUGLEVEL>2)
        fprintferr("Upon exit: jideal=%ld,jdir=%ld\n",jideal,jdir);
      avma = av; return 1;
    }
    if (!list_jideal)
    {
      if (jideal == F->KC) jideal=1; else jideal++;
    }
  }
}

/* remark: F->KCZ changes if be_honest() fails */
static int
be_honest(FB_t *F, GEN nf, long PRECLLL)
{
  long ex, i, j, J, k, iz, nbtest, ru, lgsub = lg(F->subFB), KCZ0 = F->KCZ;
  GEN G, M, P, ideal, m, vdir;
  pari_sp av;

  if (F->KCZ2 <= F->KCZ) return 1;
  if (DEBUGLEVEL)
  {
    fprintferr("Be honest for primes from %ld to %ld\n",
               F->FB[ F->KCZ+1 ], F->FB[ F->KCZ2 ]);
    flusherr();
  }
  if (!F->pow) powFBgen(F, nf, CBUCHG+1);
  M = gprec_w(gmael(nf,5,1), PRECLLL);
  G = gprec_w(gmael(nf,5,2), PRECLLL);
  ru = lg(nf[6]);
  vdir = cgetg(ru, t_VECSMALL);
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
      GEN IDEAL, ideal0 = prime_to_ideal(nf,(GEN)P[j]);
      pari_sp av2 = avma;
      for(nbtest=0;;)
      {
	ideal = ideal0;
	for (i=1; i<lgsub; i++)
	{
	  ex = random_bits(RANDOM_BITS);
	  if (ex) ideal = idealmulh(nf,ideal, gmael(F->pow->id2,i,ex));
	}
        ideal = remove_content(ideal);
        IDEAL = lllint_ip(ideal, 4);
        for (i=1; i<ru; i++) vdir[i] = random_bits(RANDOM_BITS);
	for (k=1; k<ru; k++)
	{
          m = pseudomin(IDEAL, computeGtwist(nf, vdir));
          if (m && factorgen(F,nf,ideal,m)) break;
	  for (i=1; i<ru; i++) vdir[i] = 0;
          vdir[k] = 10;
	}
	avma = av2; if (k < ru) break;
        if (++nbtest > 50)
        {
          err(warner,"be_honest() failure on prime %Z\n", P[j]);
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
  F->KCZ = KCZ0;
  avma = av; return 1;
}

int
trunc_error(GEN x)
{
  return typ(x)==t_REAL && signe(x)
                        && (expo(x)>>TWOPOTBITS_IN_LONG) + 3 > lg(x);
}

/* A = complex logarithmic embeddings of units (u_j) found so far */
static GEN
compute_multiple_of_R(GEN A,long RU,long N,GEN *ptlambda)
{
  GEN T,v,mdet,mdet_t,Im_mdet,kR,xreal,lambda;
  long i, zc = lg(A)-1, R1 = 2*RU - N;
  pari_sp av = avma;

  if (DEBUGLEVEL) fprintferr("\n#### Computing regulator multiple\n");
  xreal = greal(A); /* = (log |sigma_i(u_j)|) */
  T = cgetg(RU+1,t_COL);
  for (i=1; i<=R1; i++) T[i] = un;
  for (   ; i<=RU; i++) T[i] = deux;
  mdet = concatsp(xreal,T); /* det(Span(mdet)) = N * R */

  i = gprecision(mdet); /* truncate to avoid "near dependent" vectors */
  mdet_t = (i <= 4)? mdet: gprec_w(mdet,i-1);
  v = (GEN)sindexrank(mdet_t)[2]; /* list of independent column indices */
  /* check we have full rank for units */
  if (lg(v) != RU+1) { avma=av; return NULL; }

  Im_mdet = vecextract_p(mdet,v);
  /* integral multiple of R: the cols we picked form a Q-basis, they have an
   * index in the full lattice. Last column is T */
  kR = gdivgs(det2(Im_mdet), N);
  /* R > 0.2 uniformly */
  if (gexpo(kR) < -3) { avma=av; return NULL; }

  kR = mpabs(kR);
  lambda = gauss(Im_mdet,xreal); /* approximate rational entries */
  for (i=1; i<=zc; i++) setlg(lambda[i], RU);
  gerepileall(av,2, &lambda, &kR);
  *ptlambda = lambda; return kR;
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
 * In fact z is a very rough approximation and we only expect 0.8 < Rz < 1.3
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
  D = gmul2n(gmul(*ptkR,z), 1); /* bound for denom(lambda) */
  lambda = bestappr_noer(lambda,D);
  if (!lambda)
  {
    if (DEBUGLEVEL) fprintferr("truncation error in bestappr\n");
    return fupb_PRECI;
  }
  den = Q_denom(lambda);
  if (gcmp(den,D) > 0)
  {
    if (DEBUGLEVEL) fprintferr("D = %Z\nden = %Z\n",D,den);
    return fupb_PRECI;
  }
  L = Q_muli_to_int(lambda, den);
  H = hnfall_i(L, NULL, 1); r = lg(H)-1;

  /* tentative regulator */
  R = mpabs( gmul(*ptkR, gdiv(dethnf_i(H), gpowgs(den, r))) );
  c = gtodouble(gmul(R,z)); /* should be n (= 1 if we are done) */
  if (DEBUGLEVEL)
  {
    msgtimer("bestappr/regulator");
    fprintferr("\n ***** check = %f\n",c);
  }
  if (c < 0.8 || c > 1.3) { avma = av; return fupb_RELAT; }
  *ptkR = R; *ptL = L; return fupb_NONE;
}

/* find the smallest (wrt norm) among I, I^-1 and red(I^-1) */
static GEN
inverse_if_smaller(GEN nf, GEN I, long prec)
{
  GEN J, d, dmin, I1;

  J = (GEN)I[1];
  dmin = dethnf_i(J); I1 = idealinv(nf,I);
  J = (GEN)I1[1]; J = gmul(J,denom(J)); I1[1] = (long)J;
  d = dethnf_i(J); if (cmpii(d,dmin) < 0) {I=I1; dmin=d;}
  /* try reducing (often _increases_ the norm) */
  I1 = ideallllred(nf,I1,NULL,prec);
  J = (GEN)I1[1];
  d = dethnf_i(J); if (cmpii(d,dmin) < 0) I=I1;
  return I;
}

/* in place */
static void
neg_row(GEN U, long i)
{
  GEN c = U + lg(U)-1;
  for (; c>U; c--) coeff(c,i,0) = lneg(gcoeff(c,i,0));
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
  D = smithall(W,&U,&V); /* UWV = D, D diagonal, G = g Ui (G=new gens, g=old) */
  Ui = ginv(U);
  lo0 = lo = lg(D);
 /* we could set lo = lg(cyc) and truncate all matrices below
  *   setlg_col(D && U && Y, lo) + setlg(D && V && X && Ui, lo)
  * but it's not worth the complication:
  * 1) gain is negligible (avoid computing z^0 if lo < lo0)
  * 2) when computing ga, the products XU and VY use the original matrices
  */
  Ur  = reducemodHNF(U, D, &Y);
  Uir = reducemodHNF(Ui,W, &X);
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
    z[1]=Vbase[1]; I = idealpowred(nf0,z,p1,prec);
    for (i=2; i<lo0; i++)
    {
      p1 = gcoeff(Uir,i,j);
      if (signe(p1))
      {
	z[1]=Vbase[i]; J = idealpowred(nf0,z,p1,prec);
	I = idealmulh(nf0,I,J);
	I = ideallllred(nf0,I,NULL,prec);
      }
    }
    J = inverse_if_smaller(nf0, I, prec);
    if (J != I)
    { /* update wrt P */
      neg_row(Y ,j); V[j] = lneg((GEN)V[j]);
      neg_row(Ur,j); X[j] = lneg((GEN)X[j]);
    }
    G[j] = (long)J[1]; /* generator, order cyc[j] */
    Ga[j]= lneg(famat_to_arch(nf, (GEN)J[2], prec));
  }
  /* at this point Y = PY, Ur = PUr, V = VP, X = XP */

  /* G D =: [GD] = g (UiP + W XP) D + [Ga]D = g W (VP + XP D) + [Ga]D
   * NB: DP = PD and Ui D = W V. gW is given by (first lo0-1 cols of) C
   */
  GD = gadd(act_arch(gadd(V, gmul(X,D)), C),
            act_arch(D, Ga));
  /* -[ga] = [GD]PY + G PU - g = [GD]PY + [Ga] PU + gW XP PU
                               = gW (XP PUr + VP PY) + [Ga]PUr */
  ga = gadd(act_arch(gadd(gmul(X,Ur), gmul(V,Y)), C),
            act_arch(Ur, Ga));
  ga = gneg(ga);
  /* TODO: could (LLL)reduce ga and GD mod units ? */

  cyc = cgetg(lo,t_VEC); /* elementary divisors */
  for (j=1; j<lo; j++)
  {
    cyc[j] = coeff(D,j,j);
    if (gcmp1((GEN)cyc[j]))
    { /* strip useless components */
      lo = j; setlg(cyc,lo); setlg_col(Ur,lo);
      setlg(G,lo); setlg(Ga,lo); setlg(GD,lo); break;
    }
  }
  z = cgetg(4,t_VEC); *ptclg1 = z;
  z[1]=(long)dethnf_i(W);
  z[2]=(long)cyc;
  z[3]=(long)G;
  z = cgetg(4,t_VEC); *ptclg2 = z;
  z[1]=(long)Ur;
  z[2]=(long)ga;
  z[3]=(long)GD;
  if (DEBUGLEVEL) msgtimer("classgroup generators");
}

static void
shift_embed(GEN G, GEN Gtw, long a, long r1)
{
  long j, k, l = lg(G);
  if (a <= r1)
    for (j=1; j<l; j++) coeff(G,a,j) = coeff(Gtw,a,j);
  else
  {
    k = (a<<1) - r1;
    for (j=1; j<l; j++)
    {
      coeff(G,k-1,j) = coeff(Gtw,k-1,j);
      coeff(G,k  ,j) = coeff(Gtw,k,  j);
    }
  }
}

/* G where embeddings a and b are multiplied by 2^10 */
static GEN
shift_G(GEN G, GEN Gtw, long a, long b, long r1)
{
  GEN g = dummycopy(G);
  shift_embed(g,Gtw,a,r1);
  shift_embed(g,Gtw,b,r1); return g;
}

static GEN
compute_vecG(GEN nf,long prec)
{
  GEN vecG, Gtw, M = gmael(nf,5,1), G = gmael(nf,5,2);
  long r1, i, j, ind, n = min(lg(M[1])-1, 9);

  r1 = nf_get_r1(nf);
  vecG=cgetg(1 + n*(n+1)/2,t_VEC);
  if (nfgetprec(nf) > prec)
  {
    M = gprec_w(M,prec);
    G = gprec_w(G,prec);
  }
  Gtw = gmul2n(G, 10);
  for (ind=j=1; j<=n; j++)
    for (i=1; i<=j; i++) vecG[ind++] = (long)shift_G(G,Gtw,i,j,r1);
  if (DEBUGLEVEL) msgtimer("weighted G matrices");
  return vecG;
}

/* cf. relationrank()
 *
 * If V depends linearly from the columns of the matrix, return 0.
 * Otherwise, update INVP and L and return 1. No GC.
 */
int
addcolumntomatrix(GEN V, GEN invp, GEN L)
{
  GEN a = gmul_mat_smallvec(invp,V);
  long i,j,k, n = lg(invp);

  if (DEBUGLEVEL>6)
  {
    fprintferr("adding vector = %Z\n",V);
    fprintferr("vector in new basis = %Z\n",a);
    fprintferr("list = %Z\n",L);
    fprintferr("base change matrix =\n"); outerr(invp);
  }
  k = 1; while (k<n && (L[k] || gcmp0((GEN)a[k]))) k++;
  if (k == n) return 0;
  L[k] = 1;
  for (i=k+1; i<n; i++) a[i] = ldiv(gneg_i((GEN)a[i]),(GEN)a[k]);
  for (j=1; j<=k; j++)
  {
    GEN c = (GEN)invp[j], ck = (GEN)c[k];
    if (gcmp0(ck)) continue;
    c[k] = ldiv(ck, (GEN)a[k]);
    if (j==k)
      for (i=k+1; i<n; i++)
	c[i] = lmul((GEN)a[i], ck);
    else
      for (i=k+1; i<n; i++)
	c[i] = ladd((GEN)c[i], gmul((GEN)a[i], ck));
  }
  return 1;
}

/* compute the rank of A in M_n,r(Z) (C long), where rank(A) = r <= n.
 * Starting from the identity (canonical basis of Q^n), we obtain a base
 * change matrix P by taking the independent columns of A and vectors from
 * the canonical basis. Update invp = 1/P, and L in {0,1}^n, with L[i] = 0
 * if P[i] = e_i, and 1 if P[i] = A_i (i-th column of A)
 */
static GEN
relationrank(RELCACHE_t *cache, GEN L)
{
  pari_sp av = avma, lim = stack_lim(av, 1);
  GEN invp = idmat(lg(L) - 1);
  REL_t *rel = cache->base + 1;

  for (; rel <= cache->last; rel++)
  {
    (void)addcolumntomatrix(rel->R, invp, L);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"relationrank");
      invp = gerepilecopy(av, invp);
    }
  }
  if (avma != av) invp = gerepilecopy(av, invp);
  return invp;
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
    t = (GEN)pfc[i]; p = itos(t) / n;
    if (p > pmax) pmax = p;
  }
  L = cgetg(pmax+1, t_VEC);
  for (p=1; p<=pmax; p++) L[p] = 0;
  for (i=1; i<l; i++)
  {
    t = (GEN)pfc[i]; p = itos(t) / n;
    if (!L[p]) L[p] = (long)primedec(nf, stoi(p));
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
  long p = itos((GEN)pr[1]);
  return utoi( N*p + pr_index((GEN)L[p], pr)-1 );
}

static GEN
codeprimes(GEN Vbase, long N)
{
  GEN v, L = get_pr_lists(Vbase, N, 1);
  long i, l = lg(Vbase);
  v = cgetg(l, t_VEC);
  for (i=1; i<l; i++) v[i] = (long)codeprime(L, N, (GEN)Vbase[i]);
  return v;
}

/* compute principal ideals corresponding to (gen[i]^cyc[i]) */
static GEN
makecycgen(GEN bnf)
{
  GEN cyc,gen,h,nf,y,GD,D;
  long e,i,l;

  if (DEBUGLEVEL) err(warner,"completing bnf (building cycgen)");
  nf = checknf(bnf);
  cyc = gmael3(bnf,8,1,2); D = diagonal(cyc);
  gen = gmael3(bnf,8,1,3); GD = gmael(bnf,9,3);
  l = lg(gen); h = cgetg(l, t_VEC);
  for (i=1; i<l; i++)
  {
    if (cmpis((GEN)cyc[i], 16) < 0)
    {
      GEN N = dethnf_i((GEN)gen[i]);
      y = isprincipalarch(bnf,(GEN)GD[i], N, (GEN)cyc[i], gun, &e);
      if (y && !fact_ok(nf,y,NULL,gen,(GEN)D[i])) y = NULL;
      if (y) { h[i] = (long)to_famat_all(y,gun); continue; }
    }
    y = isprincipalfact(bnf, gen, (GEN)D[i], NULL, nf_GENMAT|nf_FORCE);
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

  if (DEBUGLEVEL) err(warner,"completing bnf (building matal)");
  W   = (GEN)bnf[1];
  B   = (GEN)bnf[2];
  WB_C= (GEN)bnf[4];
  nf  = (GEN)bnf[7];
  lW=lg(W)-1; lma=lW+lg(B);
  pFB = get_Vbase(bnf);
  ma = cgetg(lma,t_MAT);

  prec = prec_arch(bnf);
  for (j=1; j<lma; j++)
  {
    long c = getrand(), e;
    GEN ex = (j<=lW)? (GEN)W[j]: (GEN)B[j-lW];
    GEN C = (j<=lW)? NULL: (GEN)pFB[j];
    GEN dx, Nx = get_norm_fact_primes(pFB, ex, C, &dx);
    GEN y = isprincipalarch(bnf,(GEN)WB_C[j], Nx,gun, dx, &e);
    if (y && !fact_ok(nf,y,C,pFB,ex)) y = NULL;
    if (y)
    {
      if (DEBUGLEVEL>1) fprintferr("*%ld ",j);
      ma[j] = (long)y; continue;
    }

    if (!y) y = isprincipalfact(bnf,pFB,ex,C, nf_GENMAT|nf_FORCE|nf_GIVEPREC);
    if (typ(y) != t_INT)
    {
      if (DEBUGLEVEL>1) fprintferr("%ld ",j);
      ma[j] = y[2]; continue;
    }

    prec = itos(y); j--;
    if (DEBUGLEVEL) err(warnprec,"makematal",prec);
    nf = nfnewprec(nf,prec);
    bnf = bnfinit0(nf,1,NULL,prec); (void)setrand(c);
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

GEN
smallbuchinit(GEN pol,GEN gcbach,GEN gcbach2,GEN gRELSUP,GEN gborne,long nbrelpid,long minsFB,long prec)
{
  GEN y, bnf, nf, res, p1;
  pari_sp av = avma;

  if (typ(pol)==t_VEC) bnf = checkbnf(pol);
  else
  {
    const long fl = nf_INIT | nf_UNITS | nf_FORCE;
    bnf = buchall(pol,gcbach,gcbach2,gRELSUP,gborne,nbrelpid,minsFB,fl,prec);
    bnf = checkbnf_discard(bnf);
  }
  nf  = (GEN)bnf[7];
  res = (GEN)bnf[8];

  y = cgetg(13,t_VEC);
  y[1] = nf[1];
  y[2] = mael(nf,2,1);
  y[3] = nf[3];
  y[4] = nf[7];
  y[5] = nf[6];
  y[6] = mael(nf,5,5);
  y[7] = bnf[1];
  y[8] = bnf[2];
  y[9] = (long)codeprimes((GEN)bnf[5], degpol(nf[1]));

  p1 = cgetg(3, t_VEC);
  p1[1] = mael(res,4,1);
  p1[2] = (long)algtobasis(bnf,gmael(res,4,2));
  y[10] = (long)p1;

  y[11] = (long)algtobasis(bnf, (GEN)res[5]);
  (void)check_and_build_matal(bnf);
  y[12] = bnf[10]; return gerepilecopy(av, y);
}

static GEN
get_regulator(GEN mun)
{
  pari_sp av = avma;
  GEN A;

  if (lg(mun)==1) return gun;
  A = gtrans( greal(mun) );
  setlg(A, lg(A)-1);
  return gerepileupto(av, gabs(det(A), 0));
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
    GEN c = get_arch(nf, (GEN)x[k], prec);
    if (!units) c = cleanarch(c, N, prec);
    M[k] = (long)c;
  }
  return M;
}

static void
my_class_group_gen(GEN bnf, long prec, GEN nf0, GEN *ptcl, GEN *ptcl2)
{
  GEN W=(GEN)bnf[1], C=(GEN)bnf[4], nf=(GEN)bnf[7];
  class_group_gen(nf,W,C,get_Vbase(bnf),prec,nf0, ptcl,ptcl2);
}

GEN
bnfnewprec(GEN bnf, long prec)
{
  GEN nf0 = (GEN)bnf[7], nf, res, funits, mun, matal, clgp, clgp2, y;
  pari_sp av = avma;
  long r1, r2, prec1;

  bnf = checkbnf(bnf);
  if (prec <= 0) return nfnewprec(checknf(bnf),prec);
  nf = (GEN)bnf[7];
  nf_get_sign(nf, &r1, &r2);
  funits = algtobasis(nf, check_units(bnf,"bnfnewprec"));

  prec1 = prec;
  if (r2 > 1 || r1 != 0)
    prec += 1 + (gexpo(funits) >> TWOPOTBITS_IN_LONG);
  nf = nfnewprec(nf0,prec);
  mun = get_archclean(nf,funits,prec,1);
  if (prec != prec1) { mun = gprec_w(mun,prec1); prec = prec1; }
  matal = check_and_build_matal(bnf);

  y = dummycopy(bnf);
  y[3] = (long)mun;
  y[4] = (long)get_archclean(nf,matal,prec,0);
  y[7] = (long)nf;
  my_class_group_gen(y,prec,nf0, &clgp,&clgp2);
  res = dummycopy((GEN)bnf[8]);
  res[1] = (long)clgp;
  res[2] = (long)get_regulator(mun);
  y[8] = (long)res;
  y[9] = (long)clgp2; return gerepilecopy(av, y);
}

GEN
bnrnewprec(GEN bnr, long prec)
{
  GEN y = cgetg(7,t_VEC);
  long i;
  checkbnr(bnr);
  y[1] = (long)bnfnewprec((GEN)bnr[1],prec);
  for (i=2; i<7; i++) y[i]=lcopy((GEN)bnr[i]);
  return y;
}

static void
nfbasic_from_sbnf(GEN sbnf, nfbasic_t *T)
{
  T->x    = (GEN)sbnf[1];
  T->dK   = (GEN)sbnf[3];
  T->bas  = (GEN)sbnf[4];
  T->index= get_nfindex(T->bas);
  T->r1   = itos((GEN)sbnf[2]);
  T->dx   = NULL;
  T->lead = NULL;
  T->basden = NULL;
}

static GEN
get_clfu(GEN clgp, GEN reg, GEN zu, GEN fu, long fl)
{
  long l = (fl & nf_UNITS)? 6
                          : (fl & nf_ROOT1)? 5: 4;
  GEN z = cgetg(6, t_VEC);
  z[1] = (long)clgp;
  z[2] = (long)reg;
  z[3] = un; /* DUMMY */
  z[4] = (long)zu;
  z[5] = (long)fu; setlg(z, l); return z;
}

static GEN
buchall_end(GEN nf,GEN CHANGE,long fl,GEN res, GEN clg2, GEN W, GEN B,
            GEN A, GEN C, GEN Vbase)
{
  GEN p1, z;
  if (! (fl & nf_INIT))
  {
    GEN x = cgetg(5, t_VEC);
    x[1]=nf[1];
    x[2]=nf[2]; p1=cgetg(3,t_VEC); p1[1]=nf[3]; p1[2]=nf[4];
    x[3]=(long)p1;
    x[4]=nf[7];
    z=cgetg(2,t_MAT); z[1]=(long)concatsp(x, res); return z;
  }
  z=cgetg(11,t_VEC);
  z[1]=(long)W;
  z[2]=(long)B;
  z[3]=(long)A;
  z[4]=(long)C;
  z[5]=(long)Vbase;
  z[6]=zero;
  z[7]=(long)nf;
  z[8]=(long)res;
  z[9]=(long)clg2;
  z[10]=zero; /* dummy: we MUST have lg(bnf) != lg(nf) */
  if (CHANGE) { p1=cgetg(3,t_VEC); p1[1]=(long)z; p1[2]=(long)CHANGE; z=p1; }
  return z;
}

GEN
bnfmake(GEN sbnf, long prec)
{
  long j, k, l, n;
  pari_sp av = avma;
  GEN p1, bas, ro, nf, A, fu, L;
  GEN pfc, C, clgp, clgp2, res, y, W, zu, matal, Vbase;
  nfbasic_t T;

  if (typ(sbnf) != t_VEC || lg(sbnf) != 13) err(typeer,"bnfmake");
  if (prec < DEFAULTPREC) prec = DEFAULTPREC;

  nfbasic_from_sbnf(sbnf, &T);
  ro = (GEN)sbnf[5];
  if (prec > gprecision(ro)) ro = get_roots(T.x,T.r1,prec);
  nf = nfbasic_to_nf(&T, ro, prec);
  bas = (GEN)nf[7];

  p1 = (GEN)sbnf[11]; l = lg(p1); fu = cgetg(l, t_VEC);
  for (k=1; k < l; k++) fu[k] = lmul(bas, (GEN)p1[k]);
  A = get_archclean(nf,fu,prec,1);

  prec = gprecision(ro);
  matal = check_and_build_matal(sbnf);
  C = get_archclean(nf,matal,prec,0);

  pfc = (GEN)sbnf[9];
  l = lg(pfc);
  Vbase = cgetg(l,t_COL);
  L = decode_pr_lists(nf, pfc);
  n = degpol(nf[1]);
  for (j=1; j<l; j++) Vbase[j] = (long)decodeprime((GEN)pfc[j], L, n);
  W = (GEN)sbnf[7];
  class_group_gen(nf,W,C,Vbase,prec,NULL, &clgp,&clgp2);

  p1 = cgetg(3,t_VEC); zu = (GEN)sbnf[10];
  p1[1] = zu[1];
  p1[2] = lmul(bas,(GEN)zu[2]); zu = p1;

  res = get_clfu(clgp, get_regulator(A), zu, fu, nf_UNITS);
  y = buchall_end(nf,NULL,nf_INIT,res,clgp2,W,(GEN)sbnf[8],A,C,Vbase);
  y[10] = sbnf[12]; return gerepilecopy(av,y);
}

static GEN
classgroupall(GEN P, GEN data, long flag, long prec)
{
  long court[3],doubl[4];
  long fl, lx, minsFB=3, nbrelpid=4;
  pari_sp av=avma;
  GEN bach=doubl,bach2=doubl,RELSUP=court,borne=gun;

  if (!data) lx=1;
  else
  {
    lx = lg(data);
    if (typ(data)!=t_VEC || lx > 7)
      err(talker,"incorrect parameters in classgroup");
  }
  court[0]=evaltyp(t_INT) | evallg(3); affsi(5,court);
  doubl[0]=evaltyp(t_REAL)| evallg(4); affrr(dbltor(0.3),doubl);
  avma=av;
  switch(lx)
  {
    case 7: minsFB  = itos((GEN)data[6]);
    case 6: nbrelpid= itos((GEN)data[5]);
    case 5: borne  = (GEN)data[4];
    case 4: RELSUP = (GEN)data[3];
    case 3: bach2 = (GEN)data[2];
    case 2: bach  = (GEN)data[1];
  }
  switch(flag)
  {
    case 0: fl = nf_INIT | nf_UNITS; break;
    case 1: fl = nf_INIT | nf_UNITS | nf_FORCE; break;
    case 2: fl = nf_INIT | nf_ROOT1; break;
    case 3: return smallbuchinit(P,bach,bach2,RELSUP,borne,nbrelpid,minsFB,prec);
    case 4: fl = nf_UNITS; break;
    case 5: fl = nf_UNITS | nf_FORCE; break;
    case 6: fl = 0; break;
    default: err(flagerr,"classgroupall");
      return NULL; /* not reached */
  }
  return buchall(P,bach,bach2,RELSUP,borne,nbrelpid,minsFB,fl,prec);
}

GEN
bnfclassunit0(GEN P, long flag, GEN data, long prec)
{
  if (typ(P)==t_INT) return quadclassunit0(P,0,data,prec);
  if (flag < 0 || flag > 2) err(flagerr,"bnfclassunit");
  return classgroupall(P,data,flag+4,prec);
}

GEN
bnfinit0(GEN P, long flag, GEN data, long prec)
{
#if 0
  /* TODO: synchronize quadclassunit output with bnfinit */
  if (typ(P)==t_INT)
  {
    if (flag<4) err(impl,"specific bnfinit for quadratic fields");
    return quadclassunit0(P,0,data,prec);
  }
#endif
  if (flag < 0 || flag > 3) err(flagerr,"bnfinit");
  return classgroupall(P,data,flag,prec);
}

GEN
classgrouponly(GEN P, GEN data, long prec)
{
  pari_sp av = avma;
  GEN z;

  if (typ(P)==t_INT)
  {
    z=quadclassunit0(P,0,data,prec); setlg(z,4);
    return gerepilecopy(av,z);
  }
  z=(GEN)classgroupall(P,data,6,prec)[1];
  return gerepilecopy(av,(GEN)z[5]);
}

GEN
regulator(GEN P, GEN data, long prec)
{
  pari_sp av = avma;
  GEN z;

  if (typ(P)==t_INT)
  {
    if (signe(P)>0)
    {
      z=quadclassunit0(P,0,data,prec);
      return gerepilecopy(av,(GEN)z[4]);
    }
    return gun;
  }
  z=(GEN)classgroupall(P,data,6,prec)[1];
  return gerepilecopy(av,(GEN)z[6]);
}

INLINE GEN
col_0(long n)
{
   GEN c = (GEN) gpmalloc(sizeof(long)*(n+1));
   long i;
   for (i=1; i<=n; i++) c[i]=0;
   c[0] = evaltyp(t_VECSMALL) | evallg(n+1);
   return c;
}

GEN
cgetc_col(long n, long prec)
{
  GEN c = cgetg(n+1,t_COL);
  long i;
  for (i=1; i<=n; i++) c[i] = (long)cgetc(prec);
  return c;
}

static GEN
buchall_for_degree_one_pol(GEN nf, GEN CHANGE, long flun)
{
  pari_sp av = avma;
  GEN W,B,A,C,Vbase,res;
  GEN fu=cgetg(1,t_VEC), R=gun, zu=cgetg(3,t_VEC);
  GEN clg1=cgetg(4,t_VEC), clg2=cgetg(4,t_VEC);

  clg1[1]=un; clg1[2]=clg1[3]=clg2[2]=clg2[3]=lgetg(1,t_VEC);
  clg2[1]=lgetg(1,t_MAT);
  zu[1]=deux; zu[2]=lnegi(gun);
  W=B=A=C=cgetg(1,t_MAT);
  Vbase=cgetg(1,t_COL);

  res = get_clfu(clg1, R, zu, fu, flun);
  return gerepilecopy(av, buchall_end(nf,CHANGE,flun,res,clg2,W,B,A,C,Vbase));
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
  H = hnfall_i(x, NULL, 1);
  h = cgetg(1, t_MAT);
  dj = 1;
  for (j = 1; j < l; )
  {
    pari_sp av = avma;
    long lv = lg(v);

    for (k = 0; k < dj; k++) v[lv+k] = j+k;
    setlg(v, lv + dj);
    h2 = hnfall_i(vecextract_p(x, v), NULL, 1);
    if (gegal(h, h2))
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
      if (gegal(h2, H)) break;
      h = h2; j++;
    }
  }
  return v;
}

static GEN
col_dup(long n, GEN col)
{
   GEN c = new_chunk(n+1);
   memcpy(c,col,(n+1)*sizeof(long));
   return c;
}
static GEN
col_extract(REL_t *rel, FB_t *F)
{
  long i, l = lg(F->perm);
  GEN c = cgetg(l, t_COL);
  for (i = 1; i < l; i++) c[i] = lstoi( rel->R[ F->perm[i] ] );
  return c;
}

GEN
buchall(GEN P,GEN gcbach,GEN gcbach2,GEN gRELSUP,GEN gborne,long nbrelpid,
        long minsFB,long flun,long prec)
{
  pari_sp av = avma, av0, av2, limpile;
  long N, R1, R2, RU, PRECREG, PRECLLL, KCCO, RELSUP, LIMC, LIMC2, lim;
  long nlze, zc, nrelsup, nreldep, phase, i, j, k, MAXRELSUP;
  long sfb_increase, sfb_trials, precdouble = 0, precadd = 0;
  double cbach, cbach2, drc, LOGD, LOGD2;
  GEN vecG, fu, zu, nf, D, A, W, R, Res, z, h, list_jideal, PERM;
  GEN M, res, L, resc, B, C, lambda, pdep, liste, invp, clg1, clg2, Vbase;
  GEN CHANGE = NULL;
  char *precpb = NULL;
  FB_t F;
  REL_t *rel, *oldrel;
  RELCACHE_t cache;

  if (DEBUGLEVEL) (void)timer2();

  P = get_nfpol(P, &nf);
  if (typ(gRELSUP) != t_INT) gRELSUP = gtrunc(gRELSUP);
  RELSUP = itos(gRELSUP);
  if (RELSUP<=0) err(talker,"not enough relations in bnfxxx");

  /* Initializations */
  fu = NULL; /* gcc -Wall */
  N = degpol(P);
  PRECREG = max(BIGDEFAULTPREC,prec);
  if (!nf)
  {
    nf = initalg(P, PRECREG);
    /* P was non-monic and nfinit changed it ? */
    if (lg(nf)==3) { CHANGE = (GEN)nf[2]; nf = (GEN)nf[1]; }
  }
  if (N <= 1) return buchall_for_degree_one_pol(nf,CHANGE,flun);
  zu = rootsof1(nf);
  zu[2] = lmul((GEN)nf[7],(GEN)zu[2]);
  if (DEBUGLEVEL) msgtimer("initalg & rootsof1");

  nf_get_sign(nf, &R1, &R2); RU = R1+R2;
  D = (GEN)nf[3]; drc = fabs(gtodouble(D));
  LOGD = log(drc); LOGD2 = LOGD*LOGD;
  lim = (long) (exp(-(double)N) * sqrt(2*PI*N*drc) * pow(4/PI,(double)R2));
  if (lim < 3) lim = 3;
  cbach = min(12., gtodouble(gcbach)); cbach /= 2;
  if (cbach == 0.) err(talker,"Bach constant = 0 in bnfxxx");
  if (nbrelpid <= 0) gborne = gzero;

  cbach2 = gtodouble(gcbach2);
  /* resc ~ sqrt(D) w / 2^r1 (2pi)^r2 = hR / Res(zeta_K, s=1) */
  resc = gdiv(mulri(gsqrt(absi(D),DEFAULTPREC), (GEN)zu[1]),
              gmul2n(gpowgs(Pi2n(1,DEFAULTPREC), R2), R1));
  if (DEBUGLEVEL)
    fprintferr("N = %ld, R1 = %ld, R2 = %ld\nD = %Z\n",N,R1,R2,D);
  av0 = avma; cache.last = cache.base = NULL;

START:
  avma = av0; desallocate(&cache);
  cbach = check_bach(cbach,12.);
  LIMC = (long)(cbach*LOGD2);
  if (LIMC < 20) { LIMC = 20; cbach = (double)LIMC / LOGD2; }
  LIMC2= max(3 * N, (long)(cbach2*LOGD2));
  if (LIMC2 < LIMC) LIMC2 = LIMC;
  if (DEBUGLEVEL) { fprintferr("LIMC = %ld, LIMC2 = %ld\n",LIMC,LIMC2); }

  Res = FBgen(&F, nf, LIMC2, LIMC);
  if (!Res || !subFBgen(&F, nf, min(lim,LIMC2) + 0.5, minsFB)) goto START;
  PERM = gcopy(F.perm);
  if (DEBUGLEVEL)
  {
    if (DEBUGLEVEL>3)
    {
      fprintferr("\n***** IDEALS IN FACTORBASE *****\n\n");
      for (i=1; i<=F.KC; i++) fprintferr("no %ld = %Z\n",i,F.LP[i]);
      fprintferr("\n***** IDEALS IN SUB FACTORBASE *****\n\n");
      outerr(vecextract_p(F.LP,F.subFB));
      fprintferr("\n***** INITIAL PERMUTATION *****\n\n");
      fprintferr("perm = %Z\n\n",F.perm);
    }
    msgtimer("sub factorbase (%ld elements)",lg(F.subFB)-1);
  }
  KCCO = F.KC+RU-1 + RELSUP; /* expected # of needed relations */
  if (DEBUGLEVEL)
    fprintferr("relsup = %ld, KCZ = %ld, KC = %ld, KCCO = %ld\n",
               RELSUP, F.KCZ, F.KC, KCCO);
  MAXRELSUP = min(50, 4*F.KC);
  /* make room for lots of relations */
  reallocate(&cache, 10*KCCO + MAXRELSUP);
  /* trivial relations (p) = prod P^e */
  oldrel = cache.base; rel = oldrel + 1;
  for (i=1; i<=F.KCZ; i++)
  {
    long p = F.FB[i];
    GEN c, P = F.LV[p];
    if (!isclone(P)) continue;

    /* all prime divisors in FB */
    c = col_0(F.KC); k = F.iLP[p];
    rel->nz = k+1;
    rel->R  = c; c += k;
    rel->ex = NULL;
    rel->m  = NULL;
    rel->pow= F.pow;
    for (j=lg(P)-1; j; j--) c[j] = itos(gmael(P,j,3));
    rel++;
  }
  cache.last = rel - 1;
  /* initialize for other relations */
  cache.end = cache.base + KCCO;
  for (rel = cache.last + 1; rel <= cache.end; rel++) rel->R = col_0(F.KC);
  if (DEBUGLEVEL)
    fprintferr("After trivial relations, cglob = %ld\n",
               cache.last - cache.base);

  sfb_trials = sfb_increase = nreldep = nrelsup = 0;

  /* PRECLLL = prec for LLL-reductions (idealred)
   * PRECREG = prec for archimedean components */
  PRECLLL = DEFAULTPREC
          + ((expi(D)*(lg(F.subFB)-2) + ((N*N)>>2)) >> TWOPOTBITS_IN_LONG);
  if (!precdouble) PRECREG = prec+1;
  if (PRECREG < PRECLLL)
  { /* very rare */
    PRECREG = PRECLLL;
    nf = nfnewprec(nf,PRECREG); av0 = avma;
  }
  M = gmael(nf, 5, 1);
  av2 = avma; liste = vecsmall_const(F.KC, 0);
  invp = relationrank(&cache, liste);

  /* relations through elements of small norm */
  if (gsigne(gborne) > 0)
    small_norm_for_buchall(&cache,&F,PRECREG,LOGD,nf,nbrelpid,invp,liste,LIMC2);
  avma = av2; limpile = stack_lim(av2,1);

  phase = 0;
  nlze = 0; /* for lint */
  vecG = list_jideal = NULL;

  /* Random relations */
  if (cache.last == cache.end)
    ((void(*)(long))random_relation)(-1); /* enough rels. Init nevertheless */
  else
  {
    if (DEBUGLEVEL) fprintferr("\n#### Looking for random relations\n");
MORE:
    if (sfb_increase)
    {
      if (DEBUGLEVEL) fprintferr("*** Increasing sub factor base\n");
      sfb_increase = 0;
      if (++sfb_trials > SFB_MAX || !subFBgen_increase(&F, nf, SFB_STEP))
        goto START;
      nreldep = nrelsup = 0;
    }

    if (phase)
    { /* reduced the relation matrix at least once */
      long lgex = max(nlze, MIN_EXTRA); /* # of new relations sought */
      size_t slim = (cache.last - cache.base) + lgex;
      if (slim > cache.len) reallocate(&cache, slim << 1);
      cache.end = cache.base + slim;
      for (rel = cache.last + 1; rel <= cache.end; rel++) rel->R = col_0(F.KC);
      if (DEBUGLEVEL)
	fprintferr("\n(need %ld more relation%s)\n", lgex, (lgex==1)?"":"s");
    }
    if (!vecG)
    {
      vecG = compute_vecG(nf,PRECLLL);
      av2 = avma;
    }
    if (!F.pow) powFBgen(&F, nf, CBUCHG+1);
    if (!random_relation(phase, &cache, PRECREG,MAXRELSUP,
                         nf,vecG,list_jideal,&F)) goto START; /* could not find relations */
    if (DEBUGLEVEL > 3 && phase == 0) dbg_outrel(&cache);
  }

PRECPB:
  if (precpb)
  {
    precdouble++;
    if (precadd)
    { PRECREG += precadd; precadd = 0; }
    else
      PRECREG = (PRECREG<<1)-2;
    if (DEBUGLEVEL)
    {
      char str[64]; sprintf(str,"buchall (%s)",precpb);
      err(warnprec,str,PRECREG);
    }
    nf = nfnewprec(nf, PRECREG);
    M = gmael(nf, 5, 1); 
    if (F.pow && F.pow->arc) { gunclone(F.pow->arc); F.pow->arc = NULL; }
    for (i = 1; i < lg(PERM); i++) F.perm[i] = PERM[i];
    precpb = NULL; phase = 0; oldrel = cache.base;
  }
  if (F.pow && !F.pow->arc) powFB_fill(&cache, M);
  /* reduce relation matrices */
  if (phase == 0)
  { /* never reduced before */
    long lgex = cache.last - oldrel, j = 0;
    long **mat = (long**)cgetg(lgex+1, t_MAT);
    C = cgetg(lgex+1, t_MAT);
    for (rel = oldrel + 1; rel <= cache.last; rel++)
    {
      j++; mat[j] = col_dup(F.KC, rel->R);
      C[j] = (long)get_log_embed(rel, M, RU, R1, PRECREG);
    }
    W = hnfspec(mat, F.perm, &pdep, &B, &C, lg(F.subFB)-1);
  }
  else
  {
    long lgex = cache.last - oldrel, j = 0;
    GEN exmat = cgetg(lgex+1,t_MAT), exC = cgetg(lgex+1,t_MAT);
    for (rel = oldrel + 1; rel <= cache.last; rel++)
    {
      j++; exmat[j] = (long)col_extract(rel, &F);
      exC[j] = (long)get_log_embed(rel, M, RU, R1, PRECREG);
    }
    W = hnfadd(W, F.perm, &pdep, &B, &C, exmat, exC);
    if (low_stack(limpile, stack_lim(av2,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"buchall");
      gerepileall(av2,5, &W,&C,&B,&pdep,&nf);
    }
  }
  oldrel = cache.last;
  nlze = lg(pdep)>1? lg(pdep[1])-1: lg(B[1])-1;
  if (nlze) /* dependent rows */
  {
    if (phase)
    {
      list_jideal = NULL;
      if (++nreldep > MAXRELSUP || nlze > 40) sfb_increase = 1;
    } else
      list_jideal = vecextract_i(F.perm, 1, nlze);
    phase = 1;
    goto MORE;
  }
  phase = 1;

  zc = (cache.end - cache.base) - (lg(B)-1) - (lg(W)-1);
  A = vecextract_i(C, 1, zc); /* cols corresponding to units */
  R = compute_multiple_of_R(A, RU, N, &lambda);
  if (!R)
  { /* not full rank for units */
    if (DEBUGLEVEL) fprintferr("regulator is zero.\n");
    if (++nrelsup > MAXRELSUP) goto START;
    nlze = MIN_EXTRA; goto MORE;
  }
  /* anticipate precision problems */
  if (!lambda) { precpb = "bestappr"; goto PRECPB; }

  h = dethnf_i(W);
  if (DEBUGLEVEL) fprintferr("\n#### Tentative class number: %Z\n", h);

  z = mulrr(Res, resc); /* ~ hR if enough relations, a multiple otherwise */
  switch (compute_R(lambda, divir(h,z), &L, &R))
  {
    case fupb_PRECI: /* precision problem unless we cheat on Bach constant */
      if ((precdouble&7) < 7 || cbach>2) { precpb = "compute_R"; goto PRECPB; }
      goto START;
    case fupb_RELAT: /* not enough relations */
      if (++nrelsup <= MAXRELSUP) nlze = MIN_EXTRA; else sfb_increase = 1;
      goto MORE;
  }
  /* DONE */

  if (!be_honest(&F, nf, PRECLLL)) goto START;
  F.KCZ2 = 0; /* be honest only once ! */

  /* fundamental units */
  if (flun & (nf_UNITS|nf_INIT))
  {
    GEN v = extract_full_lattice(L); /* L may be very large */
    if (v)
    {
      A = vecextract_p(A, v);
      L = vecextract_p(L, v);
    }
    /* arch. components of fund. units */
    A = cleanarch(gmul(A,lllint(L)), N, PRECREG);
    if (DEBUGLEVEL) msgtimer("cleanarch");
  }
  if (flun & nf_UNITS)
  {
    long e;
    fu = getfu(nf,&A,flun,&e,PRECREG);
    if (e <= 0 && (flun & nf_FORCE))
    {
      if (e < 0) precadd = (DEFAULTPREC-2) + ((-e) >> TWOPOTBITS_IN_LONG);
      precpb = "getfu"; goto PRECPB;
    }
  }
  desallocate(&cache);

  /* class group generators */
  i = lg(C)-zc; C += zc; C[0] = evaltyp(t_MAT)|evallg(i);
  C = cleanarch(C,N,PRECREG);
  Vbase = vecextract_p(F.LP, F.perm);
  class_group_gen(nf,W,C,Vbase,PRECREG,NULL, &clg1, &clg2);
  res = get_clfu(clg1, R, zu, fu, flun);
  return gerepilecopy(av, buchall_end(nf,CHANGE,flun,res,clg2,W,B,A,C,Vbase));
}
