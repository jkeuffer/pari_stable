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

/*******************************************************************/
/*                                                                 */
/*         CLASS GROUP AND REGULATOR (McCURLEY, BUCHMANN)          */
/*                    GENERAL NUMBER FIELDS                        */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "parinf.h"
extern GEN gscal(GEN x,GEN y);
extern GEN nfbasic_to_nf(nfbasic_t *T, GEN ro, long prec);
extern GEN get_nfindex(GEN bas);
extern GEN sqred1_from_QR(GEN x, long prec);
extern GEN computeGtwist(GEN nf, GEN vdir);
extern GEN famat_to_nf(GEN nf, GEN f);
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
extern GEN init_idele(GEN nf);
extern GEN norm_by_embed(long r1, GEN x);
extern void minim_alloc(long n,double ***q,long **x,double **y,double **z,double **v);
extern GEN arch_mul(GEN x, GEN y);

#define SFB_MAX 2
#define SFB_STEP 2
#define MIN_EXTRA 1

#define RANDOM_BITS 4
static const int CBUCHG = (1<<RANDOM_BITS) - 1;
static const int randshift = BITS_IN_RANDOM-1 - RANDOM_BITS;
#undef RANDOM_BITS

/* used by factor[elt|gen|gensimple] to return factorizations of smooth elts
 * HACK: MAX_FACTOR_LEN never checked, we assume default value is enough
 * (since elts have small norm) */
static long primfact[500], expoprimfact[500];

/* a factor base contains only non-inert primes
 * KC = # of P in factor base (p <= n, NP <= n2)
 * KC2= # of P assumed to generate class group (NP <= n2)
 *
 * KCZ = # of rational primes under ideals counted by KC
 * KCZ2= same for KC2 */
typedef struct {
  GEN FB; /* FB[i] = i-th rational prime used in factor base */
  GEN LP; /* vector of all prime ideals in FB */
  GEN *LV; /* LV[p] = vector of P|p, NP <= n2
            * isclone() is set for LV[p] iff all P|p are in FB
            * LV[i], i not prime or i > n2, is undefined! */
  GEN iLP; /* iLP[p] = i such that LV[p] = [LP[i],...] */
  long KC, KCZ, KCZ2;
  GEN subFB; /* LP o subFB =  part of FB used to build random relations */
  GEN powsubFB; /* array of [P^0,...,P^CBUCHG], P in LP o subFB */
  GEN perm; /* permutation of LP used to represent relations [updated by
               hnfspec/hnfadd: dense rows come first] */
} FB_t;

/* x a t_VECSMALL */
static long
ccontent(GEN x)
{
  long i, l = lg(x), s = labs(x[1]);
  for (i=2; i<l && s!=1; i++) s = cgcd(x[i],s);
  return s;
}

static void
desallocate(GEN **M, GEN *first_nz)
{
  GEN *m = *M;
  long i;
  if (m)
  {
    for (i=lg(m)-1; i; i--) free(m[i]);
    free((void*)*M); *M = NULL;
    free((void*)*first_nz); *first_nz = NULL;
  }
}

GEN
cgetalloc(GEN x, size_t l, long t)
{
  x = (GEN)gprealloc((void*)x, l * sizeof(long));
  x[0] = evaltyp(t) | evallg(l); return x;
}

static void
reallocate(long max, GEN *M, GEN *first_nz)
{
  size_t l = max+1;
  *M = cgetalloc(*M, l, t_VEC);
  *first_nz = cgetalloc(*first_nz, l, t_VECSMALL);
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

/* set subFB, reset F->powsubFB
 * Fill F->perm (if != NULL): primes ideals sorted by increasing norm (except
 * the ones in subFB come first [dense rows for hnfspec]) */
static int
subFBgen(FB_t *F, GEN nf, double PROD, long minsFB)
{
  GEN y, perm, yes, no, D = (GEN)nf[3];
  long i, j, k, iyes, ino, lv = F->KC + 1;
  double prod;
  const int init = (F->perm == NULL);
  gpmem_t av;

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
  F->powsubFB = NULL; return 1;
}

static GEN
mulred(GEN nf,GEN x, GEN I, long prec)
{
  gpmem_t av = avma;
  GEN y = cgetg(3,t_VEC);

  y[1] = (long)idealmulh(nf,I,(GEN)x[1]);
  y[2] = x[2];
  y = ideallllred(nf,y,NULL,prec);
  y[1] = (long)ideal_two_elt(nf,(GEN)y[1]);
  return gerepilecopy(av, y);
}

/* Compute powers of prime ideals (P^0,...,P^a) in subFB (a > 1)
 * powsubFB[j][i] contains P_i^j in LLL form + archimedean part in
 * MULTIPLICATIVE form (logs are expensive) */
static void
powsubFBgen(FB_t *F, GEN nf, long a, long prec)
{
  long i,j, n = lg(F->subFB), RU = lg(nf[6]);
  GEN *pow, arch0 = cgetg(RU,t_COL);
  for (i=1; i<RU; i++) arch0[i] = un; /* 0 in multiplicative notations */

  if (DEBUGLEVEL) fprintferr("Computing powers for sub-factor base:\n");
  F->powsubFB = cgetg(n, t_VEC);
  for (i=1; i<n; i++)
  {
    GEN vp = (GEN)F->LP[ F->subFB[i] ];
    GEN z = cgetg(3,t_VEC); z[1]=vp[1]; z[2]=vp[2];
    pow = (GEN*)cgetg(a+1,t_VEC); F->powsubFB[i] = (long)pow;
    pow[1]=cgetg(3,t_VEC);
    pow[1][1] = (long)z;
    pow[1][2] = (long)arch0;
    vp = prime_to_ideal(nf,vp);
    for (j=2; j<=a; j++)
    {
      pow[j] = mulred(nf,pow[j-1],vp,prec);
      if (DEBUGLEVEL>1) fprintferr(" %ld",j);
    }
    if (DEBUGLEVEL>1) { fprintferr("\n"); flusherr(); }
  }
  if (DEBUGLEVEL) msgtimer("powsubFBgen");
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

  if (maxprime() < n2) err(primer1);
  F->FB  = cgetg(n2+1, t_VECSMALL);
  F->iLP = cgetg(n2+1, t_VECSMALL);
  F->LV = (GEN*)new_chunk(n2+1);

  Res = realun(DEFAULTPREC);
  prim = icopy(gun);
  i = ip = 0;
  F->KC = F->KCZ = 0;
  for (p = 0;;) /* p <= n2 */
  {
    gpmem_t av = avma, av1;
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
    F->iLP[p] = ip; ip += k-1;
    F->FB[++i] = p;
    F->LV[p] = P;
  }
  if (! F->KC) return NULL;
  setlg(F->FB, i); F->KCZ2 = i;
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

/* can we factor I / m ? (m pseudo minimum, computed in pseudomin) */
static long
factorgen(FB_t *F, GEN nf, GEN I, GEN m, long kcz, long limp)
{
  long i,j,n1,ip,v,p,k,lo,ifinal;
  GEN x,q,r,P,p1,listexpo;
  GEN Nm = absi( subres(gmul((GEN)nf[7],m), (GEN)nf[1]) ); /* |Nm| */

  x = diviiexact(Nm, dethnf_i(I)); /* m in I, so NI | Nm */
  if (is_pm1(x)) { primfact[0]=0; return 1; }
  listexpo = new_chunk(kcz+1);
  for (i=1; ; i++)
  {
    p=F->FB[i]; q=dvmdis(x,p,&r);
    for (k=0; !signe(r); k++) { x=q; q=dvmdis(x,p,&r); }
    listexpo[i] = k;
    if (cmpis(q,p)<=0) break;
    if (i==kcz) return 0;
  }
  if (cmpis(x,limp) > 0) return 0;

  ifinal = i; lo = 0;
  for (i=1; i<=ifinal; i++)
  {
    k = listexpo[i];
    if (k)
    {
      p = F->FB[i];
      p1 = F->LV[p]; n1 = lg(p1);
      ip = F->iLP[p];
      for (j=1; j<n1; j++)
      {
        P = (GEN)p1[j];
	v = idealval(nf,I, P) - element_val2(nf,m,Nm, P);
	if (v) /* hence < 0 */
	{
	  primfact[++lo]=ip+j; expoprimfact[lo]=v;
	  k += v * itos((GEN)P[4]);
	  if (!k) break;
	}
      }
      if (k) return 0;
    }
  }
  if (is_pm1(x)) { primfact[0]=lo; return 1; }

  p = itos(x);
  p1 = F->LV[p]; n1 = lg(p1);
  ip = F->iLP[p];
  for (k=1,j=1; j<n1; j++)
  {
    P = (GEN)p1[j];
    v = idealval(nf,I, P) - element_val2(nf,m,Nm, P);
    if (v)
    {
      primfact[++lo]=ip+j; expoprimfact[lo]=v;
      k += v*itos((GEN)P[4]);
      if (!k) { primfact[0]=lo; return 1; }
    }
  }
  return 0;
}

/* can we factor x ? Nx = norm(x) */
static long
factorelt(FB_t *F,GEN nf,GEN x,GEN Nx,long kcz,long limp)
{
  long i,j,n1,ip,v,p,k,lo,ifinal;
  GEN q,r,P,p1,listexpo;

  if (is_pm1(Nx)) { primfact[0]=0; return 1; }
  listexpo = new_chunk(kcz+1);
  for (i=1; ; i++)
  {
    p=F->FB[i]; q=dvmdis(Nx,p,&r);
    for (k=0; !signe(r); k++) { Nx=q; q=dvmdis(Nx,p,&r); }
    listexpo[i] = k;
    if (cmpis(q,p)<=0) break;
    if (i==kcz) return 0;
  }
  if (cmpis(Nx,limp) > 0) return 0;

  ifinal=i; lo = 0;
  for (i=1; i<=ifinal; i++)
  {
    k = listexpo[i];
    if (k)
    {
      p = F->FB[i];
      p1 = F->LV[p]; n1 = lg(p1);
      ip = F->iLP[p];
      for (j=1; j<n1; j++)
      {
        P = (GEN)p1[j];
	v = int_elt_val(nf,x,(GEN)P[1],(GEN)P[5], NULL);
	if (v)
	{
	  primfact[++lo]=ip+j; expoprimfact[lo]=v;
	  k -= v * itos((GEN)P[4]);
	  if (!k) break;
	}
      }
      if (k) return 0;
    }
  }
  if (is_pm1(Nx)) { primfact[0]=lo; return 1; }

  p = itos(Nx);
  p1 = F->LV[p]; n1 = lg(p1);
  ip = F->iLP[p];
  for (k=1,j=1; j<n1; j++)
  {
    P = (GEN)p1[j];
    v = int_elt_val(nf,x,(GEN)P[1],(GEN)P[5], NULL);
    if (v)
    {
      primfact[++lo]=ip+j; expoprimfact[lo]=v;
      k -= v*itos((GEN)P[4]);
      if (!k) { primfact[0]=lo; return 1; }
    }
  }
  return 0;
}

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

enum { RELAT, LARGE, PRECI };

static GEN
not_given(gpmem_t av, long fl, long reason)
{
  if (! (fl & nf_FORCE))
  {
    char *s;
    switch(reason)
    {
      case LARGE: s = "fundamental units too large"; break;
      case PRECI: s = "insufficient precision for fundamental units"; break;
      default: s = "unknown problem with fundamental units";
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

static GEN
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
static GEN
gauss_realimag(GEN x, GEN y)
{
  GEN M = (typ(x)==t_VEC)? gmael(checknf(x),5,1): x;
  long l = lg(M), r2 = l - lg(M[1]), r1 = l-1 - 2*r2;
  M = split_realimag(M,r1,r2);
  y = split_realimag(y,r1,r2); return gauss(M, y);
}

GEN
getfu(GEN nf,GEN *ptA,GEN reg,long fl,long *pte,long prec)
{
  long e, i, j, R1, RU, N=degpol(nf[1]);
  gpmem_t av = avma;
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
  if (!u) return not_given(av,fl,PRECI);

  p1 = gmul(matep,u);
  if (expgexpo(p1) > 20) { *pte = BIGINT; return not_given(av,fl,LARGE); }
  matep = gexp(p1,prec);
  y = grndtoi(gauss_realimag(nf,matep), &e);
  *pte = -e;
  if (e >= 0) return not_given(av,fl,PRECI);
  for (j=1; j<RU; j++)
    if (!gcmp1(idealnorm(nf, (GEN)y[j]))) break;
  if (j < RU) { *pte = 0; return not_given(av,fl,PRECI); }
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
  gpmem_t av = avma;
  GEN nf,A,reg,res, y = cgetg(3,t_VEC);

  bnf = checkbnf(bnf); A = (GEN)bnf[3]; nf = (GEN)bnf[7];
  res = (GEN)bnf[8]; reg = (GEN)res[2];
  if (lg(res)==7 && lg(res[5])==lg(nf[6])-1)
  {
    y[1] = lcopy((GEN)res[5]);
    y[2] = lcopy((GEN)res[6]); return y;
  }
  y[1] = (long)getfu(nf, &A, reg, nf_UNITS, &c, 0);
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

/* try to split ideal / (some integer) on FB */
static long
factorgensimple(GEN nf,GEN ideal,GEN Vbase)
{
  long N, i, v, lo, L = lg(Vbase);
  gpmem_t av1 = avma;
  GEN x;
  if (typ(ideal) != t_MAT) ideal = (GEN)ideal[1]; /* idele */
  x = dethnf_i(ideal);
  N = lg(ideal)-1;
  if (gcmp1(x)) { avma=av1; primfact[0]=0; return 1; }
  for (lo=0, i=1; i<L; i++)
  {
    GEN q,y, P=(GEN)Vbase[i], p=(GEN)P[1];
    long vx0, vx, sum_ef, e,f,lo0,i0;

    vx = pvaluation(x,p,&y);
    if (!vx) continue;
    /* p | x = Nideal */
    vx0 = vx; sum_ef = 0; lo0 =lo; i0 = i;
    for(;;)
    {
      e = itos((GEN)P[3]);
      f = itos((GEN)P[4]); sum_ef += e * f;
      v = idealval(nf,ideal,P);
      if (v)
      {
        lo++; primfact[lo]=i; expoprimfact[lo]=v;
        vx -= v * f; if (!vx) break;
      }
      i++; if (i == L) break;
      P = (GEN)Vbase[i]; q = (GEN)P[1];
      if (!egalii(p,q)) break;
    }
    if (vx)
    { /* divisible by P | p not in FB */
      long k,l,n;
      k = N - sum_ef;
      if (k == 0) err(talker,"not an ideal in factorgensimple: %Z", ideal);
      if (vx % k) break;
      k = vx / k; /* ideal / p^k may factor on FB */
      for (l = lo0+1; l <= lo; l++)
      {
        P = (GEN)Vbase[primfact[l]];
        expoprimfact[l] -= k * itos((GEN)P[3]); /* may become 0 */
      }
      n = lo0+1;
      for (l = i0; l < i; l++) /* update exponents for other P | p */
      {
        if (n <= lo && primfact[n] == l) { n++; continue; }
        lo++; primfact[lo] = l; P = (GEN)Vbase[l];
        expoprimfact[lo] = - k * itos((GEN)P[3]);
      }
      /* check that ideal / p^k / (tentative factorisation) is integral */
      {
        GEN z = ideal;
        for (l = lo0+1; l <= lo; l++)
        {
          GEN n = stoi(- expoprimfact[l]);
          z = idealmulpowprime(nf, z, (GEN)Vbase[primfact[l]], n);
        }
        z = gdiv(z, gpowgs(p, k));
        if (!gcmp1(denom(z))) { avma=av1; return 0; }
        ideal = z;
      }
    }
    if (gcmp1(y)) { avma=av1; primfact[0]=lo; return 1; }
    x = y;
  }
  avma = av1; return 0;
}

static void
add_to_fact(long l, long v, long e)
{
  long i,lo;
  if (!e) return;
  for (i=1; i<=l && primfact[i] < v; i++)/*empty*/;
  if (i <= l && primfact[i] == v)
    expoprimfact[i] += e;
  else
  {
    lo = ++primfact[0];
    primfact[lo]     = v;
    expoprimfact[lo] = e;
  }
}

/* factor x = x0[1] on Vbase (modulo principal ideals). Archimedean parts
 * computed as famat */
static GEN
split_ideal(GEN nf, GEN x0, GEN Vbase, long prec)
{
  GEN p1, vdir, id, z, ex, y, x = (GEN)x0[1];
  long nbtest_lim, nbtest, bou, i, ru, lgsub;
  int flag = (gexpo(gcoeff(x,1,1)) < 100);

  y = x0;
  if (flag && factorgensimple(nf,y,Vbase)) return y;

  y = ideallllred(nf,x0,NULL,prec);
  if (flag && gcmp0((GEN)y[2])) flag = 0; /* y == x0 */
  if (flag && factorgensimple(nf,y,Vbase)) return y;

  z = init_idele(nf); ru = lg(z[2]);
  z[2] = lgetg(1, t_MAT);
  vdir = cgetg(ru,t_VECSMALL);
  for (i=2; i<ru; i++) vdir[i]=0;
  for (i=1; i<ru; i++)
  {
    vdir[i] = 10;
    y = ideallllred(nf,x0,vdir,prec);
    if (factorgensimple(nf,y,Vbase)) return y;
    vdir[i] = 0;
  }
  nbtest = 0; nbtest_lim = (ru-1) << 2; lgsub = 3;
  ex= cgetg(lgsub, t_VECSMALL);
  for(;;)
  {
    int non0 = 0;
    id = x0;
    for (i=1; i<lgsub; i++)
    {
      ex[i] = mymyrand() >> randshift;
      if (ex[i])
      { /* don't let id become too large as lgsub gets bigger: avoid
           prec problems */
        if (non0) id = ideallllred(nf,id,NULL,prec);
        non0++;
        z[1]=Vbase[i]; p1=idealpowred(nf,z,stoi(ex[i]),prec);
        id = idealmulh(nf,id,p1);
      }
    }
    if (id == x0) continue;

    for (i=1; i<ru; i++) vdir[i] = mymyrand() >> randshift;
    for (bou=1; bou<ru; bou++)
    {
      if (bou>1)
      {
        for (i=1; i<ru; i++) vdir[i] = 0;
        vdir[bou] = 10;
      }
      nbtest++;
      y = ideallllred(nf,id,vdir,prec);
      if (DEBUGLEVEL>2)
        fprintferr("nbtest = %ld, ideal = %Z\n",nbtest,y[1]);
      if (factorgensimple(nf,y,Vbase))
      {
        long l = primfact[0];
        for (i=1; i<lgsub; i++) add_to_fact(l,i,-ex[i]);
        return y;
      }
    }
    if (nbtest > nbtest_lim)
    {
      nbtest = 0;
      if (lgsub < 7)
      {
        lgsub++; nbtest_lim <<= 2;
        ex = cgetg(lgsub, t_VECSMALL);
      }
      else nbtest_lim = VERYBIGINT; /* don't increase further */
      if (DEBUGLEVEL)
        fprintferr("split_ideal: increasing factor base [%ld]\n",lgsub);
    }
  }
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
  gpmem_t av = avma;
  long i, c = lg(e);
  GEN z = C? C: gun;
  for (i=1; i<c; i++)
    if (signe(e[i])) z = idealmul(nf, z, idealpow(nf, (GEN)g[i], (GEN)e[i]));
  if (typ(z) != t_MAT) z = idealhermite(nf,z);
  if (typ(y) != t_MAT) y = idealhermite(nf,y);
  i = gegal(y, z); avma = av; return i;
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

  U = (GEN)clg2[1];
  cyc = gmael3(bnf,8,1,2); c = lg(cyc)-1;
  gen = gmael3(bnf,8,1,3);
  ex = cgetg(c+1,t_COL);
  if (c == 0 && !(flag & (nf_GEN|nf_GEN_IF_PRINCIPAL))) return ex;

  /* factor x */
  x = Q_primitive_part(x, &xc);

  xar = init_idele(nf);
  xar[1] = (long)x;
  xar[2] = lgetg(1,t_MAT); /* compute archimedean part as a famat */
  xar = split_ideal(nf,xar,get_Vbase(bnf),prec);

  lW = lg(W)-1; Wex = vecsmall_const(lW, 0);
  lB = lg(B)-1; Bex = vecsmall_const(lB, 0);
  for (i=1; i<=primfact[0]; i++)
  {
    long k = primfact[i];
    long l = k - lW;
    if (l <= 0) Wex[k] = expoprimfact[i];
    else        Bex[l] = expoprimfact[i];
  }

  /* x = g_W Wex + g_B Bex - [xar]
   *   = g_W A - [xar] + [C_B]Bex  since g_W B + g_B = [C_B] */
  A = gsub(small_to_col(Wex), gmul_mati_smallvec(B,Bex));
  if (old_format) U = ginv(U);
  Q = gmul(U, A);
  for (i=1; i<=c; i++)
    Q[i] = (long)truedvmdii((GEN)Q[i], (GEN)cyc[i], (GEN*)(ex+i));
  if ((flag & nf_GEN_IF_PRINCIPAL))
    { if (!gcmp0(ex)) return gzero; }
  else if (!(flag & nf_GEN))
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
  col = gadd(col, famat_to_arch(nf, (GEN)xar[2], prec));

  /* find coords on Zk; Q = N (x / \prod gj^ej) = N(alpha), denom(alpha) | d */
  Q = gdiv(dethnf_i(x), get_norm_fact(gen, ex, &d));
  col = isprincipalarch(bnf, col, Q, gun, d, &e);
  if (col && !fact_ok(nf,x, col,gen,ex)) col = NULL;
  if (!col && !gcmp0(ex))
  {
    p1 = isprincipalfact(bnf, gen, gneg(ex), x, flag);
    col = (GEN)p1[2];
    e = itos((GEN)p1[3]);
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
    e = 0;
  }
  y = cgetg(4,t_VEC);
  if (!xc) xc = gun;
  col = e? gmul(xc,col): cgetg(1,t_COL);
  if (flag & nf_GEN_IF_PRINCIPAL) return col;
  y[1] = lcopy(ex);
  y[2] = (long)col;
  y[3] = lstoi(-e); return y;
}

static GEN
triv_gen(GEN nf, GEN x, long c, long flag)
{
  GEN y;
  if (flag & nf_GEN_IF_PRINCIPAL)
    return (typ(x) == t_COL)? gcopy(x): algtobasis(nf,x);
  if (!(flag & nf_GEN)) return zerocol(c);
  y = cgetg(4,t_VEC);
  y[1] = (long)zerocol(c);
  y[2] = (long)((typ(x) == t_COL)? gcopy(x): algtobasis(nf,x));
  y[3] = lstoi(BIGINT); return y;
}

GEN
isprincipalall(GEN bnf,GEN x,long flag)
{
  long c, pr, tx = typ(x);
  gpmem_t av = avma;
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
    gpmem_t av1 = avma;
    GEN y = _isprincipal(bnf,x,&pr,flag);
    if (y) return gerepileupto(av,y);

    if (DEBUGLEVEL) err(warnprec,"isprincipal",pr);
    avma = av1; bnf = bnfnewprec(bnf,pr); (void)setrand(c);
  }
}

/* isprincipal for C * \prod P[i]^e[i] (C omitted if NULL) */
GEN
isprincipalfact(GEN bnf,GEN P, GEN e, GEN C, long flag)
{
  long l = lg(e), i, prec, c;
  gpmem_t av = avma;
  GEN id,id2, nf = checknf(bnf), z = NULL; /* gcc -Wall */
  int gen = flag & (nf_GEN | nf_GENMAT);

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
    gpmem_t av1 = avma;
    GEN y = _isprincipal(bnf, gen? (GEN)id[1]: id,&prec,flag);
    if (y)
    {
      if (gen && typ(y) == t_VEC)
      {
        GEN u = lift_intern(basistoalg(nf, (GEN)y[2]));
        if (flag & nf_GENMAT)
          y[2] = (gcmp1(u)&&lg(id[2])>1)? id[2]:
                                          (long)arch_mul((GEN)id[2], (GEN)y[2]);
        else
          y[2] = (long)algtobasis(nf, gmul((GEN)id[2], u));
        y = gcopy(y);
      }
      return gerepileupto(av,y);
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

/* if x a famat, assume it is an algebraic integer (very costly to check) */
GEN
isunit(GEN bnf,GEN x)
{
  long tx = typ(x), i, R1, RU, n, prec;
  gpmem_t av = avma, tetpil;
  GEN p1, v, rlog, logunit, y, ex, nf, z, pi2_sur_w, gn, emb;

  bnf = checkbnf(bnf); nf=(GEN)bnf[7];
  logunit = (GEN)bnf[3]; RU = lg(logunit);
  p1 = gmael(bnf,8,4); /* roots of 1 */
  gn = (GEN)p1[1]; n = itos(gn);
  z  = algtobasis(nf, (GEN)p1[2]);
  switch(tx)
  {
    case t_INT: case t_FRAC: case t_FRACN:
      if (!gcmp1(x) && !gcmp_1(x)) return cgetg(1,t_COL);
      y = zerocol(RU); i = (gsigne(x) > 0)? 0: n>>1;
      y[RU] = (long)gmodulss(i, n); return y;

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
      logN = gscal(rx, v); /* log(Nx), should be ~ 0 */
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

    if (++i > 4) err(precer,"isunit");
    prec = (prec-1)<<1;
    if (DEBUGLEVEL) err(warnprec,"isunit",prec);
    nf = nfnewprec(nf, prec);
  }

  setlg(ex, RU); p1 = cgetg(RU, t_VEC);
  for (i=1; i<RU; i++) p1[i] = coeff(logunit, 1, i);
  p1 = gneg(gimag(gmul(p1,ex))); if (!R1) p1 = gmul2n(p1, -1);
  p1 = gadd(garg((GEN)emb[1],DEFAULTPREC), p1);
  /* p1 = arg(the missing root of 1) */

  pi2_sur_w = divrs(mppi(DEFAULTPREC), n>>1);
  p1 = ground(gdiv(p1, pi2_sur_w));
  if (n > 2)
  {
    GEN ro = (GEN)gmul(rowextract_i(gmael(nf,5,1), 1, 1), z)[1];
    GEN p2 = ground(gdiv(garg(ro, DEFAULTPREC), pi2_sur_w));
    p1 = mulii(p1,  mpinvmod(p2, gn));
  }

  tetpil = avma; y = cgetg(RU+1,t_COL);
  for (i=1; i<RU; i++) y[i] = lcopy((GEN)ex[i]);
  y[RU] = lmodulcp(p1, gn); return gerepile(av,tetpil,y);
}

GEN
signunits(GEN bnf)
{
  long i, j, R1, RU, mun;
  gpmem_t av;
  GEN matunit,y,p1,p2,nf,pi;

  bnf = checkbnf(bnf); nf = (GEN)bnf[7];
  matunit = (GEN)bnf[3]; RU = lg(matunit);
  R1=itos(gmael(nf,2,1)); pi=mppi(MEDDEFAULTPREC);
  y=cgetg(RU,t_MAT); mun = lnegi(gun);
  for (j=1; j<RU; j++)
  {
    p1=cgetg(R1+1,t_COL); y[j]=(long)p1; av=avma;
    for (i=1; i<=R1; i++)
    {
      p2 = ground(gdiv(gimag(gcoeff(matunit,i,j)),pi));
      p1[i] = mpodd(p2)? mun: un;
    }
    avma=av;
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
set_log_embed(GEN col, GEN x, long R1, long prec)
{
  long i, l = lg(x);
  for (i=1; i<=R1; i++) gaffect(       glog((GEN)x[i],prec)    , (GEN)col[i]);
  for (   ; i < l; i++) gaffect(gmul2n(glog((GEN)x[i],prec), 1), (GEN)col[i]);
}

static void
set_fact(GEN c, GEN first_nz, long cglob)
{
  long i;
  first_nz[cglob] = primfact[1];
  for (i=1; i<=primfact[0]; i++) c[primfact[i]] = expoprimfact[i];
}

static void
unset_fact(GEN c)
{
  long i;
  for (i=1; i<=primfact[0]; i++) c[primfact[i]] = 0;
}

/* as small_to_mat, with explicit dimension d */
static GEN
small_to_mat_i(GEN z, long d)
{
  long i,j, l = lg(z);
  GEN x = cgetg(l,t_MAT);
  for (j=1; j<l; j++)
  {
    GEN c = cgetg(d+1, t_COL), cz = (GEN)z[j];
    x[j] = (long)c;
    for (i=1; i<=d; i++) c[i] = lstoi(cz[i]);
  }
  return x;
}

/* return -1 in case of precision problems. t = current # of relations */
static long
small_norm_for_buchall(long cglob,GEN *mat,GEN first_nz, GEN matarch,
                       long LIMC, long PRECREG, FB_t *F,
                       GEN nf,long nbrelpid,GEN invp,GEN L)
{
  const int maxtry_DEP  = 20;
  const int maxtry_FACT = 500;
  const double eps = 0.000001;
  double *y,*z,**q,*v, BOUND;
  gpmem_t av = avma, av1, av2, limpile;
  long j,k,noideal, nbrel = lg(mat)-1;
  long nbsmallnorm,nbfact,R1, N = degpol(nf[1]);
  GEN x,xembed,M,G,r,Gvec,prvec;

  if (DEBUGLEVEL)
    fprintferr("\n#### Looking for %ld relations (small norms)\n",nbrel);
  xembed = NULL; /* gcc -Wall */
  nbsmallnorm = nbfact = 0;
  R1 = nf_get_r1(nf);
  M = gmael(nf,5,1);
  G = gmael(nf,5,2);

  prvec = cgetg(3,t_VECSMALL); Gvec = cgetg(3,t_VEC);
  prvec[1] = MEDDEFAULTPREC;   Gvec[1] = (long)gprec_w(G,prvec[1]);
  prvec[2] = PRECREG;          Gvec[2] = (long)G;
  minim_alloc(N+1, &q, &x, &y, &z, &v);
  av1 = avma;
  for (noideal=F->KC; noideal; noideal--)
  {
    gpmem_t av0 = avma;
    long nbrelideal=0, dependent = 0, try_factor = 0, oldcglob = cglob;
    GEN IDEAL, ideal = (GEN)F->LP[noideal];

    if (DEBUGLEVEL>1) fprintferr("\n*** Ideal no %ld: %Z\n", noideal, ideal);
    ideal = prime_to_ideal(nf,ideal);
    IDEAL = lllint_ip(ideal,4); /* should be almost T2-reduced */
    r = red_ideal(&IDEAL,Gvec,prvec);
    if (!r) return -1; /* precision problem */

    for (k=1; k<=N; k++)
    {
      v[k]=gtodouble(gcoeff(r,k,k));
      for (j=1; j<k; j++) q[j][k]=gtodouble(gcoeff(r,j,k));
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
    k = N; y[N]=z[N]=0; x[N]= (long) sqrt(BOUND/v[N]);
    for(;; x[1]--)
    {
      gpmem_t av3 = avma;
      double p;
      GEN col;

      for(;;) /* looking for primitive element of small norm */
      { /* cf minim00 */
	if (k>1)
	{
	  long l = k-1;
	  z[l] = 0;
	  for (j=k; j<=N; j++) z[l] += q[l][j]*x[j];
	  p = x[k]+z[k];
	  y[l] = y[k]+p*p*v[k];
	  x[l] = (long) floor(sqrt((BOUND-y[l])/v[l])-z[l]);
          k = l;
	}
	for(;;)
	{
	  p = x[k]+z[k];
	  if (y[k] + p*p*v[k] <= BOUND) break;
	  k++; x[k]--;
	}
	if (k==1) /* element complete */
	{
	  if (y[1]<=eps) goto ENDIDEAL; /* skip all scalars: [*,0...0] */
	  if (ccontent(x)==1) /* primitive */
	  {
            GEN Nx, gx = gmul_mati_smallvec(IDEAL,x);
            gpmem_t av4;
            if (!isnfscalar(gx))
            {
              xembed = gmul(M,gx); av4 = avma; nbsmallnorm++;
              if (++try_factor > maxtry_FACT) goto ENDIDEAL;
              Nx = ground(norm_by_embed(R1,xembed)); setsigne(Nx, 1);
              if (factorelt(F,nf,gx,Nx,F->KCZ,LIMC)) { avma = av4; break; }
              if (DEBUGLEVEL > 1) { fprintferr("."); flusherr(); }
            }
	    avma = av3;
	  }
	  x[1]--;
	}
      }
      cglob++; col = mat[cglob];
      set_fact(col, first_nz, cglob);
      /* make sure we get maximal rank first, then allow all relations */
      if (cglob > 1 && cglob <= F->KC && ! addcolumntomatrix(col,invp,L))
      { /* Q-dependent from previous ones: forget it */
        cglob--; unset_fact(col);
        if (DEBUGLEVEL>1) { fprintferr("*"); flusherr(); }
        if (++dependent > maxtry_DEP) break;
        avma = av3; continue;
      }
      /* record archimedean part */
      set_log_embed((GEN)matarch[cglob], xembed, R1, PRECREG);
      dependent = 0;

      if (DEBUGLEVEL)
      {
        if (DEBUGLEVEL==1) fprintferr("%4ld",cglob);
        else { fprintferr("cglob = %ld. ",cglob); wr_rel(mat[cglob]); }
        flusherr(); nbfact++;
      }
      if (cglob >= nbrel) goto END; /* we have enough */
      if (++nbrelideal == nbrelpid) break;

      if (low_stack(limpile, stack_lim(av2,1)))
      {
	if(DEBUGMEM>1) err(warnmem,"small_norm");
        invp = gerepilecopy(av2, invp);
      }
    }
ENDIDEAL:
    if (cglob == oldcglob) avma = av0; else invp = gerepilecopy(av1, invp);
    if (DEBUGLEVEL>1) msgtimer("for this ideal");
  }
END:
  if (DEBUGLEVEL)
  {
    fprintferr("\n"); msgtimer("small norm relations");
    fprintferr("  small norms gave %ld relations, rank = %ld.\n",
               cglob, rank(small_to_mat_i((GEN)mat, F->KC)));
    if (nbsmallnorm)
      fprintferr("  nb. fact./nb. small norm = %ld/%ld = %.3f\n",
                  nbfact,nbsmallnorm,((double)nbfact)/nbsmallnorm);
  }
  avma = av; return cglob;
}

/* I assumed to be integral HNF, G the Cholesky form of a weighted T2 matrix.
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
dbg_newrel(long jideal, long jdir, long phase, long cglob, long *col,
           GEN colarch, long lim)
{
  fprintferr("\n++++ cglob = %ld: new relation (need %ld)", cglob, lim);
  wr_rel(col);
  if (DEBUGLEVEL>3)
  {
    fprintferr("(jideal=%ld,jdir=%ld,phase=%ld)", jideal,jdir,phase);
    msgtimer("for this relation");
  }
  if (DEBUGLEVEL>6) fprintferr("archimedian part = %Z\n",colarch);
  flusherr() ;
}

static void
dbg_cancelrel(long jideal,long jdir,long phase, long *col)
{
  fprintferr("rel. cancelled. phase %ld: ",phase);
  if (DEBUGLEVEL>3) fprintferr("(jideal=%ld,jdir=%ld)",jideal,jdir);
  wr_rel(col); flusherr();
}

static void
dbg_outrel(long cglob, GEN *mat,GEN maarch)
{
  gpmem_t av = avma;
  GEN p1;
  long j;

  p1 = cgetg(cglob+1, t_MAT);
  for (j=1; j<=cglob; j++) p1[j] = (long)small_to_col(mat[j]);
  fprintferr("\nRank = %ld\n", rank(p1));
  if (DEBUGLEVEL>3)
  {
    fprintferr("relations = \n");
    for (j=1; j <= cglob; j++) wr_rel(mat[j]);
    fprintferr("\nmatarch = %Z\n",maarch);
  }
  avma = av; flusherr();
}

/* Check if we already have a column mat[i] equal to mat[s]
 * General check for colinearity useless since exceedingly rare */
static long
already_found_relation(GEN *mat, long s, GEN first_nz)
{
  GEN cols = mat[s], nz = first_nz;
  long i, bs, l = lg(cols);

  bs = 1; while (bs < l && !cols[bs]) bs++;
  if (bs == l) return s; /* zero relation */

  for (i=s-1; i; i--)
  {
    if (bs == nz[s]) /* = index of first non zero elt in coll */
    {
      GEN coll = mat[i];
      long b = bs;
      do b++; while (b < l && cols[b] == coll[b]);
      if (b == l) return i;
    }
  }
  cols[0] = bs; return 0;
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
static long
random_relation(long phase,long cglob,long LIMC,long PRECREG,long MAXRELSUP,
                GEN nf,GEN vecG,GEN *mat,GEN first_nz,GEN matarch,
                GEN list_jideal, FB_t *F)
{
  static long jideal, jdir;
  long i, maxcglob, cptlist, cptzer, nbG, lgsub, r1, jlist = 1;
  gpmem_t av, av1;
  GEN arch,col,colarch,ideal,m,P,ex;

  if (phase != 1) { jideal=jdir=1; if (phase<0) return 0; }

  r1 = nf_get_r1(nf);
  maxcglob = lg(mat)-1; /* requested # of relations */
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
    {
      if (++cptlist > 300) return -1;
    }
    ideal = P;
    do {
      for (i=1; i<lgsub; i++)
      {
        ex[i] = mymyrand()>>randshift;
        if (ex[i]) ideal = idealmulh(nf,ideal, gmael3(F->powsubFB,i,ex[i],1));
      }
    }
    while (ideal == P); /* If ex  = 0, try another */
    ideal = remove_content(ideal);

    if (phase != 1) jdir = 1; else phase = 2;
    for (av1 = avma; jdir <= nbG; jdir++, avma = av1)
    { /* reduce along various directions */
      if (DEBUGLEVEL>2)
        fprintferr("phase=%ld,jideal=%ld,jdir=%ld,rand=%ld\n",
                   phase,jideal,jdir,getrand());
      m = pseudomin(ideal,(GEN)vecG[jdir]);
      if (!m) return -2;
      if (!factorgen(F,nf,ideal,m,F->KCZ,LIMC))
      {
        if (DEBUGLEVEL>1) { fprintferr("."); flusherr(); }
        continue;
      }
      /* can factor ideal, record relation */
      cglob++; col = mat[cglob];
      set_fact(col, first_nz, cglob); col[jideal]--;
      for (i=1; i<lgsub; i++) col[ F->subFB[i] ] -= ex[i];
      if (already_found_relation(mat, cglob, first_nz))
      { /* Already known: forget it */
        if (DEBUGLEVEL>1) dbg_cancelrel(jideal,jdir,phase,col);
        cglob--; unset_fact(col); col[jideal] = 0;
        for (i=1; i<lgsub; i++) col[ F->subFB[i] ] = 0;

        if (++cptzer > MAXRELSUP)
        {
          if (list_jideal) { cptzer -= 10; break; }
          return -1;
        }
        continue;
      }

      /* Compute and record archimedian part */
      cptzer = 0; arch = NULL;
      for (i=1; i<lgsub; i++)
        if (ex[i])
        {
          GEN p1 = gmael3(F->powsubFB,i,ex[i],2);
          arch = arch? vecmul(arch, p1): p1;
        }
      colarch = (GEN)matarch[cglob];
      /* arch = archimedean component (MULTIPLICATIVE form) of ideal */
      arch = vecdiv(arch, gmul(gmael(nf,5,1), m));
      set_log_embed(colarch, arch, r1, PRECREG);
      if (DEBUGLEVEL) dbg_newrel(jideal,jdir,phase,cglob,col,colarch,maxcglob);

      /* Need more, try next P */
      if (cglob < maxcglob) break;

      /* We have found enough. Return */
      if (phase)
      {
        jdir = 1;
        if (jideal == F->KC) jideal=1; else jideal++;
      }
      if (DEBUGLEVEL>2)
        fprintferr("Upon exit: jideal=%ld,jdir=%ld\n",jideal,jdir);
      avma = av; return cglob;
    }
    if (!list_jideal)
    {
      if (jideal == F->KC) jideal=1; else jideal++;
    }
  }
}

static long
be_honest(FB_t *F, GEN nf, long PRECLLL)
{
  long ex, i, j, J, k, iz, nbtest, ru, lgsub = lg(F->subFB);
  GEN G, M, P, ideal, m, exu;
  gpmem_t av;

  if (F->KCZ2 <= F->KCZ) return 1;
  if (DEBUGLEVEL)
  {
    fprintferr("Be honest for primes from %ld to %ld\n",
               F->FB[ F->KCZ+1 ], F->FB[ F->KCZ2 ]);
    flusherr();
  }
  if (!F->powsubFB) powsubFBgen(F, nf, CBUCHG+1, 0);
  M = gprec_w(gmael(nf,5,1), PRECLLL);
  G = gprec_w(gmael(nf,5,2), PRECLLL);
  ru = lg(G);
  exu = cgetg(ru, t_VECSMALL);
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
      GEN ideal0 = prime_to_ideal(nf,(GEN)P[j]);
      gpmem_t av2 = avma;
      for(nbtest=0;;)
      {
	ideal = ideal0;
	for (i=1; i<lgsub; i++)
	{
	  ex = mymyrand()>>randshift;
	  if (ex) ideal = idealmulh(nf,ideal,gmael3(F->powsubFB,i,ex,1));
	}
        ideal = remove_content(ideal);
	for (k=1; k<ru; k++)
	{
	  if (k==1)
            for (i=1; i<ru; i++) exu[i] = mymyrand()>>randshift;
          else
	  {
	    for (i=1; i<ru; i++) exu[i] = 0;
            exu[k] = 10;
	  }
          m = pseudomin(ideal, computeGtwist(nf, exu));
          if (m && factorgen(F,nf,ideal,m,iz-1,F->FB[iz-1])) break;
	  if (++nbtest==200) return 0;
	}
	avma = av2; if (k < ru) break;
      }
    }
  }
  if (DEBUGLEVEL)
  {
    if (DEBUGLEVEL>1) fprintferr("\n");
    msgtimer("be honest");
  }
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
  gpmem_t av = avma;

  if (DEBUGLEVEL) fprintferr("\n#### Computing regulator multiple\n");
  xreal = greal(A); /* = (log |sigma_i(u_j)|) */
  T = cgetg(RU+1,t_COL);
  for (i=1; i<=R1; i++) T[i] = un;
  for (   ; i<=RU; i++) T[i] = deux;
  mdet = concatsp(xreal,T); /* det(Span(mdet)) = N * R */

  i = gprecision(mdet); /* truncate to avoid "near dependant" vectors */
  mdet_t = (i <= 4)? mdet: gprec_w(mdet,i-1);
  v = (GEN)sindexrank(mdet_t)[2]; /* list of independant column indices */
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
  VOLATILE GEN y;
  jmp_buf env;
  void *c;
  if (setjmp(env)) return NULL;
  else
  {
    c = err_catch(precer, env, NULL);
    y = bestappr(x,k);
  }
  err_leave(&c);
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
 * In fact z is a very rough approximation and we only expect 0.75 < Rz < 1.5
 *
 * Output: *ptkR = R, *ptU = basis of fundamental units (in terms lambda) */
static int
compute_R(GEN lambda, GEN z, GEN *ptL, GEN *ptkR)
{
  gpmem_t av = avma;
  long r;
  GEN L,H,D,den,R;
  double c;

  if (DEBUGLEVEL) { fprintferr("\n#### Computing check\n"); flusherr(); }
  D = gmul2n(gmul(*ptkR,z), 1); /* bound for denom(lambda) */
  lambda = bestappr_noer(lambda,D);
  if (!lambda)
  {
    if (DEBUGLEVEL) fprintferr("truncation error in bestappr\n");
    return PRECI;
  }
  den = denom(lambda);
  if (gcmp(den,D) > 0)
  {
    if (DEBUGLEVEL) fprintferr("D = %Z\nden = %Z\n",D,den);
    return PRECI;
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
  if (c < 0.75) return PRECI;
  if (c > 1.5 ) { avma = av; return RELAT; }
  *ptkR = R; *ptL = L; return LARGE;
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
  z = init_idele(nf); z[2] = lgetg(1, t_MAT);
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
shift_embed(GEN G, GEN Gtw, long a, long r1, long r2)
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
shift_G(GEN G, GEN Gtw, long a, long b, long r1, long r2)
{
  GEN g = dummycopy(G);
  shift_embed(g,Gtw,a,r1,r2);
  shift_embed(g,Gtw,b,r1,r2); return g;
}

static GEN
compute_vecG(GEN nf,long prec)
{
  GEN vecG, Gtw, M = gmael(nf,5,1), G = gmael(nf,5,2);
  long r1,r2,i,j,ind, n = min(lg(M[1])-1, 9);

  nf_get_sign(nf,&r1,&r2);
  vecG=cgetg(1 + n*(n+1)/2,t_VEC);
  if (nfgetprec(nf) > prec)
  {
    M = gprec_w(M,prec);
    G = gprec_w(G,prec);
  }
  Gtw = gmul2n(G, 10);
  for (ind=j=1; j<=n; j++)
    for (i=1; i<=j; i++) vecG[ind++] = (long)shift_G(G,Gtw,i,j,r1,r2);
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
 * change matrix P by taking the independant columns of A and vectors from
 * the canonical basis. Update invp = 1/P, and L in {0,1}^n, with L[i] = 0
 * if P[i] = e_i, and 1 if P[i] = A_i (i-th column of A)
 */
static GEN
relationrank(GEN *A, long r, GEN L)
{
  long i, n = lg(L)-1;
  gpmem_t av = avma, lim = stack_lim(av, 1);
  GEN invp = idmat(n);

  if (!r) return invp;
  if (r>n) err(talker,"incorrect matrix in relationrank");
  for (i=1; i<=r; i++)
  {
    if (! addcolumntomatrix(A[i],invp,L) && i == r)
      err(talker,"not a maximum rank matrix in relationrank");
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"relationrank");
      invp = gerepilecopy(av, invp);
    }
  }
  return gerepilecopy(av, invp);
}

/* SMALLBUCHINIT */

static GEN
get_pr_lists(GEN FB)
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
  for (i=1; i<l; i++)
  {
    pr = (GEN)FB[i]; p = itos((GEN)pr[1]);
    L[p] = (long) (L[p]? concatsp((GEN)L[p], _vec(pr)): _vec(pr));
  }
  for (p=1; p<=pmax; p++)
    if (L[p]) L[p] = (long)gen_sort((GEN)L[p],0,cmp_prime_over_p);
  return L;
}

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
codeprime(GEN L, GEN pr)
{
  long j, n, l, p = itos((GEN)pr[1]);
  GEN al, fa;

  al = (GEN)pr[2]; n = lg(al)-1;
  fa = (GEN)L[p]; l = lg(fa);
  for (j=1; j<l; j++)
    if (gegal(al, gmael(fa,j,2))) return utoi(j-1 + n*p);
  err(bugparier,"codeprime");
  return NULL; /* not reached */
}

static GEN
codeprimes(GEN Vbase)
{
  GEN v, L = get_pr_lists(Vbase);
  long i, l = lg(Vbase);
  v = cgetg(l, t_VEC);
  for (i=1; i<l; i++) v[i] = (long)codeprime(L, (GEN)Vbase[i]);
  return v;
}

static GEN
decodeprime(GEN T, GEN L, long n)
{
  long t = itos(T);
  return gmael(L, t/n, t%n + 1);
}

/* v = bnf[10] */
GEN
get_matal(GEN v)
{
  if (typ(v) == t_VEC)
  {
    GEN ma = (GEN)v[1];
    if (typ(ma) != t_INT) return ma;
  }
  return NULL;
}

GEN
get_cycgen(GEN v)
{
  if (typ(v) == t_VEC)
  {
    GEN h = (GEN)v[2];
    if (typ(h) == t_VEC) return h;
  }
  return NULL;
}

/* compute principal ideals corresponding to (gen[i]^cyc[i]) */
static GEN
makecycgen(GEN bnf)
{
  GEN cyc,gen,h,nf,y,GD,D;
  long e,i,l;

  h = get_cycgen((GEN)bnf[10]);
  if (h) return h;

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
    y = isprincipalfact(bnf, gen, (GEN)D[i], NULL,
                        nf_GEN|nf_GENMAT|nf_FORCE);
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

  ma = get_matal((GEN)bnf[10]);
  if (ma) return ma;

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

    if (!y) y = isprincipalfact(bnf,pFB,ex,C, nf_GEN|nf_FORCE|nf_GIVEPREC);
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

/* insert O in bnf at index K
 * K = 1: matal
 * K = 2: cycgen */
static void
bnfinsert(GEN bnf, GEN O, long K)
{
  GEN v = (GEN)bnf[10];
  if (typ(v) != t_VEC)
  {
    GEN w = cgetg(3, t_VEC);
    long i;
    for (i = 1; i < 3; i++)
      w[i] = (i==K)? (long)O: zero;
    w = gclone(w);
    bnf[10] = (long)w;
  }
  else
    v[K] = lclone(O);
}

GEN
check_and_build_cycgen(GEN bnf)
{
  GEN cycgen = get_cycgen((GEN)bnf[10]);
  if (!cycgen)
  {
    gpmem_t av = avma;
    if (DEBUGLEVEL) err(warner,"completing bnf (building cycgen)");
    bnfinsert(bnf, makecycgen(bnf), 2); avma = av;
    cycgen = get_cycgen((GEN)bnf[10]);
  }
  return cycgen;
}

GEN
check_and_build_matal(GEN bnf)
{
  GEN matal = get_matal((GEN)bnf[10]);
  if (!matal)
  {
    gpmem_t av = avma;
    if (DEBUGLEVEL) err(warner,"completing bnf (building matal)");
    bnfinsert(bnf, makematal(bnf), 1); avma = av;
    matal = get_matal((GEN)bnf[10]);
  }
  return matal;
}

GEN
smallbuchinit(GEN pol,GEN gcbach,GEN gcbach2,GEN gRELSUP,GEN gborne,long nbrelpid,long minsFB,long prec)
{
  GEN y, bnf, nf, res, p1;
  gpmem_t av = avma;

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
  y[9] = (long)codeprimes((GEN)bnf[5]);

  p1 = cgetg(3, t_VEC);
  p1[1] = mael(res,4,1);
  p1[2] = (long)algtobasis(bnf,gmael(res,4,2));
  y[10] = (long)p1;

  y[11] = (long)algtobasis(bnf, (GEN)res[5]);
  y[12] = gcmp0((GEN)bnf[10])? (long)makematal(bnf): bnf[10];
  return gerepilecopy(av, y);
}

static GEN
get_regulator(GEN mun)
{
  gpmem_t av = avma;
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
  gpmem_t av = avma;
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
get_clfu(GEN clgp, GEN reg, GEN c1, GEN zu, GEN fu, long k)
{
  GEN z = cgetg(7, t_VEC);
  z[1]=(long)clgp; z[2]=(long)reg; z[3]=(long)c1;
  z[4]=(long)zu;   z[5]=(long)fu;  z[6]=lstoi(k); return z;
}

GEN
bnfmake(GEN sbnf, long prec)
{
  long j, k, l, n;
  gpmem_t av = avma;
  GEN p1, bas, ro, nf, mun, fu, L;
  GEN pfc, mc, clgp, clgp2, res, y, W, zu, reg, matal, Vbase;
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
  mun = get_archclean(nf,fu,prec,1);

  prec = gprecision(ro);
  matal = get_matal((GEN)sbnf[12]);
  if (!matal) matal = (GEN)sbnf[12];
  mc = get_archclean(nf,matal,prec,0);

  pfc = (GEN)sbnf[9];
  l = lg(pfc);
  Vbase = cgetg(l,t_COL);
  L = decode_pr_lists(nf, pfc);
  n = degpol(nf[1]);
  for (j=1; j<l; j++) Vbase[j] = (long)decodeprime((GEN)pfc[j], L, n);
  W = (GEN)sbnf[7];
  class_group_gen(nf,W,mc,Vbase,prec,NULL, &clgp,&clgp2);

  reg = get_regulator(mun);
  p1 = cgetg(3,t_VEC); zu = (GEN)sbnf[10];
  p1[1] = zu[1];
  p1[2] = lmul(bas,(GEN)zu[2]); zu = p1;

  res = get_clfu(clgp,reg,dbltor(1.0),zu,fu,1000);
  y=cgetg(11,t_VEC);
  y[1]=(long)W;   y[2]=sbnf[8];     y[3]=(long)mun;
  y[4]=(long)mc;  y[5]=(long)Vbase; y[6]=zero;
  y[7]=(long)nf;  y[8]=(long)res;   y[9]=(long)clgp2;
  y[10] = sbnf[12]; return gerepilecopy(av,y);
}

static GEN
classgroupall(GEN P, GEN data, long flag, long prec)
{
  long court[3],doubl[4];
  long fl, lx, minsFB=3, nbrelpid=4;
  gpmem_t av=avma;
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
  gpmem_t av = avma;
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
  gpmem_t av = avma;
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

#ifdef INLINE
INLINE
#endif
GEN
col_0(long n)
{
   GEN c = (GEN) gpmalloc(sizeof(long)*(n+1));
   long i;
   for (i=1; i<=n; i++) c[i]=0;
   c[0] = evaltyp(t_VECSMALL) | evallg(n);
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
buchall_end(GEN nf,GEN CHANGE,long fl,GEN res, GEN clg2, GEN W, GEN B,
            GEN A, GEN matarch, GEN Vbase)
{
  long l = (fl & nf_UNITS)? 7
                          : (fl & nf_ROOT1)? 5: 4;
  GEN p1, z;

  setlg(res, l);
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
  z[4]=(long)matarch;
  z[5]=(long)Vbase;
  z[6]=zero;
  z[7]=(long)nf;
  z[8]=(long)res;
  z[9]=(long)clg2;
  z[10]=zero; /* dummy: we MUST have lg(bnf) != lg(nf) */
  if (CHANGE) { p1=cgetg(3,t_VEC); p1[1]=(long)z; p1[2]=(long)CHANGE; z=p1; }
  return z;
}

static GEN
buchall_for_degree_one_pol(GEN nf, GEN CHANGE, long flun)
{
  gpmem_t av = avma;
  GEN W,B,A,matarch,Vbase,res;
  GEN fu=cgetg(1,t_VEC), R=gun, c1=gun, zu=cgetg(3,t_VEC);
  GEN clg1=cgetg(4,t_VEC), clg2=cgetg(4,t_VEC);

  clg1[1]=un; clg1[2]=clg1[3]=clg2[2]=clg2[3]=lgetg(1,t_VEC);
  clg2[1]=lgetg(1,t_MAT);
  zu[1]=deux; zu[2]=lnegi(gun);
  W=B=A=matarch=cgetg(1,t_MAT);
  Vbase=cgetg(1,t_COL);

  res = get_clfu(clg1, R, c1, zu, fu, EXP220);
  return gerepilecopy(av, buchall_end(nf,CHANGE,flun,res,clg2,W,B,A,matarch,Vbase));
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

  v = cgetg(l, t_VECSMALL);
  setlg(v, 1);
  H = hnfall_i(x, NULL, 1);
  h = cgetg(1, t_MAT);
  dj = 1;
  for (j = 1; j < l; )
  {
    gpmem_t av = avma;
    long lv = lg(v);

    for (k = 0; k < dj; k++) v[lv+k] = j+k;
    setlg(v, lv + dj);
    h2 = hnfall_i(vecextract_p(x, v), NULL, 1);
    if (gegal(h, h2))
    { /* these dj columns can be eliminated */
      avma = av; setlg(v, lv);
      j += dj;
      if (j >= l) break; /* shouldn't occur */
      dj <<= 1;
      if (j + dj >= l) dj = (l - j) >> 1;
    }
    else if (dj > 1)
    { /* at least one interesting column, try with first half of this set */
      avma = av; setlg(v, lv);
      dj >>= 1;
    }
    else
    { /* this column should be kept */
      if (gegal(h2, H)) break;
      h = h2; j++;
    }
  }
  return v;
}

GEN
buchall(GEN P,GEN gcbach,GEN gcbach2,GEN gRELSUP,GEN gborne,long nbrelpid,
        long minsFB,long flun,long prec)
{
  gpmem_t av = avma, av0, av1, limpile;
  long N,R1,R2,RU,PRECREG,PRECLLL,PRECLLLadd,KCCO,RELSUP,LIMC,LIMC2,lim;
  long nlze,zc,nrelsup,nreldep,phase,matmax,i,j,k,seed,MAXRELSUP;
  long sfb_increase=0, sfb_trials=0, precdouble=0, precadd=0;
  long cglob; /* # of relations found so far */
  double cbach, cbach2, drc, LOGD2;
  GEN vecG,fu,zu,nf,D,A,W,R,Res,z,h,list_jideal;
  GEN res,L,resc,B,C,lambda,pdep,liste,invp,clg1,clg2,Vbase;
  GEN *mat;     /* raw relations found (as VECSMALL, not HNF-reduced) */
  GEN first_nz; /* first_nz[i] = index of 1st non-0 entry in mat[i] */
  GEN CHANGE=NULL, extramat=NULL, extraC=NULL;
  char *precpb = NULL;
  FB_t F;

  if (DEBUGLEVEL) (void)timer2();

  P = get_nfpol(P, &nf);
  if (typ(gRELSUP) != t_INT) gRELSUP = gtrunc(gRELSUP);
  RELSUP = itos(gRELSUP);
  if (RELSUP<=0) err(talker,"not enough relations in bnfxxx");

  /* Initializations */
  fu = NULL; /* gcc -Wall */
  N = degpol(P);
  PRECREG = max(BIGDEFAULTPREC,prec);
  PRECLLLadd = DEFAULTPREC;
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
  LOGD2 = log(drc); LOGD2 = LOGD2*LOGD2;
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
  av0 = avma; mat = NULL; first_nz = NULL;

START:
  seed = getrand();
  avma = av0; desallocate(&mat, &first_nz);
  if (precpb)
  {
    precdouble++;
    if (precadd)
      PRECREG += precadd;
    else
      PRECREG = (PRECREG<<1)-2;
    if (DEBUGLEVEL)
    {
      char str[64]; sprintf(str,"buchall (%s)",precpb);
      err(warnprec,str,PRECREG);
    }
    precpb = NULL;
    nf = nfnewprec(nf,PRECREG); av0 = avma;
  }
  else
    cbach = check_bach(cbach,12.);
  precadd = 0;

  LIMC = (long)(cbach*LOGD2);
  if (LIMC < 20) { LIMC = 20; cbach = LIMC / LOGD2; }
  LIMC2= max(3 * N, (long)(cbach2*LOGD2));
  if (LIMC2 < LIMC) LIMC2 = LIMC;
  if (DEBUGLEVEL) { fprintferr("LIMC = %ld, LIMC2 = %ld\n",LIMC,LIMC2); }

  Res = FBgen(&F, nf, LIMC2, LIMC);
  if (!Res || !subFBgen(&F, nf, min(lim,LIMC2) + 0.5, minsFB)) goto START;

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
  sfb_trials = sfb_increase = 0;
  nreldep = nrelsup = 0;

  /* PRECLLL = prec for LLL-reductions (idealred)
   * PRECREG = prec for archimedean components */
  PRECLLL = PRECLLLadd
          + ((expi(D)*(lg(F.subFB)-2) + ((N*N)>>2)) >> TWOPOTBITS_IN_LONG);
  if (!precdouble) PRECREG = prec+1;
  if (PRECREG < PRECLLL)
  { /* very rare */
    PRECREG = PRECLLL;
    nf = nfnewprec(nf,PRECREG); av0 = avma;
  }
  KCCO = F.KC+RU-1 + RELSUP; /* expected # of needed relations */
  if (DEBUGLEVEL)
    fprintferr("relsup = %ld, KCZ = %ld, KC = %ld, KCCO = %ld\n",
               RELSUP, F.KCZ, F.KC, KCCO);
  MAXRELSUP = min(50, 4*F.KC);
  matmax = 10*KCCO + MAXRELSUP; /* make room for lots of relations */
  reallocate(matmax, (GEN*)&mat, &first_nz);
  setlg(mat, KCCO+1);
  C = cgetg(KCCO+1,t_MAT);
  /* trivial relations (p) = prod P^e */
  cglob = 0; z = zerocol(RU);
  for (i=1; i<=F.KCZ; i++)
  {
    long p = F.FB[i];
    GEN c, P = F.LV[p];
    if (!isclone(P)) continue;

    /* all prime divisors in FB */
    cglob++;
    C[cglob] = (long)z; /* 0 */
    mat[cglob] = c = col_0(F.KC);
    k = F.iLP[p];
    first_nz[cglob] = k+1;
    c += k;
    for (j=lg(P)-1; j; j--) c[j] = itos(gmael(P,j,3));
  }
  if (DEBUGLEVEL) fprintferr("After trivial relations, cglob = %ld\n",cglob);
  /* initialize for other relations */
  for (i=cglob+1; i<=KCCO; i++)
  {
    mat[i] = col_0(F.KC);
    C[i] = (long)cgetc_col(RU,PRECREG);
  }
  av1 = avma; liste = vecsmall_const(F.KC, 0);
  invp = relationrank(mat,cglob,liste);

  /* relations through elements of small norm */
  if (gsigne(gborne) > 0)
    cglob = small_norm_for_buchall(cglob,mat,first_nz,C,(long)LIMC,PRECREG,&F,
                                   nf,nbrelpid,invp,liste);
  if (cglob < 0) { precpb = "small_norm"; goto START; }
  avma = av1; limpile = stack_lim(av1,1);

  phase = 0;
  nlze = 0; /* for lint */
  vecG = NULL;
  list_jideal = NULL;

  /* random relations */
  if (cglob == KCCO) /* enough rels, but init random_relations just in case */
    ((void(*)(long))random_relation)(-1);
  else
  {
    GEN matarch;
    long ss;

    if (DEBUGLEVEL) fprintferr("\n#### Looking for random relations\n");
MORE:
    if (sfb_increase)
    {
      if (DEBUGLEVEL) fprintferr("*** Increasing sub factor base\n");
      sfb_increase = 0;
      if (++sfb_trials > SFB_MAX) goto START;
      if (! subFBgen(&F, nf, min(lim,LIMC2) + 0.5, lg(F.subFB)-1+SFB_STEP))
        goto START;
      nreldep = nrelsup = 0;
    }

    if (phase == 0) matarch = C;
    else
    { /* reduced the relation matrix at least once */
      long lgex = max(nlze, MIN_EXTRA); /* # of new relations sought */
      long slim; /* total # of relations (including lgex new ones) */
      setlg(extraC,  lgex+1);
      setlg(extramat,lgex+1); /* were allocated after hnfspec */
      slim = cglob+lgex;
      if (slim > matmax)
      {
        matmax = 2 * slim;
        reallocate(matmax, (GEN*)&mat, &first_nz);
      }
      setlg(mat, slim+1);
      if (DEBUGLEVEL)
	fprintferr("\n(need %ld more relation%s)\n", lgex, (lgex==1)?"":"s");
      for (j=cglob+1; j<=slim; j++) mat[j] = col_0(F.KC);
      matarch = extraC - cglob; /* start at 0, the others at cglob */
    }
    if (!vecG)
    {
      vecG = compute_vecG(nf,PRECLLL);
      av1 = avma;
    }
    if (!F.powsubFB)
    {
      powsubFBgen(&F, nf, CBUCHG+1, PRECREG);
      av1 = avma;
    }
    ss = random_relation(phase,cglob,(long)LIMC,PRECREG,MAXRELSUP,
                         nf,vecG,mat,first_nz,matarch,list_jideal,&F);
    if (ss < 0)
    { /* could not find relations */
      if (ss != -1)
      {
        precpb = "random_relation"; /* precision pb */
        PRECLLLadd = (PRECLLLadd<<1) - 2;
      }
      goto START;
    }
    if (DEBUGLEVEL > 2 && phase == 0) dbg_outrel(cglob,mat,matarch);
    if (phase)
      for (j=lg(extramat)-1; j>0; j--)
      {
	GEN c = mat[cglob+j], *g = (GEN*) extramat[j];
	for (k=1; k<=F.KC; k++) g[k] = stoi(c[F.perm[k]]);
      }
    cglob = ss;
  }

  /* reduce relation matrices */
  if (phase == 0)
  { /* never reduced before */
    long lgex;
    W = hnfspec(mat,F.perm,&pdep,&B,&C, lg(F.subFB)-1);
    phase = 1;
    nlze = lg(pdep)>1? lg(pdep[1])-1: lg(B[1])-1;
    if (nlze) list_jideal = vecextract_i(F.perm, 1, nlze);
    lgex = max(nlze, MIN_EXTRA); /* set lgex > 0, in case regulator is 0 */
    /* allocate now, reduce dimension later (setlg) when lgex goes down */
    extramat= cgetg(lgex+1,t_MAT);
    extraC  = cgetg(lgex+1,t_MAT);
    for (j=1; j<=lgex; j++)
    {
      extramat[j]=lgetg(F.KC+1,t_COL);
      extraC[j] = (long)cgetc_col(RU,PRECREG);
    }
  }
  else
  {
    if (low_stack(limpile, stack_lim(av1,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"buchall");
      gerepileall(av1,6, &W,&C,&B,&pdep,&extramat,&extraC);
    }
    list_jideal = NULL;
    W = hnfadd(W,F.perm,&pdep,&B,&C, extramat,extraC);
    nlze = lg(pdep)>1? lg(pdep[1])-1: lg(B[1])-1;
    if (nlze && ++nreldep > MAXRELSUP) { sfb_increase=1; goto MORE; }
  }
  if (nlze) goto MORE; /* dependent rows */

  /* first attempt at regulator for the check */
  zc = (lg(mat)-1) - (lg(B)-1) - (lg(W)-1);
  A = vecextract_i(C, 1, zc); /* cols corresponding to units */
  R = compute_multiple_of_R(A,RU,N,&lambda);
  if (!R)
  { /* not full rank for units */
    if (DEBUGLEVEL) fprintferr("regulator is zero.\n");
    if (++nrelsup > MAXRELSUP) goto START;
    nlze = MIN_EXTRA; goto MORE;
  }
  /* anticipate precision problems */
  if (!lambda) { precpb = "bestappr"; goto START; }

  h = dethnf_i(W);
  if (DEBUGLEVEL) fprintferr("\n#### Tentative class number: %Z\n", h);

  z = mulrr(Res, resc); /* ~ hR if enough relations, a multiple otherwise */
  switch (compute_R(lambda, divir(h,z), &L, &R))
  {
    case PRECI: /* precision problem unless we cheat on Bach constant */
      if (!precdouble) precpb = "compute_R";
      goto START;
    case RELAT: /* not enough relations */
      if (++nrelsup <= MAXRELSUP) nlze = MIN_EXTRA; else sfb_increase = 1;
      goto MORE;
  }
  /* DONE */

  if (!be_honest(&F, nf, PRECLLL)) goto START;

  /* fundamental units */
  if (flun & nf_INIT || flun & nf_UNITS)
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
    fu = getfu(nf,&A,R,flun,&k,PRECREG);
    if (k <= 0 && flun & nf_FORCE)
    {
      if (k < 0) precadd = (DEFAULTPREC-2) + ((-k) >> TWOPOTBITS_IN_LONG);
      (void)setrand(seed);
      precpb = "getfu"; goto START;
    }
  }
  desallocate(&mat, &first_nz);

  /* class group generators */
  i = lg(C)-zc; C += zc; C[0] = evaltyp(t_MAT)|evallg(i);
  C = cleanarch(C,N,PRECREG);
  Vbase = vecextract_p(F.LP, F.perm);
  class_group_gen(nf,W,C,Vbase,PRECREG,NULL, &clg1, &clg2);
  res = get_clfu(clg1, R, gdiv(mpmul(R,h), z), zu, fu, k);
  return gerepilecopy(av, buchall_end(nf,CHANGE,flun,res,clg2,W,B,A,C,Vbase));
}
