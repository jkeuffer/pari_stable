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
extern GEN to_famat_all(GEN x, GEN y);
extern int addcolumntomatrix(GEN V, GEN invp, GEN L);
extern double check_bach(double cbach, double B);
extern GEN gmul_mat_smallvec(GEN x, GEN y);
extern GEN gmul_mati_smallvec(GEN x, GEN y);
extern GEN get_arch_real(GEN nf,GEN x,GEN *emb,long prec);
extern GEN get_roots(GEN x,long r1,long ru,long prec);
extern void get_nf_matrices(GEN nf, long small);
extern long int_elt_val(GEN nf, GEN x, GEN p, GEN b, GEN *t, long v);
extern GEN init_idele(GEN nf);
extern GEN norm_by_embed(long r1, GEN x);
extern void minim_alloc(long n,double ***q,long **x,double **y,double **z,double **v);
extern GEN idealmulpowprime(GEN nf, GEN x, GEN vp, GEN n);
extern GEN arch_mul(GEN x, GEN y);
extern GEN vecdiv(GEN x, GEN y);
extern GEN vecmul(GEN x, GEN y);
extern GEN mul_real(GEN x, GEN y);

#define SFB_MAX 2
#define SFB_STEP 2
#define MIN_EXTRA 1

#define RANDOM_BITS 4
static const int CBUCHG = (1<<RANDOM_BITS) - 1;
static const int randshift = BITS_IN_RANDOM-1 - RANDOM_BITS;
#undef RANDOM_BITS

static long KC,KCZ,KCZ2,MAXRELSUP;
static long primfact[500],expoprimfact[500];
static GEN *idealbase, vectbase, FB, numFB, powsubFB, numideal;

/* FB[i]     i-th rational prime used in factor base
 * numFB[i]  index k such that FB[k]=i (0 if i is not prime)
 *
 * vectbase          vector of all ideals in FB
 * vecbase o subFB   part of FB used to build random relations
 * powsubFB  array lg(subFB) x (CBUCHG+1)   all powers up to CBUCHG
 *
 * idealbase[i]      prime ideals above i in FB
 * numideal[i]       index k such that idealbase[k] = i.
 *
 * mat            all relations found (as long integers, not reduced)
 * cglob          lg(mat) = total number of relations found so far
 *
 * Use only non-inert primes, coprime to discriminant index F:
 *   KC = number of prime ideals in factor base (norm < Bach cst)
 *   KC2= number of prime ideals assumed to generate class group (>= KC)
 *
 *   KCZ = number of rational primes under ideals counted by KC
 *   KCZ2= same for KC2
 */

/* x a t_VECSMALL */
static long
ccontent(GEN x)
{
  long i, l = lg(x), s=labs(x[1]);
  for (i=2; i<l && s>1; i++) s = cgcd(x[i],s);
  return s;
}

static void
desallocate(GEN **M)
{
  GEN *m = *M;
  long i;
  if (m)
  {
    for (i=lg(m)-1; i; i--) free(m[i]);
    free(m); *M = NULL;
  }
}

/* Return the list of indexes or the primes chosen for the subFB.
 * Fill vperm (if !=0): primes ideals sorted by increasing norm (except the
 * ones in subFB come first [dense rows come first for hnfspec])
 * ss = number of rational primes whose divisors are all in FB
 */
static GEN
subFBgen(long N,long m,long minsFB,GEN vperm, long *ptss)
{
  long av = avma,i,j, lv=lg(vectbase),s=0,s1=0,n=0,ss=0,z=0;
  GEN y1,y2,subFB,perm,perm1,P,Q;
  double prod;

  (void)new_chunk(lv); /* room for subFB */
  y1 = cgetg(lv,t_COL);
  y2 = cgetg(lv,t_COL);
  for (i=1,P=(GEN)vectbase[i];;P=Q)
  { /* we'll sort ideals by norm (excluded ideals = "zero") */
    long e = itos((GEN)P[3]);
    long ef= e*itos((GEN)P[4]);

    s1 += ef;
    y2[i] = (long)powgi((GEN)P[1],(GEN)P[4]);
    /* take only unramified ideals */
    if (e>1) { y1[i]=zero; s=0; z++; } else { y1[i]=y2[i]; s += ef; }

    i++; Q = (GEN)vectbase[i];
    if (i == lv || !egalii((GEN)P[1], (GEN)Q[1]))
    { /* don't take all P above a given p (delete the last one) */
      if (s == N) { y1[i-1]=zero; z++; }
      if (s1== N) ss++;
      if (i == lv) break;
      s = s1 = 0;
    }
  }
  if (z+minsFB >= lv) return NULL;

  prod = 1.0;
  perm = sindexsort(y1) + z; /* skip "zeroes" (excluded ideals) */
  for(;;)
  {
    if (++n > minsFB && (z+n >= lv || prod > m + 0.5)) break;
    prod *= gtodouble((GEN)y1[perm[n]]);
  }
  if (prod < m) return NULL;
  n--;

  /* take the first (non excluded) n ideals (wrt norm), put them first, and
   * sort the rest by increasing norm */
  for (j=1; j<=n; j++) y2[perm[j]] = zero;
  perm1 = sindexsort(y2); avma = av;

  subFB = cgetg(n+1, t_VECSMALL);
  if (vperm)
  {
    for (j=1; j<=n; j++) vperm[j] = perm[j];
    for (   ; j<lv; j++) vperm[j] = perm1[j];
  }
  for (j=1; j<=n; j++) subFB[j] = perm[j];

  if (DEBUGLEVEL)
  {
    if (DEBUGLEVEL>3)
    {
      fprintferr("\n***** IDEALS IN FACTORBASE *****\n\n");
      for (i=1; i<=KC; i++) fprintferr("no %ld = %Z\n",i,vectbase[i]);
      fprintferr("\n***** IDEALS IN SUB FACTORBASE *****\n\n");
      outerr(vecextract_p(vectbase,subFB));
      fprintferr("\n***** INITIAL PERMUTATION *****\n\n");
      fprintferr("vperm = %Z\n\n",vperm);
    }
    msgtimer("sub factorbase (%ld elements)",n);
  }
  powsubFB = NULL;
  *ptss = ss; return subFB;
}

static GEN
mulred(GEN nf,GEN x, GEN I, long prec)
{
  ulong av = avma;
  GEN y = cgetg(3,t_VEC);

  y[1] = (long)idealmulh(nf,I,(GEN)x[1]);
  y[2] = x[2];
  y = ideallllred(nf,y,NULL,prec);
  y[1] = (long)ideal_two_elt(nf,(GEN)y[1]);
  return gerepilecopy(av, y);
}

/* Compute powers of prime ideals (P^0,...,P^a) in subFB (a > 1)
 * powsubFB[j][i] contains P_i^j in LLL form + archimedean part in
 * MULTIPLICATIVE form (logs are expensive)
 */
static void
powsubFBgen(GEN nf,GEN subFB,long a,long prec)
{
  long i,j, n = lg(subFB), RU = lg(nf[6]);
  GEN *pow, arch0 = cgetg(RU,t_COL);
  for (i=1; i<RU; i++) arch0[i] = un; /* 0 in multiplicative notations */

  if (DEBUGLEVEL) fprintferr("Computing powers for sub-factor base:\n");
  powsubFB = cgetg(n, t_VEC);
  for (i=1; i<n; i++)
  {
    GEN vp = (GEN)vectbase[subFB[i]];
    GEN z = cgetg(3,t_VEC); z[1]=vp[1]; z[2]=vp[2];
    pow = (GEN*)cgetg(a+1,t_VEC); powsubFB[i] = (long)pow;
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

/* Compute FB, numFB, idealbase, vectbase, numideal.
 * n2: bound for norm of tested prime ideals (includes be_honest())
 * n : bound for prime ideals used to build relations (Bach cst) ( <= n2 )

 * Return prod_{p<=n2} (1-1/p) / prod_{Norm(P)<=n2} (1-1/Norm(P)),
 * close to residue of zeta_K at 1 = 2^r1 (2pi)^r2 h R / (w D)
 */
static GEN
FBgen(GEN nf,long n2,long n)
{
  byteptr delta=diffptr;
  long KC2,i,j,k,p,lon,ip,nor, N = degpol(nf[1]);
  GEN p2,p1,NormP,Res;
  long prim[] = { evaltyp(t_INT)|m_evallg(3), evalsigne(1)|evallgefint(3),0 };

  numFB    = cgetg(n2+1,t_VECSMALL);
  FB       = cgetg(n2+1,t_VECSMALL);
  numideal = cgetg(n2+1,t_VECSMALL);
  idealbase= (GEN*)cgetg(n2+1,t_VEC);

  Res=realun(DEFAULTPREC);
  p=*delta++; i=0; ip=0; KC=0;
  while (p<=n2)
  {
    long av = avma, av1;
    if (DEBUGLEVEL>=2) { fprintferr(" %ld",p); flusherr(); }
    prim[2] = p; p1 = primedec(nf,prim); lon=lg(p1);
    av1 = avma;
    divrsz(mulsr(p-1,Res),p,Res);
    if (itos(gmael(p1,1,4)) == N) /* p inert */
    {
      NormP = gpowgs(prim,N);
      if (!is_bigint(NormP) && (nor=NormP[2]) <= n2)
	divrsz(mulsr(nor,Res),nor-1, Res);
      avma = av1;
    }
    else
    {
      numideal[p]=ip;
      i++; numFB[p]=i; FB[i]=p;
      for (k=1; k<lon; k++,ip++)
      {
	NormP = powgi(prim,gmael(p1,k,4));
	if (is_bigint(NormP) || (nor=NormP[2]) > n2) break;

        divrsz(mulsr(nor,Res),nor-1, Res);
      }
      /* keep all ideals with Norm <= n2 */
      avma = av1;
      if (k == lon)
        setisclone(p1); /* flag it: all prime divisors in FB */
      else
        { setlg(p1,k); p1 = gerepilecopy(av,p1); }
      idealbase[i] = p1;
    }
    if (!*delta) err(primer1);
    p += *delta++;
    if (KC == 0 && p>n) { KCZ=i; KC=ip; }
  }
  if (!KC) return NULL;
  KCZ2=i; KC2=ip; MAXRELSUP = min(50,4*KC);

  setlg(FB,KCZ2);
  setlg(numFB,KCZ2);
  setlg(numideal,KCZ2);
  setlg(idealbase,KCZ2);
  vectbase=cgetg(KC+1,t_COL);
  for (i=1; i<=KCZ; i++)
  {
    p1 = idealbase[i]; k=lg(p1);
    p2 = vectbase + numideal[FB[i]];
    for (j=1; j<k; j++) p2[j]=p1[j];
  }
  if (DEBUGLEVEL)
  {
    if (DEBUGLEVEL>1) fprintferr("\n");
    if (DEBUGLEVEL>6)
    {
      fprintferr("########## FACTORBASE ##########\n\n");
      fprintferr("KC2=%ld, KC=%ld, KCZ=%ld, KCZ2=%ld, MAXRELSUP=%ld\n",
                  KC2, KC, KCZ, KCZ2, MAXRELSUP);
      for (i=1; i<=KCZ; i++)
	fprintferr("++ idealbase[%ld] = %Z",i,idealbase[i]);
    }
    msgtimer("factor base");
  }
  return Res;
}

/* can we factor I / m ? (m pseudo minimum, computed in ideallllredpart1) */
static long
factorgen(GEN nf,GEN idealvec,long kcz,long limp)
{
  long i,j,n1,ip,v,p,k,lo,ifinal;
  GEN x,q,r,P,p1,listexpo;
  GEN I = (GEN)idealvec[1];
  GEN m = (GEN)idealvec[2];
  GEN Nm= absi( subres(gmul((GEN)nf[7],m), (GEN)nf[1]) ); /* |Nm| */

  x = divii(Nm, dethnf_i(I)); /* m in I, so NI | Nm */
  if (is_pm1(x)) { primfact[0]=0; return 1; }
  listexpo = new_chunk(kcz+1);
  for (i=1; ; i++)
  {
    p=FB[i]; q=dvmdis(x,p,&r);
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
      p = FB[i]; p1 = idealbase[numFB[p]];
      n1 = lg(p1); ip = numideal[p];
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

  p = itos(x); p1 = idealbase[numFB[p]];
  n1 = lg(p1); ip = numideal[p];
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
factorelt(GEN nf,GEN cbase,GEN x,GEN Nx,long kcz,long limp)
{
  long i,j,n1,ip,v,p,k,lo,ifinal;
  GEN q,r,P,p1,listexpo;

  if (is_pm1(Nx)) { primfact[0]=0; return 1; }
  listexpo = new_chunk(kcz+1);
  for (i=1; ; i++)
  {
    p=FB[i]; q=dvmdis(Nx,p,&r);
    for (k=0; !signe(r); k++) { Nx=q; q=dvmdis(Nx,p,&r); }
    listexpo[i] = k;
    if (cmpis(q,p)<=0) break;
    if (i==kcz) return 0;
  }
  if (cmpis(Nx,limp) > 0) return 0;

  if (cbase) x = gmul(cbase,x);
  ifinal=i; lo = 0;
  for (i=1; i<=ifinal; i++)
  {
    k = listexpo[i];
    if (k)
    {
      p = FB[i]; p1 = idealbase[numFB[p]];
      n1 = lg(p1); ip = numideal[p];
      for (j=1; j<n1; j++)
      {
        P = (GEN)p1[j];
	v = int_elt_val(nf,x,(GEN)P[1],(GEN)P[5], NULL, k);
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

  p = itos(Nx); p1 = idealbase[numFB[p]];
  n1 = lg(p1); ip = numideal[p];
  for (k=1,j=1; j<n1; j++)
  {
    P = (GEN)p1[j];
    v = int_elt_val(nf,x,(GEN)P[1],(GEN)P[5], NULL, k);
    if (v)
    {
      primfact[++lo]=ip+j; expoprimfact[lo]=v;
      k -= v*itos((GEN)P[4]);
      if (!k) { primfact[0]=lo; return 1; }
    }
  }
  return 0;
}

static GEN
cleancol(GEN x,long N,long PRECREG)
{
  long i,j,av,tetpil,tx=typ(x),R1,RU;
  GEN s,s2,re,pi4,im,y;

  if (tx==t_MAT)
  {
    y=cgetg(lg(x),tx);
    for (j=1; j<lg(x); j++)
      y[j]=(long)cleancol((GEN)x[j],N,PRECREG);
    return y;
  }
  if (!is_vec_t(tx)) err(talker,"not a vector/matrix in cleancol");
  av = avma; RU=lg(x)-1; R1 = (RU<<1)-N;
  re = greal(x); s=(GEN)re[1]; for (i=2; i<=RU; i++) s=gadd(s,(GEN)re[i]);
  im = gimag(x); s = gdivgs(s,-N);
  s2 = (N>R1)? gmul2n(s,1): NULL;
  pi4=gmul2n(mppi(PRECREG),2);
  tetpil=avma; y=cgetg(RU+1,tx);
  for (i=1; i<=RU; i++)
  {
    GEN p1=cgetg(3,t_COMPLEX); y[i]=(long)p1;
    p1[1] = ladd((GEN)re[i], (i<=R1)?s:s2);
    p1[2] = lmod((GEN)im[i], pi4);
  }
  return gerepile(av,tetpil,y);
}

#define RELAT 0
#define LARGE 1
#define PRECI 2
static GEN
not_given(long av, long flun, long reason)
{
  if (labs(flun)==2)
  {
    char *s;
    switch(reason)
    {
      case RELAT: s = "not enough relations for fundamental units"; break;
      case LARGE: s = "fundamental units too large"; break;
      case PRECI: s = "insufficient precision for fundamental units"; break;
      default: s = "unknown problem with fundamental units";
    }
    err(warner,"%s, not given",s);
  }
  avma=av; return cgetg(1,t_MAT);
}

/* check whether exp(x) will get too big */
static long
expgexpo(GEN x)
{
  long i,j,e, E = -HIGHEXPOBIT;
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
getfu(GEN nf,GEN *ptxarch,GEN reg,long flun,long *pte,long prec)
{
  long av = avma,e,i,j,R1,RU,N=degpol(nf[1]);
  GEN p1,p2,u,y,matep,s,xarch,vec;
  GEN *gptr[2];

  if (DEBUGLEVEL) fprintferr("\n#### Computing fundamental units\n");
  R1 = itos(gmael(nf,2,1)); RU = (N+R1)>>1;
  if (RU==1) { *pte=BIGINT; return cgetg(1,t_VEC); }

  *pte = 0; xarch = *ptxarch;
  if (gexpo(reg) < -8) return not_given(av,flun,RELAT);

  matep = cgetg(RU,t_MAT);
  for (j=1; j<RU; j++)
  {
    s = gzero; for (i=1; i<=RU; i++) s = gadd(s,greal(gcoeff(xarch,i,j)));
    s = gdivgs(s, -N);
    p1=cgetg(RU+1,t_COL); matep[j]=(long)p1;
    for (i=1; i<=R1; i++) p1[i] = ladd(s, gcoeff(xarch,i,j));
    for (   ; i<=RU; i++) p1[i] = ladd(s, gmul2n(gcoeff(xarch,i,j),-1));
  }
  if (prec <= 0) prec = gprecision(xarch);
  u = lllintern(greal(matep),1,prec);
  if (!u) return not_given(av,flun,PRECI);

  p1 = gmul(matep,u);
  if (expgexpo(p1) > 20) { *pte = BIGINT; return not_given(av,flun,LARGE); }
  matep = gexp(p1,prec);
  y = grndtoi(gauss_realimag(nf,matep), &e);
  *pte = -e;
  if (e>=0) return not_given(av,flun,PRECI);
  for (j=1; j<RU; j++)
    if (!gcmp1(idealnorm(nf, (GEN)y[j]))) break;
  if (j < RU) { *pte = 0; return not_given(av,flun,PRECI); }
  xarch = gmul(xarch,u);

  /* y[i] are unit generators. Normalize: smallest L2 norm + lead coeff > 0 */
  y = gmul((GEN)nf[7], y);
  vec = cgetg(RU+1,t_COL); p2 = mppi(prec);
  p1 = pureimag(p2);
  p2 = pureimag(gmul2n(p2,1));
  for (i=1; i<=R1; i++) vec[i]=(long)p1;
  for (   ; i<=RU; i++) vec[i]=(long)p2;
  for (j=1; j<RU; j++)
  {
    p1 = (GEN)y[j]; p2 = QX_invmod(p1, (GEN)nf[1]);
    if (gcmp(QuickNormL2(p2,DEFAULTPREC),
             QuickNormL2(p1,DEFAULTPREC)) < 0)
    {
      xarch[j] = lneg((GEN)xarch[j]);
      p1 = p2;
    }
    if (gsigne(leading_term(p1)) < 0)
    {
      xarch[j] = ladd((GEN)xarch[j], vec);
      p1 = gneg(p1);
    }
    y[j] = (long)p1;
  }
  if (DEBUGLEVEL) msgtimer("getfu");
  *ptxarch=xarch; gptr[0]=ptxarch; gptr[1]=&y;
  gerepilemany(av,gptr,2); return y;
}

GEN
buchfu(GEN bnf)
{
  long av = avma, c;
  GEN nf,xarch,reg,res, y = cgetg(3,t_VEC);

  bnf = checkbnf(bnf); xarch = (GEN)bnf[3]; nf = (GEN)bnf[7];
  res = (GEN)bnf[8]; reg = (GEN)res[2];
  if (lg(res)==7 && lg(res[5])==lg(nf[6])-1)
  {
    y[1] = lcopy((GEN)res[5]);
    y[2] = lcopy((GEN)res[6]); return y;
  }
  y[1] = (long)getfu(nf,&xarch,reg,2,&c,0);
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
factorgensimple(GEN nf,GEN ideal)
{
  long N,i,v,av1 = avma,lo, L = lg(vectbase);
  GEN x;
  if (typ(ideal) != t_MAT) ideal = (GEN)ideal[1]; /* idele */
  x = dethnf_i(ideal);
  N = lg(ideal)-1;
  if (gcmp1(x)) { avma=av1; primfact[0]=0; return 1; }
  for (lo=0, i=1; i<L; i++)
  {
    GEN q,y, P=(GEN)vectbase[i], p=(GEN)P[1];
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
      P = (GEN)vectbase[i]; q = (GEN)P[1];
      if (!egalii(p,q)) break;
    }
    if (vx)
    { /* divisible by P | p not in FB */
      long k,l,n;
      k = N - sum_ef;
      if (vx % k) break;
      k = vx / k; /* ideal / p^k may factor on FB */
      for (l = lo0+1; l <= lo; l++)
      {
        P = (GEN)vectbase[primfact[l]];
        expoprimfact[l] -= k * itos((GEN)P[3]); /* may become 0 */
      }
      n = lo0+1;
      for (l = i0; l < i; l++) /* update exponents for other P | p */
      {
        if (n <= lo && primfact[n] == l) { n++; continue; }
        lo++; primfact[lo] = l; P = (GEN)vectbase[l];
        expoprimfact[lo] = - k * itos((GEN)P[3]);
      }
      /* check that ideal / p^k / (tentative factorisation) is integral */
      {
        GEN z = ideal;
        for (l = lo0+1; l <= lo; l++)
        {
          GEN n = stoi(- expoprimfact[l]);
          z = idealmulpowprime(nf, z, (GEN)vectbase[primfact[l]], n);
        }
        z = gdiv(z, gpowgs(p, k));
        if (!gcmp1(denom(z))) { avma=av1; return 0; }
        ideal = z;
      }
    }
    if (gcmp1(y)) { avma=av1; primfact[0]=lo; return 1; }
    x = y;
  }
  avma=av1; return 0;
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
    primfact[lo] = v;
    expoprimfact[lo] = e;
  }
}

static void
init_sub(long l, GEN perm, GEN *v, GEN *ex)
{
  long i;
  *v = cgetg(l,t_VECSMALL);
  *ex= cgetg(l,t_VECSMALL);
  for (i=1; i<l; i++) (*v)[i] = itos((GEN)perm[i]);
}

/* factor x = x0[1] on vectbase (modulo principal ideals).
 * We may have x0[2] = NULL (principal part not wanted), in which case,
 * don't compute archimedean parts */
static GEN
split_ideal(GEN nf, GEN x0, long prec, GEN vperm)
{
  GEN p1,vdir,id,z,v,ex,y, x = (GEN)x0[1];
  long nbtest_lim,nbtest,bou,i,ru, lgsub;
  int flag = (gexpo(gcoeff(x,1,1)) < 100);

  y = x0;
  if (flag && factorgensimple(nf,y)) return y;

  y = ideallllred(nf,x0,NULL,prec);
  if (flag &&  ((!x0[2] && gegal((GEN)y[1], (GEN)x[1]))
             ||  (x0[2] && gcmp0((GEN)y[2])))) flag = 0; /* y == x0 */
  if (flag && factorgensimple(nf,y)) return y;

  z = init_idele(nf); ru = lg(z[2]);
  if (!x0[2]) { z[2] = 0; x0 = x; } /* stop cheating */
  vdir = cgetg(ru,t_VEC);
  for (i=2; i<ru; i++) vdir[i]=zero;
  for (i=1; i<ru; i++)
  {
    vdir[i]=lstoi(10);
    y = ideallllred(nf,x0,vdir,prec);
    if (factorgensimple(nf,y)) return y;
    vdir[i]=zero;
  }
  nbtest = 0; nbtest_lim = (ru-1) << 2; lgsub = 3;
  init_sub(lgsub, vperm, &v, &ex);
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
        z[1]=vectbase[v[i]]; p1=idealpowred(nf,z,stoi(ex[i]),prec);
        id = idealmulh(nf,id,p1);
      }
    }
    if (id == x0) continue;

    for (i=1; i<ru; i++) vdir[i] = lstoi(mymyrand() >> randshift);
    for (bou=1; bou<ru; bou++)
    {
      if (bou>1)
      {
        for (i=1; i<ru; i++) vdir[i]=zero;
        vdir[bou]=lstoi(10);
      }
      nbtest++;
      y = ideallllred(nf,id,vdir,prec);
      if (DEBUGLEVEL>2)
        fprintferr("nbtest = %ld, ideal = %Z\n",nbtest,y[1]);
      if (factorgensimple(nf,y))
      {
        long l = primfact[0];
        for (i=1; i<lgsub; i++) add_to_fact(l,v[i],-ex[i]);
        return y;
      }
    }
    if (nbtest > nbtest_lim)
    {
      nbtest = 0;
      if (lgsub < 7)
      {
        lgsub++; nbtest_lim <<= 2;
        init_sub(lgsub, vperm, &v, &ex);
      }
      else nbtest_lim = VERYBIGINT; /* don't increase further */
      if (DEBUGLEVEL)
        fprintferr("split_ideal: increasing factor base [%ld]\n",lgsub);
    }
  }
}

static void
get_split_expo(GEN xalpha, GEN yalpha, GEN vperm)
{
  long i, colW = lg(xalpha)-1;
  GEN vinvperm = new_chunk(lg(vectbase));
  for (i=1; i<lg(vectbase); i++) vinvperm[itos((GEN)vperm[i])]=i;
  for (i=1; i<=primfact[0]; i++)
  {
    long k = vinvperm[primfact[i]];
    long l = k - colW;
    if (l <= 0) xalpha[k]=lstoi(expoprimfact[i]);
    else        yalpha[l]=lstoi(expoprimfact[i]);
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
  x = lllintern(concatsp(mat,x), 1,prec);
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
  GEN z, a;
  long i,l = lg(A);
  if (typ(A) == t_MAT)
  {
    /* assume lg(x) >= l */
    z = cgetg(l, t_VEC);
    for (i=1; i<l; i++) z[i] = (long)act_arch((GEN)A[i], x);
    return z;
  }
  /* A a t_COL of t_INT. Assume lg(A)==lg(x) */
  l = lg(A); z = cgetg(l, t_VEC);
  if (l==1) return z;
  a = gmul((GEN)A[1], (GEN)x[1]);
  for (i=2; i<l; i++)
    if (signe(A[i])) a = gadd(a, gmul((GEN)A[i], (GEN)x[i]));
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
  col = cleancol(col,N,prec); settyp(col, t_COL);
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
  long i, c = lg(e);
  GEN z = C? C: gun;
  for (i=1; i<c; i++)
    if (signe(e[i])) z = idealmul(nf, z, idealpow(nf, (GEN)g[i], (GEN)e[i]));
  if (typ(z) != t_MAT) z = idealhermite(nf,z);
  if (typ(y) != t_MAT) y = idealhermite(nf,y);
  return gegal(y, z);
}

/* assume x in HNF. cf class_group_gen for notations */
static GEN
isprincipalall0(GEN bnf, GEN x, long *ptprec, long flag)
{
  long i,lW,lB,e,c, prec = *ptprec;
  GEN Q,xar,Wex,Bex,U,y,p1,gen,cyc,xc,ex,d,col,A;
  GEN W       = (GEN)bnf[1];
  GEN B       = (GEN)bnf[2];
  GEN WB_C    = (GEN)bnf[4];
  GEN vperm   = (GEN)bnf[6];
  GEN nf      = (GEN)bnf[7];
  GEN clg2    = (GEN)bnf[9];
  int old_format = (typ(clg2[2]) == t_MAT);

  U = (GEN)clg2[1];
  cyc = gmael3(bnf,8,1,2); c = lg(cyc)-1;
  gen = gmael3(bnf,8,1,3);

  vectbase = (GEN)bnf[5]; /* needed by factorgensimple */

  /* factor x */
  xc = content(x); if (!gcmp1(xc)) x = gdiv(x,xc);

  p1 = init_idele(nf); p1[1] = (long)x;
  if (!(flag & nf_GEN)) p1[2] = 0; /* don't compute archimedean part */
  xar = split_ideal(nf,p1,prec,vperm);

  lW = lg(W)-1; Wex = zerocol(lW);
  lB = lg(B)-1; Bex = zerocol(lB); get_split_expo(Wex,Bex,vperm);

  /* x = g_W Wex + g_B Bex - [xar]
   *   = g_W A - [xar] + [C_B]Bex  since g_W B + g_B = [C_B] */
  A = gsub(Wex, gmul(B,Bex));
  if (old_format) U = ginv(U);
  Q = gmul(U, A);
  ex = cgetg(c+1,t_COL);
  for (i=1; i<=c; i++)
    Q[i] = (long)truedvmdii((GEN)Q[i],(GEN)cyc[i],(GEN*)(ex+i));
  if (!(flag & nf_GEN)) return gcopy(ex);

  /* compute arch component of the missing principal ideal */
  if (old_format)
  {
    GEN Garch, V = (GEN)clg2[2];
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
  col = gsub(col, (GEN)xar[2]);

  /* find coords on Zk; Q = N (x / \prod gj^ej) = N(alpha), denom(alpha) | d */
  Q = gdiv(dethnf_i(x), get_norm_fact(gen, ex, &d));
  col = isprincipalarch(bnf, col, Q, gun, d, &e);
  if (col && !fact_ok(nf,x, col,gen,ex)) col = NULL;
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
  y[1] = lcopy(ex);
  y[2] = e? lmul(xc,col): lgetg(1,t_COL);
  y[3] = lstoi(-e); return y;
}

static GEN
triv_gen(GEN nf, GEN x, long c, long flag)
{
  GEN y;
  if (!(flag & nf_GEN)) return zerocol(c);
  y = cgetg(4,t_VEC);
  y[1] = (long)zerocol(c);
  x = (typ(x) == t_COL)? gcopy(x): algtobasis(nf,x);
  y[2] = (long)x;
  y[3] = lstoi(BIGINT); return y;
}

GEN
isprincipalall(GEN bnf,GEN x,long flag)
{
  long av = avma,c,pr, tx = typ(x);
  GEN nf;

  bnf = checkbnf(bnf); nf = (GEN)bnf[7];
  if (tx == t_POLMOD)
  {
    if (!gegal((GEN)x[1],(GEN)nf[1]))
      err(talker,"not the same number field in isprincipal");
    x = (GEN)x[2]; tx = t_POL;
  }
  if (tx == t_POL || tx == t_COL)
  {
    if (gcmp0(x)) err(talker,"zero ideal in isprincipal");
    return triv_gen(nf, x, lg(mael3(bnf,8,1,2))-1, flag);
  }
  x = idealhermite(nf,x);
  if (lg(x)==1) err(talker,"zero ideal in isprincipal");
  if (lgef(nf[1])==4)
    return gerepileupto(av, triv_gen(nf, gcoeff(x,1,1), 0, flag));

  pr = prec_arch(bnf); /* precision of unit matrix */
  c = getrand();
  for (;;)
  {
    long av1 = avma;
    GEN y = isprincipalall0(bnf,x,&pr,flag);
    if (y) return gerepileupto(av,y);

    if (DEBUGLEVEL) err(warnprec,"isprincipalall0",pr);
    avma = av1; bnf = bnfnewprec(bnf,pr); setrand(c);
  }
}

/* isprincipal for C * \prod P[i]^e[i] (C omitted if NULL) */
GEN
isprincipalfact(GEN bnf,GEN P, GEN e, GEN C, long flag)
{
  long av = avma, l = lg(e), i,prec,c;
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
  if (id == C)
  {
    if (!C) id = gun;
    return isprincipalall(bnf, id, flag);
  }
  c = getrand();
  for (;;)
  {
    long av1 = avma;
    GEN y = isprincipalall0(bnf, gen? (GEN)id[1]: id,&prec,flag);
    if (y)
    {
      if (gen && typ(y) == t_VEC)
      {
        GEN u = lift_intern(basistoalg(nf, (GEN)y[2]));
        if (flag & nf_GENMAT)
          y[2] = (gcmp1(u)&&lg(id[2])>1)? id[2]: (long)arch_mul((GEN)id[2], u);
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
    if (DEBUGLEVEL) err(warnprec,"isprincipalall0",prec);
    avma = av1; bnf = bnfnewprec(bnf,prec); setrand(c);
  }
}

GEN
isprincipal(GEN bnf,GEN x)
{
  return isprincipalall(bnf,x,nf_REGULAR);
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

GEN
isunit(GEN bnf,GEN x)
{
  long av=avma,tetpil,tx = typ(x),i,R1,RU,n;
  GEN p1,logunit,y,ex,nf,z,pi2_sur_w,gn,emb;

  bnf = checkbnf(bnf); nf=(GEN)bnf[7];
  logunit=(GEN)bnf[3]; RU=lg(logunit);
  p1 = gmael(bnf,8,4); /* roots of 1 */
  gn = (GEN)p1[1]; n = itos(gn);
  z  = (GEN)p1[2];
  switch(tx)
  {
    case t_INT: case t_FRAC: case t_FRACN:
      if (!gcmp1(x) && !gcmp_1(x)) return cgetg(1,t_COL);
      y = zerocol(RU); i = (gsigne(x) > 0)? 0: n>>1;
      y[RU] = (long)gmodulss(i, n); return y;

    case t_POLMOD:
      if (!gegal((GEN)nf[1],(GEN)x[1]))
        err(talker,"not the same number field in isunit");
      x = (GEN)x[2]; /* fall through */
    case t_POL:
      p1 = x; x = algtobasis(bnf,x); break;

    case t_COL:
      if (lgef(nf[1])-2 == lg(x)) { p1 = basistoalg(nf,x); break; }

    default:
      err(talker,"not an algebraic number in isunit");
  }
  if (!gcmp1(denom(x))) { avma = av; return cgetg(1,t_COL); }
  if (typ(p1) != t_POLMOD) p1 = gmodulcp(p1,(GEN)nf[1]);
  p1 = gnorm(p1);
  if (!is_pm1(p1)) { avma = av; return cgetg(1,t_COL); }

  R1 = itos(gmael(nf,2,1)); p1 = cgetg(RU+1,t_COL);
  for (i=1; i<=R1; i++) p1[i] = un;
  for (   ; i<=RU; i++) p1[i] = deux;
  logunit = concatsp(logunit,p1);
  /* ex = fundamental units exponents */
  {
    GEN rx, rlog = greal(logunit);
    long e, prec = nfgetprec(nf);
    for (i=1;;)
    {
      rx = get_arch_real(nf,x,&emb, MEDDEFAULTPREC);
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
  }

  setlg(ex, RU);
  setlg(p1, RU); settyp(p1, t_VEC);
  for (i=1; i<RU; i++) p1[i] = coeff(logunit, 1, i);
  p1 = gneg(gimag(gmul(p1,ex))); if (!R1) p1 = gmul2n(p1, -1);
  p1 = gadd(garg((GEN)emb[1],DEFAULTPREC), p1);
  /* p1 = arg(the missing root of 1) */

  pi2_sur_w = divrs(mppi(DEFAULTPREC), n>>1);
  p1 = ground(gdiv(p1, pi2_sur_w));
  if (n > 2)
  {
    GEN ro = gmael(nf,6,1);
    GEN p2 = ground(gdiv(garg(poleval(z,ro), DEFAULTPREC), pi2_sur_w));
    p1 = mulii(p1,  mpinvmod(p2, gn));
  }

  tetpil = avma; y = cgetg(RU+1,t_COL);
  for (i=1; i<RU; i++) y[i] = lcopy((GEN)ex[i]);
  y[RU] = lmodulcp(p1, gn); return gerepile(av,tetpil,y);
}

GEN
signunits(GEN bnf)
{
  long av,i,j,R1,RU,mun;
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

/* LLL-reduce ideal and return T2 | ideal */
static GEN
red_ideal(GEN *ideal,GEN T2vec,GEN prvec)
{
  long i;
  for (i=1; i<lg(T2vec); i++)
  {
    GEN p1,base, T2 = (GEN)T2vec[i];
    long prec = prvec[i];

    p1 = qf_base_change(T2, *ideal, 1);
    base = lllgramintern(p1,100,1,prec);
    if (base)
    {
      p1 = sqred1intern(qf_base_change(p1,base,1),1);
      if (p1) { *ideal = gmul(*ideal,base); return p1; }
    }
    if (DEBUGLEVEL) err(warner, "prec too low in red_ideal[%ld]: %ld",i,prec);
  }
  return NULL;
}

static double
get_minkovski(long N, long R1, GEN D, GEN gborne)
{
  const long prec = DEFAULTPREC;
  GEN p1,p2, pi = mppi(prec);
  double bound;

  p1 = gsqrt(gmulsg(N,gmul2n(pi,1)),prec);
  p1 = gdiv(p1, gexp(stoi(N),prec));
  p1 = gmulsg(N, gpui(p1, dbltor(2./(double)N),prec));
  p2 = gpui(gdivsg(4,pi), gdivgs(stoi(N-R1),N),prec);
  p1 = gmul(p1,p2);
  bound = gtodouble(gmul(p1, gpui(absi(D), dbltor(1./(double)N),prec)));
  bound *= gtodouble(gborne);
  if (DEBUGLEVEL) { fprintferr("Bound for norms = %.0f\n",bound); flusherr(); }
  return bound;
}

static void
wr_rel(long *col)
{
  long i;
  fprintferr("\nrel = ");
  for (i=1; i<=KC; i++)
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
set_fact(GEN c)
{
  long i;
  c[0] = primfact[1]; /* for already_found_relation */
  for (i=1; i<=primfact[0]; i++) c[primfact[i]] = expoprimfact[i];
}

static void
unset_fact(GEN c)
{
  long i;
  for (i=1; i<=primfact[0]; i++) c[primfact[i]] = 0;
}

#define MAXTRY 20

/* return -1 in case of precision problems. t = current number of relations */
static long
small_norm_for_buchall(long cglob,GEN *mat,GEN matarch,long LIMC, long PRECREG,
                       GEN nf,GEN gborne,long nbrelpid,GEN invp,GEN L,GEN LLLnf)
{
  const double eps = 0.000001;
  double *y,*z,**q,*v, MINKOVSKI_BOUND,BOUND;
  ulong av = avma, av1,av2,limpile;
  long i,j,k,noideal, nbrel = lg(mat)-1;
  long alldep = 0, nbsmallnorm,nbfact,R1, N = degpol(nf[1]);
  GEN x,xembed,M,T2,r,cbase,invcbase,T2vec,prvec;

  if (gsigne(gborne)<=0) return cglob;
  if (DEBUGLEVEL)
    fprintferr("\n#### Looking for %ld relations (small norms)\n",nbrel);
  xembed = NULL; /* gcc -Wall */
  nbsmallnorm = nbfact = 0;
  R1 = itos(gmael(nf,2,1));
  T2 = (GEN)LLLnf[1];
  M  = (GEN)LLLnf[2];
  cbase   =(GEN)LLLnf[3];
  invcbase=(GEN)LLLnf[4];

  prvec = cgetg(3,t_VECSMALL);
  prvec[1] = MEDDEFAULTPREC;
  prvec[2] = PRECREG;
  T2vec = cgetg(3,t_VEC);
  T2vec[1] = (long)gprec_w(T2,prvec[1]);
  T2vec[2] = (long)T2;
  minim_alloc(N+1, &q, &x, &y, &z, &v);
  av1 = avma;
  MINKOVSKI_BOUND = get_minkovski(N,R1,(GEN)nf[3],gborne);
  for (noideal=KC; noideal; noideal--)
  {
    long nbrelideal=0, dependent = 0;
    GEN IDEAL, ideal = (GEN)vectbase[noideal];
    GEN normideal = idealnorm(nf,ideal);

    if (alldep > 2*N) break;

    if (DEBUGLEVEL>1) fprintferr("\n*** Ideal no %ld: %Z\n", noideal, ideal);
    ideal = prime_to_ideal(nf,ideal);
    IDEAL = invcbase? gmul(invcbase, ideal): ideal;
    IDEAL = gmul(IDEAL, lllint(IDEAL)); /* should be almost T2-reduced */
    r = red_ideal(&IDEAL,T2vec,prvec);
    if (!r) return -1; /* precision problem */

    for (k=1; k<=N; k++)
    {
      v[k]=gtodouble(gcoeff(r,k,k));
      for (j=1; j<k; j++) q[j][k]=gtodouble(gcoeff(r,j,k));
      if (DEBUGLEVEL>3) fprintferr("v[%ld]=%.0f ",k,v[k]);
    }

    BOUND = MINKOVSKI_BOUND * pow(gtodouble(normideal),2./(double)N);
    if (DEBUGLEVEL>1)
    {
      if (DEBUGLEVEL>3) fprintferr("\n");
      fprintferr("BOUND = %.0f\n",BOUND); flusherr();
    }
    BOUND += eps; av2=avma; limpile = stack_lim(av2,1);
    k = N; y[N]=z[N]=0; x[N]= (long) sqrt(BOUND/v[N]);
    for(;; x[1]--)
    {
      ulong av3 = avma;
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
	  if (!x[1] && y[1]<=eps) goto ENDIDEAL;
	  if (ccontent(x)==1) /* primitive */
	  {
            GEN Nx, gx = gmul_mati_smallvec(IDEAL,x);
            long av4;
            if (!isnfscalar(gx))
            {
              xembed = gmul(M,gx); av4 = avma; nbsmallnorm++;
              Nx = ground(norm_by_embed(R1,xembed)); setsigne(Nx, 1);
              if (factorelt(nf,cbase,gx,Nx,KCZ,LIMC)) { avma = av4; break; }
              if (DEBUGLEVEL > 1) { fprintferr("."); flusherr(); }
            }
	    avma = av3;
	  }
	  x[1]--;
	}
      }
      cglob++; col = mat[cglob];
      set_fact(col);
      if (cglob > 1 && cglob <= KC && ! addcolumntomatrix(col,invp,L))
      { /* Q-dependent from previous ones: forget it */
        cglob--; unset_fact(col);
        if (DEBUGLEVEL>1) { fprintferr("*"); flusherr(); }
        if (++dependent > MAXTRY) { alldep++; break; }
        avma = av3; continue;
      }
      /* record archimedean part */
      set_log_embed((GEN)matarch[cglob], xembed, R1, PRECREG);
      alldep = dependent = 0;

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
    invp = gerepilecopy(av1, invp);
    if (DEBUGLEVEL>1) msgtimer("for this ideal");
  }
END:
  if (DEBUGLEVEL)
  {
    fprintferr("\n");
    msgtimer("small norm relations");
    if (DEBUGLEVEL>1)
    {
      GEN p1,tmp=cgetg(cglob+1,t_MAT);

      fprintferr("Elements of small norm gave %ld relations.\n",cglob);
      fprintferr("Computing rank: "); flusherr();
      for(j=1;j<=cglob;j++)
      {
	p1=cgetg(KC+1,t_COL); tmp[j]=(long)p1;
	for(i=1;i<=KC;i++) p1[i]=lstoi(mat[j][i]);
      }
      tmp = (GEN)sindexrank(tmp)[2]; k=lg(tmp)-1;
      fprintferr("%ld; independent columns: %Z\n",k,tmp);
    }
    if(nbsmallnorm)
      fprintferr("\nnb. fact./nb. small norm = %ld/%ld = %.3f\n",
                  nbfact,nbsmallnorm,((double)nbfact)/nbsmallnorm);
    else
      fprintferr("\nnb. small norm = 0\n");
  }
  avma = av; return cglob;
}
#undef MAXTRY

/* I assumed to be integral HNF, T2 a weighted T2 matrix */
static GEN
ideallllredpart1(GEN I, GEN T2, long prec)
{
  GEN y,m,idealpro;

  y = lllgramintern(qf_base_change(T2,I,1),100,1,prec+1);
  if (!y) return NULL;

  /* I, m, y integral */
  m = gmul(I,(GEN)y[1]);
  if (isnfscalar(m)) m = gmul(I,(GEN)y[2]);

  idealpro = cgetg(3,t_VEC);
  idealpro[1] = (long)I;
  idealpro[2] = (long)m; /* irrational element of small T2 norm in I */
  if (DEBUGLEVEL>5) fprintferr("\nidealpro = %Z\n",idealpro);
  return idealpro;
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
  fprintferr("rel. cancelled. phase %ld: %ld ",phase);
  if (DEBUGLEVEL>3) fprintferr("(jideal=%ld,jdir=%ld)",jideal,jdir);
  wr_rel(col); flusherr();
}

static void
dbg_outrel(long phase,long cglob, GEN vperm,GEN *mat,GEN maarch)
{
  long i,j;
  GEN p1,p2;

  if (phase == 0)
  {
    ulong av = avma; p2=cgetg(cglob+1,t_MAT);
    for (j=1; j<=cglob; j++)
    {
      p1=cgetg(KC+1,t_COL); p2[j]=(long)p1;
      for (i=1; i<=KC; i++) p1[i]=lstoi(mat[j][i]);
    }
    fprintferr("\nRank = %ld\n", rank(p2));
    if (DEBUGLEVEL>3)
    {
      fprintferr("relations = \n");
      for (j=1; j <= cglob; j++) wr_rel(mat[j]);
      fprintferr("\nmatarch = %Z\n",maarch);
    }
    avma = av;
  }
  else if (DEBUGLEVEL>6)
  {
    fprintferr("before hnfadd:\nvectbase[vperm[]] = \n");
    fprintferr("[");
    for (i=1; i<=KC; i++)
    {
      bruterr((GEN)vectbase[vperm[i]],'g',-1);
      if (i<KC) fprintferr(",");
    }
    fprintferr("]~\n");
  }
  flusherr();
}

/* Check if we already have a column mat[l] equal to mat[s]
 * General check for colinearity useless since exceedingly rare */
static long
already_found_relation(GEN *mat,long s)
{
  GEN coll, cols = mat[s];
  long l,bs;

  bs = 1; while (bs<=KC && !cols[bs]) bs++;
  if (bs > KC) return s; /* zero relation */

  for (l=s-1; l; l--)
  {
    coll = mat[l];
    if (bs == coll[0]) /* = index of first non zero elt in coll */
    {
      long b = bs;
      do b++; while (b<=KC && cols[b] == coll[b]);
      if (b > KC) return l;
    }
  }
  cols[0] = bs; return 0;
}

/* I integral ideal in HNF form */
static GEN
remove_content(GEN I)
{
  long N = lg(I)-1;
  if (!gcmp1(gcoeff(I,N,N))) { GEN y=content(I); if (!gcmp1(y)) I=gdiv(I,y); }
  return I;
}

/* if phase != 1 re-initialize static variables. If <0 return immediately */
static long
random_relation(long phase,long cglob,long LIMC,long PRECLLL,long PRECREG,
                GEN nf,GEN subFB,GEN vecT2,GEN *mat,GEN matarch,GEN list_jideal)
{
  static long jideal, jdir;
  long lim,i,av,av1,cptzer,nbT2,lgsub,r1, jlist = 1;
  GEN arch,col,colarch,ideal,idealpro,P,ex;

  if (phase != 1) { jideal=jdir=1; if (phase<0) return 0; }

  r1 = nf_get_r1(nf);
  lim = lg(mat)-1; /* requested number of relations */
  nbT2 = lg(vecT2)-1;
  lgsub = lg(subFB); ex = cgetg(lgsub, t_VECSMALL);
  cptzer = 0;
  if (DEBUGLEVEL && list_jideal)
    fprintferr("looking hard for %Z\n",list_jideal);
  P = NULL; /* gcc -Wall */
  for (av = avma;;)
  {
    if (list_jideal && jlist < lg(list_jideal) && jdir <= nbT2)
      jideal = list_jideal[jlist++];
    if (!list_jideal || jdir <= nbT2)
    {
      avma = av;
      P = prime_to_ideal(nf, (GEN)vectbase[jideal]);
    }
    ideal = P;
    do {
      for (i=1; i<lgsub; i++)
      {
        ex[i] = mymyrand()>>randshift;
        if (ex[i]) ideal = idealmulh(nf,ideal, gmael3(powsubFB,i,ex[i],1));
      }
    }
    while (ideal == P); /* If ex  = 0, try another */
    ideal = remove_content(ideal);

    if (phase != 1) jdir = 1; else phase = 2;
    for (av1 = avma; jdir <= nbT2; jdir++, avma = av1)
    { /* reduce along various directions */
      if (DEBUGLEVEL>2)
        fprintferr("phase=%ld,jideal=%ld,jdir=%ld,rand=%ld\n",
                   phase,jideal,jdir,getrand());
      idealpro = ideallllredpart1(ideal,(GEN)vecT2[jdir],PRECLLL);
      if (!idealpro) return -2;
      if (!factorgen(nf,idealpro,KCZ,LIMC))
      {
        if (DEBUGLEVEL>1) { fprintferr("."); flusherr(); }
        continue;
      }
      /* can factor ideal, record relation */
      cglob++; col = mat[cglob];
      set_fact(col); col[jideal]--;
      for (i=1; i<lgsub; i++) col[subFB[i]] -= ex[i];
      if (already_found_relation(mat, cglob))
      { /* Already known: forget it */
        if (DEBUGLEVEL>1) dbg_cancelrel(jideal,jdir,phase,col);
        cglob--; unset_fact(col); col[jideal] = 0;
        for (i=1; i<lgsub; i++) col[subFB[i]] = 0;

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
          GEN p1 = gmael3(powsubFB,i,ex[i],2);
          arch = arch? vecmul(arch, p1): p1;
        }
      colarch = (GEN)matarch[cglob];
      /* arch = archimedean component (MULTIPLICATIVE form) of ideal */
      arch = vecdiv(arch, gmul(gmael(nf,5,1), (GEN)idealpro[2]));
      set_log_embed(colarch, arch, r1, PRECREG);
      if (DEBUGLEVEL) dbg_newrel(jideal,jdir,phase,cglob,col,colarch,lim);

      /* Need more, try next P */
      if (cglob < lim) break;

      /* We have found enough. Return */
      if (phase)
      {
        jdir = 1;
        if (jideal == KC) jideal=1; else jideal++;
      }
      if (DEBUGLEVEL>2)
        fprintferr("Upon exit: jideal=%ld,jdir=%ld\n",jideal,jdir);
      avma = av; return cglob;
    }
    if (!list_jideal)
    {
      if (jideal == KC) jideal=1; else jideal++;
    }
  }
}

static long
be_honest(GEN nf,GEN subFB,long PRECLLL)
{
  ulong av;
  GEN MC = gmael(nf,5,2), M = gmael(nf,5,1), D = (GEN)nf[3];
  long ex,i,j,J,k,iz,nbtest, lgsub = lg(subFB), ru = lg(MC);
  GEN P,ideal,idealpro, exu = cgetg(ru, t_VECSMALL), MCtw= cgetg(ru, t_MAT);

  if (DEBUGLEVEL)
  {
    fprintferr("Be honest for primes from %ld to %ld\n", FB[KCZ+1],FB[KCZ2]);
    flusherr();
  }
  av = avma;
  for (iz=KCZ+1; iz<=KCZ2; iz++, avma = av)
  {
    if (DEBUGLEVEL>1) fprintferr("%ld ", FB[iz]);
    P = idealbase[numFB[FB[iz]]]; J = lg(P);
    /* if unramified, check all but 1 */
    if (J > 1 && !divise(D, gmael(P,1,1))) J--;
    for (j=1; j<J; j++)
    {
      GEN ideal0 = prime_to_ideal(nf,(GEN)P[j]);
      ulong av2 = avma;
      for(nbtest=0;;)
      {
	ideal = ideal0;
	for (i=1; i<lgsub; i++)
	{
	  ex = mymyrand()>>randshift;
	  if (ex) ideal = idealmulh(nf,ideal,gmael3(powsubFB,i,ex,1));
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
          for (i=1; i<ru; i++)
            MCtw[i] = exu[i]? lmul2n((GEN)MC[i],exu[i]<<1): MC[i];
          idealpro = ideallllredpart1(ideal, mulmat_real(MCtw,M), PRECLLL);
          if (idealpro && factorgen(nf,idealpro,iz-1,FB[iz-1])) break;
	  nbtest++; if (nbtest==200) return 0;
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

/* xarch = complex logarithmic embeddings of units (u_j) found so far */
static GEN
compute_multiple_of_R(GEN xarch,long RU,long N,GEN *ptlambda)
{
  GEN T,v,mdet,mdet_t,Im_mdet,kR,xreal,lambda, *gptr[2];
  long av = avma, i, zc = lg(xarch)-1, R1 = 2*RU - N;

  if (DEBUGLEVEL) fprintferr("\n#### Computing regulator multiple\n");
  xreal = greal(xarch); /* = (log |sigma_i(u_j)|) */
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
  gptr[0]=&lambda; gptr[1]=&kR; gerepilemany(av,gptr,2); 
  *ptlambda = lambda; return kR;
}

extern GEN hnflll_i(GEN A, GEN *ptB, int remove);

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

/* c = Rz = 2n, according to Dirichlet's formula. Compute a tentative
 * regulator (not a multiple this time). *ptkR = multiple of regulator */
static int
compute_R(GEN lambda, GEN z, GEN *ptU, GEN *ptkR)
{
  ulong av = avma;
  long r;
  GEN U,L,H,gc,den,R;
  double c;

  if (DEBUGLEVEL) { fprintferr("\n#### Computing check\n"); flusherr(); }
  gc = gmul(*ptkR,z);
  lambda = bestappr_noer(lambda,gc);
  if (!lambda)
  {
    if (DEBUGLEVEL) fprintferr("truncation error in bestappr\n");
    return PRECI;
  }
  den = denom(lambda);
  if (gcmp(den,gc) > 0)
  {
    if (DEBUGLEVEL) fprintferr("c = %Z\nden = %Z\n",gc,den);
    return PRECI;
  }
  L = gmul(lambda,den);
  H = hnf(L); r = lg(H)-1;
  R = gdiv(dethnf_i(H), gpowgs(den, r));
  R = mpabs(gmul(*ptkR,R)); /* tentative regulator */
  c = gtodouble(gmul(R,z)); /* should be 2n (= 2 if we are done) */
  if (DEBUGLEVEL)
  {
    msgtimer("bestappr/regulator");
    fprintferr("\n ***** check = %f\n",c/2);
  }
  if (c < 1.5) return PRECI;
  if (c > 3.) { avma = av; return RELAT; }
  /* *pU = coords. of fundamental units on sublambda */
  H = hnflll_i(L,&U,0); /* try hard to get a SMALL base change */
  U += (lg(U)-1 - r); U[0] = evaltyp(t_MAT)|evallg(r+1);
  *ptkR = R; *ptU = U; return LARGE;
}

/* find the smallest (wrt norm) among I, I^-1 and red(I^-1) */
static GEN
inverse_if_smaller(GEN nf, GEN I, long prec)
{
  GEN J, d, dmin, I1;
  int inv;
  J = (GEN)I[1];
  dmin = dethnf_i(J); I1 = idealinv(nf,I);
  J = (GEN)I1[1]; J = gmul(J,denom(J)); I1[1] = (long)J;
  d = dethnf_i(J);
  if (cmpii(d,dmin) < 0) {inv=1; I=I1; dmin=d;}
  else                    inv=0;
  /* try reducing (often _increases_ the norm) */
  I1 = ideallllred(nf,I1,NULL,prec);
  J = (GEN)I1[1];
  d = dethnf_i(J);
  if (cmpii(d,dmin) < 0) {inv=1; I=I1;}
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
class_group_gen(GEN nf,GEN W,GEN C,GEN vperm,GEN *ptclg1,GEN *ptclg2,long prec)
{
  GEN z,G,Ga,ga,GD,cyc,X,Y,D,U,V,Ur,Ui,Uir,I,J,Vbase;
  long i,j,s,lo,lo0;

  if (DEBUGLEVEL)
    { fprintferr("\n#### Computing class group generators\n"); timer2(); }
  z = smith2(W); /* U W V = D, D diagonal, G = g Ui (G=new gens, g=old)  */
  U = (GEN)z[1]; Ui = ginv(U);
  V = (GEN)z[2];
  D = (GEN)z[3];
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
  Vbase = cgetg(lo0,t_VEC);
  if (typ(vperm) == t_VECSMALL)
    for (i=1; i<lo0; i++) Vbase[i] = vectbase[vperm[i]];
  else
    for (i=1; i<lo0; i++) Vbase[i] = vectbase[itos((GEN)vperm[i])];

  G = cgetg(lo,t_VEC);
  Ga= cgetg(lo,t_VEC);
  z = init_idele(nf);
  for (j=1; j<lo; j++)
  {
    GEN p1 = gcoeff(Uir,1,j);
    z[1]=Vbase[1]; I = idealpowred(nf,z,p1,prec);
    if (signe(p1)<0) I[1] = lmul((GEN)I[1],denom((GEN)I[1]));
    for (i=2; i<lo0; i++)
    {
      p1 = gcoeff(Uir,i,j); s = signe(p1);
      if (s)
      {
	z[1]=Vbase[i]; J = idealpowred(nf,z,p1,prec);
        if (s<0) J[1] = lmul((GEN)J[1],denom((GEN)J[1]));
	I = idealmulh(nf,I,J);
	I = ideallllred(nf,I,NULL,prec);
      }
    }
    J = inverse_if_smaller(nf, I, prec);
    if (J != I)
    { /* update wrt P */
      neg_row(Y ,j); V[j] = lneg((GEN)V[j]);
      neg_row(Ur,j); X[j] = lneg((GEN)X[j]);
    }
    G[j] = (long)J[1]; /* generator, order cyc[j] */
    Ga[j]= (long)J[2];
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

/* real(MC * M), where columns a and b of MC have been multiplied by 2^20+1 */
static GEN
shift_t2(GEN T2, GEN M, GEN MC, long a, long b)
{
  long i,j,N = lg(T2);
  GEN z, t2 = cgetg(N,t_MAT);
  for (j=1; j<N; j++)
  {
    t2[j] = lgetg(N,t_COL);
    for (i=1; i<=j; i++)
    {
      z = mul_real(gcoeff(MC,i,a), gcoeff(M,a,j));
      if (a!=b) z = gadd(z, mul_real(gcoeff(MC,i,b), gcoeff(M,b,j)));
      coeff(t2,j,i) = coeff(t2,i,j) = ladd(gcoeff(T2,i,j), gmul2n(z,20));
    }
  }
  return t2;
}

static GEN
compute_vecT2(long RU,GEN nf)
{
  GEN vecT2, M = gmael(nf,5,1), MC = gmael(nf,5,2), T2 = gmael(nf,5,3);
  long i,j,n = min(RU,9), ind = 1;

  vecT2=cgetg(1 + n*(n+1)/2,t_VEC);
  for (j=1; j<=n; j++)
    for (i=1; i<=j; i++) vecT2[ind++] = (long)shift_t2(T2,M,MC,i,j);
  if (DEBUGLEVEL) msgtimer("weighted T2 matrices");
  return vecT2;
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
 * of P[i] = e_i, and 1 if P[i] = A_i (i-th column of A)
 */
static GEN
relationrank(GEN *A, long r, GEN L)
{
  long i, n = lg(L)-1, av = avma, lim = stack_lim(av,1);
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

static GEN
codeprime(GEN bnf, GEN pr)
{
  long j,av=avma,tetpil;
  GEN p,al,fa,p1;

  p=(GEN)pr[1]; al=(GEN)pr[2]; fa=primedec(bnf,p);
  for (j=1; j<lg(fa); j++)
    if (gegal(al,gmael(fa,j,2)))
    {
      p1=mulsi(lg(al)-1,p); tetpil=avma;
      return gerepile(av,tetpil,addsi(j-1,p1));
    }
  err(talker,"bug in codeprime/smallbuchinit");
  return NULL; /* not reached */
}

static GEN
decodeprime(GEN nf, GEN co)
{
  long n,indi,av=avma;
  GEN p,rem,p1;

  n=lg(nf[7])-1; p=dvmdis(co,n,&rem); indi=itos(rem)+1;
  p1=primedec(nf,p);
  return gerepilecopy(av,(GEN)p1[indi]);
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
                        nf_GEN|nf_GENMAT|nf_FORCE|nf_GIVEPREC);
    if (typ(y) != t_INT)
      h[i] = y[2];
    else
    {
      y = idealpow(nf, (GEN)gen[i], (GEN)cyc[i]);
      h[i] = isprincipalgenforce(bnf,y)[2];
    }
  }
  return h;
}

/* compute principal ideals corresponding to bnf relations */
static GEN
makematal(GEN bnf)
{
  GEN W,B,pFB,vp,nf,ma, WB_C;
  long lW,lma,j,prec;

  ma = get_matal((GEN)bnf[10]);
  if (ma) return ma;

  W   = (GEN)bnf[1];
  B   = (GEN)bnf[2];
  WB_C= (GEN)bnf[4];
  vp  = (GEN)bnf[6];
  nf  = (GEN)bnf[7];
  lW=lg(W)-1; lma=lW+lg(B);
  pFB=cgetg(lma,t_VEC); ma=(GEN)bnf[5]; /* reorder factor base */
  for (j=1; j<lma; j++) pFB[j] = ma[itos((GEN)vp[j])];
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
    bnf = bnfinit0(nf,1,NULL,prec); setrand(c);
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
    long av = avma;
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
    long av = avma;
    if (DEBUGLEVEL) err(warner,"completing bnf (building matal)");
    bnfinsert(bnf, makematal(bnf), 1); avma = av;
    matal = get_matal((GEN)bnf[10]);
  }
  return matal;
}
			
GEN
smallbuchinit(GEN pol,GEN gcbach,GEN gcbach2,GEN gRELSUP,GEN gborne,long nbrelpid,long minsFB,long prec)
{
  long av=avma,av1,k;
  GEN y,bnf,pFB,vp,nf,mas,res,uni,v1,v2,v3;

  if (typ(pol)==t_VEC) bnf = checkbnf(pol);
  else
  {
    bnf=buchall(pol,gcbach,gcbach2,gRELSUP,gborne,nbrelpid,minsFB,-3,prec);
    bnf = checkbnf_discard(bnf);
  }
  pFB=(GEN)bnf[5]; vp=(GEN)bnf[6]; nf=(GEN)bnf[7];
  mas=(GEN)nf[5]; res=(GEN)bnf[8]; uni=(GEN)res[5];

  y=cgetg(13,t_VEC); y[1]=lcopy((GEN)nf[1]); y[2]=lcopy(gmael(nf,2,1));
  y[3]=lcopy((GEN)nf[3]); y[4]=lcopy((GEN)nf[7]);
  y[5]=lcopy((GEN)nf[6]); y[6]=lcopy((GEN)mas[5]);
  y[7]=lcopy((GEN)bnf[1]); y[8]=lcopy((GEN)bnf[2]);
  v1=cgetg(lg(pFB),t_VEC); y[9]=(long)v1;
  for (k=1; k<lg(pFB); k++)
    v1[k]=(long)codeprime(bnf,(GEN)pFB[itos((GEN)vp[k])]);
  v2=cgetg(3,t_VEC); y[10]=(long)v2;
  v2[1]=lcopy(gmael(res,4,1));
  v2[2]=(long)algtobasis(bnf,gmael(res,4,2));
  v3=cgetg(lg(uni),t_VEC); y[11]=(long)v3;
  for (k=1; k<lg(uni); k++)
    v3[k] = (long)algtobasis(bnf,(GEN)uni[k]);
  av1 = avma;
  y[12] = gcmp0((GEN)bnf[10])? lpilecopy(av1, makematal(bnf))
                             : lcopy((GEN)bnf[10]);
  return gerepileupto(av,y);
}

static GEN
get_regulator(GEN mun,long prec)
{
  long av,tetpil;
  GEN p1;

  if (lg(mun)==1) return gun;
  av=avma; p1 = gtrans(greal(mun));
  setlg(p1,lg(p1)-1); p1 = det(p1);
  tetpil=avma; return gerepile(av,tetpil,gabs(p1,prec));
}

static GEN
log_poleval(GEN P, GEN *ro, long i, GEN nf, long prec0)
{
  GEN x = poleval(P, (GEN)(*ro)[i]);
  long prec = prec0, k = 0;
  while (gcmp0(x) || ((k = gprecision(x)) && k < DEFAULTPREC))
  {
    prec = (prec-2)<<1;
    if (DEBUGLEVEL) err(warnprec,"log_poleval",prec);
    *ro = get_roots((GEN)nf[1], itos(gmael(nf,2,1)),lg(*ro)-1,prec);
    x = poleval(P, (GEN)(*ro)[i]);
  }
  if (k > prec0) x = gprec_w(x,prec0);
  return glog(x, prec0);
}

/* return corrected archimedian components
 * (= log(sigma_i(x)) - log(|Nx|)/[K:Q]) for a (matrix of elements) */
static GEN
get_arch2_i(GEN nf, GEN a, long prec, int units)
{
  GEN M,N, ro = dummycopy((GEN)nf[6]);
  long j,k, la = lg(a), ru = lg(ro), r1 = nf_get_r1(nf);

  M = cgetg(la,t_MAT); if (la == 1) return M;
  if (typ(a[1]) == t_COL) a = gmul((GEN)nf[7], a);
  if (units) N = NULL; /* no correction necessary */
  else
  {
    GEN pol = (GEN)nf[1];
    N = cgetg(la,t_VEC);
    for (k=1; k<la; k++) N[k] = (long)gabs(subres(pol,(GEN)a[k]),0);
    N = gdivgs(glog(N,prec), - (degpol(pol))); /* - log(|norm|) / [K:Q] */
  }
  for (k=1; k<la; k++)
  {
    GEN p, c = cgetg(ru,t_COL); M[k] = (long)c;
    for (j=1; j<ru; j++)
    {
      p = log_poleval((GEN)a[k],&ro,j,nf,prec);
      if (N) p = gadd(p, (GEN)N[k]);
      c[j]=(j<=r1)? (long) p: lmul2n(p,1);
    }
  }
  return M;
}

static GEN
get_arch2(GEN nf, GEN a, long prec, int units)
{
  long av = avma;
  return gerepilecopy(av, get_arch2_i(nf,a,prec,units));
}

static void
my_class_group_gen(GEN bnf, GEN *ptcl, GEN *ptcl2, long prec)
{
  GEN W=(GEN)bnf[1], C=(GEN)bnf[4], vperm=(GEN)bnf[6], nf=(GEN)bnf[7], *gptr[2];
  long av = avma;

  vectbase = (GEN)bnf[5]; /* needed by class_group_gen */
  class_group_gen(nf,W,C,vperm,ptcl,ptcl2, prec);
  gptr[0]=ptcl; gptr[1]=ptcl2; gerepilemany(av,gptr,2);
}

GEN
bnfnewprec(GEN bnf, long prec)
{
  GEN nf,ro,res,p1,funits,mun,matal,clgp,clgp2,y;
  long r1,r2,ru,pl1,pl2,prec1;

  bnf = checkbnf(bnf);
  if (prec <= 0) return nfnewprec(checknf(bnf),prec);
  y = cgetg(11,t_VEC);
  funits = check_units(bnf,"bnfnewprec");
  nf = (GEN)bnf[7];
  ro = (GEN)nf[6]; ru = lg(ro)-1;
  r1 = nf_get_r1(nf);
  r2 = (r1 + ru) >> 1;
  pl1 = (ru == 1 && r1 == 0)? 0: gexpo(funits);
  pl2 = gexpo(ro);
  prec1 = prec;
  prec += ((ru + r2 - 1) * (pl1 + (ru + r2) * pl2)) >> TWOPOTBITS_IN_LONG;
  nf = nfnewprec((GEN)bnf[7],prec);
  res = cgetg(7,t_VEC);
  ro = (GEN)nf[6];
  mun = get_arch2(nf,funits,prec,1);
  if (prec != prec1) { mun = gprec_w(mun,prec1); prec = prec1; }
  res[2]=(long)get_regulator(mun,prec);
  p1 = (GEN)bnf[8];
  res[3]=lcopy((GEN)p1[3]);
  res[4]=lcopy((GEN)p1[4]);
  res[5]=lcopy((GEN)p1[5]);
  res[6]=lcopy((GEN)p1[6]);

  y[1]=lcopy((GEN)bnf[1]);
  y[2]=lcopy((GEN)bnf[2]);
  y[3]=(long)mun;
  matal = check_and_build_matal(bnf);
  y[4]=(long)get_arch2(nf,matal,prec,0);
  y[5]=lcopy((GEN)bnf[5]);
  y[6]=lcopy((GEN)bnf[6]);
  y[7]=(long)nf;
  y[8]=(long)res;
  my_class_group_gen(y,&clgp,&clgp2,prec);
  res[1]=(long)clgp;
  y[9]=(long)clgp2;
  y[10]=lcopy((GEN)bnf[10]); return y;
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

GEN
bnfmake(GEN sbnf, long prec)
{
  long av = avma, j,k,n,r1,r2,ru,lpf;
  GEN p1,x,bas,ro,nf,mun,funits,index;
  GEN pfc,vp,mc,clgp,clgp2,res,y,W,racu,reg,matal;

  if (typ(sbnf)!=t_VEC || lg(sbnf)!=13)
    err(talker,"incorrect sbnf in bnfmake");
  x=(GEN)sbnf[1]; bas=(GEN)sbnf[4]; n=lg(bas)-1;
  r1=itos((GEN)sbnf[2]); r2=(n-r1)>>1; ru=r1+r2;
  ro=(GEN)sbnf[5];
  if (prec > gprecision(ro)) ro=get_roots(x,r1,ru,prec);
  index = gun;
  for (j=2; j<=n; j++) index = mulii(index, denom(leading_term(bas[j])));

  nf=cgetg(10,t_VEC);
  nf[1]=sbnf[1]; p1=cgetg(3,t_VEC); p1[1]=lstoi(r1); p1[2]=lstoi(r2);
  nf[2]=(long)p1;
  nf[3]=sbnf[3];
  nf[4]=(long)index;
  nf[6]=(long)ro;
  nf[7]=(long)bas;
  get_nf_matrices(nf, 0);

  funits=cgetg(ru,t_VEC); p1 = (GEN)sbnf[11];
  for (k=1; k < lg(p1); k++)
    funits[k] = lmul(bas,(GEN)p1[k]);
  mun = get_arch2_i(nf,funits,prec,1);

  prec=gprecision(ro); if (prec<DEFAULTPREC) prec=DEFAULTPREC;
  matal = get_matal((GEN)sbnf[12]);
  if (!matal) matal = (GEN)sbnf[12];
  mc = get_arch2_i(nf,matal,prec,0);

  pfc=(GEN)sbnf[9]; lpf=lg(pfc);
  vectbase=cgetg(lpf,t_COL); vp=cgetg(lpf,t_COL);
  for (j=1; j<lpf; j++)
  {
    vp[j]=lstoi(j);
    vectbase[j]=(long)decodeprime(nf,(GEN)pfc[j]);
  }
  W = (GEN)sbnf[7];
  class_group_gen(nf,W,mc,vp,&clgp,&clgp2, prec); /* uses vectbase */

  reg = get_regulator(mun,prec);
  p1=cgetg(3,t_VEC); racu=(GEN)sbnf[10];
  p1[1]=racu[1]; p1[2]=lmul(bas,(GEN)racu[2]);
  racu=p1;

  res=cgetg(7,t_VEC);
  res[1]=(long)clgp; res[2]=(long)reg;    res[3]=(long)dbltor(1.0);
  res[4]=(long)racu; res[5]=(long)funits; res[6]=lstoi(1000);

  y=cgetg(11,t_VEC);
  y[1]=(long)W;   y[2]=sbnf[8];        y[3]=(long)mun;
  y[4]=(long)mc;  y[5]=(long)vectbase; y[6]=(long)vp;
  y[7]=(long)nf;  y[8]=(long)res;      y[9]=(long)clgp2; y[10]=sbnf[12];
  return gerepilecopy(av,y);
}

static GEN
classgroupall(GEN P, GEN data, long flag, long prec)
{
  long court[3],doubl[4];
  long av=avma,flun,lx, minsFB=3,nbrelpid=4;
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
    case 0: flun=-2; break;
    case 1: flun=-3; break;
    case 2: flun=-1; break;
    case 3: return smallbuchinit(P,bach,bach2,RELSUP,borne,nbrelpid,minsFB,prec);
    case 4: flun=2; break;
    case 5: flun=3; break;
    case 6: flun=0; break;
    default: err(flagerr,"classgroupall");
      return NULL; /* not reached */
  }
  return buchall(P,bach,bach2,RELSUP,borne,nbrelpid,minsFB,flun,prec);
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
  ulong av = avma;
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
  ulong av = avma;
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
buchall_end(GEN nf,GEN CHANGE,long fl,long k, GEN fu, GEN clg1, GEN clg2,
            GEN reg, GEN c_1, GEN zu, GEN W, GEN B,
            GEN xarch, GEN matarch, GEN vectbase, GEN vperm)
{
  long i, l = labs(fl)>1? 11: fl? 9: 8;
  GEN p1,z, RES = cgetg(11,t_COL);

  setlg(RES,l);
  RES[5]=(long)clg1;
  RES[6]=(long)reg;
  RES[7]=(long)c_1;
  RES[8]=(long)zu;
  RES[9]=(long)fu;
  RES[10]=lstoi(k);
  if (fl>=0)
  {
    RES[1]=nf[1];
    RES[2]=nf[2]; p1=cgetg(3,t_VEC); p1[1]=nf[3]; p1[2]=nf[4];
    RES[3]=(long)p1;
    RES[4]=nf[7];
    z=cgetg(2,t_MAT); z[1]=(long)RES; return z;
  }
  z=cgetg(11,t_VEC);
  z[1]=(long)W;
  z[2]=(long)B;
  z[3]=(long)xarch;
  z[4]=(long)matarch;
  z[5]=(long)vectbase;
  for (i=lg(vperm)-1; i>0; i--) vperm[i]=lstoi(vperm[i]);
  settyp(vperm, t_VEC);
  z[6]=(long)vperm;
  z[7]=(long)nf; RES+=4; RES[0]=evaltyp(t_VEC) | evallg(l-4);
  z[8]=(long)RES;
  z[9]=(long)clg2;
  z[10]=zero; /* dummy: we MUST have lg(bnf) != lg(nf) */
  if (CHANGE) { p1=cgetg(3,t_VEC); p1[1]=(long)z; p1[2]=(long)CHANGE; z=p1; }
  return z;
}

static GEN
buchall_for_degree_one_pol(GEN nf, GEN CHANGE, long flun)
{
  long av = avma, k = EXP220;
  GEN W,B,xarch,matarch,vectbase,vperm;
  GEN fu=cgetg(1,t_VEC), reg=gun, c_1=gun, zu=cgetg(3,t_VEC);
  GEN clg1=cgetg(4,t_VEC), clg2=cgetg(4,t_VEC);

  clg1[1]=un; clg1[2]=clg1[3]=clg2[2]=clg2[3]=lgetg(1,t_VEC);
  clg2[1]=lgetg(1,t_MAT);
  zu[1]=deux; zu[2]=lnegi(gun);
  W=B=xarch=matarch=cgetg(1,t_MAT);
  vectbase=cgetg(1,t_COL); vperm=cgetg(1,t_VEC);

  return gerepilecopy(av, buchall_end(nf,CHANGE,flun,k,fu,clg1,clg2,reg,c_1,zu,W,B,xarch,matarch,vectbase,vperm));
}

static GEN
get_LLLnf(GEN nf, long prec)
{
  GEN M  = gmael(nf,5,1);
  GEN T2 = gmael(nf,5,3);
  GEN cbase = lllgramintern(T2,100,1,prec);
  GEN v = cgetg(5,t_VEC);
  if (!cbase) return NULL;
  if (gegal(cbase, idmat(lg(T2)-1))) cbase = NULL;
  v[1] = (long) (cbase? qf_base_change(T2, cbase, 1): T2);
  v[2] = (long) (cbase? gmul(M, cbase): M);
  v[3] = (long) cbase;
  v[4] = (long) (cbase? ZM_inv(cbase,gun): NULL); return v;
}

GEN
buchall(GEN P,GEN gcbach,GEN gcbach2,GEN gRELSUP,GEN gborne,long nbrelpid,
        long minsFB,long flun,long prec)
{
  ulong av = avma,av0,av1,limpile;
  long N,R1,R2,RU,PRECREG,PRECLLL,KCCO,RELSUP,LIMC,LIMC2,lim;
  long nlze,zc,nrelsup,nreldep,phase,matmax,i,j,k,ss,cglob;
  long first=1, sfb_increase=0, sfb_trials=0, precdouble=0, precadd=0;
  double cbach,cbach2,drc,LOGD2;
  GEN p1,vecT2,fu,zu,nf,LLLnf,D,xarch,W,R,Res,z,h,vperm,subFB;
  GEN resc,B,C,c1,lambda,pdep,parch,liste,invp,clg1,clg2, *mat;
  GEN CHANGE=NULL, extramat=NULL, extraC=NULL, list_jideal=NULL;
  char *precpb = NULL;

  if (DEBUGLEVEL) timer2();

  P = get_nfpol(P, &nf);
  if (typ(gRELSUP) != t_INT) gRELSUP = gtrunc(gRELSUP);
  RELSUP = itos(gRELSUP);
  if (RELSUP<=0) err(talker,"not enough relations in bnfxxx");

  /* Initializations */
  fu = NULL; /* gcc -Wall */
  N = degpol(P); PRECREG = max(BIGDEFAULTPREC,prec);
  if (!nf)
  {
    nf = initalgall0(P, nf_REGULAR, PRECREG);
    /* P was non-monic and nfinit changed it ? */
    if (lg(nf)==3) { CHANGE = (GEN)nf[2]; nf = (GEN)nf[1]; }
  }
  if (N<=1) return buchall_for_degree_one_pol(nf,CHANGE,flun);
  zu = rootsof1(nf);
  zu[2] = lmul((GEN)nf[7],(GEN)zu[2]);
  if (DEBUGLEVEL) msgtimer("initalg & rootsof1");

  R1 = itos(gmael(nf,2,1)); R2 = (N-R1)>>1; RU = R1+R2;
  D = (GEN)nf[3]; drc = fabs(gtodouble(D));
  LOGD2 = log(drc); LOGD2 = LOGD2*LOGD2;
  lim = (long) (exp(-(double)N) * sqrt(2*PI*N*drc) * pow(4/PI,(double)R2));
  if (lim < 3) lim = 3;
  cbach = min(12., gtodouble(gcbach)); cbach /= 2;
  cbach2 = gtodouble(gcbach2);
  /* resc = sqrt(D) w / 2^r1 (2pi)^r2 ~ hR / Res(zeta_K,1) */
  resc = gmul(gmul2n(gpuigs(shiftr(mppi(DEFAULTPREC),1),-R2),-R1),
              gsqrt(absi(D),DEFAULTPREC));
  resc = mulri(resc,(GEN)zu[1]);
  if (DEBUGLEVEL)
  {
    fprintferr("N = %ld, R1 = %ld, R2 = %ld, RU = %ld\n",N,R1,R2,RU);
    fprintferr("D = %Z\n",D);
  }
  av0 = avma; mat = NULL; FB = NULL;

START:
  avma = av0;
  if (first) first = 0; else desallocate(&mat);
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

  /* T2-LLL-reduce nf.zk */
  LLLnf = get_LLLnf(nf, PRECREG);
  if (!LLLnf) { precpb = "LLLnf"; goto START; }

  LIMC = (long)(cbach*LOGD2); if (LIMC < 20) LIMC = 20;
  LIMC2= max(3 * N, (long)(cbach2*LOGD2));
  if (LIMC2 < LIMC) LIMC2 = LIMC;
  if (DEBUGLEVEL) { fprintferr("LIMC = %ld, LIMC2 = %ld\n",LIMC,LIMC2); }

  /* initialize FB, [sub]vperm */
  Res = FBgen(nf,LIMC2,LIMC);
  if (!Res) goto START;
  vperm = cgetg(lg(vectbase), t_VECSMALL);
  sfb_trials = sfb_increase = 0;
  subFB = subFBgen(N,min(lim,LIMC2), minsFB, vperm, &ss);
  if (!subFB) goto START;
  nreldep = nrelsup = 0;

  /* PRECLLL = prec for LLL-reductions (idealred)
   * PRECREG = prec for archimedean components */
  PRECLLL = DEFAULTPREC
          + ((expi(D)*(lg(subFB)-2)+((N*N)>>2))>>TWOPOTBITS_IN_LONG);
  if (!precdouble) PRECREG = prec+1;
  if (PRECREG < PRECLLL) PRECREG = PRECLLL;
  KCCO = KC+RU-1 + max(ss,RELSUP); /* expected number of needed relations */
  if (DEBUGLEVEL)
    fprintferr("relsup = %ld, ss = %ld, KCZ = %ld, KC = %ld, KCCO = %ld\n",
               RELSUP,ss,KCZ,KC,KCCO);
  matmax = 10*KCCO + MAXRELSUP; /* make room for lots of relations */
  mat = (GEN*)gpmalloc(sizeof(GEN)*(matmax + 1));
  setlg(mat, KCCO+1);
  C = cgetg(KCCO+1,t_MAT);
  /* trivial relations (p) = prod P^e */
  cglob = 0; z = zerocol(RU);
  for (i=1; i<=KCZ; i++)
  {
    GEN P = idealbase[i];
    if (isclone(P))
    { /* all prime divisors in FB */
      unsetisclone(P); cglob++;
      C[cglob] = (long)z; /* 0 */
      mat[cglob] = p1 = col_0(KC);
      k = numideal[FB[i]];
      p1[0] = k+1; /* for already_found_relation */
      p1 += k;
      for (j=lg(P)-1; j; j--) p1[j] = itos(gmael(P,j,3));
    }
  }
  if (DEBUGLEVEL) fprintferr("After trivial relations, cglob = %ld\n",cglob);
  /* initialize for other relations */
  for (i=cglob+1; i<=KCCO; i++)
  {
    mat[i] = col_0(KC);
    C[i] = (long)cgetc_col(RU,PRECREG);
  }
  av1 = avma; liste = cgetg(KC+1,t_VECSMALL);
  for (i=1; i<=KC; i++) liste[i] = 0;
  invp = relationrank(mat,cglob,liste);

  /* relations through elements of small norm */
  cglob = small_norm_for_buchall(cglob,mat,C,(long)LIMC,PRECREG,
                                 nf,gborne,nbrelpid,invp,liste,LLLnf);
  if (cglob < 0) { precpb = "small_norm"; goto START; }
  avma = av1; limpile = stack_lim(av1,1);

  phase = 0;
  nlze = matmax = 0; /* for lint */
  vecT2 = NULL;

  /* random relations */
  if (cglob == KCCO) /* enough rels, but init random_relations just in case */
    ((void(*)(long))random_relation)(-1);
  else
  {
    GEN matarch;

    if (DEBUGLEVEL) fprintferr("\n#### Looking for random relations\n");
MORE:
    if (sfb_increase)
    {
      if (DEBUGLEVEL) fprintferr("*** Increasing sub factor base\n");
      sfb_increase = 0;
      if (++sfb_trials > SFB_MAX) goto START;
      subFB = subFBgen(N,min(lim,LIMC2), lg(subFB)-1+SFB_STEP,NULL,&ss);
      if (!subFB) goto START;
      nreldep = nrelsup = 0;
    }

    if (phase == 0) matarch = C;
    else
    { /* reduced the relation matrix at least once */
      long lgex = max(nlze, MIN_EXTRA); /* number of new relations sought */
      long slim; /* total number of relations (including lgex new ones) */
      setlg(extraC,  lgex+1);
      setlg(extramat,lgex+1); /* were allocated after hnfspec */
      slim = cglob+lgex;
      if (slim > matmax)
      {
        matmax = 2 * slim;
        mat = (long**)gprealloc(mat, (matmax+1) * sizeof(long*));
      }
      setlg(mat, slim+1);
      if (DEBUGLEVEL)
	fprintferr("\n(need %ld more relation%s)\n", lgex, (lgex==1)?"":"s");
      for (j=cglob+1; j<=slim; j++) mat[j] = col_0(KC);
      matarch = extraC - cglob; /* start at 0, the others at cglob */
    }
    if (!vecT2)
    {
      vecT2 = compute_vecT2(RU,nf);
      av1 = avma;
    }
    if (!powsubFB)
    {
      powsubFBgen(nf,subFB,CBUCHG+1,PRECREG);
      av1 = avma;
    }
    ss = random_relation(phase,cglob,(long)LIMC,PRECLLL,PRECREG,
                         nf,subFB,vecT2,mat,matarch,list_jideal);
    if (ss < 0)
    { /* could not find relations */
      if (ss != -1) precpb = "random_relation"; /* precision pb */
      goto START;
    }
    if (DEBUGLEVEL > 2) dbg_outrel(phase,cglob,vperm,mat,matarch);
    if (phase)
      for (j=lg(extramat)-1; j>0; j--)
      {
	GEN c = mat[cglob+j], *g = (GEN*) extramat[j];
	for (k=1; k<=KC; k++) g[k] = stoi(c[vperm[k]]);
      }
    cglob = ss;
  }

  /* reduce relation matrices */
  if (phase == 0)
  { /* never reduced before */
    long lgex;
    W = hnfspec(mat,vperm,&pdep,&B,&C, lg(subFB)-1);
    phase = 1;
    nlze = lg(pdep)>1? lg(pdep[1])-1: lg(B[1])-1;
    if (nlze)
    {
      list_jideal = cgetg(nlze+1, t_VECSMALL);
      for (i=1; i<=nlze; i++) list_jideal[i] = vperm[i];
    }
    lgex = max(nlze, MIN_EXTRA); /* set lgex > 0, in case regulator is 0 */
    /* allocate now, reduce dimension later (setlg) when lgex goes down */
    extramat= cgetg(lgex+1,t_MAT);
    extraC  = cgetg(lgex+1,t_MAT);
    for (j=1; j<=lgex; j++)
    {
      extramat[j]=lgetg(KC+1,t_COL);
      extraC[j] = (long)cgetc_col(RU,PRECREG);
    }
  }
  else
  {
    if (low_stack(limpile, stack_lim(av1,1)))
    {
      GEN *gptr[6];
      if(DEBUGMEM>1) err(warnmem,"buchall");
      gptr[0]=&W; gptr[1]=&C; gptr[2]=&B; gptr[3]=&pdep;
      gptr[4]=&extramat; gptr[5]=&extraC; gerepilemany(av1,gptr,6);
    }
    list_jideal = NULL;
    W = hnfadd(W,vperm,&pdep,&B,&C, extramat,extraC);
    nlze = lg(pdep)>1? lg(pdep[1])-1: lg(B[1])-1;
    if (nlze && ++nreldep > MAXRELSUP) { sfb_increase=1; goto MORE; }
  }
  if (nlze) goto MORE; /* dependent rows */

  /* first attempt at regulator for the check */
  zc = (lg(mat)-1) - (lg(B)-1) - (lg(W)-1);
  xarch = cgetg(zc+1,t_MAT); /* cols corresponding to units */
  for (j=1; j<=zc; j++) xarch[j] = C[j];
  R = compute_multiple_of_R(xarch,RU,N,&lambda);
  if (!R)
  { /* not full rank for units */
    if (DEBUGLEVEL) fprintferr("regulator is zero.\n");
    if (++nrelsup > MAXRELSUP) goto START;
    nlze = MIN_EXTRA; goto MORE;
  }
  /* anticipate precision problems */
  if (!lambda) { precpb = "bestappr"; goto START; }

  /* class number */
  h = dethnf_i(W);
  if (DEBUGLEVEL) fprintferr("\n#### Tentative class number: %Z\n", h);

  /* z ~ h R if enough relations, a multiple otherwise */
  z = mulrr(Res,resc);
  p1 = gmul2n(divir(h,z), 1);
  i = compute_R(lambda,p1,&parch,&R);
  switch(i)
  {
    case PRECI: /* precision problem unless we cheat on Bach constant */
      if (!precdouble) precpb = "compute_R";
      goto START;
    case RELAT: /* not enough relations */
      if (++nrelsup <= MAXRELSUP) { nlze = MIN_EXTRA; goto MORE; }
      if (cbach < 11.99) { sfb_increase = 1; goto MORE; }
      err(warner,"suspicious check. Try to increase extra relations");
  }
  /* DONE! */

  if (KCZ2 > KCZ)
  { /* "be honest" */
    if (!powsubFB) powsubFBgen(nf,subFB,CBUCHG+1,PRECREG);
    if (!be_honest(nf,subFB,PRECLLL)) goto START;
  }

  /* fundamental units */
  if (flun < 0 || flun > 1)
  {
    xarch = gmul(xarch, parch); /* arch. components of fund. units */
    xarch = cleancol(xarch,N,PRECREG);
    if (DEBUGLEVEL) msgtimer("cleancol");
  }
  if (labs(flun) > 1)
  {
    fu = getfu(nf,&xarch,R,flun,&k,PRECREG);
    if (k <= 0 && labs(flun) > 2)
    {
      if (k < 0)
      {
        precadd = (DEFAULTPREC-2) + ((-k) >> TWOPOTBITS_IN_LONG);
        if (precadd <= 0) precadd = (DEFAULTPREC-2);
      }
      precpb = "getfu"; goto START;
    }
  }

  /* class group generators */
  i = lg(C)-zc; C += zc; C[0] = evaltyp(t_MAT)|evallg(i);
  C = cleancol(C,N,PRECREG);
  class_group_gen(nf,W,C,vperm, &clg1, &clg2, PRECREG);

  c1 = gdiv(gmul(R,h), z);
  desallocate(&mat);

  return gerepilecopy(av, buchall_end(nf,CHANGE,flun,k,fu,clg1,clg2,R,c1,zu,W,B,xarch,C,vectbase,vperm));
}
