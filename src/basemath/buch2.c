/*******************************************************************/
/*                                                                 */
/*         CLASS GROUP AND REGULATOR (McCURLEY, BUCHMANN)          */
/*                    GENERAL NUMBER FIELDS                        */
/*                                                                 */
/*******************************************************************/
/* $Id$ */
#include "pari.h"
#include "parinf.h"
int addcolumntomatrix(GEN V, GEN invp, GEN L);
double check_bach(double cbach, double B);
GEN gmul_mat_smallvec(GEN x, GEN y);
GEN get_arch_real(GEN nf,GEN x,GEN *emb,long prec);
GEN get_arch(GEN nf,GEN x,long prec);
GEN get_roots(GEN x,long r1,long ru,long prec);
long ideal_is_zk(GEN ideal,long N);
GEN idealpowred_prime(GEN nf, GEN vp, GEN n, long prec);
long int_elt_val(GEN nf, GEN x, GEN p, GEN b, long v);
GEN make_M(long n,long ru,GEN basis,GEN roo);
GEN make_MC(long n,long r1,long ru,GEN M);
GEN make_MDI(GEN nf, GEN TI, GEN *a, GEN *b);

#define SFB_MAX 2
#define SFB_STEP 2
#define MIN_EXTRA 1

#define RANDOM_BITS 4
static const int CBUCHG = (1<<RANDOM_BITS) - 1;
static const int randshift = BITS_IN_RANDOM-1 - RANDOM_BITS;
#undef RANDOM_BITS

static long KC,KCZ,KCZ2,MAXRELSUP;
static long primfact[500],expoprimfact[500];
static long *factorbase, *numfactorbase, *numideal;
static GEN *idealbase, vectbase, powsubfb;

/* factorbase[i]     i-th rational prime used in factor base
 * numfactorbase[i]  index k such that factorbase[k]=i (0 if i is not prime)
 *
 * vectbase          vector of all ideals in factorbase
 * vecbase o subfb = part of factorbase used to build random relations
 * powsubfb  array lg(subfb) x (CBUCHG+1) = all powers up to CBUCHG
 *
 * idealbase[i]      prime ideals above i in factorbase
 * numideal[i]       index k such that idealbase[k] = i.
 *
 * matcopy           all relations found (as long integers, not reduced)
 * cmptglob          lg(matcopy) = total number of relations found
 *
 * Use only non-inert primes, coprime to discriminant index F:
 *   KC = number of prime ideals in factor base (norm < Bach cst)
 *   KC2= number of prime ideals assumed to generate class group (>= KC)
 *
 *   KCZ = number of rational primes under ideal counted by KC
 *   KCZ2= same for KC2le nombre d'ideaux premiers utilises au total.
 */

/* x[0] = length(x) */
static long
ccontent(long* x)
{
  long i, s=labs(x[1]);
  for (i=2; i<=x[0] && s>1; i++) s = cgcd(x[i],s);
  return s;
}

static void
desallocate(long **matcopy)
{
  long i;
  free(numfactorbase); free(factorbase); free(numideal); free(idealbase);
  if (matcopy)
  {
    for (i=lg(matcopy)-1; i; i--) free(matcopy[i]);
    free(matcopy); matcopy = NULL;
  }
  powsubfb = NULL;
}

/* Return the list of indexes or the primes chosen for the subfactorbase.
 * Fill vperm (if !=0): primes ideals sorted by increasing norm (except the
 * ones in subfactorbase come first [dense rows come first for hnfspec])
 * ss = number of rational primes whose divisors are all in factorbase
 */
static GEN
subfactorbasegen(long N,long m,long minsfb,GEN vperm, long *ptss)
{
  long av = avma,i,j, lv=lg(vectbase),s=0,s1=0,n=0,ss=0,z=0;
  GEN y1,y2,subfb,perm,perm1,P,Q;
  double prod;

  (void)new_chunk(lv); /* room for subfb */
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
      s=0; s1=0;
    }
  }
  if (z+minsfb >= lv) return NULL;

  prod = 1.0;
  perm = sindexsort(y1) + z; /* skip "zeroes" (excluded ideals) */
  for(;;)
  {
    if (++n > minsfb && (z+n >= lv || prod > m + 0.5)) break;
    prod *= gtodouble((GEN)y1[perm[n]]);
  }
  if (prod < m) return NULL;
  n--;

  /* take the first (non excluded) n ideals (wrt norm), put them first, and
   * sort the rest by increasing norm */
  for (j=1; j<=n; j++) y2[perm[j]] = zero;
  perm1 = sindexsort(y2); avma = av;

  subfb = cgetg(n+1, t_VECSMALL);
  if (vperm)
  {
    for (j=1; j<=n; j++) vperm[j] = perm[j];
    for (   ; j<lv; j++) vperm[j] = perm1[j];
  }
  for (j=1; j<=n; j++) subfb[j] = perm[j];

  if (DEBUGLEVEL)
  {
    if (DEBUGLEVEL>3)
    {
      fprintferr("\n***** IDEALS IN FACTORBASE *****\n\n");
      for (i=1; i<=KC; i++) fprintferr("no %ld = %Z\n",i,vectbase[i]);
      fprintferr("\n***** IDEALS IN SUB FACTORBASE *****\n\n");
      P=cgetg(n+1,t_COL);
      for (j=1; j<=n; j++) P[j] = vectbase[subfb[j]];
      outerr(P);
      fprintferr("\n***** INITIAL PERMUTATION *****\n\n");
      fprintferr("vperm = %Z\n\n",vperm);
    }
    msgtimer("subfactorbase (%ld elements)",n);
  }
  *ptss = ss;
  return subfb;
}

static GEN
mulred(GEN nf,GEN x, GEN I, long prec,long precint)
{
  long av = avma;
  GEN y = cgetg(3,t_VEC);

  y[1] = (long)idealmulh(nf,I,(GEN)x[1]);
  y[2] = x[2];
  y = ideallllredall(nf,y,NULL,prec,precint);
  y[1] = (long)ideal_two_elt(nf,(GEN)y[1]);
  return gerepileupto(av,gcopy(y));
}

/* Compute powers of prime ideals (P^0,...,P^a) in subfactorbase (a > 1)
 * powsubfb[j][i] contains P_i^j in LLL form + archimedean part
 */
static void
powsubfbgen(GEN nf,GEN subfb,long a,long prec,long precint)
{
  long i,j,n=lg(subfb),N=lgef(nf[1])-3,RU;
  GEN id, *pow;

  powsubfb = cgetg(n, t_VEC);
  if (DEBUGLEVEL)
  { fprintferr("Computing powers for sub-factor base:\n"); flusherr(); }
  RU=itos(gmael(nf,2,1)); RU = RU + (N-RU)/2;
  id=cgetg(3,t_VEC);
  id[1] = (long)idmat(N);
  id[2] = (long)zerocol(RU); settyp(id[2],t_VEC);

  for (i=1; i<n; i++)
  {
    GEN vp = (GEN)vectbase[subfb[i]];
    GEN z = cgetg(3,t_VEC); z[1]=vp[1]; z[2]=vp[2];
    pow = (GEN*)cgetg(a+1,t_VEC);
    powsubfb[i] = (long)pow; pow[0]=id;
    pow[1]=cgetg(3,t_VEC);
    pow[1][1] = (long)z;
    pow[1][2] = id[2];
    vp = prime_to_ideal(nf,vp);
    for (j=2; j<=a; j++)
    {
      pow[j] = mulred(nf,pow[j-1],vp,prec,precint);
      if (DEBUGLEVEL>1) fprintferr(" %ld",j);
    }
    if (DEBUGLEVEL>1) { fprintferr("\n"); flusherr(); }
  }
  if (DEBUGLEVEL)
  {
    if (DEBUGLEVEL>7)
    {
      fprintferr("**** POWERS IN SUB-FACTOR BASE ****\n\n");
      for (i=1; i<n; i++)
      {
        pow = (GEN*)powsubfb[i];
	fprintferr("powsubfb[%ld]:\n",i);
	for (j=0; j<=a; j++) fprintferr("^%ld = %Z\n", j,pow[j]);
	fprintferr("\n");
      }
    }
    msgtimer("powsubfbgen");
  }
}

/* Compute factorbase, numfactorbase, idealbase, vectbase, numideal.
 * n2: bound for norm of tested prime ideals (includes be_honest())
 * n : bound for prime ideals used to build relations (Bach cst) ( <= n2 )

 * Return prod_{p<=n2} (1-1/p) / prod_{Norm(P)<=n2} (1-1/Norm(P)),
 * close to residue of zeta_K at 1 = 2^r1 (2pi)^r2 h R / (w D)
 */
static GEN
factorbasegen(GEN nf,long n2,long n)
{
  byteptr delta=diffptr;
  long KC2,i,j,k,p,lon,ip,nor, N = lgef(nf[1])-3;
  GEN p2,p1,NormP,lfun;
  long prim[] = { evaltyp(t_INT)|m_evallg(3), evalsigne(1)|evallgefint(3),0 };

  numfactorbase= (long*)gpmalloc(sizeof(long)*(n2+1));
  factorbase   = (long*)gpmalloc(sizeof(long)*(n2+1));
  numideal     = (long*)gpmalloc(sizeof(long)*(n2+1));
  idealbase    = (GEN *)gpmalloc(sizeof(GEN )*(n2+1));

  lfun=realun(DEFAULTPREC);
  p=*delta++; i=0; ip=0; KC=0;
  while (p<=n2)
  {
    long av = avma, av1;
    if (DEBUGLEVEL>=2) { fprintferr(" %ld",p); flusherr(); }
    prim[2] = p; p1 = primedec(nf,prim); lon=lg(p1);
    av1 = avma;
    divrsz(mulsr(p-1,lfun),p,lfun);
    if (itos(gmael(p1,1,4)) == N) /* p inert */
    {
      NormP = gpowgs(prim,N);
      if (!is_bigint(NormP) && (nor=NormP[2]) <= n2)
	divrsz(mulsr(nor,lfun),nor-1, lfun);
      avma = av1;
    }
    else
    {
      numideal[p]=ip;
      i++; numfactorbase[p]=i; factorbase[i]=p;
      for (k=1; k<lon; k++,ip++)
      {
	NormP = powgi(prim,gmael(p1,k,4));
	if (is_bigint(NormP) || (nor=NormP[2]) > n2) break;

        divrsz(mulsr(nor,lfun),nor-1, lfun);
      }
      /* keep all ideals with Norm <= n2 */
      avma = av1;
      if (k == lon)
        setisclone(p1); /* flag it: all prime divisors in factorbase */
      else
        { setlg(p1,k); p1 = gerepile(av,av1,gcopy(p1)); }
      idealbase[i] = p1;
    }
    if (!*delta) err(primer1);
    p += *delta++;
    if (KC == 0 && p>n) { KCZ=i; KC=ip; }
  }
  if (!KC) return NULL;
  KCZ2=i; KC2=ip; MAXRELSUP = min(50,4*KC);

  vectbase=cgetg(KC+1,t_COL);
  for (i=1; i<=KCZ; i++)
  {
    p1 = idealbase[i]; k=lg(p1);
    p2 = vectbase + numideal[factorbase[i]];
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
  return lfun;
}

/* can we factor I / m ? (m pseudo minimum, computed in ideallllredpart1) */
static long
factorisegen(GEN nf,GEN idealvec,long kcz,long limp)
{
  long i,j,n1,ip,v,p,k,lo,ifinal;
  GEN x,q,r,P,p1,listexpo;
  GEN I = (GEN)idealvec[1];
  GEN m = (GEN)idealvec[2];
  GEN Nm= (GEN)idealvec[3];

  x = divii(Nm, dethnf_i(I)); /* m in I, so NI | Nm */
  if (is_pm1(x)) { primfact[0]=0; return 1; }
  listexpo = new_chunk(kcz+1);
  for (i=1; ; i++)
  {
    p=factorbase[i]; q=dvmdis(x,p,&r);
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
      p = factorbase[i]; p1 = idealbase[numfactorbase[p]];
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

  p = itos(x); p1 = idealbase[numfactorbase[p]];
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

/* can we factor alpha ? */
static long
factorisealpha(GEN nf,GEN alpha,long kcz,long limp)
{
  long i,j,n1,ip,v,p,k,lo,ifinal;
  GEN x,q,r,P,p1,listexpo;

  x = absi(subres(gmul((GEN)nf[7],alpha), (GEN)nf[1]));
  if (is_pm1(x)) { primfact[0]=0; return 1; }
  listexpo = new_chunk(kcz+1);
  for (i=1; ; i++)
  {
    p=factorbase[i]; q=dvmdis(x,p,&r);
    for (k=0; !signe(r); k++) { x=q; q=dvmdis(x,p,&r); }
    listexpo[i] = k;
    if (cmpis(q,p)<=0) break;
    if (i==kcz) return 0;
  }
  if (cmpis(x,limp) > 0) return 0;

  ifinal=i; lo = 0;
  for (i=1; i<=ifinal; i++)
  {
    k = listexpo[i];
    if (k)
    {
      p = factorbase[i]; p1 = idealbase[numfactorbase[p]];
      n1 = lg(p1); ip = numideal[p];
      for (j=1; j<n1; j++)
      {
        P = (GEN)p1[j];
	v = int_elt_val(nf,alpha,(GEN)P[1],(GEN)P[5], k);
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
  if (is_pm1(x)) { primfact[0]=lo; return 1; }

  p = itos(x); p1 = idealbase[numfactorbase[p]];
  n1 = lg(p1); ip = numideal[p];
  for (k=1,j=1; j<n1; j++)
  {
    P = (GEN)p1[j];
    v = int_elt_val(nf,alpha,(GEN)P[1],(GEN)P[5], k);
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
  GEN s,s2,re,p2,im,y;

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
  im = gimag(x);
  s = gdivgs(s,-N);
  s2 = (N>R1)? gmul2n(s,1): NULL;
  p2=gmul2n(mppi(PRECREG),2);
  tetpil=avma; y=cgetg(RU+1,tx);
  for (i=1; i<=RU; i++)
  {
    GEN p1=cgetg(3,t_COMPLEX); y[i]=(long)p1;
    p1[1] = ladd((GEN)re[i], (i<=R1)?s:s2);
    p1[2] = lmod((GEN)im[i], p2);
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
    char *s=NULL;
    switch(reason)
    {
    case RELAT:
      s = "not enough relations for fundamental units, not given"; break;
    case LARGE:
      s = "fundamental units too large, not given"; break;
    case PRECI:
      s = "insufficient precision for fundamental units, not given"; break;
    }
    err(warner,s);
  }
  avma=av; return cgetg(1,t_MAT);
}

/* to check whether the exponential will get too big */
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
getfu(GEN nf,GEN *ptxarch,GEN reg,long flun,long *pte,long PRECREG)
{
  long av=avma,i,j,RU,N=lgef(nf[1])-3,e,R1,R2;
  GEN pol,p1,p2,p3,y,matep,s,xarch,vec;
  GEN *gptr[2];

  if (DEBUGLEVEL)
    { fprintferr("\n#### Computing fundamental units\n"); flusherr(); }
  R1=itos(gmael(nf,2,1)); R2=(N-R1)>>1; RU=R1+R2;
  if (RU==1) { *pte=BIGINT; return cgetg(1,t_MAT); }

  *pte = 0; xarch=*ptxarch;
  if (gexpo(reg)<-8) return not_given(av,flun,RELAT);

  matep=cgetg(RU,t_MAT);
  for (j=1; j<RU; j++)
  {
    s=gzero; for (i=1; i<=RU; i++) s=gadd(s,greal(gcoeff(xarch,i,j)));
    s=gdivgs(s,N);
    p1=cgetg(N+1,t_COL); matep[j]=(long)p1;
    for (i=1; i<=R1; i++)
      p1[i]=lsub(gcoeff(xarch,i,j),s);
    for (i=R1+1; i<=RU; i++)
    {
      p1[i]=lsub(gmul2n(gcoeff(xarch,i,j),-1),s);
      p1[i+R2]=lconj((GEN)p1[i]);
    }
  }
  p1 = lllintern(greal(matep),1,PRECREG);
  if (!p1) return not_given(av,flun,PRECI);
  p2 = gmul(matep,p1);
  if (expgexpo(p2) > 20) return not_given(av,flun,LARGE);
  matep=gexp(p2,PRECREG);
  xarch=gmul(xarch,p1);

  p1=gmael(nf,5,1);
  p2=cgetg(N+1,t_MAT);
  for (j=1; j<=N; j++)
  {
    p3=cgetg(N+1,t_COL); p2[j]=(long)p3;
    for (i=1; i<=R1; i++) p3[i]=coeff(p1,i,j);
    for (   ; i<=RU; i++)
    {
      p3[i]=coeff(p1,i,j);
      p3[i+R2]=lconj((GEN)p3[i]);
    }
  }
  y=greal(grndtoi(gauss(p2,matep),&e));
  if (e>=0) return not_given(av,flun,PRECI);
  *pte = -e; pol = (GEN) nf[1];
  p1 = cgetg(3,t_COMPLEX);
  p1[1] = zero; p1[2] = lmppi(PRECREG);  /* p1 = i * pi */
  if (R1<RU) p2 = gshift(p1,1);
  vec = cgetg(RU+1,t_COL);
  for (i=1; i<=R1; i++) vec[i]=(long)p1;
  for (   ; i<=RU; i++) vec[i]=(long)p2;
  p3=cgetg(N+1,t_COL);

  for (j=1; j<lg(y); j++)
  {
    p1=(GEN)y[j]; p2=ginvmod(gmul((GEN)nf[7],p1), pol);
    for (i=1; i<lgef(p2)-1; i++) p3[i]=p2[i+1];
    for (   ; i<=N; i++) p3[i]=zero;
    p2=gmul((GEN)nf[8],p3);
    if (gcmp(gnorml2(p2),gnorml2(p1))<0)
    {
      p1=p2; xarch[j]=lneg((GEN)xarch[j]);
    }
    i=N; while (i>=1 && gcmp0((GEN)p1[i])) i--;
    if (gsigne((GEN)p1[i])>=0) y[j]=(long)p1;
    else
    {
      y[j]=lneg(p1);
      xarch[j]=ladd((GEN)xarch[j],vec);
    }
  }
  p1=gmul((GEN)nf[7],y);
  for (j=1; j<lg(y); j++)
    if (!gcmp1(gabs(gnorm(gmodulcp((GEN)p1[j],pol)),0)))
      { *pte = 0; return not_given(av,flun,LARGE); }
  if (DEBUGLEVEL) msgtimer("getfu");
  *ptxarch=xarch; gptr[0]=ptxarch; gptr[1]=&y;
  gerepilemany(av,gptr,2); return y;
}
#undef RELAT
#undef LARGE
#undef PRECI

GEN
buchfu(GEN bnf)
{
  GEN nf,xarch,reg,res,fu,y;
  long av=avma,tetpil,c,RU;

  bnf = checkbnf(bnf); nf = (GEN)bnf[7];
  RU=itos(gmael(nf,2,1))+itos(gmael(nf,2,2));
  res=(GEN)bnf[8];
  if (lg(res)==7 && lg(res[5])==RU)
  {
    y=cgetg(3,t_VEC); y[1]=lcopy((GEN)res[5]);
    y[2]=lcopy((GEN)res[6]); return y;
  }

  xarch=(GEN)bnf[3]; reg=(GEN)res[2];
  fu=getfu(nf,&xarch,reg,2,&c,gprecision(xarch));
  tetpil=avma; y=cgetg(3,t_VEC);
  y[1]=c?lmul((GEN)nf[7],fu):lcopy(fu); y[2]=lstoi(c);
  return gerepile(av,tetpil,y);
}

static long
factorgensimple(GEN nf,GEN ideal)
{
  long i,v,av1 = avma,lo;
  GEN x = dethnf_i(ideal);

  if (gcmp1(x)) { avma=av1; primfact[0]=0; return 1; }
  for (lo=0, i=1; i<lg(vectbase); i++)
  {
    GEN p1=(GEN)vectbase[i], p=(GEN)p1[1];
    if (!smodis(x,itos(p))) /* if p | x */
    {
      v=idealval(nf,ideal,p1);
      if (v)
      {
	lo++; primfact[lo]=i; expoprimfact[lo]=v;
	x = divii(x, gpuigs(p, v * itos((GEN)p1[4])));
	if (gcmp1(x)) { avma=av1; primfact[0]=lo; return 1; }
      }
    }
  }
  avma=av1; primfact[0]=lo; return 0;
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

/* factor x on vectbase (modulo principal ideals) */
static GEN
split_ideal(GEN nf, GEN x, GEN xar, long prec, GEN vperm)
{
  GEN id,vdir,x0,y,p1;
  long v1,v2,nbtest,bou,i, ru = lg(xar);
  int flag = (gexpo(gcoeff(x,1,1)) < 100);

  if (flag && factorgensimple(nf,x)) return xar;

  id = x; x0 = cgetg(3,t_VEC);
  x = gmul(x, lllintpartial(x));
  x0[1]=(long)x; x0[2]=(long)xar;
  y = ideallllred(nf,x0,NULL,prec);
  if (gcmp0((GEN)y[2]))
    { flag = !flag; x0[1] = (long)id; }
  else
    { flag = 1; x=(GEN)y[1]; }
  if (flag && factorgensimple(nf,x)) return (GEN)y[2];

  vdir = cgetg(ru,t_VEC);
  for (i=2; i<ru; i++) vdir[i]=zero;
  for (i=1; i<ru; i++)
  {
    vdir[i]=lstoi(10);
    y = ideallllred(nf,x0,vdir,prec); x=(GEN)y[1];
    if (factorgensimple(nf,x)) return (GEN)y[2];
    vdir[i]=zero;
  }
  v1=itos((GEN)vperm[1]);
  v2=itos((GEN)vperm[2]);
  for(nbtest = 0;;)
  {
    long ex1 = mymyrand() >> randshift;
    long ex2 = mymyrand() >> randshift;
    id=idealpowred_prime(nf,(GEN)vectbase[v1],stoi(ex1),prec);
    p1=idealpowred_prime(nf,(GEN)vectbase[v2],stoi(ex2),prec);
    id = idealmulh(nf,idealmul(nf,x0,id),p1);
    for (i=1; i<ru; i++) vdir[i] = lstoi(mymyrand() >> randshift);
    for (bou=1; bou<ru; bou++)
    {
      if (bou>1)
      {
        for (i=1; i<ru; i++) vdir[i]=zero;
        vdir[bou]=lstoi(10);
      }
      nbtest++;
      y = ideallllred(nf,id,vdir,prec); x=(GEN)y[1];
      if (DEBUGLEVEL>2)
        fprintferr("nbtest = %ld, ideal = %Z\n",nbtest,(long)x);
      if (factorgensimple(nf,x))
      {
        long l = primfact[0];
        add_to_fact(l,v1,-ex1);
        add_to_fact(l,v2,-ex2); return (GEN)y[2];
      }
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

/* assume x in HNF */
static GEN
isprincipalall0(GEN bnf, GEN x, long *ptprec, long flall)
{
  long i,j,colW,colB,N,R1,R2,RU,e,c, prec = *ptprec;
  GEN xalpha,yalpha,u2,y,p1,p2,p3,p4,xar,gen,cyc,u1inv,xc,ex;
  GEN W       = (GEN)bnf[1];
  GEN B       = (GEN)bnf[2];
  GEN matunit = (GEN)bnf[3];
  GEN vperm   = (GEN)bnf[6];
  GEN nf      = (GEN)bnf[7];
  GEN RES     = (GEN)bnf[8];
  GEN clg2    = (GEN)bnf[9];

  vectbase = (GEN)bnf[5]; /* needed by factorgensimple */

  N=lgef(nf[1])-3;
  R1=itos(gmael(nf,2,1)); R2=(N-R1)>>1; RU=R1+R2;
  xc = content(x); if (!gcmp1(xc)) x=gdiv(x,xc);

  colW=lg(W)-1; colB=lg(B)-1;
  xar=cgetg(RU+1,t_VEC); for (i=1; i<=RU; i++) xar[i]=zero;
  p1 = split_ideal(nf,x,xar,prec,vperm);
  if (p1 != xar) xar = cleancol(p1,N,prec);

  xalpha=cgetg(colW+1,t_COL); for (i=1; i<=colW; i++) xalpha[i]=zero;
  yalpha=cgetg(colB+1,t_COL); for (i=1; i<=colB; i++) yalpha[i]=zero;
  get_split_expo(xalpha,yalpha,vperm);

  u1inv= (GEN)clg2[1]; /* 1/u1, we have u1*W*u2=diag(cyc_i) */
  u2   = (GEN)clg2[2];
  cyc = gmael(RES,1,2);
  gen = gmael(RES,1,3);

  /* p1 unused otherwise */
  if (colW) p1 = gauss(u1inv, gsub(xalpha, gmul(B,yalpha)));
  p4 = cgetg(colW+colB+1,t_COL); c = lg(cyc)-1;
  ex = cgetg(c+1,t_COL);
  for (i=1; i<=c; i++)
    p4[i] = (long)truedvmdii((GEN)p1[i],(GEN)cyc[i],(GEN*)(ex+i));
  if (!(flall & nf_GEN)) return gcopy(ex);

{
  GEN col, baseclorig = (GEN)clg2[3];
  GEN M=gmael(nf,5,1), M2,s,s2;
  GEN Bc = dummycopy((GEN)bnf[4]);

  for (; i<=colW; i++) p4[i]=p1[i];
  for (; i<=colW+colB; i++) p4[i]=yalpha[i-colW];
  p2=cgetg(colW+1,t_MAT);
  for (i=1; i<=colW; i++) p2[i]=Bc[i];
  p3=gmul(p2,u2);
  for (i=1; i<=colW; i++) Bc[i]=p3[i];
  settyp(xar,t_COL); col=gsub(gmul(Bc,p4),xar);
  p4=cgetg(c+1,t_MAT);
  for (j=1; j<=c; j++)
  {
    GEN dmin,pmin,d;
    pmin = p2 = (GEN)baseclorig[j];
    dmin = dethnf((GEN)p2[1]);
    p1 = idealinv(nf,p2);
    p1[1]=(long)numer((GEN)p1[1]);

    d=dethnf((GEN)p1[1]);
    if (mpcmp(d,dmin) < 0) { pmin=p1; dmin=d; }
    p1 = ideallllred(nf,p1,NULL,prec);
    d = dethnf((GEN)p1[1]);
    if (mpcmp(d,dmin) < 0) pmin = p1;

    if (!gegal((GEN)pmin[1], (GEN)gen[j]))
      err(bugparier,"isprincipal(1)");
    p4[j]=lneg((GEN)pmin[2]); settyp(p4[j],t_COL);
  }
  if (c) col = gadd(col,gmul(p4,ex));
  col = cleancol(col,N,prec);

  if (RU > 1)
  {
    s=gzero; p4=cgetg(RU+1,t_MAT);
    for (j=1; j<RU; j++)
    {
      p2=cgetg(RU+1,t_COL); p4[j]=(long)p2;
      p1=gzero;
      for (i=1; i<RU; i++)
      {
        p2[i] = lreal(gcoeff(matunit,i,j));
        p1 = gadd(p1, gsqr((GEN)p2[i]));
      }
      p2[RU]=zero; if (gcmp(p1,s)>0) s=p1;
    }
    p2=cgetg(RU+1,t_COL); p4[RU]=(long)p2;
    for (i=1; i<RU; i++) p2[i]=lreal((GEN)col[i]);
    s=gsqrt(gmul2n(s,RU+1),prec);
    if (gcmpgs(s,100000000)<0) s=stoi(100000000);
    p2[RU]=(long)s;

    p4=(GEN)lll(p4,prec)[RU];
    if (signe(p4[RU]) < 0) p4 = gneg_i(p4);
    if (!gcmp1((GEN)p4[RU])) err(bugparier,"isprincipal(2)");
    setlg(p4,RU);
    col = gadd(col, gmul(matunit,p4));
  }

  s2 = gun;
  for (j=1; j<=c; j++)
    if (signe(ex[j]))
      s2 = mulii(s2, powgi(dethnf_i((GEN)gen[j]), (GEN)ex[j]));
  s = gdivgs(glog(gdiv(dethnf_i(x),s2),prec), N);
  p4 = cgetg(N+1,t_COL);
  for (i=1; i<=R1; i++) p4[i]=lexp(gadd(s,(GEN)col[i]),prec);
  for (   ; i<=RU; i++)
  {
    p4[i]=lexp(gadd(s,gmul2n((GEN)col[i],-1)),prec); ;
    p4[i+R2]=lconj((GEN)p4[i]);
  }
  M2=cgetg(N+1,t_MAT);
  for (j=1; j<=N; j++)
  {
    p1=cgetg(N+1,t_COL); M2[j]=(long)p1;
    for (i=1; i<=R1; i++) p1[i]=coeff(M,i,j);
    for (   ; i<=RU; i++)
    {
      p1[i]=coeff(M,i,j);
      p1[i+R2]=lconj((GEN)p1[i]);
    }
  }
  p1 = gdiv(grndtoi(gmul(s2,greal(gauss(M2,p4))),&e), s2);
  if (e < -5)
  {
    p3 = p1;
    if (!c) p3=idealhermite(nf,p3);
    else
      for (j=1; j<=c; j++)
        p3 = idealmul(nf,p3,idealpow(nf,(GEN)gen[j],(GEN)ex[j]));
    if (!gegal(x,p3)) e=0;
  }
  y=cgetg(4,t_VEC); y[1]=lcopy(ex);
  if (e < -5) { y[2]=lmul(xc,p1); y[3]=lstoi(-e); }
  else
  {
    if (flall & nf_FORCE)
    {
      if (DEBUGLEVEL)
        err(warner,"precision too low for generators, e = %ld",e);
      *ptprec = prec + (e >> TWOPOTBITS_IN_LONG) + (MEDDEFAULTPREC-2);
      return NULL;
    }
    err(warner,"insufficient precision for generators, not given");
    y[2]=lgetg(1,t_COL); y[3]=zero;
  }
}
  return y;
}

static GEN
triv_gen(GEN nf, GEN x, long c, long flag)
{
  GEN y;
  if (!(flag & nf_GEN)) return cgetg(1,t_COL);
  y = cgetg(4,t_VEC);
  y[1] = (long)zerocol(c);
  x = (typ(x) == t_COL)? gcopy(x): algtobasis(nf,x);
  y[2] = (long)x;
  y[3] = lstoi(BIGINT); return y;
}

static long
prec_unit_matrix(GEN bnf)
{
  GEN a = (GEN)bnf[4];
  long i,prec;

  for (i=1; ; i++)
    if ( (prec = gprecision((GEN)a[i])) ) return prec;
  err(bugparier,"prec_unit_matrix");
  return 0; /* not reached */
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

  pr = prec_unit_matrix(bnf); /* precision of unit matrix */
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
  ex = ground(gauss(greal(logunit), get_arch_real(nf,x,&emb, MEDDEFAULTPREC)));
  if (!gcmp0((GEN)ex[RU]))
    err(talker,"insufficient precision in isunit");

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

static GEN
quad_form(GEN *cbase,GEN ideal,GEN T2vec,GEN prvec)
{
  long i;
  for (i=1; i<lg(T2vec); i++)
  {
    long prec = prvec[i];
    GEN p1,T2 = (GEN)T2vec[i];

    p1 = qf_base_change(T2,gmul(ideal,realun(prec)), 0);
    if ((*cbase=lllgramintern(p1,100,1,prec)) == NULL)
    {
      if (DEBUGLEVEL) err(warner, "prec too low in quad_form(1): %ld",prec);
      continue;
    }
    if (DEBUGLEVEL>6)
    {
      fprintferr(" input matrix for lllgram: %Z\n",(long)p1);
      fprintferr(" lllgram output (prec = %ld): %Z\n",prec,(long)*cbase);
    }
    p1 = sqred1intern(qf_base_change(p1,*cbase,1),1);
    if (p1) return p1;
    if (DEBUGLEVEL) err(warner, "prec too low in quad_form(2): %ld",prec);
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

void minim_alloc(long n,double ***q,long **x,double **y,double **z,double **v);

static long
small_norm_for_buchall(long t,long **mat,GEN matarch,long nbrel,long LIMC,
		       long PRECREG,GEN nf,GEN gborne,long nbrelpid,GEN invp,
		       GEN L)
{
  const double eps = 0.000001;
  double *y,*zz,**qq,*vv, MINKOVSKI_BOUND,IDEAL_BOUND,normideal;
  long av=avma,av1,av2,tetpil,limpile, *x,i,j,k,noideal;
  long nbsmallnorm,nbsmallfact,R1,RU, N = lgef(nf[1])-3;
  GEN V,alpha,M,T2,ideal,rrr,cbase,T2vec,prvec,oldinvp;

  if (gsigne(gborne)<=0) return t;
  if (DEBUGLEVEL)
  {
    fprintferr("\n#### Looking for %ld relations (small norms)\n",nbrel);
    flusherr();
  }
  alpha = NULL; /* gcc -Wall */
  nbsmallnorm = nbsmallfact = 0;
  R1=itos(gmael(nf,2,1)); RU = R1 + itos(gmael(nf,2,2));
  M = gmael(nf,5,1); T2 = gmael(nf,5,3);
  prvec=cgetg(3,t_VECSMALL);
  prvec[1]=(PRECREG>BIGDEFAULTPREC)? (PRECREG>>1)+1: DEFAULTPREC;
  prvec[2]=PRECREG;
  T2vec=cgetg(3,t_VEC);
  T2vec[1]=(long)gprec_w(T2,prvec[1]);
  T2vec[2]=(long)T2;
  minim_alloc(N+1, &qq, &x, &y, &zz, &vv);
  V=new_chunk(KC+1); av1=avma;
  MINKOVSKI_BOUND = get_minkovski(N,R1,(GEN)nf[3],gborne);
  for (noideal=1; noideal<=KC; noideal++)
  {
    long flbreak = 0, nbrelideal=0;

    ideal=(GEN)vectbase[KC+1-noideal];
    if (DEBUGLEVEL>1)
    {
      fprintferr("\n*** Ideal no %ld: S = %ld, prime = %Z, ideal =",
                  noideal, t, ideal[1]);
      outerr(ideal);
    }
    normideal = gtodouble(powgi((GEN)ideal[1],(GEN)ideal[4]));
    IDEAL_BOUND = MINKOVSKI_BOUND*pow(normideal,2./(double)N);
    ideal = prime_to_ideal(nf,ideal);
    if ((rrr = quad_form(&cbase,ideal,T2vec,prvec)) == NULL)
      return -1; /* precision problem */

    for (k=1; k<=N; k++)
    {
      vv[k]=gtodouble(gcoeff(rrr,k,k));
      for (j=1; j<k; j++) qq[j][k]=gtodouble(gcoeff(rrr,j,k));
      if (DEBUGLEVEL>3) fprintferr("vv[%ld]=%.0f ",k,vv[k]);
    }
    if (DEBUGLEVEL>1)
    {
      if (DEBUGLEVEL>3) fprintferr("\n");
      fprintferr("IDEAL_BOUND = %.0f\n",IDEAL_BOUND); flusherr();
    }
    IDEAL_BOUND += eps; av2=avma; limpile = stack_lim(av2,1);
    x[0]=k=N; y[N]=zz[N]=0; x[N]= (long) sqrt(IDEAL_BOUND/vv[N]);
    for(;; x[1]--)
    {
      GEN p1, *newcol;
      long *colt, av3 = avma;
      double p;

      for(;;) /* looking for primitive element of small norm */
      {
	if (k>1)
	{
	  long l = k-1; /* need to define `l' for NeXTgcc 2.5.8 */
	  zz[l]=0;
	  for (j=k; j<=N; j++) zz[l] += qq[l][j]*x[j];
	  p=x[k]+zz[k];
	  y[l]=y[k]+p*p*vv[k];
	  x[l]=(long) floor(sqrt((IDEAL_BOUND-y[l])/vv[l])-zz[l]);
          k=l;
	}
	for(;;)
	{
	  p=x[k]+zz[k];
	  if (y[k] + vv[k]*p*p <= IDEAL_BOUND) break;
	  k++; x[k]--;
	}
	if (k==1) /* element complete */
	{
	  if (!x[1] && y[1]<=eps) { flbreak=1; break; }
	  if (ccontent(x)==1) /* primitive */
	  {
	    alpha=gmul(ideal,gmul_mat_smallvec(cbase,x));
	    j=N; while (j>=2 && !signe(alpha[j])) --j;
	    if (j!=1)
	    {
              long av4 = avma;
	      if (DEBUGLEVEL)
	      {
		if (DEBUGLEVEL>1)
		{
		  fprintferr(".");
		  if (DEBUGLEVEL>7)
		  {
		    GEN gx = cgetg(N+1,t_COL);
		    outerr(gdiv(idealnorm(nf,alpha), idealnorm(nf,ideal)));
		    for (i=1; i<=N; i++) gx[i] = lstoi(x[i]);
		    outerr(qfeval(rrr,gx));
		  }
		}
		nbsmallnorm++; flusherr();
	      }
              /* can factor it ? */
	      if (factorisealpha(nf,alpha,KCZ,LIMC)) { avma = av4; break; }
	    }
	    avma=av3;
	  }
	  x[1]--;
	}
      }
      if (flbreak) { flbreak=0; break; }

      oldinvp = invp;
      if (t && t < KC)
      {
	for (i=1; i<=KC; i++) V[i]=0;
	for (i=1; i<=primfact[0]; i++) V[primfact[i]] = expoprimfact[i];
	
        if (! addcolumntomatrix(V,invp,L))
        {
          if (DEBUGLEVEL>1) { fprintferr("*"); flusherr(); }
          avma = av3; continue;
        }
      }

      /* record the new relation */
      t++; newcol=(GEN*)matarch[t]; colt=mat[t];
        colt[0] = primfact[1]; /* for already_found_relation */
      for (i=1; i<=primfact[0]; i++) colt[primfact[i]] = expoprimfact[i];

      p1 = gmul(M, alpha);
      for (i=1; i<=R1; i++)
        gaffect(glog((GEN)p1[i],PRECREG), newcol[i]);
      for (   ; i<=RU; i++)
        gaffect(gmul2n(glog((GEN)p1[i],PRECREG),1), newcol[i]);

	if (DEBUGLEVEL)
	{
	  if (DEBUGLEVEL==1) fprintferr("%4ld",t);
	  else
	  {
	    fprintferr("t = %ld. ",t);
	    if (DEBUGLEVEL>2) outerr(alpha);
            wr_rel(colt);
	  }
	  flusherr(); nbsmallfact++;
	}
	if (t>=nbrel) { flbreak=1; break; }
      if (++nbrelideal == nbrelpid) break;

      if (low_stack(limpile, stack_lim(av2,1)))
      {
	if(DEBUGMEM>1) err(warnmem,"small_norm");
        invp = gerepileupto(av2, gcopy(invp));
      }
    }
    if (flbreak) break;
    tetpil=avma; invp=gerepile(av1,tetpil,gcopy(invp));
    if (DEBUGLEVEL>1) msgtimer("for this ideal");
  }
  if (DEBUGLEVEL)
  {
    fprintferr("\n");
    msgtimer("small norm relations");
    if (DEBUGLEVEL>1)
    {
      GEN p1,tmp=cgetg(t+1,t_MAT);

      fprintferr("Elements of small norm gave %ld relations.\n",t);
      fprintferr("Computing rank :"); flusherr();
      for(j=1;j<=t;j++)
      {
	p1=cgetg(KC+1,t_COL); tmp[j]=(long)p1;
	for(i=1;i<=KC;i++) p1[i]=lstoi(mat[j][i]);
      }
      tmp = (GEN)indexrank(tmp)[2]; k=lg(tmp)-1;
      fprintferr("rank = %ld; independent columns:\n",k);
      for (i=1; i<=k; i++) fprintferr("%4ld",itos((GEN)tmp[i]));
      fprintferr("\n");
    }
    if(nbsmallnorm)
      fprintferr("\nnb. fact./nb. small norm = %ld/%ld = %f\n",
               nbsmallfact,nbsmallnorm,((double)nbsmallfact)/nbsmallnorm);
    else
      fprintferr("\nnb. small norm = 0\n");
  }
  avma=av; return t;
}

/* I assumed to be integral HNF */
static GEN
ideallllredpart1(GEN nf, GEN I, GEN matt2, long N, long PRECREGINT)
{
  GEN y,m,idealpro;

  if (!gcmp1(gcoeff(I,N,N))) { y=content(I); if (!gcmp1(y)) I=gdiv(I,y); }
  y = lllgramintern(qf_base_change(matt2,I,1),100,1,PRECREGINT+1);
  if (!y) return NULL;

  /* I, m, y integral */
  m = gmul(I,(GEN)y[1]);
  if (isnfscalar(m)) m = gmul(I,(GEN)y[2]);

  idealpro = cgetg(4,t_VEC);
  idealpro[1] = (long)I;
  idealpro[2] = (long)m; /* elt of small (weighted) T2 norm in I */
  idealpro[3] = labsi( subres(gmul((GEN)nf[7],m), (GEN)nf[1]) ); /* |Nm| */
  if (DEBUGLEVEL>5) fprintferr("\nidealpro = %Z\n",idealpro);
  return idealpro;
}

static void
ideallllredpart2(GEN colarch, GEN nf, GEN arch, GEN gamma, long prec)
{
  GEN v = get_arch(nf,gamma,prec);
  long i;
  for (i=lg(v)-1; i; i--)
    gaffect(gadd((GEN)arch[i],gneg((GEN)v[i])), (GEN)colarch[i]);
}

static void
dbg_newrel(long jideal, long jdir, long phase, long cmptglob, long *col,
           GEN colarch, long lim)
{
  fprintferr("\n++++ cmptglob = %ld: new relation (need %ld)", cmptglob, lim);
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
dbg_cancelrel(long i,long jideal,long jdir,long phase, long *col)
{
  fprintferr("rel. cancelled. phase %ld: %ld ",phase,i);
  if (DEBUGLEVEL>3) fprintferr("(jideal=%ld,jdir=%ld)",jideal,jdir);
  wr_rel(col); flusherr();
}

static void
dbg_outrel(long phase,long cmptglob, GEN vperm,long **ma,GEN maarch)
{
  long av,i,j;
  GEN p1,p2;

  if (phase == 0)
  {
    av=avma; p2=cgetg(cmptglob+1,t_MAT);
    for (j=1; j<=cmptglob; j++)
    {
      p1=cgetg(KC+1,t_COL); p2[j]=(long)p1;
      for (i=1; i<=KC; i++) p1[i]=lstoi(ma[j][i]);
    }
    fprintferr("\nRank = %ld, time = %ld\n",rank(p2),timer2());
    if (DEBUGLEVEL>3)
    {
      fprintferr("relations = \n");
      for (j=1; j <= cmptglob; j++) wr_rel(ma[j]);
      fprintferr("\nmatarch = %Z\n",maarch);
    }
    avma=av;
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

/* check if we already have a column mat[l] equal to mat[s] */
static long
already_found_relation(long **mat,long s)
{
  long l,bs,cl,*coll,*cols = mat[s];

  bs=1; while (bs<=KC && !cols[bs]) bs++;
  if (bs>KC) return s; /* zero relation */

#if 0
  /* Could check for colinearity and replace by gcd. Useless in practice */
  cs=cols[bs];
  for (l=s-1; l; l--)
  {
    coll=mat[l]; cl=coll[0]; /* = index of first non zero elt in coll */
    if (cl==bs)
    {
      long b=bs;
      cl=coll[cl];
      do b++; while (b<=KC && cl*cols[b] == cs*coll[b]);
      if (b>KC) return l;
    }
  }
#endif
  for (l=s-1; l; l--)
  {
    coll=mat[l]; cl=coll[0]; /* = index of first non zero elt in coll */
    if (cl==bs)
    {
      long b=bs;
      do b++; while (b<=KC && cols[b] == coll[b]);
      if (b>KC) return l;
    }
  }
  cols[0]=bs; return 0;
}

/* if phase != 1 re-initialize static variables. If <0 return immediately */
static long
random_relation(long phase,long cmptglob,long lim,long LIMC,long N,
                long PRECREG,long PRECREGINT,GEN nf,GEN subfb,GEN lmatt2,
		long **ma,GEN maarch,long *ex,GEN list_jideal)
{
  static long jideal, jdir;
  long i,av,av1,cptzer,nbmatt2,lgsub, jlist = 1, *col;
  GEN colarch,ideal,idealpro,P;

  if (phase != 1) { jideal=jdir=1; if (phase<0) return 0; }
  nbmatt2 = lg(lmatt2)-1;
  lgsub = lg(subfb);
  cptzer = 0;
  if (DEBUGLEVEL && list_jideal)
    fprintferr("looking hard for %Z\n",list_jideal);
  P = NULL; /* gcc -Wall */
  for (av = avma;;)
  {
    if (list_jideal && jlist < lg(list_jideal) && jdir <= nbmatt2) 
      jideal = list_jideal[jlist++];
    if (!list_jideal || jdir <= nbmatt2)
    {
      avma = av;
      P = prime_to_ideal(nf, (GEN)vectbase[jideal]);
    }
    ideal = P;
    do {
      for (i=1; i<lgsub; i++)
      {
        ex[i] = mymyrand()>>randshift;
        if (ex[i])
          ideal = idealmulh(nf,ideal, gmael(powsubfb,i,ex[i]));
      }
    }
    while (typ(ideal)==t_MAT); /* If ex  = 0, try another */
  
    if (phase != 1) jdir = 1; else phase = 2;
    for (av1 = avma; jdir <= nbmatt2; jdir++, avma = av1)
    { /* reduce along various directions */
      if (DEBUGLEVEL>2)
        fprintferr("phase=%ld,jideal=%ld,jdir=%ld,rand=%ld\n",
                   phase,jideal,jdir,getrand());
      idealpro = ideallllredpart1(nf,(GEN)ideal[1], (GEN)lmatt2[jdir],
                                  N, PRECREGINT);
      if (!idealpro) return -2;
      if (!factorisegen(nf,idealpro,KCZ,LIMC))
      {
        if (DEBUGLEVEL>1) { fprintferr("."); flusherr(); }
        continue;
      }
      /* can factor ideal, record relation */
      col = ma[++cmptglob];
      for (i=1; i<lgsub; i++) col[subfb[i]] = -ex[i];
      for (i=1; i<=primfact[0]; i++) col[primfact[i]] += expoprimfact[i];
      col[jideal]--;
      i = already_found_relation(ma,cmptglob);
      if (i)
      { /* already known. Forget it */
        if (DEBUGLEVEL>1) dbg_cancelrel(i,jideal,jdir,phase,col);
        cmptglob--; for (i=1; i<=KC; i++) col[i]=0;
        if (++cptzer > MAXRELSUP)
        {
          if (list_jideal) { cptzer -= 10; break; }
          return -1;
        }
        continue;
      }

      /* Record archimedian part */
      cptzer=0; colarch = (GEN)maarch[cmptglob];
      ideallllredpart2(colarch,nf,(GEN)ideal[2],(GEN)idealpro[2],PRECREG);
      if (DEBUGLEVEL)
        dbg_newrel(jideal,jdir,phase,cmptglob,col,colarch,lim);

      /* Need more, try next P */
      if (cmptglob < lim) break;

      /* We have found enough. Return */
      if (phase)
      {
        jdir = 1;
        if (jideal == KC) jideal=1; else jideal++;
      }
      else if (DEBUGLEVEL>2)
        fprintferr("Upon exit: jideal=%ld,jdir=%ld\n",jideal,jdir);
      avma = av; return cmptglob;
    }
    if (!list_jideal)
    {
      if (jideal == KC) jideal=1; else jideal++;
    }
  }
}

static long
be_honest(GEN nf,GEN subfb,long RU,long PRECREGINT)
{
  long av,ex,i,j,k,iz,nbtest, N = lgef(nf[1])-3, lgsub = lg(subfb);
  GEN exu=new_chunk(RU+1), MCtw = cgetg(RU+1,t_MAT);
  GEN p1,p2,ideal,idealpro, MC = gmael(nf,5,2), M = gmael(nf,5,1);

  if (DEBUGLEVEL)
  {
    fprintferr("Be honest for primes from %ld to %ld\n",
		factorbase[KCZ+1],factorbase[KCZ2]);
    flusherr();
  }
  av=avma;
  for (iz=KCZ+1; iz<=KCZ2; iz++)
  {
    p1=idealbase[numfactorbase[factorbase[iz]]];
    if (DEBUGLEVEL>1) fprintferr("%ld ", factorbase[iz]);
    for (j=1; j<lg(p1); j++)
      for(nbtest=0;;)
      {
	ideal = prime_to_ideal(nf,(GEN)p1[j]);
	for (i=1; i<lgsub; i++)
	{
	  ex = mymyrand()>>randshift;
	  if (ex) ideal = idealmulh(nf,ideal,gmael3(powsubfb,i,ex,1));
	}
	for (k=1; k<=RU; k++)
	{
	  if (k==1)
            for (i=1; i<=RU; i++) exu[i] = mymyrand()>>randshift;
          else
	  {
	    for (i=1; i<=RU; i++) exu[i] = 0;
            exu[k] = 10;
	  }
          for (i=1; i<=RU; i++)
            MCtw[i] = exu[i]? lmul2n((GEN)MC[i],exu[i]<<1): MC[i];
          p2 = mulmat_real(MCtw,M);
          idealpro = ideallllredpart1(nf,ideal,p2,N,PRECREGINT);
          if (idealpro &&
	      factorisegen(nf,idealpro,iz-1,factorbase[iz-1])) break;
	  nbtest++; if (nbtest==20) return 0;
	}
	avma=av; if (k <= RU) break;
      }
  }
  if (DEBUGLEVEL)
  {
    if (DEBUGLEVEL>1) fprintferr("\n");
    msgtimer("be honest");
  }
  avma=av; return 1;
}

int
trunc_error(GEN x)
{
  return typ(x)==t_REAL && signe(x)
                        && (expo(x)>>TWOPOTBITS_IN_LONG) + 3 > lg(x);
}

/* xarch = complex logarithmic embeddings of units (u_j) found so far */
static GEN
compute_multiple_of_R(GEN xarch,long RU,long N,long PRECREG, GEN *ptsublambda)
{
  GEN v,mdet,Im_mdet,kR,sublambda,lambda,xreal;
  GEN *gptr[2];
  long av = avma, i,j, sreg = lg(xarch)-1, R1 = 2*RU - N;

  if (DEBUGLEVEL) { fprintferr("\n#### Computing regulator\n"); flusherr(); }
  /* xreal = (log |sigma_i(u_j)|) */
  xreal=greal(xarch); v=cgetg(RU+1,t_COL);
  for (i=1; i<=R1; i++) v[i]=un;
  for (   ; i<=RU; i++) v[i]=deux;
  mdet=cgetg(sreg+2,t_MAT); mdet[1]=(long)v;
  for (j=2; j<=sreg+1; j++) mdet[j]=xreal[j-1];
  /* det(Span(mdet)) = N * R */
  Im_mdet = imagereel(mdet,PRECREG);
  if (DEBUGLEVEL) msgtimer("imagereel");

  /* check we have full rank for units */
  if (lg(Im_mdet) != RU+1) { avma=av; return NULL; }
  /* integral multiple of R: the cols we picked form a Q-basis, they have an
   * index in the full lattice */
  kR = gdivgs(det2(Im_mdet), N);
  if (DEBUGLEVEL) msgtimer("detreel");
  /* R > 0.2 uniformly */
  if (gexpo(kR) < -3) { avma=av; return NULL; }

  kR = mpabs(kR);
  sublambda = cgetg(sreg+1,t_MAT);
  lambda = gauss(Im_mdet,xreal); /* rational entries */
  for (i=1; i<=sreg; i++)
  {
    GEN p1 = cgetg(RU,t_COL), p2 = (GEN)lambda[i];
    sublambda[i] = (long)p1;
    for (j=1; j<RU; j++)
    {
      p1[j] = p2[j+1];
      if (trunc_error((GEN)p1[j])) { *ptsublambda = NULL; return gzero; }
    }
  }
  if (DEBUGLEVEL) msgtimer("gauss & lambda");
  *ptsublambda = sublambda;
  gptr[0]=ptsublambda; gptr[1]=&kR;
  gerepilemany(av,gptr,2); return kR;
}

/* Assuming enough relations, c = Rz is close to an even integer, according
 * to Dirichlet's formula. Otherwise, close to a multiple.
 * Compute a tentative regulator (not a multiple this time) */
static GEN
compute_check(GEN sublambda, GEN z, GEN *parch, GEN *reg)
{
  long av = avma, av2, tetpil;
  GEN p1,c,den, R = *reg; /* multiple of regulator */

  if (DEBUGLEVEL) { fprintferr("\n#### Computing check\n"); flusherr(); }
  c = gmul(R,z);
  sublambda = bestappr(sublambda,c); den = denom(sublambda);
  if (gcmp(den,c) > 0)
  {
    if (DEBUGLEVEL) fprintferr("c = %Z\nden = %Z\n",c,den);
    avma=av; return NULL;
  }

  p1 = gmul(sublambda,den); tetpil=avma;
  *parch = lllint(p1);

  av2=avma; p1 = det2(gmul(sublambda,*parch));
  affrr(mpabs(gmul(R,p1)), R); avma=av2;

  if (DEBUGLEVEL) msgtimer("bestappr/regulator");
  *parch = gerepile(av,tetpil,*parch); return gmul(R,z);
}

/* U W V = D, Ui = U^(-1) */
GEN
compute_class_number(GEN W, GEN *D,GEN *Ui,GEN *V)
{
  GEN S = smith2(W);

  if (DEBUGLEVEL) { fprintferr("#### Computing class number\n"); flusherr(); }
  *Ui= ginv((GEN)S[1]);
  *V = (GEN)S[2];
  *D = (GEN)S[3];
  if (DEBUGLEVEL>=4) msgtimer("smith/class group");
  return dethnf_i(*D);
}

static void
class_group_gen(GEN nf,GEN cyc,GEN clh,GEN u1,GEN u2,GEN vperm,
                GEN *ptclg1,GEN *ptclg2, long prec)
{
  GEN basecl,baseclorig,I,J,p1,dmin,d, Vbase = vectbase;
  long i,j,s,inv, lo = lg(cyc), lo0 = lo;

  if (DEBUGLEVEL)
    { fprintferr("#### Computing class group generators\n"); flusherr(); }
  if (vperm)
  {
    s = lg(Vbase); Vbase = cgetg(s,t_VEC);
    for (i=1; i<s; i++) Vbase[i] = vectbase[vperm[i]];
  }
  if (typ(cyc) == t_MAT)
  { /* diagonal matrix */
    p1 = cgetg(lo,t_VEC);
    for (j=1; j<lo; j++)
    {
      p1[j] = coeff(cyc,j,j);
      if (gcmp1((GEN)p1[j])) break;
    }
    lo0 = lo; lo = j;
    cyc = p1; setlg(cyc, lo);
  }
  baseclorig = cgetg(lo,t_VEC); /* generators = Vbase * u1 (LLL-reduced) */
  basecl = cgetg(lo,t_VEC);
  for (j=1; j<lo; j++)
  {
    p1 = gcoeff(u1,1,j);
    I = idealpowred_prime(nf,(GEN)Vbase[1],p1,prec);
    if (signe(p1)<0) I[1] = lmul((GEN)I[1],denom((GEN)I[1]));
    for (i=2; i<lo0; i++)
    {
      p1=gcoeff(u1,i,j); s=signe(p1);
      if (s)
      {
	J = idealpowred_prime(nf,(GEN)Vbase[i],p1,prec);
        if (s<0) J[1] = lmul((GEN)J[1],denom((GEN)J[1]));
	I = idealmulh(nf,I,J);
	I = ideallllred(nf,I,NULL,prec);
      }
    }
    baseclorig[j]=(long)I; I=(GEN)I[1]; /* I = a generator, order cyc[j] */
    dmin = dethnf_i(I); J = idealinv(nf,I);
    J = gmul(J,denom(J));
    d = dethnf_i(J);
    /* check if J = denom * I^(-1) has smaller norm */
    if (cmpii(d,dmin) < 0) { inv=1; I=J; dmin=d; }
    else                   { inv=0; }
    /* try reducing (may _increase_ the norm) */
    J = ideallllred(nf,J,NULL,prec);
    d = dethnf_i(J);
    if (cmpii(d,dmin) < 0) { inv=1; I=J; }
    basecl[j] = (long)I;
    if (inv)
    {
      u1[j] = lneg((GEN)u1[j]);
      u2[j] = lneg((GEN)u2[j]);
    }
  }
  p1 = cgetg(4,t_VEC);
  p1[1]=(long)clh;
  p1[2]=(long)cyc;
  p1[3]=(long)basecl; *ptclg1 = p1;
  /* W*u2 = u1*diag(cyc) */
  p1 = cgetg(4,t_VEC);
  p1[1]=(long)u1;
  p1[2]=(long)u2;
  p1[3]=(long)baseclorig; *ptclg2 = p1;
  if (DEBUGLEVEL) msgtimer("classgroup generators");
}

static GEN
compute_matt2(long RU,GEN nf)
{
  GEN matt2, MCcopy, MCshif, M = gmael(nf,5,1), MC = gmael(nf,5,2);
  long i,j,k,n = min(RU,9), N = n*(n+1)/2, ind = 1;

  MCcopy=cgetg(RU+1,t_MAT); MCshif=cgetg(n+1,t_MAT);
  for (k=1; k<=RU; k++) MCcopy[k]=MC[k];
  for (k=1; k<=n; k++) MCshif[k]=lmul2n((GEN)MC[k],20);
  matt2=cgetg(N+1,t_VEC);
  for (j=1; j<=n; j++)
  {
    MCcopy[j]=MCshif[j];
    for (i=1; i<=j; i++)
    {
      MCcopy[i]=MCshif[i];
      matt2[ind++] = (long)mulmat_real(MCcopy,M);
      MCcopy[i]=MC[i];
    }
    MCcopy[j]=MC[j];
  }
  if (DEBUGLEVEL) msgtimer("weighted T2 matrices");
  return matt2;
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
relationrank(long **A, long r, GEN L)
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
      invp = gerepileupto(av, gcopy(invp));
    }
  }
  return gerepileupto(av, gcopy(invp));
}

static void
classintern(GEN nf,GEN W,GEN *ptcl, GEN *ptcl2)
{
  long prec = (long)nfnewprec(nf,-1);
  GEN met,u1,u2, clh = compute_class_number(W,&met,&u1,&u2);
  class_group_gen(nf,met,clh,u1,u2,NULL,ptcl,ptcl2, prec);
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
  long n,indi,av=avma,tetpil;
  GEN p,rem,p1;

  n=lg(nf[7])-1; p=dvmdis(co,n,&rem); indi=itos(rem)+1;
  p1=primedec(nf,p); tetpil=avma;
  return gerepile(av,tetpil,gcopy((GEN)p1[indi]));
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
  GEN cyc,gen,h,nf;
  long i, l;

  h = get_cycgen((GEN)bnf[10]);
  if (h) return h;

  cyc = gmael3(bnf,8,1,2);
  gen = gmael3(bnf,8,1,3);
  l = lg(gen); nf = checknf(bnf);
  h = cgetg(l, t_VEC);
  for (i=1; i<l; i++)
  {
    GEN p1 = idealpow(nf, (GEN)gen[i], (GEN)cyc[i]);
    h[i] = isprincipalgenforce(bnf,p1)[2];
  }
  return h;
}

/* compute principal ideals corresponding to bnf relations */
static GEN
makematal(GEN bnf)
{
  GEN W,B,pfb,vp,nf,ma;
  long lm,lma,j,k,prec;

  ma = get_matal((GEN)bnf[10]);
  if (ma) return ma;

  W=(GEN)bnf[1]; B=(GEN)bnf[2];
  vp=(GEN)bnf[6]; nf=(GEN)bnf[7];
  lm=(lg(W)>1)?lg(W[1])-1:0; lma=lm+lg(B);
  pfb=cgetg(lma,t_VEC); ma=(GEN)bnf[5]; /* reorder factor base */
  for (j=1; j<lma; j++) pfb[j] = ma[itos((GEN)vp[j])];
  ma = cgetg(lma,t_MAT);

  prec = prec_unit_matrix(bnf);
  for (j=1; j<lma; j++)
  {
    GEN ex = (j<=lm)? (GEN)W[j]: (GEN)B[j-lm];
    GEN id = (j<=lm)? gun: (GEN)pfb[j];
    for (k=1; k<=lm; k++)
      id = idealmul(nf,id,idealpow(nf,(GEN)pfb[k],(GEN)ex[k]));
    if (typ(id) != t_MAT) id = idealhermite(nf,id);
    for (;;)
    {
      long av1 = avma, c = getrand();
      GEN y = isprincipalall0(bnf,id,&prec, nf_GEN|nf_FORCE);
      if (y)
      {
        y = gerepileupto(av1, y);
        ma[j] = y[2]; break;
      }
      if (DEBUGLEVEL) err(warnprec,"makematal",prec);
      avma = av1; nf = nfnewprec(nf,prec);
      bnf = bnfinit0(nf,1,NULL,prec); setrand(c);
    }
  }
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
smallbuchinit(GEN pol,GEN gcbach,GEN gcbach2,GEN gRELSUP,GEN gborne,long nbrelpid,long minsfb,long prec)
{
  long av=avma,av1,k;
  GEN y,bnf,pfb,vp,nf,mas,res,uni,v1,v2,v3;

  if (typ(pol)==t_VEC) bnf = checkbnf(pol);
  else
  {
    bnf=buchall(pol,gcbach,gcbach2,gRELSUP,gborne,nbrelpid,minsfb,-3,prec);
    if (checkbnf(bnf) != bnf)
    {
      err(warner,"non-monic polynomial. Change of variables discarded");
      bnf = (GEN)bnf[1];
    }
  }
  pfb=(GEN)bnf[5]; vp=(GEN)bnf[6]; nf=(GEN)bnf[7];
  mas=(GEN)nf[5]; res=(GEN)bnf[8]; uni=(GEN)res[5];

  y=cgetg(13,t_VEC); y[1]=lcopy((GEN)nf[1]); y[2]=lcopy(gmael(nf,2,1));
  y[3]=lcopy((GEN)nf[3]); y[4]=lcopy((GEN)nf[7]);
  y[5]=lcopy((GEN)nf[6]); y[6]=lcopy((GEN)mas[5]);
  y[7]=lcopy((GEN)bnf[1]); y[8]=lcopy((GEN)bnf[2]);
  v1=cgetg(lg(pfb),t_VEC); y[9]=(long)v1;
  for (k=1; k<lg(pfb); k++)
    v1[k]=(long)codeprime(bnf,(GEN)pfb[itos((GEN)vp[k])]);
  v2=cgetg(3,t_VEC); y[10]=(long)v2;
  v2[1]=lcopy(gmael(res,4,1));
  v2[2]=(long)algtobasis(bnf,gmael(res,4,2));
  v3=cgetg(lg(uni),t_VEC); y[11]=(long)v3;
  for (k=1; k<lg(uni); k++)
    v3[k] = (long)algtobasis(bnf,(GEN)uni[k]);
  av1 = avma;
  y[12] = gcmp0((GEN)bnf[10])? lpileupto(av1, gcopy(makematal(bnf)))
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
get_mun(GEN funits, GEN ro, long ru, long r1, long prec)
{
  long j,k,av=avma,tetpil;
  GEN p1,p2, mun = cgetg(ru,t_MAT);

  for (k=1; k<ru; k++)
  {
    p1=cgetg(ru+1,t_COL); mun[k]=(long)p1;
    for (j=1; j<=ru; j++)
    {
      p2 = glog(poleval((GEN)funits[k],(GEN)ro[j]),prec);
      p1[j]=(j<=r1)? (long)p2: lmul2n(p2,1);
    }
  }
  tetpil=avma; return gerepile(av,tetpil,gcopy(mun));
}

static GEN
get_mc(GEN nf, GEN alphs, long prec)
{
  GEN mc,p1,p2,p3,p4, bas = (GEN)nf[7], pol = (GEN)nf[1], ro = (GEN)nf[6];
  long ru = lg(ro), n = lgef(pol)-3, r1 = itos(gmael(nf,2,1));
  long j,k, la = lg(alphs);

  mc = cgetg(la,t_MAT);
  for (k=1; k<la; k++)
  {
    p4 = gmul(bas,(GEN)alphs[k]);
    p3 = gdivgs(glog(gabs(subres(pol,p4),prec),prec), n);
    p1 = cgetg(ru,t_COL); mc[k] = (long)p1;
    for (j=1; j<ru; j++)
    {
      p2 = gsub(glog(poleval(p4,(GEN)ro[j]),prec), p3);
      p1[j]=(j<=r1)? (long) p2: lmul2n(p2,1);
    }
  }
  return mc;
}

static void
my_class_group_gen(GEN bnf, GEN *ptcl, GEN *ptcl2)
{
  GEN nf=(GEN)bnf[7], Vbase=(GEN)bnf[5], vperm=(GEN)bnf[6], *gptr[2];
  long av = avma, i, lv = lg(Vbase);

  vectbase = cgetg(lv, t_VEC);
  for (i=1; i<lv; i++) vectbase[i] = Vbase[itos((GEN)vperm[i])];
  classintern(nf,(GEN)bnf[1],ptcl,ptcl2);
  gptr[0]=ptcl; gptr[1]=ptcl2; gerepilemany(av,gptr,2);
}

GEN
bnfnewprec(GEN bnf, long prec)
{
  GEN nf,ro,res,p1,funits,mun,matal,clgp,clgp2,y;
  long av,r1,r2,ru,pl1,pl2,prec1;

  bnf = checkbnf(bnf);
  if (prec <= 0) return nfnewprec(checknf(bnf),prec);
  y = cgetg(11,t_VEC);
  funits = check_units(bnf,"bnfnewprec");
  nf = (GEN)bnf[7];
  ro = (GEN)nf[6];
  r1 = itos(gmael(nf,2,1));
  r2 = itos(gmael(nf,2,2));
  ru = r1 + r2;
  pl1 = (ru == 1 && r1 == 0)? 0: gexpo(funits);
  pl2 = gexpo(ro);
  prec1 = prec;
  prec += ((ru + r2 - 1) * (pl1 + (ru + r2) * pl2)) >> TWOPOTBITS_IN_LONG;
  nf = nfnewprec((GEN)bnf[7],prec);
  res = cgetg(7,t_VEC);
  ro = (GEN)nf[6];
  mun = get_mun(funits,ro,ru,r1,prec);
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
  av = avma;
  y[4]=lpileupto(av, gcopy(get_mc(nf,matal,prec)));
  y[5]=lcopy((GEN)bnf[5]);
  y[6]=lcopy((GEN)bnf[6]);
  y[7]=(long)nf;
  y[8]=(long)res;
  my_class_group_gen(y,&clgp,&clgp2);
  res[1]=(long)clgp;
  y[9]=(long)clgp2;
  y[10]=lcopy((GEN)bnf[10]); return y;
}

GEN
bnfmake(GEN sbnf, long prec)
{
  long av = avma, j,k,n,r1,r2,ru,lpf;
  GEN p1,p2,pol,bas,ro,m,mul,pok,M,MC,T2,mas,T,TI,nf,mun,funits;
  GEN pfc,vp,mc,clgp,clgp2,res,y,W,mata,racu,reg,matal;

  if (typ(sbnf)!=t_VEC || lg(sbnf)!=13)
    err(talker,"incorrect sbnf in bnfmake");
  pol=(GEN)sbnf[1]; bas=(GEN)sbnf[4]; n=lg(bas)-1;
  r1=itos((GEN)sbnf[2]); r2=(n-r1)/2; ru=r1+r2;
  ro=(GEN)sbnf[5];
  if (prec > gprecision(ro)) ro=get_roots(pol,r1,ru,prec);

  m=cgetg(n+1,t_MAT);
  for (k=1; k<=n; k++)
  {
    p1=cgetg(n+1,t_COL); m[k]=(long)p1; p2=(GEN)bas[k];
    for (j=1; j<=n; j++) p1[j]=(long)truecoeff(p2,j-1);
  }
  m=invmat(m);
  mul=cgetg(n*n+1,t_MAT);
  for (k=1; k<=n*n; k++)
  {
    pok = gres(gmul((GEN)bas[(k-1)%n+1], (GEN)bas[(long)((k-1)/n)+1]), pol);
    p1=cgetg(n+1,t_COL); mul[k]=(long)p1;
    for (j=1; j<=n; j++) p1[j]=(long)truecoeff(pok,j-1);
  }
  mul=gmul(m,mul);

  M  = make_M(n,ru,bas,ro);
  MC = make_MC(n,r1,ru,M);
  T2 = mulmat_real(MC,M);
  p1=mulmat_real(gconj(MC),M); T=ground(p1);
  if (gexpo(gnorml2(gsub(p1,T))) > -30)
    err(talker,"insufficient precision in bnfmake");
  TI=gmul((GEN)sbnf[3],invmat(T));

  mas=cgetg(8,t_VEC);
  nf=cgetg(10,t_VEC);
  p1=cgetg(3,t_VEC); p1[1]=lstoi(r1); p1[2]=lstoi(r2);
  nf[1]=sbnf[1]  ; nf[2]=(long)p1;  nf[3]=sbnf[3];
  nf[4]=ldet(m)  ; nf[5]=(long)mas; nf[6]=(long)ro;
  nf[7]=(long)bas; nf[8]=(long)m;   nf[9]=(long)mul;

  mas[1]=(long)M; mas[2]=(long)MC; mas[3]=(long)T2;
  mas[4]=(long)T; mas[5]=sbnf[6];  mas[6]=(long)TI;
  mas[7]=(long)make_MDI(nf,TI,&p1,&p2);

  funits=cgetg(ru,t_VEC); p1 = (GEN)sbnf[11];
  for (k=1; k < lg(p1); k++)
    funits[k] = lmul(bas,(GEN)p1[k]);
  mun = get_mun(funits,ro,ru,r1,prec);

  prec=gprecision(ro); if (prec<DEFAULTPREC) prec=DEFAULTPREC;
  matal = get_matal((GEN)sbnf[12]);
  if (!matal) matal = (GEN)sbnf[12];
  mc = get_mc(nf, matal, prec);

  pfc=(GEN)sbnf[9]; lpf=lg(pfc);
  vectbase=cgetg(lpf,t_COL); vp=cgetg(lpf,t_COL);
  for (j=1; j<lpf; j++)
  {
    vp[j]=lstoi(j);
    vectbase[j]=(long)decodeprime(nf,(GEN)pfc[j]);
  }
  classintern(nf,(GEN)sbnf[7], &clgp, &clgp2); /* uses vectbase */

  reg = get_regulator(mun,prec);
  p1=cgetg(3,t_VEC); racu=(GEN)sbnf[10];
  p1[1]=racu[1]; p1[2]=lmul(bas,(GEN)racu[2]);
  racu=p1;

  res=cgetg(7,t_VEC);
  res[1]=(long)clgp; res[2]=(long)reg;    res[3]=(long)dbltor(1.0);
  res[4]=(long)racu; res[5]=(long)funits; res[6]=lstoi(1000);

  if (lg(sbnf[7])>1) { W=(GEN)sbnf[7]; mata=(GEN)sbnf[8]; }
  else
  {
    long la = lg(matal);
    W=cgetg(1,t_MAT); mata=cgetg(la,t_MAT);
    for (k=1; k<la; k++) mata[k]=lgetg(1,t_COL);
  }
  y=cgetg(11,t_VEC);
  y[1]=(long)W; y[2]=(long)mata;       y[3]=(long)mun;
  y[4]=(long)mc;  y[5]=(long)vectbase; y[6]=(long)vp;
  y[7]=(long)nf;  y[8]=(long)res;      y[9]=(long)clgp2; y[10]=sbnf[12];
  return gerepileupto(av,gcopy(y));
}

static GEN
classgroupall(GEN P, GEN data, long flag, long prec)
{
  long court[3],doubl[4];
  long av=avma,flun,lx, minsfb=3,nbrelpid=4;
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
    case 7: minsfb  = itos((GEN)data[6]);
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
    case 3: return smallbuchinit(P,bach,bach2,RELSUP,borne,nbrelpid,minsfb,prec);
    case 4: flun=2; break;
    case 5: flun=3; break;
    case 6: flun=0; break;
    default: err(flagerr,"classgroupall");
      return NULL; /* not reached */
  }
  return buchall(P,bach,bach2,RELSUP,borne,nbrelpid,minsfb,flun,prec);
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
  GEN y,z;
  long av=avma,tetpil,i;

  if (typ(P)==t_INT)
  {
    z=quadclassunit0(P,0,data,prec); tetpil=avma;
    y=cgetg(4,t_VEC); for (i=1; i<=3; i++) y[i]=lcopy((GEN)z[i]);
    return gerepile(av,tetpil,y);
  }
  z=(GEN)classgroupall(P,data,6,prec)[1]; tetpil=avma;
  return gerepile(av,tetpil,gcopy((GEN)z[5]));
}

GEN
regulator(GEN P, GEN data, long prec)
{
  GEN z;
  long av=avma,tetpil;

  if (typ(P)==t_INT)
  {
    if (signe(P)>0)
    {
      z=quadclassunit0(P,0,data,prec); tetpil=avma;
      return gerepile(av,tetpil,gcopy((GEN)z[4]));
    }
    return gun;
  }
  z=(GEN)classgroupall(P,data,6,prec)[1]; tetpil=avma;
  return gerepile(av,tetpil,gcopy((GEN)z[6]));
}

#ifdef INLINE
INLINE
#endif
GEN
col_dup(long n, GEN col)
{
   GEN c = (GEN) gpmalloc(sizeof(long)*(n+1));
   memcpy(c,col,(n+1)*sizeof(long));
   return c;
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

static GEN
buchall_end(GEN nf,GEN CHANGE,long fl,long k, GEN fu, GEN clg1, GEN clg2,
            GEN reg, GEN c_1, GEN zu, GEN W, GEN B,
            GEN xarch, GEN matarch, GEN vectbase, GEN vperm)
{
  long l = labs(fl)>1? 11: fl? 9: 8;
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
    z=cgetg(2,t_MAT); z[1]=lcopy(RES); return z;
  }
  z=cgetg(11,t_VEC);
  z[1]=(long)W;
  z[2]=(long)B;
  z[3]=(long)xarch;
  z[4]=(long)matarch;
  z[5]=(long)vectbase;
  z[6]=(long)vperm;
  z[7]=(long)nf; RES+=4; RES[0]=evaltyp(t_VEC) | evallg(l-4);
  z[8]=(long)RES;
  z[9]=(long)clg2;
  z[10]=zero; /* dummy: we MUST have lg(bnf) != lg(nf) */
  if (CHANGE) { p1=cgetg(3,t_VEC); p1[1]=(long)z; p1[2]=(long)CHANGE; z=p1; }
  return gcopy(z);
}

static GEN
buchall_for_degree_one_pol(GEN nf, GEN CHANGE, long flun)
{
  long av = avma, k = EXP220;
  GEN W,B,xarch,matarch,vectbase,vperm;
  GEN fu=cgetg(1,t_VEC), reg=gun, c_1=gun, zu=cgetg(3,t_VEC);
  GEN clg1=cgetg(4,t_VEC), clg2=cgetg(4,t_VEC);

  clg1[1]=un; clg1[2]=clg1[3]=clg2[3]=lgetg(1,t_VEC);
  clg2[1]=clg2[2]=lgetg(1,t_MAT);
  zu[1]=deux; zu[2]=lnegi(gun);
  W=B=xarch=matarch=cgetg(1,t_MAT);
  vectbase=cgetg(1,t_COL); vperm=cgetg(1,t_VEC);

  return gerepileupto(av, buchall_end(nf,CHANGE,flun,k,fu,clg1,clg2,reg,c_1,zu,W,B,xarch,matarch,vectbase,vperm));
}

GEN
buchall(GEN P,GEN gcbach,GEN gcbach2,GEN gRELSUP,GEN gborne,long nbrelpid,
        long minsfb,long flun,long prec)
{
  long av = avma,av0,av1,limpile,i,j,k,ss,cmptglob,lgsub;
  long N,R1,R2,RU,PRECREG,PRECREGINT,KCCO,KCCOPRO,RELSUP;
  long extrarel,nlze,sreg,nrelsup,nreldep,phase,slim,matcopymax;
  long first = 1, sfb_increase = 0, sfb_trials = 0, precdouble = 0;
  long **mat,**matcopy,*ex;
  double cbach,cbach2,drc,LOGD2,lim,LIMC,LIMC2;
  GEN p1,p2,lmatt2,fu,zu,nf,D,xarch,met,W,reg,lfun,z,clh,vperm,subfb;
  GEN B,C,u1,u2,c1,sublambda,pdep,parch,liste,invp,clg1,clg2;
  GEN CHANGE=NULL, extramat=NULL, extraC=NULL, list_jideal = NULL;
  char *precpb = NULL;

  if (DEBUGLEVEL) timer2();

  if (typ(P)==t_POL) nf = NULL;
  else
  {
    nf=checknf(P); P=(GEN)nf[1];
  }
  if (typ(gRELSUP)!=t_INT) gRELSUP=gtrunc(gRELSUP);
  RELSUP = itos(gRELSUP);
  if (RELSUP<=0) err(talker,"not enough relations in bnfxxx");

  /* Initializations */
  fu = NULL; PRECREG = KCCOPRO = extrarel = 0; /* gcc -Wall */
  N=lgef(P)-3;
  if (!nf)
  {
    nf=initalgall0(P, nf_REGULAR, max(BIGDEFAULTPREC,prec));
    if (lg(nf)==3) /* P was a non-monic polynomial, nfinit changed it */
    {
      CHANGE=(GEN)nf[2]; nf=(GEN)nf[1];
    }
    if (DEBUGLEVEL) msgtimer("initalg");
  }
  if (N<=1) return buchall_for_degree_one_pol(nf,CHANGE,flun);
  zu=rootsof1(nf);
  zu[2] = lmul((GEN)nf[7],(GEN)zu[2]);
  if (DEBUGLEVEL) msgtimer("rootsof1");

  R1=itos(gmael(nf,2,1)); R2=(N-R1)>>1; RU=R1+R2;
  D=(GEN)nf[3]; drc=fabs(gtodouble(D));
  LOGD2=log(drc); LOGD2 = LOGD2*LOGD2;
  lim = exp(-(double)N) * sqrt(2*PI*N*drc) * pow(4/PI,(double)R2);
  if (lim < 3.) lim = 3.;
  cbach = min(12., gtodouble(gcbach)); cbach /= 2;
  cbach2 = gtodouble(gcbach2);
  if (DEBUGLEVEL)
  {
    fprintferr("N = %ld, R1 = %ld, R2 = %ld, RU = %ld\n",N,R1,R2,RU);
    fprintferr("D = %Z\n",D);
  }
  av0 = avma;
  matcopy = NULL;
  powsubfb = NULL;

INCREASEGEN:
  if (precpb)
  {
    precdouble++;
    prec=(PRECREG<<1)-2;
    if (DEBUGLEVEL)
    {
      char str[64]; sprintf(str,"buchall (%s)",precpb);
      err(warnprec,str,prec);
    }
    precpb = NULL;
    avma = av0; nf = nfnewprec(nf,prec); av0 = avma;
  }
  else
    cbach = check_bach(cbach,12.);
  if (first) first = 0; else { desallocate(matcopy); avma = av0; }
  sfb_trials = sfb_increase = 0;
  nreldep = nrelsup = 0;
  LIMC = cbach*LOGD2; if (LIMC < 20.) LIMC = 20.;
  LIMC2=max(3. * N, max(cbach,cbach2)*LOGD2);
  if (LIMC2 < LIMC) LIMC2=LIMC;
  if (DEBUGLEVEL) { fprintferr("LIMC = %.1f, LIMC2 = %.1f\n",LIMC,LIMC2); }

  /* initialize factorbase, [sub]vperm */
  lfun = factorbasegen(nf,(long)LIMC2,(long)LIMC);
  if (!lfun) goto INCREASEGEN;

  vperm = cgetg(lg(vectbase), t_VECSMALL);
  subfb = subfactorbasegen(N,(long)min(lim,LIMC2), minsfb, vperm, &ss);
  if (!subfb) goto INCREASEGEN;
  lgsub = lg(subfb);
  ex = cgetg(lgsub,t_VECSMALL);

  PRECREGINT = DEFAULTPREC
             + ((expi(D)*(lgsub-2)+((N*N)>>2))>>TWOPOTBITS_IN_LONG);
  PRECREG = max(prec+1,PRECREGINT);
  KCCO = KC+RU-1 + max(ss,RELSUP);
  if (DEBUGLEVEL)
  {
    fprintferr("nbrelsup = %ld, ss = %ld, ",RELSUP,ss);
    fprintferr("KCZ = %ld, KC = %ld, KCCO = %ld \n",KCZ,KC,KCCO); flusherr();
  }
  mat=(long**)gpmalloc(sizeof(long*)*(KCCO+1));
  setlg(mat, KCCO+1);
  C = cgetg(KCCO+1,t_MAT);
  cmptglob=0;
  /* trivial relations */
  for (i=1; i<=KCZ; i++)
  {
    GEN P = idealbase[i];
    if (isclone(P))
    { /* all prime divisors in factorbase */
      unsetisclone(P); cmptglob++;
      mat[cmptglob] = p1 = col_0(KC);
      C[cmptglob] = (long)(p2 = cgetg(RU+1,t_COL));
      k = numideal[factorbase[i]];
      p1[0] = k+1; p1 += k; /* for already_found_relation */
      k = lg(P);
      for (j=1; j<k; j++) p1[j] = itos(gmael(P,j,3));
      for (j=1; j<=RU; j++) p2[j] = zero;
    }
  }
  /* initialize for other relations */
  for (i=cmptglob+1; i<=KCCO; i++)
  {
    mat[i] = col_0(KC);
    C[i] = (long) (p1 = cgetg(RU+1,t_COL));
    for (j=1; j<=RU; j++)
    {
      p2=cgetg(3,t_COMPLEX);
      p2[1]=lgetr(PRECREG);
      p2[2]=lgetr(PRECREG); p1[j]=(long)p2;
    }
  }
  if (DEBUGLEVEL)
    fprintferr("After trivial relations, cmptglob = %ld\n",cmptglob);
  av1 = avma; liste = cgetg(KC+1,t_VECSMALL);
  for (i=1; i<=KC; i++) liste[i]=0;
  invp = relationrank(mat,cmptglob,liste);

  /* relations through elements of small norm */
  cmptglob = small_norm_for_buchall(cmptglob,mat,C,KCCO,(long)LIMC,
                                    PRECREG,nf,gborne,nbrelpid,invp,liste);
  if (cmptglob < 0)
  {
    for (j=1; j<=KCCO; j++) free(mat[j]); free(mat);
    precpb = "small_norm";
    goto INCREASEGEN;
  }
  avma = av1; limpile=stack_lim(av1,1);

  slim = KCCO; phase = 0;
  nlze = matcopymax = 0; /* for lint */
  lmatt2 = NULL;

  /* random relations */
  if (cmptglob == KCCO) /* enough relations, initialize nevertheless */
    ((void(*)(long))random_relation)(-1);
  else
  {
    GEN maarch;
    long **ma;

    if (DEBUGLEVEL)
      { fprintferr("\n#### Looking for random relations\n"); flusherr(); }
  LABELINT:
    if (sfb_increase)
    { /* increase subfactorbase */
      sfb_increase = 0;
      if (++sfb_trials >= SFB_MAX) goto INCREASEGEN;
      subfb = subfactorbasegen(N, (long)min(lim,LIMC2),
                                  lgsub-1+SFB_STEP, NULL, &ss);
      if (!subfb) goto INCREASEGEN;
      if (DEBUGLEVEL) fprintferr("*** Increasing subfactorbase\n");
      powsubfb = NULL;
      nreldep = nrelsup = 0;
      lgsub = lg(subfb);
    }

    if (phase == 0) { ma = mat; maarch = C; }
    else /* reduced the relation matrix at least once */
    {
      extrarel = nlze;
      if (extrarel < MIN_EXTRA) extrarel = MIN_EXTRA;
      slim = cmptglob+extrarel;
      setlg(extraC,extrarel+1);
      setlg(extramat,extrarel+1);
      if (slim > matcopymax)
      {
        matcopy = (long**)gprealloc(matcopy, (2*slim+1) * sizeof(long*),
                                             (matcopymax+1) * sizeof(long*));
        matcopymax = 2 * slim;
      }
      setlg(matcopy,slim+1);
      if (DEBUGLEVEL)
	fprintferr("\n(need %ld more relation%s)\n",
                    extrarel, (extrarel==1)?"":"s");
      for (j=cmptglob+1; j<=slim; j++) matcopy[j] = col_0(KC);
      maarch = extraC - cmptglob; /* start at 0, the others at cmptglob */
      ma = matcopy;
    }
    if (!lmatt2)
    {
      lmatt2 = compute_matt2(RU,nf);
      av1 = avma;
    }
    if (!powsubfb)
    {
      powsubfbgen(nf,subfb,CBUCHG+1,PRECREG,PRECREGINT);
      av1 = avma;
    }
    ss = random_relation(phase,cmptglob,slim,(long)LIMC,N,PRECREG,PRECREGINT,
                         nf,subfb,lmatt2,ma,maarch,ex,list_jideal);
    if (ss < 0) /* could not find relations */
    {
      if (phase == 0) { for (j=1; j<=KCCO; j++) free(mat[j]); free(mat); }
      if (ss != -1) precpb = "random_relation"; /* precision pb */
      goto INCREASEGEN;
    }
    if (DEBUGLEVEL > 2) dbg_outrel(phase,cmptglob,vperm,ma,maarch);
    if (phase)
      for (j=1; j<=extrarel; j++)
      {
	long *c = matcopy[cmptglob+j];
	GEN  *g = (GEN*) extramat[j];
	for (k=1; k<=KC; k++) g[k] = stoi(c[vperm[k]]);
      }
    cmptglob = ss;
  }

  /* reduce relation matrices */
  if (phase == 0) /* never reduced before */
  {
    matcopymax = 10*KCCO + MAXRELSUP;
    matcopy = (long**)gpmalloc(sizeof(long*)*(matcopymax + 1));
    setlg(matcopy, KCCO+1);
    for (j=1; j<=KCCO; j++) matcopy[j] = col_dup(KC,mat[j]);
    W = hnfspec(mat,vperm,&pdep,&B,&C,lgsub-1);
    for (j=1; j<=KCCO; j++) free(mat[j]); free(mat);
    KCCOPRO = KCCO; phase = 1;
   /* keep some room for the extra relation. We will update matrix size when
    * extrarel goes down
    */
    nlze = lg(pdep)>1? lg(pdep[1])-1: lg(B[1])-1;
    if (nlze)
    {
      list_jideal = cgetg(nlze+1, t_VECSMALL);
      for (i=1; i<=nlze; i++) list_jideal[i] = vperm[i];
    }
    extrarel = nlze; /* in case the regulator is 0 */
    if (extrarel < MIN_EXTRA) extrarel = MIN_EXTRA;
    extramat =cgetg(extrarel+1,t_MAT);
    extraC=cgetg(extrarel+1,t_MAT);
    for (j=1; j<=extrarel; j++)
    {
      extramat[j]=lgetg(KC+1,t_COL);
      extraC[j]=lgetg(RU+1,t_COL);
      for (i=1; i<=RU; i++)
      {
	p1 = cgetg(3,t_COMPLEX); mael(extraC,j,i)=(long)p1;
	p1[1]=lgetr(PRECREG);
	p1[2]=lgetr(PRECREG);
      }
    }
  }
  else
  {
    list_jideal = NULL;
    if (low_stack(limpile, stack_lim(av1,1)))
    {
      GEN *gptr[6];
      if(DEBUGMEM>1) err(warnmem,"buchall");
      gptr[0]=&W; gptr[1]=&C; gptr[2]=&B; gptr[3]=&pdep;
      gptr[4]=&extramat; gptr[5]=&extraC;
      gerepilemany(av1,gptr,6);
    }
    W = hnfadd(W,vperm,&pdep,&B,&C, extramat,extraC);
    nlze = lg(pdep)>1? lg(pdep[1])-1: lg(B[1])-1;
    KCCOPRO += extrarel;
    if (nlze && ++nreldep > MAXRELSUP) { sfb_increase=1; goto LABELINT; }
  }
  if (nlze) goto LABELINT; /* dependent rows */

  /* first attempt at regulator for the check */
  sreg = KCCOPRO - (lg(B)-1) - (lg(W)-1); /* = zc (cf hnffinal) */
  xarch = cgetg(sreg+1,t_MAT); /* cols corresponding to units */
  for (j=1; j<=sreg; j++) xarch[j] = C[j];
  reg = compute_multiple_of_R(xarch,RU,N,PRECREG,&sublambda);

  if (!reg)
  { /* not full rank for units */
    if (DEBUGLEVEL) fprintferr("regulator is zero.\n");
    if (++nrelsup > MAXRELSUP) goto INCREASEGEN;
    nlze=MIN_EXTRA; goto LABELINT;
  }
  /* anticipate precision problems */
  if (!sublambda) { precpb = "bestappr"; goto INCREASEGEN; }

  /* class number */
  if (DEBUGLEVEL) fprintferr("\n");
  clh = compute_class_number(W,&met,&u1,&u2);

  /* check */
  z = mulrr(lfun,gmul(gmul2n(gpuigs(shiftr(mppi(DEFAULTPREC),1),-R2),-R1),
		      gsqrt(absi(D),DEFAULTPREC)));
  z = mulri(z,(GEN)zu[1]);
  /* z = Res (zeta_K, s = 1) * w D^(1/2) / [ 2^r1 (2pi)^r2 ] = h R */
  p1 = gmul2n(divir(clh,z), 1);
  /* c1 should be close to 2, and not much smaller */
  c1 = compute_check(sublambda,p1,&parch,&reg);
  /* precision problems? */
  if (!c1 || gcmpgs(gmul2n(c1,1),3) < 0)
  { /* has to be a prec. problem unless we cheat on Bach constant */
    if (!precdouble) precpb = "compute_check";
    goto INCREASEGEN;
  }
  if (gcmpgs(c1,3) > 0)
  {
    if (++nrelsup <= MAXRELSUP)
    {
      if (DEBUGLEVEL)
      {
        fprintferr("\n ***** check = %f\n",gtodouble(c1)/2);
        flusherr();
      }
      nlze=MIN_EXTRA; goto LABELINT;
    }
    if (cbach<11.99) { sfb_increase=1; goto LABELINT; }
    err(warner,"suspicious check. Try to increase extra relations");
  }

  /* Phase "be honest" */
  if (KCZ2 > KCZ)
  {
    if (!powsubfb)
      powsubfbgen(nf,subfb,CBUCHG+1,PRECREG,PRECREGINT);
    if (!be_honest(nf,subfb,RU,PRECREGINT)) goto INCREASEGEN;
  }

  /* regulator, roots of unity, fundamental units */
  if (flun < 0 || flun > 1)
  {
    xarch = cleancol(gmul(xarch,parch),N,PRECREG);
    if (DEBUGLEVEL) msgtimer("cleancol");
  }
  if (labs(flun) > 1)
  {
    fu = getfu(nf,&xarch,reg,flun,&k,PRECREG);
    if (k) fu = gmul((GEN)nf[7],fu);
    else if (labs(flun) > 2) { precpb = "getfu"; goto INCREASEGEN; }
  }

  /* class group generators */
  if (DEBUGLEVEL) fprintferr("\n");
  class_group_gen(nf,met,clh,u1,u2,vperm, &clg1, &clg2, PRECREGINT);

  /* cleanup */
  if (flun < 0)
  {
    i = lg(C)-sreg; C += sreg; C[0] = evaltyp(t_MAT)|evallg(i);
    C = cleancol(C,N,PRECREG);
    settyp(vperm, t_COL);
    for (i=1; i<=KC; i++) vperm[i]=lstoi(vperm[i]);
  }
  c1 = gdiv(gmul(reg,clh),z);
  desallocate(matcopy);

  return gerepileupto(av, buchall_end(nf,CHANGE,flun,k,fu,clg1,clg2,reg,c1,zu,W,B,xarch,C,vectbase,vperm));
}
