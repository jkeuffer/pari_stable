/*************************************************************************/
/**									**/
/**                           GALOIS CONJUGATES        		        **/
/**									**/
/*************************************************************************/
/* $Id$ */
#include "pari.h"

#if 0
/* f in Z[X] */
static long
is_totally_split(GEN f, GEN p)
{
  long av = avma, n=lgef(f);
  GEN z;

  if (n <= 4) return 1;
  if (!is_bigint(p) && n-3 > p[2]) return 0;
  f = Fp_pol_red(f, p);
  if (lgef(f) != n) { avma=av; return 0; }
  z = Fp_pow_mod_pol(polx[varn(f)], p, f, p);
  /* x^p = x mod (f(x),p) ? */
  avma = av; return lgef(z)==4 && gcmp1((GEN)z[3]) && !signe(z[2]);
}
#endif

GEN
galoisconj(GEN nf)
{
  GEN x,y,z;
  long i,lz,lx,v, av = avma;
  nf = checknf(nf); x = (GEN)nf[1];
  v = varn(x); lx = lgef(x)-2;
  if (v == 0) nf = gsubst(nf,0,polx[MAXVARN]);
  else
  {
    x = dummycopy(x); setvarn(x,0);
  }
  z = nfroots(nf,x); lz = lg(z);
  y = cgetg(lx, t_VEC);
  for (i=1; i<lz; i++)
  {
    GEN p1 = lift((GEN)z[i]);
    setvarn(p1,v); y[i] = (long)p1;
  }
  for (   ; i<lx; i++) y[i] = zero;
  return gerepileupto(av, y);
}

GEN
galoisconj1(GEN nf)
{
  long av=avma,tetpil,i,j,n,r1,ru,prec;
  GEN x,y,w,polr,p1,p2;

  nf=checknf(nf); x=(GEN)nf[1];

  n=lgef(x)-3; if (n<=0) return cgetg(1,t_VEC);
  r1 = itos(gmael(nf,2,1)); p1=(GEN)nf[6];
  prec = precision((GEN)p1[1]);
  /* accuracy in decimal digits */
  prec = (long)(bit_accuracy(prec) * L2SL10 * 0.75);
  ru = (n+r1)>>1;
  polr = cgetg(n+1,t_VEC);
  for (i=1; i<=r1; i++) polr[i]=p1[i];
  for (j=i; i<=ru; i++) { polr[j++]=p1[i]; polr[j++]=lconj((GEN)p1[i]); }
  p2=gmael(nf,5,1); w=cgetg(n+2,t_VEC);
  for (i=1; i<=n; i++) w[i]=coeff(p2,1,i);

  y=cgetg(n+1,t_VEC); y[1]=(long)polx[varn(x)];
  for (i=2; i<=n; i++)
  {
    y[i]=zero; w[n+1]=polr[i]; p1 = lindep2(w, prec);
    if (signe(p1[n+1]))
    {
      setlg(p1, n+1); settyp(p1,t_COL);
      p2 = gdiv(gmul((GEN)nf[7],p1), negi((GEN)p1[n+1]));
      if (gdivise(poleval(x,p2), x)) y[i] = (long)p2;
    }
    if (DEBUGLEVEL>1) fprintferr("conjugate %ld: %Z\n", i, y[i]);
  }
  tetpil=avma; return gerepile(av,tetpil,gcopy(y));
}

GEN
galoisconj2(GEN x, long prec)
{
  long av=avma,tetpil,i,n,v;
  GEN y,w,polr,p1,p2;

  if (typ(x)!=t_POL) return galoisconj1(x);

  n=lgef(x)-3; if (n<=0) return cgetg(1,t_VEC);
  if (gisirreducible(x) == gzero) err(redpoler,"galoisconj2");
  polr=roots(x,prec); p1=(GEN)polr[1];

  prec = (long)(bit_accuracy(prec) * L2SL10 * 0.75);
  w=cgetg(n+2,t_VEC); w[1]=un;
  for (i=2; i<=n; i++) w[i]=lmul(p1,(GEN)w[i-1]);

  v=varn(x); y=cgetg(n+1,t_VEC); y[1]=(long)polx[v];
  for (i=2; i<=n; i++)
  {
    y[i]=zero; w[n+1]=polr[i]; p1 = lindep2(w, prec);
    if (signe(p1[n+1]))
    {
      setlg(p1, n+1);
      p2 = gdiv(gtopolyrev(p1,v), negi((GEN)p1[n+1]));
      if (gdivise(poleval(x,p2), x)) y[i] = (long)p2;
    }
    if (DEBUGLEVEL>1) fprintferr("conjugate %ld: %Z\n", i, y[i]);
  }
  tetpil=avma; return gerepile(av,tetpil,gcopy(y));
}

/*
  T est le polynome \sum t_i*X^i
  S est un Polmod T
  Retourne un vecteur Spow verifiant la condition:
  i>=1 et t_i!=0 ==> Spow[i]=S^(i-1)*t_i
  Essaie d'etre efficace sur les polynomes lacunaires
*/
GEN
compoTS(GEN T,GEN S)
{
  GEN Spow;
  int i;
  Spow=cgetg(lgef(T)-2,t_VEC);
  for (i=3; i<lg(Spow); i++)
    Spow[i]=0;
  Spow[1]=un;
  Spow[2]=(long)S;
  for (i=2; i<lg(Spow)-1; i++)
  {
    if (!gcmp0((GEN)T[i+3]))
      for (;;)
      {
	int k,l;
	for (k=1; k<=(i>>1); k++)
	  if (Spow[k+1] && Spow[i-k+1])
	    break;
	if ((k<<1)<i)
	{
	  Spow[i+1]=lmul((GEN)Spow[k+1],(GEN)Spow[i-k+1]);
	  break;
	}
	else if ((k<<1)==i)/*En esperant que sqr est plus rapide...*/
	{
	  Spow[i+1]=lsqr((GEN)Spow[k+1]);
	  break;
	}
	for (k=i-1; k>0; k--)
	  if (Spow[k+1])
	    break;
	if ((k<<1)<i)
	{
	  Spow[(k<<1)+1]=lsqr((GEN)Spow[k+1]);
	  continue;
	}
	for (l=i-k; l>0; l--)
	  if (Spow[l+1])
	    break;
	if (Spow[i-l-k+1])
	  Spow[i-k+1]=lmul((GEN)Spow[i-l-k+1],(GEN)Spow[l+1]);
	else
	  Spow[l+k+1]=lmul((GEN)Spow[k+1],(GEN)Spow[l+1]);
      }
  }
  for (i=1; i<lg(Spow); i++)
    if (!gcmp0((GEN)T[i+2]))
      Spow[i]=lmul((GEN)Spow[i],(GEN)T[i+2]);
  return Spow;
}

/*
  Calcule T(S) a l'aide du vecteur Spow
 */
static GEN
calcTS(GEN Spow,GEN T,GEN S)
{
  GEN res=gzero;
  int i;
  for (i=1; i<lg(Spow); i++)
    if (!gcmp0((GEN)T[i+2]))
      res=gadd(res,(GEN)Spow[i]);
  res=gmul(res,S);
  return gadd(res,(GEN)T[2]);
}
/*
 Calcule T'(S) a l'aide du vecteur Spow
*/
static GEN
calcderivTS(GEN Spow,GEN T,GEN mod)
{
  GEN res=gzero;
  int i;
  for (i=1; i<lg(Spow); i++)
    if (!gcmp0((GEN)T[i+2]))
      res=gadd(res,gmul((GEN)Spow[i],stoi(i)));
  res=gmul(lift(lift(res)),mod);
  return  gmodulcp(res,T);
}
/*
Verifie que S est une solution presque surement
et calcule sa permutation
 */
static int poltopermtest(GEN f,GEN L,GEN pf)
{
  ulong ltop;
  GEN fx,fp;
  int i,j;
  fp=cgetg(lg(L),t_VECSMALL);
  ltop=avma;
  for (i=1; i<lg(fp); i++)fp[i]=1;
  for (i=1; i<lg(L); i++)
  {
    fx=gsubst(f,varn(f),(GEN)L[i]);
    for (j=1; j<lg(L); j++)
      if (fp[j] && gegal(fx,(GEN)L[j]))
      {
	pf[i]=j;
	fp[j]=0;
	break;
      }
    if (j==lg(L))
      return 0;
    avma=ltop;
  }
  return 1;
}
/*
  Soit T un polynome de \ZZ[X] , p un nombre premier , S\in\FF_p[X]/(T)
  tel que T(S)=0 [p,T]
  essaye de relever S en S_0 tel que T(S_0)=0 [T]
  den: multiple du denominateur commun de la solution.
  retourne gzero: pas de solution
  sinon retourne la permutation du vecteur L des racines l-adiques de T
  correspondant a S.
 */
GEN
frobeniuslift(GEN T,GEN den,GEN p,GEN S,GEN borne,GEN L)
{
  ulong ltop,lbot,ltop2,av=avma;
  long x;
  GEN Q,q,mod,modold;
  GEN W,Tr,Sr,Wr=gzero,Trold,Spow;
  int flag,init;
  GEN pf;
  GEN *gptr[2];
  if (DEBUGLEVEL>=1) timer2();
  pf=cgetg(lg(L),t_VECSMALL);
  ltop=avma;
  x=varn(T);
  Tr=gmul(T,gmodulcp(gun,p));
  W=ginv(gsubst(deriv(Tr,x),x,S));
  Q=powgi(p,gmax(gdeux,gceil(gdiv(glog(gmul2n(borne,1),DEFAULTPREC),glog(p,DEFAULTPREC)))));
  q=p; modold=p; Trold=Tr;
  flag=1; init=0;
  gptr[0]=&S;
  gptr[1]=&Wr;
  while (flag)
  {
    if (DEBUGLEVEL>=1) timer2();
    q=gsqr(q);
    if (gcmp(q,Q)>=0)
    {
      flag=0;
      q=Q;
    }
    mod=gmodulcp(gun,q);
    Tr=gmul(T,mod);
    ltop2=avma;
    Sr=gmodulcp(gmul(lift(lift(S)),mod),Tr);
    Spow=compoTS(Tr,Sr);
    if (init)
      W=gmul(Wr,gsub(gdeux,gmul(Wr,calcderivTS(Spow,Trold,modold))));
    else
      init=1;
    Wr=gmodulcp(gmul(lift(lift(W)),mod),Tr);
    S=gmul(Wr,calcTS(Spow,Tr,Sr));
    lbot=avma;
    Wr=gcopy(Wr);
    S=gsub(Sr,S);
    gerepilemanysp(ltop2,lbot,gptr,2);
    modold=mod; Trold=Tr;
  }
  S=gdiv(centerlift(lift(gmul(S,den))),den);
  if (DEBUGLEVEL>=1) msgtimer("frobeniuslift()");
  if (!poltopermtest(S,L,pf))
  {
    avma=av;
    return gzero;
  }
  avma=ltop;
  return pf;
}

/*
  test tous les lifts possibles a l'aide de frobeniuslift,
  pour le nombre premier p, le sous-groupe sg et l'exposant e.
  F factorisation p-adique de T.
  retourne gzero ou une permutation de L
*/
GEN
frobeniusliftall(GEN F,GEN sg,long e,GEN T,GEN den,GEN p,GEN borne,GEN *psi,GEN L)
{
  ulong ltop=avma,lbot,av,ltop2;
  long d,N,z,m,c;
  long x;
  int i,j,k;
  GEN pf,u,v,f,mod;
  x=varn(F[1]);
  m=lg(F)-1;
  c=lg(sg)-1;
  d=m/c;
  pf=cgetg(m,t_VECSMALL);
  *psi=pf;
  ltop2=avma;
  N=itos(gdiv(mpfact(m),gmul(stoi(c),gpowgs(mpfact(d),c))));
  avma=ltop2;
  for (i=1; i<m; i++)
    pf[i]=1+i/d;
  mod=gmodulcp(gun,p);
  v=powgi(gmodulcp(gmul(polx[x],mod),(GEN)F[m]),gpowgs(p,e));
  av=avma;
  for (i=0;;i++)
  {
    u=v;
    if (DEBUGLEVEL>=4) fprintferr("GaloisConj:Lifting %Z:%d:%Z\n",sg,i,pf);
    for (j=1; j<m; j++)
    {
      u=chinois(u,powgi(gmodulcp(gmul(polx[x],mod),(GEN)F[j]),gpowgs(p,e*sg[pf[j]])));
    }
    lbot=avma;
    f=frobeniuslift(T,den,p,u,borne,L);
    if (f!=gzero)
      return gerepile(ltop2,lbot,f);
    avma=av;
    if (i==N-1)
      break;
    for (j=2; j<m && pf[j-1]>=pf[j]; j++);
    for (k=1; k<j-k && pf[k]!=pf[j-k]; k++)
    {
      z=pf[k];
      pf[k]=pf[j-k];
      pf[j-k]=z;
    }
    for (k=j-1; pf[k]>=pf[j]; k--);
	z=pf[j]; pf[j]=pf[k]; pf[k]=z;
  }
  avma=ltop;
  *psi=NULL;
  return gzero;
}

/*applique une permutation t a un vecteur s sans duplication */
static GEN
applyperm(GEN s,GEN t)
{
  GEN u;
  int i;
  if (lg(s)<lg(t))
    err(talker,"First permutation shorter than second in applyperm");
  u=cgetg(lg(s),typ(s));
  for (i=1; i<lg(s); i++)
    u[i]=s[t[i]];
  return u;
}
/* alloue une ardoise pour n entiers de longueurs
   pour les test de permutation
*/
GEN
alloue_ardoise(long n,long s)
{
  GEN ar;
  long i;
  ar=cgetg(n+1,t_VEC);
  for (i=1; i<=n; i++) ar[i]=lgeti(s);
  return ar;
}

/*structure contenant toutes les données pour le tests des permutations:

ordre :ordre des tests pour verifie_test
ordre[lg(ordre)]: numero du test principal
borne : borne sur les coefficients a trouver
ladic: modlo l-adique des racines
lborne:ladic-borne
TM:vecteur des ligne de M
PV:vecteur des clones des matrices de test (Vmatrix) (ou NULL si non calcule)
L,M comme d'habitude (voir plus bas)
*/
struct test_data
{
  GEN ordre;
  GEN borne,lborne,ladic;
  GEN PV,TM;
  GEN L,M;
};

/*Calcule la matrice de tests correspondant a la n-ieme ligne de V*/
GEN
Vmatrix(long n,struct test_data *td)
{
  ulong ltop=avma,lbot;
  GEN V;
  long i;
  V=cgetg(lg(td->L),t_VEC);
  for (i=1; i<lg(V); i++)
    V[i]=((GEN **)td->M)[i][n][2];
  V=centerlift(gmul(td->L,V));
  lbot=avma;
  V=gmod(V,td->ladic);
  return gerepile(ltop,lbot,V);
}

/* Initialise la structure test_data*/
void inittest(GEN L,GEN M,GEN borne,GEN ladic,struct test_data *td)
{
  ulong ltop;
  long i;
  int n=lg(L)-1;
  if (DEBUGLEVEL>=8) fprintferr("GaloisConj:Entree Init Test\n");
  td->ordre=cgetg(n+1,t_VECSMALL);
  for (i=1; i<=n-2; i++)
    td->ordre[i]=i+2;
  for (; i<=n; i++)
    td->ordre[i]=i-n+2;
  td->borne=borne;
  td->lborne=gsub(ladic,borne);
  td->ladic=ladic;
  td->L=L;
  td->M=M;
  td->PV=cgetg(n+1,t_VECSMALL); /*peut-etre t_VEC est correct ici*/
  for (i=1; i<=n; i++)
    td->PV[i]=0;
  ltop=avma;
  td->PV[td->ordre[n]]=(long)gclone(Vmatrix(td->ordre[n],td));
  avma=ltop;
  td->TM=gtrans(M);
  settyp(td->TM,t_VEC);
  for (i=1; i<lg(td->TM); i++)
    settyp(td->TM[i],t_VEC);
  if (DEBUGLEVEL>=8) fprintferr("GaloisConj:Sortie Init Test\n");
}

/*liberer les clones de la structure test_data
  Reservé a l'accreditation ultra-violet:Liberez les clones!
      Paranoia(tm)
*/
void
freetest(struct test_data *td)
{
  int i;
  for (i=1; i<lg(td->PV); i++)
    if (td->PV[i])
    {
      gunclone((GEN)td->PV[i]);
      td->PV[i]=0;
    }
}

/*Test si le nombre padique P est proche d'un entier inferieur a td->borne
en valeur absolue.
*/
long
padicisint(GEN P,struct test_data *td)
{
  long r;
  ulong ltop=avma;
  GEN U;
  if (typ(P)!=t_INT) err(typeer,"padicisint");
  U=modii(P,td->ladic);
  r=gcmp(U,(GEN)td->borne)<=0 || gcmp(U,(GEN)td->lborne)>=0;
  avma=ltop;
  return r;
}

/* Verifie si pf est une vrai solution et non pas un "hop" */
long
verifietest(GEN pf,struct test_data *td)
{
  ulong av=avma;
  GEN P,V;
  int i,j;
  int n=lg(td->L)-1;
  if (DEBUGLEVEL>=8) fprintferr("GaloisConj:Entree Verifie Test\n");
  P=applyperm(td->L,pf);
  for (i=1; i<n; i++)
  {
    long ord;
    GEN PW;
    ord=td->ordre[i];
    PW=(GEN)td->PV[ord];
    if (PW)
    {
      V=((GEN **)PW)[1][pf[1]];
      for (j=2; j<=n; j++)
	V=gadd(V,((GEN **)PW)[j][pf[j]]);
    }
    else
      V=centerlift(gmul((GEN)td->TM[ord],P));
    if (!padicisint(V,td))
      break;
  }
  if (i==n)
  {
    if (DEBUGLEVEL>=8) fprintferr("GaloisConj:Sortie Verifie Test:1\n");
    avma=av; return 1;
  }
  if (! td->PV[td->ordre[i]])
  {
    td->PV[td->ordre[i]]=(long)gclone(Vmatrix(td->ordre[i],td));
    if (DEBUGLEVEL>=2) fprintferr("M");
  }
  if (DEBUGLEVEL>=2) fprintferr("%d.",i);
  if (i>1)
  {
    long z;
    z=td->ordre[i];
    for (j=i; j>1; j--)
      td->ordre[j]=td->ordre[j-1];
    td->ordre[1]=z;
    if (DEBUGLEVEL>=6) fprintferr("%Z",td->ordre);
  }
  if (DEBUGLEVEL>=8) fprintferr("GaloisConj:Sortie Verifie Test:0\n");
  avma=av; return 0;
}

/*
  F est la decomposition en cycle de sigma,
  B est la decomposition en cycle de cl(tau)
  Teste toutes les permutations pf pouvant correspondre a tau
  tel que :
  tau*sigma*tau^-1=sigma^s
  et
  tau^d=sigma^t  ou d est l'ordre de cl(tau)
---------
  x: vecteur des choix
  y: vecteur des mises a jour
  G: vecteur d'acces a F linéaire
*/
GEN
testpermutation(GEN F,GEN B,long s,long t,long cut,struct test_data *td)
{
  ulong av,avm=avma,av2;
  long a,b,c,d,n;
  GEN pf,x,ar,y,*G;
  int N,cx,p1,p2,p3,p4,p5,p6;
  int i,j,hop=0;
  GEN V,W;
  if (DEBUGLEVEL>=1) timer2();
  a=lg(F)-1;
  b=lg(F[1])-1;
  c=lg(B)-1;
  d=lg(B[1])-1;
  n=a*b;
  s=(b+s)%b;
  pf=cgetg(n+1,t_VECSMALL);
  av=avma;
  ar=alloue_ardoise(a,1+lg(td->ladic));
  x=cgetg(a+1,t_VECSMALL);
  y=cgetg(a+1,t_VECSMALL);
  G=(GEN *)cgetg(a+1,t_VECSMALL); /*Don't worry*/
  av2=avma;
  W=(GEN)td->PV[td->ordre[n]];
  for (cx=1,i=1,j=1; cx<=a; cx++,i++)
  {
    x[cx]=(i!=d)?0:t;
    y[cx]=1;
    G[cx]=(GEN)F[((long **)B)[j][i]]; /*Be happy*/
    if (i==d)
    {
      i=0;
      j++;
    }
  }/*Be happy now!*/
  N=itos(gpowgs(stoi(b),c*(d-1)))/cut;
  avma=av2;
  if (DEBUGLEVEL>=4) fprintferr("GaloisConj:I will try %d permutations\n",N);
  for (cx=0; cx<N; cx++)
  {
    if (DEBUGLEVEL>=2 && cx%1000==999) fprintferr("%d%% ",(100*cx)/N);
    if (cx)
    {
      for (i=1,j=d; i<a;)
      {
	y[i]=1;
	if ((++(x[i]))!=b)
	  break;
	x[i++]=0;
	if (i==j)
	{
	  y[i++]=1;
	  j+=d;
	}
      }
      y[i+1]=1;
    }
    for (p1=1,p5=d; p1<=a; p1++,p5++)
      if (y[p1])
      {
	if (p5==d)
	{
	  p5=0;
	  p4=0;
	}
	else
	  p4=x[p1-1];
	if (p5==d-1)
	  p6=p1+1-d;
	else
	  p6=p1+1;
	y[p1]=0;
	V=gzero;
	for (p2=1+p4,p3=1+x[p1]; p2<=b; p2++)
	{
	  V=gadd(V,((GEN **)W)[G[p6][p3]][G[p1][p2]]);
	  p3+=s;
	  if (p3>b)
	    p3-=b;
	}
	p3=1+x[p1]-s;
	if (p3<=0)
	  p3+=b;
	for (p2=p4; p2>=1; p2--)
	{
	  V=gadd(V,((GEN **)W)[G[p6][p3]][G[p1][p2]]);
	  p3-=s;
	  if (p3<=0)
	    p3+=b;
	}
	gaffect((GEN)V,(GEN)ar[p1]);
      }
    V=gzero;
    for (p1=1; p1<=a; p1++)
      V=gadd(V,(GEN)ar[p1]);
    if (padicisint(V,td))
    {
      for (p1=1,p5=d; p1<=a; p1++,p5++)
      {
	if (p5==d)
	{
	  p5=0;
	  p4=0;
	}
	else
	  p4=x[p1-1];
	if (p5==d-1)
	  p6=p1+1-d;
	else
	  p6=p1+1;
	for (p2=1+p4,p3=1+x[p1]; p2<=b; p2++)
	{
	  pf[G[p1][p2]]=G[p6][p3];
	  p3+=s;
	  if (p3>b)
	    p3-=b;
	}
	p3=1+x[p1]-s;
	if (p3<=0)
	  p3+=b;
	for (p2=p4; p2>=1; p2--)
	{
	  pf[G[p1][p2]]=G[p6][p3];
	  p3-=s;
	  if (p3<=0)
	    p3+=b;
	}
      }
      if (verifietest(pf,td))
      {
	avma=av;
	if (DEBUGLEVEL>=1) msgtimer("testpermutation(%d)",cx+1);
	if (DEBUGLEVEL>=2 && hop)
	  fprintferr("GaloisConj:%d hop sur %d iterations\n",hop,cx+1);
	return pf;
      }
      else
	hop++;
    }
    avma=av2;
  }
  avma=avm;
  if (DEBUGLEVEL>=1) msgtimer("testpermutation(%d)",N);
  if (DEBUGLEVEL>=2 && hop)
    fprintferr("GaloisConj:%d hop sur %d iterations\n",hop,N);
  return gzero;
}

/* Calcule la liste des sous groupes de \ZZ/m\ZZ d'ordre divisant p
et retourne la liste de leurs elements
*/
GEN
listsousgroupes(long m,long p)
{
  ulong ltop=avma,lbot;
  GEN zns,lss,res,sg,gen,ord,res1;
  int k,card,i,j,l,n,phi,h;
  if (m==2)
  {
    res=cgetg(2,t_VEC);
    sg=cgetg(2,t_VECSMALL);
    res[1]=(long)sg;
    sg[1]=1;
    return res;
  }
  zns=znstar(stoi(m));
  phi=itos((GEN)zns[1]);
  lss=subgrouplist((GEN)zns[2],0);
  gen=cgetg(lg(zns[3]),t_VECSMALL);
  ord=cgetg(lg(zns[3]),t_VECSMALL);
  res1=cgetg(lg(lss),t_VECSMALL);
  lbot=avma;
  for (k=1,i=1; i<lg(lss); i++)
  {
    long av;
    av=avma;
    card=phi/itos(det((GEN)lss[i]));
    avma=av;
    if (p%card==0)
    {
      sg=cgetg(1+card,t_VECSMALL);
      sg[1]=1;
      av=avma;
      for (j=1; j<lg(gen); j++)
      {
	gen[j]=1;
	for (h=1; h<lg(lss[i]); h++)
	  gen[j]=(gen[j]*itos(lift(powgi(((GEN **)zns)[3][h],((GEN ***)lss)[i][j][h]))))%m;
	ord[j]=itos(((GEN **)zns)[2][j])/itos(((GEN ***)lss)[i][j][j]);
      }
      avma=av;
      for (j=1,l=1; j<lg(gen); j++)
      {
	int c=l*(ord[j]-1);
	for (n=1; n<=c; n++)/*I like it*/
	  sg[++l]=(sg[n]*gen[j])%m;
      }
      res1[k++]=(long)sg;
    }
  }
  res=cgetg(k,t_VEC);
  for (i=1; i<k; i++)
    res[i]=res1[i];
  return gerepile(ltop,lbot,res);
}

/*retourne la permutation identite*/
GEN
permidentity(long l)
{
  GEN perm;
  int i;
  perm=cgetg(l+1,t_VECSMALL);
  for (i=1; i<=l; i++)
    perm[i]=i;
  return perm;
}

/*retourne la decomposition en cycle */
GEN
permtocycle(GEN p)
{
  long ltop=avma,lbot;
  int i,j,k,l,m;
  GEN bit,cycle,cy;
  cycle=cgetg(lg(p),t_VEC);
  bit=cgetg(lg(p),t_VECSMALL);
  for (i=1; i<lg(p); i++)
    bit[i]=0;
  for (k=1,l=1; k<lg(p);)
  {
    for (j=1; bit[j]; j++);
    cy=cgetg(lg(p),t_VECSMALL);
    m=1;
    do
    {
      bit[j]=1;
      k++;
      cy[m++]=j;
      j=p[j];
    }while (!bit[j]);
    setlg(cy,m);
    cycle[l++]=(long)cy;
  }
  setlg(cycle,l);
  lbot=avma;
  cycle=gcopy(cycle);
  return gerepile(ltop,lbot,cycle);
}

/*Calcule les orbites d'un ensemble de permutations*/
GEN
vecpermorbite(GEN v)
{
  ulong ltop=avma,lbot;
  int i,j,k,l,m,n,o,p,flag;
  GEN bit,cycle,cy;
  n=lg(v[1]);
  cycle=cgetg(n,t_VEC);
  bit=cgetg(n,t_VECSMALL);
  for (i=1; i<n; i++)
    bit[i]=0;
  for (k=1,l=1; k<n;)
  {
    for (j=1; bit[j]; j++);
    cy=cgetg(n,t_VECSMALL);
    m=1;
    cy[m++]=j;
    bit[j]=1;
    k++;
    do
    {
      flag=0;
      for (o=1; o<lg(v); o++)
      {
	for (p=1; p<m; p++)/*m varie!*/
	{
	  j=((long **)v)[o][cy[p]];
	  if (!bit[j])
	  {
	    flag=1;
	    bit[j]=1;
	    k++;
	    cy[m++]=j;
	  }
	}
      }
    }while (flag);
    setlg(cy,m);
    cycle[l++]=(long)cy;
  }
  setlg(cycle,l);
  lbot=avma;
  cycle=gcopy(cycle);
  return gerepile(ltop,lbot,cycle);
}

/* Calcule la permutation associe a un polynome f des racines L */
GEN
poltoperm(GEN f,GEN L)
{
  ulong ltop,ltop2;
  GEN pf,fx,fp;
  int i,j;
  pf=cgetg(lg(L),t_VECSMALL);
  ltop=avma;
  fp=cgetg(lg(L),t_VECSMALL);
  ltop2=avma;
  for (i=1; i<lg(fp); i++)fp[i]=1;
  for (i=1; i<lg(L); i++)
  {
    fx=gsubst(f,varn(f),(GEN)L[i]);
    for (j=1; j<lg(L); j++)
      if (fp[j] && gegal(fx,(GEN)L[j]))
      {
	pf[i]=j;
	fp[j]=0;
	break;
      }
    avma=ltop2;
  }
  avma=ltop;
  return pf;
}

/* Calcule un polynome R definissant  le corps fixe de T pour les orbites O
   tel que R est sans-facteur carre modulo mod et l
   retourne dans U les racines de R
*/
GEN
corpsfixeorbitemod(GEN L,GEN O,long x,GEN mod,GEN l,GEN *U)
{
  ulong ltop=avma,lbot,av,av2;
  GEN g,p,PL,*gptr[2],gmod,gl,modl;
  GEN id;
  int i,j,d;
  PL=cgetg(lg(O),t_COL);
  modl=gmodulcp(gun,l);
  av2=avma;
  d=0;
  do
  {
    avma=av2;
    id=stoi(d);
    g=polun[x];
    for (i=1; i<lg(O); i++)
    {
      p=gadd(id,(GEN)L[((GEN *)O)[i][1]]);
      for (j=2; j<lg(O[i]); j++)
	p=gmul(p,gadd(id,(GEN)L[((GEN *)O)[i][j]]));
      PL[i]=(long)p;
      g=gmul(g,gsub(polx[x],p));
    }
    lbot=avma;
    g=centerlift(g);
    av=avma;
    gmod=gmul(g,mod);
    gl=gmul(g,modl);
    if (DEBUGLEVEL>=6) fprintferr("GaloisConj:corps fixe:%d:%Z\n",d,g);
    d=(d>0 ? -d : 1-d);
  }while (degree(ggcd(deriv(gl,x),gl)) || degree(ggcd(deriv(gmod,x),gmod)));
  avma=av;
  *U=gcopy(PL);
  gptr[0]=&g;
  gptr[1]=U;
  gerepilemanysp(ltop,lbot,gptr,2);
  return g;
}

/*Calcule l'inclusion de R dans T ie S telque T|R\compo S */
GEN
corpsfixeinclusion(GEN O,GEN PL)
{
  GEN S;
  int i,j;
  S=cgetg((lg(O)-1)*(lg(O[1])-1)+1,t_COL);
  for (i=1; i<lg(O); i++)
    for (j=1; j<lg(O[i]); j++)
      S[((GEN *)O)[i][j]]=lcopy((GEN)PL[i]);
  return S;
}

/*Calcule l'inverse de la matrice de van der Monde de T multiplie par den*/
GEN
matrixbase2(GEN L,GEN T,GEN den)
{
  ulong ltop=avma,lbot;
  int i,j;
  long x=varn(T);
  GEN M,P,Tp;
  if (DEBUGLEVEL>=1) timer2();
  M=cgetg(lg(L),t_MAT);
  Tp=deriv(T,x);
  for (i=1; i<lg(L); i++)
  {
    M[i]=lgetg(lg(L),t_COL);
    P=gdiv(gdivround(T,gsub(polx[x],(GEN)L[i])),gsubst(Tp,x,(GEN)L[i]));
    for (j=1; j<lg(L); j++)
      ((GEN *)M)[i][j]=P[1+j];
  }
  if (DEBUGLEVEL>=1) msgtimer("matrixbase2");
  lbot=avma;
  M=gmul(den,M);
  return gerepile(ltop,lbot,M);
}

/*Calcule le polynome associe a un vecteur conjugue v*/
GEN
vectopol(GEN v,GEN M,GEN den,long x)
{
  ulong ltop=avma,lbot;
  GEN res;
  res=gmul(M,v);
  res=gtopolyrev(centerlift(res),x);
  lbot=avma;
  res=gdiv(res,den);
  return gerepile(ltop,lbot,res);
}

/*Calcule le polynome associe a une permuation p*/
GEN
permtopol(GEN p,GEN L,GEN M,GEN den,long x)
{
  ulong ltop=avma,lbot;
  GEN res;
  res=gmul(M,applyperm(L,p));
  res=gtopolyrev(centerlift(res),x);
  lbot=avma;
  res=gdiv(res,den);
  return gerepile(ltop,lbot,res);
}

/* factorise partiellement n sous la forme
n=d*u*f^2 ou d est sans facteur carre et u n'est pas un carre parfait
et retourne u*f
*/
GEN
mycoredisc(GEN n)
{
  ulong av=avma,tetpil,r;
  GEN y,p1,p2,ret;
  {
    long av=avma,tetpil,i;

    GEN fa,p1,p2,p3,res=gun,res2=gun,y;
    fa=auxdecomp(n,0); p1=(GEN)fa[1]; p2=(GEN)fa[2];
    for (i=1; i<lg(p1)-1; i++)
    {
      p3=(GEN)p2[i];
      if (mod2(p3)) res=mulii(res,(GEN)p1[i]);
      if (!gcmp1(p3)) res2=mulii(res2,gpui((GEN)p1[i],shifti(p3,-1),0));
    }
    p3=(GEN)p2[i];
    if (mod2(p3)) /*impaire: verifions*/
    {
      if (!gcmp1(p3)) res2=mulii(res2,gpui((GEN)p1[i],shifti(p3,-1),0));
      if (isprime((GEN)p1[i]))
	res=mulii(res,(GEN)p1[i]);
      else
	res2=mulii(res2,(GEN)p1[i]);
    }
    else /*paire:OK*/
      res2=mulii(res2,gpui((GEN)p1[i],shifti(p3,-1),0));
    tetpil=avma; y=cgetg(3,t_VEC);
    y[1]=(long)icopy(res); y[2]=(long)icopy(res2);
    ret=gerepile(av,tetpil,y);
  }
  p2=ret;
  p1=(GEN)p2[1]; r=mod4(p1); if (signe(p1)<0) r=4-r;
  if (r==1 || r==4) return (GEN)p2[2];
  tetpil=avma; y=gmul2n((GEN)p2[2],-1);
  return gerepile(av,tetpil,y);
}

/*Calcule la puissance exp dune permutation decompose en cycle*/
GEN
permcyclepow(GEN O,long exp)
{
  int j,k,n;
  GEN p;
  for (n=0,j=1; j<lg(O); j++) n+=lg(O[j])-1;
  p=cgetg(n+1,t_VECSMALL);
  for (j=1; j<lg(O); j++)
  {
    n=lg(O[j])-1;
    for (k=1; k<=n; k++)
      p[((long **)O)[j][k]]=((long **)O)[j][1+(k+exp-1)%n];
  }
  return p;
}

/*
Casse l'orbite O en sous-orbite d'odre premier
correspondant a des puissance de l'element
*/
GEN
splitorbite(GEN O)
{
  ulong ltop=avma,lbot;
  int i,n;
  GEN F,fc,res;
  n=lg(O[1])-1;
  F=factor(stoi(n));
  fc=cgetg(lg(F[1]),t_VECSMALL);
  for (i=1; i<lg(fc); i++)
    fc[i]=itos(gpow(((GEN **)F)[1][i],((GEN **)F)[2][i],DEFAULTPREC));
  lbot=avma;
  res=cgetg(lg(fc),t_VEC);
  for (i=1; i<lg(fc); i++)
  {
    GEN v;
    v=cgetg(3,t_VEC);
    res[i]=(long)v;
    v[1]=(long)permcyclepow(O,n/fc[i]);
    v[2]=(long)stoi(fc[i]);
  }
  return gerepile(ltop,lbot,res);
}

/*structure qui contient l'analyse du groupe de Galois par
  etude des degres de Frobenius: */
struct galois_analysis
{
  long p;   /* nombre premier a relever */
  long deg; /* degre */
  long exception;
  long ord;
  long l;
  long ppp;
  byteptr primepointer;
};

/*peut etre on peut accelerer(distinct degree factorisation*/
void
galoisanalysis(GEN T,struct galois_analysis *ga,long calcul_l)
{
  ulong ltop=avma;
  long n,p,ex,plift,nbmax,nbtest,exist6=0;
  GEN F,fc;
  byteptr primepointer,pp=0;
  long pha,ord,deg,ppp,pgp,ordmax=0,l=0;
  int i;
  /* Etude du cardinal:*/
  /*Calcul de l'ordre garanti d'un sous-groupe cyclique*/
  /*Tout les groupes d'ordre n sont cyclique ssi gcd(n,phi(n))==1 */
  if (DEBUGLEVEL>=1) timer2();
  n=degree(T);
  F=factor(stoi(n));
  fc=cgetg(lg(F[1]),t_VECSMALL);
  for (i=1; i<lg(fc); i++)
    fc[i]=itos(gpow(((GEN **)F)[1][i],((GEN **)F)[2][i],DEFAULTPREC));
  ppp=itos(((GEN **)F)[1][1]); /*Plus Petit diviseur Premier*/
  pgp=itos(((GEN **)F)[1][lg(F[1])-1]); /*Plus Grand diviseur Premier*/
  pha=1; ord=1; ex=0;
  for (i=lg(F[1])-1; i>0; i--)
  {
    p=itos(((GEN **)F)[1][i]);
    if (pha%p!=0)
    {
      ord*=p;
      pha*=p-1;
    }
    else
    {
      ex=1;
      break;
    }
    if (!gcmp1(((GEN **)F)[2][i]))
      break;
  }
  plift=0;
  /*Etude des ordres des Frobenius*/
  nbmax=n/2; /*Nombre maxi d'éléments à tester*/
  nbtest=0;
  deg=0;
  for (p=0,primepointer=diffptr; plift==0 || (nbtest<nbmax  && ord!=n);)
  {
    long u,s,c;
    long isram;
    GEN S;
    c=*primepointer++; if (!c) err(primer1);
    p+=c;
    if (p<=(n<<1))
      continue;
    S=(GEN)simplefactmod(T,stoi(p));
    isram=0;
    for (i=1; i<lg(S[2]) && !isram; i++)
      if (!gcmp1(((GEN **)S)[2][i]))
	isram=1;
    if (isram==0)
    {
      s=itos(((GEN **)S)[1][1]);
      for (i=2; i<lg(S[1]) && !isram; i++)
	if (itos(((GEN **)S)[1][i])!=s)
	{
	  avma=ltop;
	  if (DEBUGLEVEL>=2) fprintferr("GaloisAnalysis:non Galois for p=%d\n",p);
	  ga->p=p;
	  ga->deg=0;
	  return; /*Not a Galois polynomial*/
	}
      if (l==0 && s==1)
	l=p;
      nbtest++;
      if (nbtest>(3*nbmax) && (n==60 || n==75))
	break;
      if (s%6==0) exist6=1;
      if (DEBUGLEVEL>=6) fprintferr("GaloisAnalysis:Nbtest=%d,plift=%d,p=%d,s=%d,ord=%d\n",nbtest,plift,p,s,ord);
      if (s>ordmax) ordmax=s;
      if (s>=ord)/*Calcul de l'exposant distinguant minimal garanti*/
      {
	if (s*ppp==n)/*Tout sous groupe d'indice ppp est distingué*/
	  u=s;
	else/*Théorème de structure des groupes hyper-résoluble*/
	{
	  u=1;
	  for (i=lg(fc)-1; i>0; i--)
	  {
	    if (s%fc[i]==0)
	      u*=fc[i];
	    else
	      break;
	  }
	}
	if (u!=1)
	{
	  if (!ex || s>ord || (s==ord && ( plift==0 || u>deg)))
	  {
	    deg=u;
	    ord=s;
	    plift=p;
	    pp=primepointer;
	    ex=1;
	  }
	}
	else if (!ex && (plift==0 || s>ord))
  /*J'ai besoin de plus de connaissance sur les p-groupes, surtout pour p=2; */
	{
	  deg=pgp;
	  ord=s;
	  plift=p;
	  pp=primepointer;
	  ex=0;
	}
      }
    }
  }
  if (plift==0 || ((n==24 || n==36 || n==48) && !exist6) || (n==56 && ordmax==7) || (n==60 && ordmax==5) || (n==72 && !exist6) || (n==80 && ordmax==5))
  {
    deg=0;
    err(warner,"Galois group almost certainly not weakly super solvable");
  }
  avma=ltop;
  if (calcul_l)
  {
    ulong av;
    GEN x;
    long c;
    x=cgetg(3,t_POLMOD);
    x[2]=lpolx[varn(T)];
    av=avma;
    while (l==0)
    {
      c=*primepointer++; if (!c) err(primer1);
      p+=c;
      x[1]=lmul(T, gmodulss(1,p));
      if (gegal(gpuigs(x,p),x)) l=p;
      avma = av;
    }
    avma=ltop;
  }
  ga->p=plift;
  ga->exception=ex;
  ga->deg=deg;
  ga->ord=ord;
  ga->l=l;
  ga->primepointer=pp;
  ga->ppp=ppp;
  if (DEBUGLEVEL>=4) fprintferr("GaloisAnalysis:p=%d l=%d exc=%d deg=%d ord=%d ppp=%d\n",p,l,ex,deg,ord,ppp);
  if (DEBUGLEVEL>=1) msgtimer("galoisanalysis()");
}

/*Calcule les bornes sur les coefficients a chercher*/
struct galois_borne
{
  GEN l;
  long valsol;
  long valabs;
  GEN bornesol;
  GEN ladicsol;
  GEN ladicabs;
};

/*recalcule L avec une precision superieur */
GEN
recalculeL(GEN T,GEN Tp, GEN L,struct galois_borne *gb,struct galois_borne *ngb)
{
  ulong ltop=avma,lbot=avma;
  GEN L2,y,z,lad;
  long i,val;
   if (DEBUGLEVEL>=1) timer2();
  L2=cgetg(lg(L),typ(L));
  for (i=1; i<lg(L); i++)
  {
    ltop=avma;
    val=gb->valabs;
    lad=gb->ladicabs;
    z=(GEN)L[i];
    while (val<ngb->valabs)
    {
      val<<=1;
      if (val>=ngb->valabs)
      {
	val=ngb->valabs;
	lad=ngb->ladicabs;
      }
      else
	lad=gsqr(lad);
      y=gmodulcp((GEN)z[2],lad);
      z=gdiv(poleval(T,y),poleval(Tp,y));
      lbot=avma;
      z=gsub(y,z);
    }
    L2[i]=(long)gerepile(ltop,lbot,z);
  }
  return L2;
}

void
initborne(GEN T,GEN disc,struct galois_borne *gb,long ppp)
{
  ulong ltop=avma,lbot,av2;
  GEN borne,borneroots,borneabs;
  int i,j;
  int n;
  GEN L,M,z;
  L=roots(T,DEFAULTPREC);
  n=lg(L)-1;
  M=matrixbase2(L,T,disc);
  borne=gzero;
  for (i=1; i<=n; i++)
  {
    z=gzero;
    for (j=1; j<=n; j++)
      z=gadd(z,gabs(((GEN **)M)[j][i],DEFAULTPREC));
    if (gcmp(z,borne)>0)
      borne=z;
  }
  borneroots=gzero;
  for (i=1; i<=n; i++)
  {
    z=gabs((GEN)L[i],DEFAULTPREC);
    if (gcmp(z,borneroots)>0)
      borneroots=z;
  }
  borneabs=addsr(1,gpowgs(addsr(n,borneroots),n/ppp));
  lbot=avma;
  borneroots=addsr(1,gmul(borne,borneroots));
  av2=avma;
  borneabs=gmul2n(gmul(borne,borneabs),4);
  gb->valsol=itos(gceil(gdiv(glog(gmul2n(borneroots,4+(n>>1)),DEFAULTPREC),glog(gb->l,DEFAULTPREC))));
  if (DEBUGLEVEL>=4) fprintferr("GaloisConj:val1=%d\n",gb->valsol);
  gb->valabs=max(gb->valsol,itos(gceil(gdiv(glog(borneabs,DEFAULTPREC),glog(gb->l,DEFAULTPREC)))));
  if (DEBUGLEVEL>=4) fprintferr("GaloisConj:val2=%d\n",gb->valabs);
  avma=av2;
  gb->bornesol=gerepile(ltop,lbot,borneroots);
  gb->ladicsol=gpowgs(gb->l,gb->valsol);
  gb->ladicabs=gpowgs(gb->l,gb->valabs);
}

/*Groupe A4*/
GEN
a4galoisgen(GEN T,struct test_data *td)
{
  int ltop=avma,av,av2;
  int i,j,k;
  int n;
  int N,hop=0;
  GEN t,u;
  GEN *ar,**mt; /* tired of casting */
  long **O; /* tired of casting */
  GEN res,orb,ry;
  GEN pft,pfu,pfv;
  n=degree(T);
  res=cgetg(4,t_VEC);
  ry=cgetg(3,t_VEC);
  res[1]=(long)ry;
  pft=cgetg(n+1,t_VECSMALL);
  ry[1]=(long)pft;
  ry[2]=deux;
  ry=cgetg(3,t_VEC);
  pfu=cgetg(n+1,t_VECSMALL);
  ry[1]=(long)pfu;
  ry[2]=deux;
  res[2]=(long)ry;
  ry=cgetg(3,t_VEC);
  pfv=cgetg(n+1,t_VECSMALL);
  ry[1]=(long)pfv;
  ry[2]=lstoi(3);
  res[3]=(long)ry;
  av=avma;
  ar=(GEN *)alloue_ardoise(n,1+lg(td->ladic));
  mt=(GEN **)td->PV[td->ordre[n]];
  t=cgetg(n+1,t_VECSMALL)+1; /*Sorry for this hack*/
  u=cgetg(n+1,t_VECSMALL)+1; /*too lazy to correct*/
  av2=avma;
  N=itos(gdiv(mpfact(n),mpfact(n>>1)))>>(n>>1);
  if (DEBUGLEVEL>=4) fprintferr("A4GaloisConj:I will test %d permutations\n",N);
  avma=av2;
  for (i=0; i<n; i++)
    t[i]=i+1;
  for (i=0; i<N; i++)
  {
    GEN g;
    int a,x,y;
    if (i==0)
    {
      gaffect(gzero,ar[(n-2)>>1]);
      for (k=n-2; k>2; k-=2)
	gaddz(ar[k>>1],gadd(mt[k+1][k+2],mt[k+2][k+1]),ar[(k>>1)-1]);
    }
    else
    {
      x=i;
      y=1;
      do
      {
	hiremainder=0;
	y+=2;
	x=divll(x,y);
	a=hiremainder;
      }
      while (!a);
      switch(y)
      {
      case 3:
	x=t[2];
	if (a==1)
	{
	  t[2]=t[1]; t[1]=x;
	}
	else
	{
	  t[2]=t[0]; t[0]=x;
	}
	break;
      case 5:
	x=t[0]; t[0]=t[2]; t[2]=t[1]; t[1]=x;
	x=t[4]; t[4]=t[4-a]; t[4-a]=x;
	gaddz(ar[2],gadd(mt[t[4]][t[5]],mt[t[5]][t[4]]),ar[1]);
	break;
      case 7:
	x=t[0]; t[0]=t[4]; t[4]=t[3]; t[3]=t[1]; t[1]=t[2]; t[2]=x;
	x=t[6]; t[6]=t[6-a]; t[6-a]=x;
	gaddz(ar[3],gadd(mt[t[6]][t[7]],mt[t[7]][t[6]]),ar[2]);
	gaddz(ar[2],gadd(mt[t[4]][t[5]],mt[t[5]][t[4]]),ar[1]);
	break;
      case 9:
	x=t[0]; t[0]=t[6]; t[6]=t[5]; t[5]=t[3]; t[3]=x;
	x=t[4]; t[4]=t[1]; t[1]=x;
	x=t[8]; t[8]=t[8-a]; t[8-a]=x;
	gaddz(ar[4],gadd(mt[t[8]][t[9]],mt[t[9]][t[8]]),ar[3]);
	gaddz(ar[3],gadd(mt[t[6]][t[7]],mt[t[7]][t[6]]),ar[2]);
	gaddz(ar[2],gadd(mt[t[4]][t[5]],mt[t[5]][t[4]]),ar[1]);
	break;
      default:
	y--;
	x=t[0]; t[0]=t[2]; t[2]=t[1]; t[1]=x;
	for (k=4; k<y; k+=2)
	{
	  int j;
	  x=t[k];
	  for (j=k; j>0; j--)
	    t[j]=t[j-1];
	  t[0]=x;
	}
	x=t[y]; t[y]=t[y-a]; t[y-a]=x;
	for (k=y; k>2; k-=2)
	  gaddz(ar[k>>1],gadd(mt[t[k]][t[k+1]],mt[t[k+1]][t[k]]),ar[(k>>1)-1]);
      }
    }
    g=gadd(ar[1],gadd(gadd(mt[t[0]][t[1]],mt[t[1]][t[0]]),
		      gadd(mt[t[2]][t[3]],mt[t[3]][t[2]])));
    if (padicisint(g,td))
    {
      for (k=0; k<n; k+=2)
      {
	pft[t[k]]=t[k+1];
	pft[t[k+1]]=t[k];
      }
      if (verifietest(pft,td))
	break;
      else
	hop++;
    }
    avma=av2;
  }
  if (i==N)
  {
    avma=ltop;
    if (DEBUGLEVEL>=1 && hop)
      fprintferr("A4GaloisConj: %d hop sur %d iterations\n",hop,N);
    return gzero;
  }
  if (DEBUGLEVEL>=1 && hop)
    fprintferr("A4GaloisConj: %d hop sur %d iterations\n",hop,N);
  N=itos(gdiv(mpfact(n>>1),mpfact(n>>2)))>>1;
  avma=av2;
  if (DEBUGLEVEL>=4)fprintferr("A4GaloisConj:sigma=%Z\n",pft);
  for (i=0; i<N; i++)
  {
    GEN g;
    int a,x,y;
    if (i==0)
    {
      for (k=0; k<n; k+=4)
      {
	u[k+3]=t[k+3]; u[k+2]=t[k+1]; u[k+1]=t[k+2]; u[k]=t[k];
      }
    }
    else
    {
      x=i;
      y=-2;
      do
      {
	hiremainder=0;
	y+=4;
	x=divll(x,y);
	a=hiremainder;
      }while (!a);
      x=u[2]; u[2]=u[0]; u[0]=x;
      switch(y)
      {
      case 2:
	break;
      case 6:
	x=u[4]; u[4]=u[6]; u[6]=x;
	if (a%2==0)
	{
	  a=4-a/2;
	  x=u[6]; u[6]=u[a]; u[a]=x;
	  x=u[4]; u[4]=u[a-2]; u[a-2]=x;
	}
	break;
      case 10:
	x=u[6]; u[6]=u[3]; u[3]=u[2]; u[2]=u[4]; u[4]=u[1]; u[1]=u[0]; u[0]=x;
	if (a>=3)
	  a+=2;
	a=8-a;
	x=u[10]; u[10]=u[a]; u[a]=x;
	x=u[8]; u[8]=u[a-2]; u[a-2]=x;
	break;
      }
    }
    g=gzero;
    for (k=0; k<n; k+=2)
      g=gadd(g,gadd(mt[u[k]][u[k+1]],mt[u[k+1]][u[k]]));
    if (padicisint(g,td))
    {
      for (k=0; k<n; k+=2)
      {
	pfu[u[k]]=u[k+1];
	pfu[u[k+1]]=u[k];
      }
      if (verifietest(pfu,td))
	break;
      else
	hop++;
    }
    avma=av2; 	
  }
  if (i==N)
  {
    avma=ltop;
    return gzero;
  }
  if (DEBUGLEVEL>=1 && hop)
    fprintferr("A4GaloisConj: %d hop sur %d iterations\n",hop,N);
  if (DEBUGLEVEL>=4)fprintferr("A4GaloisConj:tau=%Z\n",u);
  avma=av2;
  orb=cgetg(3,t_VEC);
  orb[1]=(long)pft;
  orb[2]=(long)pfu;
  if (DEBUGLEVEL>=4)fprintferr("A4GaloisConj:orb=%Z\n",orb);
  O=(long**)vecpermorbite(orb);
  if (DEBUGLEVEL>=4)fprintferr("A4GaloisConj:O=%Z\n",O);
  av2=avma;
  for (j=0; j<2; j++)
  {
    pfv[O[1][1]]=O[2][1];
    pfv[O[1][2]]=O[2][3+j];
    pfv[O[1][3]]=O[2][4-(j<<1)];
    pfv[O[1][4]]=O[2][2+j];
#define swap(a,b) { long _x=a; a=b; b=_x; }
    for (i=0; i<4; i++)
    {
      GEN g;
      switch(i)
      {
      case 0: break;
      case 1:
	swap(O[3][1], O[3][2]);
	swap(O[3][3], O[3][4]); break;
      case 2:
        swap(O[3][1], O[3][4]);
	swap(O[3][2], O[3][3]); break;
      case 3:
        swap(O[3][1], O[3][2]);
	swap(O[3][3], O[3][4]);
      }
      pfv[O[2][1]]=O[3][1];
      pfv[O[2][3+j]]=O[3][4-j];
      pfv[O[2][4-(j<<1)]]=O[3][2+(j<<1)];
      pfv[O[2][2+j]]=O[3][3-j];
      pfv[O[3][1]]=O[1][1];
      pfv[O[3][4-j]]=O[1][2];
      pfv[O[3][2+(j<<1)]]=O[1][3];
      pfv[O[3][3-j]]=O[1][4];
      g=gzero;
      for (k=1; k<=n; k++)
	g=gadd(g,mt[k][pfv[k]]);
      if (padicisint(g,td) && verifietest(pfv,td))
      {
	avma=av;
	if (DEBUGLEVEL>=1)fprintferr("A4GaloisConj:%d hop sur %d iterations max\n",hop,10395+68);
	return res;
      }
      else
	hop++;
      avma=av2;
    }
  }
  /*Echec?*/
  avma=ltop;
  return gzero;
}

GEN
galoisgen(GEN T,GEN L,GEN M,GEN den,struct galois_borne *gb,const struct galois_analysis *ga)/*Grothendieck?*/
{
  struct galois_analysis Pga;
  struct galois_borne Pgb;
  struct test_data td;
  ulong ltop=avma,lbot;
  long n,p,deg,ex;
  byteptr primepointer;
  long sg,Pm=0,fp;
  long x=varn(T);
  int i,j;
  GEN Tmod,res,pf=gzero,split,psi,ip,mod,ppsi;
  GEN frob;
  GEN O;
  GEN P,PG,PL,Pden,PM,Pmod,Pp;
  GEN *lo; /*tired of casting*/
  n=degree(T);
  if (!ga->deg)
    return gzero;
  p=ga->p;
  ex=ga->exception;
  deg=ga->deg;
  primepointer=ga->primepointer;
  if (DEBUGLEVEL>=9)  fprintferr("GaloisConj:denominator:%Z\n",den);
  if (n==12 && ga->ord==3)/*A4 is very probable,so test it first*/
  {
    long av=avma;
    if (DEBUGLEVEL>=4) fprintferr("GaloisConj:Testing A4 first\n");
    inittest(L,M,gb->bornesol,gb->ladicsol,&td);
    lbot=avma;
    PG=a4galoisgen(T,&td);
    freetest(&td);
    if (PG!=gzero)
    {
      return gerepile(ltop,lbot,PG);
    }
    avma=av;
  }
  for (;;)
  {
    long isram;
    long c;
    ip=stoi(p);
    Tmod=(GEN)factmod(T,ip);
    isram=0;
    for (i=1; i<lg(Tmod[2]) && !isram; i++)
      if (!gcmp1(((GEN **)Tmod)[2][i]))
	isram=1;
    if (isram==0)
    {
      fp=degree(((GEN **)Tmod)[1][1]);
      for (i=2; i<lg(Tmod[1]); i++)
	if (degree(((GEN**)Tmod)[1][i])!=fp)
	{
	  avma=ltop;
	  return gzero; /*Not Galois polynomial*/
	}
      if (fp%deg==0)
      {
	if (DEBUGLEVEL>=4) fprintferr("Galoisconj:p=%d deg=%d fp=%d\n",p,deg,fp);
	lo=(GEN *)listsousgroupes(deg,n/fp);
	if (DEBUGLEVEL>=4) fprintferr("Galoisconj:Subgroups list:%Z\n",(GEN)lo);
	if ( deg==fp  && cgcd(deg,n/deg)==1)
	  for (sg=1; sg<lg(lo); sg++)
	  {
	    frob=frobeniusliftall((GEN)Tmod[1],lo[sg],fp/deg,T,den,ip,gb->bornesol,&psi,L);
	    if (frob!=gzero)
	      goto suite;
	  }
	  else
	  for (sg=lg(lo)-1; sg>=1; sg--)/*Start with the fastest*/
	  {
	    frob=frobeniusliftall((GEN)Tmod[1],lo[sg],fp/deg,T,den,ip,gb->bornesol,&psi,L);
	    if (frob!=gzero)
	      goto suite;
	  }
	if (ex==1 && (n==12 || n%12!=0))
	{
	  avma=ltop;
	  return gzero;
	}
	else
	{
	  ex--;
	  if (n%12==0)
	  {
	    if (n%36==0)
	      deg=5-deg;
	    else
	      deg=2; /*For group like Z/2ZxA4*/
	  }
	  if (n%12==0 && ex==-5)
	    err(warner,"galoisconj _may_ hang up for this polynomial");
	}
      }
    }
    c=*primepointer++;
    if (!c) err(primer1);
    p+=c;
    if (DEBUGLEVEL>=4)fprintferr("GaloisConj:next p=%d\n",p);
  }
 suite:/*Djikstra probably hates me. (Linus Torvalds linux/kernel/sched.c)*/
  if (deg==n)/*Cyclique*/
  {
    lbot=avma;
    res=cgetg(2,t_VEC);
    res[1]=lgetg(3,t_VEC);
    ((GEN **)res)[1][1]=gcopy(frob);
    ((GEN **)res)[1][2]=stoi(deg);
    return gerepile(ltop,lbot,res);
  }
  if (DEBUGLEVEL>=9)fprintferr("GaloisConj:Frobenius:%Z\n",frob);
  O=permtocycle(frob);
  if (DEBUGLEVEL>=9)fprintferr("GaloisConj:Orbite:%Z\n",O);
  {
    GEN S,Tp,Fi,Sp;
    long gp=n/fp;
    ppsi=cgetg(gp+1,t_VECSMALL);
    mod=gmodulcp(gun,ip);
    P=corpsfixeorbitemod(L,O,x,mod,gb->l,&PL);
    S=corpsfixeinclusion(O,PL);
    S=vectopol(S,M,den,x);
    if (DEBUGLEVEL>=6)fprintferr("GaloisConj:Inclusion:%Z\n",S);
    Pmod=(GEN)factmod(P,ip)[1];
    Tp=gmul(T,mod);
    Sp=gmul(S,mod);
    Pp=gmul(P,mod);
    if (DEBUGLEVEL>=4)fprintferr("GaloisConj:psi=%Z\n",psi);
    if (DEBUGLEVEL>=4)fprintferr("GaloisConj:Pmod=%Z\n",Pmod);
    if (DEBUGLEVEL>=4)fprintferr("GaloisConj:Tmod=%Z\n",Tmod);
    for (i=1; i<=gp; i++)
    {
      Fi=ggcd(Tp,gsubst((GEN)Pmod[i],x,Sp));
      Fi=gdiv(Fi,(GEN)Fi[lgef(Fi)-1]);
      if (DEBUGLEVEL>=6)fprintferr("GaloisConj:Fi=%Z  %d",Fi,i);
      for (j=1; j<=gp; j++)
	if (gegal(Fi,((GEN **)Tmod)[1][j]))
	  break;
      if (DEBUGLEVEL>=6)fprintferr("-->%d\n",j);
      if (j==gp+1)
      {
	avma=ltop;
	return gzero;
      }
      if (j==gp)
      {
	Pm=i;
	ppsi[i]=1;
      }
      else
	ppsi[i]=psi[j];
    }
    if (DEBUGLEVEL>=4)fprintferr("GaloisConj:Pm=%d   ppsi=%Z\n",Pm,ppsi);
    galoisanalysis(P,&Pga,0);
    if (Pga.deg==0)
    {
      avma=ltop;
      return gzero; /*Avoid computing the discriminant*/
    }
    Pden=gabs(mycoredisc(discsr(P)),DEFAULTPREC);
    Pgb.l=gb->l;
    initborne(P,Pden,&Pgb,Pga.ppp);
    if (Pgb.valabs>gb->valabs)
      PL=recalculeL(P,deriv(P,x),PL,gb,&Pgb);
    PM=matrixbase2(PL,P,Pden);
    PG=galoisgen(P,PL,PM,Pden,&Pgb,&Pga);
  }
  if (DEBUGLEVEL>=4)fprintferr("GaloisConj:Retour sur Terre:%Z\n",PG);
  if (PG==gzero)
  {
    avma=ltop;
    return gzero;
  }
  inittest(L,M,gb->bornesol,gb->ladicsol,&td);
  split=splitorbite(O);
  lbot=avma;
  res=cgetg(lg(PG)+lg(split)-1,t_VEC);
  for (i=1; i<lg(split); i++)
    res[i]=lcopy((GEN)split[i]);
  for (j=1; j<lg(PG); j++)
  {
    ulong lbot=0,av=avma;
    GEN B,tau;
    long t,g;
    long w,sr,dss;
    if (DEBUGLEVEL>=6) fprintferr("GaloisConj:G[%d][1]=%Z\n",j,((GEN**)PG)[j][1]);
    B=permtocycle(((GEN**)PG)[j][1]); if (DEBUGLEVEL>=6) fprintferr("GaloisConj:B=%Z\n",B);
    tau=gmul(mod,permtopol(((GEN**)PG)[j][1],PL,PM,Pden,x));
    tau=gsubst((GEN)Pmod[Pm],x,tau);
    tau=ggcd(Pp,tau);
    tau=gdiv(tau,(GEN)tau[lgef(tau)-1]); if (DEBUGLEVEL>=6) fprintferr("GaloisConj:tau=%Z\n",tau);
    for (g=1; g<lg(Pmod); g++)
      if (gegal(tau,(GEN)Pmod[g]))
	break;
    if (g==lg(Pmod))
    {
      freetest(&td);
      avma=ltop;
      return gzero;
    }
    w=((long **)lo)[sg][ppsi[g]];
    dss=deg/cgcd(deg,w-1);
    sr=1;
    for (i=1; i<lg(B[1])-1; i++)
      sr=(1+sr*w)%deg;
    sr=cgcd(sr,deg);
    if (DEBUGLEVEL>=6)fprintferr("GaloisConj:w=%d [%d] sr=%d dss=%d\n",w,deg,sr,dss);
    for (t=0; t<sr; t+=dss)
    {
      lbot=avma;
      pf=testpermutation(O,B,w,t,sr,&td);
      if (pf!=gzero)
	break;
    }
    if (pf==gzero)
    {
      freetest(&td);
      avma=ltop;
      return gzero;
    }
    else
    {
      GEN f;
      f=cgetg(3,t_VEC);
      f[1]=(long)pf;
      f[2]=(long)gcopy(((GEN **)PG)[j][2]);
      res[lg(split)+j-1]=(long)gerepile(av,lbot,f);
    }
  }
  if (DEBUGLEVEL>=4) fprintferr("GaloisConj:Fini!\n");
  freetest(&td);
  return gerepile(ltop,lbot,res);
}

/* T: polynome ou nf
   den optionnel: si présent doit etre un multiple du dénominateur commun des solutions
   Si T est un nf et den n'est pas présent, le denominateur de la base d'entiers est pris pour den
*/
GEN
billgaloisconj(GEN T,GEN den)
{
  ulong ltop=avma,lbot;
  GEN G,L,M,res,aut;
  struct galois_analysis ga;
  struct galois_borne gb;
  int n,i,j,k;
  if (typ(T)!=t_POL)
  {
    T=checknf(T);
    if (!den)
      den=gcoeff((GEN)T[8],degree((GEN)T[1]),degree((GEN)T[1]));
    T=(GEN)T[1];
  }
  n=lgef(T)-3; if (n<=0) err(constpoler,"billgaloisconj");
  for (k=2; k<=n+2; k++)
    if (typ(T[k])!=t_INT)
      err(talker,"polynomial not in Z[X] in billgaloisconj");
  if (!gcmp1((GEN)T[n+2]))
      err(talker,"non-monic polynomial in billgaloisconj");
  n=degree(T);
  if (n==1)/*Too easy!*/
  {
    res=cgetg(2,t_VEC);
    res[1]=(long)polx[varn(T)];
    return res;
  }
  galoisanalysis(T,&ga,1);
  if (ga.deg==0)
    return gzero; /*Avoid computing the discriminant*/
  if (!den)
    den=gabs(mycoredisc(discsr(T)),DEFAULTPREC);
  else
  {
    if (typ(den)!=t_INT)
      err(talker,"Second arg. must be integer in billgaloisconj");
    den=gabs(den,DEFAULTPREC);
  }
  gb.l=stoi(ga.l);
  initborne(T,den,&gb,ga.ppp);
  if (DEBUGLEVEL>=1) timer2();
  L=gmul(gtrunc(rootpadic(T,gb.l,gb.valabs)),gmodulcp(gun,gb.ladicabs));
  if (DEBUGLEVEL>=1) msgtimer("rootpadic()");
  M=matrixbase2(L,T,den);
  G=galoisgen(T,L,M,den,&gb,&ga);
  if (DEBUGLEVEL>=6)fprintferr("GaloisConj:%Z\n",G);
  if (G==gzero)
  {
    avma=ltop;
    return gzero;
  }
  if (DEBUGLEVEL>=1) timer2();
  res=cgetg(n+1,t_VEC);
  res[1]=(long)permidentity(n);
  k=1;
  for (i=1; i<lg(G); i++)
  {
    int c=k*(itos(((GEN **)G)[i][2])-1);
    for (j=1; j<=c; j++)/*I like it*/
      res[++k]=(long)applyperm((GEN)res[j],((GEN **)G)[i][1]);
  }
  L=gmul(L,gmodulcp(gun,gb.ladicsol));
  M=gmul(M,gmodulcp(gun,gb.ladicsol));
  lbot=avma;
  aut=cgetg(n+1,t_VEC);
  for (i=1; i<=n; i++)
    aut[i]=(long)permtopol((GEN)res[i],L,M,den,varn(T));
  if (DEBUGLEVEL>=1) msgtimer("Calcul polynomes");
  return gerepile(ltop,lbot,aut);
}

GEN
galoisconj0(GEN nf,long flag,GEN d,long prec)
{
  switch(flag)
  {
    case 0: return galoisconj(nf);
    case 2: return galoisconj1(nf);
    case 3: return galoisconj2(nf,prec);
    case 4: return billgaloisconj(nf,d);
    default: err(flagerr,"nfgaloisconj");
  }
  return NULL; /* not reached */
}

