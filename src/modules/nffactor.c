/*******************************************************************/
/*                                                                 */
/*             Factorisation dans un corps de nombres              */
/*                  et modulo un ideal premier                     */
/*                                                                 */
/*******************************************************************/
/* $Id$ */
#include "pari.h"

GEN hensel_lift(GEN pol,GEN fk,GEN fkk,GEN p,long e);
GEN hensel_lift_fact(GEN pol, GEN fact, GEN p, GEN pev, long e);
GEN nf_get_T2(GEN base, GEN polr);
GEN nfreducemodpr_i(GEN x, GEN prh);
GEN sort_factor(GEN y, int (*cmp)(GEN,GEN));
GEN pidealprimeinv(GEN nf, GEN x);

static GEN nf_pol_mul(GEN nf,GEN pol1,GEN pol2);
static GEN nf_pol_sqr(GEN nf,GEN pol1);
static GEN nf_pol_divres(GEN nf,GEN pol1,GEN pol2, GEN *pr);
static GEN nf_pol_subres(GEN nf,GEN pol1,GEN pol2);
static GEN nfmod_pol_reduce(GEN nf,GEN prhall,GEN pol);
static GEN nfmod_pol_mul(GEN nf,GEN prhall,GEN pol1,GEN pol2);
static GEN nfmod_pol_sqr(GEN nf,GEN prhall,GEN pol1);
static GEN nfmod_pol_divres(GEN nf,GEN prhall,GEN pol1,GEN pol2, GEN *pr);
static GEN nfmod_split2(GEN nf,GEN prhall,GEN pmod,GEN pol,GEN exp);
static GEN nfmod_pol_gcd(GEN nf,GEN prhall,GEN pol1,GEN pol2);
static GEN nfmod_pol_pow(GEN nf,GEN prhall,GEN pmod,GEN pol,GEN exp);
static GEN nf_bestlift(GEN id,GEN idinv,GEN den,GEN elt);
static GEN nf_pol_lift(GEN id,GEN idinv,GEN den,GEN pol);
static GEN nfsqff(GEN nf,GEN pol,long fl);
static int nf_combine_factors(GEN nf,long fxn,GEN psf,long dlim,long hint);

typedef struct Nfcmbf /* for use in nfsqff */
{
  GEN pol, h, hinv, fact, res, lt, den;
  long nfact, nfactmod;
} Nfcmbf;
static Nfcmbf nfcmbf;

static GEN
unifpol0(GEN nf,GEN pol,long flag)
{
  static long n = 0;
  static GEN vun = NULL;
  GEN f = (GEN) nf[1];
  long i = lgef(f)-3, av;

  if (i != n)
  {
    n=i; if (vun) free(vun);
    vun = (GEN) gpmalloc((n+1)*sizeof(long));
    vun[0] = evaltyp(t_COL) | evallg(n+1); vun[1]=un;
    for ( ; i>=2; i--) vun[i]=zero;
  }

  av = avma;
  switch(typ(pol))
  {
    case t_INT: case t_FRAC: case t_RFRAC:
      pol = gmul(pol,vun); break;

    case t_POL:
      pol = gmodulcp(pol,f); /* fall through */
    case t_POLMOD:
      pol = algtobasis(nf,pol);
  }
  if (flag) pol = basistoalg(nf, lift(pol));
  return gerepileupto(av,pol);
}

/* Pour pol un polynome a coefficients dans Z, nf ou l'algebre correspondant
 * renvoie le meme polynome avec pour coefficients:
 *  si flag=0: des vecteurs sur la base d'entiers.
 *  si flag=1: des polymods.
 */
GEN
unifpol(GEN nf,GEN pol,long flag)
{
  if (typ(pol)==t_POL && varn(pol) < varn(nf[1]))
  {
    long i, d = lgef(pol);
    GEN p1 = pol;

    pol=cgetg(d,t_POL); pol[1]=p1[1];
    for (i=2; i<d; i++)
      pol[i] = (long) unifpol0(nf,(GEN) p1[i],flag);

    return pol;
  }
  return unifpol0(nf,(GEN) pol, flag);
}

/* cree un polynome unitaire de degre d a entrees au hazard dans Z_nf */
GEN
random_pol(GEN nf,long d)
{
  long i,j, n = lgef(nf[1])-3;
  GEN pl,p;

  pl=cgetg(d+3,t_POL);
  for (i=2; i<d+2; i++)
  {
    p=cgetg(n+1,t_COL); pl[i]=(long)p;
    for (j=1; j<=n; j++)
      p[j] = lstoi(mymyrand()%101 - 50);
  }
  p=cgetg(n+1,t_COL); pl[i]=(long)p;
  p[1]=un; for (i=2; i<=n; i++) p[i]=zero;

  pl[1] = evalsigne(1) | evallgef(d+3) | evalvarn(0);
  return pl;
}

/* multiplication de x par y dans nf (x element accepte) */
static GEN
nf_pol_mul(GEN nf,GEN x,GEN y)
{
  long tetpil,av=avma;
  GEN res = gmul(unifpol(nf,x,1), unifpol(nf,y,1));

  tetpil = avma;
  return gerepile(av,tetpil,unifpol(nf,res,0));
}

/* calcule x^2 dans nf (x element accepte) */
static GEN
nf_pol_sqr(GEN nf,GEN x)
{
  long tetpil,av=avma;
  GEN res = gsqr(unifpol(nf,x,1));

  tetpil = avma;
  return gerepile(av,tetpil,unifpol(nf,res,0));
}

/* Reduction modulo phall des coefficients de pol (pol element accepte) */
static GEN
nfmod_pol_reduce(GEN nf,GEN prhall,GEN pol)
{
  long av=avma,tetpil,i;
  GEN p1;

  if (typ(pol)!=t_POL) return nfreducemodpr(nf,pol,prhall);
  pol=unifpol(nf,pol,0);

  tetpil=avma; i=lgef(pol);
  p1=cgetg(i,t_POL); p1[1]=pol[1];
  for (i--; i>=2; i--)
    p1[i] = (long) nfreducemodpr(nf,(GEN)pol[i],prhall);
  return gerepile(av,tetpil, normalizepol(p1));
}

/* x^2 modulo prhall ds nf (x elt accepte) */
static GEN
nfmod_pol_sqr(GEN nf,GEN prhall,GEN x)
{
  long av=avma,tetpil;
  GEN px;

  px = nfmod_pol_reduce(nf,prhall,x);
  px = unifpol(nf,lift(px),1);
  px = unifpol(nf,nf_pol_sqr(nf,px),0);
  tetpil=avma;
  return gerepile(av,tetpil,nfmod_pol_reduce(nf,prhall,px));
}

/* multiplication des polynomes x et y modulo prhall ds nf (x elt accepte) */
static GEN
nfmod_pol_mul(GEN nf,GEN prhall,GEN x,GEN y)
{
  long av=avma,tetpil;
  GEN px,py;

  px = nfmod_pol_reduce(nf,prhall,x); px = unifpol(nf,lift(px),1);
  py = nfmod_pol_reduce(nf,prhall,y); py = unifpol(nf,lift(py),1);
  px = unifpol(nf,nf_pol_mul(nf,px,py),0);
  tetpil=avma;
  return gerepile(av,tetpil,nfmod_pol_reduce(nf,prhall,px));
}

/* division euclidienne du polynome x par le polynome y */
static GEN
nf_pol_divres(GEN nf,GEN x,GEN y,GEN *pr)
{
  long av = avma,tetpil;
  GEN nq = poldivres(unifpol(nf,x,1),unifpol(nf,y,1),pr);
  GEN *gptr[2];

  tetpil=avma; nq=unifpol(nf,nq,0);
  if (pr) *pr = unifpol(nf,*pr,0);
  gptr[0]=&nq; gptr[1]=pr;
  gerepilemanysp(av,tetpil,gptr,pr ? 2:1);
  return nq;
}

/* division euclidienne du polynome x par le polynome y modulo prhall */
static GEN
nfmod_pol_divres(GEN nf,GEN prhall,GEN x,GEN y, GEN *pr)
{
  long av=avma,dx,dy,dz,i,j,k,l,n,tetpil;
  GEN z,p1,p2,p3,px,py;

  py = nfmod_pol_reduce(nf,prhall,y);
  if (gcmp0(py))
    err(talker, "division by zero in nfmod_pol_divres");

  tetpil=avma;
  px=nfmod_pol_reduce(nf,prhall,x);
  dx=lgef(px)-3; dy=lgef(py)-3; dz=dx-dy;
  if (dx<dy)
  {
    GEN vzero;

    if (pr) *pr = gerepile(av,tetpil,px);
    else avma = av;

    n=lgef(nf[1])-3;
    vzero = cgetg(n+1,t_COL);
    n=lgef(nf[1])-3;
    for (i=1; i<=n; i++) vzero[i]=zero;

    z=cgetg(3,t_POL); z[2]=(long)vzero;
    z[1]=evallgef(2) | evalvarn(varn(px));
    return z;
  }

  z=cgetg(dz+3,t_POL); z[1]=evalsigne(1) | evallgef(3+dz);
  setvarn(z,varn(px));
  z[dz+2] = (long) element_divmodpr(nf,(GEN)px[dx+2],(GEN)py[dy+2],prhall);
  for (i=dx-1; i>=dy; --i)
  {
    l=avma; p1=nfreducemodpr(nf,(GEN)px[i+2],prhall);
    for (j=i-dy+1; j<=i && j<=dz; j++)
    {
      p2=element_mul(nf,(GEN)z[j+2],(GEN)py[i-j+2]);
      p2=nfreducemodpr(nf,p2,prhall); p1=gsub(p1,p2);
    }
    tetpil=avma; p3=element_divmodpr(nf,p1,(GEN)py[dy+2],prhall);
    z[i-dy+2]=lpile(l,tetpil,p3);
    z[i-dy+2]=(long)nfreducemodpr(nf,(GEN)z[i-dy+2],prhall);
  }
  l=avma;
  for (i=dy-1; i>=0; --i)
  {
    l=avma; p1=((GEN)px[i+2]);
    for (j=0; j<=i && j<=dz; j++)
    {
      p2=element_mul(nf,(GEN)z[j+2],(GEN)py[i-j+2]);
      p2=nfreducemodpr(nf,p2,prhall); tetpil=avma; p1=gsub(p1,p2);
    }
    p1=gerepile(l,tetpil,p1);
    if (!gcmp0(nfreducemodpr(nf,p1,prhall))) break;
  }

  if (!pr) { avma = l; return z; }

  if (i<0)
  {
    avma=l;
    p3 = cgetg(3,t_POL); p3[2]=zero;
    p3[1] = evallgef(2) | evalvarn(varn(px));
    *pr=p3; return z;
  }

  p3=cgetg(i+3,t_POL);
  p3[1]=evalsigne(1) | evallgef(i+3) | evalvarn(varn(px));
  p3[i+2]=(long)nfreducemodpr(nf,p1,prhall);
  for (k=i-1; k>=0; --k)
  {
    l=avma; p1=((GEN)px[k+2]);
    for (j=0; j<=k && j<=dz; j++)
    {
      p2=element_mul(nf,(GEN)z[j+2],(GEN)py[k-j+2]);
      p2=nfreducemodpr(nf,p2,prhall); tetpil=avma; p1=gsub(p1,p2);
    }
    p3[k+2]=lpile(l,tetpil,nfreducemodpr(nf,p1,prhall));
  }
  *pr=p3; return z;
}

/* PGCD des polynomes x et y, par l'algorithme du sub-resultant */
static GEN
nf_pol_subres(GEN nf,GEN x,GEN y)
{
  long av=avma,tetpil;
  GEN s = srgcd(unifpol(nf,x,1), unifpol(nf,y,1));

  tetpil=avma; return gerepile(av,tetpil,unifpol(nf,s,1));
}

/* PGCD des polynomes x et y modulo prhall */
static GEN
nfmod_pol_gcd(GEN nf,GEN prhall,GEN x,GEN y)
{
  long av=avma;
  GEN p1,p2;

  if (lgef(x)<lgef(y)) { p1=y; y=x; x=p1; }
  p1=nfmod_pol_reduce(nf,prhall,x);
  p2=nfmod_pol_reduce(nf,prhall,y);
  while (!isexactzero(p2))
  {
    GEN p3;

    nfmod_pol_divres(nf,prhall,p1,p2,&p3);
    p1=p2; p2=p3;
  }
  return gerepileupto(av,p1);
}

/* Calcul pol^e modulo prhall et le polynome pmod */
static GEN
nfmod_pol_pow(GEN nf,GEN prhall,GEN pmod,GEN pol,GEN e)
{
  long i, av = avma, n = lgef(nf[1])-3;
  GEN p1,p2,vun;

  vun=cgetg(n+1,t_COL); vun[1]=un; for (i=2; i<=n; i++) vun[i]=zero;
  p1=gcopy(polun[varn(pol)]); p1[2]=(long)vun;
  if (gcmp0(e)) return p1;

  p2=nfmod_pol_reduce(nf,prhall,pol);
  for(;;)
  {
    if (!vali(e))
    {
      p1=nfmod_pol_mul(nf,prhall,p1,p2);
      nfmod_pol_divres(nf,prhall,p1,pmod,&p1);
    }
    if (gcmp1(e)) break;

    e=shifti(e,-1);
    p2=nfmod_pol_sqr(nf,prhall,p2);
    nfmod_pol_divres(nf,prhall,p2,pmod,&p2);
  }
  return gerepileupto(av,p1);
}

/* factorisation du polynome x modulo pr */
GEN
nffactormod(GEN nf,GEN pol,GEN pr)
{
  long av = avma, tetpil,lb,nbfact,psim,N,n,i,j,k,d,e,vf,r,kk;
  GEN y,ex,*t,f1,f2,f3,df1,g1,polb,pold,polu,vker;
  GEN Q,f,x,u,v,v2,v3,vz,q,vun,vzero,prhall;

  nf=checknf(nf);
  if (typ(pol)!=t_POL) err(typeer,"nffactormod");
  if (varn(pol) >= varn(nf[1]))
    err(talker,"polynomial variable must have highest priority in nffactormod");

  prhall=nfmodprinit(nf,pr); n=lgef(nf[1])-3;
  vun = gscalcol_i(gun, n);
  vzero = gscalcol_i(gzero, n);

  f=unifpol(nf,pol,0); f=nfmod_pol_reduce(nf,prhall,f);
  d=lgef(f)-3; vf=varn(f);
  t = (GEN*)new_chunk(d+1);
  ex= new_chunk(d+1);
  x=gcopy(polx[vf]); x[3]=(long)vun; x[2]=(long)vzero;
  if (d<=1) { nbfact=2; t[1] = f; ex[1]=1; }
  else
  {
    q = (GEN)pr[1]; psim = VERYBIGINT;
    if (!is_bigint(q)) psim = itos(q);
   /* psim has an effect only when p is small. If too big, set it to a huge
    * number (i.e ignore it) to avoid an error in itos on next line.
    */
    q=gpuigs(q, itos((GEN)pr[4]));
    f1=f; e=1; nbfact=1;
    while (lgef(f1)>3)
    {
      df1=deriv(f1,vf); f2=nfmod_pol_gcd(nf,prhall,f1,df1);
      g1=nfmod_pol_divres(nf,prhall,f1,f2,NULL); k=0;
      while (lgef(g1)>3)
      {
	k++;
	if (k%psim == 0)
	{
	  k++; f2=nfmod_pol_divres(nf,prhall,f2,g1,NULL);
	}
	f3=nfmod_pol_gcd(nf,prhall,f2,g1);
	u = nfmod_pol_divres(nf,prhall,g1,f3,NULL);
	f2= nfmod_pol_divres(nf,prhall,f2,f3,NULL);
	g1=f3;
	if (lgef(u)>3)
	{
	  N=lgef(u)-3; Q=cgetg(N+1,t_MAT);
	  v3=cgetg(N+1,t_COL); Q[1]=(long)v3;
	  v3[1]=(long)vun; for (i=2; i<=N; i++) v3[i]=(long)vzero;
	
	  v2 = v = nfmod_pol_pow(nf,prhall,u,x,q);
	  for (j=2; j<=N; j++)
	  {
	    v3=cgetg(N+1,t_COL); Q[j]=(long)v3;
	    for (i=1; i<=lgef(v2)-2; i++) v3[i]=v2[i+1];
	    for (; i<=N; i++) v3[i]=(long)vzero;
	    if (j<N)
	    {
	      v2=nfmod_pol_mul(nf,prhall,v2,v);
	      nfmod_pol_divres(nf,prhall,v2,u,&v2);
	    }
	  }
	  for (i=1; i<=N; i++)
	    coeff(Q,i,i)=lsub((GEN)coeff(Q,i,i),vun);
	  v2=nfkermodpr(nf,Q,prhall); r=lg(v2)-1; t[nbfact]=gcopy(u); kk=1;
	  if (r>1)
	  {
	    vker=cgetg(r+1,t_COL);
	    for (i=1; i<=r; i++)
	    {
	      v3=cgetg(N+2,t_POL);
	      v3[1]=evalsigne(1)+evallgef(2+N); setvarn(v3,vf);
	      vker[i]=(long)v3; for (j=1; j<=N; j++) v3[j+1]=coeff(v2,j,i);
	      normalizepol(v3);
	    }
	  }
	  while (kk<r)
	  {
	    v=gcopy(polun[vf]); v[2]=(long)vzero;
	    for (i=1; i<=r; i++)
	    {
	      vz=cgetg(n+1,t_COL);
	      for (j=1; j<=n; j++)
		vz[j] = lmodsi(mymyrand()>>8, q);
	      vz=nfreducemodpr(nf,vz,prhall);
	      v=gadd(v,nfmod_pol_mul(nf,prhall,vz,(GEN)vker[i]));
	    }
	    for (i=1; i<=kk && kk<r; i++)
	    {
	      polb=t[nbfact+i-1]; lb=lgef(polb);
	      if (lb>4)
	      {
		if(psim==2)
		  polu=nfmod_split2(nf,prhall,polb,v,q);
		else
		{
		  polu=nfmod_pol_pow(nf,prhall,polb,v,shifti(q,-1));
                  polu=gsub(polu,vun);
		}
                pold=nfmod_pol_gcd(nf,prhall,polb,polu);
		if (lgef(pold)>3 && lgef(pold)<lb)
		{
		  t[nbfact+i-1]=pold; kk++;
		  t[nbfact+kk-1]=nfmod_pol_divres(nf,prhall,polb,pold,NULL);
		}
	      }
	    }
	  }
	  for (i=nbfact; i<nbfact+r; i++) ex[i]=e*k;
	  nbfact+=r;
	}
      }
      e*=psim; j=(lgef(f2)-3)/psim+3; f1=cgetg(j,t_POL);
      f1[1] = evalsigne(1) | evallgef(j) | evalvarn(vf);
      for (i=2; i<j; i++)
	f1[i]=(long)element_powmodpr(nf,(GEN)f2[psim*(i-2)+2],
				     gdiv(q,(GEN)pr[1]),prhall);
    }
  }
  if (nbfact < 2)
    err(talker, "%Z not a prime (nffactormod)", q);
  v=element_divmodpr(nf,vun,gmael(t,1,lgef(t[1])-1),prhall);
  t[1]=unifpol(nf,nfmod_pol_mul(nf,prhall,v,(GEN)t[1]),1);
  for (j=2; j<nbfact; j++)
    if (ex[j])
    {
      v=element_divmodpr(nf,vun,gmael(t,j,lgef(t[j])-1),prhall);
      t[j]=unifpol(nf,nfmod_pol_mul(nf,prhall,v,(GEN)t[j]),1);
    }

  tetpil=avma; y=cgetg(3,t_MAT);
  u=cgetg(nbfact,t_COL); y[1]=(long)u;
  v=cgetg(nbfact,t_COL); y[2]=(long)v;
  for (j=1,k=0; j<nbfact; j++)
    if (ex[j])
    {
      k++;
      u[k]=lcopy((GEN)t[j]);
      v[k]=lstoi(ex[j]);
    }
  return gerepile(av,tetpil,y);
}

/* Calcule pol + pol^2 + ... + pol^(q/2) modulo prhall et le polynome pmod */
static GEN
nfmod_split2(GEN nf,GEN prhall,GEN pmod,GEN pol,GEN exp)
{
  long av = avma;
  GEN p1,p2,q;

  if (cmpis(exp,2)<=0) return pol;
  p2=p1=pol; q=shifti(exp,-1);
  while (!gcmp1(q))
  {
    p2=nfmod_pol_sqr(nf,prhall,p2);
    nfmod_pol_divres(nf,prhall,p2,pmod,&p2);
    q=shifti(q,-1); p1=gadd(p1,p2);
  }
  return gerepileupto(av,p1);
}

/* If p doesn't divide either a or b and has a divisor of degree 1, return it.
 * Return NULL otherwise.
 */
static GEN
p_ok(GEN nf, GEN p, GEN a)
{
  long av,m,i;
  GEN dec;

  if (divise(a,p)) return NULL;
  av = avma; dec = primedec(nf,p); m=lg(dec);
  for (i=1; i<m; i++)
  {
    GEN pr = (GEN)dec[i];
    if (is_pm1(pr[4]))
    {
      if (DEBUGLEVEL>=4)
        fprintferr("Premier choisi pour decomposition: %Z\n", pr);
      return pr;
    }
  }	
  avma = av; return NULL;
}

static GEN
choose_prime(GEN nf, GEN dk, GEN lim)
{
  GEN p, pr;

  p = nextprime(lim);
  for (;;)
  {
    if ((pr = p_ok(nf,p,dk))) break;
    p = nextprime(addis(p,2));
  }

  return pr;
}

/* Renvoie les racines de pol contenues dans nf */
GEN
nfroots(GEN nf,GEN pol)
{
  long av=avma,tetpil,i,d=lgef(pol);
  GEN p1,p2,polbase,polmod,den;

  nf=checknf(nf);
  if (typ(pol)!=t_POL) err(talker,"not a polynomial in nfroots");
  if (varn(pol) >= varn(nf[1]))
    err(talker,"polynomial variable must have highest priority in nfroots");

  polbase=unifpol(nf,pol,0);

  if (d==3)
  {
    tetpil=avma; p1=cgetg(1,t_VEC);
    return gerepile(av,tetpil,p1);
  }

  if (d==4)
  {
    tetpil=avma; p1=cgetg(2,t_VEC);
    p1[1] = (long)basistoalg(nf,gneg_i(
      element_div(nf,(GEN)polbase[2],(GEN)polbase[3])));
    return gerepile(av,tetpil,p1);
  }

  p1=element_inv(nf,leading_term(polbase));
  polbase=nf_pol_mul(nf,p1,polbase);

  den=gun;
  for (i=2; i<d; i++)
    if (! gcmp0((GEN)polbase[i]))
      den = glcm(den,denom((GEN)polbase[i]));
  if (! gcmp1(absi(den)))
    for (i=2; i<d; i++)
      polbase[i] = lmul(den,(GEN)polbase[i]);

  polmod=unifpol(nf,polbase,1);

  if (DEBUGLEVEL>=4)
    fprintferr("On teste si le polynome est square-free\n");

  p1=derivpol(polmod);
  p2=nf_pol_subres(nf,polmod,p1);

  if (degree(p2) > 0)
  {
    p1=element_inv(nf,leading_term(p2));
    p2=nf_pol_mul(nf,p1,p2);
    polmod=nf_pol_divres(nf,polmod,p2,NULL);

    p1=element_inv(nf,leading_term(polmod));
    polmod=nf_pol_mul(nf,p1,polmod);

    d=lgef(polmod); den=gun;
    for (i=2; i<d; i++)
      if (!gcmp0((GEN)polmod[i]))
	den = glcm(den,denom((GEN)polmod[i]));
    if (!gcmp1(absi(den)))
      for (i=2; i<d; i++)
	polmod[i] = lmul(den,(GEN)polmod[i]);

    polmod=unifpol(nf,polmod,1);
  }

  p1 = nfsqff(nf,polmod,1);
  tetpil=avma; return gerepile(av, tetpil, gen_sort(p1, 0, cmp_pol));
}

/* Relevement de elt modulo id minimal */
static GEN
nf_bestlift(GEN id,GEN idinv,GEN den,GEN elt)
{
  return gsub(elt,gmul(id,ground(gmul(den,gmul(idinv,elt)))));
}

/* Releve le polynome pol avec des coeff de norme t2 <= C si possible */
static GEN
nf_pol_lift(GEN id,GEN idinv,GEN den,GEN pol)
{
  long i, d = lgef(pol);
  GEN p1 = pol;

  pol=cgetg(d,t_POL); pol[1]=p1[1];
  for (i=2; i<d; i++)
    pol[i] = (long) nf_bestlift(id,idinv,den,(GEN)p1[i]);
  return pol;
}

#if 0
/* Evalue le polynome pol en elt */
static GEN
nf_pol_eval(GEN nf,GEN pol,GEN elt)
{
  long av=avma,tetpil,i;
  GEN p1;

  i=lgef(pol)-1; if (i==2) return gcopy((GEN)pol[2]);

  p1=element_mul(nf,(GEN)pol[i],elt);
  for (i--; i>=3; i--)
    p1=element_mul(nf,elt,gadd((GEN)pol[i],p1));
  tetpil=avma; return gerepile(av,tetpil,gadd(p1,(GEN)pol[2]));
}
#endif

/* Calcule la factorisation du polynome x dans nf */
GEN
nffactor(GEN nf,GEN pol)
{ GEN y,p1,p2,den,p3,p4,quot, rep = cgetg(3,t_MAT);
  long av = avma,tetpil,i,d;

  if (DEBUGLEVEL >= 4) timer2();

  nf=checknf(nf);
  if (typ(pol)!=t_POL) err(typeer,"nffactor");
  if (varn(pol) >= varn(nf[1]))
    err(talker,"polynomial variable must have highest priority in nffactor");

  d=lgef(pol);
  if (d==3)
  {
    rep[1]=lgetg(1,t_COL);
    rep[2]=lgetg(1,t_COL);
    return rep;
  }
  if (d==4)
  {
    p1=cgetg(2,t_COL); rep[1]=(long)p1; p1[1]=lcopy(pol);
    p1=cgetg(2,t_COL); rep[2]=(long)p1; p1[1]=un;
    return rep;
  }

  p1=element_inv(nf,leading_term(pol));
  pol=nf_pol_mul(nf,p1,pol);

  p1=unifpol(nf,pol,0); den=gun;
  for (i=2; i<d; i++)
    if (! gcmp0((GEN)p1[i]))
      den = glcm(den,denom((GEN)p1[i]));
  if (! gcmp1(absi(den)))
    for (i=2; i<d; i++)
      p1[i] = lmul(den,(GEN)p1[i]);

  if (DEBUGLEVEL>=4)
    fprintferr("On teste si le polynome est square-free\n");

  p2=derivpol(p1);
  p3=nf_pol_subres(nf,p1,p2);

  if (degree(p3) > 0)
  {
    p4=element_inv(nf,leading_term(p3));
    p3=nf_pol_mul(nf,p4,p3);

    p2=nf_pol_divres(nf,p1,p3,NULL);
    p4=element_inv(nf,leading_term(p2));
    p2=nf_pol_mul(nf,p4,p2);

    d=lgef(p2); den=gun;
    for (i=2; i<d; i++)
      if (!gcmp0((GEN)p2[i]))
	den = glcm(den,denom((GEN)p2[i]));
    if (!gcmp1(absi(den)))
      for (i=2; i<d; i++)
	p2[i] = lmul(den,(GEN)p2[i]);

    p2=unifpol(nf,p2,1); 
    tetpil = avma; y = nfsqff(nf,p2,0);
    i = nfcmbf.nfact;

    quot=nf_pol_divres(nf,p1,p2,NULL);
    p3=(GEN)gpmalloc((i+1) * sizeof(long));
    for ( ; i>=1; i--)
    {
      GEN fact=(GEN)y[i], quo = quot, rem;
      long e = 0;

      do
      {
	quo = nf_pol_divres(nf,quo,fact,&rem);
	e++;
      }
      while (gcmp0(rem));
      p3[i]=lstoi(e);
    }
    avma = (long)y; y = gerepile(av, tetpil, y);
    p2=cgetg(i+1, t_COL); for (; i>=1; i--) p2[i]=lstoi(p3[i]);
    free(p3);
  }
  else
  {
    tetpil=avma; y = gerepile(av,tetpil,nfsqff(nf,p1,0));
    i = nfcmbf.nfact;
    p2=cgetg(i+1, t_COL); for (; i>=1; i--) p2[i]=un;
  }
  if (DEBUGLEVEL>=4)
    fprintferr("Nombre de facteur(s) trouve(s) : %ld\n", nfcmbf.nfact);
  rep[1]=(long)y;
  rep[2]=(long)p2; return sort_factor(rep, cmp_pol);
}

/* teste si la matrice M est suffisament orthogonale */
static long
test_mat(GEN M, GEN p, GEN C2, long k)
{
  long av = avma, i, N = lg(M);
  GEN min, prod, L2, R;

  min = prod = gcoeff(M,1,1);
  for (i = 2; i < N; i++)
  {
    L2 = gcoeff(M,i,i); prod = mpmul(prod,L2);
    if (mpcmp(L2,min) < 0) min = L2;
  }
  R = mpmul(min, gpowgs(p, k<<1));
  i = mpcmp(mpmul(C2,prod), R); avma = av;
  return (i < 0);
}

/* calcule la matrice correspondant a pr^e jusqu'a ce que R(pr^e) > C */
static GEN
T2_matrix_pow(GEN nf, GEN pre, GEN p, GEN C, long *kmax, long prec)
{
  long av=avma,av1,lim, k = *kmax, N = lgef((GEN)nf[1])-3;
  int tot_real = !signe(gmael(nf,2,2));
  GEN p1,p2,p3,u,C2,T2, x = (GEN)nf[1];

  C2 = gdiv(gmul2n(C,2), absi((GEN)nf[3]));
  p1 = gmul(pre,lllintpartial(pre)); av1 = avma;
  T2 = tot_real? gmael(nf,5,4)
               : nf_get_T2((GEN) nf[7], roots(x,prec));
  p3 = qf_base_change(T2,p1,1);

  if (N <= 6 && test_mat(p3,p,C2,k))
  {
    avma = av1; return gerepileupto(av,p1);
  }

  av1=avma; lim = stack_lim(av1,2);
  for (;;)
  {
    if (DEBUGLEVEL>2) fprintferr("exponent: %ld\n",k);

    for(;;)
    {
      u = tot_real? lllgramint(p3): lllgramintern(p3,100,1,prec);
      if (u) break;

      prec=(prec<<1)-2;
      if (DEBUGLEVEL > 1) err(warnprec,"nffactor[1]",prec);
      T2 = nf_get_T2((GEN) nf[7], roots(x,prec));
      p3 = qf_base_change(T2,p1,1);
    }
    if (DEBUGLEVEL>2) msgtimer("lllgram + base change");
    p3 = qf_base_change(p3,u,1);
    if (test_mat(p3,p,C2,k))
    {
      *kmax = k;
      return gerepileupto(av,gmul(p1,u));
    }

    /* il faut augmenter la precision en meme temps */
    p2=shifti(gceil(mulsr(k, glog(p,DEFAULTPREC))),-1);
    prec += (long)(itos(p2)*pariK1);
    if (DEBUGLEVEL > 1) err(warnprec,"nffactor[2]",prec);
    k = k<<1; p1 = idealmullll(nf,p1,p1);
    if (low_stack(lim, stack_lim(av1,2)))
    {
      if (DEBUGMEM>1) err(warnmem,"T2_matrix_pow");
      p1 = gerepileupto(av1,p1);
    }
    if (!tot_real) T2 = nf_get_T2((GEN) nf[7], roots(x,prec));
    p3 = qf_base_change(T2,p1,1);
  }
}

/* Calcule la factorisation du polynome x qui est sans facteurs carres dans nf,
   Le polynome est a coefficients dans Z_k et son terme dominant est un entier
   rationnel, si fl=1 renvoie seulement les racines du polynome contenues
   dans le corps */
static GEN
nfsqff(GEN nf,GEN pol, long fl)
{
  long d=lgef(pol),i,k,m,n,av=avma,tetpil,newprec,prec;
  GEN p1,pr,p2,rep,k2,C,h,dk,dki,p,prh,p3,T2,polbase,fact,pk;
  GEN polmod,polred,hinv,lt,minp,den,maxp=shifti(gun,32),run;

  dk=absi((GEN)nf[3]);
  dki=mulii(dk,(GEN)nf[4]);
  n=lgef(nf[1])-3;

  polbase = unifpol(nf,pol,0);
  polmod  = unifpol(nf,pol,1);
  dki=mulii(dki,gnorm((GEN)polmod[d-1]));

  prec = DEFAULTPREC;
  for (;;)
  {
    if (prec <= gprecision(nf))
      T2 = gprec_w(gmael(nf,5,3), prec);
    else
      T2 = nf_get_T2((GEN)nf[7], roots((GEN)nf[1], prec));

    run=realun(prec);
    p1=realzero(prec);
    for (i=2; i<d; i++)
    { 
      p2 = gmul(run, (GEN)polbase[i]);
      p1 = addrr(p1, qfeval(T2, p2));
      if (signe(p1) < 0) break;
    }

    if (signe(p1) > 0) break;

    prec = (prec<<1)-2;
    if (DEBUGLEVEL > 1) err(warnprec, "nfsqff", prec);
  }

  if (DEBUGLEVEL>=4)
    fprintferr("La norme de ce polynome est : %Z\n", p1);

  lt=(GEN)leading_term(polbase)[1];
  p2=mulis(sqri(lt),n);
  C=mpadd(p1,p2);
  C=mpadd(C,gsqrt(gmul(p1,p2),prec));
	    
  if (!fl)
    C=mpmul(C,sqri(binome(shifti(stoi(n-1),-1),(n-1)>>2)));
    
  C=gmul(C,sqri(lt));
  
  if (DEBUGLEVEL>=4)
    fprintferr("La borne de la norme des coeff du diviseur est : %Z\n", C);
  
  k2=gmul2n(gmulgs(glog(gdivgs(gmul2n(C,2),n),DEFAULTPREC),n),-1);
  if (!fl) k2=mulrr(k2,dbltor(1.1));
 
  minp=gmin(gexp(gmul2n(k2,-6),BIGDEFAULTPREC), maxp);
  minp=gceil(minp);
  
  if (DEBUGLEVEL>=4)
  {
    fprintferr("borne inf. sur les nombres premiers : %Z\n", minp);
    msgtimer("Calcul des bornes");
  }
  for (;;)
  {
    pr=choose_prime(nf,dki,minp); p=(GEN)pr[1];
    prh=prime_to_ideal(nf,pr);

    polred=gcopy(polbase);
    lt=(GEN)leading_term(polbase)[1];
    lt=mpinvmod(lt,p);

    for (i=2; i<d; i++)
      polred[i] = nfreducemodpr_i(gmul(lt,(GEN)polbase[i]), prh)[1];
    if (!divise(discsr(polred),p)) break;
    minp = addis(p,1);
  }

  k = itos(gceil(gdiv(k2,glog(p,BIGDEFAULTPREC))));	
  rep=(GEN)simplefactmod(polred,p)[1];

  if (DEBUGLEVEL>=4)
  {
    msgtimer("Choix de l'ideal premier");
    fprintferr("Nombre de facteurs irreductibles modulo pr = %ld\n", lg(rep)-1);
  }
  if (lg(rep)==2)
  {
    if (fl) { avma=av; return cgetg(1,t_VEC); }
    rep=cgetg(2,t_VEC); rep[1]=lcopy(polmod);
    nfcmbf.nfact=1; return gerepileupto(av, rep);
  }

  p2=cgetr(DEFAULTPREC);
  affir(mulii(absi(dk),gpowgs(p,k)),p2);
  p2=shifti(gceil(mplog(p2)),-1);

  newprec = MEDDEFAULTPREC + (long)(itos(p2)*pariK1);
  if (DEBUGLEVEL>=4)
    fprintferr("nouvelle precision : %ld\n",newprec);

  prh = idealpows(nf,pr,k); m = k;
  h = T2_matrix_pow(nf,prh,p,C, &k, newprec);
  if (m != k) prh=idealpows(nf,pr,k); 

  if (DEBUGLEVEL>=4)
  {
    fprintferr("un exposant convenable est : %ld\n",(long)k);
    msgtimer("Calcul de H");
  }

  pk = gcoeff(prh,1,1);
  lt=(GEN)leading_term(polbase)[1];
  lt=mpinvmod(lt,pk);

  polred[1] = polbase[1];
  for (i=2; i<d; i++)
    polred[i] = nfreducemodpr_i(gmul(lt,(GEN)polbase[i]), prh)[1];

  fact = lift_intern((GEN)factmod(polred,p)[1]);
  rep = hensel_lift_fact(polred,fact,p,pk,k);

  if (DEBUGLEVEL >= 4) msgtimer("Calcul de la factorisation pr-adique");

  den=ginv(det(h));
  hinv=adj(h);
  lt=(GEN)leading_term(polbase)[1];

  if (fl)
  {
    long x_a[] = { evaltyp(t_POL)|m_evallg(4), 0,0,0 };
    GEN mlt = negi(lt), rem;
    x_a[1] = polbase[1]; setlgef(x_a, 4);
    x_a[3] = un;
    p1=cgetg(lg(rep)+1,t_VEC);
    polbase = unifpol(nf,polbase,1);
    for (m=1,i=1; i<lg(rep); i++)
    {
      p2=(GEN)rep[i]; if (lgef(p2)!=4) break;

      p3 = algtobasis(nf, gmul(mlt,(GEN)p2[2]));
      p3 = nf_bestlift(h,hinv,den,p3);
      p3 = gdiv(p3,lt);
      x_a[2] = lneg(p3); /* check P(p3) == 0 */
      p2 = poldivres(polbase, unifpol(nf,x_a,1), &rem);
      if (!signe(rem)) { polbase = p2; p1[m++] = (long)p3; }
    }
    tetpil=avma; rep=cgetg(m,t_VEC);
    for (i=1; i<m; i++) rep[i]=(long)basistoalg(nf,(GEN)p1[i]);
    return gerepile(av,tetpil,rep);
  }

  for (i=1; i<lg(rep); i++)
    rep[i] = (long)unifpol(nf,(GEN)rep[i],0);

  nfcmbf.pol      = polmod;
  nfcmbf.lt       = lt;
  nfcmbf.h        = h;
  nfcmbf.hinv     = hinv;
  nfcmbf.den      = den;
  nfcmbf.fact     = rep;
  nfcmbf.res      = cgetg(lg(rep)+1,t_VEC);
  nfcmbf.nfact    = 0;
  nfcmbf.nfactmod = lg(rep)-1;
  nf_combine_factors(nf,1,NULL,d-3,1);

  if (DEBUGLEVEL >= 4) msgtimer("Reconnaissance des facteurs");

  i = nfcmbf.nfact;
  if (lgef(nfcmbf.pol)>3)
  {
    nfcmbf.res[++i] = (long) nf_pol_divres(nf,nfcmbf.pol,nfcmbf.lt,NULL);
    nfcmbf.nfact = i;
  }

  tetpil=avma; rep=cgetg(i+1,t_VEC);
  for (  ; i>=1; i--)
    rep[i]=(long)unifpol(nf,(GEN)nfcmbf.res[i],1);
  return gerepile(av,tetpil,rep);
}

static int
nf_combine_factors(GEN nf,long fxn,GEN psf,long dlim,long hint)
{
  int val=0; /* assume failure */
  GEN newf, newpsf = NULL;
  long newd,ltop,i;

  if (dlim<=0) return 0;
  if (fxn > nfcmbf.nfactmod) return 0;
  /* first, try deeper factors without considering the current one */
  if (fxn != nfcmbf.nfactmod)
  {
    val=nf_combine_factors(nf,fxn+1,psf,dlim,hint);
    if (val && psf) return 1;
  }

  /* second, try including the current modular factor in the product */
  newf=(GEN)nfcmbf.fact[fxn];
  if (!newf) return val; /* modular factor already used */
  newd=lgef(newf)-3;
  if (newd>dlim) return val; /* degree of new factor is too large */

  if (newd%hint == 0)
  {
    GEN p, quot,rem;

    newpsf = nf_pol_mul(nf, (psf)? psf: nfcmbf.lt, newf);
    newpsf = nf_pol_lift(nfcmbf.h,nfcmbf.hinv,nfcmbf.den,newpsf);
    /* try out the new combination */
    ltop=avma;
    quot=nf_pol_divres(nf,nfcmbf.pol,newpsf,&rem);
    if (gcmp0(rem))  /* found a factor */
    {
      p = nf_pol_mul(nf,element_inv(nf,leading_term(newpsf)),newpsf);
      nfcmbf.res[++nfcmbf.nfact] = (long) p; /* store factor */
      nfcmbf.fact[fxn]=0;                    /* remove used modular factor */

      /* fix up target */
      p=gun; quot=unifpol(nf,quot,0);
      for (i=2; i<lgef(quot); i++)
	if (!gcmp0((GEN)quot[i]))
	  p = glcm(p, denom((GEN)quot[i]));

      nfcmbf.pol = nf_pol_mul(nf,p,quot);
      nfcmbf.lt  = leading_term(nfcmbf.pol);
      return 1;
    }
    avma=ltop;
  }

  /* newpsf needs more; try for it */
  if (newd==dlim) return val; /* no more room in degree limit */
  if (fxn==nfcmbf.nfactmod) return val; /* no more modular factors to try */

  if (nf_combine_factors(nf,fxn+1,newpsf,dlim-newd,hint))
  {
    nfcmbf.fact[fxn]=0; /* remove used modular factor */
    return 1;
  }
  return val;
}

/* Calcule le polynome caracteristique de alpha sur nf ou alpha est un
   element de l'algebre nf[X]/(T) exprime comme polynome en x */
GEN
rnfcharpoly(GEN nf,GEN T,GEN alpha,int v)
{
  long av=avma,tetpil;
  GEN p1;

  nf=checknf(nf); if (v<0) v = 0;
  if (typ(alpha) == t_POLMOD) alpha = lift_to_pol(alpha);
  p1 = caract2(unifpol(nf,T,1), unifpol(nf,alpha,1), v);
  tetpil=avma; return gerepile(av,tetpil,unifpol(nf,p1,1));
}

#if 0
/* Calcule le polynome minimal de alpha sur nf ou alpha est un
   element de l'algebre nf[X]/(T) exprime comme polynome en x */
GEN
rnfminpoly(GEN nf,GEN T,GEN alpha,int n)
{
  long av=avma,tetpil;
  GEN p1,p2;

  nf=checknf(nf); p1=rnfcharpoly(nf,T,alpha,n);
  tetpil=avma; p2=nf_pol_subres(nf,p1,deriv(p1,varn(T)));
  if (lgef(p2)==3) { avma=tetpil; return p1; }

  p1 = nf_pol_divres(nf,p1,p2,NULL);
  p2 = element_inv(nf,leading_term(p1));
  tetpil=avma; return gerepile(av,tetpil,unifpol(nf,nf_pol_mul(nf,p2,p1),1));
}
#endif

/* relative Dedekind criterion over nf, applied to the order defined by a
 * root of irreducible polynomial T, modulo the prime ideal pr. Returns
 * [flag,basis,val], where basis is a pseudo-basis of the enlarged order,
 * flag is 1 iff this order is pr-maximal, and val is the valuation in pr of
 * the order discriminant
 */
GEN
rnfdedekind(GEN nf,GEN T,GEN pr)
{
  long av=avma,vt,r,d,da,n,m,i,j;
  GEN p1,p2,p,tau,g,vecun,veczero,matid;
  GEN prhall,res,h,k,base,Ca;

  nf=checknf(nf); Ca=unifpol(nf,T,0);
  res=cgetg(4,t_VEC);
  if (typ(pr)==t_VEC && lg(pr)==3)
  { prhall = (GEN)pr[2]; pr = (GEN)pr[1]; }
  else
    prhall=nfmodprinit(nf,pr);
  p=(GEN)pr[1]; tau=gdiv((GEN)pr[5],p);
  n=lgef(nf[1])-3; m=lgef(T)-3;

  vecun=cgetg(n+1,t_COL); vecun[1]=un;
  veczero=cgetg(n+1,t_COL); veczero[1]=zero;
  for (i=2; i<=n; i++) vecun[i] = veczero[i] = zero;

  p1=(GEN)nffactormod(nf,Ca,pr)[1];
  g=lift((GEN)p1[1]); r=lg(p1);
  for (i=2; i<r; i++)
    g = nf_pol_mul(nf,g, lift((GEN)p1[i]));
  h=nfmod_pol_divres(nf,prhall,Ca,g,NULL);
  k=nf_pol_mul(nf,tau,gsub(Ca, nf_pol_mul(nf,lift(g),lift(h))));
  p2=nfmod_pol_gcd(nf,prhall,g,h);
  k= nfmod_pol_gcd(nf,prhall,p2,k);

  d=lgef(k)-3;  /* <= m */
  vt = idealval(nf,discsr(T),pr) - 2*d;
  res[3]=lstoi(vt);
  if (!d || vt<=1) res[1]=un; else res[1]=zero;

  base=cgetg(3,t_VEC);
  p1=cgetg(m+d+1,t_MAT); base[1]=(long)p1;
  p2=cgetg(m+d+1,t_VEC); base[2]=(long)p2;
 /* if d > 0, base[2] temporarily multiplied by p, for the final nfhermitemod
  * [ which requires integral ideals ] */
  matid = gscalmat(d? p: gun, n);
  for (j=1; j<=m; j++)
  {
    p2[j]=(long)matid;
    p1[j]=lgetg(m+1,t_COL);
    for (i=1; i<=m; i++)
      coeff(p1,i,j) = (i==j)?(long)vecun:(long)veczero;
  }
  if (d)
  {
    GEN pal = lift(nfmod_pol_divres(nf,prhall,Ca,k,NULL));
    GEN prinvp = pidealprimeinv(nf,pr); /* again multiplied by p */
    GEN nfx = unifpol(nf,polx[varn(T)],0);

    for (   ; j<=m+d; j++)
    {
      p1[j]=lgetg(m+1,t_COL);
      da=lgef(pal)-3;
      for (i=1; i<=da+1; i++) coeff(p1,i,j)=pal[i+1];
      for (   ; i<=m; i++) coeff(p1,i,j)=(long)veczero;
      p2[j]=(long)prinvp;
      nf_pol_divres(nf,nf_pol_mul(nf,pal,nfx),T,&pal);
    }
    /* the modulus is integral */
    base = nfhermitemod(nf,base, gmul(gpowgs(p, m-d), 
				      idealpows(nf, prinvp, d))); 
    base[2] = ldiv((GEN)base[2], p); /* cancel the factor p */
  }
  res[2]=(long)base; return gerepileupto(av, gcopy(res));
}
