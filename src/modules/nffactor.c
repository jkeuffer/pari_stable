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
/*            POLYNOMIAL FACTORIZATION IN A NUMBER FIELD           */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "parinf.h"

extern GEN nfgcd(GEN P, GEN Q, GEN nf, GEN den);
extern GEN hensel_lift_fact(GEN pol, GEN fact, GEN T, GEN p, GEN pev, long e);
extern GEN nf_get_T2(GEN base, GEN polr);
extern GEN nfreducemodpr_i(GEN x, GEN prh);
extern GEN sort_factor(GEN y, int (*cmp)(GEN,GEN));
extern GEN pidealprimeinv(GEN nf, GEN x);

static GEN nffactormod2(GEN nf,GEN pol,GEN pr);
static GEN nfmod_split2(GEN nf, GEN prhall, GEN polb, GEN v, GEN q);
static GEN nf_pol_mul(GEN nf,GEN pol1,GEN pol2);
static GEN nf_pol_divres(GEN nf,GEN pol1,GEN pol2, GEN *pr);
static GEN nfmod_pol_reduce(GEN nf,GEN prhall,GEN pol);
static GEN nfmod_pol_divres(GEN nf,GEN prhall,GEN pol1,GEN pol2, GEN *pr);
static GEN nfmod_pol_gcd(GEN nf,GEN prhall,GEN pol1,GEN pol2);
static GEN nf_bestlift(GEN id,GEN idinv,GEN den,GEN elt);
static GEN nf_pol_lift(GEN id,GEN idinv,GEN den,GEN pol);
static GEN nfsqff(GEN nf,GEN pol,long fl);

typedef struct /* for use in nfsqff */
{
  GEN nf, pol, h, hinv, fact, res, lt, den;
  long nfact, nfactmod, hint;
} nfcmbf_t;

static GEN
unifpol0(GEN nf,GEN pol,long flag)
{
  static long n = 0;
  static GEN vun = NULL;
  GEN f = (GEN) nf[1];
  long i = degpol(f);
  gpmem_t av;

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

/* Let pol be a polynomial with coefficients in Z or nf (vectors or polymods)
 * return the same polynomial with coefficients expressed:
 *  if flag=0: as vectors (on the integral basis).
 *  if flag=1: as polymods.
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

#if 0
/* return a monic polynomial of degree d with random coefficients in Z_nf */
static GEN
random_pol(GEN nf,long d)
{
  long i,j, n = degpol(nf[1]);
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
#endif

/* multiplication of x by y */
static GEN
nf_pol_mul(GEN nf,GEN x,GEN y)
{
  gpmem_t tetpil, av=avma;
  GEN res = gmul(unifpol(nf,x,1), unifpol(nf,y,1));

  tetpil = avma;
  return gerepile(av,tetpil,unifpol(nf,res,0));
}

/* compute x^2 in nf */
static GEN
nf_pol_sqr(GEN nf,GEN x)
{
  gpmem_t tetpil, av=avma;
  GEN res = gsqr(unifpol(nf,x,1));

  tetpil = avma;
  return gerepile(av,tetpil,unifpol(nf,res,0));
}

/* reduce the coefficients of pol modulo prhall */
static GEN
nfmod_pol_reduce(GEN nf,GEN prhall,GEN pol)
{
  long i;
  gpmem_t av=avma, tetpil;
  GEN p1;

  if (typ(pol)!=t_POL) return nfreducemodpr(nf,pol,prhall);
  pol=unifpol(nf,pol,0);

  tetpil=avma; i=lgef(pol);
  p1=cgetg(i,t_POL); p1[1]=pol[1];
  for (i--; i>=2; i--)
    p1[i] = (long) nfreducemodpr(nf,(GEN)pol[i],prhall);
  return gerepile(av,tetpil, normalizepol(p1));
}

/* x^2 modulo prhall */
static GEN
nfmod_pol_sqr(GEN nf,GEN prhall,GEN x)
{
  gpmem_t av=avma, tetpil;
  GEN px;

  px = nfmod_pol_reduce(nf,prhall,x);
  px = unifpol(nf,lift(px),1);
  px = unifpol(nf,nf_pol_sqr(nf,px),0);
  tetpil=avma;
  return gerepile(av,tetpil,nfmod_pol_reduce(nf,prhall,px));
}

/* multiplication of x by y modulo prhall */
static GEN
nfmod_pol_mul(GEN nf,GEN prhall,GEN x,GEN y)
{
  gpmem_t av=avma, tetpil;
  GEN px,py;

  px = nfmod_pol_reduce(nf,prhall,x); px = unifpol(nf,lift(px),1);
  py = nfmod_pol_reduce(nf,prhall,y); py = unifpol(nf,lift(py),1);
  px = unifpol(nf,nf_pol_mul(nf,px,py),0);
  tetpil=avma;
  return gerepile(av,tetpil,nfmod_pol_reduce(nf,prhall,px));
}

/* Euclidan division of x by y */
static GEN
nf_pol_divres(GEN nf,GEN x,GEN y,GEN *pr)
{
  gpmem_t av = avma, tetpil;
  GEN nq = poldivres(unifpol(nf,x,1),unifpol(nf,y,1),pr);
  GEN *gptr[2];

  tetpil=avma; nq=unifpol(nf,nq,0);
  if (pr) *pr = unifpol(nf,*pr,0);
  gptr[0]=&nq; gptr[1]=pr;
  gerepilemanysp(av,tetpil,gptr,pr ? 2:1);
  return nq;
}

/* Euclidan division of x by y modulo prhall */
static GEN
nfmod_pol_divres(GEN nf,GEN prhall,GEN x,GEN y, GEN *pr)
{
  long dx, dy, dz, i, j, k, n;
  gpmem_t av=avma, av1, tetpil;
  GEN z,p1,p3,px,py;

  py = nfmod_pol_reduce(nf,prhall,y);
  if (gcmp0(py))
    err(talker, "division by zero in nfmod_pol_divres");

  tetpil=avma;
  px=nfmod_pol_reduce(nf,prhall,x);
  dx=degpol(px); dy=degpol(py); dz=dx-dy;
  if (dx<dy)
  {
    GEN vzero;

    if (pr) *pr = gerepile(av,tetpil,px);
    else avma = av;

    n=degpol(nf[1]);
    vzero = cgetg(n+1,t_COL);
    n=degpol(nf[1]);
    for (i=1; i<=n; i++) vzero[i]=zero;

    z=cgetg(3,t_POL); z[2]=(long)vzero;
    z[1]=evallgef(2) | evalvarn(varn(px));
    return z;
  }
  p1 = NULL; /* gcc -Wall */

  z=cgetg(dz+3,t_POL); z[1]=evalsigne(1) | evallgef(3+dz);
  setvarn(z,varn(px));
  z[dz+2] = (long) element_divmodpr(nf,(GEN)px[dx+2],(GEN)py[dy+2],prhall);
  for (i=dx-1; i>=dy; --i)
  {
    av1=avma; p1=(GEN)px[i+2];
    for (j=i-dy+1; j<=i && j<=dz; j++)
      p1 = gsub(p1, element_mul(nf,(GEN)z[j+2],(GEN)py[i-j+2]));
    p1 = nfreducemodpr(nf,p1,prhall);
    tetpil=avma; p3=element_divmodpr(nf,p1,(GEN)py[dy+2],prhall);
    z[i-dy+2]=lpile(av1,tetpil,p3);
    z[i-dy+2]=(long)nfreducemodpr(nf,(GEN)z[i-dy+2],prhall);
  }
  av1=avma;
  for (i=dy-1; i>=0; --i)
  {
    av1=avma; p1=((GEN)px[i+2]);
    for (j=0; j<=i && j<=dz; j++)
      p1 = gsub(p1, element_mul(nf,(GEN)z[j+2],(GEN)py[i-j+2]));
    p1 = gerepileupto(av1, nfreducemodpr(nf,p1,prhall));
    if (!gcmp0(p1)) break;
  }

  if (!pr) { avma = av1; return z; }

  if (i<0)
  {
    avma=av1;
    p3 = cgetg(3,t_POL); p3[2]=zero;
    p3[1] = evallgef(2) | evalvarn(varn(px));
    *pr=p3; return z;
  }

  p3=cgetg(i+3,t_POL);
  p3[1]=evalsigne(1) | evallgef(i+3) | evalvarn(varn(px));
  p3[i+2]=(long)nfreducemodpr(nf,p1,prhall);
  for (k=i-1; k>=0; --k)
  {
    av1=avma; p1=((GEN)px[k+2]);
    for (j=0; j<=k && j<=dz; j++)
      p1 = gsub(p1, element_mul(nf,(GEN)z[j+2],(GEN)py[k-j+2]));
    p3[k+2]=lpileupto(av1,nfreducemodpr(nf,p1,prhall));
  }
  *pr=p3; return z;
}

/* GCD of x and y modulo prhall */
static GEN
nfmod_pol_gcd(GEN nf,GEN prhall,GEN x,GEN y)
{
  gpmem_t av=avma;
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

/* return pol^e modulo prhall and the polynomial pmod */
static GEN
nfmod_pol_pow(GEN nf,GEN prhall,GEN pmod,GEN pol,GEN e)
{
  long i, n = degpol(nf[1]);
  gpmem_t av = avma;
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

/* return the factor of nf.pol modulo p corresponding to pr */
static GEN
localpol(GEN nf, GEN pr)
{
  GEN g, pol = (GEN)nf[1], p = (GEN)pr[1];
  if (degpol(pol) == itos((GEN)pr[4])) return pol; /* pr inert */

  g = gmul((GEN)nf[7], (GEN)pr[2]); /* uniformizer */
  g = primpart(g); return FpX_gcd(g,pol,p);
}

/* factorization of x modulo pr */
static GEN
nffactormod0(GEN nf, GEN x, GEN pr)
{
  long j, l, vx = varn(x), vn;
  gpmem_t av = avma;
  GEN rep, xrd, prh, p1;

  nf=checknf(nf);
  vn = varn((GEN)nf[1]);
  if (typ(x)!=t_POL) err(typeer,"nffactormod");
  if (vx >= vn)
    err(talker,"polynomial variable must have highest priority in nffactormod");

  prh = nfmodprinit(nf, pr);

  if (divise((GEN)nf[4], (GEN)pr[1]))
    return gerepileupto(av, nffactormod2(nf,x,pr));

  xrd = nfmod_pol_reduce(nf, prh, x);
  if (gcmp1((GEN)pr[4]))
  {
    for (j = 2; j < lg(xrd); j++)
      xrd[j] = mael(xrd, j, 1);
    rep = factmod(xrd, (GEN)pr[1]);
    rep = lift(rep);
  }
  else
  {
    GEN pol = localpol(nf, pr);
    xrd = lift(unifpol(nf, xrd, 1));
    p1  = gun;
    for (j = 2; j < lg(xrd); j++)
    {
      xrd[j] = lmod((GEN)xrd[j], pol);
      p1 = mpppcm(p1, denom(content((GEN)xrd[j])));
    }
    rep = factmod9(gmul(xrd, p1), (GEN)pr[1], pol);
    rep = lift(lift(rep));
  }

  l = lg((GEN)rep[1]);
  for (j = 1; j < l; j++)
    mael(rep, 1, j) = (long)unifpol(nf, gmael(rep, 1, j), 1);

  return gerepilecopy(av, rep);
}

GEN
nffactormod(GEN nf, GEN x, GEN pr)
{
  return nffactormod0(nf, x, pr);
}

extern GEN trivfact(void);

/* factorization of x modulo pr */
GEN
nffactormod2(GEN nf,GEN pol,GEN pr)
{
  long lb, nbfact, psim, N, n, i, j, k, d, e, vf, r, kk;
  gpmem_t av = avma, tetpil;
  GEN y,ex,*t,f1,f2,f3,df1,g1,polb,pold,polu,vker;
  GEN Q,f,x,u,v,v2,v3,vz,q,vun,vzero,prhall;

  nf=checknf(nf);
  if (typ(pol)!=t_POL) err(typeer,"nffactormod");
  if (varn(pol) >= varn(nf[1]))
    err(talker,"polynomial variable must have highest priority in nffactormod");

  prhall=nfmodprinit(nf,pr); n=degpol(nf[1]);
  vun = gscalcol_i(gun, n);
  vzero = gscalcol_i(gzero, n);
  q = vker = NULL; /* gcc -Wall */

  f=unifpol(nf,pol,0); f=nfmod_pol_reduce(nf,prhall,f);
  if (!signe(f)) err(zeropoler,"nffactormod");
  d=degpol(f); vf=varn(f);
  if (d == 0) return trivfact();
  t  = (GEN*)new_chunk(d+1); ex = cgetg(d+1, t_VECSMALL);
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
	  N=degpol(u); Q=cgetg(N+1,t_MAT);
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
      e*=psim; j=(degpol(f2))/psim+3; f1=cgetg(j,t_POL);
      f1[1] = evalsigne(1) | evallgef(j) | evalvarn(vf);
      for (i=2; i<j; i++)
	f1[i]=(long)element_powmodpr(nf,(GEN)f2[psim*(i-2)+2],
				     gdiv(q,(GEN)pr[1]),prhall);
    }
  }
  if (nbfact < 2)
    err(talker, "%Z not a prime (nffactormod)", q);
  for (j=1; j<nbfact; j++)
  {
    v = element_divmodpr(nf,vun,gmael(t,j,lgef(t[j])-1),prhall);
    t[j] = unifpol(nf,nfmod_pol_mul(nf,prhall,v,(GEN)t[j]),1);
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

/* return pol + pol^2 + ... + pol^(q/2) modulo prhall and
   the polynomial pmod */
static GEN
nfmod_split2(GEN nf,GEN prhall,GEN pmod,GEN pol,GEN exp)
{
  gpmem_t av = avma;
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

extern GEN apply_kummer(GEN nf,GEN pol,GEN e,GEN p,GEN *beta);

/* If p doesn't divide bad and has a divisor of degree 1, return it. */
static GEN
choose_prime(GEN nf, GEN bad, GEN lim)
{
  GEN p, r, L, x = (GEN)nf[1];
  for (L = lim;; L = addis(p,2))
  {
    p = nextprime(L);
    if (divise(bad,p)) continue;
    r = rootmod(x, p);
    if (lg(r) > 1) break;
  }
  r = gsub(polx[varn(x)], lift_intern((GEN)r[1]));
  return apply_kummer(nf,r,gun,p,NULL);
}

/* rescale p in K[X] (coeffs in algtobasis form) --> primitive in O_K[X] */
GEN
nf_pol_to_int(GEN p, GEN *den)
{
  long i, l = lgef(p);
  GEN d = gun;
  for (i=2; i<l; i++)
    d = mpppcm(d,denom((GEN)p[i]));
  if (! gcmp1(d)) p = gmul(p, d);
  *den = d; return p;
}

static GEN
nf_pol_normalize(GEN nf, GEN P)
{
  GEN t = element_inv(nf, leading_term(P));
  return nf_pol_mul(nf,t,P);
}

/* return the roots of pol in nf */
GEN
nfroots(GEN nf,GEN pol)
{
  gpmem_t av = avma;
  int d = degpol(pol);
  GEN A,g,den;

  nf = checknf(nf);
  if (typ(pol) != t_POL) err(notpoler,"nfroots");
  if (varn(pol) >= varn(nf[1]))
    err(talker,"polynomial variable must have highest priority in nfroots");
  if (d == 0) return cgetg(1,t_VEC);
  if (d == 1)
  {
    A = gneg_i(gdiv((GEN)pol[2],(GEN)pol[3]));
    return gerepilecopy(av, _vec( basistoalg(nf,A) ));
  }
  A = fix_relative_pol(nf,pol,0);
  A = primpart( lift_intern(A) );
  if (DEBUGLEVEL>3) fprintferr("test if polynomial is square-free\n");
  g = nfgcd(A, derivpol(A), (GEN)nf[1], NULL);

  if (degpol(g))
  { /* not squarefree */
    g = nf_pol_normalize(nf, g);
    A = nf_pol_divres(nf,A,g,NULL);
  }
  A = nf_pol_normalize(nf,A);
  A = nf_pol_to_int(A, &den);
  A = nfsqff(nf,A,1);
  return gerepileupto(av, gen_sort(A, 0, cmp_pol));
}

/* return a minimal lift of elt modulo id */
static GEN
nf_bestlift(GEN id,GEN idinv,GEN den,GEN elt)
{
  GEN u = gmul(idinv,elt);
  long i, l = lg(u);
  for (i=1; i<l; i++) u[i] = (long)gdivround((GEN)u[i], den);
  return gsub(elt, gmul(id, u));
}

/* return the lift of pol with coefficients of T2-norm <= C (if possible) */
static GEN
nf_pol_lift(GEN id,GEN idinv,GEN den,GEN pol)
{
  long i, d = lgef(pol);
  GEN x = cgetg(d,t_POL);
  x[1] = pol[1];
  for (i=2; i<d; i++)
    x[i] = (long) nf_bestlift(id,idinv,den,(GEN)pol[i]);
  return x;
}

#if 0
/* return pol(elt) */
static GEN
nf_pol_eval(GEN nf,GEN pol,GEN elt)
{
  long i;
  gpmem_t av=avma, tetpil;
  GEN p1;

  i=lgef(pol)-1; if (i==2) return gcopy((GEN)pol[2]);

  p1=element_mul(nf,(GEN)pol[i],elt);
  for (i--; i>=3; i--)
    p1=element_mul(nf,elt,gadd((GEN)pol[i],p1));
  tetpil=avma; return gerepile(av,tetpil,gadd(p1,(GEN)pol[2]));
}
#endif

extern GEN trivfact(void);

/* return the factorization of x in nf */
GEN
nffactor(GEN nf,GEN pol)
{
  GEN A,g,y,p1,den,rep;
  long l, j, d = degpol(pol);
  gpmem_t av;
  if (DEBUGLEVEL>3) timer2();

  nf = checknf(nf);
  if (typ(pol) != t_POL) err(notpoler,"nffactor");
  if (varn(pol) >= varn(nf[1]))
    err(talker,"polynomial variable must have highest priority in nffactor");

  if (d == 0) return trivfact();
  rep = cgetg(3, t_MAT); av = avma;
  if (d == 1)
  {
    rep[1] = (long)_col( gcopy(pol) );
    rep[2] = (long)_col( gun );
    return rep;
  }

  A = fix_relative_pol(nf,pol,0);
  A = primpart( lift_intern(A) );
  if (DEBUGLEVEL>3) fprintferr("test if polynomial is square-free\n");
  g = nfgcd(A, derivpol(A), (GEN)nf[1], NULL);

  A = nf_pol_normalize(nf, A);
  A = nf_pol_to_int(A, &den);

  if (degpol(g))
  { /* not squarefree */
    gpmem_t av1;
    GEN ex;
    g = nf_pol_normalize(nf, g);
    A = nf_pol_divres(nf,A,g,NULL);

    y = nfsqff(nf,A,0); av1 = avma;
    l = lg(y);
    ex=(GEN)gpmalloc(l * sizeof(long));
    for (j=l-1; j>=1; j--)
    {
      GEN fact=(GEN)y[j], quo = g, rem;
      long e = 0;

      do
      {
	quo = nf_pol_divres(nf,quo,fact,&rem);
	e++;
      }
      while (gcmp0(rem));
      ex[j] = e;
    }
    avma = av1; y = gerepileupto(av, y);
    p1 = cgetg(l, t_COL); for (j=l-1; j>=1; j--) p1[j] = lstoi(ex[j]);
    free(ex);
  }
  else
  {
    y = gerepileupto(av, nfsqff(nf,A,0));
    l = lg(y);
    p1 = cgetg(l, t_COL); for (j=l-1; j>=1; j--) p1[j] = un;
  }
  if (DEBUGLEVEL>3)
    fprintferr("number of factor(s) found: %ld\n", lg(y)-1);
  rep[1] = (long)y;
  rep[2] = (long)p1; return sort_factor(rep, cmp_pol);
}

/* test if the matrix M is suitable */
static long
PRK_good_enough(GEN M, GEN p, long k, GEN C2)
{
  long i, l = lg(M);
  GEN min, prod, L2, p2k = gpowgs(p, k<<1);

  min = prod = gcoeff(M,1,1);
  for (i = 2; i < l; i++)
  {
    L2 = gcoeff(M,i,i); prod = mpmul(prod,L2);
    if (mpcmp(L2,min) < 0) min = L2;
  }
  return (mpcmp(mpmul(C2,prod), mpmul(min, p2k)) < 0);
}

/* We want to be able to reconstruct x, T_2(x) < C, from x mod pr^k
 * k > B / log(N pr) is probably OK.
 * Theoretical guaranteed bound is (n/2) [ log(C/n) + n*(n-1) * log(4)/4 ]
 * We replace log(4)/4 ~ 0.347 by 0.15.  Assume C a t_REAL */
static GEN
bestlift_bound(GEN C, long n)
{
  GEN t = addrr(mplog(divrs(C,n)), dbltor(n*(n-1) * 0.15));
  return gmul2n(mulrs(t,n), -1);
}

static GEN
get_T2(GEN nf, int tot_real, long prec)
{
  if (tot_real) return gmael(nf,5,4);
  if (prec <= nfgetprec(nf)) return gmael(nf,5,3);
  return nf_get_T2((GEN)nf[7], roots((GEN)nf[1],prec));
}

/* return the matrix corresponding to pr^e with R(pr^e) > C */
static GEN
bestlift_init(GEN nf, GEN pr, GEN C, long *kmax, GEN *prkmax)
{
  long k, prec, n = degpol(nf[1]);
  gpmem_t av = avma, av1, av2;
  int tot_real = !signe(gmael(nf,2,2)), early_try = (n <= 6);
  GEN prk,dk,logdk, PRK,p1,u,C2,T2,T2PRK;
  GEN p = (GEN)pr[1], logp = glog(p,DEFAULTPREC);
  GEN *gptr[2];

  dk = absi((GEN)nf[3]); logdk = glog(dk,DEFAULTPREC);
  C2 = gdiv(gmul2n(C,2), dk);

  av1 = avma; u = NULL;
  p1 = bestlift_bound(C, n);
  k = itos(gceil( divrr(p1,logp) ));
  for (;; k<<=1, avma = av1)
  {
    p1 = gmul2n(addrr(logdk , mulsr(k, logp)), -1);
    prec = MEDDEFAULTPREC + (long)(itos(gceil(p1))*pariK1);

    if (DEBUGLEVEL>2) fprintferr("exponent: %ld, precision: %ld\n",k,prec);
    prk = idealpows(nf, pr, k);
    PRK = gmul(prk, lllintpartial(prk)); av2 = avma;
    for(;;)
    {
      T2 = get_T2(nf, tot_real, prec);
      T2PRK = qf_base_change(T2,PRK,1);
      if (early_try && PRK_good_enough(T2PRK, p,k,C2)) break;
      early_try = 0;

      u = tot_real? lllgramall(T2PRK,2,lll_IM) : lllgramintern(T2PRK,2,1,prec);
      if (u) { T2PRK = qf_base_change(T2PRK,u,1); break; }

      prec = (prec<<1)-2;
      if (DEBUGLEVEL>1) err(warnprec,"nffactor[1]",prec);
    }
    if (early_try) break;

    if (DEBUGLEVEL>2) msgtimer("lllgram + base change");
    if (PRK_good_enough(T2PRK, p,k,C2)) { PRK = gmul(PRK, u); break; }
  }
  gptr[0] = &prk; gptr[1] = &PRK; gerepilemany(av, gptr, 2);
  *kmax   = k;
  *prkmax = prk; return PRK;
}

/* assume lc(pol) != 0 mod prh */
static GEN
nf_pol_red(GEN pol, GEN prh)
{
  long i, l = lgef(pol);
  GEN z = cgetg(l, t_POL); z[1] = pol[1];
  for (i=2; i<l; i++) z[i] = nfreducemodpr_i((GEN)pol[i], prh)[1];
  return z;
}

/* return a bound for T_2(P), P | polbase */
static GEN
nf_factor_bound(GEN nf, GEN polbase)
{
  GEN lt,C,run,p1,p2, T2 = gmael(nf,5,3);
  long i,prec,precnf, d = lgef(polbase), n = degpol(nf[1]);

  precnf = gprecision(T2);
  prec   = DEFAULTPREC;
  for (;;)
  {
    run= realun(prec);
    p1 = realzero(prec);
    for (i=2; i<d; i++)
    {
      p2 = gmul(run, (GEN)polbase[i]);
      p2 = qfeval(T2, p2); if (signe(p2) < 0) break;
      p1 = addrr(p1, gdiv(p2, binome(stoi(d), i-2)));
    }
    if (i == d) break;

    prec = (prec<<1)-2;
    if (prec > precnf)
    {
      if (DEBUGLEVEL>1) err(warnprec, "nfsqff", prec);
      T2 = nf_get_T2((GEN)nf[7], roots((GEN)nf[1], prec));
    }
  }
  lt = (GEN)leading_term(polbase)[1];
  p1 = gmul(p1, mulis(sqri(lt), n));
  C = gpow(stoi(3), dbltor(0.75 + d), DEFAULTPREC);
  return gdiv(gmul(C, p1), gmulsg(d, mppi(DEFAULTPREC)));
}

static int
nf_combine_factors(nfcmbf_t *T,long fxn,GEN psf,long dlim)
{
  int val = 0; /* assume failure */
  GEN newf, newpsf = NULL;
  long newd, i;
  gpmem_t av, ltop;

  /* Assertion: fxn <= T->nfactmod && dlim > 0 */

  /* first, try deeper factors without considering the current one */
  if (fxn != T->nfactmod)
  {
    val = nf_combine_factors(T,fxn+1,psf,dlim);
    if (val && psf) return 1;
  }

  /* second, try including the current modular factor in the product */
  newf = (GEN)T->fact[fxn];
  if (!newf) return val; /* modular factor already used */
  newd = degpol(newf);
  if (newd > dlim) return val; /* degree of new factor is too large */

  av = avma;
  if (newd % T->hint == 0)
  {
    GEN p, quot,rem, nf = T->nf;

    newpsf = nf_pol_mul(nf, psf? psf: T->lt, newf);
    newpsf = nf_pol_lift(T->h,T->hinv,T->den,newpsf);
    /* try out the new combination */
    ltop=avma;
    quot=nf_pol_divres(nf,T->pol,newpsf,&rem);
    if (gcmp0(rem))  /* found a factor */
    {
      p = nf_pol_mul(nf,element_inv(nf,leading_term(newpsf)),newpsf);
      T->res[++T->nfact] = (long) p; /* store factor */
      T->fact[fxn]=0; /* remove used modular factor */

      /* fix up target */
      p=gun; quot=unifpol(nf,quot,0);
      for (i=2; i<lgef(quot); i++)
        p = mpppcm(p, denom((GEN)quot[i]));

      T->pol = gmul(quot,p);
      T->lt  = leading_term(T->pol);
      return 1;
    }
    avma=ltop;
  }

  /* If room in degree limit + more modular factors to try, add more factors to
   * newpsf */
  if (newd < dlim && fxn < T->nfactmod
                  && nf_combine_factors(T,fxn+1,newpsf,dlim-newd))
  {
    T->fact[fxn]=0; /* remove used modular factor */
    return 1;
  }
  avma = av; return val;
}

/* return the factorization of the square-free polynomial x.
   The coeff of x are in Z_nf and its leading term is a rational integer.
   deg(x) > 1
   If fl = 1,return only the roots of x in nf */
static GEN
nfsqff(GEN nf,GEN pol, long fl)
{
  long d=lgef(pol), i, k, m, n, nbf, anbf, ct;
  gpmem_t av = avma;
  GEN pr,rep,k2,C,h,dk,bad,p,prk,polbase,fact,pk;
  GEN ap,polmod,polred,hinv,lt,minp;
  nfcmbf_t T;

  if (DEBUGLEVEL>3) msgtimer("square-free");
  polbase = unifpol(nf,pol,0);
  polmod  = unifpol(nf,pol,1);
  lt  = (GEN)leading_term(polbase)[1];

  dk = absi((GEN)nf[3]);
  bad = mulii(mulii(dk,(GEN)nf[4]), lt);
  n = degpol(nf[1]);

  C = nf_factor_bound(nf, polbase);
  if (DEBUGLEVEL>3) fprintferr("Bound on the T2-norm of a factor: %Z\n", C);

  k2 = bestlift_bound(C, n);
  minp = gexp(gmul2n(k2,-6), DEFAULTPREC);
  if (expo(minp) > 32) minp = utoi(1UL<<31);
  minp = gceil(minp); if (DEBUGLEVEL>3)
  {
    fprintferr("lower bound for the prime numbers: %Z\n", minp);
    msgtimer("bounds computation");
  }

  p = polred = NULL; /* gcc -Wall */
  pr= NULL; nbf = BIGINT;
  for (ct = 5;; minp = addis(ap,1))
  {
    GEN apr = choose_prime(nf,bad,minp);
    GEN aprh = prime_to_ideal(nf,apr);

    ap = (GEN)apr[1];
    polred = nf_pol_red(polbase, aprh);
    if (!FpX_is_squarefree(polred,ap)) continue;

    ct--;
    anbf= FpX_nbfact(polred,ap);
    if (anbf < nbf)
    {
      nbf = anbf; pr = apr; p = ap;
      if (DEBUGLEVEL>3) {
        fprintferr("prime ideal considered: %Z\n", pr);
        fprintferr("number of irreducible factors: %ld\n", nbf);
      }
      if (nbf == 1) /* irreducible */
      {
        if (fl) { avma = av; return cgetg(1,t_VEC); }
        return gerepilecopy(av, _vec(polmod));
      }
    }
    if (pr && !ct) break;
  }
  if (DEBUGLEVEL>3) {
    fprintferr("prime ideal chosen: %Z\n", pr);
    msgtimer("choice of the prime ideal");
  }

  h = bestlift_init(nf,pr,C, &k,&prk);
  if (DEBUGLEVEL>3) msgtimer("computation of H");
  pk = gcoeff(prk,1,1);
  hinv = ZM_inv(h, pk);
  if (DEBUGLEVEL>3) msgtimer("computation of H^(-1)");

  /* polred is monic */
  polred = nf_pol_red(gmul(mpinvmod(lt,pk), polbase), prk);

  fact = (GEN)factmod0(polred,p)[1];
  rep = hensel_lift_fact(polred,fact,NULL,p,pk,k);
  if (DEBUGLEVEL>3) msgtimer("Hensel lift");

  if (fl)
  { /* roots only */
    long x_a[] = { evaltyp(t_POL)|_evallg(4), 0,0,0 };
    GEN rem,p2,p3;
    x_a[1] = polmod[1]; setlgef(x_a, 4);
    x_a[3] = un;
    for (m=1,i=1; i<lg(rep); i++)
    {
      p2 = (GEN)rep[i]; if (degpol(p2) > 1) break;

      p3 = algtobasis(nf, (GEN)p2[2]);
      p3 = nf_bestlift(h,hinv,pk, gmul(lt,p3));
      p3 = basistoalg(nf, gdiv(p3,lt));
      x_a[2] = (long)p3; /* check P(p3) == 0 */
      p2 = poldivres(polmod, x_a, &rem);
      if (!signe(rem)) { polmod = p2; rep[m++] = lneg(p3); }
    }
    setlg(rep, m); return gerepilecopy(av, rep);
  }

  m = lg(rep);
  for (i=1; i<m; i++) rep[i] = (long)unifpol(nf,(GEN)rep[i],0);

  T.pol      = polmod;
  T.lt       = lt;
  T.h        = h;
  T.hinv     = hinv;
  T.den      = pk;
  T.fact     = rep;
  T.res      = cgetg(m,t_VEC);
  T.nfact    = 0;
  T.nfactmod = m-1;
  T.nf       = nf;
  T.hint     = 1;
  nf_combine_factors(&T, 1,NULL,d-3);
  if (DEBUGLEVEL>3) msgtimer("computation of the factors");

  m = T.nfact + 1;
  if (degpol(T.pol))
    T.res[m++] = (long) nf_pol_divres(nf,T.pol,T.lt,NULL);

  rep = cgetg(m,t_VEC);
  for (i=1;i<m; i++) rep[i] = (long)unifpol(nf,(GEN)T.res[i],1);
  return gerepileupto(av, rep);
}

/* return the characteristic polynomial of alpha over nf, where alpha
   is an element of the algebra nf[X]/(T) given as a polynomial in X */
GEN
rnfcharpoly(GEN nf,GEN T,GEN alpha,int v)
{
  long vnf, vT, lT;
  gpmem_t av = avma;
  GEN p1;

  nf=checknf(nf); vnf = varn(nf[1]);
  if (v<0) v = 0;
  T = fix_relative_pol(nf,T,1);
  if (typ(alpha) == t_POLMOD) alpha = lift_to_pol(alpha);
  lT = lgef(T);
  if (typ(alpha) != t_POL || varn(alpha) == vnf)
    return gerepileupto(av, gpowgs(gsub(polx[v], alpha), lT - 3));
  vT = varn(T);
  if (varn(alpha) != vT || v >= vnf)
    err(talker,"incorrect variables in rnfcharpoly");
  if (lgef(alpha) >= lT) alpha = gmod(alpha,T);
  if (lT <= 4)
    return gerepileupto(av, gsub(polx[v], alpha));
  p1 = caract2(unifpol(nf,T,1), unifpol(nf,alpha,1), v);
  return gerepileupto(av, unifpol(nf,p1,1));
}

/* relative Dedekind criterion over nf, applied to the order defined by a
 * root of irreducible polynomial T, modulo the prime ideal pr. Returns
 * [flag,basis,val], where basis is a pseudo-basis of the enlarged order,
 * flag is 1 iff this order is pr-maximal, and val is the valuation at pr of
 * the order discriminant */
GEN
rnfdedekind(GEN nf,GEN T,GEN pr)
{
  long vt, r, d, da, n, m, i, j;
  gpmem_t av=avma;
  GEN p1,p2,p,tau,g,vecun,veczero,matid;
  GEN prhall,res,h,k,base,Ca;

  nf=checknf(nf); Ca=unifpol(nf,T,0);
  res=cgetg(4,t_VEC);
  if (typ(pr)==t_VEC && lg(pr)==3)
  { prhall = (GEN)pr[2]; pr = (GEN)pr[1]; }
  else
    prhall=nfmodprinit(nf,pr);
  p=(GEN)pr[1]; tau=gdiv((GEN)pr[5],p);
  n=degpol(nf[1]); m=degpol(T);

  vecun = gscalcol_i(gun,n);
  veczero = zerocol(n);

  p1=(GEN)nffactormod(nf,Ca,pr)[1];
  r=lg(p1); if (r < 2) err(constpoler,"rnfdedekind");
  g=lift((GEN)p1[1]);
  for (i=2; i<r; i++)
    g = nf_pol_mul(nf,g, lift((GEN)p1[i]));
  h=nfmod_pol_divres(nf,prhall,Ca,g,NULL);
  k=nf_pol_mul(nf,tau,gsub(Ca, nf_pol_mul(nf,lift(g),lift(h))));
  p2=nfmod_pol_gcd(nf,prhall,g,h);
  k= nfmod_pol_gcd(nf,prhall,p2,k);

  d=degpol(k);  /* <= m */
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
      da=degpol(pal);
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
  res[2]=(long)base; return gerepilecopy(av, res);
}
