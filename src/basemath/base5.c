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
/*                       BASIC NF OPERATIONS                       */
/*                          (continued 2)                          */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
extern GEN mul_content(GEN cx, GEN cy);

GEN
matbasistoalg(GEN nf,GEN x)
{
  long i,j,lx,li;
  GEN p1,z;

  if (typ(x)!=t_MAT)
    err(talker,"argument must be a matrix in matbasistoalg");
  lx=lg(x); z=cgetg(lx,t_MAT); if (lx==1) return z;

  li=lg(x[1]);
  for (j=1; j<lx; j++)
  {
    p1=cgetg(li,t_COL); z[j]=(long)p1;
    for (i=1; i<li; i++) p1[i]=(long)basistoalg(nf,gcoeff(x,i,j));
  }
  return z;
}

GEN
matalgtobasis(GEN nf,GEN x)
{
  long i,j,lx,li;
  GEN p1,z,c;

  if (typ(x)!=t_MAT)
    err(talker,"argument must be a matrix in matalgtobasis");
  lx=lg(x); z=cgetg(lx,t_MAT); if (lx==1) return z;

  li=lg(x[1]);
  for (j=1; j<lx; j++)
  {
    p1=cgetg(li,t_COL); z[j]=(long)p1;
    for (i=1; i<li; i++)
    {
      c = gcoeff(x,i,j);
      c = typ(c)==t_COL? gcopy(c): algtobasis(nf,c);
      p1[i]=(long)c;
    }
  }
  return z;
}

static GEN
rnfmakematrices(GEN rnf)
{
  long i,j,k,n,r1,r2,ru,ruk,r1rel,r2rel;
  GEN nf,pol,rac,base,base1,racnf,sig,vecmat,vecM,vecMC,vecT2,rack;
  GEN M,p2,p3,MC,sigk,T2,T,p1,MD,TI,MDI;

  nf=(GEN)rnf[10]; racnf=(GEN)nf[6]; pol=(GEN)rnf[1];
  n=degpol(pol);
  base=(GEN)rnf[7]; base1=(GEN)base[1]; rac=(GEN)rnf[6]; sig=(GEN)rnf[2];
  r1 = nf_get_r1(nf);
  r2 = nf_get_r2(nf); ru = r1+r2;
  vecmat=cgetg(8,t_VEC);
  vecM=cgetg(ru+1,t_VEC); vecmat[1]=(long)vecM;
  vecMC=cgetg(ru+1,t_VEC); vecmat[2]=(long)vecMC;
  vecT2=cgetg(ru+1,t_VEC); vecmat[3]=(long)vecT2;
  for (k=1; k<=ru; k++)
  {
    rack=(GEN)rac[k]; ruk=lg(rack)-1;
    M=cgetg(n+1,t_MAT); vecM[k]=(long)M;
    for (j=1; j<=n; j++)
    {
      p2=cgetg(ruk+1,t_COL); M[j]=(long)p2; p3=lift((GEN)base1[j]);
      p3=gsubst(p3,varn(nf[1]),(GEN)racnf[k]);
      for (i=1; i<=ruk; i++) p2[i]=lsubst(p3,varn(rnf[1]),(GEN)rack[i]);
    }
    MC=gconj(gtrans(M)); vecMC[k]=(long)MC;
    if (k<=r1)
    {
      sigk=(GEN)sig[k]; r1rel=itos((GEN)sigk[1]); r2rel=itos((GEN)sigk[2]);
      if (r1rel+r2rel != lg(MC)-1) err(talker,"bug in rnfmakematrices");
      for (j=r1rel+1; j<=r1rel+r2rel; j++) MC[j]=lmul2n((GEN)MC[j],1);
    }
    T2=gmul(MC,M); vecT2[k]=(long)T2;
  }
  T=cgetg(n+1,t_MAT); vecmat[4]=(long)T;
  for (j=1; j<=n; j++)
  {
    p1=cgetg(n+1,t_COL); T[j]=(long)p1;
    for (i=1; i<=n; i++)
      p1[i]=ltrace(gmodulcp(gmul((GEN)base1[i],(GEN)base1[j]),pol));
  }
  MD=cgetg(1,t_MAT); vecmat[5]=(long)MD; /* matrice de la differente */
  TI=cgetg(1,t_MAT); vecmat[6]=(long)TI; /* matrice .... ? */
  MDI=cgetg(1,t_MAT); vecmat[7]=(long)MDI; /* matrice .... ? */
  return vecmat;
}

GEN
rnfinitalg(GEN nf,GEN pol,long prec)
{
  gpmem_t av = avma;
  long m,n,r1,r2,vnf,i,j,k,vpol,r1j,r2j,lfac,degabs;
  GEN RES,sig,rac,p1,p2,liftpol,delta,RAC,ro,p3,bas;
  GEN f,f2,fac,fac1,fac2,id,p4;

  if (typ(pol)!=t_POL) err(notpoler,"rnfinitalg");
  nf=checknf(nf); n=degpol(pol); vpol=varn(pol);
  pol = fix_relative_pol(nf,pol,0);
  vnf = varn(nf[1]);

  if (vpol >= vnf)
    err(talker,"main variable must be of higher priority in rnfinitalg");
  RES=cgetg(12,t_VEC);
  RES[1]=(long)pol;
  m = degpol(nf[1]); degabs=n*m;
  r1 = nf_get_r1(nf); r2 = (m-r1) >> 1;
  sig=cgetg(r1+r2+1,t_VEC); RES[2]=(long)sig;
  rac=(GEN)nf[6]; liftpol=lift(pol);
  RAC=cgetg(r1+r2+1,t_VEC); RES[6]=(long)RAC;
  for (j=1; j<=r1; j++)
  {
    p1=gsubst(liftpol,vnf,(GEN)rac[j]);
    ro=roots(p1,prec);
    r1j=0;
    while (r1j<n && gcmp0(gimag((GEN)ro[r1j+1]))) r1j++;
    p2=cgetg(3,t_VEC); p2[1]=lstoi(r1j); p2[2]=lstoi(r2j=((n-r1j)>>1));
    sig[j]=(long)p2;
    p3=cgetg(r1j+r2j+1,t_VEC);
    for (i=1; i<=r1j; i++) p3[i]=lreal((GEN)ro[i]);
    for (; i<=r1j+r2j; i++) p3[i]=(long)ro[(i<<1)-r1j];
    RAC[j]=(long)p3;
  }
  for (; j<=r1+r2; j++)
  {
    p2=cgetg(3,t_VEC); p2[1]=zero; p2[2]=lstoi(n); sig[j]=(long)p2;
    p1=gsubst(liftpol,vnf,(GEN)rac[j]);
    RAC[j]=(long)roots(p1,prec);
  }
  p1 = rnfpseudobasis(nf,pol);

  delta = cgetg(3,t_VEC);
    delta[1]=p1[3];
    delta[2]=p1[4];
  RES[3]=(long)delta;
  p2 = matbasistoalg(nf,(GEN)p1[1]);
  bas = cgetg(3,t_VEC);
    bas[1]=(long)mat_to_vecpol(p2,vpol);
    bas[2]=(long)p1[2];
  RES[7]=(long)bas;
  RES[8]=linvmat(p2);

  f2 = idealdiv(nf, discsr(pol), (GEN)p1[3]);
  fac = idealfactor(nf,f2);
  fac1 = (GEN)fac[1];
  fac2 = (GEN)fac[2]; lfac = lg(fac1)-1;
  f = idmat(m);
  for (i=1; i<=lfac; i++)
  {
    if (mpodd((GEN)fac2[i])) err(bugparier,"rnfinitalg (odd exponent)");
    f=idealmul(nf,f,idealpow(nf,(GEN)fac1[i],gmul2n((GEN)fac2[i],-1)));
  }
  RES[4]=(long)f;
  RES[10]=(long)nf;
  RES[5]=(long)rnfmakematrices(RES);
  if (DEBUGLEVEL>1) msgtimer("matrices");
  RES[9]=lgetg(1,t_VEC); /* table de multiplication */
  p2=cgetg(6,t_VEC); RES[11]=(long)p2;
  p1=rnfequation2(nf,pol); for (i=1; i<=3; i++) p2[i]=p1[i];
  p4=cgetg(degabs+1,t_MAT);
  for (i=1; i<=n; i++)
  { /* removing denominators speeds up multiplication */
    GEN c, cop3,com, om = rnfelementreltoabs(RES,gmael(bas,1,i));

    if (DEBUGLEVEL>1) msgtimer("i = %ld",i);
    om = primitive_part(om, &com);
    id=gmael(bas,2,i);
    for (j=1; j<=m; j++)
    {
      p1 = gmul((GEN)nf[7],(GEN)id[j]);
      p3 = gsubst(p1, vnf, (GEN)p2[2]);
      p3 = primitive_part(p3, &cop3);
      c = mul_content(cop3, com);

      p3 = lift_intern(gmul(om,p3));
      if (c) p3 = gmul(c,p3);
      p4[(i-1)*m+j] = (long)pol_to_vec(p3, degabs);
    }
  }
  if (DEBUGLEVEL>1) msgtimer("p4");
  p4 = Q_remove_denom(p4, &p3);
  if (p3) p4 = hnfmodid(p4, p3); else p4 = idmat(degabs);
  if (DEBUGLEVEL>1) msgtimer("hnfmod");
  for (j=degabs-1; j>0; j--)
    if (cmpis(gcoeff(p4,j,j),2) > 0)
    {
      p1=shifti(gcoeff(p4,j,j),-1);
      for (k=j+1; k<=degabs; k++)
        if (cmpii(gcoeff(p4,j,k),p1) > 0)
          for (i=1; i<=j; i++)
            coeff(p4,i,k)=lsubii(gcoeff(p4,i,k),gcoeff(p4,i,j));
    }
  if (p3) p4 = gdiv(p4,p3);
  p2[4]=(long)mat_to_vecpol(p4,vpol);
  p2[5]=linvmat(p4);
  return gerepilecopy(av,RES);
}

GEN
rnfbasistoalg(GEN rnf,GEN x)
{
  long tx=typ(x), lx=lg(x), i, n;
  gpmem_t av=avma, tetpil;
  GEN p1,z,nf;

  checkrnf(rnf); nf=(GEN)rnf[10];
  switch(tx)
  {
    case t_VEC:
      x=gtrans(x); /* fall through */
    case t_COL:
      n=lg(x)-1; p1=cgetg(n+1,t_COL);
      for (i=1; i<=n; i++)
      {
	if (typ(x[i])==t_COL) p1[i]=(long)basistoalg(nf,(GEN)x[i]);
	else p1[i]=x[i];
      }
      p1=gmul(gmael(rnf,7,1),p1); tetpil=avma;
      return gerepile(av,tetpil,gmodulcp(p1,(GEN)rnf[1]));

    case t_MAT:
      z=cgetg(lx,tx);
      for (i=1; i<lx; i++) z[i]=(long)rnfbasistoalg(rnf,(GEN)x[i]);
      return z;

    case t_POLMOD:
      return gcopy(x);

    default:
      z=cgetg(3,t_POLMOD); z[1]=lcopy((GEN)rnf[1]);
      z[2]=lmul(x,polun[varn(rnf[1])]); return z;
  }
}

extern long polegal_spec(GEN x, GEN y);

/* assume x is a t_POLMOD */
GEN
lift_to_pol(GEN x)
{
  GEN y = (GEN)x[2]; 
  return (typ(y) != t_POL)? gtopoly(y,varn(x[1])): y;
}

extern GEN mulmat_pol(GEN A, GEN x);

GEN
rnfalgtobasis(GEN rnf,GEN x)
{
  long tx=typ(x), i, lx;
  gpmem_t av=avma;
  GEN z;

  checkrnf(rnf);
  switch(tx)
  {
    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); z = cgetg(lx,tx);
      for (i=1; i<lx; i++) z[i]=(long)rnfalgtobasis(rnf,(GEN)x[i]);
      return z;

    case t_POLMOD:
      if (!polegal_spec((GEN)rnf[1],(GEN)x[1]))
	err(talker,"not the same number field in rnfalgtobasis");
      x = lift_to_pol(x); /* fall through */
    case t_POL:
    { /* cf algtobasis_i */
      GEN P = (GEN)rnf[1];
      long N = degpol(P);
      if (degpol(x) >= N) x = gres(x,P);
      return gerepileupto(av, mulmat_pol((GEN)rnf[8], x));
    }
  }
  return gscalcol(x, degpol(rnf[1]));
}

/* x doit etre un polymod ou un polynome ou un vecteur de tels objets... */
GEN
rnfelementreltoabs(GEN rnf,GEN x)
{
  long tx, i, lx, va, tp3;
  gpmem_t av=avma;
  GEN z,p1,p2,p3,polabs,teta,alpha,s,k;

  checkrnf(rnf); tx=typ(x); lx=lg(x); va=varn((GEN)rnf[1]);
  switch(tx)
  {
    case t_VEC: case t_COL: case t_MAT:
      z=cgetg(lx,tx);
      for (i=1; i<lx; i++) z[i]=(long)rnfelementreltoabs(rnf,(GEN)x[i]);
      return z;

    case t_POLMOD:
      x=lift_to_pol(x); /* fall through */
    case t_POL:
      if (gvar(x) > va) x = scalarpol(x,va);
      p1=(GEN)rnf[11]; polabs=(GEN)p1[1]; alpha=(GEN)p1[2]; k=(GEN)p1[3];
      if (typ(alpha) == t_INT)
	teta=gmodulcp(gsub(polx[va],gmul(k,alpha)),polabs);
      else
	teta=gmodulcp(gsub(polx[va],gmul(k,(GEN)alpha[2])),polabs);
      s=gzero;
      for (i=lgef(x)-1; i>1; i--)
      {
	p3=(GEN)x[i]; tp3=typ(p3);
	if (is_const_t(tp3)) p2 = p3;
	else
	  switch(tp3)
	  {
	    case t_POLMOD:
	      p3 = (GEN)p3[2]; /* fall through */
	    case t_POL:
	      p2 = poleval(p3,alpha);
              break;
            default: err(talker, "incorrect data in rnfelementreltoabs");
              return NULL; /* not reached */
	  }
	s=gadd(p2,gmul(teta,s));
      }
      return gerepileupto(av,s);

    default: return gcopy(x);
  }
}

/* assume x,T,pol t_POL. T defines base field, pol defines rnf over T.
 * x an absolute element of the extension */
GEN 
eltabstorel(GEN x, GEN T, GEN pol, GEN k)
{
  GEN theta = gmodulcp(gadd(polx[varn(pol)],
                            gmul(k, gmodulcp(polx[varn(T)],T))), pol);
  return poleval(x, theta);
}

GEN
rnfelementabstorel(GEN rnf,GEN x)
{
  long tx, i, lx;
  gpmem_t av=avma;
  GEN z,k,nf,T;

  checkrnf(rnf); tx=typ(x); lx=lg(x);
  switch(tx)
  {
    case t_VEC: case t_COL: case t_MAT:
      z=cgetg(lx,tx);
      for (i=1; i<lx; i++) z[i]=(long)rnfelementabstorel(rnf,(GEN)x[i]);
      return z;

    case t_POLMOD:
      x = lift_to_pol(x); /* fall through */
    case t_POL:
      k  = (GEN)rnf[11]; k = (GEN)k[3];
      nf = (GEN)rnf[10]; T = (GEN)nf[1];
      return gerepileupto(av, eltabstorel(x,T,(GEN)rnf[1],k));

    default: return gcopy(x);
  }
}

/* x doit etre un polymod ou un polynome ou un vecteur de tels objets... */
GEN
rnfelementup(GEN rnf,GEN x)
{
  long i,lx,tx;
  GEN z;

  checkrnf(rnf); tx=typ(x); lx=lg(x);
  switch(tx)
  {
    case t_VEC: case t_COL: case t_MAT:
      z=cgetg(lx,tx);
      for (i=1; i<lx; i++) z[i]=(long)rnfelementup(rnf,(GEN)x[i]);
      return z;

    case t_POLMOD:
      x=(GEN)x[2]; /* fall through */
    case t_POL:
      return poleval(x,gmael(rnf,11,2));

    default: return gcopy(x);
  }
}

/* x doit etre un polymod ou un polynome ou un vecteur de tels objets..*/
GEN
rnfelementdown(GEN rnf,GEN x)
{
  gpmem_t av = avma;
  long i,lx,tx;
  GEN p1,z;

  checkrnf(rnf); tx=typ(x); lx=lg(x);
  switch(tx)
  {
    case t_VEC: case t_COL: case t_MAT:
      z=cgetg(lx,tx);
      for (i=1; i<lx; i++) z[i]=(long)rnfelementdown(rnf,(GEN)x[i]);
      return z;

    case t_POLMOD:
      x=(GEN)x[2]; /* fall through */
    case t_POL:
      if (gcmp0(x)) return gzero;

      p1=rnfelementabstorel(rnf,x);
      if (typ(p1)==t_POLMOD && varn(p1[1])==varn(rnf[1])) p1=(GEN)p1[2];
      if (gvar(p1)>varn(rnf[1])) return gerepilecopy(av,p1);
      if (lgef(p1)==3) return gerepilecopy(av,(GEN)p1[2]);
      err(talker,"element is not in the base field in rnfelementdown");

    default: return gcopy(x);
  }
}

/* x est exprime sur la base relative */
static GEN
rnfprincipaltohermite(GEN rnf,GEN x)
{
  gpmem_t av=avma, tetpil;
  GEN nf,bas,bas1,p1,z;

  x=rnfbasistoalg(rnf,x); nf=(GEN)rnf[10];
  bas=(GEN)rnf[7]; bas1=(GEN)bas[1];
  p1=rnfalgtobasis(rnf,gmul(x,gmodulcp(bas1,(GEN)rnf[1])));
  z=cgetg(3,t_VEC); z[2]=bas[2];
  settyp(p1,t_MAT); z[1]=(long)p1;

  tetpil=avma;
  return gerepile(av,tetpil,nfhermite(nf,z));
}

GEN
rnfidealhermite(GEN rnf,GEN x)
{
  long tx=typ(x), lx=lg(x), i, j, n, m;
  gpmem_t av=avma, tetpil;
  GEN z,p1,p2,x1,x2,x1j,nf,bas,unnf,zeronf;

  checkrnf(rnf);
  n=degpol(rnf[1]); nf=(GEN)rnf[10]; bas=(GEN)rnf[7];

  switch(tx)
  {
    case t_INT: case t_FRAC: case t_FRACN: z=cgetg(3,t_VEC);
      m=degpol(nf[1]); zeronf=gscalcol_i(gzero,m); unnf=gscalcol_i(gun,m);
      p1=cgetg(n+1,t_MAT); z[1]=(long)p1;
      for (j=1; j<=n; j++)
      {
	p2=cgetg(n+1,t_COL); p1[j]=(long)p2;
	for (i=1; i<=n; i++) p2[i]=(i==j)?(long)unnf:(long)zeronf;
      }
      z[2]=lmul(x,(GEN)bas[2]); return z;

    case t_POLMOD: case t_POL:
      p1=rnfalgtobasis(rnf,x); tetpil=avma;
      return gerepile(av,tetpil,rnfprincipaltohermite(rnf,p1));

    case t_VEC:
      switch(lx)
      {
	case 3:
	  x1=(GEN)x[1];
	  if (typ(x1)!=t_MAT || lg(x1) < n+1 || lg(x1[1]) != n+1)
	    err(talker,"incorrect type in rnfidealhermite");
	  p1=cgetg(n+1,t_MAT);
	  for (j=1; j<=n; j++)
	  {
	    p2=cgetg(n+1,t_COL); p1[j]=(long)p2; x1j=(GEN)x1[j];
	    for (i=1; i<=n; i++)
	    {
              tx = typ(x1j[i]);
              if (is_const_t(tx)) p2[i] = x1j[i];
              else
                switch(tx)
                {
                  case t_POLMOD: case t_POL:
                    p2[i]=(long)algtobasis(nf,(GEN)x1j[i]); break;
                  case t_COL:
                    p2[i]=x1j[i]; break;
                  default: err(talker,"incorrect type in rnfidealhermite");
                }
	    }
	  }
	  x2=(GEN)x[2];
	  if (typ(x2)!=t_VEC || lg(x2)!=lg(x1))
	    err(talker,"incorrect type in rnfidealhermite");
	  tetpil=avma; z=cgetg(3,t_VEC); z[1]=lcopy(p1); z[2]=lcopy(x2);
	  z=gerepile(av,tetpil,nfhermite(nf,z));
	  if (lg(z[1]) != n+1)
	    err(talker,"not an ideal in rnfidealhermite");
	  return z;

	case 6:
	  err(impl,"rnfidealhermite for prime ideals");
	default:
	  err(typeer,"rnfidealhermite");
      }

    case t_COL:
      if (lx!=(n+1)) err(typeer,"rnfidealhermite");
      return rnfprincipaltohermite(rnf,x);

    case t_MAT:
      return rnfidealabstorel(rnf,x);
  }
  err(typeer,"rnfidealhermite");
  return NULL; /* not reached */
}

GEN
rnfidealnormrel(GEN rnf,GEN id)
{
  long i, n;
  gpmem_t av=avma;
  GEN z,id2,nf;

  checkrnf(rnf);
  id=rnfidealhermite(rnf,id); id2=(GEN)id[2];
  n=degpol(rnf[1]); nf=(GEN)rnf[10];
  if (n==1) { avma=av; return idmat(degpol(nf[1])); }
  z=(GEN)id2[1]; for (i=2; i<=n; i++) z=idealmul(nf,z,(GEN)id2[i]);
  return gerepileupto(av,z);
}

GEN
rnfidealnormabs(GEN rnf,GEN id)
{
  long i, n;
  gpmem_t av=avma;
  GEN z,id2;

  checkrnf(rnf);
  id=rnfidealhermite(rnf,id); id2=(GEN)id[2];
  n=degpol(rnf[1]);
  z=gun; for (i=1; i<=n; i++) z=gmul(z,dethnf((GEN)id2[i]));
  return gerepileupto(av,z);
}

GEN
rnfidealreltoabs(GEN rnf,GEN x)
{
  long i, j, k, n, m;
  gpmem_t av=avma;
  GEN nf,basinv,om,id,p1,p2,p3,p4,p5,c;

  checkrnf(rnf);
  x = rnfidealhermite(rnf,x);
  n=degpol(rnf[1]); nf=(GEN)rnf[10]; m=degpol(nf[1]);
  basinv = gmael(rnf,11,5);
  p3=cgetg(n*m+1,t_MAT); p2=gmael(rnf,11,2);
  for (i=1; i<=n; i++)
  {
    om=rnfbasistoalg(rnf,gmael(x,1,i)); id=gmael(x,2,i);
    om=rnfelementreltoabs(rnf,om);
    for (j=1; j<=m; j++)
    {
      p1=gmul((GEN)nf[7],(GEN)id[j]);
      p4=lift_intern(gmul(om,gsubst(p1,varn(nf[1]),p2)));
      p5=cgetg(n*m+1,t_COL);
      for (k=0; k<n*m; k++) p5[k+1]=(long)truecoeff(p4,k);
      p3[(i-1)*m+j]=(long)p5;
    }
  }
  p1 = gmul(basinv,p3);
  p1 = primitive_part(p1, &c);
  p2 = gmael(p1,1,1); /* x \cap Z */
  p1 = hnfmodid(p1, p2);
  if (c) p1 = gmul(p1, c);
  return gerepileupto(av, p1);
}

GEN
rnfidealabstorel(GEN rnf,GEN x)
{
  long n, m, j, k;
  gpmem_t av=avma, tetpil;
  GEN nf,basabs,ma,xj,p1,p2,id;

  checkrnf(rnf); n=degpol(rnf[1]); nf=(GEN)rnf[10]; m=degpol(nf[1]);
  if (typ(x)!=t_MAT || lg(x)!=(n*m+1) || lg(x[1])!=(n*m+1))
    err(impl,"rnfidealabstorel for an ideal not in HNF");
  basabs=gmael(rnf,11,4); ma=cgetg(n*m+1,t_MAT);
  for (j=1; j<=n*m; j++)
  {
    p2=cgetg(n+1,t_COL); ma[j]=(long)p2;
    xj=gmul(basabs,(GEN)x[j]);
    xj=lift_intern(rnfelementabstorel(rnf,xj));
    for (k=0; k<n; k++)
      p2[k+1]=(long)truecoeff(xj,k);
  }
  ma=gmul((GEN)rnf[8],ma);
  p1=cgetg(n*m+1,t_VEC); id=idmat(m);
  for (j=1; j<=n*m; j++) p1[j]=(long)id;
  p2=cgetg(3,t_VEC); p2[1]=(long)ma; p2[2]=(long)p1;
  tetpil=avma; return gerepile(av,tetpil,nfhermite(nf,p2));
}

GEN
rnfidealdown(GEN rnf,GEN x)
{
  gpmem_t av=avma;

  checkrnf(rnf); x=rnfidealhermite(rnf,x);
  return gerepilecopy(av,gmael(x,2,1));
}

/* lift ideal x to the relative extension, returns a Z-basis */
GEN
rnfidealup(GEN rnf,GEN x)
{
  long i, n, m;
  gpmem_t av=avma, tetpil;
  GEN nf,bas,bas2,p1,p2,zeronf,unnf;

  checkrnf(rnf);
  bas=(GEN)rnf[7]; bas2=(GEN)bas[2];
  n=lg(bas2)-1; nf=(GEN)rnf[10]; m=degpol((GEN)nf[1]);
  zeronf=zerocol(m); unnf=gscalcol_i(gun,m);
  p2=cgetg(3,t_VEC); p1=cgetg(n+1,t_VEC);
  p2[1]=(long)idmat_intern(n,unnf,zeronf);
  p2[2]=(long)p1;
  for (i=1; i<=n; i++) p1[i]=(long)idealmul(nf,x,(GEN)bas2[i]);
  tetpil=avma; return gerepile(av,tetpil,rnfidealreltoabs(rnf,p2));
}

/* x a relative HNF ---> vector of 2 generators (relative polymods) */
GEN
rnfidealtwoelement(GEN rnf,GEN x)
{
  long j;
  gpmem_t av=avma, tetpil;
  GEN p1,p2,p3,res,polabs,nfabs,z;

  checkrnf(rnf);
  res=(GEN)rnf[11]; polabs=(GEN)res[1];
  nfabs=cgetg(10,t_VEC); nfabs[1]=(long)polabs;
  for (j=2; j<=9; j++) nfabs[j]=zero;
  nfabs[7]=(long)lift((GEN)res[4]); nfabs[8]=res[5];
  p1=rnfidealreltoabs(rnf,x);
  p2=ideal_two_elt(nfabs,p1);
  p3=rnfelementabstorel(rnf,gmul((GEN)res[4],(GEN)p2[2]));
  tetpil=avma; z=cgetg(3,t_VEC); z[1]=lcopy((GEN)p2[1]);
  z[2]=(long)rnfalgtobasis(rnf,p3);
  return gerepile(av,tetpil,z);
}

GEN
rnfidealmul(GEN rnf,GEN x,GEN y) /* x et y sous HNF relative uniquement */
{
  long i, j, n;
  gpmem_t av=avma, tetpil;
  GEN z,nf,x1,x2,p1,p2,p3,p4,p5,res;

  z=rnfidealtwoelement(rnf,y);
  nf=(GEN)rnf[10]; n=degpol(rnf[1]);
  x=rnfidealhermite(rnf,x);
  x1=gmodulcp(gmul(gmael(rnf,7,1),matbasistoalg(nf,(GEN)x[1])),(GEN) rnf[1]);
  x2=(GEN)x[2]; p1=gmul((GEN)z[1],(GEN)x[1]);
  p2=lift_intern(gmul(rnfbasistoalg(rnf,(GEN)z[2]),x1));
  p3=cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++)
  {
    p4=cgetg(n+1,t_COL); p3[j]=(long)p4; p5=(GEN)p2[j];
    for (i=1; i<=n; i++)
      p4[i]=(long)algtobasis(nf,truecoeff((GEN)p5,i-1));
  }
  res=cgetg(3,t_VEC);
  res[1]=(long)concatsp(p1,p3);
  res[2]=(long)concatsp(x2,x2);
  tetpil=avma; return gerepile(av,tetpil,nfhermite(nf,res));
}
