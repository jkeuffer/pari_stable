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
extern long polegal_spec(GEN x, GEN y);
extern GEN mulmat_pol(GEN A, GEN x);
extern GEN idealsqrtn(GEN nf, GEN x, GEN gn, int strict);

GEN
matbasistoalg(GEN nf,GEN x)
{
  long i, j, li, lx = lg(x);
  GEN c, z = cgetg(lx,t_MAT);

  if (typ(x) != t_MAT) err(talker,"argument must be a matrix in matbasistoalg");
  if (lx == 1) return z;
  li = lg(x[1]);
  for (j=1; j<lx; j++)
  {
    c = cgetg(li,t_COL); z[j] = (long)c;
    for (i=1; i<li; i++) c[i] = (long)basistoalg(nf,gcoeff(x,i,j));
  }
  return z;
}

GEN
matalgtobasis(GEN nf,GEN x)
{
  long i, j, li, lx = lg(x);
  GEN c, z = cgetg(lx, t_MAT);

  if (typ(x) != t_MAT) err(talker,"argument must be a matrix in matalgtobasis");
  if (lx == 1) return z;
  li = lg(x[1]);
  for (j=1; j<lx; j++)
  {
    c = cgetg(li,t_COL); z[j] = (long)c;
    for (i=1; i<li; i++) c[i] = (long)_algtobasis_cp(nf, gcoeff(x,i,j));
  }
  return z;
}

GEN
_checkrnfeq(GEN x)
{
  if (typ(x) == t_VEC)
    switch(lg(x))
    {
      case 12: /* checkrnf(x); */ return (GEN)x[11];
      case  6: /* rnf[11]. FIXME: change the rnf struct */
      case  4: return x;
    }
  return NULL;
}

GEN
checkrnfeq(GEN x)
{
  x = _checkrnfeq(x);
  if (!x) err(talker,"please apply rnfequation(,,1)");
  return x;
}

GEN
eltreltoabs(GEN rnfeq, GEN x)
{
  long i, k, va;
  pari_sp av = avma;
  GEN polabs, teta, alpha, s;

  rnfeq = checkrnfeq(rnfeq);
  polabs= (GEN)rnfeq[1];
  alpha = (GEN)rnfeq[2];
  k     = itos((GEN)rnfeq[3]);

  va = varn(polabs);
  if (gvar(x) > va) x = scalarpol(x,va);
  /* Mod(X + k alpha, polabs(X)), alpha root of the polynomial defining base */
  teta = gmodulcp(gsub(polx[va], gmulsg(k,lift_intern(alpha))), polabs);
  s = gzero;
  for (i=lgef(x)-1; i>1; i--)
  {
    GEN c = (GEN)x[i];
    long tc = typ(c);
    switch(tc)
    {
      case t_POLMOD: c = (GEN)c[2]; /* fall through */
      case t_POL:    c = poleval(c, alpha); break;
      default:
        if (!is_const_t(tc)) err(talker, "incorrect data in eltreltoabs");
    }
    s = gadd(c, gmul(teta,s));
  }
  return gerepileupto(av,s);
}

static GEN
rnfmakematrices(GEN rnf)
{
  long i,j,k,n,r1,r2,ru, vnf,vpol;
  GEN nf,pol,rac,bas,bas1,racnf,sig,z,vecM,vecMC,vecT2;
  GEN p1,p2,p3,T,MD,TI,MDI;

  pol = (GEN)rnf[1]; n = degpol(pol); vpol = varn(pol);
  sig = (GEN)rnf[2];
  rac = (GEN)rnf[6];
  bas = (GEN)rnf[7]; bas1 = lift((GEN)bas[1]);
  nf = (GEN)rnf[10]; racnf = (GEN)nf[6]; vnf = varn(nf[1]);
  nf_get_sign(nf,&r1,&r2); ru = r1+r2;
  z = cgetg(8,t_VEC);
  vecM = cgetg(ru+1,t_VEC); z[1] = (long)vecM;
  vecMC= cgetg(ru+1,t_VEC); z[2] = (long)vecMC;
  vecT2= cgetg(ru+1,t_VEC); z[3] = (long)vecT2;
  for (k=1; k<=ru; k++)
  {
    GEN M, MC, rack = (GEN)rac[k];
    long l = lg(rack);
    M = cgetg(n+1,t_MAT); vecM[k] = (long)M;
    for (j=1; j<=n; j++)
    {
      p2 = cgetg(l,t_COL); M[j] = (long)p2; 
      p3 = gsubst((GEN)bas1[j], vnf, (GEN)racnf[k]);
      for (i=1; i<l; i++) p2[i] = lsubst(p3, vpol, (GEN)rack[i]);
    }
    MC = gconj(gtrans(M)); vecMC[k] = (long)MC;
    if (k <= r1)
    {
      GEN sigk = (GEN)sig[k];
      long r1rel = itos((GEN)sigk[1]);
      long r2rel = itos((GEN)sigk[2]);
      for (j=r1rel+1; j<=r1rel+r2rel; j++) MC[j] = lmul2n((GEN)MC[j],1);
    }
    vecT2[k] = lmul(MC,M);
  }
  T=cgetg(n+1,t_MAT); z[4] = (long)T;
  bas1 = (GEN)bas[1];
  for (j=1; j<=n; j++)
  {
    p1 = cgetg(n+1,t_COL); T[j] = (long)p1;
    for (i=1; i<=n; i++)
      p1[i] = ltrace(gmodulcp(gmul((GEN)bas1[i],(GEN)bas1[j]),pol));
  }
  MD = cgetg(1,t_MAT); z[5] = (long)MD;
  TI = cgetg(1,t_MAT); z[6] = (long)TI;
  MDI= cgetg(1,t_MAT); z[7] = (long)MDI; return z;
}

static GEN
modulereltoabs(GEN nf, GEN rnfeq, GEN x)
{
  GEN oms = (GEN)x[1], ids = (GEN)x[2], T = (GEN)nf[1];
  GEN p1, M, basnf, cobasnf;
  long i,j, n = lg(oms)-1, m = degpol(T), degabs = n*m;

  M = cgetg(degabs+1,t_MAT);
  basnf = gsubst((GEN)nf[7], varn(T), (GEN)rnfeq[2]);
  /* removing denominators speeds up multiplication */
  basnf = primitive_part(basnf, &cobasnf);
  for (i=1; i<=n; i++)
  {
    GEN c,c0,c1, om = (GEN)oms[i], id = (GEN)ids[i];

    om = primitive_part(eltreltoabs(rnfeq, om), &c0);
    c0 = mul_content(c0, cobasnf);
    for (j=1; j<=m; j++)
    {
      p1 = primitive_part(gmul(basnf,(GEN)id[j]), &c1);
      p1 = lift_intern(gmul(om,p1));
      c = mul_content(c1, c0);
      if (c) p1 = gmul(c,p1);
      M[(i-1)*m+j] = (long)pol_to_vec(p1, degabs);
    }
  }
  return M;
}

GEN
rnfinitalg(GEN nf,GEN pol,long prec)
{
  pari_sp av = avma;
  long m,n,r1,r2,vnf,i,j,k,vpol,degabs;
  GEN RES,sig,rac,liftpol,delta,RAC,ro,bas,f2,rnfeq,M, p1,p2,p3;

  if (typ(pol)!=t_POL) err(notpoler,"rnfinitalg");
  nf=checknf(nf); n=degpol(pol); vpol=varn(pol);
  pol = fix_relative_pol(nf,pol,0);
  vnf = varn(nf[1]);

  if (vpol >= vnf)
    err(talker,"main variable must be of higher priority in rnfinitalg");
  RES = cgetg(12,t_VEC);
  RES[1] = (long)pol;
  m = degpol(nf[1]); degabs = n*m;
  nf_get_sign(nf, &r1, &r2);
  sig = cgetg(r1+r2+1,t_VEC); RES[2] = (long)sig;
  RAC = cgetg(r1+r2+1,t_VEC); RES[6] = (long)RAC;
  rac = (GEN)nf[6]; liftpol = lift(pol);
  for (j=1; j<=r1; j++)
  {
    long r1j = 0;
    ro = roots(gsubst(liftpol,vnf,(GEN)rac[j]), prec);
    while (r1j<n && gcmp0(gimag((GEN)ro[r1j+1]))) r1j++;
    p1 = cgetg(3,t_VEC);
    p1[1] = lstoi(r1j);
    p1[2] = lstoi((n-r1j)>>1);
    sig[j] = (long)p1;
    RAC[j] = (long)get_roots(ro, r1j, 0);
  }
  for (; j<=r1+r2; j++)
  {
    ro = roots(gsubst(liftpol,vnf,(GEN)rac[j]), prec);
    p1 = cgetg(3,t_VEC);
    p1[1] = zero;
    p1[2] = lstoi(n);
    sig[j] = (long)p1;
    RAC[j] = (long)ro;
  }

  p1 = rnfpseudobasis(nf,pol);
  delta = cgetg(3,t_VEC);
    delta[1] = p1[3];
    delta[2] = p1[4];
  RES[3] = (long)delta;
  p2 = matbasistoalg(nf,(GEN)p1[1]);
  bas = cgetg(3,t_VEC);
    bas[1] = (long)mat_to_vecpol(p2,vpol);
    bas[2] = (long)p1[2];
  RES[7] = (long)bas;
  RES[8] = linvmat(p2);

  f2 = idealdiv(nf, discsr(pol), (GEN)p1[3]);
  RES[4] = (long)idealsqrtn(nf, f2, gdeux, 1);
  RES[9] = lgetg(1,t_VEC); /* multiplication table: dummy */
  RES[10] = (long)nf;
  RES[5] = (long)rnfmakematrices(RES);
  if (DEBUGLEVEL>1) msgtimer("matrices");

  rnfeq = rnfequation2(nf,pol);
  M = modulereltoabs(nf, rnfeq, bas);
  if (DEBUGLEVEL>1) msgtimer("M");
  M = Q_remove_denom(M, &p3);
  if (p3) M = hnfmodid(M, p3); else M = idmat(degabs);
  for (j=degabs-1; j>0; j--)
    if (cmpis(gcoeff(M,j,j),2) > 0)
    {
      p1 = shifti(gcoeff(M,j,j),-1);
      for (k=j+1; k<=degabs; k++)
        if (cmpii(gcoeff(M,j,k),p1) > 0)
          for (i=1; i<=j; i++)
            coeff(M,i,k) = lsubii(gcoeff(M,i,k),gcoeff(M,i,j));
    }
  if (p3) M = gdiv(M,p3);
  if (DEBUGLEVEL>1) msgtimer("hnfmod");

  p1 = cgetg(6,t_VEC); RES[11] = (long)p1;
  for (i=1; i<=3; i++) p1[i] = rnfeq[i];
  p1[4] = (long)mat_to_vecpol(M,vpol);
  p1[5] = linvmat(M);
  return gerepilecopy(av, RES);
}

GEN
rnfbasistoalg(GEN rnf,GEN x)
{
  long tx=typ(x), lx=lg(x), i;
  pari_sp av=avma, tetpil;
  GEN p1,z,nf;

  checkrnf(rnf); nf=(GEN)rnf[10];
  switch(tx)
  {
    case t_VEC:
    case t_COL:
      p1 = cgetg(lx,t_COL);
      for (i=1; i<lx; i++) p1[i] = (long)_basistoalg(nf, (GEN)x[i]);
      p1 = gmul(gmael(rnf,7,1),p1); tetpil = avma;
      return gerepile(av,tetpil, gmodulcp(p1,(GEN)rnf[1]));

    case t_MAT:
      z = cgetg(lx,tx);
      for (i=1; i<lx; i++) z[i] = (long)rnfbasistoalg(rnf,(GEN)x[i]);
      return z;

    case t_POLMOD:
      return gcopy(x);

    default:
      z=cgetg(3,t_POLMOD); z[1]=lcopy((GEN)rnf[1]);
      z[2]=lmul(x,polun[varn(rnf[1])]); return z;
  }
}

/* assume x is a t_POLMOD */
GEN
lift_to_pol(GEN x)
{
  GEN y = (GEN)x[2];
  return (typ(y) != t_POL)? gtopoly(y,varn(x[1])): y;
}

GEN
rnfalgtobasis(GEN rnf,GEN x)
{
  long tx=typ(x), i, lx;
  pari_sp av=avma;
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
  long i, lx, tx = typ(x);
  GEN z;

  switch(tx)
  {
    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); z = cgetg(lx,tx);
      for (i=1; i<lx; i++) z[i] = (long)rnfelementreltoabs(rnf, (GEN)x[i]);
      return z;

    case t_POLMOD: x = lift_to_pol(x); /* fall through */
    case t_POL: return eltreltoabs(rnf, x);
    default: return gcopy(x);
  }
}

/* assume x,T,pol t_POL. T defines base field, pol defines rnf over T.
 * x an absolute element of the extension */
GEN
get_theta_abstorel(GEN T, GEN pol, GEN k)
{
  return gmodulcp(gadd(polx[varn(pol)],
                       gmul(k, gmodulcp(polx[varn(T)],T))), pol);
}
GEN
eltabstorel(GEN x, GEN T, GEN pol, GEN k)
{
  return poleval(x, get_theta_abstorel(T,pol,k));
}

GEN
rnfelementabstorel(GEN rnf,GEN x)
{
  long tx, i, lx;
  pari_sp av=avma;
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

/* x t_POLMOD or t_POL or vector of such objects */
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

/* x t_POLMOD or t_POL or vector of such objects */
GEN
rnfelementdown(GEN rnf,GEN x)
{
  pari_sp av = avma;
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
  pari_sp av = avma;
  GEN nf,bas,bas1,p1,z;

  x = rnfbasistoalg(rnf,x); nf = (GEN)rnf[10];
  bas = (GEN)rnf[7]; bas1 = (GEN)bas[1];
  p1 = rnfalgtobasis(rnf, gmul(x,gmodulcp(bas1,(GEN)rnf[1])));
  settyp(p1,t_MAT);

  z = cgetg(3,t_VEC);
  z[1] = (long)p1;
  z[2] = bas[2];
  return gerepileupto(av, nfhermite(nf,z));
}

static GEN
rnfid(long n, long m)
{
  return idmat_intern(n, gscalcol_i(gun,m), zerocol(m));
}

GEN
rnfidealhermite(GEN rnf,GEN x)
{
  long tx=typ(x), lx=lg(x), i, j, n, m;
  pari_sp av=avma, tetpil;
  GEN z,p1,p2,x1,x2,x1j,nf,bas;

  checkrnf(rnf);
  n = degpol(rnf[1]); nf = (GEN)rnf[10]; bas = (GEN)rnf[7];

  switch(tx)
  {
    case t_INT: case t_FRAC: case t_FRACN:
      m = degpol(nf[1]);
      z = cgetg(3,t_VEC);
      z[1] = (long)rnfid(n, m);
      z[2] = lmul(x, (GEN)bas[2]); return z;

    case t_POLMOD: case t_POL:
      p1 = rnfalgtobasis(rnf,x);
      return gerepileupto(av, rnfprincipaltohermite(rnf,p1));

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

static GEN
prodid(GEN nf, GEN I)
{
  long i, l = lg(I);
  GEN z;

  if (l == 1) return idmat(degpol(nf[1]));
  z = (GEN)I[1];
  for (i=2; i<l; i++) z = idealmul(nf, z, (GEN)I[i]);
  return z;
}

static GEN
prodidnorm(GEN I)
{
  long i, l = lg(I);
  GEN z;

  if (l == 1) return gun;
  z = dethnf((GEN)I[1]);
  for (i=2; i<l; i++) z = gmul(z, dethnf((GEN)I[i]));
  return z;
}

GEN
rnfidealnormrel(GEN rnf,GEN id)
{
  pari_sp av = avma;
  GEN z, t, nf;
  long n;

  checkrnf(rnf); nf = (GEN)rnf[10];
  n = degpol(rnf[1]);
  if (n == 1) { avma = av; return idmat(degpol(nf[1])); }

  id = rnfidealhermite(rnf,id);
  t = prodid(nf, gmael(rnf,7,2));
  z = prodid(nf, (GEN)id[2]);
  return gerepileupto(av, idealdiv(nf,z,t));
}

GEN
rnfidealnormabs(GEN rnf,GEN id)
{
  pari_sp av = avma;
  GEN z, t;
  long n;

  checkrnf(rnf);
  n = degpol(rnf[1]);
  if (n == 1) return gun;

  id = rnfidealhermite(rnf,id);
  z = prodidnorm((GEN)id[2]);
  t = prodidnorm(gmael(rnf,7,2));
  return gerepileupto(av, gdiv(z, t));
}

GEN
rnfidealreltoabs(GEN rnf,GEN x)
{
  long i, l;
  pari_sp av = avma;
  GEN nf,basinv,oms,M,p1,d;

  nf = (GEN)rnf[10];
  x = rnfidealhermite(rnf,x);
  oms = (GEN)x[1]; l = lg(oms); settyp(oms,t_VEC);
  for (i=1; i<l; i++)
    oms[i] = (long)lift( rnfbasistoalg(rnf, (GEN)oms[i]) );
  M = modulereltoabs(nf, (GEN)rnf[11], x);
  basinv = gmael(rnf,11,5);
  p1 = Q_remove_denom(gmul(basinv,M), &d);
  p1 = hnfmodid(p1, gmael(p1,1,1)); /* mod x \cap Z */
  if (d) p1 = gdiv(p1, d);
  return gerepileupto(av, p1);
}

GEN
rnfidealabstorel(GEN rnf,GEN x)
{
  long n, m, j;
  pari_sp av = avma;
  GEN nf,basabs,M,xj,p1,p2,id;

  checkrnf(rnf); nf = (GEN)rnf[10];
  n = degpol(rnf[1]);
  m = degpol(nf[1]);
  if (typ(x) != t_MAT || lg(x) != n*m+1 || lg(x[1]) != n*m+1)
    err(impl,"rnfidealabstorel for an ideal not in HNF");
  basabs = gmael(rnf,11,4);
  M = cgetg(n*m+1,t_MAT);
  for (j=1; j<=n*m; j++)
  {
    xj = gmul(basabs,(GEN)x[j]);
    xj = lift_intern(rnfelementabstorel(rnf,xj));
    M[j] = (long)pol_to_vec(xj, n);
  }
  M = gmul((GEN)rnf[8], M);
  p1 = cgetg(n*m+1,t_VEC); id = idmat(m);
  for (j=1; j<=n*m; j++) p1[j] = (long)id;
  p2 = cgetg(3,t_VEC);
  p2[1] = (long)M;
  p2[2] = (long)p1;
  return gerepileupto(av, nfhermite(nf,p2));
}

GEN
rnfidealdown(GEN rnf,GEN x)
{
  pari_sp av = avma;
  x = rnfidealhermite(rnf,x);
  return gerepilecopy(av,gmael(x,2,1));
}

/* lift ideal x to the relative extension, returns a Z-basis */
GEN
rnfidealup(GEN rnf,GEN x)
{
  pari_sp av = avma;
  long i, n, m;
  GEN nf,bas,bas2,p1,p2;

  checkrnf(rnf); nf = (GEN)rnf[10];
  n = degpol(rnf[1]);
  m = degpol((GEN)nf[1]);
  bas = (GEN)rnf[7]; bas2 = (GEN)bas[2];

  p2 = cgetg(3,t_VEC); p1 = cgetg(n+1,t_VEC);
  p2[1] = (long)rnfid(n, m);
  p2[2] = (long)p1;
  for (i=1; i<=n; i++) p1[i] = (long)idealmul(nf,x,(GEN)bas2[i]);
  return gerepileupto(av, rnfidealreltoabs(rnf,p2));
}

/* x a relative HNF ---> vector of 2 generators (relative polymods) */
GEN
rnfidealtwoelement(GEN rnf,GEN x)
{
  pari_sp av = avma;
  long j;
  GEN p1,p2,p3,res,polabs,nfabs,z;

  checkrnf(rnf);
  res=(GEN)rnf[11]; polabs=(GEN)res[1];
  nfabs = cgetg(10,t_VEC);
  nfabs[1] = (long)polabs;
  for (j=2; j<=9; j++) nfabs[j] = zero;
  nfabs[7] = (long)lift((GEN)res[4]);
  nfabs[8] = res[5];
  p1 = rnfidealreltoabs(rnf,x);
  p2 = ideal_two_elt(nfabs,p1);
  p3 = rnfelementabstorel(rnf,gmul((GEN)res[4],(GEN)p2[2]));
  z = cgetg(3,t_VEC);
  z[1] = lcopy((GEN)p2[1]);
  z[2] = (long)rnfalgtobasis(rnf,p3);
  return gerepileupto(av, z);
}

GEN
rnfidealmul(GEN rnf,GEN x,GEN y) /* x et y sous HNF relative uniquement */
{
  long i, j, n;
  pari_sp av = avma;
  GEN z,nf,x1,x2,p1,p2,p3,p4,res;

  z = rnfidealtwoelement(rnf,y);
  nf = (GEN)rnf[10]; n = degpol(rnf[1]);
  x = rnfidealhermite(rnf,x);
  x1 = gmodulcp(gmul(gmael(rnf,7,1), matbasistoalg(nf,(GEN)x[1])),(GEN) rnf[1]);
  x2 = (GEN)x[2];
  p1 = gmul((GEN)z[1],(GEN)x[1]);
  p2 = lift_intern(gmul(rnfbasistoalg(rnf,(GEN)z[2]),x1));
  p3 = cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++)
  {
    p4 = pol_to_vec((GEN)p2[j], n); p3[j] = (long)p4;
    for (i=1; i<=n; i++) p4[i] = (long)algtobasis(nf,(GEN)p4[i]);
  }
  res = cgetg(3,t_VEC);
  res[1] = (long)concatsp(p1,p3);
  res[2] = (long)concatsp(x2,x2);
  return gerepileupto(av, nfhermite(nf,res));
}
