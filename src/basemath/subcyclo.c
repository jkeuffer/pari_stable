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

/* Calcule les orbites d'un sous-groupe de Z/nZ donne par un
 * generateur ou d'un ensemble de generateur donne par un vecteur. 
 */
GEN
subgroupcoset(long n, GEN v)
{
  ulong lbot;
  gpmem_t ltop = avma;
  int     i, j, k = 1, l, m, o, p, flag;
  GEN     bit, cycle, cy;
  cycle = cgetg(n, t_VEC);
  bit = cgetg(n, t_VECSMALL);
  for (i = 1; i < n; i++)
    if (cgcd(i,n)==1)
      bit[i] = 0;
    else
    {
      bit[i] = -1;
      k++;
    }
  for (l = 1; k < n;)
  {
    for (j = 1; bit[j]; j++);
    cy = cgetg(n, t_VECSMALL);
    m = 1;
    cy[m++] = j;
    bit[j] = 1;
    k++;
    do
    {
      flag = 0;
      for (o = 1; o < lg(v); o++)
      {
	for (p = 1; p < m; p++)	/* m varie! */
	{
	  j = mulssmod(v[o],cy[p],n);
	  if (!bit[j])
	  {
	    flag = 1;
	    bit[j] = 1;
	    k++;
	    cy[m++] = j;
	  }
	}
      }
    }
    while (flag);
    setlg(cy, m);
    cycle[l++] = (long) cy;
  }
  setlg(cycle, l);
  lbot = avma;
  cycle = gcopy(cycle);
  return gerepile(ltop, lbot, cycle);
}
/* Calcule les elements d'un sous-groupe H de Z/nZ donne par un
 * generateur ou d'un ensemble de generateur donne par un vecteur (v). 
 *
 * cy liste des elements   VECSMALL de longueur au moins card H.
 * bit bitmap des elements VECSMALL de longueur au moins n.
 * retourne le nombre d'elements+1
 */
long
sousgroupeelem(long n, GEN v, GEN cy, GEN bit)
{
  int     j, m, o, p, flag;
  for(j=1;j<n;j++) 
    bit[j]=0;
  m = 1;
  bit[m] = 1;
  cy[m++] = 1;
  do
  {
    flag = 0;
    for (o = 1; o < lg(v); o++)
    {
      for (p = 1; p < m; p++)	/* m varie! */
      {
	j = mulssmod(v[o],cy[p],n);
	if (!bit[j])
	{
	  flag = 1;
	  bit[j] = 1;
	  cy[m++] = j;
	}
      }
    }
  }
  while (flag);
  return m;
}
/* n,v comme precedemment.
 * Calcule le conducteur et retourne le nouveau groupe de congruence dans V
 * V doit etre un t_VECSMALL de taille n+1 au moins.
 */
long znconductor(long n, GEN v, GEN V)
{
  ulong ltop;
  int i,j;
  long m;
  GEN F,W;
  W = cgetg(n, t_VECSMALL);
  ltop=avma;
  m = sousgroupeelem(n,v,V,W);
  setlg(V,m);
  if (DEBUGLEVEL>=6)
    fprintferr("SubCyclo:elements:%Z\n",V);
  F = factor(stoi(n));  
  for(i=lg((GEN)F[1])-1;i>0;i--)
  {
    long p,e,q;
    p=itos(gcoeff(F,i,1));
    e=itos(gcoeff(F,i,2));
    if (DEBUGLEVEL>=4)
      fprintferr("SubCyclo:testing %ld^%ld\n",p,e);
    while (e>=1)
    {
      int z = 1;
      q=n/p;
      for(j=1;j<p;j++)
      {
	z += q;
	if (!W[z] && z%p) break;
      }
      if (j<p)
      {
	if (DEBUGLEVEL>=4)
	  fprintferr("SubCyclo:%ld not found\n",z);
	break;
      }
      e--;
      n=q;
      if (DEBUGLEVEL>=4)
	fprintferr("SubCyclo:new conductor:%ld\n",n);
      m=sousgroupeelem(n,v,V,W);
      setlg(V,m); 
      if (DEBUGLEVEL>=6)
	fprintferr("SubCyclo:elements:%Z\n",V);
    }
  } 
  if (DEBUGLEVEL>=6)
    fprintferr("SubCyclo:conductor:%ld\n",n);
  avma=ltop;
  return n;
}

static GEN gscycloconductor(GEN g, long n, long flag)
{
  if (flag==2)
  {
    GEN V=cgetg(3,t_VEC);
    V[1]=lcopy(g);
    V[2]=lstoi(n);
    return V;
  }
  return g;
}
static GEN 
lift_check_modulus(GEN H, GEN n)
{
  long t=typ(H), l=lg(H);
  long i;
  GEN V;
  switch(t)
  {
    case t_INTMOD:
      if (cmpii(n,(GEN)H[1]))
	err(talker,"wrong modulus in galoissubcyclo");
      H = (GEN)H[2];
    case t_INT:
      if (!is_pm1(mppgcd(H,n)))
	err(talker,"generators must be prime to conductor in galoissubcyclo");
      return modii(H,n);
    case t_VEC: case t_COL:
      V=cgetg(l,t);
      for(i=1;i<l;i++)
	V[i] = (long)lift_check_modulus((GEN)H[i],n);
      return V;
    case t_VECSMALL:
      return H;
  }
  err(talker,"wrong type in galoissubcyclo");
  return NULL;/*not reached*/
}

GEN subcyclo_cyclic(long n, long d, long m ,long z, long g, GEN powz, GEN le)
{
  GEN V=cgetg(d+1,t_VEC);
  long base=1;
  long i,k;
  long lle=lg(le)*2+1;/*Assume dvmdii use lx+ly space*/
  gpmem_t ltop=avma;
  avma=ltop;
  for (i=1;i<=d;i++,base=mulssmod(base,z,n))
  {
    gpmem_t ltop=avma;
    long ex=base;
    GEN s=gzero;
    new_chunk(lle);
    for (k=0; k<m; k++, ex = mulssmod(ex,g,n))
      s=addii(s,(GEN)powz[ex]);
    avma=ltop;
    V[i]=lmodii(s,le);
  }
  return V;
}

GEN subcyclo_orbits(GEN O, GEN powz, GEN le)
{
  long d=lg(O)-1;
  long m=lg(O[1])-1;
  GEN V=cgetg(d+1,t_VEC);
  long i,j;
  long lle=lg(le)*2+1;/*Assume dvmdii use lx+ly space*/
  for(i=1;i<=d;i++)
  {
    GEN s=gzero;
    gpmem_t av=avma;
    new_chunk(lle);
    for(j=1;j<=m;j++)
      s=addii(s,(GEN)powz[mael(O,i,j)]);
    avma=av;
    V[i]=(long)modii(s,le);
  }
  return V;
}

/* n must be the exact conductor of the extension.
 * d is the degree of the extension.
 * if g!=0, this is the generator of the galois group and O is not used
 * if g==0, O must be the orbit of the Galois group.
 */
GEN 
subcyclo_main(long n, long d, long o, long g, long gd, GEN O, long v)
{
  gpmem_t ltop=avma, av;
  GEN l,borne,le,powz,z,V;
  long lle;
  long i;
  long e,val;
  GEN R;
  if ( v==-1 ) v=0;
  V = cgetg(n, t_VECSMALL);
  if (DEBUGLEVEL >= 1)
    timer2();
  l=stoi(n+1);e=1;
  while(!isprime(l)) 
  { 
    l=addis(l,n);
    e++;
  }
  if (DEBUGLEVEL >= 4)
    fprintferr("Subcyclo: prime l=%Z\n",l);
  av=avma;
  /*Borne utilise': 
    Vecmax(Vec((x+o)^u)=max{binome(u,i)*o^i ;1<=i<=u} 
  */
  i=d-(1+d)/(1+o);
  borne=mulii(binome(stoi(d),i),gpowgs(stoi(o),i));
  if (DEBUGLEVEL >= 4)
    fprintferr("Subcyclo: borne=%Z\n",borne);
  val=logint(shifti(borne,1),l,NULL);
  avma=av;
  if (DEBUGLEVEL >= 4)
    fprintferr("Subcyclo: val=%ld\n",val);
  le=gpowgs(l,val);
  z=lift(gpowgs(gener(l),e));
  z=padicsqrtnlift(gun,stoi(n),z,l,val);
  if (DEBUGLEVEL >= 1)
    msgtimer("padicsqrtnlift.");
  powz = cgetg(n,t_VEC); powz[1] = (long)z;
  lle=lg(le)*3;/*Assume dvmdii use lx+ly space*/
  for (i=2; i<n; i++)
  {
    gpmem_t av=avma;
    GEN p1;
    new_chunk(lle);
    p1 = mulii(z,(GEN)powz[i-1]);
    avma=av;
    powz[i] = lmodii(p1,le);
  }
  if (DEBUGLEVEL >= 1)
    msgtimer("computing roots.");  
  if (g)
    R=subcyclo_cyclic(n,d,o,g,gd,powz,le);
  else
    R=subcyclo_orbits(O,powz,le);
  if (DEBUGLEVEL >= 1)
    msgtimer("computing new roots."); 
  R=FpV_roots_to_pol(R,le,v);
  if (DEBUGLEVEL >= 1)
    msgtimer("computing products."); 
  R=FpX_center(R,le);
  return gerepileupto(ltop,R);
}


GEN 
galoissubcyclo(long n, GEN H, GEN Z, long v, long flag)
{
  gpmem_t ltop=avma;
  GEN V;
  long i;
  long d,o;
  GEN O,g;
  if (flag<0 || flag>2) err(flagerr,"galoisubcyclo");
  if ( v==-1 ) v=0;
  if ( n<1 ) err(arither2);
  if ( n>=VERYBIGINT) 
    err(impl,"galoissubcyclo for huge conductor");    
  if ( typ(H)==t_MAT )
  {
    GEN zn2, zn3, gen, ord;
    if (lg(H) == 1 || lg(H) != lg(H[1]))
      err(talker,"not a HNF matrix in galoissubcyclo");
    if (!Z)
      Z=znstar(stoi(n));
    else if (typ(Z)!=t_VEC || lg(Z)!=4) 
      err(talker,"Optionnal parameter must be as output by znstar in galoissubcyclo");
    zn2 = gtovecsmall((GEN)Z[2]);
    zn3 = lift((GEN)Z[3]);
    if ( lg(zn2) != lg(H) || lg(zn3) != lg(H))
      err(talker,"Matrix of wrong dimensions in galoissubcyclo");
    gen = cgetg(lg(zn3), t_VECSMALL);
    ord = cgetg(lg(zn3), t_VECSMALL);
    hnftogeneratorslist(n,zn2,zn3,H,gen,ord);
    H=gen;
  }
  else
  {
    H=lift_check_modulus(H,stoi(n));
    H=gtovecsmall(H);
    for (i=1;i<lg(H);i++)
      if (H[i]<0)
	H[i]=mulssmod(-H[i],n-1,n);
    /*Should check components are prime to n, but it is costly*/
  }
  V = cgetg(n, t_VECSMALL);
  if (DEBUGLEVEL >= 1)
    timer2();
  n = znconductor(n,H,V);
  if (flag==1)  {avma=ltop;return stoi(n);}
  if (DEBUGLEVEL >= 1)
    msgtimer("znconductor.");
  H = V;
  O = subgroupcoset(n,H);
  if (DEBUGLEVEL >= 1)
    msgtimer("subgroupcoset.");
  if (DEBUGLEVEL >= 6)
    fprintferr("Subcyclo: orbit=%Z\n",O);
  if (lg(O)==1 || lg(O[1])==2)
  {
    avma=ltop;
    return gscycloconductor(cyclo(n,v),n,flag);
  }
  d=lg(O)-1;o=lg(O[1])-1;
  if (DEBUGLEVEL >= 4)
    fprintferr("Subcyclo: %ld orbits with %ld elements each\n",d,o);
  g=subcyclo_main(n,d,o,0,0,O,v);
  return gerepileupto(ltop,gscycloconductor(g,n,flag));
}

GEN
subcyclo(long n, long d, long v)
{
  gpmem_t av=avma;
  long q,p,al,r,g,gd;
  GEN fa,G;
  if (v<0) v = 0;
  if (d==1) return polx[v];
  if (d<=0 || n<=0) err(typeer,"subcyclo");
  if ((n & 3) == 2) n >>= 1;
  if (n == 1 || d >= n) err(talker,"degree does not divide phi(n) in subcyclo");
  fa = decomp(stoi(n));
  p = itos(gmael(fa,1,1));
  al= itos(gmael(fa,2,1));
  if (lg((GEN)fa[1]) > 2 || (p==2 && al>2))
    err(talker,"non-cyclic case in polsubcyclo: use galoissubcyclo instead");
  avma=av;
  r = cgcd(d,n); /* = p^(v_p(d))*/
  n = r*p;
  q = n-r; /* = phi(n) */
  if (q == d) return cyclo(n,v);
  if (q % d) err(talker,"degree does not divide phi(n) in subcyclo");
  q /= d;
  if (p==2)
  {
    GEN pol = powgi(polx[v],gdeux); pol[2]=un; /* replace gzero */
    return pol; /* = x^2 + 1 */
  }
  G=gener(stoi(n));
  g=itos((GEN)G[2]);
  gd=itos((GEN)gpowgs(G,d)[2]);
  avma=av;
  return subcyclo_main(n,d,q,g,gd,NULL,v);
}

