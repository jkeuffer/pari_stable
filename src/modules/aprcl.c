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
/*                    THE APRCL PRIMALITY TEST                     */
/*                                                                 */
/*******************************************************************/
#include "pari.h"

static ulong lglobfa,ctglob,sgtaut,sgt6,sgtjac,kglob,NBITSN,ltaball;
static GEN globfa,tabfaq,tabj,tabj2,tabj3,sgt,ctsgt;
static GEN tabaall,tabtall,tabefin,tabcyc,tabE,tabTH,tabeta;

/* contains [t,floor(200*log(e(t))/log(10))] for e(t) < 10^529, good for
 N<10^1058 */

static ulong vet[61][2] =
{{6,540},{12,963},{24,1023},{48,1330},{36,1628},{60,1967},{120,2349},{180,3083},{240,3132},{504,3270},{360,3838},{420,4115},{720,4621},{840,4987},{1440,5079},{1260,6212},{1680,6686},{2520,8137},{3360,8415},{5040,10437},{13860,11643},{10080,12826},{13860,11643},{10080,12826},{16380,13369},{21840,13540},{18480,15060},{27720,15934},{32760,17695},{36960,18816},{55440,21338},{65520,23179},{98280,23484},{110880,27465},{131040,30380},{131040,30380},{166320,31369},{196560,33866},{262080,34530},{277200,36195},{360360,37095},{480480,38179},{332640,41396},{554400,43301},{720720,47483},{665280,47742},{831600,50202},{1113840,52502},{1441440,60245},{1663200,63112},{2227680,65395},{2162160,69895},{2827440,71567},{3326400,75708},{3603600,79377},{6126120,82703},{4324320,91180},{6683040,93978},{7207200,98840},{11138400,99282},{8648640,105811}};

static int tabfaux[12]={0,1,1,0,1,0,1,0,0,0,1,0};

/* programmes de puissances de polmods mod N, fenetre flexible */

/* la donnee est un polmod, la sortie est un pol entiers. */

static GEN
makepoldeg1(GEN c, GEN d)
{
  GEN res;
  if (signe(c))
  {
    res=cgetg(4,t_POL); res[1]=evalsigne(1)|evallgef(4);
    res[2]=(long)d; res[3]=(long)c; return res;
  }
  if (signe(d))
  {
    res=cgetg(3,t_POL); res[1]=evalsigne(1)|evallgef(3);
    res[2]=(long)d; return res;
  }
  else
  {
    res=cgetg(2,t_POL); res[1]=evalsigne(0)|evallgef(2);
    return res;
  }
}

static GEN
sqrmod3(GEN pol, GEN N)
{
  GEN a,b,bma,c,d,p1;
  long lv=lgef(pol);

  if (lv==3) 
  {
    p1 = cgetg(3,t_POL);
    p1[2] = (long)modii(sqri((GEN)pol[2]),N);
    p1[1] = pol[1]; return p1;
  }
  if (lv==2) return pol;
  a = (GEN)pol[3];
  b = (GEN)pol[2];
  bma = subii(b,a);
  c = modii(mulii(a,addii(b,bma)), N);
  d = modii(mulii(bma,addii(a,b)), N);
  return makepoldeg1(c,d);
}

static GEN
powpolmod3(GEN N, GEN jac)
{
  GEN pc,tabt,taba,res,pol2,vz;
  int lv,tf,efin,f,i;
  
  pc = (GEN)tabcyc[3];
  taba = (GEN)tabaall[3];
  tabt = (GEN)tabtall[3];
  efin = tabefin[3];
  lv = (1<<(kglob-1));
  vz = cgetg(lv+1,t_VEC);
  res = lift(jac); vz[1] = (long)res;
  pol2 = FpX_red(sqrmod3(res,N),N);
  for (i=2; i<=lv; i++)
    vz[i] = (long)FpX_red(gmod(gmul((GEN)vz[i-1],pol2),pc),N);
  for (f=efin; f>=1; f--)
  {
    res = f==efin ? (GEN)vz[taba[f]]
                  : FpX_red(gmod(gmul((GEN)vz[taba[f]],res),pc),N);
    tf = tabt[f];
    for (i=1; i<=tf; i++) res = FpX_red(sqrmod3(res,N),N); 
  }
  return res;
}

static GEN
sqrmod4(GEN pol, GEN N)
{
  GEN a,b,c,d,p1;
  long lv=lgef(pol);

  if (lv==2) return pol;
  if (lv==3)
  {
    p1 = cgetg(3,t_POL);
    p1[2] = (long)modii(sqri((GEN)pol[2]),N);
    p1[1] = pol[1]; return p1;
  }
  a = (GEN)pol[3];
  b = (GEN)pol[2];
  c = modii(mulii(a,addii(b,b)),N);
  d = modii(mulii(subii(b,a),addii(b,a)),N);
  return makepoldeg1(c,d);
}

static GEN
powpolmod4(GEN N, GEN jac)
{
  GEN pc,tabt,taba,res,pol2,vz;
  int lv,tf,efin,f,i;
  
  pc = (GEN)tabcyc[4];
  taba = (GEN)tabaall[4];
  tabt = (GEN)tabtall[4];
  efin = tabefin[4];
  lv = (1<<(kglob-1));
  vz = cgetg(lv+1,t_VEC);
  res = lift(jac); vz[1] = (long)res;
  pol2 = FpX_red(sqrmod4(res,N),N);
  for (i=2; i<=lv; i++)
    vz[i] = (long)FpX_red(gmod(gmul((GEN)vz[i-1],pol2),pc),N);
  for (f=efin; f>=1; f--)
  {
    res = f==efin ? (GEN)vz[taba[f]]
                  : FpX_red(gmod(gmul((GEN)vz[taba[f]],res),pc),N);
    tf = tabt[f];
    for (i=1; i<=tf; i++) res = FpX_red(sqrmod4(res,N),N); 
  }
  return res;
}

GEN
powpolmodspec(GEN N, int pk, GEN jac)
{
  GEN pc,pc2,tabt,taba,res,pol2,vz;
  int lv,tf,efin,f,i;
  
  pc = (GEN)tabcyc[pk];
  pc2 = cgetg(pk+3,t_POL); pc2[1] = evalsigne(1)|evallgef(pk+3);
  pc2[2] = lstoi(-1);
  pc2[pk+2] = un;
  for (i=3; i<=pk+1; i++) pc2[i] = zero;
  taba = (GEN)tabaall[pk];
  tabt = (GEN)tabtall[pk];
  efin = tabefin[pk];
  lv = (1<<(kglob-1));
  vz = cgetg(lv+1,t_VEC);
  res = lift(jac); vz[1] = (long)res;
  pol2 = FpX_red(gmod(gmod(gsqr(res),pc2),pc),N);
  for (i=2; i<=lv; i++)
    vz[i] = (long)FpX_red(gmod(gmod(gmul((GEN)vz[i-1],pol2),pc2),pc),N);
  for (f=efin; f>=1; f--)
  {
    res = f==efin? (GEN)vz[taba[f]]
                 : FpX_red(gmod(gmod(gmul((GEN)vz[taba[f]],res),pc2),pc),N);
    tf = tabt[f];
    for (i=1; i<=tf; i++) res = FpX_red(gmod(gmod(gsqr(res),pc2),pc),N); 
  }
  return res;
}

GEN
powpolmod(GEN N, int k, int pk, GEN jac)
{
  GEN pc,tabt,taba,res,pol2,vz;
  int lv,tf,efin,f,i;
  
  if (pk==3) return powpolmod3(N,jac);
  if (pk==4) return powpolmod4(N,jac);
  if (k==1 && pk>=5) return powpolmodspec(N,pk,jac);
  pc=(GEN)tabcyc[pk];
  taba=(GEN)tabaall[pk]; tabt=(GEN)tabtall[pk]; efin=tabefin[pk];
  lv=(1<<(kglob-1)); vz=cgetg(lv+1,t_VEC);
  res=lift(jac); vz[1]=(long)res;
  pol2=FpX_red(gmod(gsqr(res),pc),N);
  for (i=2; i<=lv; i++)
    vz[i]=(long)FpX_red(gmod(gmul((GEN)vz[i-1],pol2),pc),N);
  for (f=efin; f>=1; f--)
  {
    res=f==efin ? (GEN)vz[taba[f]] : FpX_red(gmod(gmul((GEN)vz[taba[f]],res),pc),N);
    tf=tabt[f];
    for (i=1; i<=tf; i++) res=FpX_red(gmod(gsqr(res),pc),N); 
  }
  return res;
}

static GEN
e(ulong t)
{
  GEN fa,fapr,faex,s,dp1,tgen;
  ulong nbd,m,k,ex,d;
  int lfa,i,j;

  tgen=stoi(t);
  fa=decomp(tgen); fapr=(GEN)fa[1]; faex=(GEN)fa[2]; lfa=lg(fapr);
  nbd=1; for (i=1; i<lfa; i++) nbd*=itos((GEN)faex[i])+1;
  s=stoi(2);
  for (k=0; k<nbd; k++)
  {
    m=k; d=1;
    for (j=1; j<lfa; j++)
    {
      ex=itos((GEN)faex[j])+1;
      d*=itos(gpuigs((GEN)fapr[j],m%ex));
      m/=ex;
    }
    dp1=stoi(d+1);
    if (isprime(dp1)) s=mulii(s,gpuigs(dp1,ggval(stoi(t),dp1)+1));
  }
  return s;
}

static ulong
compt(GEN N)
{
  int lvet,i;
  ulong lim,Bint,t;
  GEN B,LN;

  Bint=itos(gceil(mulsr(100,divrr(glog(N,DEFAULTPREC),
                                  glog(stoi(10),DEFAULTPREC)))));
  lvet=61;
  for (i=0; i<lvet; i++) if (vet[i][1]>Bint) return vet[i][0];
  LN=glog(N,5); B=racine(N); lim=0xffffffff;
  for (t=vet[lvet-1][0]+840; t<=lim; t+=840) if (cmpii(e(t),B)>0) return t;
  err(talker,"no t<2^32 found in compt");
  return 0;
}

/* x doit etre un Vecsmall non nul */
GEN
smallpolrev(GEN x)
{
  long lx,i,j;
  GEN y;
  
  lx=lg(x);
  while (lx-- && x[lx]==0);
  i=lx+2; y=cgetg(i,t_POL);
  y[1]=evallgef(i) | evalsigne(1);
  for (j=2; j<i; j++) y[j]=lstoi(x[j-1]);
  return y;
}

/* tabdl[i] contient le log discret de i+1 */
static GEN
computetabdl(ulong q)
{
  GEN v;
  ulong h,qm3s2,qm1s2,qm1,a,i;

  v=cgetg(q-1,t_VECSMALL);
  h=itos(lift(ggener(stoi(q))));
  qm3s2=(q-3)>>1; qm1s2=qm3s2+1; qm1=q-1;
  v[q-2]=qm1s2; a=1;
  for (i=1; i<=qm3s2; i++)
  {
    a=itos(modis(mulss(h,a),q));v[a-1]=i;v[qm1-a]=i+qm1s2;
  }
  return v;
}

static void
calcjac(GEN et)
{
  ulong q,ltabg,qm3s2,x;
  int lfaq,p,k,ii,i,j,pk;
  GEN ze8,tabf,tabg,faq,faqpr,faqex,ze,vpk,v8;

  globfa=(GEN)decomp(shifti(et,-vali(et)))[1];
  lglobfa=lg(globfa);
  tabfaq=cgetg(lglobfa,t_VEC);
  tabj=cgetg(lglobfa,t_VEC);
  tabj2=cgetg(lglobfa,t_VEC);
  tabj3=cgetg(lglobfa,t_VEC);
  ze8=cgetg(7,t_POL);
  ze8[1]=evalsigne(1)|evallgef(7);
  ze8[2]=ze8[6]=un; ze8[3]=ze8[4]=ze8[5]=zero;
  v8=cgetg(9,t_VECSMALL);
  for (i=1; i<lglobfa; i++)
  {
    q=itos((GEN)globfa[i]);
    tabf=computetabdl(q); qm3s2=(q-3)>>1;
    faq=decomp(stoi(q-1)); tabfaq[i]=(long)faq;
    faqpr=(GEN)faq[1]; faqex=(GEN)faq[2]; lfaq=lg(faqpr);
    ltabg=cmpis((GEN)faqex[1],3)>=0 ? q-2 : qm3s2;
    tabg=cgetg(ltabg+1,t_VECSMALL);
    for (x=1; x<=ltabg; x++) tabg[x]=tabf[x]+tabf[q-x-1];
    tabj[i]=lgetg(lfaq,t_VEC);
    for (j=1; j<lfaq; j++)
    {
      p=itos((GEN)faqpr[j]); k=itos((GEN)faqex[j]);
      pk=p; for (ii=2; ii<=k; ii++) pk*=p;
      vpk=cgetg(pk+1,t_VECSMALL); for (ii=1; ii<=pk; ii++) vpk[ii]=0;
      ze=(GEN)tabcyc[pk];
      if (p>=3 || k>=2)
      {
	for (x=1; x<=qm3s2; x++) vpk[tabg[x]%pk+1]++;
	for (x=1; x<=pk; x++) vpk[x]<<=1;
	vpk[(2*tabf[qm3s2+1])%pk+1]++;
	((GEN)tabj[i])[j]=lmod(smallpolrev(vpk),ze);
      }
      if (p==2 && k>=3)
      {
	for (x=1; x<=8; x++) v8[x]=0;
	for (x=1; x<=ltabg; x++) tabg[x]+=tabf[x];
	for (x=1; x<=q-2; x++) v8[((tabf[x]+tabg[x])&7)+1]++;
	tabj2[i]=(long)gmod(gsubst(gsqr(gmod(smallpolrev(v8),ze8)),0,gpuigs(polx[0],pk>>3)),ze);
	for (x=1; x<=pk; x++) vpk[x]=0;
	for (x=1; x<=q-2; x++) vpk[tabg[x]%pk+1]++;
	tabj3[i]=(long)gmod(gmul((GEN)((GEN)tabj[i])[1],gmod(smallpolrev(vpk),ze)),ze);
      }
    }
  }
}

static void
inittabs()
{
  int lv,i;
  
  lv=ltaball+1;
  tabaall=cgetg(lv,t_VECSMALL); tabtall=cgetg(lv,t_VECSMALL);
  tabefin=cgetg(lv,t_VECSMALL); tabcyc=cgetg(lv,t_VEC);
  tabE=cgetg(lv,t_VEC); tabTH=cgetg(lv,t_VEC); tabeta=cgetg(lv,t_VEC);
  sgt=cgetg(lv,t_VECSMALL); ctsgt=cgetg(lv,t_VECSMALL);
  for (i=1; i<lv; i++) sgt[i]=ctsgt[i]=0;
}

static void
filltabs(GEN N, int p, int k, ulong ltab)
{
  int pk,efin,ii,i,j,LE=0;
  ulong s,mask=(1<<kglob)-1,ee,lp1;
  GEN tabt,taba,m,E=gzero,p1,p2;
  
  pk=p; for (ii=2; ii<=k; ii++) pk*=p;
  tabcyc[pk]=(long)cyclo(pk,0);
  p1=cgetg(pk+1,t_VEC);
  for (i=1; i<=pk; i++) p1[i]=(long)gmod(gpuigs(polx[0],i-1),(GEN)tabcyc[pk]);
  tabeta[pk]=lmul(gmodulcp(gun,N),p1);
  if (p>2)
  {
    LE=pk-pk/p+1; E=cgetg(LE,t_VECSMALL);
    for(i=1,j=0; i<pk; i++) if (i%p) E[++j]=i;
  }
  else
  {
    if (k>=3)
    {
      LE=(pk>>2)+1; E=cgetg(LE,t_VECSMALL);
      for(i=1,j=0; i<pk; i++) if ((i%8)==1 || (i%8)==3) E[++j]=i;
    }
  }
  if (p>2 || k>=3)
  {
    tabE[pk]=(long)E;
    p1=cgetg(LE,t_VEC);
    for (i=1; i<LE; i++)
    {
      p2=cgetg(3,t_VECSMALL); p2[1]=p2[2]=E[i];
      p1[i]=(long)p2;
    }
    tabTH[pk]=(long)p1;
  }
  tabt=cgetg(ltab+1,t_VECSMALL); taba=cgetg(ltab+1,t_VECSMALL);
  m=divis(N,pk);
  s=vali(m); tabt[1]=s; efin=ltab+1;
  for (ee=1; ee<=ltab; ee++)
  {
    p1=shifti(m,-s); lp1=lgefint(p1);
    taba[ee]=lp1==2 ? 0 : (((p1[lp1-1])&mask)+1)>>1;
    m=shifti(m,-(s+kglob));
    if (!signe(m)) {efin=ee;break;}
    s=vali(m); tabt[ee+1]=s+kglob;
  }
  if (efin>ltab) err(talker,"bug in filltabs");
  tabaall[pk]=(long)taba; tabtall[pk]=(long)tabt; tabefin[pk]=efin;
}

static GEN
extend(GEN v, int lvz)
{
  long lv=lg(v),i,tv=typ(v),ltot;
  GEN w;

  ltot=lv+lvz; w=cgetg(ltot,tv);
  if (typ(v)==t_VEC)
  {
    for (i=1; i<lv; i++) w[i]=lcopy((GEN)v[i]); for (; i<ltot; i++) w[i]=zero;
  }
  else
  {
    for (i=1; i<lv; i++) w[i]=v[i]; for (; i<ltot; i++) w[i]=0;
  }
  return w;
}

static void
extendtabs(GEN N, int p, int k)
{
  int pk,ii,lvz;
  ulong ltab;
  
  pk=p; for (ii=2; ii<=k; ii++) pk*=p;
  ltab=(NBITSN/kglob)+2; 
  if (pk<=ltaball)
  {
    if (tabcyc[pk]==0) filltabs(N,p,k,ltab);
    return;
  }
  lvz=pk-ltaball;
  tabaall=extend(tabaall,lvz); tabtall=extend(tabtall,lvz);
  tabefin=extend(tabefin,lvz); tabcyc=extend(tabcyc,lvz);
  tabE=extend(tabE,lvz); tabTH=extend(tabTH,lvz); tabeta=extend(tabeta,lvz);
  sgt=extend(sgt,lvz); ctsgt=extend(ctsgt,lvz);
  ltaball=pk;
  filltabs(N,p,k,ltab);
}

static GEN
calcglobs(GEN N, ulong t)
{
  GEN fat,fapr,faex;
  int lfa,pk,p,ex,i,k;
  ulong ltab;

  NBITSN=((lgefint(N)-2)<<TWOPOTBITS_IN_LONG)-1;
  while (bittest(N,NBITSN)==0) NBITSN--;
  NBITSN++;
  kglob=3; while (((kglob+1)*(kglob+2)<<(kglob-1))<NBITSN) kglob++;
  ltab=(NBITSN/kglob)+2; 
  fat=decomp(stoi(t)); fapr=(GEN)fat[1]; faex=(GEN)fat[2]; lfa=lg(fapr);
  ltaball=1;
  for (i=1; i<lfa; i++)
  {
    pk=itos(gpuigs((GEN)fapr[i],itos((GEN)faex[i])));
    if (pk>ltaball) ltaball=pk;
  }
  inittabs();
  for (i=1; i<lfa; i++)
  {
    p=itos((GEN)fapr[i]); ex=itos((GEN)faex[i]);
    for (k=1; k<=ex; k++) filltabs(N,p,k,ltab);
  }
  return fapr;
}

/* Calculer sig_a^{-1}(z) pour z dans Q(ze) et sig_a: ze -> ze^a */
static GEN
aut(int pk, GEN z,int x)
{
  int i;
  GEN v;

  v=cgetg(pk+1,t_VEC);
  for (i=1; i<=pk; i++) v[i]=(long)polcoeff0(z,(x*(i-1))%pk,0);
  return gmodulcp(gtopolyrev(v,0),(GEN)tabcyc[pk]);
}

/* calculer z^v pour v dans Z[G] represente par des couples [sig_x^{-1},y] */
static GEN
autvec(int pk, GEN z, GEN v)
{
  int i,lv=lg(v);
  GEN s;
  
  s=gun;
  for (i=1; i<lv; i++)
    s=gmul(s,gpuigs(aut(pk,z,((GEN)v[i])[1]),((GEN)v[i])[2]));
  return s;
}

static int
step4a(GEN N, int p, int k, GEN jpq)
{
  int pk,i,r,ind,LE,ii;
  GEN E,AL,p1,s1,s2,s3,etats;

  pk=p; for (ii=2; ii<=k; ii++) pk*=p;
  r=itos(modis(N,pk));
  E=(GEN)tabE[pk]; LE=lg(E);
  AL=cgetg(LE,t_VEC);
  for (i=1; i<LE; i++)
  {
    p1=cgetg(3,t_VECSMALL); p1[1]=E[i];
    p1[2]=(r*E[i])/pk;
    AL[i]=(long)p1;
  }
  if (DEBUGLEVEL) timer();
  s1=autvec(pk,jpq,(GEN)tabTH[pk]);
  if (DEBUGLEVEL) sgtaut+=timer();
  s2=powpolmod(N,k,pk,s1);
  if (DEBUGLEVEL) {sgt[pk]+=timer();ctsgt[pk]++;};
  s3=autvec(pk,jpq,AL);
  if (DEBUGLEVEL) sgtaut+=timer();
  s3=FpX_red(gmod(gmul(lift(s3),s2),(GEN)tabcyc[pk]),N);
  if (DEBUGLEVEL) sgt[pk]+=timer();
  etats=(GEN)tabeta[pk]; ind=pk;
  for (i=1; i<=pk; i++)
    if (gegal(s3,(GEN)etats[i])) {ind=i-1;break;}
  if (ind==pk) return -1;
  return (ind%p)!=0;
}

/* p=2, k>=3 */

static int
step4b(GEN N, ulong q, int k, GEN j2q, GEN j3q)
{
  int pk,r,ind,i,LE;
  GEN E,AL,p1,s1,s2,s3,etats;
  
  pk=1<<k;
  r=itos(modis(N,pk));
  E=(GEN)tabE[pk]; LE=lg(E);
  AL=cgetg(LE,t_VEC);
  for (i=1; i<LE; i++)
  {
    p1=cgetg(3,t_VECSMALL); p1[1]=E[i];
    p1[2]=(r*E[i])/pk;
    AL[i]=(long)p1;
  }
  if (DEBUGLEVEL) timer();
  s1=autvec(pk,j3q,(GEN)tabTH[pk]);
  if (DEBUGLEVEL) sgtaut+=timer();
  s2=powpolmod(N,k,pk,s1);
  if (DEBUGLEVEL) {sgt[pk]+=timer();ctsgt[pk]++;}
  s3=autvec(pk,j3q,AL);
  if (DEBUGLEVEL) sgtaut+=timer();
  if ((N[lgefint(N)-1]&7)>=5)
    s3=FpX_red(gmod(gmul(j2q,FpX_red(gmod(gmul(lift(s3),s2),(GEN)tabcyc[pk]),N)),(GEN)tabcyc[pk]),N);
  else s3=FpX_red(gmod(gmul(lift(s3),s2),(GEN)tabcyc[pk]),N);
  if (DEBUGLEVEL) sgt[pk]+=timer();
  etats=(GEN)tabeta[pk]; ind=pk;
  for (i=1; i<=pk; i++) if (gegal(s3,(GEN)etats[i])) {ind=i-1;break;}
  if (ind==pk) return -1;
  if ((ind&1)==0) return 0;
  else
  {
    if (DEBUGLEVEL) timer();
    s3=powgi(gmodulcp(stoi(q),N),shifti(addis(N,-1),-1));
    if (DEBUGLEVEL) {sgt[pk]+=timer();ctsgt[pk]++;}
    return gcmp0(gadd(s3,gun));
  }
}

/* p=2, k=2 */
static int
step4c(GEN N, ulong q, GEN jpq)
{
  int ind,i;
  GEN s0,s1,s3,etats;
  
  s0=gmod(gsqr(jpq),(GEN)tabcyc[4]);
  s1=gmulsg(q,s0);
  if (DEBUGLEVEL) timer();
  s3=powpolmod(N,2,4,s1);
  if ((N[lgefint(N)-1]&3)==3) s3=FpX_red(gmod(gmul(s0,s3),(GEN)tabcyc[4]),N);
  if (DEBUGLEVEL) {sgt[4]+=timer();ctsgt[4]++;}
  etats=(GEN)tabeta[4]; ind=4;
  for (i=1; i<=4; i++) if (gegal(s3,(GEN)etats[i])) {ind=i-1;break;}
  if (ind==4) return -1;
  if ((ind&1)==0) return 0;
  else
  {
    if (DEBUGLEVEL) timer();
    s3=powgi(gmodulcp(stoi(q),N),shifti(addis(N,-1),-1));
    if (DEBUGLEVEL) {sgt[4]+=timer();ctsgt[4]++;}
    return gcmp0(gadd(s3,gun));
  }
}

/* p=2, k=1 */
static int
step4d(GEN N, ulong q)
{
  GEN s1;

  if (DEBUGLEVEL) timer();
  s1=powgi(gmodulcp(negi(stoi(q)),N),shifti(addis(N,-1),-1));
  if (DEBUGLEVEL) {sgt[2]+=timer();ctsgt[2]++;}
  if (gcmp1(s1)) return 0;
  if (!gcmp0(gaddsg(1,s1))) return -1;
  else return ((N[lgefint(N)-1]&3)==1);
}

static int
step5(GEN N, int p, GEN et)
{
  ulong ct,qm3s2,ltabg,q,qp,x,av;
  int k,pk,fl=-1,i,qf;
  GEN ze8,tabf,tabg,ze,jpq=gun,j3q,j2q,vpk,v8;
  byteptr d=diffptr+1;

  ze8=cyclo(8,0);
  v8=cgetg(9,t_VECSMALL);
  ct=0;
  q=2;
  av=avma;
  while (*d && q<=10000)
  {
    avma=av;
    q+= *d++;
    if (q%p==1 && signe(modis(et,q)))
    {
      if (!signe(modis(N,q))) return -1;
      k=1; qp=(q-1)/p; pk=p;
      while (qp%p==0) {k++; pk*=p; qp/=p;}
      extendtabs(N,p,k);
      tabf=computetabdl(q); qm3s2=(q-3)>>1;
      ltabg=(p==2 && k>=3) ? q-2 : qm3s2;
      tabg=cgetg(ltabg+1,t_VECSMALL);
      for (x=1; x<=ltabg; x++) tabg[x]=tabf[x]+tabf[q-x-1];
      vpk=cgetg(pk+1,t_VECSMALL); for (i=1; i<=pk; i++) vpk[i]=0;
      ze=(GEN)tabcyc[pk];
      if (p>=3 || k>=2)
      {
	for (x=1; x<=qm3s2; x++) vpk[tabg[x]%pk+1]++;
	for (x=1; x<=pk; x++) vpk[x]<<=1;
	vpk[(2*tabf[qm3s2+1])%pk+1]++;
	jpq=gmod(smallpolrev(vpk),ze);
      }
      if (p>=3) fl=step4a(N,p,k,jpq);
      else
      {
	if (k>=3)
	{
	  for (x=1; x<=pk; x++) vpk[x]=0;
	  for (x=1; x<=ltabg; x++) tabg[x]+=tabf[x];
	  for (x=1; x<=q-2; x++) vpk[tabg[x]%pk+1]++;
	  j3q=gmod(gmul(jpq,gmod(smallpolrev(vpk),ze)),ze);
	  if ((N[lgefint(N)-1]&7)>=5)
	  {
	    for (x=1; x<=8; x++) v8[x]=0;
	    for (x=1; x<=q-2; x++) v8[((tabf[x]+tabg[x])&7)+1]++;
	    j2q=gmod(gsubst(gsqr(gmod(smallpolrev(v8),ze8)),0,gpuigs(polx[0],pk>>3)),ze);
	  }
	  else j2q=gun;
	  fl=step4b(N,q,k,j2q,j3q);
	}
	else fl=(k==2) ? step4c(N,q,jpq) : step4d(N,q);
      }
    }
    if (fl==-1) {qf=(int)(-q); return qf;}
    if (fl==1) {ctglob=max(ctglob,ct);return 1;}
    ct++;
    if (ct>10000) return 0;
  }
  return 0;
}

static GEN
step6(GEN N, ulong t, GEN et)
{
  GEN N1,r,p1;
  ulong i,av;

  if (DEBUGLEVEL) timer();
  N1=modii(N,et);
  r=gun;
  av=avma;
  for (i=1; i<t; i++)
  {
    avma=av;
    r=modii(mulii(r,N1),et);
    if (!signe(modii(N,r)))
    {
      if (!gcmp1(r) && !gegal(r,N))
      {
	p1=cgetg(3,t_VEC); p1[1]=(long)r; p1[2]=zero; return p1;
      }
    }
  }
  if (DEBUGLEVEL) sgt6=timer();
  return gun;
}

GEN
aprcl(GEN N)
{
  GEN et,fat,flaglp,faq,faqpr,faqex,p1;
  ulong lfat,p,q,lfaq,k,fl,t,i,j;
  ulong av, av0 = avma;
  
  if (cmpis(N,12)<=0)
  {
    if (tabfaux[itos(N)]) return gun;
    else
    {
      p1=cgetg(3,t_VEC); p1[1]=p1[2]=zero; return p1;
    }
  }
  ctglob=0;
  if (DEBUGLEVEL) timer();
  t=compt(N);
  if (DEBUGLEVEL>=2) fprintferr("choosing t = %ld\n",t);
  et=e(t);
  if (cmpii(sqri(et),N)<0) err(talker,"e(t) not large enough in aprcl");
  if (!gcmp1(mppgcd(N,mulsi(t,et))))
  {
    avma = av0;
    p1=cgetg(3,t_VEC); p1[1]=un; p1[2]=zero; return p1;
  }
  fat=calcglobs(N,t); lfat=lg(fat);
  flaglp=cgetg(itos((GEN)fat[lfat-1])+1,t_VECSMALL);
  for (i=2; i<lfat; i++)
  {
    p=itos((GEN)fat[i]);
    if (!gcmp1(lift(gpuigs(gmodulcp(N,stoi(p*p)),p-1)))) flaglp[p]=1;
  }
  calcjac(et);
  if (DEBUGLEVEL) sgtjac=timer();
  if (DEBUGLEVEL>=3)
    fprintferr("Jacobi sums and tables computed in %ld ms\nq-values: ",sgtjac);
  sgtaut=0;
  av=avma;
  for (i=1; i<lglobfa; i++)
  {
    avma=av;
    q=itos((GEN)globfa[i]);
    if (DEBUGLEVEL>=3) fprintferr("%ld ",q);
    faq=(GEN)tabfaq[i];
    faqpr=(GEN)faq[1]; faqex=(GEN)faq[2]; lfaq=lg(faqpr);
    for (j=1; j<lfaq; j++)
    {
      p=itos((GEN)faqpr[j]); k=itos((GEN)faqex[j]);
      if (p>=3) fl=step4a(N,p,k,(GEN)((GEN)tabj[i])[j]);
      else
      {
	if (k>=3) fl=step4b(N,q,k,(GEN)tabj2[i],(GEN)tabj3[i]);
	else
	{
	  if (k==2) fl=step4c(N,q,(GEN)((GEN)tabj[i])[1]); else fl=step4d(N,q);
	}
      }
      if (fl==-1)
      {
	p1=cgetg(4,t_VEC); p1[1]=lstoi(q); p1[2]=lstoi(p); p1[3]=zero;
	return p1;
      }
      if (fl==1) flaglp[p]=1;
    }
  }
 if (DEBUGLEVEL>=3) fprintferr("\nnormal test done; testing conditions lp\n");
 for (i=1; i<lfat; i++)
 {
   p=itos((GEN)fat[i]);
   if (flaglp[p]==0)
   {
     fl=step5(N,p,et);
     if (fl<0)
     {
       avma = av0;
       p1=cgetg(4,t_VEC); p1[1]=lstoi(fl); p1[2]=lstoi(p); p1[3]=zero;
       return p1;
     }
     if (fl==1) continue;
     if (fl==0) err(talker,"aprcl test fails! this is highly improbable");
   }
 }
 if (DEBUGLEVEL>=3) fprintferr("conditions lp done, doing step6\n");
 return gerepilecopy(av0, step6(N,t,et));
}

/* si flag=0 retourne une reponse vrai/faux, sinon retourne des details 
quand N non premier */

GEN
istrueprime(GEN N, int flag)
{
  GEN res;

  res=aprcl(N);
  if (gcmp1(res)) return gun;
  return flag ? res : gzero;
}
