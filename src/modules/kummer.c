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
/*                      KUMMER EXTENSIONS                          */
/*                                                                 */
/*******************************************************************/
#include "pari.h"

static long rc,gc,ell,degK,degKz,m,d,ru,rv,lraycyc,vnf,dv,nbcol,lSml2;
static long lSl,lSp,dK,lSl2,dc;
static GEN module,matexpoteta1,bnf,nf,raycyc,polnf,phiell,powtaubet,vecMsup;
static GEN unmodell,bnfz,nfz,U,uu,gell,cyc,gencyc,vecalpha,R,A1,A2,g,vselmer;
static GEN bnrz,polrel,steinitzZk,listmod,listprSp,listbid,listunif,listellrank;
static GEN listmodsup,listbidsup,listellranksup,vecw,Sm,Sml1,Sml2,Sl;
static GEN ESml2,Sp,vecbetap,vecalphap,matP,gg,mginv;

/* row vector B x matrix T : c_j=prod_i (b_i^T_ij) */
static GEN
groupproduct(GEN B, GEN T)
{
  long lB,lT,i,j;
  GEN c,p1;

  lB=lg(B)-1;
  lT=lg(T)-1;
  c=cgetg(lT+1,t_VEC);
  for (j=1; j<=lT; j++)
  {
    p1=gun;
    for (i=1; i<=lB; i++) p1=gmul(p1,gpui((GEN)B[i],gcoeff(T,i,j),0));
    c[j]=(long)p1;
  }
  return c;
}

static GEN
grouppows(GEN B, long ex)
{
  long lB,j;
  GEN c;

  lB=lg(B)-1;
  c=cgetg(lB+1,t_VEC);
  for (j=1; j<=lB; j++) c[j]=(long)gpuigs((GEN)B[j],ex);
  return c;
}

static GEN
get_listx(GEN arch,GEN msign,GEN munit,GEN vecmunit2,long ell,long lSp,long lSml2,long nbvunit,long r1)
{
  GEN kermat,p2,p3,p4,y,yinit,listx,unmodell = gmodulss(1,ell);
  long i,j,k,cmpt,lker;

  kermat=lift(ker(munit)); lker=lg(kermat)-1;
  if (!lker) return cgetg(1,t_VEC);
  yinit=cgetg(lker,t_VEC); y=cgetg(lker,t_VEC);
  for (i=1; i<lker; i++)
  {
    y[i]=lgeti(3); affii(gzero,(GEN)y[i]);
    yinit[i]=zero;
  }
  listx=cgetg(1,t_VEC);
  for(;;)
  {
    p2=cgetg(2,t_VEC);
    p3=(GEN)kermat[lker];
    for (j=1; j<lker; j++)
      p3=lift(gmul(unmodell,gadd(p3,gmul((GEN)y[j],(GEN)kermat[j]))));
    cmpt=0; for (j=1; j<=lSp; j++) if (gcmp0((GEN)p3[j+nbvunit])) cmpt++;
    if (!cmpt)
    {
      for (k=1; k<=lSml2; k++)
      {
        p4=lift(gmul((GEN)vecmunit2[k],p3));
        j=1; while (j<lg(p4) && !signe(p4[j])) j++;
        if (j>=lg(p4)) break;
      }
      if (k>lSml2)
      {
        p4=lift(gmul(msign,p3));
        j=1; while (j<=r1 && gegal((GEN)p4[j],(GEN)arch[j])) j++;
        if (j>r1) { p2[1]=(long)p3; listx=concatsp(listx,p2); }
      }
    }
    if (!lSp)
    {
      j=1; while (j<lker && !signe(y[j])) j++;
      if (j<lker && gcmp1((GEN)y[j]))
      {
        p3=gsub(p3,(GEN)kermat[lker]);
        for (k=1; k<=lSml2; k++)
        {
          p4=lift(gmul((GEN)vecmunit2[k],p3));
          j=1; while (j<lg(p4) && !signe(p4[j])) j++;
          if (j>=lg(p4)) break;
        }
        if (k>lSml2)
        {
          p4=lift(gmul(msign,p3));
          j=1; while (j<=r1 && gegal((GEN)p4[j],(GEN)arch[j])) j++;
          if (j>r1) { p2[1]=(long)p3; listx=concatsp(listx,p2); }
        }
      }
    }
    i=lker;
    do
    {
      i--; if (!i) return listx;

      if (i<lker-1) affii((GEN)yinit[i+1],(GEN)y[i+1]);
      gaddgsz((GEN)y[i],1,(GEN)y[i]);
    }
    while (cmpis((GEN)y[i],ell)>=0);
  }
}

static GEN
reducealpha(GEN nf,GEN x,GEN gell)
/* etant donne un nombre algebrique x du corps nf -- non necessairement
   entier -- calcule un entier algebrique de la forme x*g^gell */
{
  long tx=typ(x),i;
  GEN den,fa,fac,ep,p1,y;

  nf=checknf(nf);
  if ((tx==t_POL)||(tx==t_POLMOD)) y=algtobasis(nf,x);
  else { y=x; x=basistoalg(nf,y); }
  den=denom(y);
  if (gcmp1(den)) return x;
  fa=decomp(den);fac=(GEN)fa[1];ep=(GEN)fa[2];
  p1=gun;
  for (i=1; i<lg(fac); i++)
    p1=mulii(p1,gpui((GEN)fac[i],gceil(gdiv((GEN)ep[i],gell)),0));
  return gmul(gpui(p1,gell,0),x);
}

/* si all!=0, donne toutes les equations correspondant a un sousgroupe
   de determinant all (i.e. de degre all) */
static GEN
rnfkummersimple(GEN bnr, GEN subgroup, long all, long prec)
{
  long r1,degnf,ell,j,i;
  long nbgenclK,lprm,lprl,lSml2,lSl,lSp,lastindex,nbvunit,nbvunit0;
  long kmax,nbgenbid,lastbid,nbcol,nblig,k,llistx,e,vp,vd,v1;

  GEN bnf,nf,p1,classgroup,cyclic,bid,module,ideal,arch;
  GEN gell,p2,p3,p22;
  GEN clK,cyclicK,genK,listgamma,listalpha,fa,prm,expom,Sm,Sml1,Sml2,Sl,ESml2;
  GEN pp,p,prl,Sp,vecbeta,matexpo,unmodell,vunit,id,pr,vsml2,listalpha0;
  GEN cycpro,cl,cycbid,munit,vecmunit2,msign,archartif,listx,listal,listgamma0;
  GEN vecbeta0;

  checkbnrgen(bnr); bnf=(GEN)bnr[1];
  nf=(GEN)bnf[7]; r1 = nf_get_r1(nf);
  polnf=(GEN)nf[1]; vnf=varn(polnf);
  if (vnf==0) err(talker,"main variable in kummer must not be x");
  p1=conductor(bnr,all ? gzero : subgroup,2,prec);
  bnr=(GEN)p1[2]; if(!all) subgroup=(GEN)p1[3];
  classgroup=(GEN)bnr[5];
  cyclic=(GEN)classgroup[2];
  bid=(GEN)bnr[2]; module=(GEN)bid[1];
  ideal=(GEN)module[1]; arch=(GEN)module[2];
  if (!all && gcmp0(subgroup)) subgroup = diagonal(cyclic);
  degnf=lgef(polnf)-3;
  gell = all? stoi(all): det(subgroup);
  if (!isprime(gell))
    err(impl,"kummer for non prime relative degree");
  ell=itos(gell);
  unmodell=gmodulss(1,ell);
  clK=gmael(bnf,8,1); cyclicK=(GEN)clK[2]; genK=(GEN)clK[3];
  nbgenclK=lg(genK)-1;
  i=1; while (i<=nbgenclK && gdivise((GEN)cyclicK[i],gell)) i++;
  lastindex=i-1;
  listgamma0=cgetg(nbgenclK+1,t_VEC);
  listgamma=cgetg(nbgenclK+1,t_VEC);
  listalpha0=cgetg(lastindex+1,t_VEC);
  listalpha=cgetg(lastindex+1,t_VEC);
  p1=gmul(gell,ideal);
  for (i=1; i<=lastindex; i++)
  {
    p3=basistoalg(nf,idealcoprime(nf,(GEN)genK[i],p1));
    listgamma[i]=listgamma0[i]=linv(p3);
    p2=idealpow(nf,(GEN)genK[i],(GEN)cyclicK[i]);
    listalpha0[i]=(long)basistoalg(nf,(GEN)isprincipalgen(bnf,p2)[2]);
    listalpha[i]=lmul((GEN)listalpha0[i],gpui(p3,(GEN)cyclicK[i],0));
  }
  for (   ; i<=nbgenclK; i++)
  {
    p3=basistoalg(nf,idealcoprime(nf,(GEN)genK[i],p1));
    p2=idealpow(nf,(GEN)genK[i],(GEN)cyclicK[i]);
    p2=basistoalg(nf,(GEN)isprincipalgen(bnf,p2)[2]);
    p22=lift(ginv(gmul(unmodell,(GEN)cyclicK[i])));
    p2=gpui(p2,p22,0);listgamma0[i]=(long)p2;
    listgamma[i]=lmul(p2,gpui(p3,addis(mulii(p22,(GEN)cyclicK[i]),-1),0));
  }
  /* a ce stade, module est egal au conducteur. */
  fa=idealfactor(nf,ideal);
  prm=(GEN)fa[1]; expom=(GEN)fa[2]; lprm=lg(prm)-1;
  Sm=cgetg(1,t_VEC);Sml1=cgetg(1,t_VEC);Sml2=cgetg(1,t_VEC);Sl=cgetg(1,t_VEC);
  ESml2=cgetg(1,t_VEC);
  for (i=1; i<=lprm; i++)
  {
    pp=cgetg(2,t_VEC); pp[1]=prm[i];
    p=gmael(pp,1,1); e=itos(gmael(pp,1,3));
    if (!gegal(p,gell))
    {
      if (!gcmp1((GEN)expom[i]))
      {
	if (all) return cgetg(1,t_VEC);
	err(talker,"bug1 in kummer");
      }
      Sm=concatsp(Sm,pp);
    }
    else
    {
      vp=itos((GEN)expom[i]); vd=(vp-1)*(ell-1)-ell*e;
      if (vd > 0)
      {
	if (all) return cgetg(1,t_VEC);
	err(talker,"bug4 in kummer");
      }
      if (vd==0)
        Sml1=concatsp(Sml1,pp);
      else
      {
	if (vp==1)
	{
	  if (all) return cgetg(1,t_VEC);
	  err(talker,"bug2 in kummer");
	}
	else
	{
	  Sml2=concatsp(Sml2,pp); ESml2=concatsp(ESml2,(GEN)expom[i]);
	}
      }
    }
  }
  prl=primedec(nf,gell); lprl=lg(prl)-1;
  for (i=1; i<=lprl; i++)
    if (!idealval(nf,ideal,(GEN)prl[i]))
    {
      pp=cgetg(2,t_VEC); pp[1]=prl[i];
      Sl=concatsp(Sl,pp);
    }
  lSml2=lg(Sml2)-1; lSl=lg(Sl)-1;
  Sp=concatsp(Sm,Sml1); lSp=lg(Sp)-1;
  vecbeta=cgetg(lSp+1,t_VEC); matexpo=cgetg(lSp+1,t_MAT);
  vecbeta0=cgetg(lSp+1,t_VEC);
  for (j=1; j<=lSp; j++)
  {
    p1=isprincipalgen(bnf,(GEN)Sp[j]);
    p2=basistoalg(nf,(GEN)p1[2]);
    for (i=1; i<=lastindex; i++)
      p2 = gmul(p2,gpui((GEN)listgamma[i],gmael(p1,1,i),0));
    p22=p2;
    for (   ; i<=nbgenclK; i++)
    {
      p2 = gmul(p2,gpui((GEN)listgamma[i],gmael(p1,1,i),0));
      p22 = gmul(p22,gpui((GEN)listgamma0[i],gmael(p1,1,i),0));
    }
    matexpo[j]=(long)p1[1];
    vecbeta[j]=(long)p2; /* attention, ceci sont les beta modifies */
    vecbeta0[j]=(long)p22;
  }
  matexpo=gmul(unmodell,matexpo);
  vunit=gmodulcp(concatsp(gmael(bnf,8,5),gmael3(bnf,8,4,2)),polnf);
  nbvunit0=lg(vunit)-1;
  for (i=1; i<=lastindex; i++) vunit=concatsp(vunit,(GEN)listalpha[i]);
  nbvunit=lg(vunit)-1;
  id=idmat(degnf);
  for (i=1; i<=lSl; i++)
  {
    pr=(GEN)Sl[i];
    id=idealmul(nf,idealpow(nf,pr,stoi((ell*itos((GEN)pr[3]))/(ell-1))),id);
  }
  vsml2=cgetg(lSml2+1,t_VEC);
  for (i=1; i<=lSml2; i++)
  {
    pr=(GEN)Sml2[i];
    v1=itos((GEN)ESml2[i]);
    kmax=(itos((GEN)pr[3])*ell)/(ell-1)+1-v1;
    p1=idealpow(nf,pr,stoi(kmax));
    id=idealmul(nf,id,p1);
    p2=idealmul(nf,p1,pr);
    p3=zidealstarinitgen(nf,p2);
    vsml2[i]=(long)p3;
    cycpro=gmael(p3,2,2);
    for (j=1;j<lg(cycpro);j++)
      if (! gdivise((GEN)cycpro[j],gell)) err(talker,"bug5 in kummer");
  }
  bid=zidealstarinitgen(nf,id);
  cl=(GEN)bid[2]; cycbid=(GEN)cl[2]; nbgenbid=lg(cycbid)-1;
  i=1; while (i<=nbgenbid && gdivise((GEN)cycbid[i],gell)) i++;
  lastbid=i-1;
  nbcol=nbvunit+lSp; nblig=lastbid+lastindex;
  munit=cgetg(nbcol+1,t_MAT); vecmunit2=cgetg(lSml2+1,t_VEC);
  msign=cgetg(nbcol+1,t_MAT);
  for (k=1; k<=lSml2; k++) vecmunit2[k]=lgetg(nbcol+1,t_MAT);
  archartif=cgetg(r1+1,t_VEC); for (j=1; j<=r1; j++) archartif[j]=un;
  for (j=1; j<=nbvunit; j++)
  {
    p1=zideallog(nf,(GEN)vunit[j],bid);
    p2=cgetg(nblig+1,t_COL); munit[j]=(long)p2;
    for (i=1; i<=lastbid; i++) p2[i]=p1[i];
    for (   ; i<=nblig; i++) p2[i]=zero;
    for (k=1; k<=lSml2; k++)
      ((GEN)vecmunit2[k])[j]=(long)zideallog(nf,(GEN)vunit[j],(GEN)vsml2[k]);
    msign[j]=(long)zsigne(nf,(GEN)vunit[j],archartif);
  }
  p1=cgetg(nbgenclK-lastindex+1,t_VEC);
  for (j=1; j<=lSp; j++)
  {
    p2=zideallog(nf,(GEN)vecbeta[j],bid);
    p3=cgetg(nblig+1,t_COL); munit[j+nbvunit]=(long)p3;
    for (i=1; i<=lastbid; i++) p3[i]=p2[i];
    for (   ; i<=nblig; i++) p3[i]=coeff(matexpo,i-lastbid,j);
    for (k=1; k<=lSml2; k++)
    {
      p2=zideallog(nf,(GEN)vecbeta[j],(GEN)vsml2[k]);
      ((GEN)vecmunit2[k])[j+nbvunit]=(long)p2;
    }
    msign[j+nbvunit]=(long)zsigne(nf,(GEN)vecbeta[j],archartif);
  }
  munit=gmul(unmodell,munit); vecmunit2=gmul(unmodell,vecmunit2);
  listx = get_listx(arch,msign,munit,vecmunit2,ell,lSp,lSml2,nbvunit,r1);
  llistx=lg(listx)-1;
  listal=cgetg(llistx+1,t_VEC);
  for (i=1; i<=llistx; i++)
  {
    p1=gun; p3=(GEN)listx[i];
    for (j=1; j<=nbvunit0; j++)
      p1 = gmul(p1,gpui((GEN)vunit[j],(GEN)p3[j],0));
    for (   ; j<=nbvunit; j++)
      p1 = gmul(p1,gpui((GEN)listalpha0[j-nbvunit0],(GEN)p3[j],0));
    for (j=1; j<=lSp; j++)
      p1 = gmul(p1,gpui((GEN)vecbeta0[j],(GEN)p3[j+nbvunit],0));
    listal[i]=(long)reducealpha(nf,p1,gell);
  }
 /* A ce stade, tous les alpha dans la liste listal statisfont les
  * congruences, noncongruences et signatures, et ne sont pas des puissances
  * l-iemes donc x^l-alpha est irreductible, sa signature est correcte ainsi
  * que son discriminant relatif. Reste a determiner son groupe de normes.
  * Les alpha ne sont peut-etre pas des entiers algebriques..  */
  if (DEBUGLEVEL)
    { fprintferr("listalpha = \n"); outerr(listal); flusherr(); }
  p2=cgetg(1,t_VEC);
  for (i=1; i<=llistx; i++)
  {
    p1=gsub(gpuigs(polx[0],ell),(GEN)listal[i]);
    if (all || gegal(rnfnormgroup(bnr,p1),subgroup))
      p2=concatsp(p2,p1);
  }
  if (all) return gcopy(p2);
  switch(lg(p2)-1)
  {
    case 0: err(talker,"bug 6: no equation found in kummer");
    case 1: return gcopy((GEN)p2[1]);
    default: fprintferr("equations = \n"); outerr(p2);
      err(talker,"bug 7: more than one equation found in kummer");
  }
  return gzero; /* not reached */
}

static GEN
tauofideal(GEN id)
{
  long j;
  GEN p1,p2;

  p1=gsubst(gmul((GEN)nfz[7],id),vnf,U);
  p2=cgetg(lg(p1),t_MAT);
  for (j=1; j<lg(p1); j++) p2[j]=(long)algtobasis(nfz,(GEN)p1[j]);
  return p2;
}

static GEN
tauofprimeideal(GEN pr)
{
  GEN p1;

  p1=gcopy(pr);
  p1[2]=(long)algtobasis(nfz,gsubst(gmul((GEN)nfz[7],(GEN)pr[2]),vnf,U));
  return gcoeff(idealfactor(nfz,prime_to_ideal(nfz,p1)),1,1);
}

static long
isprimeidealconj(GEN pr1, GEN pr2)
{
  GEN pr=pr1;

  do
  {
    if (gegal(pr,pr2)) return 1;
    pr=tauofprimeideal(pr);
  }
  while (!gegal(pr,pr1));
  return 0;
}

static long
isconjinprimelist(GEN listpr, GEN pr2)
{
  long ll=lg(listpr)-1,i;

  for (i=1; i<=ll; i++)
    if (isprimeidealconj((GEN)listpr[i],pr2)) return 1;
  return 0;
}

static void
computematexpoteta1(void)
{
  long i,j;
  GEN p4,p5,p6;

  matexpoteta1=cgetg(degK+1,t_MAT);
  p4=gmodulcp(polun[vnf],R);
  for (j=1; j<=degK; j++)
  {
    p5=cgetg(degKz+1,t_COL); matexpoteta1[j]=(long)p5; p6=lift(p4);
    for (i=1; i<=degKz; i++) p5[i]=(long)truecoeff(p6,i-1);
    if (j<degK) p4=gmul(p4,A1);
  }
}

static GEN
downtoK(GEN x)
{
  long i;
  GEN p1,p2,p3;

  p1=cgetg(degKz+1,t_COL);
  p2=lift(x);
  for (i=1; i<=degKz; i++) p1[i]=(long)truecoeff(p2,i-1);
  p2=inverseimage(matexpoteta1,p1);
  if (lg(p2)==1) err(talker,"not an element of K in downtoK");
  p3=(GEN)p2[degK];
  for (i=degK-1; i; i--) p3=gadd((GEN)p2[i],gmul(polx[vnf],p3));
  return gmodulcp(p3,polnf);
}

static GEN
tracetoK(GEN x)
{
  long i;
  GEN p1,p2;

  p1=x; p2=x;
  for (i=1; i<=m-1; i++)
  {
    p1=gsubst(lift(p1),vnf,U);
    p2=gadd(p2,p1);
  }
  return downtoK(p2);
}

static GEN
normtoK(GEN x)
{
  long i;
  GEN p1,p2;

  p1=x; p2=x;
  for (i=1; i<=m-1; i++)
  {
    p1=gsubst(lift(p1),vnf,U);
    p2=gmul(p2,p1);
  }
  return downtoK(p2);
}

static GEN
computepolrel(void)
{
  long i,j;
  GEN p1,p2;

  p1=gun; p2=gmodulcp(polx[vnf],R);
  for (i=0; i<=m-1; i++)
  {
    p1=gmul(p1,gsub(polx[0],p2));
    if (i<m-1) p2=gsubst(lift(p2),vnf,U);
  }
  for (j=2; j<=m+2; j++) p1[j]=(long)downtoK((GEN)p1[j]);
  return p1;
}

/* alg. 5.2.15. with remark */
static GEN
isprincipalell(GEN id)
{
  long i;
  GEN p1,p2,logdisc,be;

  p1=isprincipalgen(bnfz,id); logdisc=(GEN)p1[1];
  be=basistoalg(bnfz,(GEN)p1[2]);
  for (i=rc+1; i<=gc; i++)
    be=gmul(be,gpui((GEN)vecalpha[i],modii(mulii((GEN)logdisc[i],(GEN)uu[i]),gell),0));
  p2=cgetg(3,t_VEC);
  p2[2]=(long)be;
  p1=cgetg(rc+1,t_COL); p2[1]=(long)p1;
  for (i=1; i<=rc; i++) p1[i]=logdisc[i];
  return p2;
}

/* alg. 5.3.11. */
static GEN
isvirtualunit(GEN v)
{
  long llist,i,j,ex;
  GEN p1,p2,listex,listpr,q,ga,eps,vecy,logdisc;

  p1=idealfactor(nfz,v);
  listex=(GEN)p1[2]; listpr=(GEN)p1[1]; llist=lg(listex)-1;
  q=idmat(degKz);
  for (i=1; i<=llist; i++)
  {
    ex=itos((GEN)listex[i]);
    if (ex%ell) err(talker,"not a virtual unit in isvirtualunit");
    q=idealmul(nfz,q,idealpow(nfz,(GEN)listpr[i],stoi(ex/ell)));
  }
  p1=isprincipalgen(bnfz,q); logdisc=(GEN)p1[1];
  ga=basistoalg(nfz,(GEN)p1[2]);
  for (j=rc+1; j<=gc; j++)
    ga=gmul(ga,gpui((GEN)vecalpha[j],divii((GEN)logdisc[j],(GEN)cyc[j]),0));
  eps=gpuigs(ga,ell);
  vecy=cgetg(rc+1,t_COL);
  for (j=1; j<=rc; j++)
  {
    vecy[j]=(long)divii((GEN)logdisc[j],divii((GEN)cyc[j],gell));
    eps=gmul(eps,gpui((GEN)vecalpha[j],(GEN)vecy[j],0));
  }
  eps=gdiv(v,eps);
  p1=isunit(bnfz,eps);
  p2=cgetg(3,t_VEC);
  p2[1]=(long)concatsp(vecy,lift(p1));
  p2[2]=(long)ga;
  return p2;
}

static GEN
lifttokz(GEN id)
{
  long i,j;
  GEN p1,p2,p3;

  p1=gsubst(gmul((GEN)nf[7],id),vnf,A1);
  p2=gmodulcp((GEN)nfz[7],R);
  p3=cgetg(degK*degKz+1,t_MAT);
  for (i=1; i<=degK; i++)
    for (j=1; j<=degKz; j++)
      p3[(i-1)*degKz+j]=(long)algtobasis(nfz,gmul((GEN)p1[i],(GEN)p2[j]));
  return hnfmod(p3,detint(p3));
}

static GEN
steinitzaux(GEN id)
{
  long i,j;
  GEN p1,p2,p3,vecid,matid,pseudomat,pid;

  p1=gsubst(gmul((GEN)nfz[7],id),vnf,polx[0]);
  for (j=1; j<=degKz; j++)
    p1[j]=(long)gmod((GEN)p1[j],polrel);
  p2=cgetg(degKz+1,t_MAT);
  for (j=1; j<=degKz; j++)
  {
    p3=cgetg(m+1,t_COL); p2[j]=(long)p3;
    for (i=1; i<=m; i++) p3[i]=(long)algtobasis(nf,truecoeff((GEN)p1[j],i-1));
  }
  vecid=cgetg(degKz+1,t_VEC); matid=idmat(degK);
  for (j=1; j<=degKz; j++) vecid[j]=(long)matid;
  pseudomat=cgetg(3,t_VEC);
  pseudomat[1]=(long)p2; pseudomat[2]=(long)vecid;
  pid=(GEN)nfhermite(nf,pseudomat)[2];
  p1=matid;
  for (j=1; j<=m; j++) p1=idealmul(nf,p1,(GEN)pid[j]);
  return p1;
}

static GEN
normrelz(GEN id)
{
  GEN p1;

  p1=steinitzaux(id);
  return idealdiv(nf,p1,steinitzZk);
}

static GEN
invimsubgroup(GEN bnr, GEN subgroup, GEN idealz, long prec)
{
  long lraycycz,i,j;
  GEN Plog,rayclgpz,genraycycz,utemp,p1,p2;

  bnrz=buchrayinitgen(bnfz,idealz,prec);
  rayclgpz=(GEN)bnrz[5];
  genraycycz=(GEN)rayclgpz[3]; lraycycz=lg(genraycycz)-1;
  Plog=cgetg(lraycycz+lraycyc+1,t_MAT);
  for (j=1; j<=lraycycz; j++)
    Plog[j]=(long)isprincipalray(bnr,normrelz((GEN)genraycycz[j]));
  for (   ; j<=lraycycz+lraycyc; j++)
    Plog[j]=subgroup[j-lraycycz];
  utemp=(GEN)hnfall(Plog)[2];
  p2=cgetg((lraycycz<<1)+1,t_MAT);
  for (j=1; j<=lraycycz; j++)
  {
    p1=cgetg(lraycycz+1,t_COL); p2[j]=(long)p1;
    for (i=1; i<=lraycycz; i++) p1[i]=coeff(utemp,i,j);
  }
  p1=diagonal((GEN)rayclgpz[2]);
  for (  ; j<=(lraycycz<<1); j++) p2[j]=p1[j-lraycycz];
  return hnfmod(p2,(GEN)rayclgpz[1]);
}

static GEN
ideallogaux(long ind, GEN al)
{
  long llogli,valal;
  GEN p1;

  valal=element_val(nfz,algtobasis(nfz,al),(GEN)listprSp[ind]);
  al=gmul(al,gpuigs((GEN)listunif[ind],valal));
  p1=zideallog(nfz,al,(GEN)listbid[ind]);
  llogli=itos((GEN)listellrank[ind]);
  setlg(p1,llogli+1); return p1;
}

static GEN
ideallogauxsup(long ind, GEN al)
{
  long llogli,valal;
  GEN p1;

  valal=element_val(nfz,algtobasis(nfz,al),(GEN)listprSp[ind]);
  al=gmul(al,gpuigs((GEN)listunif[ind],valal));
  p1=zideallog(nfz,al,(GEN)listbidsup[ind]);
  llogli=itos((GEN)listellranksup[ind]);
  setlg(p1,llogli+1); return p1;
}

static GEN
vectau(GEN list)
{
  long i,j,n,cmpt;
  GEN listz,listc,yz,yc,listfl,s,p1,p2,y;

  listz=(GEN)list[1]; listc=(GEN)list[2]; n=lg(listz)-1;
  yz=cgetg(n+1,t_VEC); yc=cgetg(n+1,t_VEC);
  listfl=cgetg(n+1,t_VEC); for (i=1; i<=n; i++) listfl[i]=un;
  cmpt=0;
  for (i=1; i<=n; i++)
  {
    if (signe((GEN)listfl[i]))
    {
      cmpt++;
      yz[cmpt]=listz[i];
      s=(GEN)listc[i];
      for (j=i+1; j<=n; j++)
      {
	if (signe((GEN)listfl[j])&&gegal((GEN)listz[j],(GEN)listz[i]))
	{
	  s=gadd(s,(GEN)listc[j]);
	  listfl[j]=zero;
	}
      }
      yc[cmpt]=(long)s;
    }
  }
  y=cgetg(3,t_VEC);
  p1=cgetg(cmpt+1,t_VEC); p2=cgetg(cmpt+1,t_VEC); y[1]=(long)p1; y[2]=(long)p2;
  for (i=1; i<=cmpt; i++)
  {
    p1[i]=yz[i];
    p2[i]=yc[i];
  }
  return y;
}

#if 0
static GEN
addtau(GEN listx, GEN listy)
{
  GEN p1,p2,y;

  p1=concat((GEN)listx[1],(GEN)listy[1]);
  p2=concat((GEN)listx[2],(GEN)listy[2]);
  y=cgetg(3,t_VEC); y[1]=(long)p1; y[2]=(long)p2;
  return vectau(y);
}
#endif

static GEN
subtau(GEN listx, GEN listy)
{
  GEN p1,p2,y;

  p1=concat((GEN)listx[1],(GEN)listy[1]);
  p2=concat((GEN)listx[2],gneg_i((GEN)listy[2]));
  y=cgetg(3,t_VEC); y[1]=(long)p1; y[2]=(long)p2;
  return vectau(y);
}

static GEN
negtau(GEN list)
{
  GEN y;

  y=cgetg(3,t_VEC);
  y[1]=list[1];
  y[2]=lneg((GEN)list[2]);
  return y;
}

static GEN
multau(GEN listx, GEN listy)
{
  GEN lzx,lzy,lcx,lcy,lzz,lcz,y;
  long nx,ny,i,j,k;

  lzx=(GEN)listx[1]; lcx=(GEN)listx[2]; nx=lg(lzx)-1;
  lzy=(GEN)listy[1]; lcy=(GEN)listy[2]; ny=lg(lzy)-1;
  lzz=cgetg(nx*ny+1,t_VEC); lcz=cgetg(nx*ny+1,t_VEC);
  for (i=1; i<=nx; i++)
    for (j=1; j<=ny; j++)
    {
      k=(i-1)*ny+j;
      lzz[k]=ladd((GEN)lzx[i],(GEN)lzy[j]);
      lcz[k]=lmul((GEN)lcx[i],(GEN)lcy[j]);
    }
  y=cgetg(3,t_VEC); y[1]=(long)lzz; y[2]=(long)lcz;
  return vectau(y);
}

#if 0
static GEN
puipol(GEN be, GEN pol)
{
  long i,degpol;
  GEN y;

  degpol=degree(pol);
  y=gun;
  for (i=0; i<=degpol; i++)
    if (!gcmp0((GEN)pol[i+2])) y=gmul(y,gpui((GEN)powtaubet[i+1],(GEN)pol[i+2],0));
  return y;
}

static GEN
puitau(GEN be, GEN list)
{
  long lgl,i;
  GEN y,listz,listc,p1;

  y=gun; listz=(GEN)list[1]; listc=(GEN)list[2]; lgl=lg(listz)-1;
  for (i=1; i<=lgl; i++)
  {
    p1=lift((GEN)listc[i]);
    if (!gcmp0(p1))
    {
      if (!gcmp0(lift(gmul(unmodell,(GEN)listz[i]))))
	err(talker,"bug1 in puitau");
      if (degree(p1)) err(talker,"bug2 in puitau");
      if (typ(p1)==t_POL) p1=(GEN)p1[2];
      y=gmul(y,gpui(puipol(be,(GEN)listz[i]),p1,0));
    }
  }
  return y;
}
#endif

static GEN
mulpoltau(GEN poltau, GEN list)
{
  long i,j;
  GEN y;

  j=lg(poltau)-2;
  y=cgetg(j+3,t_VEC);
  y[1]=(long)negtau(multau(list,(GEN)poltau[1]));
  for (i=2; i<=j+1; i++)
  {
    y[i]=(long)subtau((GEN)poltau[i-1],multau(list,(GEN)poltau[i]));
  }
  y[j+2]=poltau[j+1];
  return y;
}

/* th. 5.3.5. and prop. 5.3.9. */
static GEN
computepolrelbeta(GEN be)
{
  long i,a,b,j;
  GEN e,u,u1,u2,u3,p1,p2,p3,p4,zet,be1,be2,listr,s,veczi,vecci;

  switch (ell)
  {
    case 2: err(talker,"you should not be here in rnfkummer !!"); break;
    case 3: e=normtoK(be); u=tracetoK(be);
      return gsub(gmul(polx[0],gsub(gsqr(polx[0]),gmulsg(3,e))),gmul(e,u));
    case 5: e=normtoK(be);
      if (d==2)
      {
	u=tracetoK(gpuigs(be,3));
	p1=gadd(gmulsg(5,gsqr(e)),gmul(gsqr(polx[0]),gsub(gsqr(polx[0]),gmulsg(5,e))));
	return gsub(gmul(polx[0],p1),gmul(e,u));
      }
      else
      {
	be1=gsubst(lift(be),vnf,U); be2=gsubst(lift(be1),vnf,U);
	u1=tracetoK(gmul(be,be1)); u2=tracetoK(gmul(gmul(be,be2),gsqr(be1)));
	u3=tracetoK(gmul(gmul(gsqr(be),gpuigs(be1,3)),be2));
	p1=gsub(gsqr(polx[0]),gmulsg(10,e));
	p1=gsub(gmul(polx[0],p1),gmulsg(5,gmul(e,u1)));
	p1=gadd(gmul(polx[0],p1),gmul(gmulsg(5,e),gsub(e,u2)));
	p1=gsub(gmul(polx[0],p1),gmul(e,u3));
	return p1;
      }
    default: p1=cgetg(2,t_VEC); p2=cgetg(3,t_VEC); p3=cgetg(2,t_VEC);
      p4=cgetg(2,t_VEC); p3[1]=zero; p4[1]=un;
      p2[1]=(long)p3; p2[2]=(long)p4; p1[1]=(long)p2;
      zet=gmodulcp(polx[vnf],phiell);
      listr=cgetg(m+1,t_VEC);
      listr[1]=un;
      for (i=2; i<=m; i++) listr[i]=(long)modii(mulii((GEN)listr[i-1],g),gell);
      veczi=cgetg(m+1,t_VEC);
      for (b=0; b<m; b++)
      {
	s=gzero;
	for (a=0; a<m; a++)
	  s=gadd(gmul(polx[0],s),modii(mulii((GEN)listr[b+1],(GEN)listr[a+1]),gell));
	veczi[b+1]=(long)s;
      }
      for (j=0; j<ell; j++)
      {
	vecci=cgetg(m+1,t_VEC);
	for (b=0; b<m; b++) vecci[b+1]=(long)gpui(zet,mulsi(j,(GEN)listr[b+1]),0);
	p4=cgetg(3,t_VEC);
	p4[1]=(long)veczi; p4[2]=(long)vecci;
	p1=mulpoltau(p1,p4);
      }
      powtaubet=cgetg(m+1,t_VEC);
      powtaubet[1]=(long)be;
      for (i=2; i<=m; i++) powtaubet[i]=(long)gsubst(lift((GEN)powtaubet[i-1]),vnf,U);
      err(impl,"difficult Kummer for ell>=7"); return gzero;
  }
  return NULL; /* not reached */
}

/* multiply be by ell-th powers of units as to find "small" L2-norm for new be */
static GEN
reducebeta(GEN be)
{
  long i,lu;
  GEN p1,p2,unitsell,unitsellinv,nmax,ben;

  unitsell=grouppows(gmodulcp(concatsp(gmael(bnfz,8,5),gmael3(bnfz,8,4,2)),R),ell);
  unitsellinv=grouppows(unitsell,-1);
  unitsell=concatsp(unitsell,unitsellinv);
  p1=unitsell;
  for (i=2; i<=max((ell>>1),3); i++) p1=concatsp(p1,grouppows(unitsell,i));
  unitsell=p1;
  nmax=gnorml2(algtobasis(nfz,be));
  lu=lg(unitsell)-1; ben=be;
  do
  {
    be=ben;
    for (i=1; i<=lu; i++)
    {
      p1=gmul(be,(GEN)unitsell[i]);
      p2=gnorml2(algtobasis(nfz,p1));
      if (gcmp(p2,nmax)<0)
      {
	nmax=p2; ben=p1;
      }
    }
  }
  while (!gegal(be,ben));
  return be;
}

static GEN
testx(GEN subgroup, GEN X, long prec)
{
  long i,v;
  GEN be,polrelbe,p1;

/* in alg. 5.3.18., C=nbcol */
  X=gmul(unmodell,X);
  if (gcmp0(X)) return gzero;
  for (i=dv+1; i<=nbcol; i++) if (gcmp0((GEN)X[i])) return gzero;
  for (i=1; i<=lSml2; i++)
    if (gcmp0(gmul((GEN)vecMsup[i],X))) return gzero;
  be=gun;
  for (i=1; i<=nbcol; i++) be=gmul(be,gpui((GEN)vecw[i],lift((GEN)X[i]),0));
  if (DEBUGLEVEL>=2) { fprintferr("reducing beta = "); outerr(be); }
  be=reducebeta(be);
  if (DEBUGLEVEL>=2) { fprintferr("beta reduced = "); outerr(be); }
  polrelbe=computepolrelbeta(be);
  v=varn(polrelbe);
  p1=unifpol((GEN)bnf[7],polrelbe,0);
  p1=denom(gtovec(p1));
  polrelbe=gsubst(polrelbe,v,gdiv(polx[v],p1));
  polrelbe=gmul(polrelbe,gpuigs(p1,degree(polrelbe)));
  if (DEBUGLEVEL>=2) { fprintferr("polrelbe = "); outerr(polrelbe); }
  p1=rnfconductor(bnf,polrelbe,0,prec);
  if (!gegal((GEN)p1[1],module)) return gzero;
  if (!gegal((GEN)p1[3],subgroup)) return gzero;
  return polrelbe;
}

GEN
rnfkummer(GEN bnr, GEN subgroup, long all, long prec)
{
  long i,j,av=avma,tetpil,llistpr,lfactell,e,vp,vd,ind;
  GEN p1,p2,p3,p4,wk;
  GEN rayclgp,bid,ideal;
  GEN kk,clgp,fununits,torsunit,vecB,vecC,Tc,Tv,P;
  GEN Q,Qt,idealz,gothf,factgothf,listpr,listex,factell,pp,p,pr,z,vecnul;
  GEN M,al,K,Msup,X,finalresult,y,cycpro;

  checkbnrgen(bnr);
  wk=gmael4(bnr,1,8,4,1);
  if (all) gell=stoi(all);
  else
  {
    if (!gcmp0(subgroup)) gell=det(subgroup);
    else gell=det(diagonal(gmael(bnr,5,2)));
  }
  if (gcmp1(gell)) { avma = av; return polx[varn(gmael3(bnr,1,7,1))]; }
  if (!isprime(gell)) err(impl,"kummer for composite relative degree");
  if (divise(wk,gell))
    return gerepileupto(av,rnfkummersimple(bnr,subgroup,all,prec));
  if (all && gcmp0(subgroup))
    err(talker,"kummer when zeta not in K requires a specific subgroup");
  bnf=(GEN)bnr[1];
  nf=(GEN)bnf[7];
  polnf=(GEN)nf[1]; vnf=varn(polnf); degK=degree(polnf);
  if (!vnf) err(talker,"main variable in kummer must not be x");
      /* step 7 */
  p1=conductor(bnr,subgroup,2,prec);
      /* fin step 7 */
  bnr=(GEN)p1[2];
  rayclgp=(GEN)bnr[5];
  raycyc=(GEN)rayclgp[2]; lraycyc=lg(raycyc)-1;
  bid=(GEN)bnr[2]; module=(GEN)bid[1];
  ideal=(GEN)module[1];
  if (gcmp0(subgroup)) subgroup = diagonal(raycyc);
  ell=itos(gell);
  unmodell=gmodulss(1,ell);
      /* step 1 of alg 5.3.5. */
  if (DEBUGLEVEL>=3) { fprintferr("Step 1\n"); flusherr(); }
  phiell=cyclo(ell,vnf);
  p1=(GEN)compositum2(polnf,phiell)[1];
  kk=(GEN)p1[4];
  R=(GEN)p1[1];
  A1=(GEN)p1[2];
  A2=(GEN)p1[3];
  if (signe(leadingcoeff(R))<0)
  {
    R=gneg_i(R); A1=gmodulcp(lift(A1),R); A2=gmodulcp(lift(A2),R);
  }
      /* step 2 */
  if (DEBUGLEVEL>=3) { fprintferr("Step 2\n"); flusherr(); }
  degKz=degree(R);
  m=degKz/degK;
  d=(ell-1)/m;
  g=lift(gpuigs(gener(gell),d));
  if (gcmp1(lift(gpuigs(gmodulcp(g,stoi(ell*ell)),m)))) g=addsi(ell,g);
      /* step reduction of R */
  if (degKz<=20)
  {
    GEN A3,A3rev;

    if (DEBUGLEVEL>=3) { fprintferr("Step reduction\n"); flusherr(); }
    p1=polredabs2(R,prec);
    if (DEBUGLEVEL>=3) { fprintferr("polredabs = ");outerr((GEN)p1[1]); }
    R=(GEN)p1[1];
    A3=(GEN)p1[2];
    A1=gsubst(lift(A1),vnf,A3);
    A2=gsubst(lift(A2),vnf,A3);
    A3rev=polymodrecip(A3);
    U=gadd(gpui(A2,g,0),gmul(kk,A1));
    U=gsubst(lift(A3rev),vnf,U);
  }
  else U=gadd(gpui(A2,g,0),gmul(kk,A1));
      /* step 3 */
      /* on peut factoriser disc(R) avec th. 2.1.6. */
  if (DEBUGLEVEL>=3) { fprintferr("Step 3\n"); flusherr(); }
  bnfz=bnfinit0(R,0,NULL,prec); nfz=(GEN)bnfz[7];
  clgp=gmael(bnfz,8,1);
  cyc=(GEN)clgp[2]; gc=lg(cyc)-1; gencyc=(GEN)clgp[3];
  for (j=1; j<=gc && divise((GEN)cyc[j],gell); j++);
  rc=j-1;
  vecalpha=cgetg(gc+1,t_VEC);
  for (j=1; j<=gc; j++)
  {
    p1 = idealpow(nfz,(GEN)gencyc[j],(GEN)cyc[j]);
    p1 = (GEN)isprincipalgenforce(bnfz, p1)[2];
    vecalpha[j] = (long)basistoalg(nfz, p1);
  }
  fununits = check_units(bnfz,"rnfkummer");
  torsunit = gmael3(bnfz,8,4,2);
  ru=(degKz>>1)-1;
  rv=rc+ru+1;
  vselmer=cgetg(rv+1,t_VEC);
  for (j=1; j<=rc; j++) vselmer[j]=vecalpha[j];
  for (   ; j<rv; j++) vselmer[j]=(long)gmodulcp((GEN)fununits[j-rc],R);
  vselmer[rv]=(long)gmodulcp((GEN)torsunit,R);
      /* computation of the uu(j) (see remark 5.2.15.) */
  uu=cgetg(gc+1,t_VEC);
  for (j=1; j<=rc; j++) uu[j]=zero;
  for (   ; j<=gc; j++) uu[j]=(long)lift(ginv(gmodulcp((GEN)cyc[j],gell)));
    /* step 4 */
  if (DEBUGLEVEL>=3) { fprintferr("Step 4\n"); flusherr(); }
  vecB=cgetg(rc+1,t_VEC);
  Tc=cgetg(rc+1,t_MAT);
  for (j=1; j<=rc; j++)
  {
    p1=isprincipalell(tauofideal((GEN)gencyc[j]));
    vecB[j]=p1[2];
    Tc[j]=p1[1];
  }
  p1=cgetg(m,t_VEC);
  p1[1]=(long)idmat(rc);
  for (j=2; j<=m-1; j++) p1[j]=lmul((GEN)p1[j-1],Tc);
  p2=cgetg(rc+1,t_VEC);
  for (j=1; j<=rc; j++) p2[j]=un;
  p3=vecB;
  for (j=1; j<=m-1; j++)
  {
    p3=gsubst(lift(p3),vnf,U);
    p4=groupproduct(grouppows(p3,(j*d)%ell),(GEN)p1[m-j]);
    for (i=1; i<=rc; i++) p2[i]=lmul((GEN)p2[i],(GEN)p4[i]);
  }
  vecC=p2;
      /* step 5 */
  if (DEBUGLEVEL>=3) { fprintferr("Step 5\n"); flusherr(); }
  Tv=cgetg(rv+1,t_MAT);
  for (j=1; j<=rv; j++)
  {
    Tv[j]=isvirtualunit(gsubst(lift((GEN)vselmer[j]),vnf,U))[1];
    if (DEBUGLEVEL>=3) { fprintferr("   %ld\n",j); flusherr(); }
  }
  P=lift(ker(gmul(unmodell,gsub(Tv,gmul(g,idmat(rv))))));
  dv=lg(P)-1;
  vecw=cgetg(dv+1,t_VEC);
  for (j=1; j<=dv; j++)
  {
    p1=gun;
    for (i=1; i<=rv; i++) p1=gmul(p1,gpui((GEN)vselmer[i],gcoeff(P,i,j),0));
    vecw[j]=(long)p1;
  }
      /* step 6 */
  if (DEBUGLEVEL>=3) { fprintferr("Step 6\n"); flusherr(); }
  Q=ker(gmul(unmodell,gsub(gtrans(Tc),gmul(g,idmat(rc)))));
  Qt=gtrans(Q);
  dc=lg(Q)-1;
      /* step 7 done above */
      /* step 8 */
  if (DEBUGLEVEL>=3) { fprintferr("Step 7 and 8\n"); flusherr(); }
  idealz=lifttokz(ideal);
  computematexpoteta1();
  if (!divise(idealnorm(nf,ideal),gell)) gothf=idealz;
  else
  {
    GEN subgroupz;

    polrel=computepolrel();
    steinitzZk=steinitzaux(idmat(degKz));
    subgroupz=invimsubgroup(bnr,subgroup,idealz,prec);
    gothf=conductor(bnrz,subgroupz,0,prec);
  }
      /* step 9 */
  if (DEBUGLEVEL>=3) { fprintferr("Step 9\n"); flusherr(); }
  factgothf=idealfactor(nfz,gothf);
  listpr=(GEN)factgothf[1]; listex=(GEN)factgothf[2]; llistpr=lg(listpr)-1;
  factell=primedec(nfz,gell); lfactell=lg(factell)-1;
      /* step 10 and step 11 */
  if (DEBUGLEVEL>=3) { fprintferr("Step 10 and 11\n"); flusherr(); }
  Sm=cgetg(1,t_VEC);Sml1=cgetg(1,t_VEC);Sml2=cgetg(1,t_VEC);Sl=cgetg(1,t_VEC);
  ESml2=cgetg(1,t_VEC);
  for (i=1; i<=llistpr; i++)
  {
    pp=cgetg(2,t_VEC); pp[1]=listpr[i];
    p=gmael(pp,1,1); e=itos(gmael(pp,1,3));
    if (!gegal(p,gell))
    {
      if (!gcmp1((GEN)listex[i])) { avma=av; return gzero; }
      if (!isconjinprimelist(Sm,(GEN)pp[1])) Sm=concatsp(Sm,pp);
    }
    else
    {
      vp=itos((GEN)listex[i]); vd=(vp-1)*(ell-1)-ell*e;
      if (vd > 0) { avma=av; return gzero; }
      if (vd==0)
      {
	if (!isconjinprimelist(Sml1,(GEN)pp[1])) Sml1=concatsp(Sml1,pp);
      }
      else
      {
	if (vp==1) { avma=av; return gzero; }
        if (!isconjinprimelist(Sml2,(GEN)pp[1]))
        {
          Sml2=concatsp(Sml2,pp); ESml2=concatsp(ESml2,(GEN)listex[i]);
        }
      }
    }
  }
  for (i=1; i<=lfactell; i++)
    if (!idealval(nfz,gothf,(GEN)factell[i]))
    {
      pp=cgetg(2,t_VEC); pp[1]=factell[i];
      if (!isconjinprimelist(Sl,(GEN)pp[1])) Sl=concatsp(Sl,pp);
    }
  lSml2=lg(Sml2)-1; lSl=lg(Sl)-1; lSl2=lSml2+lSl;
  Sp=concatsp(Sm,Sml1); lSp=lg(Sp)-1;
      /* step 12 */
  if (DEBUGLEVEL>=3) { fprintferr("Step 12\n"); flusherr(); }
  vecbetap=cgetg(lSp+1,t_VEC);
  vecalphap=cgetg(lSp+1,t_VEC);
  matP=cgetg(lSp+1,t_MAT);
  gg=gmodulcp(g,gell);
  for (j=1; j<=lSp; j++)
  {
    p1=isprincipalell((GEN)Sp[j]);
    matP[j]=p1[1];
    p2=gun;
    for (i=1; i<=rc; i++)
      p2=gmul(p2,gpui((GEN)vecC[i],gmael(p1,1,i),0));
    p3=gdiv((GEN)p1[2],p2); vecbetap[j]=(long)p3;
    p2=gun;
    for (i=0; i<m; i++)
    {
      p2=gmul(p2,gpui(p3,lift(gpuigs(gg,m-1-i)),0));
      if (i<m-1) p3=gsubst(lift(p3),vnf,U);
    }
    vecalphap[j]=(long)p2;
  }
      /* step 13 */
  if (DEBUGLEVEL>=3) { fprintferr("Step 13\n"); flusherr(); }
  nbcol=lSp+dv;
  vecw=concatsp(vecw,vecbetap);
  listmod=cgetg(lSl2+1,t_VEC);
  listunif=cgetg(lSl2+1,t_VEC);
  listprSp=cgetg(lSl2+1,t_VEC);
  for (j=1; j<=lSml2; j++)
  {
    pr=(GEN)Sml2[j]; z=addsi(1,mulsi(ell,divis((GEN)pr[3],ell-1)));
    listmod[j]=(long)idealpow(nfz,pr,gsub(z,(GEN)ESml2[j]));
    listunif[j]=(long)basistoalg(nfz,gdiv((GEN)pr[5],(GEN)pr[1]));
    listprSp[j]=(long)pr;
  }
  for (   ; j<=lSl2; j++)
  {
    pr=(GEN)Sl[j-lSml2]; z=mulsi(ell,divis((GEN)pr[3],ell-1));
    listmod[j]=(long)idealpow(nfz,pr,z);
    listunif[j]=(long)basistoalg(nfz,gdiv((GEN)pr[5],(GEN)pr[1]));
    listprSp[j]=(long)pr;
  }
      /* step 14 and step 15 */
  if (DEBUGLEVEL>=3) { fprintferr("Step 14 and 15\n"); flusherr(); }
  listbid=cgetg(lSl2+1,t_VEC);
  listellrank=cgetg(lSl2+1,t_VEC);
  for (i=1; i<=lSl2; i++)
  {
    listbid[i]=(long)zidealstarinitgen(nfz,(GEN)listmod[i]);
    cycpro=gmael3(listbid,i,2,2);
    for (j=1; (j<lg(cycpro)) && (divise((GEN)cycpro[j],gell)); j++);
    listellrank[i]=lstoi(j-1);
  }
  mginv=lift(gmulsg(m,ginv(gg)));
  vecnul=cgetg(dc+1,t_COL); for (i=1; i<=dc; i++) vecnul[i]=zero;
  M=cgetg(nbcol+1,t_MAT);
  for (j=1; j<=dv; j++)
  {
    p1=cgetg(1,t_COL);
    al=(GEN)vecw[j];
    for (ind=1; ind<=lSl2; ind++) p1=concatsp(p1,ideallogaux(ind,al));
    p1=gmul(mginv,p1);
    M[j]=(long)concatsp(p1,vecnul);
  }
  for (   ; j<=nbcol; j++)
  {
    p1=cgetg(1,t_COL);
    al=(GEN)vecalphap[j-dv];
    for (ind=1; ind<=lSl2; ind++) p1=concatsp(p1,ideallogaux(ind,al));
    M[j]=(long)concatsp(p1,gmul(Qt,(GEN)matP[j-dv]));
  }
  M=gmul(unmodell,M);
      /* step 16 */
  if (DEBUGLEVEL>=3) { fprintferr("Step 16\n"); flusherr(); }
  K=ker(M);
  dK=lg(K)-1;
  if (!dK) { avma=av; return gzero; }
      /* step 17 */
  if (DEBUGLEVEL>=3) { fprintferr("Step 17\n"); flusherr(); }
  listmodsup=cgetg(lSml2+1,t_VEC);
  listbidsup=cgetg(lSml2+1,t_VEC);
  listellranksup=cgetg(lSml2+1,t_VEC);
  for (j=1; j<=lSml2; j++)
  {
    listmodsup[j]=(long)idealmul(nfz,(GEN)listprSp[j],(GEN)listmod[j]);
    listbidsup[j]=(long)zidealstarinitgen(nfz,(GEN)listmodsup[j]);
    cycpro=gmael3(listbidsup,j,2,2);
    for (i=1; (i<lg(cycpro)) && (divise((GEN)cycpro[i],gell)); i++);
    listellranksup[j]=lstoi(i-1);
  }
  vecMsup=cgetg(lSml2+1,t_VEC);
  for (i=1; i<=lSml2; i++)
  {
    Msup=cgetg(nbcol+1,t_MAT); vecMsup[i]=(long)Msup;
    for (j=1; j<=dv; j++) Msup[j]=lmul(mginv,ideallogauxsup(i,(GEN)vecw[j]));
    for (   ; j<=nbcol; j++) Msup[j]=(long)ideallogauxsup(i,(GEN)vecalphap[j-dv]);
  }
      /* step 18 */
  if (DEBUGLEVEL>=3) { fprintferr("Step 18\n"); flusherr(); }
  do
  {
    y=cgetg(dK,t_VEC);
    for (i=1; i<dK; i++) y[i]=zero;
	/* step 19 */
    LAB19:
    X=(GEN)K[dK];
    for (j=1; j<dK; j++) X=gadd(X,gmul((GEN)y[j],(GEN)K[j]));
    finalresult=testx(subgroup,X,prec);
    if (!gcmp0(finalresult))
    {
      tetpil=avma; return gerepile(av,tetpil,gcopy(finalresult));
    }
	/* step 20 */
    i=dK;
	/* step 21 */
    LAB21:
    i--;
	/* step 22 */
    if (i)
    {
      y[i]=(long)addsi(1,(GEN)y[i]);
      if (i<dK-1) y[i+1]=zero;
      if (cmpii((GEN)y[i],gell) >= 0) goto LAB21; else goto LAB19;
    }
    dK--;
  }
  while (dK);
  avma=av; return gzero;
}
