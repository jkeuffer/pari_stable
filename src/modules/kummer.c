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
extern GEN check_and_build_cycgen(GEN bnf);
extern GEN get_arch_real(GEN nf,GEN x,GEN *emb,long prec);
extern GEN vecmul(GEN x, GEN y);
extern GEN vecinv(GEN x);
extern GEN T2_from_embed_norm(GEN x, long r1);
extern GEN pol_to_vec(GEN x, long N);
extern GEN famat_to_nf(GEN nf, GEN f);

static long rc,ell,degK,degKz,m,d,vnf,dv;
static GEN matexpoteta1,nf,raycyc,polnf;
static GEN bnfz,nfz,U,uu,gell,cyc,gencyc,vecalpha,R,g;
static GEN listmod,listprSp,listbid,listunif,listellrank;
static GEN listbidsup,listellranksup,vecw;

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
  long lB = lg(B),j;
  GEN c;

  c = cgetg(lB,t_VEC);
  for (j=1; j<lB; j++) c[j] = lpowgs((GEN)B[j], ex);
  return c;
}

static GEN
get_listx(GEN arch,GEN msign,GEN munit,GEN vecmunit2,long ell,long lSp,long lSml2,long nbvunit,long r1)
{
  GEN kermat,p2,p3,p4,y,yinit,listx;
  long i,j,k,cmpt,lker;

  kermat = FpM_ker(munit,gell); lker=lg(kermat)-1;
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
      p3 = gadd(p3, gmul((GEN)y[j],(GEN)kermat[j]));
    p3 = FpV_red(p3, gell);
    cmpt=0; for (j=1; j<=lSp; j++) if (gcmp0((GEN)p3[j+nbvunit])) cmpt++;
    if (!cmpt)
    {
      for (k=1; k<=lSml2; k++)
      {
        p4 = FpV_red(gmul((GEN)vecmunit2[k], p3), gell);
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
          p4 = FpV_red(gmul((GEN)vecmunit2[k], p3), gell);
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

  nf = checknf(nf);
  if (tx==t_POL || tx==t_POLMOD) y = algtobasis(nf,x);
  else { y = x; x = basistoalg(nf,y); }
  den = denom(y);
  if (gcmp1(den)) return x;
  fa = decomp(den); fac = (GEN)fa[1];ep = (GEN)fa[2];
  p1 = gun;
  for (i=1; i<lg(fac); i++)
    p1 = mulii(p1, powgi((GEN)fac[i], gceil(gdiv((GEN)ep[i],gell))));
  return gmul(powgi(p1, gell), x);
}

long
ellrank(GEN cyc, long ell)
{
  long i;
  for (i=1; i<lg(cyc); i++)
    if (smodis((GEN)cyc[i],ell)) break;
  return i-1;
}

static GEN
no_sol(long all, int i)
{
  if (!all) err(talker,"bug%d in kummer",i);
  return cgetg(1,t_VEC);
}

static void
_append(GEN x, GEN t)
{
  long l = lg(x); x[l] = (long)t; setlg(x, l+1);
}

/* si all!=0, donne toutes les equations correspondant a un sousgroupe
   de determinant all (i.e. de degre all) */
static GEN
rnfkummersimple(GEN bnr, GEN subgroup, long all)
{
  long r1,degnf,ell,j,i,l;
  long nbgenclK,lSml2,lSl,lSp,lastindex,nbvunit;
  long kmax,lastbid,nbcol,nblig,k,llistx,e,vp,vd;

  GEN bnf,nf,classgroup,cyclic,bid,ideal,arch,cycgen,gell,p1,p2,p3;
  GEN clK,cyclicK,genK,listgamma,listalpha,fa,prm,expom,Sm,Sml1,Sml2,Sl,ESml2;
  GEN p,factell,Sp,vecbeta,matexpo,vunit,id,pr,vsml2,vecalpha0;
  GEN cycpro,munit,vecmunit2,msign,archartif,listx,listal,listg,listgamma0;
  GEN vecbeta0;

  checkbnrgen(bnr); bnf=(GEN)bnr[1];
  nf=(GEN)bnf[7]; r1 = nf_get_r1(nf);
  polnf=(GEN)nf[1]; vnf=varn(polnf);
  if (vnf==0) err(talker,"main variable in kummer must not be x");
  p1=conductor(bnr,all ? gzero : subgroup,2);
  bnr=(GEN)p1[2]; if(!all) subgroup=(GEN)p1[3];
  classgroup=(GEN)bnr[5];
  cyclic=(GEN)classgroup[2];
  bid = (GEN)bnr[2];
  ideal= gmael(bid,1,1);
  arch = gmael(bid,1,2);
  if (!all && gcmp0(subgroup)) subgroup = diagonal(cyclic);
  degnf=lgef(polnf)-3;
  gell = all? stoi(all): det(subgroup);
  if (!isprime(gell))
    err(impl,"kummer for non prime relative degree");
  ell=itos(gell);
  clK=gmael(bnf,8,1); cyclicK=(GEN)clK[2]; genK=(GEN)clK[3];
  lastindex = ellrank(cyclicK,ell);
  nbgenclK = lg(genK)-1;
  listgamma0=cgetg(nbgenclK+1,t_VEC);
  listgamma=cgetg(nbgenclK+1,t_VEC);
  vecalpha0=cgetg(lastindex+1,t_VEC);
  listalpha=cgetg(lastindex+1,t_VEC);
  p1 = gmul(gell,ideal);
  cycgen = check_and_build_cycgen(bnf);
  for (i=1; i<=lastindex; i++)
  {
    p3 = basistoalg(nf,idealcoprime(nf,(GEN)genK[i],p1));
    listgamma[i] = listgamma0[i] = linv(p3);
    p2 = basistoalg(nf, famat_to_nf(nf, (GEN)cycgen[i]));
    vecalpha0[i]=(long)p2;
    listalpha[i] = lmul((GEN)vecalpha0[i], powgi(p3,(GEN)cyclicK[i]));
  }
  for (   ; i<=nbgenclK; i++)
  {
    long k;
    p3 = basistoalg(nf,idealcoprime(nf,(GEN)genK[i],p1));
    p2 = basistoalg(nf, famat_to_nf(nf, (GEN)cycgen[i]));
    k = itos(mpinvmod((GEN)cyclicK[i], gell));
    p2 = gpowgs(p2,k);
    listgamma0[i]= (long)p2;
    listgamma[i] = lmul(p2, gpowgs(p3, k * itos((GEN)cyclicK[i]) - 1));
  }
  /* a ce stade, module est egal au conducteur. */
  fa = idealfactor(nf,ideal);
  prm   = (GEN)fa[1];
  expom = (GEN)fa[2]; l = lg(prm);
  Sm  = cgetg(l,t_VEC); setlg(Sm,1);
  Sml1= cgetg(l,t_VEC); setlg(Sml1,1);
  Sml2= cgetg(l,t_VEC); setlg(Sml2,1);
  Sl  = cgetg(l+degnf,t_VEC); setlg(Sl,1);
  ESml2=cgetg(l,t_VECSMALL); setlg(ESml2,1);
  for (i=1; i<l; i++)
  {
    pr = (GEN)prm[i]; p = (GEN)pr[1]; e = itos((GEN)pr[3]);
    vp = itos((GEN)expom[i]);
    if (!egalii(p,gell))
    {
      if (vp != 1) return no_sol(all,1);
      _append(Sm, pr);
    }
    else
    {
      vd = (vp-1)*(ell-1)-ell*e;
      if (vd > 0) return no_sol(all,4);
      if (vd==0)
        _append(Sml1, pr);
      else
      {
	if (vp==1) return no_sol(all,2);
        _append(Sml2, pr);
        _append(ESml2,(GEN)vp);
      }
    }
  }
  factell = primedec(nf,gell); l = lg(factell);
  for (i=1; i<l; i++)
  {
    pr = (GEN)factell[i];
    if (!idealval(nf,ideal,pr)) _append(Sl, pr);
  }
  lSml2=lg(Sml2)-1; lSl=lg(Sl)-1;
  Sp = concatsp(Sm,Sml1); lSp = lg(Sp)-1;
  vecbeta = cgetg(lSp+1,t_VEC); matexpo=cgetg(lSp+1,t_MAT);
  vecbeta0= cgetg(lSp+1,t_VEC);
  for (j=1; j<=lSp; j++)
  {
    p1=isprincipalgenforce(bnf,(GEN)Sp[j]);
    p2=basistoalg(nf,(GEN)p1[2]);
    for (i=1; i<=lastindex; i++)
      p2 = gmul(p2, powgi((GEN)listgamma[i],gmael(p1,1,i)));
    p3 = p2;
    for (   ; i<=nbgenclK; i++)
    {
      p2 = gmul(p2, powgi((GEN)listgamma[i],gmael(p1,1,i)));
      p3 = gmul(p3, powgi((GEN)listgamma0[i],gmael(p1,1,i)));
    }
    matexpo[j]=(long)p1[1];
    vecbeta[j]=(long)p2; /* attention, ceci sont les beta modifies */
    vecbeta0[j]=(long)p3;
  }
  vunit=gmodulcp(concatsp(gmael(bnf,8,5),gmael3(bnf,8,4,2)),polnf);
  listg = vunit;
  for (i=1; i<=lastindex; i++) vunit = concatsp(vunit,(GEN)listalpha[i]);
  nbvunit=lg(vunit)-1;
  id=idmat(degnf);
  for (i=1; i<=lSl; i++)
  {
    pr = (GEN)Sl[i]; e = itos((GEN)pr[3]);
    id = idealmul(nf, id, idealpows(nf,pr,(ell*e)/(ell-1)));
  }
  vsml2=cgetg(lSml2+1,t_VEC);
  for (i=1; i<=lSml2; i++)
  {
    pr = (GEN)Sml2[i]; e = itos((GEN)pr[3]);
    kmax = (e*ell)/(ell-1) + 1 - ESml2[i];
    p1=idealpow(nf,pr,stoi(kmax));
    id=idealmul(nf,id,p1);
    p2=idealmul(nf,p1,pr);
    p3=zidealstarinitgen(nf,p2);
    vsml2[i] = (long)p3;
    cycpro = gmael(p3,2,2); l = lg(cycpro)-1;
    if (! gdivise((GEN)cycpro[l],gell)) err(talker,"bug5 in kummer");
  }
  bid = zidealstarinitgen(nf,id);
  lastbid = ellrank(gmael(bid,2,2), ell);
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
      mael(vecmunit2,k,j) = (long)zideallog(nf,(GEN)vunit[j],(GEN)vsml2[k]);
    msign[j] = (long)zsigne(nf,(GEN)vunit[j],archartif);
  }
  p1=cgetg(nbgenclK-lastindex+1,t_VEC);
  for (j=1; j<=lSp; j++)
  {
    p2=zideallog(nf,(GEN)vecbeta[j],bid);
    p3=cgetg(nblig+1,t_COL); munit[j+nbvunit]=(long)p3;
    for (i=1; i<=lastbid; i++) p3[i]=p2[i];
    for (   ; i<=nblig; i++) p3[i]=coeff(matexpo,i-lastbid,j);
    for (k=1; k<=lSml2; k++)
      mael(vecmunit2,k,j+nbvunit) = (long)zideallog(nf,(GEN)vecbeta[j],(GEN)vsml2[k]);
    msign[j+nbvunit]=(long)zsigne(nf,(GEN)vecbeta[j],archartif);
  }
  listx = get_listx(arch,msign,munit,vecmunit2,ell,lSp,lSml2,nbvunit,r1);
  llistx= lg(listx);
  listal= cgetg(llistx,t_VEC);
  listg = concatsp(listg, concatsp(vecalpha0,vecbeta0));
  l = lg(listg);
  for (i=1; i<llistx; i++)
  {
    p1 = gun; p2 = (GEN)listx[i];
    for (j=1; j<l; j++)
      p1 = gmul(p1, powgi((GEN)listg[j],(GEN)p2[j]));
    listal[i] = (long)reducealpha(nf,p1,gell);
  }
 /* A ce stade, tous les alpha dans la liste listal statisfont les
  * congruences, noncongruences et signatures, et ne sont pas des puissances
  * l-iemes donc x^l-alpha est irreductible, sa signature est correcte ainsi
  * que son discriminant relatif. Reste a determiner son groupe de normes. */
  if (DEBUGLEVEL) fprintferr("listalpha = %Z\n",listal);
  p2=cgetg(1,t_VEC);
  for (i=1; i<llistx; i++)
  {
    p1 = gsub(gpuigs(polx[0],ell), (GEN)listal[i]);
    if (all || gegal(rnfnormgroup(bnr,p1),subgroup)) p2 = concatsp(p2,p1);
  }
  if (all) return gcopy(p2);
  switch(lg(p2)-1)
  {
    case 0: err(talker,"bug 6: no equation found in kummer");
    case 1: break; /* OK */
    default: fprintferr("equations = \n%Z",p2);
      err(talker,"bug 7: more than one equation found in kummer");
  }
  return gcopy((GEN)p2[1]);
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
  GEN p1 = dummycopy(pr);

  p1[2] = (long)algtobasis(nfz, gsubst(gmul((GEN)nfz[7],(GEN)pr[2]),vnf,U));
  return gcoeff(idealfactor(nfz,prime_to_ideal(nfz,p1)),1,1);
}

static long
isprimeidealconj(GEN pr1, GEN pr2)
{
  GEN pr=pr1;

  do
  {
    if (gegal(pr,pr2)) return 1;
    pr = tauofprimeideal(pr);
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
computematexpoteta1(GEN A1, GEN R)
{
  long j;
  GEN Aj = polun[vnf];
  matexpoteta1 = cgetg(degK+1,t_MAT);
  for (j=1; j<=degK; j++)
  {
    matexpoteta1[j] = (long)pol_to_vec(Aj, degKz);
    if (j<degK) Aj = gmod(gmul(Aj,A1), R);
  }
}

static GEN
downtoK(GEN x)
{
  long i;
  GEN p2,p3;

  p2 = inverseimage(matexpoteta1, pol_to_vec(lift(x), degKz));
  if (lg(p2)==1) err(talker,"not an element of K in downtoK");
  p3 = (GEN)p2[degK];
  for (i=degK-1; i; i--) p3 = gadd((GEN)p2[i],gmul(polx[vnf],p3));
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
  long i, l = lg(vecalpha);
  GEN p1,p2,logdisc,be;

  p1=isprincipalgenforce(bnfz,id); logdisc=(GEN)p1[1];
  be=basistoalg(bnfz,(GEN)p1[2]);
  for (i=rc+1; i<l; i++)
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
  long llist,i,j,ex, l = lg(vecalpha);
  GEN p1,p2,listex,listpr,q,ga,eps,vecy,logdisc;

  p1=idealfactor(nfz,v);
  listex=(GEN)p1[2]; listpr=(GEN)p1[1]; llist=lg(listex)-1;
  q=idmat(degKz);
  for (i=1; i<=llist; i++)
  {
    ex = itos((GEN)listex[i]);
    if (ex%ell) err(talker,"not a virtual unit in isvirtualunit");
    q=idealmul(nfz,q,idealpow(nfz,(GEN)listpr[i],stoi(ex/ell)));
  }
  p1=isprincipalgenforce(bnfz,q); logdisc=(GEN)p1[1];
  ga=basistoalg(nfz,(GEN)p1[2]);
  for (j=rc+1; j<l; j++)
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
lifttokz(GEN id, GEN A1)
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
steinitzaux(GEN id, GEN polrel)
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
normrelz(GEN id, GEN polrel, GEN steinitzZk)
{
  GEN p1 = steinitzaux(idealhermite(nfz, id), polrel);
  return idealdiv(nf,p1,steinitzZk);
}

static GEN
invimsubgroup(GEN bnrz, GEN bnr, GEN subgroup)
{
  long l,j;
  GEN g,Plog,raycycz,rayclgpz,genraycycz,U,polrel,steinitzZk;

  polrel = computepolrel();
  steinitzZk = steinitzaux(idmat(degKz), polrel); 
  rayclgpz = (GEN)bnrz[5];
  raycycz   = (GEN)rayclgpz[2]; l=lg(raycycz);
  genraycycz= (GEN)rayclgpz[3];
  Plog = cgetg(l,t_MAT);
  for (j=1; j<l; j++)
  {
    g = normrelz((GEN)genraycycz[j],polrel,steinitzZk);
    Plog[j] = (long)isprincipalray(bnr, g);
  }
  U = (GEN)hnfall(concatsp(Plog, subgroup))[2];
  setlg(U, l); for (j=1; j<l; j++) setlg(U[j], l);
  return hnfmod(concatsp(U, diagonal(raycycz)), (GEN)raycycz[1]);
}

static GEN
ideallogaux(long i, GEN al)
{
  long llogli,valal;
  GEN p1;

  valal = element_val(nfz,al,(GEN)listprSp[i]);
  al = gmul(al,gpuigs((GEN)listunif[i],valal));
  p1 = zideallog(nfz,al,(GEN)listbid[i]);
  llogli = listellrank[i];
  setlg(p1,llogli+1); return p1;
}

static GEN
ideallogauxsup(long i, GEN al)
{
  long llogli,valal;
  GEN p1;

  valal = element_val(nfz,al,(GEN)listprSp[i]);
  al = gmul(al,gpuigs((GEN)listunif[i],valal));
  p1 = zideallog(nfz,al,(GEN)listbidsup[i]);
  llogli = listellranksup[i];
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
  GEN e,u,u1,u2,u3,p1,p2,p3,p4,zet,be1,be2,listr,s,veczi,vecci,powtaubet;

  switch (ell)
  {
    case 2: err(talker,"you should not be here in rnfkummer !!"); break;
    case 3: e=normtoK(be); u=tracetoK(be);
      return gsub(gmul(polx[0],gsub(gsqr(polx[0]),gmulsg(3,e))),gmul(e,u));
    case 5: e=normtoK(be);
      if (d==2)
      {
	u=tracetoK(gpuigs(be,3));
	p1=gadd(gmulsg(5,gsqr(e)), gmul(gsqr(polx[0]), gsub(gsqr(polx[0]),gmulsg(5,e))));
	return gsub(gmul(polx[0],p1),gmul(e,u));
      }
      else
      {
	be1=gsubst(lift(be),vnf,U);
        be2=gsubst(lift(be1),vnf,U);
	u1=tracetoK(gmul(be,be1));
        u2=tracetoK(gmul(gmul(be,be2),gsqr(be1)));
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
      zet=gmodulcp(polx[vnf], cyclo(ell,vnf));
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

static GEN
fix_be(GEN be, GEN u)
{
  GEN e,g, nf = checknf(bnfz), fu = gmael(bnfz,8,5);
  long i,lu;

  lu = lg(u);
  for (i=1; i<lu; i++)
  {
    if (!signe(u[i])) continue;
    e = mulsi(ell, (GEN)u[i]);
    g = gmodulcp((GEN)fu[i],(GEN)nf[1]);
    be = gmul(be, powgi(g, e));
  }
  return be;
}

static GEN
logarch2arch(GEN x, long r1, long prec)
{
  long i, lx = lg(x), tx = typ(x);
  GEN y = cgetg(lx, tx);

  if (tx == t_MAT)
  {
    for (i=1; i<lx; i++) y[i] = (long)logarch2arch((GEN)x[i], r1, prec);
    return y;
  }
  for (i=1; i<=r1;i++) y[i] = lexp((GEN)x[i],prec);
  for (   ; i<lx; i++) y[i] = lexp(gmul2n((GEN)x[i],-1),prec);
  return y;
}

/* multiply be by ell-th powers of units as to find small L2-norm for new be */
static GEN
reducebetanaive(GEN be, GEN b)
{
  long i,k,n,ru,r1, prec = nfgetprec(bnfz);
  GEN z,p1,p2,nmax,c, nf = checknf(bnfz);

  if (DEBUGLEVEL) fprintferr("reduce modulo (Z_K^*)^l\n");
  r1 = nf_get_r1(nf);
  if (!b) b = gmul(gmael(nf,5,1), algtobasis(nf,be));
  n = max((ell>>1), 3);
  z = cgetg(n+1, t_VEC);
  c = gmulgs(greal((GEN)bnfz[3]), ell);
  c = logarch2arch(c, r1, prec); /* = embeddings of fu^ell */
  c = gprec_w(gnorm(c), DEFAULTPREC);
  b = gprec_w(gnorm(b), DEFAULTPREC); /* need little precision */
  z[1] = (long)concatsp(c, vecinv(c));
  for (k=2; k<=n; k++) z[k] = (long) vecmul((GEN)z[1], (GEN)z[k-1]);
  nmax = T2_from_embed_norm(b, r1);
  ru = lg(c)-1; c = zerovec(ru);
  for(;;)
  {
    GEN B = NULL;
    long besti = 0, bestk = 0;
    for (k=1; k<=n; k++)
      for (i=1; i<=ru; i++)
      {
        p1 = vecmul(b, gmael(z,k,i));    p2 = T2_from_embed_norm(p1,r1);
        if (gcmp(p2,nmax) < 0) { B=p1; nmax=p2; besti=i; bestk = k; continue; }
        p1 = vecmul(b, gmael(z,k,i+ru)); p2 = T2_from_embed_norm(p1,r1);
        if (gcmp(p2,nmax) < 0) { B=p1; nmax=p2; besti=i; bestk =-k; }
      }
    if (!B) break;
    b = B; c[besti] = laddis((GEN)c[besti], bestk);
  }
  if (DEBUGLEVEL) fprintferr("unit exponents = %Z",c);
  return fix_be(be,c);
}

static GEN
reducebeta(GEN be)
{
  long j,ru, prec = nfgetprec(bnfz);
  GEN emb,z,u,matunit, nf = checknf(bnfz);

  if (gcmp1(gnorm(be))) return reducebetanaive(be,NULL);
  matunit = gmulgs(greal((GEN)bnfz[3]), ell); /* log. embeddings of fu^ell */
  for (;;)
  {
    z = get_arch_real(nf, be, &emb, prec);
    if (z) break;
    prec = (prec-1)<<1;
    if (DEBUGLEVEL) err(warnprec,"reducebeta",prec);
    nf = nfnewprec(nf,prec);
  }
  z = concatsp(matunit, z);
  u = lllintern(z, 1, prec);
  if (!u) return reducebetanaive(be,emb); /* shouldn't occur */
  ru = lg(u);
  for (j=1; j<ru; j++)
    if (smodis(gcoeff(u,ru-1,j), ell)) break; /* prime to ell */
  u = (GEN)u[j]; /* coords on (fu^ell, be) of a small generator */
  ru--; setlg(u, ru);
  be = powgi(be, (GEN)u[ru]);
  return reducebetanaive(fix_be(be, u), NULL);
}

/* cf. algo 5.3.18 */
static GEN
testx(GEN bnf, GEN X, GEN module, GEN subgroup, GEN vecMsup)
{
  long i,v,l,lX;
  GEN be,polrelbe,p1;

  X = FpV_red(X, gell);
  if (gcmp0(X)) return NULL;
  lX = lg(X);
  for (i=dv+1; i<lX; i++)
    if (gcmp0((GEN)X[i])) return NULL;
  l = lg(vecMsup);
  for (i=1; i<l; i++)
    if (gcmp0(FpV_red(gmul((GEN)vecMsup[i],X), gell))) return NULL;
  be = gun;
  for (i=1; i<lX; i++)
    be = gmul(be, powgi((GEN)vecw[i], (GEN)X[i]));
  if (DEBUGLEVEL>1) fprintferr("reducing beta = %Z\n",be);
  be = reducebeta(be);
  if (DEBUGLEVEL>1) fprintferr("beta reduced = %Z\n",be);
  polrelbe = computepolrelbeta(be);
  v = varn(polrelbe);
  p1 = unifpol((GEN)bnf[7],polrelbe,0);
  p1 = denom(gtovec(p1));
  polrelbe = gsubst(polrelbe,v, gdiv(polx[v],p1));
  polrelbe = gmul(polrelbe, gpowgs(p1, degree(polrelbe)));
  if (DEBUGLEVEL>1) fprintferr("polrelbe = %Z\n",polrelbe);
  p1 = rnfconductor(bnf,polrelbe,0);
  if (!gegal((GEN)p1[1],module) || !gegal((GEN)p1[3],subgroup)) return NULL;
  return polrelbe;
}

GEN
rnfkummer(GEN bnr, GEN subgroup, long all, long prec)
{
  long i,j,l,av=avma,e,vp,vd,dK,lSl,lSp,lSl2,lSml2,dc,ru,rv,nbcol;
  GEN p1,p2,p3,p4,wk,pr;
  GEN bnf,rayclgp,bid,ideal,cycgen,vselmer;
  GEN kk,clgp,fununits,torsunit,vecB,vecC,Tc,Tv,P;
  GEN Q,Qt,idealz,gothf,factgothf,listpr,listex,factell,p,vecnul;
  GEN M,al,K,Msup,X,finalresult,y,module,A1,A2,vecMsup;
  GEN listmodsup,vecalphap,vecbetap,mginv,matP,ESml2,Sp,Sm,Sml1,Sml2,Sl;

  checkbnrgen(bnr);
  wk = gmael4(bnr,1,8,4,1);
  if (all) gell=stoi(all);
  else
  {
    if (!gcmp0(subgroup)) gell=det(subgroup);
    else gell=det(diagonal(gmael(bnr,5,2)));
  }
  if (gcmp1(gell)) { avma = av; return polx[varn(gmael3(bnr,1,7,1))]; }
  if (!isprime(gell)) err(impl,"kummer for composite relative degree");
  if (divise(wk,gell))
    return gerepileupto(av,rnfkummersimple(bnr,subgroup,all));
  if (all && gcmp0(subgroup))
    err(talker,"kummer when zeta not in K requires a specific subgroup");
  bnf=(GEN)bnr[1];
  nf=(GEN)bnf[7];
  polnf=(GEN)nf[1]; vnf=varn(polnf); degK=degree(polnf);
  if (!vnf) err(talker,"main variable in kummer must not be x");
      /* step 7 */
  p1=conductor(bnr,subgroup,2);
      /* fin step 7 */
  bnr=(GEN)p1[2]; 
  subgroup=(GEN)p1[3];
  rayclgp=(GEN)bnr[5];
  raycyc=(GEN)rayclgp[2];
  bid=(GEN)bnr[2]; module=(GEN)bid[1];
  ideal=(GEN)module[1];
  if (gcmp0(subgroup)) subgroup = diagonal(raycyc);
  ell=itos(gell);
      /* step 1 of alg 5.3.5. */
  if (DEBUGLEVEL>2) fprintferr("Step 1\n");
  
  p1 = (GEN)compositum2(polnf, cyclo(ell,vnf))[1];
  R = (GEN)p1[1];
  A1= (GEN)p1[2];
  A2= (GEN)p1[3];
  kk= (GEN)p1[4];
  if (signe(leadingcoeff(R)) < 0)
  {
    R = gneg_i(R);
    A1 = gmodulcp(lift(A1),R);
    A2 = gmodulcp(lift(A2),R);
  }
      /* step 2 */
  if (DEBUGLEVEL>2) fprintferr("Step 2\n");
  degKz = degree(R);
  m = degKz/degK;
  d = (ell-1)/m;
  g = lift(gpuigs(gener(gell),d)); /* g has order m in all (Z/ell^k)^* */
  if (gcmp1(powmodulo(g, stoi(m), stoi(ell*ell)))) g = addsi(ell,g);
      /* step reduction of R */
  if (degKz<=20)
  {
    GEN A3,A3rev;

    if (DEBUGLEVEL>2) fprintferr("Step reduction\n");
    p1 = polredabs2(R,prec);
    if (DEBUGLEVEL>2) fprintferr("polredabs = %Z",p1[1]);
    R = (GEN)p1[1];
    A3= (GEN)p1[2];
    A1 = gsubst(lift(A1),vnf,A3);
    A2 = gsubst(lift(A2),vnf,A3);
    A3rev= polymodrecip(A3);
    U = gadd(powgi(A2,g), gmul(kk,A1));
    U = gsubst(lift(A3rev),vnf,U);
  }
  else U = gadd(powgi(A2,g), gmul(kk,A1));
      /* step 3 */
      /* one could factor disc(R) using th. 2.1.6. */
  if (DEBUGLEVEL>2) fprintferr("Step 3\n");
  bnfz = bnfinit0(R,1,NULL,prec);
  nfz = (GEN)bnfz[7];
  clgp = gmael(bnfz,8,1);
  cyc   = (GEN)clgp[2]; l = lg(cyc);
  gencyc= (GEN)clgp[3];
  rc = ellrank(cyc,ell);
  vecalpha=cgetg(l,t_VEC);
  cycgen = check_and_build_cycgen(bnfz);
  for (j=1; j<l; j++)
    vecalpha[j] = (long)basistoalg(nfz, famat_to_nf(nfz, (GEN)cycgen[j]));
      /* computation of the uu(j) (see remark 5.2.15.) */
  uu = cgetg(l,t_VEC);
  for (j=1; j<=rc; j++) uu[j] = zero;
  for (   ; j<  l; j++) uu[j] = lmpinvmod((GEN)cyc[j], gell);

  fununits = check_units(bnfz,"rnfkummer");
  torsunit = gmael3(bnfz,8,4,2);
  ru=(degKz>>1)-1;
  rv=rc+ru+1;
  vselmer = cgetg(rv+1,t_VEC);
  for (j=1; j<=rc; j++) vselmer[j] = vecalpha[j];
  for (   ; j< rv; j++) vselmer[j] = lmodulcp((GEN)fununits[j-rc],R);
  vselmer[rv]=(long)gmodulcp((GEN)torsunit,R);
    /* step 4 */
  if (DEBUGLEVEL>2) fprintferr("Step 4\n");
  vecB=cgetg(rc+1,t_VEC);
  Tc=cgetg(rc+1,t_MAT);
  for (j=1; j<=rc; j++)
  {
    p1=isprincipalell(tauofideal((GEN)gencyc[j]));
    vecB[j] = p1[2];
    Tc[j] = p1[1];
  }
  p1=cgetg(m,t_VEC);
  p1[1]=(long)idmat(rc);
  for (j=2; j<=m-1; j++) p1[j]=lmul((GEN)p1[j-1],Tc);
  p2=cgetg(rc+1,t_VEC);
  for (j=1; j<=rc; j++) p2[j]=un;
  p3=vecB;
  for (j=1; j<=m-1; j++)
  {
    p3 = gsubst(lift(p3),vnf,U);
    p4 = groupproduct(grouppows(p3,(j*d)%ell),(GEN)p1[m-j]);
    for (i=1; i<=rc; i++) p2[i] = lmul((GEN)p2[i],(GEN)p4[i]);
  }
  vecC=p2;
      /* step 5 */
  if (DEBUGLEVEL>2) fprintferr("Step 5\n");
  Tv=cgetg(rv+1,t_MAT);
  for (j=1; j<=rv; j++)
  {
    Tv[j]=isvirtualunit(gsubst(lift((GEN)vselmer[j]),vnf,U))[1];
    if (DEBUGLEVEL>2) fprintferr("   %ld\n",j);
  }
  P = FpM_ker(gsub(Tv, g), gell);
  dv=lg(P)-1;
  vecw=cgetg(dv+1,t_VEC);
  for (j=1; j<=dv; j++)
  {
    p1=gun;
    for (i=1; i<=rv; i++) p1=gmul(p1,gpui((GEN)vselmer[i],gcoeff(P,i,j),0));
    vecw[j]=(long)p1;
  }
      /* step 6 */
  if (DEBUGLEVEL>2) fprintferr("Step 6\n");
  Q = FpM_ker(gsub(gtrans(Tc), g), gell);
  Qt = gtrans(Q); dc = lg(Q)-1;
      /* step 7 done above */
      /* step 8 */
  if (DEBUGLEVEL>2) fprintferr("Step 7 and 8\n");
  idealz=lifttokz(ideal, A1);
  computematexpoteta1(lift(A1), R);
  if (!divise(idealnorm(nf,ideal),gell)) gothf = idealz;
  else
  {
    GEN bnrz, subgroupz;
    bnrz = buchrayinitgen(bnfz,idealz);
    subgroupz = invimsubgroup(bnrz,bnr,subgroup);
    gothf = conductor(bnrz,subgroupz,0);
  }
      /* step 9 */
  if (DEBUGLEVEL>2) fprintferr("Step 9\n");
  factgothf=idealfactor(nfz,gothf);
  listpr = (GEN)factgothf[1];
  listex = (GEN)factgothf[2]; l = lg(listpr);
      /* step 10 and step 11 */
  if (DEBUGLEVEL>2) fprintferr("Step 10 and 11\n");
  Sm  = cgetg(l,t_VEC); setlg(Sm,1);
  Sml1= cgetg(l,t_VEC); setlg(Sml1,1);
  Sml2= cgetg(l,t_VEC); setlg(Sml2,1);
  Sl  = cgetg(l+degKz,t_VEC); setlg(Sl,1);
  ESml2=cgetg(l,t_VECSMALL); setlg(ESml2,1);
  for (i=1; i<l; i++)
  {
    pr = (GEN)listpr[i]; p = (GEN)pr[1]; e = itos((GEN)pr[3]);
    vp = itos((GEN)listex[i]);
    if (!egalii(p,gell))
    {
      if (vp != 1) { avma = av; return gzero; }
      if (!isconjinprimelist(Sm,pr)) _append(Sm,pr);
    }
    else
    {
      vd = (vp-1)*(ell-1)-ell*e;
      if (vd > 0) { avma = av; return gzero; }
      if (vd==0)
      {
	if (!isconjinprimelist(Sml1,pr)) _append(Sml1, pr);
      }
      else
      {
	if (vp==1) { avma = av; return gzero; }
        if (!isconjinprimelist(Sml2,pr))
        {
          _append(Sml2, pr);
          _append(ESml2,(GEN)vp);
        }
      }
    }
  }
  factell = primedec(nfz,gell); l = lg(factell);
  for (i=1; i<l; i++)
  {
    pr = (GEN)factell[i];
    if (!idealval(nfz,gothf,pr))
      if (!isconjinprimelist(Sl,pr)) _append(Sl, pr);
  }
  lSml2=lg(Sml2)-1; lSl=lg(Sl)-1; lSl2=lSml2+lSl;
  Sp=concatsp(Sm,Sml1); lSp=lg(Sp)-1;
      /* step 12 */
  if (DEBUGLEVEL>2) fprintferr("Step 12\n");
  vecbetap=cgetg(lSp+1,t_VEC);
  vecalphap=cgetg(lSp+1,t_VEC);
  matP=cgetg(lSp+1,t_MAT);
  for (j=1; j<=lSp; j++)
  {
    p1=isprincipalell((GEN)Sp[j]);
    matP[j]=p1[1];
    p2=gun;
    for (i=1; i<=rc; i++)
      p2 = gmul(p2, powgi((GEN)vecC[i],gmael(p1,1,i)));
    p3=gdiv((GEN)p1[2],p2); vecbetap[j]=(long)p3;
    p2=gun;
    for (i=0; i<m; i++)
    {
      p2 = gmul(p2, powgi(p3, powmodulo(g,stoi(m-1-i),gell)));
      if (i<m-1) p3=gsubst(lift(p3),vnf,U);
    }
    vecalphap[j]=(long)p2;
  }
      /* step 13 */
  if (DEBUGLEVEL>2) fprintferr("Step 13\n");
  nbcol=lSp+dv;
  vecw=concatsp(vecw,vecbetap);
  listmod=cgetg(lSl2+1,t_VEC);
  listunif=cgetg(lSl2+1,t_VEC);
  listprSp = concatsp(Sml2, Sl);
  for (j=1; j<=lSl2; j++)
  {
    GEN pr = (GEN)listprSp[j];
    long e = itos((GEN)pr[3]), z = ell * (e / (ell-1));
    if (j <= lSml2) z += 1 - ESml2[j];
    listmod[j]=(long)idealpows(nfz,pr, z);
    listunif[j]=(long)basistoalg(nfz,gdiv((GEN)pr[5],(GEN)pr[1]));
  }
      /* step 14 and step 15 */
  if (DEBUGLEVEL>2) fprintferr("Step 14 and 15\n");
  listbid=cgetg(lSl2+1,t_VEC);
  listellrank = cgetg(lSl2+1,t_VECSMALL);
  for (i=1; i<=lSl2; i++)
  {
    listbid[i]=(long)zidealstarinitgen(nfz,(GEN)listmod[i]);
    listellrank[i] = ellrank(gmael3(listbid,i,2,2), ell);
  }
  mginv = modii(mulsi(m, mpinvmod(g,gell)), gell);
  vecnul=cgetg(dc+1,t_COL); for (i=1; i<=dc; i++) vecnul[i]=zero;
  M=cgetg(nbcol+1,t_MAT);
  for (j=1; j<=dv; j++)
  {
    p1=cgetg(1,t_COL);
    al=(GEN)vecw[j];
    for (i=1; i<=lSl2; i++) p1 = concatsp(p1,ideallogaux(i,al));
    p1=gmul(mginv,p1);
    M[j]=(long)concatsp(p1,vecnul);
  }
  for (   ; j<=nbcol; j++)
  {
    p1=cgetg(1,t_COL);
    al=(GEN)vecalphap[j-dv];
    for (i=1; i<=lSl2; i++) p1 = concatsp(p1,ideallogaux(i,al));
    M[j]=(long)concatsp(p1,gmul(Qt,(GEN)matP[j-dv]));
  }
      /* step 16 */
  if (DEBUGLEVEL>2) fprintferr("Step 16\n");
  K = FpM_ker(M, gell);
  dK= lg(K)-1; if (!dK) { avma=av; return gzero; }
      /* step 17 */
  if (DEBUGLEVEL>2) fprintferr("Step 17\n");
  listmodsup=cgetg(lSml2+1,t_VEC);
  listbidsup=cgetg(lSml2+1,t_VEC);
  listellranksup=cgetg(lSml2+1,t_VECSMALL);
  for (i=1; i<=lSml2; i++)
  {
    listmodsup[i]=(long)idealmul(nfz,(GEN)listprSp[i],(GEN)listmod[i]);
    listbidsup[i]=(long)zidealstarinitgen(nfz,(GEN)listmodsup[i]);
    listellranksup[i] = ellrank(gmael3(listbidsup,i,2,2), ell);
  }
  vecMsup=cgetg(lSml2+1,t_VEC);
  for (i=1; i<=lSml2; i++)
  {
    Msup=cgetg(nbcol+1,t_MAT); vecMsup[i]=(long)Msup;
    for (j=1; j<=dv; j++) Msup[j]=lmul(mginv,ideallogauxsup(i,(GEN)vecw[j]));
    for (   ; j<=nbcol; j++) Msup[j]=(long)ideallogauxsup(i,(GEN)vecalphap[j-dv]);
  }
      /* step 18 */
  if (DEBUGLEVEL>2) fprintferr("Step 18\n");
  do
  {
    y=cgetg(dK,t_VEC);
    for (i=1; i<dK; i++) y[i]=zero;
	/* step 19 */
    LAB19:
    X = (GEN)K[dK];
    for (j=1; j<dK; j++) X = gadd(X, gmul((GEN)y[j],(GEN)K[j]));
    finalresult = testx(bnf,X,module,subgroup,vecMsup);
    if (finalresult) return gerepileupto(av, gcopy(finalresult));
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
