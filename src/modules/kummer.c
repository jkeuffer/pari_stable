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
#include "parinf.h"
extern GEN check_and_build_cycgen(GEN bnf);
extern GEN get_arch_real(GEN nf,GEN x,GEN *emb,long prec);
extern GEN vecmul(GEN x, GEN y);
extern GEN vecinv(GEN x);
extern GEN T2_from_embed_norm(GEN x, long r1);
extern GEN pol_to_vec(GEN x, long N);
extern GEN famat_to_nf(GEN nf, GEN f);
extern GEN vconcat(GEN A, GEN B);
extern long int_elt_val(GEN nf, GEN x, GEN p, GEN b, GEN *newx);
    

static long rc,ell,degK,degKz,m,d,vnf;
static GEN invexpoteta1,nfz,gell;

/* row vector B x matrix T : c_j=prod_i (b_i^T_ij) */
static GEN
groupproduct(GEN B, GEN T)
{
  long i,j, lB = lg(B), lT = lg(T);
  GEN c = cgetg(lT,t_VEC);
 
  for (j=1; j<lT; j++)
  {
    GEN p1 = gun;
    for (i=1; i<lB; i++) p1 = gmul(p1, powgi((GEN)B[i],gcoeff(T,i,j)));
    c[j] = (long)p1;
  }
  return c;
}

static int
ok_x(GEN X, GEN arch, GEN vecmunit2, GEN msign)
{
  long i, l = lg(vecmunit2);
  GEN p1;
  for (i=1; i<l; i++)
  {
    p1 = FpV_red(gmul((GEN)vecmunit2[i], X), gell);
    if (gcmp0(p1)) return 0;
  }
  p1 = lift(gmul(msign,X)); settyp(p1,t_VEC);
  return gegal(p1, arch);
}

static GEN
get_listx(GEN arch,GEN msign,GEN munit,GEN vecmunit2,long ell,long lSp,long nbvunit)
{
  GEN kermat,p2,X,y, listx = cgetg(1,t_VEC);
  long i,j,cmpt,lker;

  kermat = FpM_ker(munit,gell); lker=lg(kermat)-1;
  if (!lker) return listx;
  y = cgetg(lker,t_VECSMALL);
  for (i=1; i<lker; i++) y[i] = 0;
  for(;;)
  {
    p2 = cgetg(2,t_VEC);
    X = (GEN)kermat[lker];
    for (j=1; j<lker; j++) X = gadd(X, gmulsg(y[j],(GEN)kermat[j]));
    X = FpV_red(X, gell);
    cmpt = 0; for (j=1; j<=lSp; j++) if (gcmp0((GEN)X[j+nbvunit])) cmpt++;
    if (!cmpt)
    {
      if (ok_x(X, arch, vecmunit2, msign))
        { p2[1] = (long)X; listx = concatsp(listx,p2); }
    }
    if (!lSp)
    {
      j = 1; while (j<lker && !y[j]) j++;
      if (j<lker && y[j] == 1)
      {
        X = gsub(X,(GEN)kermat[lker]);
        if (ok_x(X, arch, vecmunit2, msign))
          { p2[1] = (long)X; listx = concatsp(listx,p2); }
      }
    }
    i = lker;
    do
    {
      i--; if (!i) return listx;
      if (i < lker-1) y[i+1] = 0;
      y[i]++;
    }
    while (y[i] >= ell);
  }
}

/* given x in nf -- possibly not integral -- compute an algebraic integer
 * of the form x * y^gell */
static GEN
reducealpha(GEN nf,GEN x,GEN gell)
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
prank(GEN cyc, long ell)
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
  long r1, degnf, ell, j, i, l;
  long nbgenclK, lSml2, lSl, lSl2, lSp, rc, nbvunit;
  long lastbid, llistx, e, vp, vd;

  GEN polnf,bnf,nf,bid,ideal,arch,cycgen,gell,p1,p2,p3;
  GEN cyclicK,genK,listgamma,listalpha,fa,prm,expom,Sm,Sml1,Sml2,Sl,ESml2;
  GEN p,factell,Sp,listprSp,vecbeta,matexpo,vunit,id,pr,vecalpha0;
  GEN munit,vecmunit2,msign,archartif,listx,listal,listg,listgamma0;
  GEN vecbeta0,vunit_beta,fununits,torsunit;

  checkbnrgen(bnr);
  bnf = (GEN)bnr[1];
  nf = (GEN)bnf[7]; r1 = nf_get_r1(nf);
  polnf = (GEN)nf[1]; vnf = varn(polnf); degnf = degpol(polnf);
  if (vnf==0) err(talker,"main variable in kummer must not be x");

  p1 = conductor(bnr,all ? gzero : subgroup,2);
  bnr = (GEN)p1[2];
  if (!all) subgroup = (GEN)p1[3];
  
  bid = (GEN)bnr[2];
  ideal= gmael(bid,1,1);
  arch = gmael(bid,1,2); /* this is the conductor */
  if (!all && gcmp0(subgroup)) subgroup = diagonal(gmael(bnr,5,2));
  gell = all? stoi(all): det(subgroup);
  ell = itos(gell);

  cyclicK= gmael3(bnf,8,1,2); rc = prank(cyclicK,ell);
  genK   = gmael3(bnf,8,1,3); nbgenclK = lg(genK)-1;
  listgamma0=cgetg(nbgenclK+1,t_VEC);
  listgamma=cgetg(nbgenclK+1,t_VEC);
  vecalpha0=cgetg(rc+1,t_VEC);
  listalpha=cgetg(rc+1,t_VEC);
  cycgen = check_and_build_cycgen(bnf);
  p1 = gmul(gell,ideal);
  for (i=1; i<=rc; i++)
  {
    p3 = basistoalg(nf,idealcoprime(nf,(GEN)genK[i],p1));
    p2 = basistoalg(nf, famat_to_nf(nf, (GEN)cycgen[i]));
    listgamma[i] = listgamma0[i] = linv(p3);
    vecalpha0[i] = (long)p2;
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
  fa = (GEN)bid[3];
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
  lSml2 = lg(Sml2)-1; lSl = lg(Sl)-1; lSl2 = lSml2+lSl;
  Sp = concatsp(Sm,Sml1); lSp = lg(Sp)-1;
  vecbeta = cgetg(lSp+1,t_VEC); matexpo=cgetg(lSp+1,t_MAT);
  vecbeta0= cgetg(lSp+1,t_VEC);
  for (j=1; j<=lSp; j++)
  {
    p1 = isprincipalgenforce(bnf,(GEN)Sp[j]);
    p2 = basistoalg(nf,(GEN)p1[2]);
    p1 = (GEN)p1[1];
    for (i=1; i<=rc; i++)
      p2 = gmul(p2, powgi((GEN)listgamma[i], (GEN)p1[i]));
    p3 = p2;
    for (   ; i<=nbgenclK; i++)
    {
      p2 = gmul(p2, powgi((GEN)listgamma[i], (GEN)p1[i]));
      p3 = gmul(p3, powgi((GEN)listgamma0[i],(GEN)p1[i]));
    }
    matexpo[j] = (long)p1; setlg(p1, rc+1);
    vecbeta[j] = (long)p2; /* attention, ceci sont les beta modifies */
    vecbeta0[j]= (long)p3;
  }
  fununits = check_units(bnf,"rnfkummer");
  torsunit = gmael3(bnf,8,4,2);
  listg = gmodulcp(concatsp(fununits,torsunit),polnf);
  vunit = concatsp(listg, listalpha);

  vunit_beta = algtobasis(nf, concatsp(vunit, vecbeta));
  l = lg(vunit_beta);
{
  long prec = DEFAULTPREC +
    ((gexpo(vunit_beta) + gexpo(gmael(nf,5,1))) >> TWOPOTBYTES_IN_LONG);
  if (nfgetprec(nf) < prec) nf = nfnewprec(nf, prec);
}

  vecmunit2 = cgetg(lSml2+1,t_VEC);
  listprSp = concatsp(Sml2, Sl);
  id = idmat(degnf);
  for (i=1; i<=lSl2; i++)
  {
    GEN pr = (GEN)listprSp[i];
    long e = itos((GEN)pr[3]), z = ell * (e / (ell-1));

    if (i <= lSml2)
    {
      GEN c, cyc;
      z += 1 - ESml2[i];
      bid = zidealstarinitgen(nf, idealpows(nf, pr, z+1));
      cyc = gmael(bid,2,2);
      if (smodis((GEN)cyc[lg(cyc)-1], ell)) err(talker,"bug5 in kummer");

      c = cgetg(l,t_MAT); vecmunit2[i] = (long)c;
      for (j=1; j<l; j++) c[j] = (long)zideallog(nf,(GEN)vunit_beta[j],bid);
    }
    id = idealmulpowprime(nf, id, pr, stoi(z));
  }
  nbvunit = lg(vunit)-1;
  matexpo = concatsp(zeromat(rc,nbvunit), matexpo);
  archartif = cgetg(r1+1,t_VEC); for (j=1; j<=r1; j++) archartif[j] = un;
  munit = cgetg(l, t_MAT);
  msign = cgetg(l, t_MAT);
  bid = zidealstarinitgen(nf, id);
  lastbid = prank(gmael(bid,2,2), ell);
  for (j=1; j<l; j++)
  {
    GEN z = (GEN)vunit_beta[j];
    p1 = zideallog(nf,z,bid); setlg(p1, lastbid+1);
    munit[j] = (long)concatsp(p1, (GEN)matexpo[j]);
    msign[j] = (long)zsigne(nf, z, archartif);
  }

  listx = get_listx(arch,msign,munit,vecmunit2,ell,lSp,nbvunit);
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
  p2 = cgetg(1,t_VEC);
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
tauofelt(GEN nf, GEN x, GEN U)
{
  return algtobasis(nfz, gsubst(gmul((GEN)nf[7],x),vnf,U));
}
static GEN
tauofalg(GEN x, GEN U)
{
  return gsubst(lift(x),vnf,U);
}

static GEN
lifttoKz(GEN nfz, GEN nf, GEN id, GEN A1)
{
  GEN I = ideal_two_elt(nf,id);
  I[2] = (long)tauofelt(nf,(GEN)I[2],A1);
  return prime_to_ideal(nfz,I);
}


static GEN
tauofideal(GEN id, GEN U)
{
  GEN I = ideal_two_elt(nfz,id);
  I[2] = (long)tauofelt(nfz,(GEN)I[2],U);
  return prime_to_ideal(nfz,I);
}

static int
isprimeidealconj(GEN pr1, GEN pr2, GEN U)
{
  GEN p = (GEN)pr1[1];
  GEN x = (GEN)pr1[2];
  GEN b1= (GEN)pr1[5];
  GEN b2= (GEN)pr2[5];
  if (!egalii(p, (GEN)pr2[1])
   || !egalii((GEN)pr1[3], (GEN)pr2[3])
   || !egalii((GEN)pr1[4], (GEN)pr2[4])) return 0;
  if (gegal(x,(GEN)pr2[2])) return 1;
  for(;;)
  {
    if (int_elt_val(nfz,x,p,b2,NULL)) return 1;
    x = FpV_red(tauofelt(nfz,x,U), p);
    if (int_elt_val(nfz,x,p,b1,NULL)) return 0;
  }
}

static int
isconjinprimelist(GEN S, GEN pr2, GEN U)
{
  long lS=lg(S),i;

  for (i=1; i<lS; i++)
    if (isprimeidealconj((GEN)S[i],pr2,U)) return 1;
  return 0;
}

static GEN
downtoK(GEN polnf, GEN x)
{
  GEN y = gmul(invexpoteta1, pol_to_vec(lift(x), degKz));
  return gmodulcp(gtopolyrev(y,vnf),polnf);
}

static GEN
tracetoK(GEN polnf, GEN x, GEN U)
{
  GEN p1 = x;
  long i;
  for (i=1; i<m; i++) p1 = gadd(x, tauofalg(p1,U));
  return downtoK(polnf,p1);
}

static GEN
normtoK(GEN polnf, GEN x, GEN U)
{
  GEN p1 = x;
  long i;
  for (i=1; i<m; i++) p1 = gmul(x, tauofalg(p1,U));
  return downtoK(polnf,p1);
}

static GEN
computepolrel(GEN polnf, GEN be, GEN U)
{
  GEN p1 = gun, p2 = be;
  long i,j;

  for (i=0; i<m; i++)
  {
    p1 = gmul(p1,gsub(polx[0],p2));
    if (i<m-1) p2 = tauofalg(p2,U);
  }
  for (j=2; j<=m+2; j++) p1[j]=(long)downtoK(polnf,(GEN)p1[j]);
  return p1;
}

/* alg. 5.2.15. with remark */
static GEN
isprincipalell(GEN bnfz, GEN id, GEN vecalpha, GEN uu)
{
  long i, l = lg(vecalpha);
  GEN y,logdisc,be;

  y = isprincipalgenforce(bnfz,id);
  logdisc = gmod((GEN)y[1], gell);
  be = basistoalg(bnfz,(GEN)y[2]);
  for (i=rc+1; i<l; i++)
    be = gmul(be, powgi((GEN)vecalpha[i], modii(mulii((GEN)logdisc[i],(GEN)uu[i]),gell)));
  y = cgetg(3,t_VEC);
  y[1]=(long)logdisc; setlg(logdisc,rc+1);
  y[2]=(long)be;
  return y;
}

/* alg. 5.3.11. */
static GEN
isvirtualunit(GEN bnfz, GEN v, GEN vecalpha, GEN cyc)
{
  long llist,i,j,ex, l = lg(vecalpha);
  GEN p1,listex,listpr,q,ga,eps,vecy,logdisc;

  p1=idealfactor(nfz,v);
  listpr = (GEN)p1[1]; llist = lg(listpr)-1;
  listex = (GEN)p1[2]; q = gun;
  for (i=1; i<=llist; i++)
  {
    ex = itos((GEN)listex[i]);
    if (ex%ell) err(talker,"not a virtual unit in isvirtualunit");
    q = idealmul(nfz,q, idealpows(nfz,(GEN)listpr[i], ex/ell));
  }
  /* q^ell = (v) */
  p1 = isprincipalgenforce(bnfz,q);
  logdisc = (GEN)p1[1];
  ga = basistoalg(nfz,(GEN)p1[2]);
  for (j=rc+1; j<l; j++)
    ga = gmul(ga, powgi((GEN)vecalpha[j],divii((GEN)logdisc[j],(GEN)cyc[j])));
  eps = gpuigs(ga,ell);
  vecy = cgetg(rc+1,t_COL);
  for (j=1; j<=rc; j++)
  {
    vecy[j] = (long)divii((GEN)logdisc[j], divii((GEN)cyc[j],gell));
    eps = gmul(eps, powgi((GEN)vecalpha[j],(GEN)vecy[j]));
  }
  eps = gdiv(v,eps);
  p1 = cgetg(3,t_VEC);
  p1[1] = (long)concatsp(vecy, lift(isunit(bnfz,eps)));
  p1[2] = (long)ga;
  return p1;
}

static GEN
steinitzaux(GEN nf, GEN id, GEN polrel)
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
normrelz(GEN nf, GEN id, GEN polrel, GEN steinitzZk)
{
  GEN p1 = steinitzaux(nf,idealhermite(nfz, id), polrel);
  return idealdiv(nf,p1,steinitzZk);
}

static GEN
invimsubgroup(GEN bnrz, GEN bnr, GEN subgroup, GEN tau)
{
  long l,j;
  GEN g,Plog,raycycz,rayclgpz,genraycycz,U,polrel,steinitzZk;
  GEN nf = checknf(bnr);

  polrel = computepolrel((GEN)nf[1], polx[vnf], tau);
  steinitzZk = steinitzaux(nf,idmat(degKz), polrel); 
  rayclgpz = (GEN)bnrz[5];
  raycycz   = (GEN)rayclgpz[2]; l=lg(raycycz);
  genraycycz= (GEN)rayclgpz[3];
  Plog = cgetg(l,t_MAT);
  for (j=1; j<l; j++)
  {
    g = normrelz(nf,(GEN)genraycycz[j],polrel,steinitzZk);
    Plog[j] = (long)isprincipalray(bnr, g);
  }
  U = (GEN)hnfall(concatsp(Plog, subgroup))[2];
  setlg(U, l); for (j=1; j<l; j++) setlg(U[j], l);
  return hnfmod(concatsp(U, diagonal(raycycz)), (GEN)raycycz[1]);
}

static GEN
vectau(GEN list)
{
  long i,j,k,n;
  GEN listz,listc,yz,yc,listfl,s, y = cgetg(3,t_VEC);

  listz = (GEN)list[1];
  listc = (GEN)list[2]; n = lg(listz);
  yz = cgetg(n,t_VEC); y[1] = (long)yz;
  yc = cgetg(n,t_VEC); y[2] = (long)yc;
  listfl=cgetg(n,t_VECSMALL); for (i=1; i<n; i++) listfl[i] = 1;
  k = 1;
  for (i=1; i<n; i++)
  {
    if (!listfl[i]) continue;

    yz[k] = listz[i];
    s = (GEN)listc[i];
    for (j=i+1; j<n; j++)
    {
      if (listfl[j] && gegal((GEN)listz[j],(GEN)listz[i]))
      {
        s = gadd(s,(GEN)listc[j]);
        listfl[j] = 0;
      }
    }
    yc[k] = (long)s; k++;
  }
  setlg(yz, k);
  setlg(yc, k); return y;
}

static GEN
subtau(GEN listx, GEN listy)
{
  GEN y = cgetg(3,t_VEC);
  y[1] = (long)concatsp((GEN)listx[1], (GEN)listy[1]);
  y[2] = (long)concatsp((GEN)listx[2], gneg_i((GEN)listy[2]));
  return vectau(y);
}

static GEN
negtau(GEN list)
{
  GEN y = cgetg(3,t_VEC);
  y[1] = list[1];
  y[2] = lneg((GEN)list[2]);
  return y;
}

static GEN
multau(GEN listx, GEN listy)
{
  GEN lzx,lzy,lcx,lcy,lzz,lcz, y = cgetg(3,t_VEC);
  long nx,ny,i,j,k;

  lzx=(GEN)listx[1]; lcx=(GEN)listx[2]; nx=lg(lzx)-1;
  lzy=(GEN)listy[1]; lcy=(GEN)listy[2]; ny=lg(lzy)-1;
  lzz = cgetg(nx*ny+1,t_VEC); y[1]=(long)lzz;
  lcz = cgetg(nx*ny+1,t_VEC); y[2]=(long)lcz;
  k = 0;
  for (i=1; i<=nx; i++)
    for (j=1; j<=ny; j++)
    {
      k++;
      lzz[k] = ladd((GEN)lzx[i],(GEN)lzy[j]);
      lcz[k] = lmul((GEN)lcx[i],(GEN)lcy[j]);
    }
  return vectau(y);
}

static GEN
mulpoltau(GEN poltau, GEN list)
{
  long i,j;
  GEN y;

  j = lg(poltau)-2;
  y = cgetg(j+3,t_VEC);
  y[1] = (long)negtau(multau(list,(GEN)poltau[1]));
  for (i=2; i<=j+1; i++)
    y[i] = (long)subtau((GEN)poltau[i-1],multau(list,(GEN)poltau[i]));
  y[j+2] = poltau[j+1]; return y;
}

/* th. 5.3.5. and prop. 5.3.9. */
static GEN
computepolrelbeta(GEN polnf, GEN be, long g, GEN U)
{
  long i,a,b,j;
  GEN e,u,u1,u2,u3,p1,p2,p3,p4,zet,be1,be2,listr,s,veczi,vecci,powtaubet;

  switch (ell)
  {
    case 2: err(talker,"you should not be here in rnfkummer !!"); break;
    case 3: e=normtoK(polnf,be,U); u=tracetoK(polnf,be,U);
      return gsub(gmul(polx[0],gsub(gsqr(polx[0]),gmulsg(3,e))),gmul(e,u));
    case 5: e=normtoK(polnf,be,U);
      if (d==2)
      {
	u=tracetoK(polnf,gpuigs(be,3),U);
	p1=gadd(gmulsg(5,gsqr(e)), gmul(gsqr(polx[0]), gsub(gsqr(polx[0]),gmulsg(5,e))));
	return gsub(gmul(polx[0],p1),gmul(e,u));
      }
      else
      {
	be1=tauofalg(be,U);
        be2=tauofalg(be1,U);
	u1=tracetoK(polnf,gmul(be,be1),U);
        u2=tracetoK(polnf,gmul(gmul(be,be2),gsqr(be1)),U);
	u3=tracetoK(polnf,gmul(gmul(gsqr(be),gpuigs(be1,3)),be2),U);
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
      for (i=2; i<=m; i++) listr[i]=(long)modii(mulis((GEN)listr[i-1],g),gell);
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
      for (i=2; i<=m; i++) powtaubet[i]=(long)tauofalg((GEN)powtaubet[i-1],U);
      err(impl,"difficult Kummer for ell>=7"); return gzero;
  }
  return NULL; /* not reached */
}

static GEN
fix_be(GEN bnfz, GEN be, GEN u)
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
reducebetanaive(GEN bnfz, GEN be, GEN b)
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
  if (DEBUGLEVEL) fprintferr("unit exponents = %Z\n",c);
  return fix_be(bnfz,be,c);
}

static GEN
reducebeta(GEN bnfz, GEN be)
{
  long j,ru, prec = nfgetprec(bnfz);
  GEN emb,z,u,matunit, nf = checknf(bnfz);

  if (gcmp1(gnorm(be))) return reducebetanaive(bnfz,be,NULL);
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
  u = lllintern(z, 100, 1, prec);
  if (!u) return reducebetanaive(bnfz,be,emb); /* shouldn't occur */
  ru = lg(u);
  for (j=1; j<ru; j++)
    if (smodis(gcoeff(u,ru-1,j), ell)) break; /* prime to ell */
  u = (GEN)u[j]; /* coords on (fu^ell, be) of a small generator */
  ru--; setlg(u, ru);
  be = powgi(be, (GEN)u[ru]);
  return reducebetanaive(bnfz,fix_be(bnfz,be,u), NULL);
}

/* cf. algo 5.3.18 */
static GEN
testx(GEN bnfz, GEN bnr, GEN X, GEN subgroup, GEN vecMsup, GEN vecWB, long g,
      GEN U, long lW)
{
  long i,l,lX;
  GEN be,polrelbe,p1,nf;

  if (gcmp0(X)) return NULL;
  lX = lg(X);
  for (i=lW; i<lX; i++)
    if (gcmp0((GEN)X[i])) return NULL;
  l = lg(vecMsup);
  for (i=1; i<l; i++)
    if (gcmp0(FpV_red(gmul((GEN)vecMsup[i],X), gell))) return NULL;
  be = factorback(vecWB, X);
  if (DEBUGLEVEL>1) fprintferr("reducing beta = %Z\n",be);
  be = reducebeta(bnfz, be);
  if (DEBUGLEVEL>1) fprintferr("beta reduced = %Z\n",be);
  nf = checknf(bnr);
  polrelbe = computepolrelbeta((GEN)nf[1],be,g,U);
 
  p1 = unifpol(nf,polrelbe,0);
  l = lg(p1); /* lift to Q rational coeffs */
  for (i=2; i<l; i++)
    if (isnfscalar((GEN)p1[i])) polrelbe[i] = mael(p1,i,1);
   
  p1 = denom(gtovec(p1));
  polrelbe = rescale_pol(polrelbe,p1);
  if (DEBUGLEVEL>1) fprintferr("polrelbe = %Z\n",polrelbe);

  p1 = rnfnormgroup(bnr,polrelbe);
  if (!gegal(p1,subgroup)) return NULL;
  return polrelbe;
}

static GEN
logall(GEN vecWA, long lW, long mginv, GEN pr, long ex)
{
  GEN p1, bid, mod, al, M, p = (GEN)pr[1], tau = (GEN)pr[5];
  long ellrank, val, i, l = lg(vecWA);

  mod = idealpows(nfz, pr, ex);
  bid = zidealstarinitgen(nfz,mod);
  ellrank = prank(gmael(bid,2,2), ell);
  M = cgetg(l,t_MAT);
  for (i=1; i<l; i++)
  {
    al = (GEN)vecWA[i]; val = element_val(nfz,al,pr);
    al = algtobasis(nfz, al);
    if (val)
    {
      al = element_mul(nfz, al, element_pow(nfz, tau, stoi(val)));
      al = Q_div_to_int(al, gpowgs(p, val));
    }
    p1 = zideallog(nfz, al, bid); setlg(p1,ellrank+1);
    if (i < lW) p1 = gmulsg(mginv, p1);
    M[i] = (long)p1;
  }
  return M;
}

GEN
rnfkummer(GEN bnr, GEN subgroup, long all, long prec)
{
  long i, j, l, e, vp, vd, dK, lSl, lSp, lSl2, lSml2, lW, dc, ru, rv, g, mginv;
  gpmem_t av = avma;
  GEN p1,p2,p3,p4,wk,pr,U,R;
  GEN polnf,nf,bnf,bnfz,bid,ideal,cycgen,vselmer;
  GEN kk,clgp,fununits,torsunit,vecB,vecC,Tc,Tv,P;
  GEN Q,idealz,gothf,factgothf,factell,p;
  GEN listprSp,listpr,listex,vecw,vecWA,vecWB;
  GEN M,K,X,finalresult,y,module,A1,A2,A3,A3rev,vecMsup;
  GEN uu,gencyc,cyc,vecalpha,vecalphap,vecbetap,matP,ESml2,Sp,Sm,Sml1,Sml2,Sl;

  checkbnrgen(bnr);
  if (!subgroup) subgroup = gzero;
  wk = gmael4(bnr,1,8,4,1);
  if (all) gell = stoi(all);
  else
  {
    if (!gcmp0(subgroup)) gell = det(subgroup);
    else gell = det(diagonal(gmael(bnr,5,2)));
    if (typ(gell) != t_INT) err(arither1);
  }
  if (gcmp1(gell)) { avma = av; return polx[varn(gmael3(bnr,1,7,1))]; }
  if (!isprime(gell)) err(impl,"kummer for composite relative degree");
  if (divise(wk,gell))
    return gerepileupto(av,rnfkummersimple(bnr,subgroup,all));
  if (all && gcmp0(subgroup))
    err(talker,"kummer when zeta not in K requires a specific subgroup");
  bnf = (GEN)bnr[1];
  nf  = (GEN)bnf[7];
  polnf = (GEN)nf[1]; vnf = varn(polnf); degK = degpol(polnf);
  if (!vnf) err(talker,"main variable in kummer must not be x");
      /* step 7 */
  p1 = conductor(bnr,subgroup,2);
      /* end step 7 */
  bnr = (GEN)p1[2]; 
  subgroup = (GEN)p1[3];
  
  bid = (GEN)bnr[2]; module=(GEN)bid[1];
  ideal = (GEN)module[1];
  if (gcmp0(subgroup)) subgroup = diagonal(gmael(bnr,5,2));
  ell = itos(gell);
      /* step 1 of alg 5.3.5. */
  if (DEBUGLEVEL>2) fprintferr("Step 1\n");
  
  p1 = (GEN)compositum2(polnf, cyclo(ell,vnf))[1];
  R = (GEN)p1[1];
  A1= (GEN)p1[2];
  A2= (GEN)p1[3];
  kk= (GEN)p1[4];
      /* step 2 */
  if (DEBUGLEVEL>2) fprintferr("Step 2\n");
  degKz = degpol(R);
  m = degKz/degK;
  d = (ell-1)/m;
  g = powuumod(itos(lift(gener(gell))), d, ell);
  if (powuumod(g, m, ell*ell) == 1) g += ell; /* ord(g)=m in all (Z/ell^k)^* */
      /* step reduction of R */
  if (DEBUGLEVEL>2) fprintferr("Step reduction\n");
  p1 = polredabs0(R, nf_ORIG|nf_PARTIALFACT);
  R = (GEN)p1[1]; if (DEBUGLEVEL>2) fprintferr("polredabs = %Z",R);
  A3= (GEN)p1[2];
  A1 = poleval(lift(A1), A3);
  A2 = poleval(lift(A2), A3);
  A3rev= modreverse_i((GEN)A3[2], (GEN)A3[1]);
  U = gadd(gpowgs(A2,g), gmul(kk,A1));
  U = poleval(A3rev, U);
      /* step 3 */
      /* one could factor disc(R) using th. 2.1.6. */
  if (DEBUGLEVEL>2) fprintferr("Step 3\n");
  bnfz = bnfinit0(R,1,NULL,prec);
  nfz = (GEN)bnfz[7];
  clgp = gmael(bnfz,8,1);
  cyc   = (GEN)clgp[2]; rc = prank(cyc,ell);
  gencyc= (GEN)clgp[3]; l = lg(cyc);
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
    p1 = isprincipalell(bnfz, tauofideal((GEN)gencyc[j],U), vecalpha,uu);
    Tc[j]  = p1[1];
    vecB[j]= p1[2];
  }
  p1=cgetg(m,t_VEC);
  p1[1]=(long)idmat(rc);
  for (j=2; j<=m-1; j++) p1[j]=lmul((GEN)p1[j-1],Tc);
  p2=cgetg(rc+1,t_VEC);
  for (j=1; j<=rc; j++) p2[j]=un;
  p3=vecB;
  for (j=1; j<=m-1; j++)
  {
    p3 = tauofalg(p3,U);
    p4 = groupproduct(p3, gmod(gmulsg((j*d)%ell,(GEN)p1[m-j]), gell));
    for (i=1; i<=rc; i++) p2[i] = lmul((GEN)p2[i],(GEN)p4[i]);
  }
  vecC=p2;
      /* step 5 */
  if (DEBUGLEVEL>2) fprintferr("Step 5\n");
  Tv = cgetg(rv+1,t_MAT);
  for (j=1; j<=rv; j++)
  {
    Tv[j] = isvirtualunit(bnfz, tauofalg((GEN)vselmer[j],U), vecalpha,cyc)[1];
    if (DEBUGLEVEL>2) fprintferr("   %ld\n",j);
  }
  P = FpM_ker(gsubgs(Tv, g), gell);
  lW= lg(P); vecw = cgetg(lW,t_VEC);
  for (j=1; j<lW; j++)
  {
    p1 = gun;
    for (i=1; i<=rv; i++) p1 = gmul(p1, powgi((GEN)vselmer[i],gcoeff(P,i,j)));
    vecw[j] = (long)p1;
  }
      /* step 6 */
  if (DEBUGLEVEL>2) fprintferr("Step 6\n");
  Q = FpM_ker(gsubgs(gtrans(Tc), g), gell);
  dc = lg(Q)-1;
      /* step 7 done above */
      /* step 8 */
  if (DEBUGLEVEL>2) fprintferr("Step 7 and 8\n");
  idealz = lifttoKz(nfz, nf, ideal, A1);
  A1 = lift_intern(A1);
  p1 = polun[vnf];
  p2 = cgetg(degK+1,t_MAT);
  for (j=1; j<=degK; j++)
  {
    p2[j] = (long)pol_to_vec(p1, degKz);
    if (j<degK) p1 = gmod(gmul(p1,A1), R);
  }
  invexpoteta1 = invmat(p2); /* left inverse */
 
  if (!divise(idealnorm(nf,ideal),gell)) gothf = idealz;
  else
  {
    GEN bnrz = buchrayinitgen(bnfz,idealz);
    GEN subgroupz = invimsubgroup(bnrz,bnr,subgroup,U);
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
      if (!isconjinprimelist(Sm,pr,U)) _append(Sm,pr);
    }
    else
    {
      vd = (vp-1)*(ell-1)-ell*e;
      if (vd > 0) { avma = av; return gzero; }
      if (vd==0)
      {
	if (!isconjinprimelist(Sml1,pr,U)) _append(Sml1, pr);
      }
      else
      {
	if (vp==1) { avma = av; return gzero; }
        if (!isconjinprimelist(Sml2,pr,U))
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
      if (!isconjinprimelist(Sl,pr,U)) _append(Sl, pr);
  }
  lSml2 = lg(Sml2)-1; lSl = lg(Sl)-1; lSl2 = lSml2+lSl;
  Sp = concatsp(Sm,Sml1); lSp = lg(Sp)-1;
      /* step 12 */
  if (DEBUGLEVEL>2) fprintferr("Step 12\n");
  vecbetap=cgetg(lSp+1,t_VEC);
  vecalphap=cgetg(lSp+1,t_VEC);
  matP=cgetg(lSp+1,t_MAT);
  for (j=1; j<=lSp; j++)
  {
    p1 = isprincipalell(bnfz, (GEN)Sp[j], vecalpha,uu);
    matP[j] = p1[1];
    p2 = gun;
    for (i=1; i<=rc; i++)
      p2 = gmul(p2, powgi((GEN)vecC[i],gmael(p1,1,i)));
    p3=gdiv((GEN)p1[2],p2); vecbetap[j]=(long)p3;
    p2=gun;
    for (i=0; i<m; i++)
    {
      p2 = gmul(p2, gpowgs(p3, powuumod(g,m-1-i,ell)));
      if (i<m-1) p3 = tauofalg(p3,U);
    }
    vecalphap[j]=(long)p2;
  }
      /* step 13 */
  if (DEBUGLEVEL>2) fprintferr("Step 13\n");
  vecWB = concatsp(vecw, vecbetap);
  vecWA = concatsp(vecw, vecalphap);
  listprSp = concatsp(Sml2, Sl);
      /* step 14, 15, and 17 */
  if (DEBUGLEVEL>2) fprintferr("Step 14, 15 and 17\n");
  mginv = (m * u_invmod(g,ell)) % ell;
  vecMsup = cgetg(lSml2+1,t_VEC);
  M = NULL;
  for (i=1; i<=lSl2; i++)
  {
    GEN pr = (GEN)listprSp[i];
    long e = itos((GEN)pr[3]), z = ell * (e / (ell-1));

    if (i <= lSml2)
    {
      z += 1 - ESml2[i];
      vecMsup[i] = (long)logall(vecWA,lW,mginv,pr, z+1);
    }
    M = vconcat(M, logall(vecWA,lW,mginv,pr, z));
  }
  if (dc)
  {
    GEN QtP = gmul(gtrans_i(Q),matP);
    M = vconcat(M, concatsp(zeromat(dc,lW-1), QtP));
  }
  if (!M) M = zeromat(1, lSp + lW - 1);
      /* step 16 */
  if (DEBUGLEVEL>2) fprintferr("Step 16\n");
  K = FpM_ker(M, gell);
  dK= lg(K)-1; if (!dK) { avma=av; return gzero; }
      /* step 18 */
  if (DEBUGLEVEL>2) fprintferr("Step 18\n");
  y = cgetg(dK,t_VECSMALL);
  do
  {
    for (i=1; i<dK; i++) y[i] = 0;
	/* step 19 */
    for(;;)
    {
      X = (GEN)K[dK];
      for (j=1; j<dK; j++) X = gadd(X, gmulsg(y[j],(GEN)K[j]));
      X = FpV_red(X, gell);
      finalresult = testx(bnfz,bnr,X,subgroup,vecMsup,vecWB,g,U,lW);
      if (finalresult) return gerepilecopy(av, finalresult);
        /* step 20,21,22 */
      i = dK;
      do
      {
        i--; if (!i) goto DECREASE;
        if (i < dK-1) y[i+1] = 0;
        y[i]++;
      } while (y[i] >= ell);
    }
DECREASE:
    dK--;
  }
  while (dK);
  avma = av; return gzero;
}
