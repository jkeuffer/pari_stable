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

extern GEN famat_pow(GEN f, GEN n);
extern GEN famat_mul(GEN f, GEN g);
extern GEN famat_reduce(GEN fa);
extern GEN famat_ideallog(GEN nf, GEN g, GEN e, GEN bid);
extern GEN to_famat(GEN g, GEN e);
extern GEN to_famat_all(GEN x, GEN y);

typedef struct {
  GEN x;  /* tau ( Mod(x, nf.pol) ) */
  GEN zk; /* action of tau on nf.zk (as t_MAT) */
} tau_s;

typedef struct {
  GEN polnf, invexpoteta1;
  tau_s *tau;
  long m;
} toK_s;

static int
ok_x(GEN X, GEN arch, GEN vecmunit2, GEN msign, GEN gell)
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
get_listx(GEN arch,GEN msign,GEN munit,GEN vecmunit2,GEN gell,long lSp,long nbvunit)
{
  GEN kermat,p2,X,y, listx = cgetg(1,t_VEC);
  long i,j,cmpt,lker, ell = itos(gell);

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
      if (ok_x(X, arch, vecmunit2, msign, gell))
        { p2[1] = (long)X; listx = concatsp(listx,p2); }
    }
    if (!lSp)
    {
      j = 1; while (j<lker && !y[j]) j++;
      if (j<lker && y[j] == 1)
      {
        X = gsub(X,(GEN)kermat[lker]);
        if (ok_x(X, arch, vecmunit2, msign, gell))
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
tauofalg(GEN x, GEN U) {
  return gsubst(lift(x), varn(U[1]), U);
}

static tau_s *
get_tau(tau_s *tau, GEN nf, GEN U)
{
  GEN bas = (GEN)nf[7], Uzk;
  long i, l = lg(bas);
  Uzk = cgetg(l, t_MAT);
  for (i=1; i<l; i++)
    Uzk[i] = (long)algtobasis(nf, tauofalg((GEN)bas[i], U));
  tau->zk = Uzk;
  tau->x  = U; return tau;
}

static GEN tauoffamat(GEN x, tau_s *tau);

static GEN
tauofelt(GEN x, tau_s *tau)
{
  switch(typ(x))
  {
    case t_COL: return gmul(tau->zk, x);
    case t_MAT: return tauoffamat(x, tau);
    default: return tauofalg(x, tau->x);
  }
}
static GEN
tauofvec(GEN x, tau_s *tau)
{
  long i, l = lg(x);
  GEN y = cgetg(l, typ(x));

  for (i=1; i<l; i++) y[i] = (long)tauofelt((GEN)x[i], tau);
  return y;
}

static GEN
tauoffamat(GEN x, tau_s *tau)
{
  GEN y = cgetg(3, t_MAT);
  y[1] = (long)tauofvec((GEN)x[1], tau);
  y[2] = x[2]; return y;
}

/* TODO: wasteful to reduce to 2-elt form. Compute image directly */
static GEN
tauofideal(GEN nfz, GEN id, tau_s *tau)
{
  GEN I = ideal_two_elt(nfz,id);
  I[2] = (long)tauofelt((GEN)I[2], tau);
  return prime_to_ideal(nfz,I);
}

static int
isprimeidealconj(GEN nfz, GEN pr1, GEN pr2, tau_s *tau)
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
    x = FpV_red(tauofelt(x, tau), p);
    if (int_elt_val(nfz,x,p,b1,NULL)) return 0;
  }
}

static int
isconjinprimelist(GEN nfz, GEN S, GEN pr, tau_s *tau)
{
  long i, l;
  
  if (!tau) return 0;
  l = lg(S);
  for (i=1; i<l; i++)
    if (isprimeidealconj(nfz, (GEN)S[i],pr,tau)) return 1;
  return 0;
}

static GEN
downtoK(toK_s *T, GEN x)
{
  long degKz = lg(T->invexpoteta1) - 1;
  GEN y = gmul(T->invexpoteta1, pol_to_vec(lift(x), degKz));
  return gmodulcp(gtopolyrev(y,varn(T->polnf)), T->polnf);
}

static GEN
tracetoK(toK_s *T, GEN x)
{
  GEN p1 = x;
  long i;
  for (i=1; i < T->m; i++) p1 = gadd(x, tauofelt(p1,T->tau));
  return downtoK(T, p1);
}

static GEN
normtoK(toK_s *T, GEN x)
{
  GEN p1 = x;
  long i;
  for (i=1; i < T->m; i++) p1 = gmul(x, tauofelt(p1,T->tau));
  return downtoK(T, p1);
}

static GEN
no_sol(long all, int i)
{
  if (!all) err(talker,"bug%d in kummer",i);
  return cgetg(1,t_VEC);
}

static GEN
get_gell(GEN bnr, GEN subgp, long all)
{
  GEN gell;
  if (all)        gell = stoi(all);
  else if (subgp) gell = det(subgp);
  else            gell = det(diagonal(gmael(bnr,5,2)));
  if (typ(gell) != t_INT) err(arither1);
  return gell;
}

typedef struct {
  GEN Sm, Sml1, Sml2, Sl, ESml2;
} primlist;

static void
_append(GEN x, GEN t)
{
  long l = lg(x); x[l] = (long)t; setlg(x, l+1);
}

static GEN
cget1(long l, long t)
{
  GEN z = cgetg(l, t); setlg(z, 1); return z;
}

static int
build_list_Hecke(primlist *L, GEN nfz, GEN fa, GEN gothf, GEN gell, tau_s *tau)
{
  GEN listpr, listex, pr, p, factell;
  long vd, vp, e, i, l, ell = itos(gell), degKz = degpol(nfz[1]);

  listpr = (GEN)fa[1];
  listex = (GEN)fa[2]; l = lg(listpr);
  L->Sm  = cget1(l,t_VEC);
  L->Sml1= cget1(l,t_VEC);
  L->Sml2= cget1(l,t_VEC);
  L->Sl  = cget1(l+degKz,t_VEC);
  L->ESml2=cget1(l,t_VECSMALL);
  for (i=1; i<l; i++)
  {
    pr = (GEN)listpr[i]; p = (GEN)pr[1]; e = itos((GEN)pr[3]);
    vp = itos((GEN)listex[i]);
    if (!egalii(p,gell))
    {
      if (vp != 1) return 1;
      if (!isconjinprimelist(nfz, L->Sm,pr,tau)) _append(L->Sm,pr);
    }
    else
    {
      vd = (vp-1)*(ell-1)-ell*e;
      if (vd > 0) return 4;
      if (vd==0)
      {
	if (!isconjinprimelist(nfz, L->Sml1,pr,tau)) _append(L->Sml1, pr);
      }
      else
      {
	if (vp==1) return 2;
        if (!isconjinprimelist(nfz, L->Sml2,pr,tau))
        {
          _append(L->Sml2, pr);
          _append(L->ESml2,(GEN)vp);
        }
      }
    }
  }
  factell = primedec(nfz,gell); l = lg(factell);
  for (i=1; i<l; i++)
  {
    pr = (GEN)factell[i];
    if (!idealval(nfz,gothf,pr))
      if (!isconjinprimelist(nfz, L->Sl,pr,tau)) _append(L->Sl, pr);
  }
  return 0; /* OK */
}

/* if all!=0, give all equations of degree 'all'. Assume bnr modulus is the
 * conductor */
static GEN
rnfkummersimple(GEN bnr, GEN subgroup, long all)
{
  long r1, degnf, ell, j, i, l;
  long nbgenclK, lSml2, lSl2, lSp, rc, nbvunit;
  long lastbid, llistx;

  GEN polnf,bnf,nf,bid,ideal,arch,cycgen,gell,p1,p2,p3;
  GEN cyclicK,genK,listgamma,listalpha;
  GEN Sp,listprSp,vecbeta,matexpo,vunit,id,vecalpha0;
  GEN munit,vecmunit2,msign,archartif,listx,listal,listg,listgamma0;
  GEN vecbeta0,vunit_beta,fununits,torsunit;
  primlist L;

  bnf = (GEN)bnr[1];
  nf  = (GEN)bnf[7]; r1 = nf_get_r1(nf);
  polnf = (GEN)nf[1]; degnf = degpol(polnf);
  gell = get_gell(bnr,subgroup,all);
  
  bid = (GEN)bnr[2];
  ideal= gmael(bid,1,1);
  arch = gmael(bid,1,2); /* this is the conductor */
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
    p3 = basistoalg(nf, idealcoprime(nf,(GEN)genK[i],p1));
    p2 = basistoalg(nf, famat_to_nf(nf, (GEN)cycgen[i]));
    listgamma[i] = listgamma0[i] = linv(p3);
    vecalpha0[i] = (long)p2;
    listalpha[i] = lmul(p2, powgi(p3, (GEN)cyclicK[i]));
  }
  for (   ; i<=nbgenclK; i++)
  {
    long k;
    p3 = basistoalg(nf, idealcoprime(nf,(GEN)genK[i],p1));
    p2 = basistoalg(nf, famat_to_nf(nf, (GEN)cycgen[i]));
    k = itos(mpinvmod((GEN)cyclicK[i], gell));
    p2 = gpowgs(p2,k);
    listgamma0[i]= (long)p2;
    listgamma[i] = lmul(p2, gpowgs(p3, k * itos((GEN)cyclicK[i]) - 1));
  }
  i = build_list_Hecke(&L, nf, (GEN)bid[3], ideal, gell, NULL);
  if (i) return no_sol(all,i);

  lSml2 = lg(L.Sml2)-1;
  Sp = concatsp(L.Sm, L.Sml1); lSp = lg(Sp)-1;
  listprSp = concatsp(L.Sml2, L.Sl); lSl2 = lg(listprSp)-1;

  vecbeta = cgetg(lSp+1,t_VEC);
  vecbeta0= cgetg(lSp+1,t_VEC);
  matexpo = cgetg(lSp+1,t_MAT);
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

  id = idmat(degnf);
  for (i=1; i<=lSl2; i++)
  {
    GEN pr = (GEN)listprSp[i];
    long e = itos((GEN)pr[3]), z = ell * (e / (ell-1));

    if (i <= lSml2)
    {
      GEN c;
      z += 1 - L.ESml2[i];
      bid = zidealstarinitgen(nf, idealpows(nf, pr, z+1));
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

  listx = get_listx(arch,msign,munit,vecmunit2,gell,lSp,nbvunit);
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
 /* Now, alpha in listal satisfies all congruences, non-congruences,
  * x^l - alpha is irreducible, signature and relative disciminant are
  * correct. Remains to check its norm group. */
  if (DEBUGLEVEL) fprintferr("listalpha = %Z\n",listal);
  p2 = cgetg(1,t_VEC);
  for (i=1; i<llistx; i++)
  {
    p1 = gsub(gpuigs(polx[0],ell), (GEN)listal[i]);
    if (all || gegal(rnfnormgroup(bnr,p1),subgroup)) p2 = concatsp(p2,p1);
  }
  if (all) return p2;
  switch(lg(p2)-1)
  {
    case 0: err(talker,"bug 6: no equation found in kummer");
    case 1: break; /* OK */
    default:err(talker,"bug 7: more than one equation found in kummer: %Z",p2);
  }
  return (GEN)p2[1];
}

static GEN
computepolrel(toK_s *T, GEN be)
{
  GEN p1 = gun, p2 = be;
  long i,j;

  for (i=0; i<T->m; i++)
  {
    p1 = gmul(p1, gsub(polx[0],p2));
    if (i < T->m-1) p2 = tauofelt(p2, T->tau);
  }
  for (j=2; j<=T->m+2; j++) p1[j] = (long)downtoK(T, (GEN)p1[j]);
  return p1;
}

/* alg. 5.2.15. with remark */
static GEN
isprincipalell(GEN bnfz, GEN id, GEN cycgen, GEN uu, GEN gell, long rc)
{
  long i, l = lg(cycgen);
  GEN y, logdisc, b;

  y = isprincipalgenforce(bnfz,id);
  logdisc = gmod((GEN)y[1], gell);
  b = to_famat_all((GEN)y[2], gun);
  for (i=rc+1; i<l; i++)
  {
    GEN e = modii(mulii((GEN)logdisc[i],(GEN)uu[i]), gell);
    b = famat_mul(b, famat_pow((GEN)cycgen[i], e));
  }
  y = cgetg(3,t_VEC);
  y[1] = (long)logdisc; setlg(logdisc,rc+1);
  y[2] = (long)b; return y;
}

/* return q, q^n = x */
static GEN
idealsqrtn(GEN nf, GEN x, GEN gn)
{
  long i, l, n = itos(gn);
  GEN fa, q, Ex, Pr;

  fa = idealfactor(nf, x);
  Pr = (GEN)fa[1]; l = lg(Pr);
  Ex = (GEN)fa[2]; q = NULL;
  for (i=1; i<l; i++)
  {
    long ex = itos((GEN)Ex[i]);
    GEN e = stoi(ex / n);
    if (ex % n) err(talker,"not an n-th power in idealsqrtn");
    if (q) q = idealmulpowprime(nf, q, (GEN)Pr[i], e);
    else   q = idealpow(nf, (GEN)Pr[i], e);
  }
  return q? q: gun;
}

/* alg. 5.3.11. */
static GEN
isvirtualunit(GEN bnfz, GEN v, GEN vecalpha, GEN cyc, GEN gell, long rc)
{
  GEN p1, ga, eps, vecy, logdisc, nfz = checknf(bnfz);
  long i, l;

  p1 = isprincipalgenforce(bnfz, idealsqrtn(nfz, v, gell));
  logdisc = (GEN)p1[1];
  ga = basistoalg(nfz,(GEN)p1[2]);
  l = lg(vecalpha);
  for (i=rc+1; i<l; i++)
    ga = gmul(ga, powgi((GEN)vecalpha[i],divii((GEN)logdisc[i],(GEN)cyc[i])));
  eps = powgi(ga, gell);
  vecy = cgetg(rc+1,t_COL);
  for (i=1; i<=rc; i++)
  {
    vecy[i] = (long)divii((GEN)logdisc[i], divii((GEN)cyc[i],gell));
    eps = gmul(eps, powgi((GEN)vecalpha[i],(GEN)vecy[i]));
  }
  eps = element_div(nfz, v, eps);
  p1 = cgetg(3,t_VEC);
  p1[1] = (long)concatsp(vecy, lift(isunit(bnfz,eps)));
  p1[2] = (long)ga; return p1;
}

static GEN
steinitzaux(GEN nfz, GEN nf, GEN id, GEN polrel, long m)
{
  long i,j, degKz = degpol(nfz[1]), degK = degpol(nf[1]);
  GEN p1,p2,p3,vecid,matid,pseudomat,pid;

  p1 = gsubst(gmul((GEN)nfz[7],id), varn(nfz[1]), polx[0]);
  for (j=1; j<=degKz; j++)
    p1[j] = (long)gmod((GEN)p1[j], polrel);
  p2=cgetg(degKz+1,t_MAT);
  for (j=1; j<=degKz; j++)
  {
    p3=cgetg(m+1,t_COL); p2[j]=(long)p3;
    for (i=1; i<=m; i++) p3[i]=(long)algtobasis(nf,truecoeff((GEN)p1[j],i-1));
  }
  vecid=cgetg(degKz+1,t_VEC); matid = idmat(degK);
  for (j=1; j<=degKz; j++) vecid[j]=(long)matid;
  pseudomat=cgetg(3,t_VEC);
  pseudomat[1]=(long)p2; pseudomat[2]=(long)vecid;
  pid=(GEN)nfhermite(nf,pseudomat)[2];
  p1=matid;
  for (j=1; j<=m; j++) p1=idealmul(nf,p1,(GEN)pid[j]);
  return p1;
}

static GEN
normrelz(GEN nfz, GEN nf, GEN id, GEN polrel, GEN steinitzZk, long m)
{
  GEN p1 = steinitzaux(nfz,nf,idealhermite(nfz, id), polrel, m);
  return idealdiv(nf,p1,steinitzZk);
}

static GEN
invimsubgroup(toK_s *T, GEN bnrz, GEN bnr, GEN subgroup)
{
  long l,j;
  GEN g,Plog,raycycz,rayclgpz,genraycycz,U,polrel,steinitzZk;
  GEN nf = checknf(bnr), nfz = checknf(bnrz), polz = (GEN)nfz[1];

  polrel = computepolrel(T, polx[varn(polz)]);
  steinitzZk = steinitzaux(nfz,nf,idmat(degpol(polz)), polrel, T->m); 
  rayclgpz = (GEN)bnrz[5];
  raycycz   = (GEN)rayclgpz[2]; l = lg(raycycz);
  genraycycz= (GEN)rayclgpz[3];
  Plog = cgetg(l,t_MAT);
  for (j=1; j<l; j++)
  {
    g = normrelz(nfz,nf,(GEN)genraycycz[j],polrel,steinitzZk,T->m);
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
computepolrelbeta(toK_s *T, GEN be, long g, long ell)
{
  long i, a, b, j, m, vnf;
  GEN e,u,u1,u2,u3,p1,p2,zet,be1,be2,listr,s,veczi,vecci,powtaubet;
  GEN X = polx[0];

  switch (ell)
  {
    case 2: err(bugparier,"rnfkummer (-1 not in nf!)"); break;
    case 3: e = normtoK(T,be); u = tracetoK(T,be);
      return gsub(gmul(X,gsub(gsqr(X),gmulsg(3,e))), gmul(e,u));
    case 5: e = normtoK(T,be);
      if (ell-1 == 2*T->m) /* d == 2 */
      {
	u = tracetoK(T,gpuigs(be,3));
	p1=gadd(gmulsg(5,gsqr(e)), gmul(gsqr(X), gsub(gsqr(X),gmulsg(5,e))));
	return gsub(gmul(X,p1), gmul(e,u));
      }
      be1 = tauofelt(be,T->tau);
      be2 = tauofelt(be1,T->tau);
      u1 = tracetoK(T,gmul(be,be1));
      u2 = tracetoK(T,gmul(gmul(be,be2),gsqr(be1)));
      u3 = tracetoK(T,gmul(gmul(gsqr(be),gpuigs(be1,3)),be2));
      p1 = gsub(gsqr(X), gmulsg(10,e));
      p1 = gsub(gmul(X,p1), gmulsg(5,gmul(e,u1)));
      p1 = gadd(gmul(X,p1), gmul(gmulsg(5,e),gsub(e,u2)));
      p1 = gsub(gmul(X,p1), gmul(e,u3));
      return p1;

    default: p2 = cgetg(3,t_VEC);
      p2[1] = (long)_vec(gzero);
      p2[2] = (long)_vec(gun); p1 = _vec(p2);
      m = T->m;
      vnf = varn(T->polnf);
      zet = gmodulcp(polx[vnf], cyclo(ell,vnf));
      listr = cgetg(m+1,t_VECSMALL);
      listr[1] = 1;
      for (i=2; i<=m; i++) listr[i] = (listr[i-1]*g) % ell;
      veczi=cgetg(m+1,t_VEC);
      for (b=0; b<m; b++)
      {
	s = gzero;
	for (a=0; a<m; a++)
	  s = gaddgs(gmul(X,s), (listr[b+1] * listr[a+1]) % ell);
	veczi[b+1]=(long)s;
      }
      for (j=0; j<ell; j++)
      {
	GEN p3 = cgetg(3,t_VEC);
	vecci = cgetg(m+1,t_VEC);
	for (b=0; b<m; b++) vecci[b+1] = (long)gpowgs(zet, j * listr[b+1]);
	p3[1] = (long)veczi;
        p3[2] = (long)vecci;
	p1 = mulpoltau(p1,p3);
      }
      powtaubet=cgetg(m+1,t_VEC);
      powtaubet[1]=(long)be;
      for (i=2; i<=m; i++)
        powtaubet[i] = (long)tauofelt((GEN)powtaubet[i-1],T->tau);
      err(impl,"difficult Kummer for ell>=7"); /* FIXME */
  }
  return NULL; /* not reached */
}

static GEN
fix_be(GEN bnfz, GEN be, GEN u)
{
  GEN nf = checknf(bnfz), fu = gmael(bnfz,8,5);
  return element_mul(nf, be, factorbackelt(fu, u, nf));
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
reducebetanaive(GEN bnfz, GEN be, GEN b, long ell)
{
  long i,k,n,ru,r1, prec = nfgetprec(bnfz);
  GEN z,p1,p2,nmax,c, nf = checknf(bnfz);

  if (DEBUGLEVEL) fprintferr("reduce modulo (Z_K^*)^l\n");
  r1 = nf_get_r1(nf);
  if (!b)
  {
    if (typ(be) != t_COL) be = algtobasis(nf, be);
    b = gmul(gmael(nf,5,1), be);
  }
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
reducebeta(GEN bnfz, GEN be, long ell)
{
  long j,ru, prec = nfgetprec(bnfz);
  GEN emb,z,u,matunit, nf = checknf(bnfz);

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
  if (u)
  {
    ru = lg(u);
    for (j=1; j < ru; j++)
      if (smodis(gcoeff(u,ru-1,j), ell)) break; /* prime to ell */
    if (j < ru)
    {
      u = (GEN)u[j]; /* coords on (fu^ell, be) of a small generator */
      ru--; setlg(u, ru);
      be = element_pow(nf, be, (GEN)u[ru]);
      be = fix_be(bnfz,be,u);
    }
  }
  return reducebetanaive(bnfz, be, NULL, ell);
}

static GEN
famat_factorback(GEN v, GEN e)
{
  long i, l = lg(v);
  GEN V = cgetg(1, t_MAT);
  for (i=1; i<l; i++) 
    V = famat_mul(V, famat_pow((GEN)v[i], (GEN)e[i]));
  return V;
}

/* cf. algo 5.3.18 */
static GEN
testx(toK_s *T, GEN bnfz, GEN bnr, GEN X, GEN subgroup, GEN vecMsup,
      GEN vecWB, long g, GEN gell, long lW)
{
  long i,l,lX, ell = itos(gell);
  GEN BE, be, polrelbe, p1, nf, c;

  X = FpV_red(X, gell);
  if (gcmp0(X)) return NULL;
  lX = lg(X);
  for (i=lW; i<lX; i++)
    if (gcmp0((GEN)X[i])) return NULL;
  l = lg(vecMsup);
  for (i=1; i<l; i++)
    if (gcmp0(FpV_red(gmul((GEN)vecMsup[i],X), gell))) return NULL;
  BE = famat_reduce(famat_factorback(vecWB, X));
  BE[2] = (long)centermod((GEN)BE[2], gell);
  be = factorbackelt(BE, bnfz, NULL);
  /* reduce mod Q^ell */
  if (typ(be) != t_COL) be = algtobasis(bnfz, be);
  be = primitive_part(be, &c);
  if (c)
  {
    p1 = factor(c);
    p1[2] = (long)FpV_red((GEN)p1[2], gell);
    c = factorback(p1, NULL);
    be = gmul(be, c);
  }

  if (DEBUGLEVEL>1) fprintferr("reducing beta = %Z\n",be);
  be = reducebeta(bnfz, be, ell);
  if (DEBUGLEVEL>1) fprintferr("beta reduced = %Z\n",be);
  nf = checknf(bnr);
  be = basistoalg(bnfz, be); /* FIXME */
  polrelbe = computepolrelbeta(T, be, g, ell);
 
  p1 = unifpol(nf,polrelbe,0);
  l = lg(p1); /* lift to Q rational coeffs */
  for (i=2; i<l; i++)
  {
    GEN c = (GEN)p1[i];
    if (isnfscalar(c)) polrelbe[i] = c[1];
  }
  if (DEBUGLEVEL>1) fprintferr("polrelbe = %Z\n",polrelbe);

  p1 = rnfnormgroup(bnr,polrelbe);
  if (!gegal(p1,subgroup)) return NULL;
  return polrelbe;
}

static GEN
logall(GEN nfz, GEN vecWA, long lW, long mginv, long ell, GEN pr, long ex)
{
  GEN m, bid, al, M;
  long ellrank, i, l = lg(vecWA);

  bid = zidealstarinitgen(nfz, idealpows(nfz, pr, ex));
  ellrank = prank(gmael(bid,2,2), ell);
  M = cgetg(l,t_MAT);
  for (i=1; i<l; i++)
  {
    al = (GEN)vecWA[i];
    m = famat_ideallog(nfz, (GEN)al[1], (GEN)al[2], bid);
    setlg(m,ellrank+1);
    if (i < lW) m = gmulsg(mginv, m);
    M[i] = (long)m;
  }
  return M;
}

static GEN
lifttoKz(GEN nfz, GEN nf, GEN id, GEN U)
{
  GEN I = ideal_two_elt(nf,id);
  GEN x = (GEN)I[2];
  I[2] = (long)algtobasis(nfz, poleval(gmul((GEN)nf[7],x), U));
  return prime_to_ideal(nfz,I);
}

GEN
rnfkummer(GEN bnr, GEN subgroup, long all, long prec)
{
  long i, j, l, m, d, dK, dc, rc, ru, rv, g, mginv, degK, degKz, ell;
  long lSp, lSl2, lSml2, lW, vnf;
  gpmem_t av = avma;
  GEN p1,p2,p3,wk,U,R,gell;
  GEN polnf,nf,bnf,bnfz,bid,ideal,cycgen,vselmer;
  GEN kk,clgp,fununits,torsunit,vecB,vecC,Tc,Tv,P;
  GEN Q,idealz,gothf,factgothf,nfz;
  GEN listprSp,vecW,vecWA,vecWB;
  GEN M,K,y,A1,A2,A3,A3rev,vecMsup;
  GEN uu,gen,cyc,vecalpha,vecalphap,vecbetap,matP,Sp;
  primlist L;
  toK_s T;
  tau_s _tau, *tau;

  checkbnrgen(bnr);
  bnf = (GEN)bnr[1];
  nf  = (GEN)bnf[7];
  polnf = (GEN)nf[1]; vnf = varn(polnf);
  if (!vnf) err(talker,"main variable in kummer must not be x");
  wk = gmael3(bnf,8,4,1);
      /* step 7 */
  if (all) subgroup = NULL;
  p1 = conductor(bnr, subgroup, 2);
  bnr      = (GEN)p1[2]; 
  subgroup = (GEN)p1[3];
  gell = get_gell(bnr,subgroup,all);
  if (gcmp1(gell)) { avma = av; return polx[vnf]; }
  if (!isprime(gell)) err(impl,"kummer for composite relative degree");
  if (divise(wk,gell))
    return gerepilecopy(av, rnfkummersimple(bnr,subgroup,all));
  if (all) err(impl,"extensions by degree in kummer when zeta not in K");

  bid = (GEN)bnr[2];
  ideal = gmael(bid,1,1);
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
  degK  = degpol(polnf);
  degKz = degpol(R);
  m = degKz/degK;
  d = (ell-1)/m;
  g = powuumod(u_gener(ell), d, ell);
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
  tau = get_tau(&_tau, nfz, U);
  clgp = gmael(bnfz,8,1);
  cyc = (GEN)clgp[2]; rc = prank(cyc,ell);
  gen = (GEN)clgp[3]; l = lg(cyc);
  vecalpha = cgetg(l,t_VEC);
  cycgen = check_and_build_cycgen(bnfz);
  for (j=1; j<l; j++)
    vecalpha[j] = (long)basistoalg(nfz, famat_to_nf(nfz, (GEN)cycgen[j]));
      /* computation of the uu(j) (see remark 5.2.15.) */
  uu = cgetg(l,t_VEC);
  for (j=1; j<=rc; j++) uu[j] = zero;
  for (   ; j<  l; j++) uu[j] = lmpinvmod((GEN)cyc[j], gell);

  fununits = check_units(bnfz,"rnfkummer");
  torsunit = gmael3(bnfz,8,4,2);
  ru = (degKz>>1)-1;
  rv = rc+ru+1;
  vselmer = cgetg(rv+1,t_VEC);
  for (j=1; j<=rc; j++) vselmer[j] = cycgen[j];
  for (   ; j< rv; j++) vselmer[j] = fununits[j-rc];
  vselmer[rv]=(long)torsunit;
    /* step 4 */
  if (DEBUGLEVEL>2) fprintferr("Step 4\n");
  vecB=cgetg(rc+1,t_VEC);
  Tc=cgetg(rc+1,t_MAT);
  for (j=1; j<=rc; j++)
  {
    p1 = tauofideal(nfz,(GEN)gen[j], tau);
    p1 = isprincipalell(bnfz, p1, cycgen,uu,gell,rc);
    Tc[j]  = p1[1];
    vecB[j]= p1[2];
  }
  p1 = cgetg(m,t_VEC);
  p1[1] = (long)idmat(rc);
  for (j=2; j<=m-1; j++) p1[j] = lmul((GEN)p1[j-1],Tc);
  p2 = cgetg(rc+1,t_VEC);
  for (j=1; j<=rc; j++) p2[j] = lgetg(1, t_MAT);
  p3 = vecB;
  for (j=1; j<=m-1; j++)
  {
    GEN T = FpM_red(gmulsg((j*d)%ell,(GEN)p1[m-j]), gell);
    p3 = tauofvec(p3, tau);
    for (i=1; i<=rc; i++)
      p2[i] = (long)famat_mul((GEN)p2[i], famat_factorback(p3, (GEN)T[i]));
  }
  vecC = p2;
  for (i=1; i<=rc; i++) vecC[i] = (long)famat_reduce((GEN)vecC[i]);
      /* step 5 */
  if (DEBUGLEVEL>2) fprintferr("Step 5\n");
  Tv = cgetg(rv+1,t_MAT);
  for (j=1; j<=rv; j++)
  {
    p1 = tauofelt((GEN)vselmer[j], tau);
    if (typ(p1) == t_MAT) p1 = factorbackelt(p1, nfz, NULL); /* famat */
    Tv[j] = isvirtualunit(bnfz, p1, vecalpha,cyc,gell,rc)[1];
  }
  P = FpM_ker(gsubgs(Tv, g), gell);
  lW = lg(P); vecW = cgetg(lW,t_VEC);
  for (j=1; j<lW; j++) vecW[j] = (long)famat_factorback(vselmer, (GEN)P[j]);
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
  T.invexpoteta1 = invmat(p2); /* left inverse */
  T.polnf = polnf;
  T.tau = tau;
  T.m = m;
 
  if (smodis(idealnorm(nf,ideal), ell)) gothf = idealz;
  else
  { /* l | N(ideal) */
    GEN bnrz = buchrayinitgen(bnfz, idealz);
    GEN subgroupz = invimsubgroup(&T, bnrz,bnr,subgroup);
    gothf = conductor(bnrz,subgroupz,0);
  }
      /* step 9 */
  if (DEBUGLEVEL>2) fprintferr("Step 9\n");
  factgothf = idealfactor(nfz,gothf);
      /* step 10 and step 11 */
  if (DEBUGLEVEL>2) fprintferr("Step 10 and 11\n");
  i = build_list_Hecke(&L, nfz, factgothf, gothf, gell, tau);
  if (i) return no_sol(all,i);

  lSml2 = lg(L.Sml2)-1;
  Sp = concatsp(L.Sm, L.Sml1); lSp = lg(Sp)-1;
  listprSp = concatsp(L.Sml2, L.Sl); lSl2 = lg(listprSp)-1;

      /* step 12 */
  if (DEBUGLEVEL>2) fprintferr("Step 12\n");
  vecbetap = cgetg(lSp+1,t_VEC);
  vecalphap= cgetg(lSp+1,t_VEC);
  matP = cgetg(lSp+1,t_MAT);
  for (j=1; j<=lSp; j++)
  {
    GEN e, a;
    p1 = isprincipalell(bnfz, (GEN)Sp[j], cycgen,uu,gell,rc);
    e = (GEN)p1[1];
    a = (GEN)p1[2];
    matP[j] = (long)e;
    p3 = famat_mul(famat_factorback(vecC, gneg(e)), a);
    vecbetap[j] = (long)p3;
    p2 = cgetg(1, t_MAT);
    for (i=0; i<m; i++)
    {
      p2 = famat_mul(p2, famat_pow(p3, utoi(powuumod(g,m-1-i,ell))));
      if (i < m-1) p3 = tauofelt(p3, tau);
    }
    vecalphap[j] = (long)p2;
  }
      /* step 13 */
  if (DEBUGLEVEL>2) fprintferr("Step 13\n");
  vecWB = concatsp(vecW, vecbetap);
  vecWA = concatsp(vecW, vecalphap);

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
      z += 1 - L.ESml2[i];
      vecMsup[i] = (long)logall(nfz, vecWA,lW,mginv,ell,pr, z+1);
    }
    M = vconcat(M, logall(nfz, vecWA,lW,mginv,ell,pr, z));
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
      GEN res, X = (GEN)K[dK];
      for (j=1; j<dK; j++) X = gadd(X, gmulsg(y[j],(GEN)K[j]));
      res = testx(&T,bnfz,bnr,X,subgroup,vecMsup,vecWB,g,gell,lW);
      if (res) return gerepilecopy(av, res);
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
