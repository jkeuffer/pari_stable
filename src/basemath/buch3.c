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
/*                       RAY CLASS FIELDS                          */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "parinf.h"

extern GEN init_units(GEN BNF);
extern GEN F2V_red_ip(GEN v);
extern GEN zlog(GEN nf, GEN a, GEN sgn, zlog_S *S);
extern GEN make_integral(GEN nf, GEN L0, GEN f, GEN *listpr);
extern GEN unif_mod_fZ(GEN pr, GEN F);
extern GEN init_unif_mod_fZ(GEN L);
extern void testprimes(GEN bnf, long bound);
extern GEN Fp_PHlog(GEN a, GEN g, GEN p, GEN ord);
extern GEN FqX_factor(GEN x, GEN T, GEN p);
extern GEN arch_mul(GEN x, GEN y);
extern GEN check_and_build_cycgen(GEN bnf);
extern GEN colreducemodHNF(GEN x, GEN y, GEN *Q);
extern GEN detcyc(GEN cyc);
extern GEN famat_reduce(GEN fa);
extern GEN famat_to_nf_modideal_coprime(GEN nf, GEN g, GEN e, GEN id, GEN EX);
extern GEN famat_to_nf_modidele(GEN nf, GEN g, GEN e, GEN bid);
extern GEN gmul_mat_smallvec(GEN x, GEN y);
extern GEN idealaddtoone_i(GEN nf, GEN x, GEN y);
extern GEN isprincipalfact(GEN bnf,GEN P, GEN e, GEN C, long flag);
extern GEN logunitmatrix(GEN nf, GEN U, GEN sgnU, GEN bid);
extern GEN sqred1_from_QR(GEN x, long prec);
extern GEN subgroupcondlist(GEN cyc, GEN bound, GEN listKer);
extern GEN to_Fp_simple(GEN nf, GEN x, GEN ffproj);
extern GEN to_famat_all(GEN x, GEN y);
extern GEN trivfact(void);
extern GEN vconcat(GEN Q1, GEN Q2);
extern long FqX_is_squarefree(GEN P, GEN T, GEN p);
extern long int_elt_val(GEN nf, GEN x, GEN p, GEN b, GEN *newx);
extern void minim_alloc(long n, double ***q, GEN *x, double **y,  double **z, double **v);
extern void rowselect_p(GEN A, GEN B, GEN p, long init);
extern int hnfdivide(GEN A, GEN B);
extern GEN perm_to_arch(GEN nf, GEN archp);

/* FIXME: obsolete, see zarchstar (which is much slower unfortunately). */
static GEN
get_full_rank(GEN nf, GEN v, GEN _0, GEN _1, GEN gen, long ngen, long rankmax)
{
  GEN vecsign,v1,p1,alpha, bas=(GEN)nf[7], rac=(GEN)nf[6];
  long rankinit = lg(v)-1, N = degpol(nf[1]), va = varn(nf[1]);
  long limr,i,k,kk,r,rr;
  vecsign = cgetg(rankmax+1,t_COL);
  for (r=1,rr=3; ; r++,rr+=2)
  {
    p1 = gpowgs(stoi(rr),N);
    limr = is_bigint(p1)? BIGINT: p1[2];
    limr = (limr-1)>>1;
    for (k=rr;  k<=limr; k++)
    {
      pari_sp av1=avma;
      alpha = gzero;
      for (kk=k,i=1; i<=N; i++,kk/=rr)
      {
        long lambda = (kk+r)%rr - r;
        if (lambda)
          alpha = gadd(alpha,gmulsg(lambda,(GEN)bas[i]));
      }
      for (i=1; i<=rankmax; i++)
	vecsign[i] = (gsigne(gsubst(alpha,va,(GEN)rac[i])) > 0)? (long)_0
                                                               : (long)_1;
      v1 = concatsp(v, vecsign);
      if (rank(v1) == rankinit) { avma = av1; continue; }

      v=v1; rankinit++; ngen++;
      gen[ngen] = (long) alpha;
      if (rankinit == rankmax) return ginv(v); /* full rank */
      vecsign = cgetg(rankmax+1,t_COL);
    }
  }
}

/* FIXME: obsolete. Replace by a call to buchrayall (currently much slower) */
GEN
buchnarrow(GEN bnf)
{
  GEN nf,_0,_1,cyc,gen,v,matsign,arch,cycgen,logs;
  GEN dataunit,p1,p2,h,basecl,met,u1;
  long r1,R,i,j,ngen,sizeh,t,lo,c;
  pari_sp av = avma;

  bnf = checkbnf(bnf);
  nf = checknf(bnf); r1 = nf_get_r1(nf);
  if (!r1) return gcopy(gmael(bnf,8,1));

  _1 = gmodulss(1,2);
  _0 = gmodulss(0,2);
  cyc = gmael3(bnf,8,1,2);
  gen = gmael3(bnf,8,1,3); ngen = lg(gen)-1;
  matsign = signunits(bnf); R = lg(matsign);
  dataunit = cgetg(R+1,t_MAT);
  for (j=1; j<R; j++)
  {
    p1=cgetg(r1+1,t_COL); dataunit[j]=(long)p1;
    for (i=1; i<=r1; i++)
      p1[i] = (signe(gcoeff(matsign,i,j)) > 0)? (long)_0: (long)_1;
  }
  v = cgetg(r1+1,t_COL); for (i=1; i<=r1; i++) v[i] = (long)_1;
  dataunit[R] = (long)v; v = image(dataunit); t = lg(v)-1;
  if (t == r1) { avma = av; return gcopy(gmael(bnf,8,1)); }

  sizeh = ngen+r1-t; p1 = cgetg(sizeh+1,t_COL);
  for (i=1; i<=ngen; i++) p1[i] = gen[i];
  gen = p1;
  v = get_full_rank(nf,v,_0,_1,gen,ngen,r1);

  arch = cgetg(r1+1,t_VEC); for (i=1; i<=r1; i++) arch[i]=un;
  cycgen = check_and_build_cycgen(bnf);
  logs = cgetg(ngen+1,t_MAT);
  for (j=1; j<=ngen; j++)
  {
    GEN u = gmul(v, zsigne(nf,(GEN)cycgen[j],arch));
    logs[j] = (long)F2V_red_ip( vecextract_i(u, t+1, r1) );
  }
  /* [ cyc  0 ]
   * [ logs 2 ] = relation matrix for Cl_f */
  h = concatsp(
    vconcat(diagonal(cyc), logs),
    vconcat(zeromat(ngen, r1-t), gscalmat(gdeux,r1-t))
  );
 
  lo = lg(h)-1;
  met = smithrel(h,NULL,&u1);
  c = lg(met);
  if (DEBUGLEVEL>3) msgtimer("smith/class group");

  basecl = cgetg(c,t_VEC);
  for (j=1; j<c; j++)
  {
    p1 = gcoeff(u1,1,j);
    p2 = idealpow(nf,(GEN)gen[1],p1);
    if (signe(p1) < 0) p2 = numer(p2);
    for (i=2; i<=lo; i++)
    {
      p1 = gcoeff(u1,i,j);
      if (signe(p1))
      {
	p2 = idealmul(nf,p2, idealpow(nf,(GEN)gen[i],p1));
        p2 = primpart(p2);
      }
    }
    basecl[j] = (long)p2;
  }
  v = cgetg(4,t_VEC);
  v[1] = (long)dethnf_i(h);
  v[2] = (long)met;
  v[3] = (long)basecl; return gerepilecopy(av, v);
}

/********************************************************************/
/**                                                                **/
/**                  REDUCTION MOD IDELE                           **/
/**                                                                **/
/********************************************************************/

static GEN
compute_fact(GEN nf, GEN u1, GEN gen)
{
  GEN G, basecl;
  long prec,i,j, l = lg(u1), h = lg(u1[1]); /* l > 1 */

  basecl = cgetg(l,t_VEC);
  prec = nfgetprec(nf);
  G = cgetg(3,t_VEC);
  G[2] = lgetg(1,t_MAT);

  for (j=1; j<l; j++)
  {
    GEN g,e, z = NULL;
    for (i=1; i<h; i++)
    {
      e = gcoeff(u1,i,j); if (!signe(e)) continue;

      g = (GEN)gen[i];
      if (typ(g) != t_MAT)
      {
        if (z) 
          z[2] = (long)arch_mul((GEN)z[2], to_famat_all(g, e));
        else
        {
          z = cgetg(3,t_VEC);
          z[1] = 0;
          z[2] = (long)to_famat_all(g, e);
        }
        continue;
      }

      G[1] = (long)g;
      g = idealpowred(nf,G,e,prec);
      z = z? idealmulred(nf,z,g,prec): g;
    }
    z[2] = (long)famat_reduce((GEN)z[2]);
    basecl[j] = (long)z;
  }
  return basecl;
}

/* given two coprime integral ideals x and f (f HNF), compute "small"
 * non-zero a in x, such that a = 1 mod (f). GTM 193: Algo 4.3.3 */
static GEN
redideal(GEN nf,GEN x,GEN f)
{
  if (gcmp1(gcoeff(f,1,1))) return idealred_elt(nf, x); /* f = 1 */
  return idealaddtoone_i(nf,x,f); /* a = b mod (x f), != 0 since 1 mod f */
}

static int
too_big(GEN nf, GEN bet)
{
  GEN x = gnorm(basistoalg(nf,bet));
  switch (typ(x))
  {
    case t_INT: return absi_cmp(x, gun);
    case t_FRAC: return absi_cmp((GEN)x[1], (GEN)x[2]);
  }
  err(bugparier, "wrong type in too_big");
  return 0; /* not reached */
}

/* GTM 193: Algo 4.3.4. Reduce x mod idele */
static GEN
_idealmodidele(GEN nf, GEN x, GEN idele, GEN sarch)
{
  pari_sp av = avma;
  GEN a,A,D,G, f = (GEN)idele[1];

  G = redideal(nf, x, f);
  D = redideal(nf, idealdiv(nf,G,x), f);
  A = element_div(nf,D,G);
  if (too_big(nf,A) > 0) { avma = av; return x; }
  a = set_sign_mod_idele(nf, NULL, A, idele, sarch);
  if (a != A && too_big(nf,A) > 0) { avma = av; return x; }
  return idealmul(nf, a, x);
}

GEN
idealmodidele(GEN bnr, GEN x)
{
  GEN bid = (GEN)bnr[2], fa2 = (GEN)bid[4];
  GEN idele = (GEN)bid[1];
  GEN sarch = (GEN)fa2[lg(fa2)-1];
  return _idealmodidele(checknf(bnr), x, idele, sarch);
}

/* v_pr(L0 * cx). tau = pr[5] or (more efficient) mult. table for pr[5] */
static long
fast_val(GEN nf,GEN L0,GEN cx,GEN pr,GEN tau)
{
  GEN p = (GEN)pr[1];
  long v = int_elt_val(nf,L0,p,tau,NULL);
  if (cx)
  {
    long w = ggval(cx, p);
    if (w) v += w * itos((GEN)pr[3]);
  }
  return v;
}

/* x coprime to fZ, return y = x mod fZ, y integral */
static GEN
make_integral_Z(GEN x, GEN fZ)
{
  GEN d, y = Q_remove_denom(x, &d);
  if (d) y = FpV_red(gmul(y, mpinvmod(d, fZ)), fZ);
  return y;
}

/* p pi^(-1) mod f */
static GEN
get_pinvpi(GEN nf, GEN fZ, GEN p, GEN pi, GEN *v)
{
  if (!*v) {
    GEN invpi = element_inv(nf, pi);
    *v = make_integral_Z(gmul(p, invpi), mulii(p, fZ));
  }
  return *v; 
}
/* p pi^(-1) mod f */
static GEN
get_pi(GEN F, GEN pr, GEN *v)
{
  if (!*v) *v = unif_mod_fZ(pr, F);
  return *v; 
}

static GEN
compute_raygen(GEN nf, GEN u1, GEN gen, GEN bid)
{
  GEN f, fZ, basecl, module, fa, fa2, pr, t, EX, sarch, cyc, F;
  GEN *listpr, *listep, *vecpi, *vecpinvpi, *vectau;
  long i,j,l,lp;

  /* basecl = generators in factored form */
  basecl = compute_fact(nf,u1,gen);

  module = (GEN)bid[1];
  cyc = gmael(bid,2,2); EX = (GEN)cyc[1]; /* exponent of (O/f)^* */
  f   = (GEN)module[1]; fZ = gcoeff(f,1,1);
  fa  = (GEN)bid[3];
  fa2 = (GEN)bid[4]; sarch = (GEN)fa2[lg(fa2)-1];
  listpr = (GEN*)fa[1]; F = init_unif_mod_fZ((GEN)listpr);
  listep = (GEN*)fa[2];

  lp = lg(listpr);
  vecpinvpi = (GEN*)cgetg(lp, t_VEC);
  vecpi  = (GEN*)cgetg(lp, t_VEC);
  vectau = (GEN*)cgetg(lp, t_VEC);
  for (i=1; i<lp; i++) 
  {
    pr = listpr[i];
    vecpi[i]    = NULL; /* to be computed if needed */
    vecpinvpi[i] = NULL; /* to be computed if needed */
    vectau[i] = eltmul_get_table(nf, (GEN)pr[5]);
  }

  l = lg(basecl);
  for (i=1; i<l; i++)
  {
    GEN p, pi, pinvpi, dmulI, mulI, G, I, A, e, L, newL;
    long la, v, k;
    /* G = [I, A=famat(L,e)] is a generator, I integral */
    G = (GEN)basecl[i];
    I = (GEN)G[1];
    A = (GEN)G[2];
      L = (GEN)A[1];
      e = (GEN)A[2];
    /* if no reduction took place in compute_fact, everybody is still coprime
     * to f + no denominators */
    if (!I)
    {
      basecl[i] = (long)famat_to_nf_modidele(nf, L, e, bid);
      continue;
    }
    if (lg(A) == 1)
    {
      basecl[i] = (long)I;
      continue;
    }

    /* compute mulI so that mulI * I coprime to f
     * FIXME: use idealcoprime ??? (Less efficient. Fix idealcoprime!) */
    dmulI = mulI = NULL;
    for (j=1; j<lp; j++)
    {
      pr = listpr[j]; 
      v  = idealval(nf, I, pr);
      if (!v) continue;
      p  = (GEN)pr[1];
      pi = get_pi(F, pr, &vecpi[j]);
      pinvpi = get_pinvpi(nf, fZ, p, pi, &vecpinvpi[j]);
      t = element_pow(nf, pinvpi, stoi(v));
      mulI = mulI? element_mul(nf, mulI, t): t;
      t = gpowgs((GEN)pr[1], v);
      dmulI = dmulI? mulii(dmulI, t): t;
    }

    /* make all components of L coprime to f. 
     * Assuming (L^e * I, f) = 1, then newL^e * mulI = L^e */
    la = lg(e); newL = cgetg(la, t_VEC);
    for (k=1; k<la; k++)
    {
      GEN L0, cx, LL = _algtobasis(nf, (GEN)L[k]);
      L0 = Q_primitive_part(LL, &cx); /* LL = L0*cx (faster element_val) */
      for (j=1; j<lp; j++)
      {
        pr = listpr[j];
        v  = fast_val(nf, L0,cx, pr,vectau[j]); /* = val_pr(LL) */
        if (!v) continue;
        p  = (GEN)pr[1];
        pi = get_pi(F, pr, &vecpi[j]);
        if (v > 0)
        {
          pinvpi = get_pinvpi(nf, fZ, p, pi, &vecpinvpi[j]);
          t = element_pow(nf,pinvpi,stoi(v));
          LL = element_mul(nf, LL, t);
          LL = gdiv(LL, gpowgs(p, v));
        }
        else
        {
          t = element_pow(nf,pi,stoi(-v));
          LL = element_mul(nf, LL, t);
        }
      }
      newL[k] = (long)FpV_red(make_integral(nf,LL,f,listpr), fZ);
    }

    /* G in nf, = L^e mod f */
    G = famat_to_nf_modideal_coprime(nf, newL, e, f, EX);
    if (mulI)
    {
      G = element_muli(nf, G, mulI);
      G = colreducemodHNF(G, gmul(f, dmulI), NULL);
    }
    G = set_sign_mod_idele(nf,A,G,module,sarch);
    I = idealmul(nf,I,G);
    if (dmulI) I = gdivexact(I, dmulI);
    /* more or less useless, but cheap at this point */
    I = _idealmodidele(nf,I,module,sarch);
    basecl[i] = (long)I;
  }
  return basecl;
}

/********************************************************************/
/**                                                                **/
/**                   INIT RAY CLASS GROUP                         **/
/**                                                                **/
/********************************************************************/
static GEN
get_dataunit(GEN bnf, GEN bid)
{
  GEN D, cyc = gmael(bid,2,2), U = init_units(bnf), nf = (GEN)bnf[7];
  long i, l;
  zlog_S S; init_zlog_bid(&S, bid);
  D = zsignunits(bnf, S.archp, 1); l = lg(D);
  for (i = 1; i < l; i++)
    D[i] = (long)vecmodii(gmul(S.U, zlog(nf, (GEN)U[i],(GEN)D[i], &S)), cyc);
  return concatsp(D, diagonal(cyc));
}

static GEN
buchrayall(GEN bnf,GEN module,long flag)
{
  GEN nf, cyc, gen, Gen, u, clg, logs, p1, h, met, u1, u2, U, cycgen;
  GEN bigres, bid, cycbid, genbid, x, y, funits, hmat, El;
  long RU, Ri, j, ngen, lh;
  const int add_gen = flag & nf_GEN;
  const int do_init = flag & nf_INIT;
  pari_sp av = avma;

  bnf = checkbnf(bnf); nf = checknf(bnf);
  funits = check_units(bnf, "buchrayall"); RU = lg(funits);
  El = Gen = NULL; /* gcc -Wall */
  bigres = (GEN)bnf[8];
  cyc = gmael(bigres,1,2);
  gen = gmael(bigres,1,3); ngen = lg(cyc)-1;

  bid = zidealstarinitall(nf,module,1);
  cycbid = gmael(bid,2,2);
  genbid = gmael(bid,2,3);
  Ri = lg(cycbid)-1; lh = ngen+Ri;

  x = idealhermite(nf,module);
  if (Ri || add_gen || do_init)
  {
    El = cgetg(ngen+1,t_VEC);
    for (j=1; j<=ngen; j++)
    {
      p1 = idealcoprime(nf,(GEN)gen[j],x);
      if (isnfscalar(p1)) p1 = (GEN)p1[1];
      El[j] = (long)p1;
    }
  }
  if (add_gen)
  {
    Gen = cgetg(lh+1,t_VEC);
    for (j=1; j<=ngen; j++) Gen[j] = (long)idealmul(nf,(GEN)El[j],(GEN)gen[j]);
    for (   ; j<=lh; j++)   Gen[j] = genbid[j - ngen];
  }
  if (!Ri)
  {
    clg = cgetg(add_gen? 4: 3,t_VEC);
    if (add_gen) clg[3] = (long)Gen;
    clg[1] = mael(bigres,1,1);
    clg[2] = (long)cyc;
    if (!do_init) return gerepilecopy(av,clg);
    y = cgetg(7,t_VEC);
    y[1] = (long)bnf;
    y[2] = (long)bid;
    y[3] = (long)El;
    y[4] = (long)idmat(ngen);
    y[5] = (long)clg; u = cgetg(3,t_VEC);
    y[6] = (long)u;
      u[1] = lgetg(1,t_MAT);
      u[2] = (long)idmat(RU);
    return gerepilecopy(av,y);
  }

  cycgen = check_and_build_cycgen(bnf);
  hmat = hnfall_i( get_dataunit(bnf, bid), do_init? &u: NULL, 1);
  logs = cgetg(ngen+1, t_MAT);
  /* FIXME: cycgen[j] is not necessarily coprime to bid, but it is made coprime
   * in famat_zlog using canonical uniformizers [from bid data]: no need to
   * correct it here. The same ones will be used in isprincipalrayall. Hence
   * modification by El is useless. */
  for (j=1; j<=ngen; j++)
  {
    p1 = (GEN)cycgen[j];
    if (typ(El[j]) != t_INT) /* <==> != 1 */
      p1 = arch_mul(to_famat_all((GEN)El[j], (GEN)cyc[j]), p1);
    logs[j] = (long)zideallog(nf, p1, bid); /* = log(Gen[j]) */
  }
  /* [ cyc  0   ]
   * [-logs hmat] = relation matrix for Cl_f */
  h = concatsp(
    vconcat(diagonal(cyc), gneg_i(logs)),
    vconcat(zeromat(ngen, Ri), hmat)
  );
  met = smithrel(hnf(h), &U, add_gen? &u1: NULL);
  clg = cgetg(add_gen? 4: 3, t_VEC);
  clg[1] = (long)detcyc(met);
  clg[2] = (long)met;
  if (add_gen) clg[3] = (long)compute_raygen(nf,u1,Gen,bid);
  if (!do_init) return gerepilecopy(av, clg);

  u2 = cgetg(Ri+1,t_MAT);
  u1 = cgetg(RU+1,t_MAT);
  for (j=1; j<=RU; j++) { u1[j]=u[j]; setlg(u[j],RU+1); }
  u += RU;
  for (j=1; j<=Ri; j++) { u2[j]=u[j]; setlg(u[j],RU+1); }
 
  y = cgetg(7,t_VEC);
  y[1] = (long)bnf;
  y[2] = (long)bid;
  y[3] = (long)El;
  y[4] = (long)U;
  y[5] = (long)clg; u = cgetg(3,t_VEC);
  y[6] = (long)u;
    u[1] = lmul(u2, ginv(hmat));
    u[2] = (long)lllint_ip(u1,100);
  return gerepilecopy(av,y);
}

GEN
buchrayinitgen(GEN bnf, GEN ideal)
{
  return buchrayall(bnf,ideal, nf_INIT | nf_GEN);
}

GEN
buchrayinit(GEN bnf, GEN ideal)
{
  return buchrayall(bnf,ideal, nf_INIT);
}

GEN
buchray(GEN bnf, GEN ideal)
{
  return buchrayall(bnf,ideal, nf_GEN);
}

GEN
bnrclass0(GEN bnf, GEN ideal, long flag)
{
  switch(flag)
  {
    case 0: flag = nf_GEN; break;
    case 1: flag = nf_INIT; break;
    case 2: flag = nf_INIT | nf_GEN; break;
    default: err(flagerr,"bnrclass");
  }
  return buchrayall(bnf,ideal,flag);
}

GEN
bnrinit0(GEN bnf, GEN ideal, long flag)
{
  switch(flag)
  {
    case 0: flag = nf_INIT; break;
    case 1: flag = nf_INIT | nf_GEN; break;
    default: err(flagerr,"bnrinit");
  }
  return buchrayall(bnf,ideal,flag);
}

GEN
rayclassno(GEN bnf,GEN ideal)
{
  GEN nf, h, D, bigres, bid, cycbid, funits, H;
  pari_sp av = avma;

  bnf = checkbnf(bnf); nf = (GEN)bnf[7];
  bigres = (GEN)bnf[8]; h = gmael(bigres,1,1); /* class number */
  bid = zidealstarinitall(nf,ideal,0);
  cycbid = gmael(bid,2,2);
  if (lg(cycbid) == 1) return gerepileuptoint(av, icopy(h));

  funits = check_units(bnf,"rayclassno");
  D = get_dataunit(bnf, bid);
  H = hnfmodid(D, (GEN)cycbid[1]); /* (Z_K/f)^* / units ~ Z^n / H */
  return gerepileuptoint(av, mulii(h, dethnf_i(H)));
}

GEN
quick_isprincipalgen(GEN bnf, GEN x)
{
  GEN z = cgetg(3, t_VEC), gen = gmael3(bnf,8,1,3);
  GEN idep, ep = isprincipal(bnf,x);
  /* x \prod g[i]^(-ep[i]) = factorisation of principal ideal */
  idep = isprincipalfact(bnf, gen, gneg(ep), x, nf_GENMAT|nf_FORCE);
  z[1] = (long)ep;
  z[2] = idep[2]; return z;
}

GEN
isprincipalrayall(GEN bnr, GEN x, long flag)
{
  long i, j, c;
  pari_sp av = avma;
  GEN bnf, nf, bid, U, El, ep, p1, beta, idep, ex, rayclass, divray, genray;
  GEN alpha;

  checkbnr(bnr); rayclass = (GEN)bnr[5];
  divray = (GEN)rayclass[2]; c = lg(divray);
  ex = cgetg(c,t_COL);
  if (c == 1 && !(flag & nf_GEN)) return ex;

  bnf = (GEN)bnr[1]; nf = (GEN)bnf[7];
  bid = (GEN)bnr[2];
  El  = (GEN)bnr[3];
  U   = (GEN)bnr[4];

  if (typ(x) == t_VEC && lg(x) == 3)
  { idep = (GEN)x[2]; x = (GEN)x[1]; }  /* precomputed */
  else
    idep = quick_isprincipalgen(bnf, x);
  ep  = (GEN)idep[1];
  beta= (GEN)idep[2];
  j = lg(ep);
  for (i=1; i<j; i++) /* modify beta as if gen -> El.gen (coprime to bid) */
    if (typ(El[i]) != t_INT && signe(ep[i])) /* <==> != 1 */
      beta = arch_mul(to_famat_all((GEN)El[i], negi((GEN)ep[i])), beta);
  p1 = gmul(U, concatsp(ep, zideallog(nf,beta,bid)));
  ex = vecmodii(p1, divray);
  if (!(flag & nf_GEN)) return gerepileupto(av, ex);

  /* compute generator */
  if (lg(rayclass)<=3)
    err(talker,"please apply bnrinit(,,1) and not bnrinit(,,0)");

  genray = (GEN)rayclass[3];
  /* TODO: should be using nf_GENMAT and function should return a famat */
  p1 = isprincipalfact(bnf, genray, gneg(ex), x, nf_GEN | nf_FORCE);
  if (!gcmp0((GEN)p1[1])) err(bugparier,"isprincipalray");
  alpha = (GEN)p1[2];
  if (lg(bid[5]) > 1 && lg(mael(bid,5,1)) > 1)
  {
    GEN u = (GEN)bnr[6], y = gmul((GEN)u[1], zideallog(nf, alpha, bid));
    y = reducemodinvertible(y, (GEN)u[2]);
    alpha = element_div(nf, alpha, factorbackelt(init_units(bnf), y, nf));
  }
  p1 = cgetg(3,t_VEC);
  p1[1] = (long)ex;
  p1[2] = (long)alpha;
  return gerepilecopy(av, p1);
}

GEN
isprincipalray(GEN bnr, GEN x)
{
  return isprincipalrayall(bnr,x,0);
}

GEN
isprincipalraygen(GEN bnr, GEN x)
{
  return isprincipalrayall(bnr,x,nf_GEN);
}

/* N! / N^N * (4/pi)^r2 * sqrt(|D|) */
GEN
minkowski_bound(GEN D, long N, long r2, long prec)
{
  pari_sp av = avma;
  GEN p1;
  p1 = gdiv(mpfactr(N,prec), gpowgs(stoi(N),N));
  p1 = gmul(p1, gpowgs(gdivsg(4,mppi(prec)), r2));
  p1 = gmul(p1, gsqrt(absi(D),prec));
  return gerepileupto(av, p1);
}

/* DK = |dK| */
static long
zimmertbound(long N,long R2,GEN DK)
{
  pari_sp av = avma;
  GEN w;

  if (N < 2) return 1;
  if (N < 21)
  {
    static double c[19][11] = {
{/*2*/  0.6931,     0.45158},
{/*3*/  1.71733859, 1.37420604},
{/*4*/  2.91799837, 2.50091538, 2.11943331},
{/*5*/  4.22701425, 3.75471588, 3.31196660},
{/*6*/  5.61209925, 5.09730381, 4.60693851, 4.14303665},
{/*7*/  7.05406203, 6.50550021, 5.97735406, 5.47145968},
{/*8*/  8.54052636, 7.96438858, 7.40555445, 6.86558259, 6.34608077},
{/*9*/ 10.0630022,  9.46382812, 8.87952524, 8.31139202, 7.76081149},
{/*10*/11.6153797, 10.9966020, 10.3907654,  9.79895170, 9.22232770, 8.66213267},
{/*11*/13.1930961, 12.5573772, 11.9330458, 11.3210061, 10.7222412, 10.1378082},
{/*12*/14.7926394, 14.1420915, 13.5016616, 12.8721114, 12.2542699, 11.6490374,
       11.0573775},
{/*13*/16.4112395, 15.7475710, 15.0929680, 14.4480777, 13.8136054, 13.1903162,
       12.5790381},
{/*14*/18.0466672, 17.3712806, 16.7040780, 16.0456127, 15.3964878, 14.7573587,
       14.1289364, 13.5119848},
{/*15*/19.6970961, 19.0111606, 18.3326615, 17.6620757, 16.9999233, 16.3467686,
       15.7032228, 15.0699480},
{/*16*/21.3610081, 20.6655103, 19.9768082, 19.2953176, 18.6214885, 17.9558093,
       17.2988108, 16.6510652, 16.0131906},

{/*17*/23.0371259, 22.3329066, 21.6349299, 20.9435607, 20.2591899, 19.5822454,
       18.9131878, 18.2525157, 17.6007672},

{/*18*/24.7243611, 24.0121449, 23.3056902, 22.6053167, 21.9113705, 21.2242247,
       20.5442836, 19.8719830, 19.2077941, 18.5522234},

{/*19*/26.4217792, 25.7021950, 24.9879497, 24.2793271, 23.5766321, 22.8801952,
       22.1903709, 21.5075437, 20.8321263, 20.1645647},
{/*20*/28.1285704, 27.4021674, 26.6807314, 25.9645140, 25.2537867, 24.5488420,
       23.8499943, 23.1575823, 22.4719720, 21.7935548, 21.1227537}
    };
    w = gmul(dbltor(exp(-c[N-2][R2])), gsqrt(DK,MEDDEFAULTPREC));
  }
  else
  {
    w = minkowski_bound(DK, N, R2, MEDDEFAULTPREC);
    if (cmpis(w, 500000))
      err(warner,"large Minkowski bound: certification will be VERY long");
  }
  w = gceil(w);
  if (is_bigint(w))
    err(talker,"Minkowski bound is too large");
  avma = av; return itos(w);
}

/* return \gamma_n^n if known, an upper bound otherwise */
static GEN
hermiteconstant(long n)
{
  GEN h,h1;
  pari_sp av;

  switch(n)
  {
    case 1: return gun;
    case 2: h=cgetg(3,t_FRAC); h[1]=lstoi(4); h[2]=lstoi(3); return h;
    case 3: return gdeux;
    case 4: return stoi(4);
    case 5: return stoi(8);
    case 6: h=cgetg(3,t_FRAC); h[1]=lstoi(64); h[2]=lstoi(3); return h;
    case 7: return stoi(64);
    case 8: return stoi(256);
  }
  av = avma;
  h  = gpowgs(divsr(2,mppi(DEFAULTPREC)), n);
  h1 = gsqr(ggamma(gdivgs(stoi(n+4),2),DEFAULTPREC));
  return gerepileupto(av, gmul(h,h1));
}

/* 1 if L (= nf != Q) primitive for sure, 0 if MAYBE imprimitive (may have a
 * subfield K) */
static long
isprimitive(GEN nf)
{
  long N,p,i,l,ep;
  GEN d,fa;

  N = degpol(nf[1]); fa = (GEN)factor(stoi(N))[1]; /* primes | N */
  p = itos((GEN)fa[1]); if (p == N) return 1; /* prime degree */

  /* N = [L:Q] = product of primes >= p, same is true for [L:K]
   * d_L = t d_K^[L:K] --> check that some q^p divides d_L */
  d = absi((GEN)nf[3]);
  fa = (GEN)auxdecomp(d,0)[2]; /* list of v_q(d_L). Don't check large primes */
  if (mod2(d)) i = 1;
  else
  { /* q = 2 */
    ep = itos((GEN)fa[1]);
    if ((ep>>1) >= p) return 0; /* 2 | d_K ==> 4 | d_K */
    i = 2;
  }
  l = lg(fa);
  for ( ; i < l; i++)
  {
    ep = itos((GEN)fa[i]);
    if (ep >= p) return 0;
  }
  return 1;
}

static GEN
dft_bound()
{
  if (DEBUGLEVEL>1) fprintferr("Default bound for regulator: 0.2\n");
  return dbltor(0.2);
}

static GEN
regulatorbound(GEN bnf)
{
  long N, R1, R2, R;
  GEN nf, dKa, p1, c1;

  nf = (GEN)bnf[7]; N = degpol(nf[1]);
  if (!isprimitive(nf)) return dft_bound();

  dKa = absi((GEN)nf[3]);
  nf_get_sign(nf, &R1, &R2); R = R1+R2-1;
  if (!R2 && N<12) c1 = gpowgs(stoi(4),N>>1); else c1 = gpowgs(stoi(N),N);
  if (cmpii(dKa,c1) <= 0) return dft_bound();

  p1 = gsqr(glog(gdiv(dKa,c1),DEFAULTPREC));
  p1 = divrs(gmul2n(gpowgs(divrs(mulrs(p1,3),N*(N*N-1)-6*R2),R),R2), N);
  p1 = mpsqrt(gdiv(p1, hermiteconstant(R)));
  if (DEBUGLEVEL>1) fprintferr("Mahler bound for regulator: %Z\n",p1);
  return gmax(p1, dbltor(0.2));
}

/* x given by its embeddings */
GEN
norm_by_embed(long r1, GEN x)
{
  long i, ru = lg(x)-1;
  GEN p = (GEN)x[ru];
  if (r1 == ru)
  {
    for (i=ru-1; i>0; i--) p = gmul(p, (GEN)x[i]);
    return p;
  }
  p = gnorm(p);
  for (i=ru-1; i>r1; i--) p = gmul(p, gnorm((GEN)x[i]));
  for (      ; i>0 ; i--) p = gmul(p, (GEN)x[i]);
  return p;
}

static int
is_unit(GEN M, long r1, GEN x)
{
  pari_sp av = avma;
  GEN Nx = ground( norm_by_embed(r1, gmul_mat_smallvec(M,x)) );
  int ok = is_pm1(Nx);
  avma = av; return ok;
}

/* FIXME: should use smallvectors */
static GEN
minimforunits(GEN nf, long BORNE, GEN w)
{
  const long prec = MEDDEFAULTPREC;
  long n, i, j, k, s, *x, r1, cnt = 0;
  pari_sp av = avma;
  GEN u,r,a,M;
  double p, norme, normin, normax;
  double **q,*v,*y,*z;
  double eps=0.000001, BOUND = BORNE * 1.00001;

  if (DEBUGLEVEL>=2)
  {
    fprintferr("Searching minimum of T2-form on units:\n");
    if (DEBUGLEVEL>2) fprintferr("   BOUND = %ld\n",BOUND);
    flusherr();
  }
  r1 = nf_get_r1(nf); n = degpol(nf[1]);
  minim_alloc(n+1, &q, &x, &y, &z, &v);
  M = gprec_w(gmael(nf,5,1), prec);
  a = gmul(gmael(nf,5,2), realun(prec));
  r = sqred1_from_QR(a, prec);
  for (j=1; j<=n; j++)
  {
    v[j] = rtodbl(gcoeff(r,j,j));
    for (i=1; i<j; i++) q[i][j] = rtodbl(gcoeff(r,i,j));
  }
  normax = 0.; normin = (double)BOUND;
  s=0; k=n; y[n]=z[n]=0;
  x[n]=(long)(sqrt(BOUND/v[n]));

  for(;;)
  {
    do
    {
      if (k>1)
      {
        long l = k-1;
	z[l] = 0;
	for (j=k; j<=n; j++) z[l] = z[l]+q[l][j]*x[j];
	p = (double)x[k] + z[k];
	y[l] = y[k]+p*p*v[k];
	x[l] = (long)floor(sqrt((BOUND-y[l])/v[l])-z[l]);
        k = l;
      }
      for(;;)
      {
	p = (double)x[k] + z[k];
        if (y[k] + p*p*v[k] <= BOUND) break;
	k++; x[k]--;
      }
    }
    while (k>1);
    if (!x[1] && y[1]<=eps) break;

    if (DEBUGLEVEL>8){ fprintferr("."); flusherr(); }
    if (++cnt == 5000) return NULL; /* too expensive */

    p = (double)x[1] + z[1]; norme = y[1] + p*p*v[1] + eps;
    if (norme > normax) normax = norme;
    if (is_unit(M,r1, x)
    && (norme > 2*n  /* exclude roots of unity */
        || !isnfscalar(element_pow(nf, small_to_col(x), w))))
    {
      if (norme < normin) normin = norme;
      if (DEBUGLEVEL>=2) { fprintferr("*"); flusherr(); }
    }
    x[k]--;
  }
  if (DEBUGLEVEL>=2){ fprintferr("\n"); flusherr(); }
  avma = av; u = cgetg(4,t_VEC);
  u[1] = lstoi(s<<1);
  u[2] = (long)dbltor(normax);
  u[3] = (long)dbltor(normin);
  return u;
}

#undef NBMAX
static int
is_zero(GEN x, long bitprec) { return (gexpo(x) < -bitprec); }

static int
is_complex(GEN x, long bitprec) { return (!is_zero(gimag(x), bitprec)); }

static GEN
compute_M0(GEN M_star,long N)
{
  long m1,m2,n1,n2,n3,k,kk,lr,lr1,lr2,i,j,l,vx,vy,vz,vM,prec;
  GEN pol,p1,p2,p3,p4,p5,p6,p7,p8,p9,u,v,w,r,r1,r2,M0,M0_pro,S,P,M;
  GEN f1,f2,f3,g1,g2,g3,pg1,pg2,pg3,pf1,pf2,pf3,X,Y,Z;
  long bitprec = 24, PREC = gprecision(M_star);

  if (N==2) return gmul2n(gsqr(gach(gmul2n(M_star,-1),PREC)), -1);
  vM = fetch_var(); M = polx[vM];
  vz = fetch_var(); Z = polx[vz];
  vy = fetch_var(); Y = polx[vy];
  vx = fetch_var(); X = polx[vx];

  PREC = PREC>>1; if (!PREC) PREC = DEFAULTPREC;
  M0 = NULL; m1 = N/3;
  for (n1=1; n1<=m1; n1++)
  {
    m2 = (N-n1)>>1;
    for (n2=n1; n2<=m2; n2++)
    {
      pari_sp av = avma; n3=N-n1-n2; prec=PREC;
      if (n1==n2 && n1==n3) /* n1 = n2 = n3 = m1 = N/3 */
      {
	p1=gdivgs(M_star,m1);
        p2=gaddsg(1,p1);
        p3=gsubgs(p1,3);
	p4=gsqrt(gmul(p2,p3),prec);
        p5=gsubgs(p1,1);
	u=gun;
        v=gmul2n(gadd(p5,p4),-1);
        w=gmul2n(gsub(p5,p4),-1);
	M0_pro=gmul2n(gmulsg(m1,gadd(gsqr(glog(v,prec)),gsqr(glog(w,prec)))),-2);
	if (DEBUGLEVEL>2)
	{
	  fprintferr("[ %ld, %ld, %ld ]: %Z\n",n1,n2,n3,gprec_w(M0_pro,3));
	  flusherr();
	}
	if (!M0 || gcmp(M0_pro,M0)<0) M0 = M0_pro;
      }
      else if (n1==n2 || n2==n3)
      { /* n3 > N/3 >= n1 */
	k = n2; kk = N-2*k;
	p2=gsub(M_star,gmulgs(X,k));
	p3=gmul(gpowgs(stoi(kk),kk),gpowgs(gsubgs(gmul(M_star,p2),kk*kk),k));
	pol=gsub(p3,gmul(gmul(gpowgs(stoi(k),k),gpowgs(X,k)),gpowgs(p2,N-k)));
	prec=gprecision(pol); if (!prec) prec = MEDDEFAULTPREC;
	r=roots(pol,prec); lr = lg(r);
	for (i=1; i<lr; i++)
	{
	  if (is_complex((GEN)r[i], bitprec) ||
	      signe(S = greal((GEN)r[i])) <= 0) continue;

          p4=gsub(M_star,gmulsg(k,S));
          P=gdiv(gmul(gmulsg(k,S),p4),gsubgs(gmul(M_star,p4),kk*kk));
          p5=gsub(gsqr(S),gmul2n(P,2));
          if (gsigne(p5) < 0) continue;

          p6=gsqrt(p5,prec);
          v=gmul2n(gsub(S,p6),-1);
          if (gsigne(v) <= 0) continue;

          u=gmul2n(gadd(S,p6),-1);
          w=gpow(P,gdivgs(stoi(-k),kk),prec);
          p6=gmulsg(k,gadd(gsqr(glog(u,prec)),gsqr(glog(v,prec))));
          M0_pro=gmul2n(gadd(p6,gmulsg(kk,gsqr(glog(w,prec)))),-2);
          if (DEBUGLEVEL>2)
          {
            fprintferr("[ %ld, %ld, %ld ]: %Z\n",n1,n2,n3,gprec_w(M0_pro,3));
            flusherr();
          }
          if (!M0 || gcmp(M0_pro,M0)<0) M0 = M0_pro;
	}
      }
      else
      {
	f1 = gsub(gadd(gmulsg(n1,X),gadd(gmulsg(n2,Y),gmulsg(n3,Z))), M);
	f2 =         gmulsg(n1,gmul(Y,Z));
	f2 = gadd(f2,gmulsg(n2,gmul(X,Z)));
	f2 = gadd(f2,gmulsg(n3,gmul(X,Y)));
	f2 = gsub(f2,gmul(M,gmul(X,gmul(Y,Z))));
	f3 = gsub(gmul(gpowgs(X,n1),gmul(gpowgs(Y,n2),gpowgs(Z,n3))), gun);
        /* f1 = n1 X + n2 Y + n3 Z - M */
        /* f2 = n1 YZ + n2 XZ + n3 XY */
        /* f3 = X^n1 Y^n2 Z^n3 - 1*/
	g1=subres(f1,f2); g1=gdiv(g1,content(g1));
	g2=subres(f1,f3); g2=gdiv(g2,content(g2));
	g3=subres(g1,g2); g3=gdiv(g3,content(g3));
	pf1=gsubst(f1,vM,M_star); pg1=gsubst(g1,vM,M_star);
	pf2=gsubst(f2,vM,M_star); pg2=gsubst(g2,vM,M_star);
	pf3=gsubst(f3,vM,M_star); pg3=gsubst(g3,vM,M_star);
	prec=gprecision(pg3); if (!prec) prec = MEDDEFAULTPREC;
	r=roots(pg3,prec); lr = lg(r);
	for (i=1; i<lr; i++)
	{
	  if (is_complex((GEN)r[i], bitprec) ||
	      signe(w = greal((GEN)r[i])) <= 0) continue;
          p1=gsubst(pg1,vz,w);
          p2=gsubst(pg2,vz,w);
          p3=gsubst(pf1,vz,w);
          p4=gsubst(pf2,vz,w);
          p5=gsubst(pf3,vz,w);
          prec=gprecision(p1); if (!prec) prec = MEDDEFAULTPREC;
          r1 = roots(p1,prec); lr1 = lg(r1);
          for (j=1; j<lr1; j++)
          {
            if (is_complex((GEN)r1[j], bitprec)
             || signe(v = greal((GEN)r1[j])) <= 0
             || !is_zero(gsubst(p2,vy,v), bitprec)) continue;

            p7=gsubst(p3,vy,v);
            p8=gsubst(p4,vy,v);
            p9=gsubst(p5,vy,v);
            prec=gprecision(p7); if (!prec) prec = MEDDEFAULTPREC;
            r2 = roots(p7,prec); lr2 = lg(r2);
            for (l=1; l<lr2; l++)
            {
              if (is_complex((GEN)r2[l], bitprec)
               || signe(u = greal((GEN)r2[l])) <= 0
               || !is_zero(gsubst(p8,vx,u), bitprec)
               || !is_zero(gsubst(p9,vx,u), bitprec)) continue;

              M0_pro =              gmulsg(n1,gsqr(mplog(u)));
              M0_pro = gadd(M0_pro, gmulsg(n2,gsqr(mplog(v))));
              M0_pro = gadd(M0_pro, gmulsg(n3,gsqr(mplog(w))));
              M0_pro = gmul2n(M0_pro,-2);
              if (DEBUGLEVEL>2)
              {
               fprintferr("[ %ld, %ld, %ld ]: %Z\n",n1,n2,n3,gprec_w(M0_pro,3));
               flusherr();
              }
              if (!M0 || gcmp(M0_pro,M0) < 0) M0 = M0_pro;
            }
          }
	}
      }
      if (!M0) avma = av; else M0 = gerepilecopy(av, M0);
    }
  }
  for (i=1;i<=4;i++) (void)delete_var();
  return M0? M0: gzero;
}

static GEN
lowerboundforregulator_i(GEN bnf)
{
  long N,R1,R2,RU,i;
  GEN nf,M0,M,G,bound,minunit,newminunit;
  GEN vecminim,p1,pol,y;
  GEN units = check_units(bnf,"bnfcertify");

  nf = (GEN)bnf[7]; N = degpol(nf[1]);
  nf_get_sign(nf, &R1, &R2); RU = R1+R2-1;
  if (!RU) return gun;

  G = gmael(nf,5,2);
  units = algtobasis(bnf,units);
  minunit = gnorml2(gmul(G, (GEN)units[1])); /* T2(units[1]) */
  for (i=2; i<=RU; i++)
  {
    newminunit = gnorml2(gmul(G, (GEN)units[i]));
    if (gcmp(newminunit,minunit) < 0) minunit = newminunit;
  }
  if (gexpo(minunit) > 30) return NULL;

  vecminim = minimforunits(nf, itos(gceil(minunit)), gmael3(bnf,8,4,1));
  if (!vecminim) return NULL;
  bound = (GEN)vecminim[3];
  if (DEBUGLEVEL>1)
  {
    fprintferr("M* = %Z\n", bound);
    if (DEBUGLEVEL>2)
    {
      p1=polx[0]; pol=gaddgs(gsub(gpowgs(p1,N),gmul(bound,p1)),N-1);
      p1 = roots(pol,DEFAULTPREC);
      if (N&1) y=greal((GEN)p1[3]); else y=greal((GEN)p1[2]);
      M0 = gmul2n(gmulsg(N*(N-1),gsqr(glog(y,DEFAULTPREC))),-2);
      fprintferr("pol = %Z\n",pol);
      fprintferr("old method: y = %Z, M0 = %Z\n",y,gprec_w(M0,3));
    }
  }
  M0 = compute_M0(bound,N);
  if (DEBUGLEVEL>1) { fprintferr("M0 = %Z\n",gprec_w(M0,3)); flusherr(); }
  M = gmul2n(gdivgs(gdiv(gpowgs(M0,RU),hermiteconstant(RU)),N),R2);
  if (gcmp(M, dbltor(0.04)) < 0) return NULL;
  M = gsqrt(M,DEFAULTPREC);
  if (DEBUGLEVEL>1)
    fprintferr("(lower bound for regulator) M = %Z\n",gprec_w(M,3));
  return M;
}

static GEN
lowerboundforregulator(GEN bnf)
{
  pari_sp av = avma;
  GEN x = lowerboundforregulator_i(bnf);
  if (!x) { avma = av; x = regulatorbound(bnf); }
  return x;
}

/* Compute a square matrix of rank length(beta) associated to a family
 * (P_i), 1<=i<=length(beta), of primes s.t. N(P_i) = 1 mod pp, and
 * (P_i,beta[j]) = 1 for all i,j */
static void
primecertify(GEN bnf,GEN beta,long pp,GEN big)
{
  long i,j,qq,nbcol,lb,nbqq,ra,N;
  GEN nf,mat,mat1,qgen,decqq,newcol,Q,g,ord,modpr;

  ord = NULL; /* gcc -Wall */
  nbcol = 0; nf = (GEN)bnf[7]; N = degpol(nf[1]);
  lb = lg(beta)-1; mat = cgetg(1,t_MAT); qq = 1;
  for(;;)
  {
    qq += 2*pp; qgen = stoi(qq);
    if (smodis(big,qq)==0 || !isprime(qgen)) continue;

    decqq = primedec(bnf,qgen); nbqq = lg(decqq)-1;
    g = NULL;
    for (i=1; i<=nbqq; i++)
    {
      Q = (GEN)decqq[i]; if (!gcmp1((GEN)Q[4])) break;
      /* Q has degree 1 */
      if (!g)
      {
        g = lift_intern(gener(qgen)); /* primitive root */
        ord = decomp(stoi(qq-1));
      }
      modpr = zkmodprinit(nf, Q);
      newcol = cgetg(lb+1,t_COL);
      for (j=1; j<=lb; j++)
      {
        GEN t = to_Fp_simple(nf, (GEN)beta[j], modpr);
        newcol[j] = (long)Fp_PHlog(t,g,qgen,ord);
      }
      if (DEBUGLEVEL>3)
      {
        if (i==1) fprintferr("       generator of (Zk/Q)^*: %Z\n", g);
        fprintferr("       prime ideal Q: %Z\n",Q);
        fprintferr("       column #%ld of the matrix log(b_j/Q): %Z\n",
                   nbcol, newcol);
      }
      mat1 = concatsp(mat,newcol); ra = rank(mat1);
      if (ra==nbcol) continue;

      if (DEBUGLEVEL>2) fprintferr("       new rank: %ld\n",ra);
      if (++nbcol == lb) return;
      mat = mat1;
    }
  }
}

static void
check_prime(long p, GEN bnf, GEN cyc, GEN cycgen, GEN fu, GEN mu, GEN big)
{
  pari_sp av = avma;
  long i,b, lc = lg(cyc), w = itos((GEN)mu[1]), lf = lg(fu);
  GEN beta = cgetg(lf+lc, t_VEC);

  if (DEBUGLEVEL>1) fprintferr("  *** testing p = %ld\n",p);
  for (b=1; b<lc; b++)
  {
    if (smodis((GEN)cyc[b], p)) break; /* p \nmod cyc[b] */
    if (b==1 && DEBUGLEVEL>2) fprintferr("     p divides h(K)\n");
    beta[b] = cycgen[b];
  }
  if (w % p == 0)
  {
    if (DEBUGLEVEL>2) fprintferr("     p divides w(K)\n");
    beta[b++] = mu[2];
  }
  for (i=1; i<lf; i++) beta[b++] = fu[i];
  setlg(beta, b); /* beta = [cycgen[i] if p|cyc[i], tu if p|w, fu] */
  if (DEBUGLEVEL>3) {fprintferr("     Beta list = %Z\n",beta); flusherr();}
  primecertify(bnf,beta,p,big); avma = av;
}

long
certifybuchall(GEN bnf)
{
  pari_sp av = avma;
  long nbgen,i,j,p,N,R1,R2,R,bound;
  GEN big,nf,reg,rootsofone,funits,gen,p1,gbound,cycgen,cyc;
  byteptr delta = diffptr;

  bnf = checkbnf(bnf); nf = (GEN)bnf[7];
  N=degpol(nf[1]); if (N==1) return 1;
  nf_get_sign(nf, &R1, &R2); R = R1+R2-1;
  funits = check_units(bnf,"bnfcertify");
  testprimes(bnf, zimmertbound(N,R2,absi((GEN)nf[3])));
  reg = gmael(bnf,8,2);
  cyc = gmael3(bnf,8,1,2); nbgen = lg(cyc)-1;
  gen = gmael3(bnf,8,1,3); rootsofone = gmael(bnf,8,4);
  gbound = ground(gdiv(reg,lowerboundforregulator(bnf)));
  if (is_bigint(gbound))
    err(talker,"sorry, too many primes to check");

  bound = itos(gbound);
  maxprime_check((ulong)bound);
  if (DEBUGLEVEL>1)
  {
    fprintferr("\nPHASE 2: are all primes good ?\n\n");
    fprintferr("  Testing primes <= B (= %ld)\n\n",bound); flusherr();
  }
  cycgen = check_and_build_cycgen(bnf);
  for (big=gun,i=1; i<=nbgen; i++)
    big = mpppcm(big, gcoeff(gen[i],1,1));
  for (i=1; i<=nbgen; i++)
  {
    p1 = (GEN)cycgen[i];
    if (typ(p1) == t_MAT)
    {
      GEN h, g = (GEN)p1[1];
      for (j=1; j<lg(g); j++)
      {
        h = idealhermite(nf, (GEN)g[j]);
        big = mpppcm(big, gcoeff(h,1,1));
      }
    }
  } /* p | big <--> p | some cycgen[i]  */

  funits = dummycopy(funits);
  for (i=1; i<lg(funits); i++)
    funits[i] = (long)algtobasis(nf, (GEN)funits[i]);
  rootsofone = dummycopy(rootsofone);
  rootsofone[2] = (long)algtobasis(nf, (GEN)rootsofone[2]);

  for (p = *delta++; p <= bound; ) {  
    check_prime(p,bnf,cyc,cycgen,funits,rootsofone,big);
    NEXT_PRIME_VIADIFF(p, delta);
  }

  if (nbgen)
  {
    GEN f = factor((GEN)cyc[1]), f1 = (GEN)f[1];
    long nbf1 = lg(f1);
    if (DEBUGLEVEL>1) { fprintferr("  Testing primes | h(K)\n\n"); flusherr(); }
    for (i=1; i<nbf1; i++)
    {
      p = itos((GEN)f1[i]);
      if (p > bound) check_prime(p,bnf,cyc,cycgen,funits,rootsofone,big);
    }
  }
  avma=av; return 1;
}

/*******************************************************************/
/*                                                                 */
/*        RAY CLASS FIELDS: CONDUCTORS AND DISCRIMINANTS           */
/*                                                                 */
/*******************************************************************/
GEN
bnrGetSurj(GEN bnr1, GEN bnr2)
{
  long l, i;
  GEN gen, M;

  gen = gmael(bnr1, 5, 3);
  l = lg(gen); M = cgetg(l, t_MAT);
  for (i = 1; i < l; i++)
    M[i] = (long)isprincipalray(bnr2, (GEN)gen[i]);
  return M;
}

/* Kernel of the above map */
static GEN
bnrGetKer(GEN bnr, GEN mod2)
{
  long i, n;
  pari_sp av = avma;
  GEN P,U, bnr2 = buchrayall(bnr,mod2,nf_INIT);

  P = bnrGetSurj(bnr, bnr2); n = lg(P);
  P = concatsp(P, diagonal(gmael(bnr2,5,2)));
  U = (GEN)hnfall(P)[2]; setlg(U,n);
  for (i=1; i<n; i++) setlg(U[i], n);
  U = concatsp(U, diagonal(gmael(bnr, 5,2)));
  return gerepileupto(av, hnf(U));
}

/* s: <gen> = Cl_f --> Cl_f2 --> 0, H subgroup of Cl_f (generators given as
 * HNF on [gen]). Return subgroup s(H) in Cl_f2 */
static GEN
imageofgroup(GEN bnr, GEN bnr2, GEN H)
{
  GEN H2, Delta = diagonal(gmael(bnr2,5,2)); /* SNF structure of Cl_n */

  if (!H || gcmp0(H)) return Delta;
  H2 = gmul(bnrGetSurj(bnr, bnr2), H);
  return hnf( concatsp(H2, Delta) ); /* s(H) in Cl_n */
}

static GEN
args_to_bnr(GEN arg0, GEN arg1, GEN arg2, GEN *subgroup, int gen)
{
  GEN bnr,bnf;

  if (typ(arg0)!=t_VEC)
    err(talker,"neither bnf nor bnr in conductor or discray");
  if (!arg1) arg1 = gzero;
  if (!arg2) arg2 = gzero;

  switch(lg(arg0))
  {
    case 7:  /* bnr */
      bnr = arg0; (void)checkbnf((GEN)bnr[1]);
      *subgroup = arg1; break;

    case 11: /* bnf */
      bnf = checkbnf(arg0);
      bnr = buchrayall(bnf,arg1, gen? nf_INIT | nf_GEN: nf_INIT);
      *subgroup = arg2; break;

    default: err(talker,"neither bnf nor bnr in conductor or discray");
      return NULL; /* not reached */
  }
  if (!gcmp0(*subgroup))
  {
    long tx = typ(*subgroup);
    if (!is_matvec_t(tx))
      err(talker,"bad subgroup in conductor or discray");
  }
  return bnr;
}

GEN
bnrconductor(GEN arg0,GEN arg1,GEN arg2,GEN all)
{
  long flag = all? itos(all): 0;
  GEN sub = arg1, bnr = args_to_bnr(arg0,arg1,arg2,&sub, flag > 0);
  return conductor(bnr,sub, flag);
}

long
bnrisconductor(GEN arg0,GEN arg1,GEN arg2)
{
  GEN sub = arg1, bnr = args_to_bnr(arg0,arg1,arg2,&sub, 0);
  return itos(conductor(bnr,sub,-1));
}

static GEN
check_subgroup(GEN bnr, GEN H, GEN *clhray, int triv_is_NULL, char *s)
{
  GEN h, D = NULL;
  if (H && gcmp0(H)) H = NULL;
  if (H)
  {
    D = diagonal(gmael(bnr,5,2));
    H = hnf(H);
    if (!hnfdivide(H, D)) err(talker,"incorrect subgroup in %s", s);
    h = dethnf_i(H);
    if (egalii(h, *clhray)) H = NULL; else *clhray = h;
  }
  if (!H && !triv_is_NULL) H = D? D: diagonal(gmael(bnr,5,2));
  return H;
}

extern GEN log_gen_pr(zlog_S *S, long index, GEN nf, long e);
extern GEN log_gen_arch(zlog_S *S, long index);
extern GEN factorbackprime(GEN nf, GEN L, GEN e);
extern GEN hnf_gauss(GEN A, GEN B);

/* return bnrisprincipal(bnr, (x)), assuming z = ideallog(x) */
static GEN
ideallog_to_bnr(GEN bnr, GEN z)
{
  GEN rayclass = (GEN)bnr[5], U = (GEN)bnr[4], divray = (GEN)rayclass[2];
  long j, l, lU, lz;
  int col;

  if (lg(z) == 1) return z;
  col = (typ(z) == t_COL); /* else t_MAT */
  lz = col? lg(z): lg(z[1]);
  lU = lg(U);
  if (lz != lU)
  {
    if (lz == 1) return zerocol(lg(U[1]) - 1); /* lU != 1 */
    U = vecextract_i(U, lU-lz+1, lU-1); /* remove Cl(K) part */
  }
  z = gmul(U, z);
  if (col)
    z = vecmodii(z, divray);
  else
  {
    l = lg(z);
    for (j = 1; j < l; j++) z[j] = (long)vecmodii((GEN)z[j], divray);
  }
  return z;
}
static GEN
bnr_log_gen_pr(GEN bnr, zlog_S *S, GEN nf, long e, long index)
{
  return ideallog_to_bnr(bnr, log_gen_pr(S, index, nf, e));
}
static GEN
bnr_log_gen_arch(GEN bnr, zlog_S *S, long index)
{
  return ideallog_to_bnr(bnr, log_gen_arch(S, index));
}

/* A \subset H ? Allow H = NULL = trivial subgroup */
static int
contains(GEN H, GEN A)
{
  return H? (hnf_gauss(H, A) != NULL): gcmp0(A);
}

/* (see also discrayrelall). Given a number field bnf=bnr[1], a ray class
 * group structure bnr (with generators if all > 0), and a subgroup H of the
 * ray class group, compute the conductor of H if all=0. If all > 0, compute
 * furthermore the corresponding H' and output
 * if all = 1: [[ideal,arch],[hm,cyc,gen],H']
 * if all = 2: [[ideal,arch],newbnr,H']
 * if all < 0, answer only 1 is module is the conductor, 0 otherwise. */
GEN
conductor(GEN bnr, GEN H0, long all)
{
  pari_sp av = avma;
  long j, k, l;
  GEN bnf, nf, bid, ideal, archp, p1, clhray, bnr2;
  GEN e2, e, mod, H;
  zlog_S S;

  if (all > 0) checkbnrgen(bnr); else checkbnr(bnr);
  bnf = (GEN)bnr[1];
  bid = (GEN)bnr[2]; init_zlog_bid(&S, bid);
  clhray = gmael(bnr,5,1);
  nf = (GEN)bnf[7];
  H = check_subgroup(bnr, H0, &clhray, 1, "conductor");

  archp = S.archp;
  e     = S.e; l = lg(e);
  e2 = cgetg(l, t_COL);
  for (k = 1; k < l; k++)
  {
    for (j = itos((GEN)e[k]); j > 0; j--)
    {
      if (!contains(H, bnr_log_gen_pr(bnr, &S, nf, j, k))) break;
      if (all < 0) { avma = av; return gzero; }
    }
    e2[k] = lstoi(j);
  }
  l = lg(archp);
  for (k = 1; k < l; k++)
  {
    if (!contains(H, bnr_log_gen_arch(bnr, &S, k))) continue;
    if (all < 0) { avma = av; return gzero; }
    archp[k] = 0;
  }
  if (all < 0) { avma = av; return gun; }
  ideal = gegal(e2, e)? gmael(bid,1,1): factorbackprime(nf, S.P, e2);
  for (j = k = 1; k < l; k++)
    if (archp[k]) archp[j++] = archp[k];
  setlg(archp, j);
  mod = cgetg(3,t_VEC);
  mod[1] = (long)ideal;
  mod[2] = (long)perm_to_arch(nf, archp);
  if (!all) return gerepilecopy(av, mod);

  bnr2 = buchrayall(bnf, mod, nf_INIT | nf_GEN);
  p1 = cgetg(4,t_VEC);
  p1[3] = (long)imageofgroup(bnr, bnr2, H);
  p1[2] = (all == 1)? bnr2[5]: (long)bnr2;
  p1[1] = (long)mod; return gerepilecopy(av, p1);
}

/* return the norm group corresponding to the relative extension given by
 * polrel over bnr.bnf, assuming it is abelian and the modulus of bnr is a
 * multiple of the conductor */
GEN
rnfnormgroup(GEN bnr, GEN polrel)
{
  long i, j, reldeg, sizemat, p, nfac, k;
  pari_sp av = avma;
  GEN bnf,index,discnf,nf,raycl,group,detgroup,fa,greldeg;
  GEN famo,ep,fac,col;
  byteptr d = diffptr;

  checkbnr(bnr); bnf=(GEN)bnr[1]; raycl=(GEN)bnr[5];
  nf=(GEN)bnf[7];
  polrel = fix_relative_pol(nf,polrel,1);
  if (typ(polrel)!=t_POL) err(typeer,"rnfnormgroup");
  reldeg = degpol(polrel);
  /* reldeg-th powers are in norm group */
  greldeg = stoi(reldeg);
  group = diagonal(gmod((GEN)raycl[2], greldeg));
  for (i=1; i<lg(group); i++)
    if (!signe(gcoeff(group,i,i))) coeff(group,i,i) = (long)greldeg;
  detgroup = dethnf_i(group);
  k = cmpis(detgroup,reldeg);
  if (k < 0)
    err(talker,"not an Abelian extension in rnfnormgroup?");
  if (!k) return gerepilecopy(av, group);

  discnf = (GEN)nf[3];
  index  = (GEN)nf[4];
  sizemat=lg(group)-1;
  for (p=0 ;;)
  {
    long oldf = -1, lfa;
    /* If all pr are unramified and have the same residue degree, p =prod pr
     * and including last pr^f or p^f is the same, but the last isprincipal
     * is much easier! oldf is used to track this */

    NEXT_PRIME_VIADIFF_CHECK(p,d);
    if (!smodis(index, p)) continue; /* can't be treated efficiently */

    fa = primedec(nf, stoi(p)); lfa = lg(fa)-1;
    for (i=1; i<=lfa; i++)
    {
      GEN pr = (GEN)fa[i], pp, T, polr;
      GEN modpr = nf_to_ff_init(nf, &pr, &T, &pp);
      long f;

      polr = modprX(polrel, nf, modpr);
      /* if pr (probably) ramified, we have to use all (non-ram) P | pr */
      if (!FqX_is_squarefree(polr, T,pp)) { oldf = 0; continue; }

      famo = FqX_factor(polr, T, pp);
      fac = (GEN)famo[1]; f = degpol((GEN)fac[1]);
      ep  = (GEN)famo[2]; nfac = lg(ep)-1;
      /* check decomposition of pr has Galois type */
      for (j=1; j<=nfac; j++)
      {
        if (!gcmp1((GEN)ep[j])) err(bugparier,"rnfnormgroup");
        if (degpol(fac[j]) != f)
          err(talker,"non Galois extension in rnfnormgroup");
      }
      if (oldf < 0) oldf = f; else if (oldf != f) oldf = 0;
      if (f == reldeg) continue; /* reldeg-th powers already included */

      if (oldf && i == lfa && !smodis(discnf, p)) pr = stoi(p);

      /* pr^f = N P, P | pr, hence is in norm group */
      col = gmulsg(f, isprincipalrayall(bnr,pr,0));
      group = hnf(concatsp(group, col));
      detgroup = dethnf_i(group);
      k = cmpis(detgroup,reldeg);
      if (k < 0)
        err(talker,"not an Abelian extension in rnfnormgroup");
      if (!k) { cgiv(detgroup); return gerepileupto(av,group); }
    }
  }
  if (k>0) err(bugparier,"rnfnormgroup");
  cgiv(detgroup); return gerepileupto(av,group);
}

static GEN
liftpol(GEN pol, GEN q, long v)
{
  long i, l = lgef(pol);
  GEN y = cgetg(l, t_POL);
  y[1] = pol[1];
  for (i = 2; i < l; i++)
  {
    y[i] = (long)lift_intern(poleval((GEN)pol[i], q));
    if (typ(y[i]) == t_POL) setvarn(y[i], v);
  }
  return y;
}

/* FIXME: check should be done mod p [ p \nmid Norm(disc(pol)) ]*/
static int
rnf_is_abelian(GEN nf, GEN pol)
{
  GEN ro, rores, nfL, L, eq, mod, d;
  long i, j, l, v = varn(nf[1]);

  eq = rnfequation2(nf,pol);
  L = (GEN)eq[1];
  mod = dummycopy(L); setvarn(mod, v);
  nfL = _initalg(mod, nf_PARTIALFACT, DEFAULTPREC);
  ro = nfroots(nfL, liftpol(pol, (GEN)eq[2], v));
  l = lg(ro)-1;
  if (l != degpol(pol)) return 0;
  if (isprime(stoi(l))) return 1;
  ro = Q_remove_denom(ro, &d);
  if (!d) rores = ro;
  else
  {
    rores = cgetg(l+1, t_VEC);
    for (i=1; i<=l; i++)
      rores[i] = (long)rescale_pol((GEN)ro[i], d);
  }
  /* assume roots are sorted by increasing degree */
  for (i=1; i<l; i++)
    for (j=1; j<i; j++)
    {
      GEN a = RX_RXQ_compo((GEN)rores[j], (GEN)ro[i], mod);
      GEN b = RX_RXQ_compo((GEN)rores[i], (GEN)ro[j], mod);
      if (d) a = gmul(a, gpowgs(d, degpol(ro[i]) - degpol(ro[j])));
      if (!gegal(a, b)) return 0;
    }
  return 1;
}

/* Given bnf and polrel defining an abelian relative extension, compute the
 * corresponding conductor and congruence subgroup. Return
 * [[ideal,arch],[hm,cyc,gen],group] where [ideal,arch] is the conductor, and
 * [hm,cyc,gen] is the corresponding ray class group.
 * If flag != 0, check that the extension is abelian */
GEN
rnfconductor(GEN bnf, GEN polrel, long flag)
{
  long R1, i;
  pari_sp av = avma;
  GEN nf, module, arch, bnr, group, p1, pol2;

  bnf = checkbnf(bnf); nf = (GEN)bnf[7];
  if (typ(polrel) != t_POL) err(typeer,"rnfconductor");
  p1 = unifpol(nf, polrel, t_COL);
  pol2 = rescale_pol(polrel, Q_denom(p1));
  if (flag && !rnf_is_abelian(nf, pol2)) { avma = av; return gzero; }

  pol2 = fix_relative_pol(nf, pol2, 1);
  module = cgetg(3,t_VEC);
  module[1] = rnfdiscf(nf,pol2)[1];
  R1 = nf_get_r1(nf); arch = cgetg(R1+1,t_VEC);
  module[2] = (long)arch; for (i=1; i<=R1; i++) arch[i]=un;
  bnr   = buchrayall(bnf,module,nf_INIT | nf_GEN);
  group = rnfnormgroup(bnr,pol2);
  if (!group) { avma = av; return gzero; }
  return gerepileupto(av, conductor(bnr,group,1));
}

/* Given a number field bnf=bnr[1], a ray class group structure bnr, and a
 * subgroup H (HNF form) of the ray class group, compute [n, r1, dk]
 * associated to H (cf. discrayall). If flcond = 1, abort (return gzero) if
 * module is not the conductor If flrel = 0, compute only N(dk) instead of
 * the ideal dk proper */
static GEN
discrayrelall(GEN bnr, GEN H0, long flag)
{
  pari_sp av = avma;
  long j, k, l, nz, flrel = flag & nf_REL, flcond = flag & nf_COND;
  GEN bnf, nf, bid, ideal, archp, y, clhray, clhss, P, e, dlk, H;
  zlog_S S;

  checkbnr(bnr);
  bnf = (GEN)bnr[1];
  bid = (GEN)bnr[2]; init_zlog_bid(&S, bid);
  clhray = gmael(bnr,5,1);
  nf = (GEN)bnf[7];
  ideal= gmael(bid,1,1);
  H0 = H = check_subgroup(bnr, H0, &clhray, 0, "bnrdiscray");
  archp = S.archp;
  P     = S.P;
  e     = S.e; l = lg(e);
  dlk = flrel? idealpow(nf,ideal,clhray)
             : powgi(dethnf_i(ideal),clhray);
  for (k = 1; k < l; k++)
  {
    GEN pr = (GEN)P[k], sum = gzero;
    long ep = itos((GEN)e[k]);
    for (j = ep; j > 0; j--)
    {
      GEN z = bnr_log_gen_pr(bnr, &S, nf, j, k);
      H = hnf(concatsp(H, z));
      clhss = dethnf_i(H);
      if (flcond && j==ep && egalii(clhss,clhray)) { avma = av; return gzero; }
      if (is_pm1(clhss)) { sum = addis(sum, j); break; }
      sum = addii(sum, clhss);
    }
    dlk = flrel? idealdivpowprime(nf, dlk, pr, sum)
               : diviiexact(dlk, powgi(idealnorm(nf,pr),sum));
  }
  l = lg(archp); nz = nf_get_r1(nf) - (l-1);
  for (k = 1; k < l; k++)
  {
    if (!contains(H0, bnr_log_gen_arch(bnr, &S, k))) continue;
    if (flcond) { avma = av; return gzero; }
    nz++;
  }
  y = cgetg(4,t_VEC);
  y[1] = (long)clhray;
  y[2] = lstoi(nz);
  y[3] = (long)dlk; return gerepilecopy(av, y);
}

static GEN
discrayabsall(GEN bnr, GEN subgroup,long flag)
{
  pari_sp av = avma;
  long clhray, n, R1;
  GEN z, p1, D, dk, nf, dkabs;

  D = discrayrelall(bnr, subgroup, flag);
  if ((flag & nf_REL) || D == gzero) return D;

  nf = checknf(bnr);
  dkabs = absi((GEN)nf[3]);
  clhray = itos((GEN)D[1]); p1 = gpowgs(dkabs, clhray);
  n = clhray * degpol(nf[1]);
  R1= clhray * itos((GEN)D[2]);
  dk = (GEN)D[3];
  if (((n-R1)&3) == 2) dk = negi(dk); /* (2r2) mod 4 = 2 : r2(relext) is odd */
  z = cgetg(4,t_VEC);
  z[1] = lstoi(n);
  z[2] = lstoi(R1);
  z[3] = lmulii(dk,p1); return gerepileupto(av, z);
}

GEN
bnrdisc0(GEN arg0, GEN arg1, GEN arg2, long flag)
{
  GEN H, bnr = args_to_bnr(arg0,arg1,arg2,&H, 0);
  return discrayabsall(bnr,H,flag);
}

GEN
discrayrel(GEN bnr, GEN H)
{
  return discrayrelall(bnr,H,nf_REL);
}

GEN
discrayrelcond(GEN bnr, GEN H)
{
  return discrayrelall(bnr,H,nf_REL | nf_COND);
}

GEN
discrayabs(GEN bnr, GEN H)
{
  return discrayabsall(bnr,H,0);
}

GEN
discrayabscond(GEN bnr, GEN H)
{
  return discrayabsall(bnr,H,nf_COND);
}

/* chi character of abelian G: chi[i] = chi(z_i), where G = \oplus Z/cyc[i] z_i.
 * Return Ker chi [ NULL = trivial subgroup of G ] */
static GEN
KerChar(GEN chi, GEN cyc)
{
  long i, l = lg(cyc);
  GEN m, U, d1;

  if (lg(chi) != l) err(talker,"incorrect character length in KerChar");
  if (l == 1) return NULL; /* trivial subgroup */
  d1 = (GEN)cyc[1]; m = cgetg(l+1,t_MAT);
  for (i=1; i<l; i++)
  {
    if (typ(chi[i]) != t_INT) err(typeer,"conductorofchar");
    m[i] = (long)_col(mulii((GEN)chi[i], diviiexact(d1, (GEN)cyc[i])));
  }
  m[i] = (long)_col(d1);
  U = (GEN)hnfall(m)[2];
  for (i = 1; i < l; i++) setlg(U[i], l);
  setlg(U,l); return U;
}

/* Given a number field bnf=bnr[1], a ray class group structure bnr and a
 * vector chi representing a character on the generators bnr[2][3], compute
 * the conductor of chi. */
GEN
bnrconductorofchar(GEN bnr, GEN chi)
{
  pari_sp av = avma; checkbnr(bnr);
  return gerepileupto(av, conductor(bnr, KerChar(chi, gmael(bnr,5,2)), 0));
}

/* Given lists of [zidealstarinit, unit ideallogs], return lists of ray class
 * numbers */
GEN
rayclassnolist(GEN bnf,GEN lists)
{
  pari_sp av = avma;
  long i,j,lx,ly;
  GEN B,U,L,h,b,u,l,m;

  bnf = checkbnf(bnf); h = gmael3(bnf,8,1,1);
  B = (GEN)lists[1];
  U = (GEN)lists[2];
  if (typ(lists)!=t_VEC || lg(lists)!=3 || typ(B)!=t_VEC || typ(U)!=t_VEC)
    err(typeer,"rayclassnolist");
  lx = lg(B); L = cgetg(lx,t_VEC);
  for (i = 1; i < lx; i++)
  {
    b = (GEN)B[i]; /* bid's */
    u = (GEN)U[i]; /* units logs wrt bid */
    ly = lg(b); l = cgetg(ly,t_VEC); L[i] = (long)l;
    for (j=1; j<ly; j++)
    {
      GEN bid = (GEN)b[j], cyc = gmael(bid,2,2);
      m = concatsp((GEN)u[j], diagonal(cyc));
      l[j] = lmulii(h, dethnf_i(hnf(m)));
    }
  }
  return gerepilecopy(av, L);
}

static long
rayclassnolists(GEN sous, GEN sousclass, GEN fac)
{
  long i;
  for (i=1; i<lg(sous); i++)
    if (gegal(gmael(sous,i,3),fac)) return itos((GEN)sousclass[i]);
  err(bugparier,"discrayabslist");
  return 0; /* not reached */
}

static GEN
rayclassnolistessimp(GEN sous, GEN fac)
{
  long i;
  for (i=1; i<lg(sous); i++)
    if (gegal(gmael(sous,i,1),fac)) return gmael(sous,i,2);
  err(bugparier,"discrayabslistlong");
  return NULL; /* not reached */
}

static GEN
factormul(GEN fa1,GEN fa2)
{
  GEN p,pnew,e,enew,v,P, y = cgetg(3,t_MAT);
  long i,c,lx;

  p = concatsp((GEN)fa1[1],(GEN)fa2[1]); y[1] = (long)p;
  e = concatsp((GEN)fa1[2],(GEN)fa2[2]); y[2] = (long)e;
  v = sindexsort(p); lx = lg(p);
  pnew = cgetg(lx,t_COL); for (i=1; i<lx; i++) pnew[i] = p[v[i]];
  enew = cgetg(lx,t_COL); for (i=1; i<lx; i++) enew[i] = e[v[i]];
  P = gzero; c = 0;
  for (i=1; i<lx; i++)
  {
    if (gegal((GEN)pnew[i],P))
      e[c] = laddii((GEN)e[c],(GEN)enew[i]);
    else
    {
      c++; P = (GEN)pnew[i];
      p[c] = (long)P;
      e[c] = enew[i];
    }
  }
  setlg(p, c+1);
  setlg(e, c+1); return y;
}

static GEN
factordivexact(GEN fa1,GEN fa2)
{
  long i,j,k,c,lx1,lx2;
  GEN Lpr,Lex,y,Lpr1,Lex1,Lpr2,Lex2,p1;

  Lpr1 = (GEN)fa1[1]; Lex1 = (GEN)fa1[2]; lx1 = lg(Lpr1);
  Lpr2 = (GEN)fa2[1]; Lex2 = (GEN)fa2[2]; lx2 = lg(Lpr1);
  y = cgetg(3,t_MAT);
  Lpr = cgetg(lx1,t_COL); y[1] = (long)Lpr;
  Lex = cgetg(lx1,t_COL); y[2] = (long)Lex;
  for (c=0,i=1; i<lx1; i++)
  {
    j = isinvector(Lpr2,(GEN)Lpr1[i],lx2-1);
    if (!j) { c++; Lpr[c] = Lpr1[i]; Lex[c] = Lex1[i]; }
    else
    {
      p1 = subii((GEN)Lex1[i], (GEN)Lex2[j]); k = signe(p1);
      if (k<0) err(talker,"factordivexact is not exact!");
      if (k>0) { c++; Lpr[c] = Lpr1[i]; Lex[c] = (long)p1; }
    }
  }
  setlg(Lpr,c+1);
  setlg(Lex,c+1); return y;
}

static GEN
factorpow(GEN fa,long n)
{
  GEN y;
  if (!n) return trivfact();
  y = cgetg(3,t_MAT);
  y[1] = fa[1];
  y[2] = lmulsg(n, (GEN)fa[2]); return y;
}

/* Etant donne la liste des zidealstarinit et des matrices d'unites
 * correspondantes, sort la liste des discrayabs. On ne garde pas les modules
 * qui ne sont pas des conducteurs
 */
GEN
discrayabslist(GEN bnf, GEN lists)
{
  pari_sp av = avma;
  long ii,jj,i,j,k,clhss,ep,clhray,lx,ly,r1,degk,nz;
  long n,R1,lP;
  GEN hlist,blist,dlist,nf,dkabs,b,h,d;
  GEN z,ideal,arch,fa,P,ex,idealrel,mod,pr,dlk,arch2,p3,fac;

  bnf = checkbnf(bnf);
  hlist = rayclassnolist(bnf,lists);
  blist = (GEN)lists[1];
  lx = lg(hlist); dlist = cgetg(lx,t_VEC);
  nf = (GEN)bnf[7]; r1 = nf_get_r1(nf);
  degk = degpol(nf[1]); dkabs = absi((GEN)nf[3]);
  nz = 0; dlk = NULL; /* gcc -Wall */
  for (ii=1; ii<lx; ii++)
  {
    b = (GEN)blist[ii]; /* zidealstarinits */
    h = (GEN)hlist[ii]; /* class numbers */
    ly = lg(b); d = cgetg(ly,t_VEC); dlist[ii] = (long)d; /* discriminants */
    for (jj=1; jj<ly; jj++)
    {
      GEN fac1,fac2, bid = (GEN)b[jj];
      clhray = itos((GEN)h[jj]);
      ideal= gmael(bid,1,1);
      arch = gmael(bid,1,2);
      fa = (GEN)bid[3]; fac = dummycopy(fa);
      P = (GEN)fa[1]; fac1 = (GEN)fac[1];
      ex= (GEN)fa[2]; fac2 = (GEN)fac[2];
      lP = lg(P)-1; idealrel = trivfact();
      for (k=1; k<=lP; k++)
      {
        GEN normp;
        long S = 0, normps, normi;
	pr = (GEN)P[k]; ep = itos((GEN)ex[k]);
	normi = ii; normps = itos(idealnorm(nf,pr));
	for (j=1; j<=ep; j++)
	{
          GEN fad, fad1, fad2;
          if (j < ep) { fac2[k] = lstoi(ep-j); fad = fac; }
          else
          {
            fad = cgetg(3,t_MAT);
            fad1 = cgetg(lP,t_COL); fad[1] = (long)fad1;
            fad2 = cgetg(lP,t_COL); fad[2] = (long)fad2;
            for (i=1; i< k; i++) { fad1[i] = fac1[i];  fad2[i] = fac2[i]; }
            for (   ; i<lP; i++) { fad1[i] = fac1[i+1];fad2[i] = fac2[i+1]; }
          }
          normi /= normps;
          clhss = rayclassnolists((GEN)blist[normi],(GEN)hlist[normi], fad);
          if (j==1 && clhss==clhray)
	  {
	    clhray = 0; fac2[k] = ex[k]; goto LLDISCRAY;
	  }
          if (clhss == 1) { S += ep-j+1; break; }
          S += clhss;
	}
	fac2[k] = ex[k];
	normp = to_famat_all((GEN)pr[1], (GEN)pr[4]);
	idealrel = factormul(idealrel, factorpow(normp,S));
      }
      dlk = factordivexact(factorpow(factor(stoi(ii)),clhray), idealrel);
      mod = cgetg(3,t_VEC);
      mod[1] = (long)ideal; arch2 = dummycopy(arch);
      mod[2] = (long)arch2; nz = 0;
      for (k=1; k<=r1; k++)
      {
	if (signe(arch[k]))
	{
	  arch2[k] = zero;
	  clhss = itos(rayclassno(bnf,mod));
	  arch2[k] = un;
	  if (clhss == clhray) { clhray = 0; break; }
	}
	else nz++;
      }
LLDISCRAY:
      if (!clhray) { d[jj] = lgetg(1,t_VEC); continue; }

      p3 = factorpow(factor(dkabs),clhray);
      n = clhray * degk;
      R1= clhray * nz;
      if (((n-R1)&3) == 2) /* r2 odd, set dlk = -dlk */
        dlk = factormul(to_famat_all(stoi(-1),gun), dlk);
      z = cgetg(4,t_VEC);
      z[1] = lstoi(n);
      z[2] = lstoi(R1);
      z[3] = (long)factormul(dlk,p3);
      d[jj] = (long)z;
    }
  }
  return gerepilecopy(av, dlist);
}

#define SHLGVINT 15
#define LGVINT (1L << SHLGVINT)

/* Attention: bound est le nombre de vraies composantes voulues. */
static GEN
bigcgetvec(long bound)
{
  long nbcext,nbfinal,i;
  GEN vext;

  nbcext = ((bound-1)>>SHLGVINT)+1;
  nbfinal = bound-((nbcext-1)<<SHLGVINT);
  vext = cgetg(nbcext+1,t_VEC);
  for (i=1; i<nbcext; i++) vext[i] = lgetg(LGVINT+1,t_VEC);
  vext[nbcext] = lgetg(nbfinal+1,t_VEC); return vext;
}

static GEN
getcompobig(GEN vext,long i)
{
  long cext;
  if (i<=LGVINT) return gmael(vext,1,i);
  cext = ((i-1)>>SHLGVINT)+1;
  return gmael(vext, cext, i - ((cext-1)<<SHLGVINT));
}

static void
putcompobig(GEN vext,long i,GEN x)
{
  long cext;
  if (i<=LGVINT) { mael(vext, 1, i) = (long)x; return; }
  cext = ((i-1)>>SHLGVINT) + 1;
  mael(vext, cext, i - ((cext-1)<<SHLGVINT)) = (long)x;
}

static GEN
zsimp(GEN bid, GEN matunit)
{
  GEN y = cgetg(5,t_VEC);
  y[1] = bid[3];
  y[2] = mael(bid,2,2);
  y[3] = bid[5];
  y[4] = (long)matunit; return y;
}

static GEN
zsimpjoin(GEN bidsimp, GEN bidp, GEN dummyfa, GEN matunit)
{
  long i, l1, l2, nbgen, c;
  pari_sp av = avma;
  GEN U,U1,U2,cyc1,cyc2,cyc,u1u2,met, y = cgetg(5,t_VEC);

  y[1] = (long)vconcat((GEN)bidsimp[1],dummyfa);
  U1 = (GEN)bidsimp[3]; cyc1 = (GEN)bidsimp[2]; l1 = lg(cyc1);
  U2 = (GEN)bidp[5];    cyc2 = gmael(bidp,2,2); l2 = lg(cyc2);
  nbgen = l1+l2-2;
  if (nbgen)
  {
    cyc = diagonal(concatsp(cyc1,cyc2));
    u1u2 = matsnf0(cyc, 1 | 4); /* all && clean */
    U = (GEN)u1u2[1];
    met=(GEN)u1u2[3];
    y[3] = (long)concatsp(
      l1==1   ? zeromat(nbgen, lg(U1)-1): gmul(vecextract_i(U, 1,   l1-1), U1) ,
      l1>nbgen? zeromat(nbgen, lg(U2)-1): gmul(vecextract_i(U, l1, nbgen), U2)
    );
  }
  else
  {
    c = lg(U1)+lg(U2)-1; U = cgetg(c,t_MAT);
    for (i=1; i<c; i++) U[i]=lgetg(1,t_COL);
    met = cgetg(1,t_MAT);
    y[3] = (long)U;
  }
  c = lg(met); cyc = cgetg(c,t_VEC);
  for (i=1; i<c; i++) cyc[i] = coeff(met,i,i);
  y[2] = (long)cyc;
  y[4] = (long)vconcat((GEN)bidsimp[4],matunit);
  return gerepilecopy(av, y);
}

static GEN
rayclassnointern(GEN blist, GEN h)
{
  long lx,j;
  GEN bid,qm,L,cyc,m,z;

  lx = lg(blist); L = cgetg(lx,t_VEC);
  for (j=1; j<lx; j++)
  {
    bid = (GEN)blist[j];
    qm = gmul((GEN)bid[3],(GEN)bid[4]);
    cyc = (GEN)bid[2];
    m = concatsp(qm, diagonal(cyc));
    z = cgetg(3,t_VEC); L[j] = (long)z;
    z[1] = bid[1];
    z[2] = lmulii(h, dethnf_i(hnf(m)));
  }
  return L;
}

static GEN
rayclassnointernarch(GEN blist, GEN h, GEN matU)
{
  long lx,nc,k,kk,j,r1,jj,nba,nbarch;
  GEN _2,bid,qm,Lray,cyc,m,z,z2,mm,rowsel;

  if (!matU) return rayclassnointern(blist,h);
  lx = lg(blist); if (lx == 1) return blist;

  r1 = lg(matU[1])-1; _2 = gscalmat(gdeux,r1);
  Lray = cgetg(lx,t_VEC); nbarch = 1<<r1;
  for (j=1; j<lx; j++)
  {
    bid = (GEN)blist[j];
    qm = gmul((GEN)bid[3],(GEN)bid[4]);
    cyc = (GEN)bid[2]; nc = lg(cyc)-1;
    /* [ qm   cyc 0 ]
     * [ matU  0  2 ] */
    m = concatsp3(vconcat(qm, matU),
             vconcat(diagonal(cyc), zeromat(r1,nc)),
             vconcat(zeromat(nc,r1), _2));
    m = hnf(m); mm = dummycopy(m);
    z2 = cgetg(nbarch+1,t_VEC);
    rowsel = cgetg(nc+r1+1,t_VECSMALL);
    for (k = 0; k < nbarch; k++)
    {
      nba = nc+1;
      for (kk=k,jj=1; jj<=r1; jj++,kk>>=1)
	if (kk&1) rowsel[nba++] = nc + jj;
      setlg(rowsel, nba);
      rowselect_p(m, mm, rowsel, nc+1);
      z2[k+1] = lmulii(h, dethnf_i(hnf(mm)));
    }
    z = cgetg(3,t_VEC); Lray[j] = (long)z;
    z[1] = bid[1];
    z[2] = (long)z2;
  }
  return Lray;
}

GEN
decodemodule(GEN nf, GEN fa)
{
  long n, k, j, fauxpr;
  pari_sp av=avma;
  GEN g,e,id,pr;

  nf = checknf(nf);
  if (typ(fa)!=t_MAT || lg(fa)!=3)
    err(talker,"incorrect factorisation in decodemodule");
  n = degpol(nf[1]); id = idmat(n);
  g = (GEN)fa[1];
  e = (GEN)fa[2];
  for (k=1; k<lg(g); k++)
  {
    fauxpr = itos((GEN)g[k]);
    j = (fauxpr%n)+1; fauxpr /= n*n;
    pr = (GEN)primedec(nf,stoi(fauxpr))[j];
    id = idealmulpowprime(nf,id, pr,(GEN)e[k]);
  }
  return gerepileupto(av,id);
}

/* Do all from scratch, bound < 2^30. For the time being, no subgroups.
 * Ouput: vector vext whose components vint have exactly 2^LGVINT entries
 * but for the last one which is allowed to be shorter. vext[i][j]
 * (where j<=2^LGVINT) is understood as component number I = (i-1)*2^LGVINT+j 
 * in a unique huge vector V.  Such a component V[I] is a vector indexed by
 * all ideals of norm I. Given such an ideal m_0, the component is as follows:
 *
 * + if arch = NULL, run through all possible archimedean parts, the archs
 * are ordered using inverse lexicographic order, [0,..,0], [1,0,..,0],
 * [0,1,..,0],... Component is [m_0,V] where V is a vector with
 * 2^r1 entries, giving for each arch the triple [N,R1,D], with N, R1, D 
 * as in discrayabs [D is in factored form]
 *
 * + otherwise [m_0,arch,N,R1,D]
 *
 * If ramip != 0 and -1, keep only modules which are squarefree outside ramip
 * If ramip < 0, archsquare. (????)
 */
static GEN
discrayabslistarchintern(GEN bnf, GEN arch, long bound, long ramip)
{
  byteptr ptdif=diffptr;
  long degk,i,j,k,lfa,lp1,sqbou,cex, allarch;
  long ffs,fs,resp,flbou,nba, k2,karch,kka,nbarch,jjj,jj,square;
  long ii2,ii,ly,clhray,lP,ep,S,clhss,normps,normi,nz,r1,R1,n,c;
  ulong q, p2s;
  pari_sp av0 = avma, av, av1, lim;
  GEN nf,p,z,p1,p2,p3,fa,pr,normp,ideal,bidp,z2,matarchunit;
  GEN embunit,sous,clh,sousray,raylist;
  GEN clhrayall,discall,faall,Id,idealrel,idealrelinit;
  GEN sousdisc,mod,P,ex,fac,fadkabs,pz;
  GEN arch2,dlk,disclist,p4,faussefa,fauxpr,gprime, U, sgnU;

  if (bound <= 0) err(talker,"non-positive bound in discrayabslist");
  clhray = nz = 0; /* gcc -Wall */
  mod = Id = dlk = ideal = clhrayall = discall = faall = NULL;

  /* ce qui suit recopie d'assez pres ideallistzstarall */
  if (DEBUGLEVEL>2) (void)timer2();
  bnf = checkbnf(bnf); flbou=0;
  nf = (GEN)bnf[7]; r1 = nf_get_r1(nf);
  degk = degpol(nf[1]);
  fadkabs = factor(absi((GEN)nf[3]));
  clh = gmael3(bnf,8,1,1);
  U = init_units(bnf);
  sgnU = zsignunits(bnf, NULL, 1);

  if (ramip >= 0) square = 0;
  else
  {
    square = 1; ramip = -ramip;
    if (ramip==1) ramip=0;
  }
  nba = 0; allarch = (arch==NULL);
  if (allarch)
    { arch=cgetg(r1+1,t_VEC); for (i=1; i<=r1; i++) arch[i]=un; nba=r1; }
  else if (gcmp0(arch))
    { arch=cgetg(r1+1,t_VEC); for (i=1; i<=r1; i++) arch[i]=zero; }
  else
  {
    if (lg(arch)!=r1+1)
      err(talker,"incorrect archimedean argument in discrayabslistarchintern");
    for (i=1; i<=r1; i++) if (signe(arch[i])) nba++;
    if (nba) mod = cgetg(3,t_VEC);
  }
  p1 = cgetg(3,t_VEC);
  p1[1] = (long)idmat(degk);
  p1[2] = (long)arch; bidp = zidealstarinitall(nf,p1,0);
  if (allarch)
  {
    matarchunit = logunitmatrix(nf, U, sgnU, bidp);
    if (r1>15) err(talker,"r1>15 in discrayabslistarchintern");
  }
  else
    matarchunit = (GEN)NULL;

  p = cgeti(3); p[1] = evalsigne(1)|evallgef(3);
  sqbou = (long)sqrt((double)bound) + 1;
  av = avma; lim = stack_lim(av,1);
  z = bigcgetvec(bound); for (i=2;i<=bound;i++) putcompobig(z,i,cgetg(1,t_VEC));
  if (allarch) bidp = zidealstarinitall(nf,idmat(degk),0);
  embunit = logunitmatrix(nf, U, sgnU, bidp);
  putcompobig(z,1, _vec(zsimp(bidp,embunit))); 
  if (DEBUGLEVEL>1) fprintferr("Starting zidealstarunits computations\n");
  maxprime_check((ulong)bound);
  for (p[2]=0; p[2]<=bound; )
  {
    NEXT_PRIME_VIADIFF(p[2], ptdif);
    if (!flbou && p[2]>sqbou)
    {
      if (DEBUGLEVEL>1) fprintferr("\nStarting rayclassno computations\n");
      flbou = 1;
      z = gerepilecopy(av,z);
      av1 = avma; raylist = bigcgetvec(bound);
      for (i=1; i<=bound; i++)
      {
	sous = getcompobig(z,i);
        sousray = rayclassnointernarch(sous,clh,matarchunit);
	putcompobig(raylist,i,sousray);
      }
      raylist = gerepilecopy(av1,raylist);
      z2 = bigcgetvec(sqbou);
      for (i=1; i<=sqbou; i++) putcompobig(z2,i, gcopy(getcompobig(z,i)));
      z = z2;
    }
    fa = primedec(nf,p); lfa = lg(fa)-1;
    for (j=1; j<=lfa; j++)
    {
      pr = (GEN)fa[j]; p1 = powgi(p,(GEN)pr[4]);
      if (DEBUGLEVEL>1) { fprintferr("%ld ",p[2]); flusherr(); }
      if (is_bigint(p1) || (q = (ulong)itos(p1)) > (ulong)bound) continue;

      fauxpr = stoi((p[2]*degk + itos((GEN)pr[4])-1)*degk + j-1);
      p2s = q; ideal = pr; cex = 0;
      while (q <= (ulong)bound)
      {
        cex++; bidp = zidealstarinitall(nf,ideal,0);
        faussefa = to_famat_all(fauxpr, stoi(cex));
        embunit = logunitmatrix(nf, U, sgnU, bidp);
        for (i=q; i<=bound; i+=q)
        {
          p1 = getcompobig(z,i/q); lp1 = lg(p1);
          if (lp1 == 1) continue;

          p2 = cgetg(lp1,t_VEC); c=0;
          for (k=1; k<lp1; k++)
          {
            p3=(GEN)p1[k];
            if (q == (ulong)i ||
                ((p4=gmael(p3,1,1)) && !isinvector(p4,fauxpr,lg(p4)-1)))
              p2[++c] = (long)zsimpjoin(p3,bidp,faussefa,embunit);
          }

          setlg(p2, c+1);
          if (p[2] <= sqbou)
          {
            pz = getcompobig(z,i);
            if (lg(pz) > 1) p2 = concatsp(pz,p2);
            putcompobig(z,i,p2);
          }
          else
          {
            p2 = rayclassnointernarch(p2,clh,matarchunit);
            pz = getcompobig(raylist,i);
            if (lg(pz) > 1) p2 = concatsp(pz,p2);
            putcompobig(raylist,i,p2);
          }
        }
        if (ramip && ramip % p[2]) break;
        pz = muluu(q, p2s);
        if (is_bigint(pz) || (q = (ulong)pz[2]) > (ulong)bound) break;

        ideal = idealmul(nf,ideal,pr);
      }
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"[1]: discrayabslistarch");
      if (!flbou)
      {
	if (DEBUGLEVEL>2)
          fprintferr("avma = %ld, t(z) = %ld ",avma-bot,taille2(z));
        z = gerepilecopy(av, z);
      }
      else
      {
	if (DEBUGLEVEL>2)
	  fprintferr("avma = %ld, t(r) = %ld ",avma-bot,taille2(raylist));
	gerepileall(av, 2, &z, &raylist);
      }
      if (DEBUGLEVEL>2) { fprintferr("avma = %ld ",avma-bot); flusherr(); }
    }
  }
  if (!flbou)
  {
    if (DEBUGLEVEL>1) fprintferr("\nStarting rayclassno computations\n");
    z = gerepilecopy(av, z);
    av1 = avma; raylist = bigcgetvec(bound);
    for (i=1; i<=bound; i++)
    {
      sous = getcompobig(z,i);
      sousray = rayclassnointernarch(sous,clh,matarchunit);
      putcompobig(raylist,i,sousray);
    }
  }
  if (DEBUGLEVEL>2)
    fprintferr("avma = %ld, t(r) = %ld ",avma-bot,taille2(raylist));
  raylist = gerepilecopy(av, raylist);
  if (DEBUGLEVEL>2)
    { fprintferr("avma = %ld ",avma-bot); msgtimer("zidealstarlist"); }
  /* following discrayabslist */
  if (DEBUGLEVEL>1)
    { fprintferr("Starting discrayabs computations\n"); flusherr(); }

  if (allarch) nbarch = 1<<r1;
  else
  {
    nbarch = 1;
    clhrayall = cgetg(2,t_VEC);
    discall = cgetg(2,t_VEC);
    faall = cgetg(2,t_VEC);
    Id = idmat(degk);
  }
  idealrelinit = trivfact();
  av1 = avma; lim = stack_lim(av1,1);
  if (square) bound = sqbou-1;
  disclist = bigcgetvec(bound);
  for (ii=1; ii<=bound; ii++) putcompobig(disclist,ii,cgetg(1,t_VEC));
  for (ii2=1; ii2<=bound; ii2++)
  {
    ii = square? ii2*ii2: ii2;
    if (DEBUGLEVEL>1 && ii%100==0) { fprintferr("%ld ",ii); flusherr(); }
    sous = getcompobig(raylist,ii); ly = lg(sous); sousdisc = cgetg(ly,t_VEC);
    putcompobig(disclist, square? ii2: ii,sousdisc);
    for (jj=1; jj<ly; jj++)
    {
      GEN fac1, fac2, bidsimp = (GEN)sous[jj];
      fa = (GEN)bidsimp[1]; fac = dummycopy(fa);
      P = (GEN)fa[1]; fac1 = (GEN)fac[1];
      ex= (GEN)fa[2]; fac2 = (GEN)fac[2];
      lP = lg(P)-1;

      if (allarch)
      {
        clhrayall = (GEN)bidsimp[2];
        discall = cgetg(nbarch+1,t_VEC);
      }
      else
        clhray = itos((GEN)bidsimp[2]);
      for (karch=0; karch<nbarch; karch++)
      {
        if (!allarch) ideal = Id;
        else
        {
          nba=0;
          for (kka=karch,jjj=1; jjj<=r1; jjj++,kka>>=1)
            if (kka & 1) nba++;
          clhray = itos((GEN)clhrayall[karch+1]);
          for (k2=1,k=1; k<=r1; k++,k2<<=1)
          {
            if (karch&k2 && clhray==itos((GEN)clhrayall[karch-k2+1]))
              { clhray=0; goto LDISCRAY; }
          }
        }
        idealrel = idealrelinit;
        for (k=1; k<=lP; k++)
        {
          fauxpr = (GEN)P[k]; ep = itos((GEN)ex[k]); ffs = itos(fauxpr);
          /* Hack for NeXTgcc 2.5.8 -- splitting "resp=fs%degk+1" */
          fs = ffs/degk; resp = fs%degk; resp++;
          gprime = stoi((long)(fs/degk));
          if (!allarch && nba)
          {
            p1 = (GEN)primedec(nf,gprime)[ffs%degk+1];
            ideal = idealmulpowprime(nf,ideal,p1,(GEN)ex[k]);
          }
          S=0; clhss=0;
          normi = ii; normps= itos(gpowgs(gprime,resp));
          for (j=1; j<=ep; j++)
          {
            GEN fad, fad1, fad2;
            if (clhss==1) S++;
            else
            {
              if (j < ep) { fac2[k] = lstoi(ep-j); fad = fac; }
              else
              {
                fad = cgetg(3,t_MAT);
                fad1 = cgetg(lP,t_COL); fad[1] = (long)fad1;
                fad2 = cgetg(lP,t_COL); fad[2] = (long)fad2;
                for (i=1; i<k; i++) { fad1[i]=fac1[i];   fad2[i]=fac2[i]; }
                for (   ; i<lP; i++){ fad1[i]=fac1[i+1]; fad2[i]=fac2[i+1]; }
              }
              normi /= normps;
	      dlk = rayclassnolistessimp(getcompobig(raylist,normi),fad);
              if (allarch) dlk = (GEN)dlk[karch+1];
	      clhss = itos(dlk);
              if (j==1 && clhss==clhray)
	      {
		clhray=0; fac2[k] = ex[k]; goto LDISCRAY;
	      }
              S += clhss;
            }
          }
          fac2[k] = ex[k];
          normp = to_famat_all(gprime, stoi(resp));
          idealrel = factormul(idealrel,factorpow(normp,S));
        }
        dlk = factordivexact(factorpow(factor(stoi(ii)),clhray),idealrel);
        if (!allarch && nba)
        {
          mod[1] = (long)ideal; arch2 = dummycopy(arch);
          mod[2] = (long)arch2; nz = 0;
          for (k=1; k<=r1; k++)
          {
            if (signe(arch[k]))
            {
              arch2[k] = zero;
              clhss = itos(rayclassno(bnf,mod));
              arch2[k] = un;
              if (clhss==clhray) { clhray=0; goto LDISCRAY; }
            }
            else nz++;
          }
        }
        else nz = r1-nba;
LDISCRAY:
        p1=cgetg(4,t_VEC); discall[karch+1]=(long)p1;
	if (!clhray) p1[1]=p1[2]=p1[3]=zero;
	else
	{
	  p3 = factorpow(fadkabs,clhray);
          n = clhray * degk;
          R1= clhray * nz;
	  if (((n-R1)&3)==2)
	    dlk=factormul(to_famat_all(stoi(-1),gun), dlk);
	  p1[1] = lstoi(n);
          p1[2] = lstoi(R1);
          p1[3] = (long)factormul(dlk,p3);
	}
      }
      if (allarch)
        { p1 = cgetg(3,t_VEC); p1[1]=(long)fa; p1[2]=(long)discall; }
      else
        { faall[1]=(long)fa; p1 = concatsp(faall, p1); }
      sousdisc[jj]=(long)p1;
      if (low_stack(lim, stack_lim(av1,1)))
      {
        if(DEBUGMEM>1) err(warnmem,"[2]: discrayabslistarch");
        if (DEBUGLEVEL>2)
          fprintferr("avma = %ld, t(d) = %ld ",avma-bot,taille2(disclist));
        disclist = gerepilecopy(av1, disclist);
        if (DEBUGLEVEL>2) { fprintferr("avma = %ld ",avma-bot); flusherr(); }
      }
    }
  }
  if (DEBUGLEVEL>2) msgtimer("discrayabs");
  return gerepilecopy(av0, disclist);
}

GEN
discrayabslistarch(GEN bnf, GEN arch, long bound)
{ return discrayabslistarchintern(bnf,arch,bound, 0); }

GEN
discrayabslistlong(GEN bnf, long bound)
{ return discrayabslistarchintern(bnf,gzero,bound, 0); }

GEN
discrayabslistarchsquare(GEN bnf, GEN arch, long bound)
{ return discrayabslistarchintern(bnf,arch,bound, -1); }

/* Let bnr1, bnr2 be such that mod(bnr2) | mod(bnr1), compute the
   matrix of the surjective map Cl(bnr1) ->> Cl(bnr2) */
static GEN
subgroupcond(GEN bnr, GEN indexbound)
{
  pari_sp av = avma;
  long i,j,lgi,lp;
  GEN li,p1,lidet,perm,nf,bid,ideal,arch,arch2,primelist,listKer;
  GEN mod = cgetg(3, t_VEC);

  checkbnrgen(bnr); bid=(GEN)bnr[2];
  ideal=gmael(bid,1,1);
  arch =gmael(bid,1,2); nf=gmael(bnr,1,7);
  primelist=gmael(bid,3,1); lp=lg(primelist)-1;
  mod[2] = (long)arch;
  listKer=cgetg(lp+lg(arch),t_VEC);
  for (i=1; i<=lp; )
  {
    mod[1] = (long)idealdivpowprime(nf,ideal,(GEN)primelist[i],gun);
    listKer[i++] = (long)bnrGetKer(bnr,mod);
  }
  mod[1] = (long)ideal; arch2 = dummycopy(arch);
  mod[2] = (long)arch2;
  for (j=1; j<lg(arch); j++)
    if (signe((GEN)arch[j]))
    {
      arch2[j] = zero; 
      listKer[i++] = (long)bnrGetKer(bnr,mod);
      arch2[j] = un;
    }
  setlg(listKer,i);

  li = subgroupcondlist(gmael(bnr,5,2),indexbound,listKer);
  lgi = lg(li);
  /* sort by increasing index */
  lidet = cgetg(lgi,t_VEC);
  for (i=1; i<lgi; i++) lidet[i] = (long)dethnf_i((GEN)li[i]);
  perm = sindexsort(lidet); p1 = li; li = cgetg(lgi,t_VEC);
  for (i=1; i<lgi; i++) li[i] = p1[perm[lgi-i]];
  return gerepilecopy(av,li);
}

GEN
subgrouplist0(GEN bnr, GEN indexbound, long all)
{
  if (typ(bnr)!=t_VEC) err(typeer,"subgrouplist");
  if (lg(bnr)!=1 && typ(bnr[1])!=t_INT)
  {
    if (!all) return subgroupcond(bnr,indexbound);
    checkbnr(bnr); bnr = gmael(bnr,5,2);
  }
  return subgrouplist(bnr,indexbound);
}

GEN
bnrdisclist0(GEN bnf, GEN borne, GEN arch, long all)
{
  if (typ(borne)==t_INT)
  {
    if (!arch) arch = gzero;
    if (all==1) { arch = NULL; all = 0; }
    return discrayabslistarchintern(bnf,arch,itos(borne),all);
  }
  return discrayabslist(bnf,borne);
}
