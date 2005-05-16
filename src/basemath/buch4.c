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
/*               S-CLASS GROUP AND NORM SYMBOLS                    */
/*          (Denis Simon, desimon@math.u-bordeaux.fr)              */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"
#include "parinf.h"

static int
psquare(GEN a,GEN p)
{
  long v;
  GEN ap;

  if (!signe(a) || gcmp1(a)) return 1;
  v = Z_pvalrem(a, p, &ap);
  if (v&1) return 0;
  return equaliu(p, 2)? umodiu(ap, 8) == 1
                      : kronecker(ap,p) == 1;
}

static long
lemma6(GEN pol,GEN p,long nu,GEN x)
{
  long lambda, mu;
  pari_sp ltop=avma;
  GEN gx, gpx;

  gx = poleval(pol, x);
  if (psquare(gx,p)) return 1;

  gpx = poleval(derivpol(pol), x);
  lambda = Z_pval(gx, p);
  mu = gcmp0(gpx)? BIGINT: Z_pval(gpx,p);
  avma = ltop;

  if (lambda > (mu<<1)) return 1;
  if (lambda >= (nu<<1) && mu >= nu) return 0;
  return -1;
}

static long
lemma7(GEN pol,long nu,GEN x)
{
  long odd4, lambda, mu, mnl;
  pari_sp ltop = avma;
  GEN gx, gpx, oddgx;

  gx = poleval(pol, x);
  if (psquare(gx,gen_2)) return 1;

  gpx = poleval(derivpol(pol), x);
  lambda = Z_lvalrem(gx, 2, &oddgx);
  mu = gcmp0(gpx)? BIGINT: vali(gpx);
  mnl = mu+nu-lambda;
  odd4 = umodiu(oddgx,4);
  avma=ltop;
  if (lambda > (mu<<1)) return 1;
  if (nu > mu)
  {
    if (mnl==1 && (lambda&1) == 0) return 1;
    if (mnl==2 && (lambda&1) == 0 && odd4==1) return 1;
  }
  else
  {
    if (lambda >= (nu<<1)) return 0;
    if (lambda == ((nu-1)<<1) && odd4==1) return 0;
  }
  return -1;
}

static long
zpsol(GEN pol,GEN p,long nu,GEN pnu,GEN x0)
{
  long i, result;
  pari_sp ltop=avma;
  GEN x,pnup;

  result = equaliu(p,2)? lemma7(pol,nu,x0): lemma6(pol,p,nu,x0);
  if (result== 1) return 1;
  if (result==-1) return 0;
  x = gcopy(x0); pnup = mulii(pnu,p);
  for (i=0; i < itos(p); i++)
  {
    x = addii(x,pnu);
    if (zpsol(pol,p,nu+1,pnup,x)) { avma=ltop; return 1; }
  }
  avma=ltop; return 0;
}

/* vaut 1 si l'equation y^2=Pol(x) a une solution p-adique entiere
 * 0 sinon. Les coefficients sont entiers.
 */
long
zpsoluble(GEN pol,GEN p)
{
  if ((typ(pol)!=t_POL && typ(pol)!=t_INT) || typ(p)!=t_INT )
    err(typeer,"zpsoluble");
  return zpsol(pol,p,0,gen_1,gen_0);
}

/* vaut 1 si l'equation y^2=Pol(x) a une solution p-adique rationnelle
 * (eventuellement infinie), 0 sinon. Les coefficients sont entiers.
 */
long
qpsoluble(GEN pol,GEN p)
{
  if ((typ(pol)!=t_POL && typ(pol)!=t_INT) || typ(p)!=t_INT )
    err(typeer,"qpsoluble");
  if (zpsol(pol,p,0,gen_1,gen_0)) return 1;
  return zpsol(polrecip(pol),p,1,p,gen_0);
}

/* (pr,2) = 1. return 1 if a square in (ZK / pr), 0 otherwise */
static long
psquarenf(GEN nf,GEN a,GEN pr)
{
  pari_sp av = avma;
  long v;
  GEN norm;

  if (gcmp0(a)) return 1;
  v = idealval(nf,a,pr); if (v&1) return 0;
  if (v) a = gdiv(a, gpowgs(basistoalg(nf, (GEN)pr[2]), v));

  norm = gshift(pr_norm(pr), -1);
  a = gmul(a, gmodulsg(1,(GEN)pr[1]));
  a = gaddgs(powgi(a,norm), -1);
  if (gcmp0(a)) { avma = av; return 1; }
  a = lift(lift(a));
  v = idealval(nf,a,pr);
  avma = av; return (v>0);
}

static long
check2(GEN nf, GEN a, GEN zinit)
{
  GEN zlog = zideallog(nf,a,zinit), cyc = gmael(zinit,2,2);
  long i, l = lg(cyc);

  for (i=1; i<l; i++)
  {
    if (mpodd((GEN)cyc[i])) break;
    if (mpodd((GEN)zlog[i])) return 0;
  }
  return 1;
}

/* pr | 2. Return 1 if a square in (ZK / pr), 0 otherwise */
static long
psquare2nf(GEN nf,GEN a,GEN pr,GEN zinit)
{
  long v;
  pari_sp ltop = avma;

  if (gcmp0(a)) return 1;
  v = idealval(nf,a,pr); if (v&1) return 0;
  if (v) a = gdiv(a, gpowgs(basistoalg(nf, (GEN)pr[2]), v));
  /* now (a,pr) = 1 */
  v = check2(nf,a,zinit); avma = ltop; return v;
}

static long
lemma6nf(GEN nf,GEN pol,GEN pr,long nu,GEN x)
{
  long lambda, mu;
  GEN gx, gpx;

  gx = poleval(pol, x);
  if (psquarenf(nf,gx,pr)) return 1;
  lambda = idealval(nf,gx,pr);

  gpx = poleval(derivpol(pol), x);
  mu = gcmp0(gpx)? BIGINT: idealval(nf,gpx,pr);

  if (lambda > mu<<1) return 1;
  if (lambda >= nu<<1  && mu >= nu) return 0;
  return -1;
}

static long
lemma7nf(GEN nf,GEN pol,GEN pr,long nu,GEN x,GEN zinit)
{
  long res, lambda, mu, q;
  GEN gx, gpx, p1;

  gx = poleval(pol, x);
  if (psquare2nf(nf,gx,pr,zinit)) return 1;
  lambda = element_val(nf,gx,pr);

  gpx = poleval(derivpol(pol), x);
  mu = gcmp0(gpx)? BIGINT: idealval(nf,gpx,pr);
  if (lambda > (mu<<1)) return 1;

  if (nu > mu)
  {
    if (lambda&1) return -1;
    q=mu+nu-lambda; res=1;
  }
  else
  {
    if (lambda>=(nu<<1)) return 0;
    if (lambda&1) return -1;
    q=(nu<<1)-lambda; res=0;
  }
  if (q > itos((GEN) pr[3])<<1)  return -1;
  p1 = gpowgs(basistoalg(nf, (GEN)pr[2]), lambda);

  zinit = zidealstarinit(nf, idealpows(nf,pr,q));
  if (!check2(nf,gdiv(gx,p1),zinit)) res = -1;
  return res;
}

static long
zpsolnf(GEN nf,GEN pol,GEN pr,long nu,GEN pnu,GEN x0,GEN repr,GEN zinit)
{
  long i, result;
  pari_sp ltop=avma;
  GEN pnup;

  result = zinit? lemma7nf(nf,pol,pr,nu,x0,zinit)
                : lemma6nf(nf,pol,pr,nu,x0);
  avma = ltop;
  if (result== 1) return 1;
  if (result==-1) return 0;
  pnup = gmul(pnu, basistoalg(nf,(GEN)pr[2]));
  nu++;
  for (i=1; i<lg(repr); i++)
    if (zpsolnf(nf,pol,pr,nu,pnup,gadd(x0,gmul(pnu,(GEN)repr[i])),repr,zinit))
    { avma=ltop; return 1; }
  avma=ltop; return 0;
}

/* calcule un systeme de representants Zk/pr */
static GEN
repres(GEN nf,GEN pr)
{
  long i,j,k,f,pp,ppf,ppi;
  GEN mat,fond,rep;

  fond=cgetg(1,t_VEC);
  mat=idealhermite(nf,pr);
  for (i=1; i<lg(mat); i++)
    if (!gcmp1(gmael(mat,i,i)))
      fond = concatsp(fond,gmael(nf,7,i));
  f=lg(fond)-1;
  pp=itos((GEN) pr[1]);
  for (i=1,ppf=1; i<=f; i++) ppf*=pp;
  rep=cgetg(ppf+1,t_VEC);
  rep[1]= (long)gen_0; ppi=1;
  for (i=0; i<f; i++,ppi*=pp)
    for (j=1; j<pp; j++)
      for (k=1; k<=ppi; k++)
	rep[j*ppi+k]=ladd((GEN) rep[k],gmulsg(j,(GEN) fond[i+1]));
  return gmodulcp(rep,(GEN) nf[1]);
}

/* =1 si l'equation y^2 = z^deg(pol) * pol(x/z) a une solution rationnelle
 *    p-adique (eventuellement (1,y,0) = oo)
 * =0 sinon.
 * Les coefficients de pol doivent etre des entiers de nf. */
long
qpsolublenf(GEN nf,GEN pol,GEN pr)
{
  GEN repr, zinit, p1;
  pari_sp ltop=avma;

  if (gcmp0(pol)) return 1;
  if (typ(pol)!=t_POL) err(notpoler,"qpsolublenf");
  checkprimeid(pr);
  nf = checknf(nf);

  if (equaliu((GEN)pr[1], 2))
  { /* tough case */
    zinit = zidealstarinit(nf, idealpows(nf,pr,1+2*idealval(nf,gen_2,pr)));
    if (psquare2nf(nf,constant_term(pol),pr,zinit)) return 1;
    if (psquare2nf(nf, leading_term(pol),pr,zinit)) return 1;
  }
  else
  {
    if (psquarenf(nf,constant_term(pol),pr)) return 1;
    if (psquarenf(nf, leading_term(pol),pr)) return 1;
    zinit = NULL;
  }
  repr = repres(nf,pr);
  if (zpsolnf(nf,pol,pr,0,gen_1,gen_0,repr,zinit)) { avma=ltop; return 1; }
  p1 = basistoalg(nf, (GEN)pr[2]);
  if (zpsolnf(nf,polrecip(pol),pr,1,p1,gen_0,repr,zinit))
    { avma=ltop; return 1; }

  avma=ltop; return 0;
}

/* =1 si l'equation y^2 = pol(x) a une solution entiere p-adique
 * =0 sinon.
 * Les coefficients de pol doivent etre des entiers de nf. */
long
zpsolublenf(GEN nf,GEN pol,GEN pr)
{
  GEN repr,zinit;
  pari_sp ltop=avma;

  if (gcmp0(pol)) return 1;
  if (typ(pol)!=t_POL) err(notpoler,"zpsolublenf");
  checkprimeid(pr);
  nf = checknf(nf);

  if (equaliu((GEN)pr[1],2))
  {
    zinit = zidealstarinit(nf,idealpows(nf,pr,1+2*idealval(nf,gen_2,pr)));
    if (psquare2nf(nf,constant_term(pol),pr,zinit)) return 1;
  }
  else
  {
    if (psquarenf(nf,constant_term(pol),pr)) return 1;
    zinit = NULL;
  }
  repr=repres(nf,pr);
  if (zpsolnf(nf,pol,pr,0,gen_1,gen_0,repr,zinit)) { avma=ltop; return 1; }
  avma=ltop; return 0;
}

static long
hilb2nf(GEN nf,GEN a,GEN b,GEN p)
{
  pari_sp av = avma;
  long rep;
  GEN pol;

  if (typ(a) != t_POLMOD) a = basistoalg(nf, a);
  if (typ(b) != t_POLMOD) b = basistoalg(nf, b);
  pol = coefs_to_pol(3, lift(a), zero, lift(b));
  /* varn(nf.pol) = 0, pol is not a valid GEN  [as in Pol([x,x], x)].
   * But it is only used as a placeholder, hence it is not a problem */

  rep = qpsolublenf(nf,pol,p)? 1: -1;
  avma = av; return rep;
}

/* local quadratic Hilbert symbol (a,b)_pr, for a,b (non-zero) in nf */
long
nfhilbertp(GEN nf,GEN a,GEN b,GEN pr)
{
  GEN ord, ordp, T,p, modpr,t;
  long va, vb, rep;
  pari_sp av = avma;

  if (gcmp0(a) || gcmp0(b)) err (talker,"0 argument in nfhilbertp");
  checkprimeid(pr); nf = checknf(nf);
  p = (GEN)pr[1];

  if (equaliu(p,2)) return hilb2nf(nf,a,b,pr);

  /* pr not above 2, compute t = tame symbol */
  va = idealval(nf,a,pr);
  vb = idealval(nf,b,pr);
  if (!odd(va) && !odd(vb)) { avma = av; return 1; }
  t = element_div(nf, element_pow(nf,a, stoi(vb)),
                      element_pow(nf,b, stoi(va)));
  if (odd(va) && odd(vb)) t = gneg_i(t); /* t mod pr = tame_pr(a,b) */

  /* quad. symbol is image of t by the quadratic character  */
  ord = subis( pr_norm(pr), 1 ); /* |(O_K / pr)^*| */
  ordp= subis( p, 1);                 /* |F_p^*|        */
  modpr = nf_to_ff_init(nf, &pr,&T,&p);
  t = nf_to_ff(nf,t,modpr);
  t = Fq_pow(t, diviiexact(ord, ordp), T,p); /* in F_p^* */
  if (typ(t) == t_POL)
  {
    if (degpol(t)) err(bugparier,"nfhilbertp");
    t = constant_term(t);
  }
  rep = kronecker(t, p);
  avma = av; return rep;
}

/* global quadratic Hilbert symbol (a,b):
 *  =  1 if X^2 - aY^2 - bZ^2 has a point in projective plane
 *  = -1 otherwise
 * a, b should be non-zero
 */
long
nfhilbert(GEN nf,GEN a,GEN b)
{
  pari_sp av = avma;
  long r1, i;
  GEN S, al, bl, ro;

  if (gcmp0(a) || gcmp0(b)) err (talker,"0 argument in nfhilbert");
  nf = checknf(nf);

  if (typ(a) != t_POLMOD) a = basistoalg(nf, a);
  if (typ(b) != t_POLMOD) b = basistoalg(nf, b);

  al = lift(a);
  bl = lift(b);
 /* local solutions in real completions ? */
  r1 = nf_get_r1(nf); ro = (GEN)nf[6];
  for (i=1; i<=r1; i++)
    if (signe(poleval(al,(GEN)ro[i])) < 0 &&
        signe(poleval(bl,(GEN)ro[i])) < 0)
    {
      if (DEBUGLEVEL>=4)
        fprintferr("nfhilbert not soluble at real place %ld\n",i);
      avma = av; return -1;
    }

  /* local solutions in finite completions ? (pr | 2ab)
   * primes above 2 are toughest. Try the others first */

  S = (GEN) idealfactor(nf,gmul(gmulsg(2,a),b))[1];
  /* product of all hilbertp is 1 ==> remove one prime (above 2!) */
  for (i=lg(S)-1; i>1; i--)
    if (nfhilbertp(nf,a,b,(GEN) S[i]) < 0)
    {
      if (DEBUGLEVEL >=4)
	fprintferr("nfhilbert not soluble at finite place: %Z\n",S[i]);
      avma = av; return -1;
    }
  avma = av; return 1;
}

long
nfhilbert0(GEN nf,GEN a,GEN b,GEN p)
{
  if (p) return nfhilbertp(nf,a,b,p);
  return nfhilbert(nf,a,b);
}

/* S a list of prime ideal in primedec format. Return res:
 * res[1] = generators of (S-units / units), as polynomials
 * res[2] = [perm, HB, den], for bnfissunit
 * res[3] = [] (was: log. embeddings of res[1])
 * res[4] = S-regulator ( = R * det(res[2]) * \prod log(Norm(S[i])))
 * res[5] = S class group
 * res[6] = S */
GEN
bnfsunit(GEN bnf,GEN S,long prec)
{
  pari_sp ltop = avma;
  long i,j,ls;
  GEN p1,nf,classgp,gen,M,U,H;
  GEN sunit,card,sreg,res,pow;

  if (typ(S) != t_VEC) err(typeer,"bnfsunit");
  bnf = checkbnf(bnf); nf=(GEN)bnf[7];
  classgp=gmael(bnf,8,1);
  gen = (GEN)classgp[3];

  sreg = gmael(bnf,8,2);
  res=cgetg(7,t_VEC);
  res[1]=res[2]=res[3]=lgetg(1,t_VEC);
  res[4]=(long)sreg;
  res[5]=(long)classgp;
  res[6]=(long)S; ls=lg(S);

 /* M = relation matrix for the S class group (in terms of the class group
  * generators given by gen)
  * 1) ideals in S
  */
  M = cgetg(ls,t_MAT);
  for (i=1; i<ls; i++)
  {
    p1 = (GEN)S[i]; checkprimeid(p1);
    M[i] = (long)isprincipal(bnf,p1);
  }
  /* 2) relations from bnf class group */		
  M = concatsp(M, diagonal_i((GEN) classgp[2]));

  /* S class group */
  H = hnfall_i(M, &U, 1);
  card = gen_1;
  if (lg(H) > 1)
  { /* non trivial (rare!) */
    GEN U, D = smithall(H, &U, NULL);
    D = mattodiagonal_i(D);
    card = detcyc(D, &i);
    setlg(D,i);
    p1=cgetg(i,t_VEC); pow=ZM_inv(U,gen_1);
    for(i--; i; i--)
      p1[i] = (long)factorback_i(gen, (GEN)pow[i], nf, 1);
    res[5] = (long)mkvec3(card,D,p1);
  }

  /* S-units */
  if (ls>1)
  {
    GEN den, Sperm, perm, dep, B, A, U1 = U;
    long lH, lB, fl = nf_GEN|nf_FORCE;

   /* U1 = upper left corner of U, invertible. S * U1 = principal ideals
    * whose generators generate the S-units */
    setlg(U1,ls); p1 = cgetg(ls, t_MAT); /* p1 is junk for mathnfspec */
    for (i=1; i<ls; i++) { setlg(U1[i],ls); p1[i] = lgetg(1,t_COL); }
    H = mathnfspec(U1,&perm,&dep,&B,&p1);
    lH = lg(H);
    lB = lg(B);
    if (lg(dep) > 1 && lg(dep[1]) > 1) err(bugparier,"bnfsunit");
   /*                   [ H B  ]            [ H^-1   - H^-1 B ]
    * perm o HNF(U1) =  [ 0 Id ], inverse = [  0         Id   ]
    * (permute the rows)
    * S * HNF(U1) = _integral_ generators for S-units  = sunit */
    Sperm = cgetg(ls, t_VEC); sunit = cgetg(ls, t_VEC);
    for (i=1; i<ls; i++) Sperm[i] = S[perm[i]]; /* S o perm */

    setlg(Sperm, lH);
    for (i=1; i<lH; i++)
      sunit[i] = isprincipalfact(bnf,Sperm,(GEN)H[i],NULL,fl)[2];
    for (j=1; j<lB; j++,i++)
      sunit[i] = isprincipalfact(bnf,Sperm,(GEN)B[j],(GEN)Sperm[i],fl)[2];

    den = dethnf_i(H); H = ZM_inv(H,den);
    A = concatsp(H, gneg(gmul(H,B))); /* top part of inverse * den */
    sunit = basistoalg(nf,sunit);
    /* HNF in split form perm + (H B) [0 Id missing] */
    res[1] = (long)lift_intern(sunit);
    res[2] = (long)mkvec3(perm,A,den);
  }

  /* S-regulator */
  sreg = gmul(sreg,card);
  for (i=1; i<ls; i++)
  {
    GEN p = (GEN)S[i];
    if (typ(p) == t_VEC) p = (GEN) p[1];
    sreg = gmul(sreg,glog(p,prec));
  }
  res[4]=(long) sreg;
  return gerepilecopy(ltop,res);
}

static GEN
make_unit(GEN bnf, GEN suni, GEN *px)
{
  long lB, cH, i, k, ls;
  GEN den,gen,S,v,p1,xp,xm,xb,N,HB,perm;

  if (gcmp0(*px)) return NULL;
  S = (GEN) suni[6]; ls=lg(S);
  if (ls==1) return cgetg(1, t_COL);

  xb = algtobasis(bnf,*px); p1 = Q_denom(xb);
  N = mulii(gnorm(gmul(*px,p1)), p1); /* relevant primes divide N */
  if (is_pm1(N)) return zerocol(ls -1);

  p1 = (GEN)suni[2];
  perm = (GEN)p1[1];
  HB = (GEN)p1[2];
  den = (GEN)p1[3];
  cH = lg(HB[1]) - 1;
  lB = lg(HB) - cH;
  v = cgetg(ls, t_VECSMALL);
  for (i=1; i<ls; i++)
  {
    GEN P = (GEN)S[i];
    v[i] = (remii(N, (GEN)P[1]) == gen_0)? element_val(bnf,xb,P): 0;
  }
  /* here, x = S v */
  p1 = cgetg(ls, t_COL);
  for (i=1; i<ls; i++) p1[i] = lstoi(v[perm[i]]); /* p1 = v o perm */
  v = gmul(HB, p1);
  for (i=1; i<=cH; i++)
  {
    GEN w = gdiv((GEN)v[i], den);
    if (typ(w) != t_INT) return NULL;
    v[i] = (long)w;
  }
  p1 += cH;
  p1[0] = evaltyp(t_COL) | evallg(lB);
  v = concatsp(v, p1); /* append bottom of p1 (= [0 Id] part) */

  xp = gen_1; xm = gen_1; gen = (GEN)suni[1];
  for (i=1; i<ls; i++)
  {
    k = -itos((GEN)v[i]); if (!k) continue;
    p1 = basistoalg(bnf, (GEN)gen[i]);
    if (k > 0) xp = gmul(xp, gpowgs(p1, k));
    else       xm = gmul(xm, gpowgs(p1,-k));
  }
  if (xp != gen_1) *px = gmul(*px,xp);
  if (xm != gen_1) *px = gdiv(*px,xm);
  return v;
}

/* cette fonction est l'equivalent de isunit, sauf qu'elle donne le resultat
 * avec des s-unites: si x n'est pas une s-unite alors issunit=[]~;
 * si x est une s-unite alors
 * x=\prod_{i=0}^r {e_i^issunit[i]}*prod{i=r+1}^{r+s} {s_i^issunit[i]}
 * ou les e_i sont les unites du corps (comme dans isunit)
 * et les s_i sont les s-unites calculees par sunit (dans le meme ordre).
 */
GEN
bnfissunit(GEN bnf,GEN suni,GEN x)
{
  pari_sp av = avma;
  GEN v, w;

  bnf = checkbnf(bnf);
  if (typ(suni)!=t_VEC || lg(suni)!=7) err(typeer,"bnfissunit");
  switch (typ(x))
  {
    case t_INT: case t_FRAC: case t_POL: case t_COL:
      x = basistoalg(bnf,x); break;
    case t_POLMOD: break;
    default: err(typeer,"bnfissunit");
  }
  v = NULL;
  if ( (w = make_unit(bnf, suni, &x)) ) v = isunit(bnf, x);
  if (!v || lg(v) == 1) { avma = av; return cgetg(1,t_COL); }
  return gerepileupto(av, concat(v, w));
}

static void
pr_append(GEN nf, GEN rel, GEN p, GEN *prod, GEN *S1, GEN *S2)
{
  if (dvdii(*prod, p)) return;
  *prod = mulii(*prod, p);
  *S1 = concatsp(*S1, primedec(nf,p));
  *S2 = concatsp(*S2, primedec(rel,p));
}

static void
fa_pr_append(GEN nf,GEN rel,GEN N,GEN *prod,GEN *S1,GEN *S2)
{
  if (!is_pm1(N))
  {
    GEN v = (GEN)factor(N)[1];
    long i, l = lg(v);
    for (i=1; i<l; i++) pr_append(nf,rel,(GEN)v[i],prod,S1,S2);
  }
}

static GEN
pol_up(GEN rnfeq, GEN x, long v)
{
  long i, l = lg(x);
  GEN y = cgetg(l, t_POL); y[1] = x[1];
  for (i=2; i<l; i++) 
  {
    GEN t = eltreltoabs(rnfeq, gel(x,i));
    if (typ(t) == t_POL) setvarn(t, v);
    gel(y,i) = t;
  }
  return y;
}

GEN
rnfisnorminit(GEN T, GEN relpol, int galois)
{
  pari_sp av = avma;
  long i, l, drel, vbas; 
  GEN prod, S1, S2, gen, cyc, bnf, nf, nfabs, rnfeq, bnfabs, res, k, polabs;
  GEN y = cgetg(9, t_VEC);

  T = get_bnfpol(T, &bnf, &nf); vbas = varn(T);
  if (!bnf) bnf = bnfinit0(nf? nf: T, 1, NULL, DEFAULTPREC);
  if (!nf) nf = checknf(bnf);

  relpol = get_bnfpol(relpol, &bnfabs, &nfabs);
  if (!gcmp1(leading_term(relpol))) err(impl,"non monic relative equation");
  drel = degpol(relpol);
  if (varncmp(varn(relpol), vbas) >= 0)
    err(talker,"main variable must be of higher priority in rnfisnorminit");

  rnfeq = NULL; /* no reltoabs needed */
  if (degpol(nf[1]) == 1)
  { /* over Q */
    polabs = lift(relpol);
    k = gen_0;
  }
  else
  {
    if (galois == 2 && drel > 2)
    { /* needs reltoabs */
      rnfeq = rnfequation2(bnf, relpol);
      polabs = gel(rnfeq,1);
      gel(rnfeq,2) = lift_intern(gel(rnfeq,2));
      k = gel(rnfeq,3);
    }
    else
    {
      long sk;
      polabs = _rnfequation(bnf, relpol, &sk, NULL);
      k = stoi(sk);
    }
  }
  if (!bnfabs || !gcmp0(k)) bnfabs = bnfinit0(polabs, 1, NULL, nfgetprec(nf));
  if (!nfabs) nfabs = checknf(bnfabs);

  if (galois < 0 || galois > 2) err(flagerr, "rnfisnorminit");
  if (galois == 2)
  {
    GEN P = rnfeq? pol_up(rnfeq, relpol, vbas): relpol;
    galois = nfisgalois(gsubst(nfabs, varn(nfabs[1]), polx[vbas]), P);
  }

  prod = gen_1; S1 = S2 = cgetg(1, t_VEC);
  res = gmael(bnfabs,8,1);
  cyc = (GEN)res[2];
  gen = (GEN)res[3]; l = lg(cyc);
  for(i=1; i<l; i++)
  {
    if (cgcd(umodiu((GEN)cyc[i], drel), drel) == 1) break;
    fa_pr_append(nf,bnfabs,gmael3(gen,i,1,1),&prod,&S1,&S2);
  }
  if (!galois)
  {
    GEN Ndiscrel = diviiexact((GEN)nfabs[3], gpowgs((GEN)nf[3], drel));
    fa_pr_append(nf,bnfabs,absi(Ndiscrel), &prod,&S1,&S2);
  }

  y[1] = (long)bnf;
  y[2] = (long)bnfabs;
  y[3] = (long)relpol;
  y[4] = (long)get_theta_abstorel(T, relpol, k);
  y[5] = (long)prod;
  y[6] = (long)S1;
  y[7] = (long)S2;
  y[8] = lstoi(galois); return gerepilecopy(av, y);
}

/* T as output by rnfisnorminit
 * if flag=0 assume extension is Galois (==> answer is unconditional)
 * if flag>0 add to S all primes dividing p <= flag
 * if flag<0 add to S all primes dividing abs(flag)

 * answer is a vector v = [a,b] such that
 * x = N(a)*b and x is a norm iff b = 1  [assuming S large enough] */
GEN
rnfisnorm(GEN T, GEN x, long flag)
{
  pari_sp av = avma;
  GEN bnf = (GEN)T[1], rel = (GEN)T[2], relpol = (GEN)T[3], theta = (GEN)T[4];
  GEN nf, aux, H, U, Y, M, A, suni, sunitrel, futu, tu, w, prod, S1, S2;
  long L, i, drel, itu;

  if (typ(T) != t_VEC || lg(T) != 9)
    err(talker,"please apply rnfisnorminit first");
  bnf = checkbnf(bnf);
  rel = checkbnf(rel);
  nf = checknf(bnf);
  x = basistoalg(nf,x);
  if (typ(x) != t_POLMOD) err(typeer, "rnfisnorm");
  drel = degpol(relpol);
  if (gcmp0(x) || gcmp1(x) || (gcmp_1(x) && odd(drel)))
  {
    GEN res = cgetg(3, t_VEC);
    res[1] = (long)simplify((GEN)x[2]);
    res[2] = (long)gen_1; return res;
  }

  /* build set T of ideals involved in the solutions */
  prod = (GEN)T[5];
  S1   = (GEN)T[6];
  S2   = (GEN)T[7];
  if (flag && !gcmp0((GEN)T[8]))
    err(warner,"useless flag in rnfisnorm: the extension is Galois");
  if (flag > 0)
  {
    byteptr d = diffptr;
    long p = 0;
    maxprime_check((ulong)flag);
    for(;;)
    {
      NEXT_PRIME_VIADIFF(p, d);
      if (p > flag) break;
      pr_append(nf,rel, utoipos(p),&prod,&S1,&S2);
    }
  }
  else if (flag < 0)
    fa_pr_append(nf,rel,stoi(-flag),&prod,&S1,&S2);
  /* overkill: prime ideals dividing x would be enough */
  fa_pr_append(nf,rel,idealnorm(nf,x), &prod,&S1,&S2);

  /* computation on T-units */
  w  = gmael3(rel,8,4,1);
  tu = gmael3(rel,8,4,2);
  futu = concatsp(check_units(rel,"rnfisnorm"), tu);
  suni = bnfsunit(bnf,S1,3);
  sunitrel = (GEN)bnfsunit(rel,S2,3)[1];
  if (lg(sunitrel) > 1) sunitrel = lift_intern(basistoalg(rel,sunitrel));
  sunitrel = concatsp(futu, sunitrel);

  A = lift(bnfissunit(bnf,suni,x));
  L = lg(sunitrel);
  itu = lg(nf[6])-1; /* index of torsion unit in bnfsunit(nf) output */
  M = cgetg(L+1,t_MAT);
  for (i=1; i<L; i++)
  {
    GEN u = poleval((GEN)sunitrel[i], theta); /* abstorel */
    if (typ(u) != t_POLMOD) u = mkpolmod(u, (GEN)theta[1]);
    sunitrel[i] = (long)u;
    u = bnfissunit(bnf,suni, gnorm(u));
    if (lg(u) == 1) err(bugparier,"rnfisnorm");
    u[itu] = llift((GEN)u[itu]); /* lift root of 1 part */
    M[i] = (long)u;
  }
  aux = zerocol(lg(A)-1); aux[itu] = (long)w;
  M[L] = (long)aux;
  H = hnfall_i(M, &U, 0);
  Y = gmul(U, inverseimage(H,A));
  /* Y: sols of MY = A over Q */
  setlg(Y, L);
  aux = factorback(sunitrel, gfloor(Y));
  x = gdiv(x, gnorm(gmodulcp(lift_intern(aux), relpol)));
  if (typ(x) == t_POLMOD && (typ(x[2]) != t_POL || !degpol(x[2])))
  {
    x = (GEN)x[2]; /* rational number */
    if (typ(x) == t_POL) x = (GEN)x[2];
  }
  if (typ(aux) == t_POLMOD && degpol(nf[1]) == 1)
    aux[2] = (long)lift_intern((GEN)aux[2]);
  return gerepilecopy(av, mkvec2(aux, x));
}

GEN
bnfisnorm(GEN bnf,GEN x,long flag,long PREC)
{
  pari_sp av = avma;
  GEN T = rnfisnorminit(polx[MAXVARN], bnf, flag == 0? 1: 2);
  return gerepileupto(av, rnfisnorm(T, x, flag == 1? 0: flag));
}
