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
#include "parinf.h"

static long
psquare(GEN a,GEN p)
{
  long v;
  GEN ap;

  if (gcmp0(a) || gcmp1(a)) return 1;

  if (!cmpis(p,2))
  {
    v=vali(a); if (v&1) return 0;
    return (smodis(shifti(a,-v),8)==1);
  }

  ap=stoi(1); v=pvaluation(a,p,&ap);
  if (v&1) return 0;
  return (kronecker(ap,p)==1);
}

static long
lemma6(GEN pol,GEN p,long nu,GEN x)
{
  long i,lambda,mu,ltop=avma;
  GEN gx,gpx;

  for (i=lgef(pol)-2,gx=(GEN) pol[i+1]; i>1; i--)
    gx=addii(mulii(gx,x),(GEN) pol[i]);
  if (psquare(gx,p)) return 1;

  for (i=lgef(pol)-2,gpx=mulis((GEN) pol[i+1],i-1); i>2; i--)
    gpx=addii(mulii(gpx,x),mulis((GEN) pol[i],i-2));

  lambda=pvaluation(gx,p,&gx);
  if (gcmp0(gpx)) mu=BIGINT; else mu=pvaluation(gpx,p,&gpx);
  avma=ltop;

  if (lambda>(mu<<1)) return 1;
  if (lambda>=(nu<<1) && mu>=nu) return 0;
  return -1;
}

static long
lemma7(GEN pol,long nu,GEN x)
{ long i,odd4,lambda,mu,mnl,ltop=avma;
  GEN gx,gpx,oddgx;

  for (i=lgef(pol)-2,gx=(GEN) pol[i+1]; i>1; i--)
    gx=addii(mulii(gx,x),(GEN) pol[i]);
  if (psquare(gx,gdeux)) return 1;

  for (i=lgef(pol)-2,gpx=gmulgs((GEN) pol[i+1],i-1); i>2; i--)
    gpx=gadd(gmul(gpx,x),gmulgs((GEN) pol[i],i-2));

  lambda=vali(gx);
  if (gcmp0(gpx)) mu=BIGINT; else mu=vali(gpx);
  oddgx=shifti(gx,-lambda);
  mnl=mu+nu-lambda;
  odd4=smodis(oddgx,4);
  avma=ltop;
  if (lambda>(mu<<1)) return 1;
  if (nu > mu)
    { if (mnl==1 && (lambda&1) == 0) return 1;
      if (mnl==2 && (lambda&1) == 0 && odd4==1) return 1;
    }
  else
    { if (lambda>=(nu<<1)) return 0;
      if (lambda==((nu-1)<<1) && odd4==1) return 0;
    }
  return -1;
}

static long
zpsol(GEN pol,GEN p,long nu,GEN pnu,GEN x0)
{
  long i,result,ltop=avma;
  GEN x,pnup;

  result = (cmpis(p,2)) ? lemma6(pol,p,nu,x0) : lemma7(pol,nu,x0);
  if (result==+1) return 1; if (result==-1) return 0;
  x=gcopy(x0); pnup=mulii(pnu,p);
  for (i=0; i<itos(p); i++)
  {
    x=addii(x,pnu);
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
  return zpsol(pol,p,0,gun,gzero);
}

/* vaut 1 si l'equation y^2=Pol(x) a une solution p-adique rationnelle
 * (eventuellement infinie), 0 sinon. Les coefficients sont entiers.
 */
long
qpsoluble(GEN pol,GEN p)
{
  if ((typ(pol)!=t_POL && typ(pol)!=t_INT) || typ(p)!=t_INT )
    err(typeer,"qpsoluble");
  if (zpsol(pol,p,0,gun,gzero)) return 1;
  return (zpsol(polrecip(pol),p,1,p,gzero));
}

/* (pr,2) = 1. return 1 if a square in (ZK / pr), 0 otherwise */
static long
psquarenf(GEN nf,GEN a,GEN pr)
{
  ulong av = avma;
  long v;
  GEN norm;

  if (gcmp0(a)) return 1;
  v = idealval(nf,a,pr); if (v&1) return 0;
  if (v) a = gdiv(a, gpowgs(basistoalg(nf, (GEN)pr[2]), v));

  norm = gshift(idealnorm(nf,pr), -1);
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
  GEN zlog=zideallog(nf,a,zinit), p1 = gmael(zinit,2,2);
  long i;

  for (i=1; i<lg(p1); i++)
    if (!mpodd((GEN)p1[i]) && mpodd((GEN)zlog[i])) return 0;
  return 1;
}

/* pr | 2. Return 1 if a square in (ZK / pr), 0 otherwise */
static long
psquare2nf(GEN nf,GEN a,GEN pr,GEN zinit)
{
  long v, ltop = avma;

  if (gcmp0(a)) return 1;
  v = idealval(nf,a,pr); if (v&1) return 0;
  if (v) a = gdiv(a, gpowgs(basistoalg(nf, (GEN)pr[2]), v));
  /* now (a,pr) = 1 */
  v = check2(nf,a,zinit); avma = ltop; return v;
}

/* pr | 2. Return 1 if a square in (ZK / pr^q)^*, and 0 otherwise */
static long
psquare2qnf(GEN nf,GEN a,GEN p,long q)
{
  long v, ltop=avma;
  GEN zinit = zidealstarinit(nf,idealpows(nf,p,q));

  v = check2(nf,a,zinit); avma = ltop; return v;
}

static long
lemma6nf(GEN nf,GEN pol,GEN p,long nu,GEN x)
{
  long i,lambda,mu,ltop=avma;
  GEN gx,gpx;

  for (i=lgef(pol)-2,gx=(GEN) pol[i+1]; i>1; i--)
    gx = gadd(gmul(gx,x),(GEN) pol[i]);
  if (psquarenf(nf,gx,p)) { avma=ltop; return 1; }
  lambda = idealval(nf,gx,p);

  for (i=lgef(pol)-2,gpx=gmulgs((GEN) pol[i+1],i-1); i>2; i--)
    gpx=gadd(gmul(gpx,x),gmulgs((GEN) pol[i],i-2));
  mu = gcmp0(gpx)? BIGINT: idealval(nf,gpx,p);

  avma=ltop;
  if (lambda > mu<<1) return 1;
  if (lambda >= nu<<1  && mu >= nu) return 0;
  return -1;
}

static long
lemma7nf(GEN nf,GEN pol,GEN p,long nu,GEN x,GEN zinit)
{
  long res,i,lambda,mu,q,ltop=avma;
  GEN gx,gpx,p1;

  for (i=lgef(pol)-2, gx=(GEN) pol[i+1]; i>1; i--)
    gx=gadd(gmul(gx,x),(GEN) pol[i]);
  if (psquare2nf(nf,gx,p,zinit)) { avma=ltop; return 1; }
  lambda=idealval(nf,gx,p);

  for (i=lgef(pol)-2,gpx=gmulgs((GEN) pol[i+1],i-1); i>2; i--)
    gpx=gadd(gmul(gpx,x),gmulgs((GEN) pol[i],i-2));
  if (!gcmp0(gpx)) mu=idealval(nf,gpx,p); else mu=BIGINT;

  if (lambda>(mu<<1)) { avma=ltop; return 1; }
  if (nu > mu)
  {
    if (lambda&1) { avma=ltop; return -1; }
    q=mu+nu-lambda; res=1;
  }
  else
  {
    if (lambda>=(nu<<1)) { avma=ltop; return 0; }
    if (lambda&1) { avma=ltop; return -1; }
    q=(nu<<1)-lambda; res=0;
  }
  if (q > itos((GEN) p[3])<<1) { avma=ltop; return -1; }
  p1 = gmodulcp(gpuigs(gmul((GEN)nf[7],(GEN)p[2]), lambda), (GEN)nf[1]);
  if (!psquare2qnf(nf,gdiv(gx,p1), p,q)) res = -1;
  avma=ltop; return res;
}

static long
zpsolnf(GEN nf,GEN pol,GEN p,long nu,GEN pnu,GEN x0,GEN repr,GEN zinit)
{
  long i,result,ltop=avma;
  GEN pnup;

  nf=checknf(nf);
  if (cmpis((GEN) p[1],2))
    result=lemma6nf(nf,pol,p,nu,x0);
  else
    result=lemma7nf(nf,pol,p,nu,x0,zinit);
  if (result== 1) return 1;
  if (result==-1) return 0;
  pnup = gmul(pnu, basistoalg(nf,(GEN)p[2]));
  nu++;
  for (i=1; i<lg(repr); i++)
    if (zpsolnf(nf,pol,p,nu,pnup,gadd(x0,gmul(pnu,(GEN)repr[i])),repr,zinit))
    { avma=ltop; return 1; }
  avma=ltop; return 0;
}

/* calcule un systeme de representants Zk/p */
static GEN
repres(GEN nf,GEN p)
{
  long i,j,k,f,pp,ppf,ppi;
  GEN mat,fond,rep;

  fond=cgetg(1,t_VEC);
  mat=idealhermite(nf,p);
  for (i=1; i<lg(mat); i++)
    if (!gcmp1(gmael(mat,i,i)))
      fond = concatsp(fond,gmael(nf,7,i));
  f=lg(fond)-1;
  pp=itos((GEN) p[1]);
  for (i=1,ppf=1; i<=f; i++) ppf*=pp;
  rep=cgetg(ppf+1,t_VEC);
  rep[1]=zero; ppi=1;
  for (i=0; i<f; i++,ppi*=pp)
    for (j=1; j<pp; j++)
      for (k=1; k<=ppi; k++)
	rep[j*ppi+k]=ladd((GEN) rep[k],gmulsg(j,(GEN) fond[i+1]));
  return gmodulcp(rep,(GEN) nf[1]);
}

/* =1 si l'equation y^2 = z^deg(pol) * pol(x/z) a une solution rationnelle
 *    p-adique (eventuellement (1,y,0) = oo)
 * =0 sinon.
 * Les coefficients de pol doivent etre des entiers de nf.
 * p est un ideal premier sous forme primedec.
 */
long
qpsolublenf(GEN nf,GEN pol,GEN pr)
{
  GEN repr,zinit,p1;
  long ltop=avma;

  if (gcmp0(pol)) return 1;
  if (typ(pol)!=t_POL) err(notpoler,"qpsolublenf");
  checkprimeid(pr);

  if (egalii((GEN) pr[1], gdeux))
  { /* tough case */
    zinit = zidealstarinit(nf, idealpows(nf,pr,1+2*idealval(nf,gdeux,pr)));
    if (psquare2nf(nf,(GEN) pol[2],pr,zinit)) return 1;
    if (psquare2nf(nf, leading_term(pol),pr,zinit)) return 1;
  }
  else
  {
    if (psquarenf(nf,(GEN) pol[2],pr)) return 1;
    if (psquarenf(nf, leading_term(pol),pr)) return 1;
    zinit = gzero;
  }
  repr = repres(nf,pr);
  if (zpsolnf(nf,pol,pr,0,gun,gzero,repr,zinit)) { avma=ltop; return 1; }
  p1 = gmodulcp(gmul((GEN) nf[7],(GEN) pr[2]),(GEN) nf[1]);
  if (zpsolnf(nf,polrecip(pol),pr,1,p1,gzero,repr,zinit))
    { avma=ltop; return 1; }

  avma=ltop; return 0;
}

/* =1 si l'equation y^2 = pol(x) a une solution entiere p-adique
 * =0 sinon.
 * Les coefficients de pol doivent etre des entiers de nf.
 * p est un ideal premier sous forme primedec.
 */
long
zpsolublenf(GEN nf,GEN pol,GEN p)
{
  GEN repr,zinit;
  long ltop=avma;

  if (gcmp0(pol)) return 1;
  if (typ(pol)!=t_POL) err(notpoler,"zpsolublenf");
  if (typ(p)!=t_VEC || lg(p)!=6)
    err(talker,"not a prime ideal in zpsolublenf");
  nf=checknf(nf);

  if (cmpis((GEN)p[1],2))
  {
    if (psquarenf(nf,(GEN) pol[2],p)) return 1;
    zinit=gzero;
  }
  else
  {
    zinit=zidealstarinit(nf,idealpows(nf,p,1+2*idealval(nf,gdeux,p)));
    if (psquare2nf(nf,(GEN) pol[2],p,zinit)) return 1;
  }
  repr=repres(nf,p);
  if (zpsolnf(nf,pol,p,0,gun,gzero,repr,zinit)) { avma=ltop; return 1; }
  avma=ltop; return 0;
}

static long
hilb2nf(GEN nf,GEN a,GEN b,GEN p)
{
  ulong av = avma;
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
  GEN ord, ordp, p, prhall,t;
  long va, vb, rep;
  ulong av = avma;

  if (gcmp0(a) || gcmp0(b)) err (talker,"0 argument in nfhilbertp");
  checkprimeid(pr); nf = checknf(nf);
  p = (GEN)pr[1];

  if (egalii(p,gdeux)) return hilb2nf(nf,a,b,pr);

  /* pr not above 2, compute t = tame symbol */
  va = idealval(nf,a,pr);
  vb = idealval(nf,b,pr);
  if (!odd(va) && !odd(vb)) { avma = av; return 1; }
  t = element_div(nf, element_pow(nf,a,stoi(vb)),
                      element_pow(nf,b,stoi(va)));
  if (odd(va) && odd(vb)) t = gneg_i(t); /* t mod pr = tame_pr(a,b) */

  /* quad. symbol is image of t by the quadratic character  */
  ord = subis( idealnorm(nf,pr), 1 ); /* |(O_K / pr)^*| */
  ordp= subis( p, 1);                 /* |F_p^*|        */
  prhall = nfmodprinit(nf, pr);
  t = element_powmodpr(nf, t, divii(ord, ordp), prhall); /* in F_p^* */
  t = lift_intern((GEN)t[1]);
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
  ulong av = avma;
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

extern GEN isprincipalfact(GEN bnf,GEN P, GEN e, GEN C, long flag);
extern GEN vconcat(GEN Q1, GEN Q2);
extern GEN mathnfspec(GEN x, GEN *ptperm, GEN *ptdep, GEN *ptB, GEN *ptC);
extern GEN factorback_i(GEN fa, GEN e, GEN nf, int red);
/* S a list of prime ideal in primedec format. Return res:
 * res[1] = generators of (S-units / units), as polynomials
 * res[2] = [perm, HB, den], for bnfissunit
 * res[3] = [] (was: log. embeddings of res[1])
 * res[4] = S-regulator ( = R * det(res[2]) * \prod log(Norm(S[i])))
 * res[5] = S class group
 * res[6] = S
 */
GEN
bnfsunit(GEN bnf,GEN S,long prec)
{
  ulong ltop = avma;
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
  M = concatsp(M, diagonal((GEN) classgp[2]));

  /* S class group */
  H = hnfall(M); U = (GEN)H[2]; H= (GEN)H[1];
  card = gun;
  if (lg(H) > 1)
  { /* non trivial (rare!) */
    GEN SNF, ClS = cgetg(4,t_VEC);

    SNF = smith2(H); p1 = (GEN)SNF[3];
    card = dethnf_i(p1);
    ClS[1] = (long)card; /* h */
    for(i=1; i<lg(p1); i++)
      if (gcmp1((GEN)p1[i])) break;
    setlg(p1,i);
    ClS[2]=(long)p1; /* cyc */

    p1=cgetg(i,t_VEC); pow=ZM_inv((GEN)SNF[1],gun);
    for(i--; i; i--)
      p1[i] = (long)factorback_i(gen, (GEN)pow[i], nf, 1);
    ClS[3]=(long)p1; /* gen */
    res[5]=(long) ClS;
  }

  /* S-units */
  if (ls>1)
  {
    GEN den, Sperm, perm, dep, B, U1 = U;
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

    p1 = cgetg(4,t_VEC);
    den = dethnf_i(H); H = ZM_inv(H,den);
    p1[1] = (long)perm;
    p1[2] = (long)concatsp(H, gneg(gmul(H,B))); /* top part of inverse * den */
    p1[3] = (long)den; /* keep denominator separately */
    sunit = basistoalg(nf,sunit);
    res[2] = (long)p1; /* HNF in split form perm + (H B) [0 Id missing] */
    res[1] = (long)lift_intern(sunit);
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
  long lB,cH,i,k,ls,tetpil, av = avma;
  GEN den,gen,S,v,p1,xp,xm,xb,N,HB,perm;

  bnf = checkbnf(bnf);
  if (typ(suni)!=t_VEC || lg(suni)!=7) err(typeer,"bnfissunit");
  switch (typ(x))
  {
    case t_INT: case t_FRAC: case t_FRACN:
    case t_POL: case t_COL:
      x = basistoalg(bnf,x); break;
    case t_POLMOD: break;
    default: err(typeer,"bnfissunit");
  }
  if (gcmp0(x)) return cgetg(1,t_COL);

  S = (GEN) suni[6]; ls=lg(S);
  if (ls==1) return isunit(bnf,x);

  p1 = (GEN)suni[2];
  perm = (GEN)p1[1];
  HB = (GEN)p1[2]; den = (GEN)p1[3];
  cH = lg(HB[1]) - 1;
  lB = lg(HB) - cH;
  xb = algtobasis(bnf,x); p1 = denom(content(xb));
  N = mulii(gnorm(gmul(x,p1)), p1); /* relevant primes divide N */
  v = cgetg(ls, t_VECSMALL);
  for (i=1; i<ls; i++)
  {
    GEN P = (GEN)S[i];
    v[i] = (resii(N, (GEN)P[1]) == gzero)? element_val(bnf,xb,P): 0;
  }
  /* here, x = S v */
  p1 = cgetg(ls, t_COL);
  for (i=1; i<ls; i++) p1[i] = lstoi(v[perm[i]]); /* p1 = v o perm */
  v = gmul(HB, p1);
  for (i=1; i<=cH; i++)
  {
    GEN w = gdiv((GEN)v[i], den);
    if (typ(w) != t_INT) { avma = av; return cgetg(1,t_COL); }
    v[i] = (long)w;
  }
  p1 += cH;
  p1[0] = evaltyp(t_COL) | evallg(lB);
  v = concatsp(v, p1); /* append bottom of p1 (= [0 Id] part) */

  xp = gun; xm = gun; gen = (GEN)suni[1];
  for (i=1; i<ls; i++)
  {
    k = -itos((GEN)v[i]); if (!k) continue;
    p1 = basistoalg(bnf, (GEN)gen[i]);
    if (k > 0) xp = gmul(xp, gpuigs(p1, k));
    else       xm = gmul(xm, gpuigs(p1,-k));
  }
  if (xp != gun) x = gmul(x,xp);
  if (xm != gun) x = gdiv(x,xm);
  p1 = isunit(bnf,x);
  if (lg(p1)==1) { avma = av; return cgetg(1,t_COL); }
  tetpil=avma; return gerepile(av,tetpil,concat(p1,v));
}

static void
vecconcat(GEN bnf,GEN relnf,GEN vec,GEN *prod,GEN *S1,GEN *S2)
{
  long i;

  for (i=1; i<lg(vec); i++)
    if (signe(resii(*prod,(GEN)vec[i])))
    {
       *prod=mulii(*prod,(GEN)vec[i]);
       *S1=concatsp(*S1,primedec(bnf,(GEN)vec[i]));
       *S2=concatsp(*S2,primedec(relnf,(GEN)vec[i]));
    }
}

/* bnf est le corps de base (buchinitfu).
 * ext definit l'extension relative:
 * ext[1] est une equation relative du corps,
 * telle qu'une de ses racines engendre le corps sur Q.
 * ext[2] exprime le generateur (y) du corps de base,
 * en fonction de la racine (x) de ext[1],
 * ext[3] est le buchinitfu (sur Q) de l'extension.

 * si flag=0 c'est qu'on sait a l'avance que l'extension est galoisienne,
 * et dans ce cas la reponse est exacte.
 * si flag>0 alors on ajoue dans S tous les ideaux qui divisent p<=flag.
 * si flag<0 alors on ajoute dans S tous les ideaux qui divisent -flag.

 * la reponse est un vecteur v a 2 composantes telles que
 * x=N(v[1])*v[2].
 * x est une norme ssi v[2]=1.
 */
GEN
rnfisnorm(GEN bnf,GEN ext,GEN x,long flag,long PREC)
{
  long lgsunitrelnf,i;
  ulong ltop = avma;
  GEN relnf,aux,vec,tors,xnf,H,Y,M,A,suni,sunitrelnf,sunitnormnf,prod;
  GEN res = cgetg(3,t_VEC), S1,S2;

  if (typ(ext)!=t_VEC || lg(ext)!=4) err (typeer,"bnfisnorm");
  if (typ(x)!=t_POL) x = basistoalg(bnf,x);
  bnf = checkbnf(bnf); relnf = (GEN)ext[3];
  if (gcmp0(x) || gcmp1(x) || (gcmp_1(x) && (degpol(ext[1])&1)))
  {
    avma = (long)res; res[1]=lcopy(x); res[2]=un; return res;
  }

/* construction de l'ensemble S des ideaux
   qui interviennent dans les solutions */

  prod=gun; S1=S2=cgetg(1,t_VEC);
  if (!gcmp1(gmael3(relnf,8,1,1)))
  {
    GEN genclass=gmael3(relnf,8,1,3);
    vec=cgetg(1,t_VEC);
    for(i=1;i<lg(genclass);i++)
      if (!gcmp1(ggcd(gmael4(relnf,8,1,2,i), stoi(degpol(ext[1])))))
        vec=concatsp(vec,(GEN)factor(gmael3(genclass,i,1,1))[1]);
    vecconcat(bnf,relnf,vec,&prod,&S1,&S2);
  }

  if (flag>1)
  {
    for (i=2; i<=flag; i++)
      if (isprime(stoi(i)) && signe(resis(prod,i)))
      {
	prod=mulis(prod,i);
	S1=concatsp(S1,primedec(bnf,stoi(i)));
	S2=concatsp(S2,primedec(relnf,stoi(i)));
      }
  }
  else if (flag<0)
    vecconcat(bnf,relnf,(GEN)factor(stoi(-flag))[1],&prod,&S1,&S2);

  if (flag)
  {
    GEN normdiscrel=divii(gmael(relnf,7,3),
			  gpuigs(gmael(bnf,7,3),lg(ext[1])-3));
    vecconcat(bnf,relnf,(GEN) factor(absi(normdiscrel))[1],
	      &prod,&S1,&S2);
  }
  vec=(GEN) idealfactor(bnf,x)[1]; aux=cgetg(2,t_VEC);
  for (i=1; i<lg(vec); i++)
    if (signe(resii(prod,gmael(vec,i,1))))
    {
      aux[1]=vec[i]; S1=concatsp(S1,aux);
    }
  xnf=lift(x);
  xnf=gsubst(xnf,varn(xnf),(GEN)ext[2]);
  vec=(GEN) idealfactor(relnf,xnf)[1];
  for (i=1; i<lg(vec); i++)
    if (signe(resii(prod,gmael(vec,i,1))))
    {
      aux[1]=vec[i]; S2=concatsp(S2,aux);
    }

  res[1]=un; res[2]=(long)x;
  tors=cgetg(2,t_VEC); tors[1]=mael3(relnf,8,4,2);

  /* calcul sur les S-unites */

  suni=bnfsunit(bnf,S1,PREC);
  A=lift(bnfissunit(bnf,suni,x));
  sunitrelnf=(GEN) bnfsunit(relnf,S2,PREC)[1];
  if (lg(sunitrelnf)>1)
  {
    sunitrelnf=lift(basistoalg(relnf,sunitrelnf));
    sunitrelnf=concatsp(tors,sunitrelnf);
  }
  else sunitrelnf=tors;
  aux=(GEN)relnf[8];
  if (lg(aux)>=6) aux=(GEN)aux[5];
  else
  {
    aux=buchfu(relnf);
    if(gcmp0((GEN)aux[2]))
      err(precer,"bnfisnorm, please increase precision and try again");
    aux=(GEN)aux[1];
  }
  if (lg(aux)>1)
    sunitrelnf=concatsp(aux,sunitrelnf);
  lgsunitrelnf=lg(sunitrelnf);
  M=cgetg(lgsunitrelnf+1,t_MAT);
  sunitnormnf=cgetg(lgsunitrelnf,t_VEC);
  for (i=1; i<lgsunitrelnf; i++)
  {
    sunitnormnf[i]=lnorm(gmodulcp((GEN) sunitrelnf[i],(GEN)ext[1]));
    M[i]=llift(bnfissunit(bnf,suni,(GEN) sunitnormnf[i]));
  }
  M[lgsunitrelnf]=lgetg(lg(A),t_COL);
  for (i=1; i<lg(A); i++) mael(M,lgsunitrelnf,i)=zero;
  mael(M,lgsunitrelnf,lg(mael(bnf,7,6))-1)=mael3(bnf,8,4,1);
  H=hnfall(M); Y=inverseimage(gmul(M,(GEN) H[2]),A);
  Y=gmul((GEN) H[2],Y);
  for (aux=(GEN)res[1],i=1; i<lgsunitrelnf; i++)
    aux=gmul(aux,gpuigs(gmodulcp((GEN) sunitrelnf[i],(GEN)ext[1]),
                        itos(gfloor((GEN)Y[i]))));
  x = gdiv(x,gnorm(gmodulcp(lift(aux),(GEN)ext[1])));
  if (typ(x) == t_POLMOD && (typ(x[2]) != t_POL || lgef(x[2]) == 3))
  {
    x = (GEN)x[2]; /* rational number */
    if (typ(x) == t_POL) x = (GEN)x[2];
  }
  res[1]=(long)aux;
  res[2]=(long)x;
  return gerepilecopy(ltop,res);
}

GEN
bnfisnorm(GEN bnf,GEN x,long flag,long PREC)
{
  long ltop = avma, lbot;
  GEN ext = cgetg(4,t_VEC);

  bnf = checkbnf(bnf);
  ext[1] = mael(bnf,7,1);
  ext[2] = zero;
  ext[3] = (long) bnf;
  bnf = buchinitfu(polx[MAXVARN],NULL,NULL,0); lbot = avma;
  return gerepile(ltop,lbot,rnfisnorm(bnf,ext,x,flag,PREC));
}
