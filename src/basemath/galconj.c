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
extern GEN bezout_lift_fact(GEN T, GEN Tmod, GEN p, long e);
extern GEN respm(GEN x,GEN y,GEN pm);
extern GEN ZX_disc_all(GEN,ulong);
extern GEN polratlift(GEN P, GEN mod, GEN amax, GEN bmax, GEN denom);
extern GEN znstar_hnf_elts(GEN Z, GEN H);
extern long ZX_get_prec(GEN x);

/*************************************************************************/
/**									**/
/**                           GALOIS CONJUGATES        		        **/
/**									**/
/*************************************************************************/

GEN
galoisconj(GEN nf)
{
  GEN     x, y, z;
  long i, lz, v;
  pari_sp av = avma;
  nf = checknf(nf);
  x = (GEN) nf[1];
  v = varn(x);
  if (v == 0)
    nf = gsubst(nf, 0, polx[MAXVARN]);
  else
  {
    x = dummycopy(x);
    setvarn(x, 0);
  }
  z = nfroots(nf, x);
  lz = lg(z);
  y = cgetg(lz, t_COL);
  for (i = 1; i < lz; i++)
  {
    GEN     p1 = lift((GEN) z[i]);
    setvarn(p1, v);
    y[i] = (long) p1;
  }
  return gerepileupto(av, y);
}

/* nbmax: maximum number of possible conjugates */
GEN
galoisconj2pol(GEN x, long nbmax, long prec)
{
  long i, n, v, nbauto;
  pari_sp av = avma;
  GEN     y, w, polr, p1, p2;
  n = degpol(x);
  if (n <= 0)
    return cgetg(1, t_VEC);
  if (gisirreducible(x) == gzero)
    err(redpoler, "galoisconj2pol");
  polr = roots(x, prec);
  p1 = (GEN) polr[1];
  nbauto = 1;
  prec = (long) (bit_accuracy(prec) * L2SL10 * 0.75);
  w = cgetg(n + 2, t_VEC);
  w[1] = un;
  for (i = 2; i <= n; i++)
    w[i] = lmul(p1, (GEN) w[i - 1]);
  v = varn(x);
  y = cgetg(nbmax + 1, t_COL);
  y[1] = (long) polx[v];
  for (i = 2; i <= n && nbauto < nbmax; i++)
  {
    w[n + 1] = polr[i];
    p1 = lindep2(w, prec);
    if (signe(p1[n + 1]))
    {
      setlg(p1, n + 1);
      p2 = gdiv(gtopolyrev(p1, v), negi((GEN) p1[n + 1]));
      if (gdivise(poleval(x, p2), x))
      {
	y[++nbauto] = (long) p2;
	if (DEBUGLEVEL > 1)
	  fprintferr("conjugate %ld: %Z\n", i, y[nbauto]);
      }
    }
  }
  setlg(y, 1 + nbauto);
  return gerepileupto(av, gen_sort(y, 0, cmp_pol));
}

GEN
galoisconj2(GEN nf, long nbmax, long prec)
{
  long i, j, n, r1, ru, nbauto;
  pari_sp av = avma;
  GEN     x, y, w, polr, p1, p2;
  if (typ(nf) == t_POL)
    return galoisconj2pol(nf, nbmax, prec);
  nf = checknf(nf);
  x = (GEN) nf[1];
  n = degpol(x);
  if (n <= 0)
    return cgetg(1, t_VEC);
  r1 = nf_get_r1(nf);
  p1 = (GEN) nf[6];
  prec = precision((GEN) p1[1]);
  /* accuracy in decimal digits */
  prec = (long) (bit_accuracy(prec) * L2SL10 * 0.75);
  ru = (n + r1) >> 1;
  nbauto = 1;
  polr = cgetg(n + 1, t_VEC);
  for (i = 1; i <= r1; i++)
    polr[i] = p1[i];
  for (j = i; i <= ru; i++)
  {
    polr[j++] = p1[i];
    polr[j++] = lconj((GEN) p1[i]);
  }
  p2 = gmael(nf, 5, 1);
  w = cgetg(n + 2, t_VEC);
  for (i = 1; i <= n; i++)
    w[i] = coeff(p2, 1, i);
  y = cgetg(nbmax + 1, t_COL);
  y[1] = (long) polx[varn(x)];
  for (i = 2; i <= n && nbauto < nbmax; i++)
  {
    w[n + 1] = polr[i];
    p1 = lindep2(w, prec);
    if (signe(p1[n + 1]))
    {
      setlg(p1, n + 1);
      settyp(p1, t_COL);
      p2 = gdiv(gmul((GEN) nf[7], p1), negi((GEN) p1[n + 1]));
      if (gdivise(poleval(x, p2), x))
      {
	y[++nbauto] = (long) p2;
	if (DEBUGLEVEL > 1)
	  fprintferr("conjugate %ld: %Z\n", i, y[nbauto]);
      }
    }
  }
  setlg(y, 1 + nbauto);
  return gerepileupto(av, gen_sort(y, 0, cmp_pol));
}
/*************************************************************************/
/**									**/
/**                           GALOISCONJ4             		        **/
/**									**/
/**                                                                     **/
/*************************************************************************/
/*DEBUGLEVEL:
  1: timing
  2: outline
  4: complete outline
  6: detail
  7: memory
  9: complete detail
*/

/* DP = multiple of disc(P) or NULL
 * Return a multiple of the denominator of an algebraic integer (in Q[X]/(P))
 * when expressed in terms of the power basis */
GEN
indexpartial(GEN P, GEN DP)
{
  pari_sp av = avma;
  long i, nb;
  GEN fa, p1, res = gun, dP;
  pari_timer T;

  dP = derivpol(P);
  if(DEBUGLEVEL>=5) (void)TIMER(&T);
  if(!DP) DP = ZX_disc(P);
  DP = mpabs(DP);
  if(DEBUGLEVEL>=5) msgTIMER(&T,"IndexPartial: discriminant");
  fa = auxdecomp(DP, 0);
  if(DEBUGLEVEL>=5) msgTIMER(&T,"IndexPartial: factorization");
  nb = lg(fa[1]);
  for (i = 1; i < nb; i++)
  {
    GEN p=gmael(fa,1,i);
    GEN e=gmael(fa,2,i);
    p1 = powgi(p,shifti(e,-1));
    if ( i==nb-1 )
    {
      if ( mod2(e) && !isprime(p) )
	p1 = mulii(p1,p);
    }
    else if ( cmpis(e,4)>=0 )
    {
      if(DEBUGLEVEL>=5) fprintferr("IndexPartial: factor %Z ",p1);
      p1 = mppgcd(p1, respm(P,dP,p1));
      if(DEBUGLEVEL>=5) 
      {
        fprintferr("--> %Z : ",p1);
        msgTIMER(&T,"");
      }
    }
    res=mulii(res,p1);
  }
  return gerepileupto(av,res);
}

GEN
vandermondeinverseprep(GEN L)
{
  int     i, j, n = lg(L);
  GEN     V;
  V = cgetg(n, t_VEC);
  for (i = 1; i < n; i++)
  {
    pari_sp ltop=avma;
    GEN W=cgetg(n,t_VEC);
    for (j = 1; j < n; j++)
      if (i==j)
	W[j]=un;
      else
	W[j]=lsub((GEN)L[i],(GEN)L[j]);
    V[i]=lpileupto(ltop,divide_conquer_prod(W,&gmul));
  }
  return V;
}

/* Calcule l'inverse de la matrice de van der Monde de T multiplie par den */
GEN
vandermondeinverse(GEN L, GEN T, GEN den, GEN prep)
{
  pari_sp ltop = avma;
  int     i, n = lg(L)-1;
  long    x = varn(T);
  GEN     M, P;
  if (!prep)
    prep = vandermondeinverseprep(L);
  M = cgetg(n+1, t_MAT);
  for (i = 1; i <= n; i++)
  {
    P = gdiv(gdeuc(T, gsub(polx[x], (GEN) L[i])), (GEN) prep[i]);
    M[i] = (long)pol_to_vec(P,n);
  }
  return gerepileupto(ltop, gmul(den, M));
}

/* Calcule les bornes sur les coefficients a chercher */
struct galois_borne
{
  GEN     l;
  long    valsol;
  long    valabs;
  GEN     bornesol;
  GEN     ladicsol;
  GEN     ladicabs;
  GEN     lbornesol;
};


GEN
initgaloisborne(GEN T, GEN dn, long prec, GEN *ptL, GEN *ptprep, GEN *ptdis)
{
  int i, n = degpol(T);
  GEN L, z, prep, den;
  pari_timer ti;

  if (DEBUGLEVEL>=4) (void)TIMER(&ti);
  L = roots(T, prec);
  if (DEBUGLEVEL>=4) msgTIMER(&ti,"roots");
  for (i = 1; i <= n; i++)
  {
    z = (GEN) L[i];
    if (signe(z[2])) break;
    L[i] = z[1];
  }
  if (DEBUGLEVEL>=4) (void)TIMER(&ti);
  prep = vandermondeinverseprep(L);
  if (!dn)
  {
    GEN dis, res = divide_conquer_prod(gabs(prep,prec), mpmul);
    disable_dbg(0);
    dis = ZX_disc_all(T, 1+logint(res,gdeux,NULL));
    disable_dbg(-1);
    den = indexpartial(T,dis);
    if (ptdis) *ptdis = dis;
  }
  else
  {
    if (typ(dn) != t_INT || signe(dn) <= 0)
      err(talker, "incorrect denominator in initgaloisborne: %Z", dn);
    den = dn;
  }
  if (ptprep) *ptprep = prep;
  *ptL = L; return den;
}

/* ||| M ||| with respect to || x ||_oo. Assume M square t_MAT */
GEN
matrixnorm(GEN M, long prec)
{
  long i,j, n = lg(M);
  GEN B = realzero(prec);

  for (i = 1; i < n; i++)
  {
    GEN z = gabs(gcoeff(M,i,1), prec);
    for (j = 2; j < n; j++)
      z = gadd(z, gabs(gcoeff(M,i,j), prec));
    if (gcmp(z, B) > 0) B = z;
  }
  return B;
}

/* L a t_VEC/t_COL, return ||L||_oo */
GEN
supnorm(GEN L, long prec)
{
  long i, n = lg(L);
  GEN z, B;

  if (n == 1) return realzero(prec);
  B = gabs((GEN)L[1], prec);
  for (i = 2; i < n; i++)
  {
    z = gabs((GEN)L[i], prec);
    if (gcmp(z, B) > 0) B = z;
  }
  return B;
}

GEN
galoisborne(GEN T, GEN dn, struct galois_borne *gb, long ppp)
{
  pari_sp ltop = avma, av2;
  GEN     borne, borneroots, borneabs;
  int     n;
  GEN     L, M, prep, den;
  long    prec;
  pari_timer ti;

  prec = ZX_get_prec(T);
  den = initgaloisborne(T,dn,prec, &L,&prep,NULL);
  if (!dn) den = gclone(den);
  if (DEBUGLEVEL>=4) TIMERstart(&ti);
  M = vandermondeinverse(L, gmul(T, realun(prec)), den, prep);
  if (DEBUGLEVEL>=4) msgTIMER(&ti,"vandermondeinverse");
  borne = matrixnorm(M, prec);
  borneroots = supnorm(L, prec);
  n = degpol(T);
  borneabs = addsr(1, gmulsg(n, gpowgs(borneroots, n/ppp)));
  /*if (ppp == 1)
    borneabs = addsr(1, gmulsg(n, gpowgs(borneabs, 2)));*/
  borneroots = addsr(1, gmul(borne, borneroots));
  av2 = avma;
  /*We use d-1 test, so we must overlift to 2^BITS_IN_LONG*/
  gb->valsol = logint(gmul2n(borneroots,2+BITS_IN_LONG), gb->l,NULL);
  gb->valabs = logint(gmul2n(borneabs,2), gb->l,NULL);
  gb->valabs = max(gb->valsol, gb->valabs);
  if (DEBUGLEVEL >= 4)
    fprintferr("GaloisConj:val1=%ld val2=%ld\n", gb->valsol, gb->valabs);
  avma = av2;
  gb->bornesol = gerepileupto(ltop, ceil_safe(mulrs(borneroots,2)));
  if (DEBUGLEVEL >= 9)
    fprintferr("GaloisConj: Bound %Z\n",borneroots);
  gb->ladicsol = gpowgs(gb->l, gb->valsol);
  gb->ladicabs = gpowgs(gb->l, gb->valabs);
  gb->lbornesol = subii(gb->ladicsol,gb->bornesol);
  if (!dn) { dn = icopy(den); gunclone(den); }
  return dn;
}

struct galois_lift
{
  GEN     T;
  GEN     den;
  GEN     p;
  GEN     L;
  GEN     Lden;
  long    e;
  GEN     Q;
  GEN     TQ;
  struct galois_borne *gb;
};
/* Initialise la structure galois_lift */
GEN makeLden(GEN L,GEN den, struct galois_borne *gb)
{
  pari_sp ltop=avma;
  long i,l=lg(L);
  GEN Lden;
  Lden=cgetg(l,t_VEC);
  for (i=1;i<l;i++)
    Lden[i]=lmulii((GEN)L[i],den);
  for (i=1;i<l;i++)
    Lden[i]=lmodii((GEN)Lden[i],gb->ladicsol);
  return gerepileupto(ltop,Lden);
}
void
initlift(GEN T, GEN den, GEN p, GEN L, GEN Lden, struct galois_borne *gb, struct galois_lift *gl)
{
  pari_sp ltop, lbot;
  gl->gb=gb;
  gl->T = T;
  gl->den = den;
  gl->p = p;
  gl->L = L;
  gl->Lden = Lden;
  ltop = avma;
  gl->e = logint(gmul2n(gb->bornesol, 2+BITS_IN_LONG),p,NULL);
  gl->e = max(2,gl->e);
  lbot = avma;
  gl->Q = gpowgs(p, gl->e);
  gl->Q = gerepile(ltop, lbot, gl->Q);
  gl->TQ = FpX_red(T,gl->Q);
}

/*
 * Verifie que f est une solution presque surement et calcule sa permutation
 */
static int
poltopermtest(GEN f, struct galois_lift *gl, GEN pf)
{
  pari_sp ltop;
  GEN     fx, fp;
  long     i, j,ll;
  for (i = 2; i< lgef(f); i++)
    if (cmpii((GEN)f[i],gl->gb->bornesol)>0 
	&& cmpii((GEN)f[i],gl->gb->lbornesol)<0)
    {
      if (DEBUGLEVEL>=4)
	fprintferr("GaloisConj: Solution too large, discard it.\n");
      if (DEBUGLEVEL>=8)
	fprintferr("f=%Z\n borne=%Z\n l-borne=%Z\n",f,gl->gb->bornesol,gl->gb->lbornesol);
      return 0;
    }
  ll=lg(gl->L);
  fp = cgetg(ll, t_VECSMALL);
  ltop = avma;
  for (i = 1; i < ll; i++)
    fp[i] = 1;
  for (i = 1; i < ll; i++)
  {
    fx = FpX_eval(f, (GEN) gl->L[i],gl->gb->ladicsol);
    for (j = 1; j < ll; j++)
    {
      if (fp[j] && egalii(fx, (GEN) gl->Lden[j]))
      {
	pf[i] = j;
	fp[j] = 0;
	break;
      }
    }
    if (j == ll)
      return 0;
    avma = ltop;
  }
  return 1;
}

/*
 * Soit P un polynome de \ZZ[X] , p un nombre premier , S\in\FF_p[X]/(Q) tel
 * que P(S)=0 [p,Q] Relever S en S_0 tel que P(S_0)=0 [p^e,Q]
 * Unclean stack.
 */
static long monoratlift(GEN S, GEN q, GEN qm1old,struct galois_lift *gl, GEN frob)
{
  pari_sp ltop=avma;
  GEN tlift = polratlift(S,q,qm1old,qm1old,gl->den);
  if (tlift)
  {
    if(DEBUGLEVEL>=4)
      fprintferr("MonomorphismLift: trying early solution %Z\n",tlift);
    /*Rationals coefficients*/
    tlift=lift(gmul(tlift,gmodulcp(gl->den,gl->gb->ladicsol)));
    if (poltopermtest(tlift, gl, frob))
    {
      if(DEBUGLEVEL>=4)
	fprintferr("MonomorphismLift: true early solution.\n");
      avma=ltop;
      return 1;
    }
    if(DEBUGLEVEL>=4)
      fprintferr("MonomorphismLift: false early solution.\n");
  }
  avma=ltop;
  return 0;
}
  GEN
monomorphismratlift(GEN P, GEN S, struct galois_lift *gl, GEN frob)
{
  pari_sp ltop, lbot;
  long rt;
  GEN     Q=gl->T, p=gl->p;
  long    e=gl->e, level=1;
  long    x;
  GEN     q, qold, qm1, qm1old;
  GEN     W, Pr, Qr, Sr, Wr = gzero, Prold, Qrold, Spow;
  long    i,nb,mask;
  GEN    *gptr[2];
  if (DEBUGLEVEL == 1) (void)timer2();
  x = varn(P);
  rt = brent_kung_optpow(degpol(Q),1);
  q = p; qm1 = gun; /*during the run, we have p*qm1=q*/
  nb=hensel_lift_accel(e, &mask);
  Pr = FpX_red(P,q);
  Qr = (P==Q)?Pr:FpX_red(Q, q);/*A little speed up for automorphismlift*/
  W=FpX_FpXQ_compo(deriv(Pr, x),S,Qr,q);
  W=FpXQ_inv(W,Qr,q);
  qold = p; qm1old=gun;
  Prold = Pr;
  Qrold = Qr;
  gptr[0] = &S;
  gptr[1] = &Wr;
  for (i=0; i<nb;i++)
  {
    if (DEBUGLEVEL>=2)
    {
      level=(level<<1)-((mask>>i)&1);
      (void)timer2();
    }
    qm1 = (mask&(1<<i))?sqri(qm1):mulii(qm1, q);
    q   =  mulii(qm1, p);
    Pr = FpX_red(P, q);
    Qr = (P==Q)?Pr:FpX_red(Q, q);/*A little speed up for automorphismlift*/
    ltop = avma;
    Sr = S;
    Spow = FpXQ_powers(Sr, rt, Qr, q);

    if (i)
    {
      W = FpXQ_mul(Wr, FpX_FpXQV_compo(deriv(Pr,-1),FpXV_red(Spow,qold),Qrold,qold), Qrold, qold);
      W = FpX_neg(W, qold);
      W = FpX_Fp_add(W, gdeux, qold);
      W = FpXQ_mul(Wr, W, Qrold, qold);
    }
    Wr = W;
    S = FpXQ_mul(Wr, FpX_FpXQV_compo(Pr, Spow, Qr, q),Qr,q);
    S = FpX_sub(Sr, S, NULL);
    lbot = avma;
    Wr = gcopy(Wr);
    S = FpX_red(S, q);
    gerepilemanysp(ltop, lbot, gptr, 2);
    if (i && i<nb-1 && frob && monoratlift(S,q,qm1old,gl,frob))
      return NULL;
    qold = q; qm1old=qm1; Prold = Pr; Qrold = Qr;
    if (DEBUGLEVEL >= 2)
      msgtimer("MonomorphismLift: lift to prec %d",level);
  }
  if (DEBUGLEVEL == 1)
    msgtimer("monomorphismlift()");
  return S;
}
/*
 * Soit T un polynome de \ZZ[X] , p un nombre premier , S\in\FF_p[X]/(T) tel
 * que T(S)=0 [p,T] Relever S en S_0 tel que T(S_0)=0 [T,p^e]
 * Unclean stack.
 */
GEN
automorphismlift(GEN S, struct galois_lift *gl, GEN frob)
{
  return  monomorphismratlift(gl->T, S, gl, frob);
}
GEN
monomorphismlift(GEN P, GEN S, GEN Q, GEN p, long e)
{
  struct galois_lift gl;
  gl.T=Q;
  gl.p=p;
  gl.e=e;
  return monomorphismratlift(P,S,&gl,NULL);
}

struct galois_testlift
{
  long    n;
  long    f;
  long    g;
  GEN     bezoutcoeff;
  GEN     pauto;
  GEN     C;
  GEN     Cd;
};
static GEN
galoisdolift(struct galois_lift *gl, GEN frob)
{
  pari_sp ltop=avma;
  long v = varn(gl->T);
  GEN Tp = FpX_red(gl->T, gl->p);
  GEN S = FpXQ_pow(polx[v],gl->p, Tp,gl->p);
  GEN plift = automorphismlift(S, gl, frob);
  return gerepileupto(ltop,plift);
}

static void
inittestlift( GEN plift, GEN Tmod, struct galois_lift *gl, 
    struct galois_testlift *gt)
{
  long v = varn(gl->T);
  gt->n = lg(gl->L) - 1;
  gt->g = lg(Tmod) - 1;
  gt->f = gt->n / gt->g;
  gt->bezoutcoeff = bezout_lift_fact(gl->T, Tmod, gl->p, gl->e);
  gt->pauto = cgetg(gt->f + 1, t_VEC);
  gt->pauto[1] = (long) polx[v];
  gt->pauto[2] = (long) gcopy(plift);
  if (gt->f > 2)
  {
    pari_sp ltop=avma;
    int i;
    long nautpow=brent_kung_optpow(gt->n-1,gt->f-2);
    GEN autpow;
    if (DEBUGLEVEL >= 1) (void)timer2();
    autpow = FpXQ_powers(plift,nautpow,gl->TQ,gl->Q);
    for (i = 3; i <= gt->f; i++)
      gt->pauto[i] = (long) FpX_FpXQV_compo((GEN)gt->pauto[i-1],autpow,gl->TQ,gl->Q);
    /*Somewhat paranoid with memory, but this function use a lot of stack.*/
    gt->pauto=gerepileupto(ltop, gt->pauto);
    if (DEBUGLEVEL >= 1) msgtimer("frobenius power");
  }
}

long intheadlong(GEN x, GEN mod)
{
  pari_sp ltop=avma;
  GEN r;
  int s;
  long res;
  r=divii(shifti(x,BITS_IN_LONG),mod);
  s=signe(r);
  res=s?s>0?r[2]:-r[2]:0;
  avma=ltop;
  return res;
}

GEN matheadlong(GEN W, GEN mod)
{
  long i,j;
  GEN V=cgetg(lg(W),t_VEC);
  for(i=1;i<lg(W);i++)
  {
    V[i]=lgetg(lg(W[i]),t_VECSMALL);
    for(j=1;j<lg(W[i]);j++)
      mael(V,i,j)=intheadlong(gmael(W,i,j),mod);
  }
  return V;
}

long polheadlong(GEN P, long n, GEN mod)
{
  return (lgef(P)>n+2)?intheadlong((GEN)P[n+2],mod):0;
}
/*
 * 
 */
long
frobeniusliftall(GEN sg, long el, GEN *psi, struct galois_lift *gl,
		 struct galois_testlift *gt, GEN frob)
{
  pari_sp av, ltop2, ltop = avma;
  long    d, z, m, c, n, ord;
  int     i, j, k;
  GEN     pf, u, v;
  GEN     C, Cd, SG, cache;
  long    Z, c_idx=gt->g-1;
  long    stop=0,hop=0;
  GEN     NN,NQ,NR;
  long    N1,N2,R1,Ni;
  m = gt->g;
  ord = gt->f;
  n = lg(gl->L) - 1;
  c = lg(sg) - 1;
  d = m / c;
  pf = cgetg(m, t_VECSMALL);
  *psi = pf;
  ltop2 = avma;
  NN = gdiv(mpfact(m), gmul(stoi(c), gpowgs(mpfact(d), c)));
  if (DEBUGLEVEL >= 4)
    fprintferr("GaloisConj:I will try %Z permutations\n", NN);
  N1=10000000;
  NQ=dvmdis(NN,N1,&NR);
  if (cmpis(NQ,1000000000)>0)
  {
    err(warner,"Combinatorics too hard : would need %Z tests!\n"
	"I will skip it,but it may induce galoisinit to loop",NN);
    avma = ltop;
    *psi = NULL;
    return 0;
  }
  N2=itos(NQ); R1=itos(NR); if(!N2) N1=R1;
  if (DEBUGLEVEL>=4)
  {
    stop=N1/20;
    (void)timer2();
  }
  avma = ltop2;
  C=gt->C;
  Cd=gt->Cd;
  v = FpX_Fp_mul(FpXQ_mul((GEN)gt->pauto[1+el%ord], (GEN)
	gt->bezoutcoeff[m],gl->TQ,gl->Q),gl->den,gl->Q);
  SG=cgetg(lg(sg),t_VECSMALL);
  for(i=1;i<lg(SG);i++)
    SG[i]=(el*sg[i])%ord + 1;
  cache=cgetg(m+1,t_VECSMALL);
  cache[m]=polheadlong(v,1,gl->Q);
  Z=polheadlong(v,2,gl->Q);
  for (i = 1; i < m; i++)
    pf[i] = 1 + i / d;
  av = avma;
  for (Ni = 0, i = 0; ;i++)
  {
    for (j = c_idx ; j > 0; j--)
    {
      long h;
      h=SG[pf[j]];
      if (!mael(C,h,j))
      {
	pari_sp av3=avma;
	GEN r;
	r=FpX_Fp_mul(FpXQ_mul((GEN) gt->pauto[h], 
	      (GEN) gt->bezoutcoeff[j],gl->TQ,gl->Q),gl->den,gl->Q);
	mael(C,h,j)  = lclone(r);
	mael(Cd,h,j) = polheadlong(r,1,gl->Q);
	avma=av3;
      }
      cache[j]=cache[j+1]+mael(Cd,h,j);
    }
    if (labs(cache[1])<=n )
    {
      long ZZ=Z;
      for (j = 1; j < m; j++)
	ZZ += polheadlong(gmael(C,SG[pf[j]],j),2,gl->Q);
      if (labs(ZZ)<=n )
      {
	u = v;
	for (j = 1; j < m; j++)
	  u = FpX_add(u, gmael(C,SG[pf[j]],j),NULL);
	u = FpX_center(FpX_red(u, gl->Q), gl->Q);
	if (poltopermtest(u, gl, frob))
	{
	  if (DEBUGLEVEL >= 4 )
	  {
	    msgtimer("");
	    fprintferr("GaloisConj: %d hops on %Z tests\n",hop,addis(mulss(Ni,N1),i));
	  }
	  avma = ltop2;
	  return 1;
	}
	else if (DEBUGLEVEL >= 4 )
	  fprintferr("M");
      }
      else hop++;
    }
    if (DEBUGLEVEL >= 4 && i==stop)
    {
      stop+=N1/20;
      msgtimer("GaloisConj:Testing %Z", addis(mulss(Ni,N1),i));
    }
    avma = av;
    if (i == N1 - 1)
    {
      if (Ni==N2-1)
	N1=R1;
      if (Ni==N2)
	break;
      Ni++;
      i=0;
      if (DEBUGLEVEL>=4)
      {
	stop=N1/20;
	(void)timer2();
      }
    }
    for (j = 2; j < m && pf[j - 1] >= pf[j]; j++);
    for (k = 1; k < j - k && pf[k] != pf[j - k]; k++)
    {
      z = pf[k];
      pf[k] = pf[j - k];
      pf[j - k] = z;
    }
    for (k = j - 1; pf[k] >= pf[j]; k--);
    z = pf[j];
    pf[j] = pf[k];
    pf[k] = z;
    c_idx=j;
  }
  if (DEBUGLEVEL>=4)
    fprintferr("GaloisConj: not found, %d hops \n",hop);
  avma = ltop;
  *psi = NULL;
  return 0;
}

/*
 * alloue une ardoise pour n entiers de longueurs pour les test de
 * permutation
 */
GEN
alloue_ardoise(long n, long s)
{
  GEN     ar;
  long    i;
  ar = cgetg(n + 1, t_VEC);
  for (i = 1; i <= n; i++)
    ar[i] = lgetg(s, t_INT);
  return ar;
}

/* structure containing all data for permutation test:
 * 
 * ordre :ordre des tests pour verifie_test ordre[lg(ordre)]: numero du test
 * principal borne : borne sur les coefficients a trouver ladic: modulo
 * l-adique des racines lborne:ladic-borne TM:vecteur des ligne de M
 * PV:vecteur des clones des matrices de test (Vmatrix) (ou NULL si non
 * calcule) L,M comme d'habitude (voir plus bas)
 */
struct galois_test
{
  GEN     ordre;
  GEN     borne, lborne, ladic;
  GEN     PV, TM;
  GEN     L, M;
};
/* Calcule la matrice de tests correspondant a la n-ieme ligne de V */
static GEN
Vmatrix(long n, struct galois_test *td)
{
  pari_sp lbot, ltop = avma;
  GEN     V;
  long    i;
  V = cgetg(lg(td->L), t_VEC);
  for (i = 1; i < lg(V); i++)
    V[i] = mael(td->M,i,n);
  V = gmul(td->L, V);
  lbot = avma;
  V = gmod(V, td->ladic);
  return gerepile(ltop, lbot, V);
}

/*
 * Initialise la structure galois_test
 */
static void
inittest(GEN L, GEN M, GEN borne, GEN ladic, struct galois_test *td)
{
  pari_sp ltop;
  long    i;
  int     n = lg(L) - 1;
  if (DEBUGLEVEL >= 8)
    fprintferr("GaloisConj:Entree Init Test\n");
  td->ordre = cgetg(n + 1, t_VECSMALL);
  for (i = 1; i <= n - 2; i++)
    td->ordre[i] = i + 2;
  for (; i <= n; i++)
    td->ordre[i] = i - n + 2;
  td->borne = borne;ltop = avma;
  td->lborne = subii(ladic, borne);
  td->ladic = ladic;
  td->L = L;
  td->M = M;
  td->PV = cgetg(n + 1, t_VECSMALL);	/* peut-etre t_VEC est correct ici */
  for (i = 1; i <= n; i++)
    td->PV[i] = 0;
  ltop = avma;
  td->PV[td->ordre[n]] = (long) gclone(Vmatrix(td->ordre[n], td));
  avma = ltop;
  td->TM = gtrans_i(M);
  settyp(td->TM, t_VEC);
  for (i = 1; i < lg(td->TM); i++)
    settyp(td->TM[i], t_VEC);
  if (DEBUGLEVEL >= 8)
    fprintferr("GaloisConj:Sortie Init Test\n");
}

/* liberer les clones de la structure galois_test */
static void
freetest(struct galois_test *td)
{
  int     i;
  for (i = 1; i < lg(td->PV); i++)
    if (td->PV[i])
    {
      gunclone((GEN) td->PV[i]);
      td->PV[i] = 0;
    }
}

/*
 * Test si le nombre padique P est proche d'un entier inferieur a td->borne
 * en valeur absolue.
 */
static long
padicisint(GEN P, struct galois_test *td)
{
  long    r;
  pari_sp ltop = avma;
  GEN     U;
  /*if (typ(P) != t_INT)    err(typeer, "padicisint");*/
  U = modii(P, td->ladic);
  r = gcmp(U, (GEN) td->borne) <= 0 || gcmp(U, (GEN) td->lborne) >= 0;
  avma = ltop;
  return r;
}

/*
 * Verifie si pf est une vrai solution et non pas un "hop"
 */
static long
verifietest(GEN pf, struct galois_test *td)
{
  pari_sp av = avma;
  GEN     P, V;
  int     i, j;
  int     n = lg(td->L) - 1;
  if (DEBUGLEVEL >= 8)
    fprintferr("GaloisConj:Entree Verifie Test\n");
  P = perm_mul(td->L, pf);
  for (i = 1; i < n; i++)
  {
    long    ord;
    GEN     PW;
    ord = td->ordre[i];
    PW = (GEN) td->PV[ord];
    if (PW)
    {
      V = ((GEN **) PW)[1][pf[1]];
      for (j = 2; j <= n; j++)
	V = addii(V, ((GEN **) PW)[j][pf[j]]);
    }
    else
      V = centermod(gmul((GEN) td->TM[ord], P),td->ladic);
    if (!padicisint(V, td))
      break;
  }
  if (i == n)
  {
    if (DEBUGLEVEL >= 8)
      fprintferr("GaloisConj:Sortie Verifie Test:1\n");
    avma = av;
    return 1;
  }
  if (!td->PV[td->ordre[i]])
  {
    td->PV[td->ordre[i]] = (long) gclone(Vmatrix(td->ordre[i], td));
    if (DEBUGLEVEL >= 4)
      fprintferr("M");
  }
  if (DEBUGLEVEL >= 4)
    fprintferr("%d.", i);
  if (i > 1)
  {
    long    z;
    z = td->ordre[i];
    for (j = i; j > 1; j--)
      td->ordre[j] = td->ordre[j - 1];
    td->ordre[1] = z;
    if (DEBUGLEVEL >= 8)
      fprintferr("%Z", td->ordre);
  }
  if (DEBUGLEVEL >= 8)
    fprintferr("GaloisConj:Sortie Verifie Test:0\n");
  avma = av;
  return 0;
}
/*Compute a*b/c when a*b will overflow*/
static long muldiv(long a,long b,long c)
{
  return (long)((double)a*(double)b/c);
}

/*
 * F est la decomposition en cycle de sigma, B est la decomposition en cycle
 * de cl(tau) Teste toutes les permutations pf pouvant correspondre a tau tel
 * que : tau*sigma*tau^-1=sigma^s et tau^d=sigma^t  ou d est l'ordre de
 * cl(tau) --------- x: vecteur des choix y: vecteur des mises a jour G:
 * vecteur d'acces a F linéaire
 */
GEN
testpermutation(GEN F, GEN B, long s, long t, long cut,
		struct galois_test *td)
{
  pari_sp av, avm = avma;
  int     a, b, c, d, n;
  GEN     pf, x, ar, y, *G;
  int     p1, p2, p3, p4, p5, p6;
  long 	  l1, l2, N1, N2, R1;
  long    i, j, cx, hop = 0, start = 0;
  GEN     W, NN, NQ, NR;
  long    V;
  if (DEBUGLEVEL >= 1) (void)timer2();
  a = lg(F) - 1;
  b = lg(F[1]) - 1;
  c = lg(B) - 1;
  d = lg(B[1]) - 1;
  n = a * b;
  s = (b + s) % b;
  pf = cgetg(n + 1, t_VECSMALL);
  av = avma;
  ar = cgetg(a + 1, t_VECSMALL);
  x = cgetg(a + 1, t_VECSMALL);
  y = cgetg(a + 1, t_VECSMALL);
  G = (GEN *) cgetg(a + 1, t_VECSMALL);	/* Don't worry */
  W = matheadlong((GEN) td->PV[td->ordre[n]],td->ladic);
  for (cx = 1, i = 1, j = 1; cx <= a; cx++, i++)
  {
    x[cx] = (i != d) ? 0 : t;
    y[cx] = 1;
    G[cx] = (GEN) F[((long **) B)[j][i]];	/* Be happy */
    if (i == d)
    {
      i = 0;
      j++;
    }
  }				/* Be happy now! */
  NN = divis(gpowgs(stoi(b), c * (d - 1)),cut);
  if (DEBUGLEVEL >= 4)
    fprintferr("GaloisConj:I will try %Z permutations\n", NN);
  N1=100000;
  NQ=dvmdis(NN,N1,&NR);
  if (cmpis(NQ,1000000000)>0)
  {
    avma=avm;
    err(warner,"Combinatorics too hard : would need %Z tests!\n I'll skip it but you will get a partial result...",NN);
    return perm_identity(n);
  }
  N2=itos(NQ); R1=itos(NR);
  for (l2 = 0; l2 <= N2; l2++)
  {
    long nbiter = (l2<N2) ? N1: R1;
    if (DEBUGLEVEL >= 2 && N2)
      fprintferr("%d%% ", muldiv(l2,100,N2));
    for (l1 = 0; l1 < nbiter; l1++)
    {
      if (start)
      {
	for (i = 1, j = d; i < a;)
	{
	  y[i] = 1;
	  if ((++(x[i])) != b)
	    break;
	  x[i++] = 0;
	  if (i == j)
	  {
	    y[i++] = 1;
	    j += d;
	  }
	}
	y[i + 1] = 1;
      }
      else start=1;
      for (p1 = 1, p5 = d; p1 <= a; p1++, p5++)
	if (y[p1])
	{
	  if (p5 == d)
	  {
	    p5 = 0;
	    p4 = 0;
	  }
	  else
	    p4 = x[p1 - 1];
	  if (p5 == d - 1)
	    p6 = p1 + 1 - d;
	  else
	    p6 = p1 + 1;
	  y[p1] = 0;
	  V = 0;
	  for (p2 = 1 + p4, p3 = 1 + x[p1]; p2 <= b; p2++)
	  {
	    V += mael(W,G[p6][p3],G[p1][p2]);
	    p3 += s;
	    if (p3 > b)
	      p3 -= b;
	  }
	  p3 = 1 + x[p1] - s;
	  if (p3 <= 0)
	    p3 += b;
	  for (p2 = p4; p2 >= 1; p2--)
	  {
	    V += mael(W,G[p6][p3],G[p1][p2]);
	    p3 -= s;
	    if (p3 <= 0)
	      p3 += b;
	  }
	  ar[p1]=V;
	}
      V = 0;
      for (p1 = 1; p1 <= a; p1++)
	V += ar[p1];
      if (labs(V)<=n)
      {
	for (p1 = 1, p5 = d; p1 <= a; p1++, p5++)
	{
	  if (p5 == d)
	  {
	    p5 = 0;
	    p4 = 0;
	  }
	  else
	    p4 = x[p1 - 1];
	  if (p5 == d - 1)
	    p6 = p1 + 1 - d;
	  else
	    p6 = p1 + 1;
	  for (p2 = 1 + p4, p3 = 1 + x[p1]; p2 <= b; p2++)
	  {
	    pf[G[p1][p2]] = G[p6][p3];
	    p3 += s;
	    if (p3 > b)
	      p3 -= b;
	  }
	  p3 = 1 + x[p1] - s;
	  if (p3 <= 0)
	    p3 += b;
	  for (p2 = p4; p2 >= 1; p2--)
	  {
	    pf[G[p1][p2]] = G[p6][p3];
	    p3 -= s;
	    if (p3 <= 0)
	      p3 += b;
	  }
	}
	if (verifietest(pf, td))
	{
	  if (DEBUGLEVEL >= 1)
	  {
	    GEN nb=addis(mulss(l2,N1),l1);
	    msgtimer("testpermutation(%Z)", nb);
	    if (DEBUGLEVEL >= 2 && hop)
	      fprintferr("GaloisConj:%d hop sur %Z iterations\n", hop, nb);
	  }
	  avma = av;
	  return pf;
	}
	else
	  hop++;
      }
    }
  }
  if (DEBUGLEVEL >= 1)
  {
    msgtimer("testpermutation(%Z)", NN);
    if (DEBUGLEVEL >= 2 && hop)
      fprintferr("GaloisConj:%d hop sur %Z iterations\n", hop, NN);
  }
  avma = avm;
  return gzero;
}
int pari_compare_lg(GEN x, GEN y)
{
  return lg(x)-lg(y);
}

/*
 * Calcule la liste des sous groupes de (\ZZ/m\ZZ)^* d'ordre divisant p et
 * retourne la liste de leurs elements
 */
GEN
listsousgroupes(long m, long p)
{
  pari_sp ltop = avma;
  GEN     zn, zns, lss, sg, res;
  int     k, card, i, phi;
  if (m == 2)
  {
    res = cgetg(2, t_VEC);
    sg = cgetg(2, t_VECSMALL);
    res[1] = (long) sg;
    sg[1] = 1;
    return res;
  }
  zn = znstar(stoi(m));
  phi = itos((GEN) zn[1]);
  zns = znstar_small(zn);
  lss = subgrouplist((GEN) zn[2], NULL);
  res = cgetg(lg(lss), t_VEC);
  for (k = 1, i = lg(lss) - 1; i >= 1; i--)
  {
    pari_sp av;
    av = avma;
    card = phi / itos(det((GEN) lss[i]));
    avma = av;
    if (p % card == 0)
      res[k++] = (long) znstar_hnf_elts(zns,(GEN)lss[i]);
  }
  setlg(res,k);
  res=gen_sort(res,0,&pari_compare_lg);
  return gerepileupto(ltop,res);
}

GEN
fixedfieldpolsigma(GEN sigma, GEN p, GEN Tp, GEN sym, GEN deg, long g)
{
  pari_sp ltop=avma;
  long i, j, npows;
  GEN  s, f, pows;
  sigma=lift(gmul(sigma,gmodulsg(1,p)));
  f=polx[varn(sigma)];
  s=zeropol(varn(sigma));
  for(j=1;j<lg(sym);j++)
    if(sym[j])
    {
      s=FpX_add(s,FpX_Fp_mul(FpXQ_pow(f,stoi(deg[j]),Tp,p),stoi(sym[j]),p),p);
    }
  npows = brent_kung_optpow(lgef(Tp)-4,g-1);
  pows  = FpXQ_powers(sigma,npows,Tp,p);
  for(i=2; i<=g;i++)
  {
    f=FpX_FpXQV_compo(f,pows,Tp,p);
    for(j=1;j<lg(sym);j++)
      if(sym[j])
      {
	s=FpX_add(s,FpX_Fp_mul(FpXQ_pow(f,stoi(deg[j]),Tp,p),stoi(sym[j]),p),p);
      }
  }
  return gerepileupto(ltop, s);
}

GEN
fixedfieldfactmod(GEN Sp, GEN p, GEN Tmod)
{
  long i;
  long l=lg(Tmod);
  GEN F=cgetg(l,t_VEC);
  for(i=1;i<l;i++)
    F[i]=(long)FpXQ_minpoly(FpX_res(Sp,(GEN) Tmod[i],p), (GEN) Tmod[i],p);
  return F;
}

GEN
fixedfieldnewtonsumaut(GEN sigma, GEN p, GEN Tp, GEN e, long g)
{
  pari_sp ltop=avma;
  long i;
  GEN s,f,V;
  long rt;
  sigma=lift(gmul(sigma,gmodulsg(1,p)));
  f=polx[varn(sigma)];
  rt=brent_kung_optpow(lgef(Tp)-4,g-1);
  V=FpXQ_powers(sigma,rt,Tp,p);
  s=FpXQ_pow(f,e,Tp,p);
  for(i=2; i<=g;i++)
  {
    f=FpX_FpXQV_compo(f,V,Tp,p);
    s=FpX_add(s,FpXQ_pow(f,e,Tp,p),p);
  }
  return gerepileupto(ltop, s);
}

GEN
fixedfieldnewtonsum(GEN O, GEN L, GEN mod, GEN e)
{
  long f,g;
  long i,j;
  GEN PL;
  f=lg(O)-1;
  g=lg(O[1])-1;
  PL=cgetg(lg(O), t_COL);
  for(i=1; i<=f; i++)
  {
    pari_sp ltop=avma;
    GEN s=gzero;
    for(j=1; j<=g; j++)
      s=addii(s,powmodulo((GEN)L[mael(O,i,j)],e,mod));
    PL[i]=lpileupto(ltop,modii(s,mod));
  }
  return PL;
}

GEN
fixedfieldpol(GEN O, GEN L, GEN mod, GEN sym, GEN deg)
{
  pari_sp ltop=avma;
  long i;
  GEN S=gzero;
  for(i=1;i<lg(sym);i++)
    if (sym[i])
      S=gadd(S,gmulsg(sym[i],fixedfieldnewtonsum(O, L, mod, stoi(deg[i]))));
  S=FpV_red(S,mod);
  return gerepileupto(ltop, S);
}

static long 
fixedfieldtests(GEN LN, long n)
{
  long i,j,k;
  for (i=1;i<lg(LN[1]);i++)
    for(j=i+1;j<lg(LN[1]);j++)
    {
      for(k=1;k<=n;k++)
	if (cmpii(gmael(LN,k,j),gmael(LN,k,i)))
	  break;
      if (k>n)
	return 0;
    }
  return 1;
}

static long 
fixedfieldtest(GEN V)
{
  long i,j;
  for (i=1;i<lg(V);i++)
    for(j=i+1;j<lg(V);j++)
      if (!cmpii((GEN)V[i],(GEN)V[j]))
	return 0;
  return 1;
}

void
debug_surmer(char *s,GEN S, long n)
{
  long l=lg(S);
  setlg(S,n+1);
  fprintferr(s,S);
  setlg(S,l);
}

/*We try hard to find a polynomial R squarefree mod p.
Unfortunately, it may be too much asked.
A less bugprone way would be to only ask it to be squarefree mod p^e
with e not too big. Most of the code is here, but I lack the theoretical
knowledge to make it to work smoothly.B.A.
*/ 
static GEN
fixedfieldsurmer(GEN O, GEN L, GEN mod, GEN l, GEN p, GEN S, GEN deg, long v, GEN LN,long n)
{
  long i;
  GEN V;
  V=(GEN)LN[n];
  for (i=1;i<lg(S);i++)
    S[i]=0;
  S[n]=1;
  for (i=0;i<2*n-1;i++)
  {
    long k;
    if (fixedfieldtest(V))
    {
      pari_sp av=avma;
      GEN s=fixedfieldpol(O,L,mod,S,deg);
      GEN P=FpV_roots_to_pol(s,mod,v);
      P=FpX_center(P,mod);
      if (p==gun || FpX_is_squarefree(P,p))
      {
	GEN V;
	if (DEBUGLEVEL>=4) 
	  debug_surmer("FixedField: Sym: %Z\n",S,n);
	V=cgetg(3,t_VEC);
	V[1]=lcopy(s);/*do not swap*/
	V[2]=lcopy(P);
	return V;
      }
      else
      {
	if (DEBUGLEVEL>=6)
	  debug_surmer("FixedField: bad mod: %Z\n",S,n);
	avma=av;
      }
    }
    else 
    {
      if (DEBUGLEVEL>=6)
        debug_surmer("FixedField: Tested: %Z\n",S,n);
    }
    k=1+(i%n);
    S[k]++;
    V=FpV_red(gadd(V,(GEN)LN[k]),l);
  }
  return NULL;
}

GEN
fixedfieldsympol(GEN O, GEN L, GEN mod, GEN l, GEN p, GEN S, GEN deg, long v)
{
  pari_sp ltop=avma;
  GEN V=NULL;
  GEN LN=cgetg(lg(L),t_VEC);
  GEN Ll=FpV_red(L,l);
  long n,i;
  for(i=1;i<lg(deg);i++)
    deg[i]=0;
  for(n=1,i=1;i<lg(L);i++)
  {
    long j;
    LN[n]=(long)fixedfieldnewtonsum(O,Ll,l,stoi(i));
    for(j=2;j<lg(LN[n]);j++)
      if(cmpii(gmael(LN,n,j),gmael(LN,n,1)))
	break;
    if(j==lg(LN[n]) && j>2)
      continue;
    if (DEBUGLEVEL>=6) fprintferr("FixedField: LN[%d]=%Z\n",n,LN[n]);
    deg[n]=i;
    if (fixedfieldtests(LN,n))
    {
      V=fixedfieldsurmer(O,L,mod,l,p,S,deg,v,LN,n);
      if (V)
	break;
    }
    n++;
  }
  if (DEBUGLEVEL>=4) 
  {
    long l=lg(deg);
    setlg(deg,n);
    fprintferr("FixedField: Computed degrees: %Z\n",deg);
    setlg(deg,l);
  }
  if (!V)
    err(talker, "prime too small in fixedfield");
  return gerepileupto(ltop,V);
}
/*
 * Calcule l'inclusion de R dans T i.e. S telque T|R\compo S
 * Ne recopie pas PL.
 */
GEN
fixedfieldinclusion(GEN O, GEN PL)
{
  GEN     S;
  int     i, j;
  S = cgetg((lg(O) - 1) * (lg(O[1]) - 1) + 1, t_COL);
  for (i = 1; i < lg(O); i++)
    for (j = 1; j < lg(O[i]); j++)
      S[((GEN *) O)[i][j]] = PL[i];
  return S;
}

/*Usually mod is bigger than than den so there is no need to reduce it.*/
GEN
vandermondeinversemod(GEN L, GEN T, GEN den, GEN mod)
{
  pari_sp av;
  int     i, j, n = lg(L);
  long    x = varn(T);
  GEN     M, P, Tp;
  M = cgetg(n, t_MAT);
  av=avma;
  Tp = gclone(FpX_red(deriv(T, x),mod)); /*clone*/
  avma=av;
  for (i = 1; i < n; i++)
  {
    GEN z;
    av = avma;
    z = mpinvmod(FpX_eval(Tp, (GEN) L[i],mod),mod);
    z = modii(mulii(den,z),mod);
    P = FpX_Fp_mul(FpX_div(T, deg1pol(gun,negi((GEN) L[i]),x),mod), z, mod); 
    M[i] = lgetg(n, t_COL);
    for (j = 1; j < n; j++)
      mael(M,i,j) = lcopy((GEN) P[1 + j]);
    M[i] = lpileupto(av,(GEN)M[i]);
  }
  gunclone(Tp); /*unclone*/
  return M;
}
/* Calcule le polynome associe a un vecteur conjugue v*/
static GEN
vectopol(GEN v, GEN M, GEN den , GEN mod, long x)
{
  long n = lg(v), i, k;
  pari_sp av;
  GEN z = cgetg(n+1,t_POL),p1,p2,mod2;
  av=avma;
  mod2=gclone(shifti(mod,-1));/*clone*/
  avma=av;
  z[1]=evalsigne(1)|evalvarn(x)|evallgef(n+1);
  for (i=2; i<=n; i++)
  {
    p1=gzero; av=avma;
    for (k=1; k<n; k++)
    {
      p2=mulii(gcoeff(M,i-1,k),(GEN)v[k]);
      p1=addii(p1,p2);
    }
    p1=modii(p1,mod);
    if (cmpii(p1,mod2)>0) p1=subii(p1,mod);
    p1=gdiv(p1,den);
    z[i]=lpileupto(av,p1);
  }
  gunclone(mod2);/*unclone*/
  return normalizepol_i(z,n+1);
}
/* Calcule le polynome associe a une permutation des racines*/
static GEN
permtopol(GEN p, GEN L, GEN M, GEN den, GEN mod, long x)
{
  long n = lg(L), i, k;
  pari_sp av;
  GEN z = cgetg(n+1,t_POL),p1,p2,mod2;
  if (lg(p) != n) err(talker,"incorrect permutation in permtopol");
  av=avma;
  mod2=gclone(shifti(mod,-1)); /*clone*/
  avma=av;
  z[1]=evalsigne(1)|evalvarn(x)|evallgef(n+1);
  for (i=2; i<=n; i++)
  {
    p1=gzero; av=avma;
    for (k=1; k<n; k++)
    {
      p2=mulii(gcoeff(M,i-1,k),(GEN)L[p[k]]);
      p1=addii(p1,p2);
    }
    p1=modii(p1,mod);
    if (cmpii(p1,mod2)>0) p1=subii(p1,mod);
    p1=gdiv(p1,den);
    z[i]=lpileupto(av,p1);
  }
  gunclone(mod2); /*unclone*/
  return normalizepol_i(z,n+1);
}

GEN
galoisgrouptopol( GEN res, GEN L, GEN M, GEN den, GEN mod, long v)
{
  GEN aut = cgetg(lg(res), t_COL);
  long i;
  for (i = 1; i < lg(res); i++)
  {
    if (DEBUGLEVEL>=6)
      fprintferr("%d ",i);
    aut[i] = (long) permtopol((GEN) res[i], L, M, den, mod, v);
  }
  return aut;
}

/*
 * Casse l'orbite O en sous-orbite d'ordre premier correspondant a des
 * puissance de l'element
 */
GEN
splitorbite(GEN O)
{
  pari_sp lbot, ltop = avma;
  int     i, n;
  GEN     fc, res;
  n = lg(O[1]) - 1;
  fc = decomp_primary_small(n);
  lbot = avma;
  res = cgetg(3, t_VEC);
  res[1] = lgetg(lg(fc), t_VEC);
  res[2] = lgetg(lg(fc), t_VECSMALL);
  for (i = 1; i < lg(fc); i++)
  {
    mael(res,1,lg(fc) - i) = (long)cyc_powtoperm(O, n / fc[i]);
    mael(res,2,lg(fc) - i) = fc[i];
  }
  if ( DEBUGLEVEL>=4 )
    fprintferr("GaloisConj:splitorbite: %Z\n",res);
  return gerepile(ltop, lbot, res);
}

/*
 * structure qui contient l'analyse du groupe de Galois par etude des degres
 * de Frobenius:
 * 
 * p: nombre premier a relever deg: degre du lift a effectuer pgp: plus grand
 * diviseur premier du degre de T. 
 * l: un nombre premier tel que T est totalement decompose
 * modulo l ppp:  plus petit diviseur premier du degre de T. primepointer:
 * permet de calculer les premiers suivant p.
 */
enum ga_code {ga_all_normal=1,ga_ext_2=2,ga_non_wss=4};
struct galois_analysis
{
  long    p;
  long    deg;
  long    ord;
  long    l;
  long    ppp;
  long    p4;
  enum ga_code group;
  byteptr primepointer;
};
void
galoisanalysis(GEN T, struct galois_analysis *ga, long calcul_l, long karma_type)
{
  pari_sp ltop=avma;
  long n,p;
  long i;
  enum k_code {k_amoeba=0,k_snake=1,k_fish=2,k_bird=4,k_rodent=6,k_dog=8,k_human=9,k_cat=12} karma;
  long group,linf;
  /*TODO: complete the table to at least 200*/
  const int prim_nonss_orders[]={36,48,56,60,72,75,80,96,108,120,132,0};
  GEN F,Fp,Fe,Fpe,O;
  long min_prime,np;
  long order,phi_order;
  long plift,nbmax,nbtest,deg;
  byteptr primepointer,pp;

  if (!ZX_is_squarefree(T))
    err(talker, "Polynomial not squarefree in galoisinit");
  if (DEBUGLEVEL >= 1) (void)timer2();
  n = degpol(T);
  if (!karma_type) karma_type=n;
  else err(warner,"entering black magic computation");
  O = cgetg(n+1,t_VECSMALL);
  for(i=1;i<=n;i++) O[i]=0;
  F = factor(stoi(n));
  Fp=gtovecsmall((GEN)F[1]);
  Fe=gtovecsmall((GEN)F[2]);
  np=lg(Fp)-1;
  Fpe=cgetg(np+1, t_VECSMALL);
  for (i = 1; i < lg(Fpe); i++)
    Fpe[i] = itos(powgi(gmael(F,1,i), gmael(F,2,i)));
  /*In this part, we study the cardinal of the group to have an information
    about the orders, so if we are unlucky we can continue.*/

  /*Are there non WSS groups of this order ?*/
  group=0;
  for(i=0;prim_nonss_orders[i];i++)
    if (n%prim_nonss_orders[i] == 0)
    {
      group |= ga_non_wss;
      break;
    }
  if ( n>12 && n%12 == 0 )
  {
    /*We need to know the greatest prime dividing n/12*/
    if ( Fp[np] == 3 && Fe[np] == 1 )
      group |= ga_ext_2;
  }
  phi_order = 1;
  order = 1;
  for (i = np; i > 0; i--)
  {
    p = Fp[i];
    if (phi_order % p != 0)
    {
      order *= p;
      phi_order *= p - 1;
    }
    else
    {
      group |= ga_all_normal;
      break;
    }
    if (Fe[i]>1)
      break;
  }
  /*Now, we study the orders of the Frobenius elements*/
  min_prime=n*max((long)(BITS_IN_LONG-bfffo(n)-4),2);
  plift = 0;
  nbmax = 8+(n>>1);
  nbtest = 0; karma = k_amoeba;
  deg = Fp[np];
  for (p = 0, pp = primepointer = diffptr;
       (plift == 0 
	|| (nbtest < nbmax && (nbtest <=8 || order < (n>>1)))
	|| (n == 24 && O[6] == 0 && O[4] == 0)
        || ((group&ga_non_wss) && order == Fp[np]))
         && (nbtest < 3 * nbmax || !(group&ga_non_wss)) ;)
  {
    pari_sp av;
    GEN     ip,FS,p1;
    long o,norm_o=1;

    NEXT_PRIME_VIADIFF_CHECK(p,primepointer);
    /*discard small primes*/
    if (p <= min_prime)
      continue;
    ip=stoi(p);
    if (!FpX_is_squarefree(T,ip))
      continue;
    nbtest++;
    av=avma;
    FS=(GEN)simplefactmod(T,ip)[1];
    p1=(GEN)FS[1];
    for(i=2;i<lg(FS);i++)
      if (cmpii(p1,(GEN)FS[i]))
	break;
    if (i<lg(FS))
    {
      avma = ltop;
      if (DEBUGLEVEL >= 2)
	fprintferr("GaloisAnalysis:non Galois for p=%ld\n", p);
      ga->p = p;
      ga->deg = 0;
      return;		/* Not a Galois polynomial */
    }
    o=n/(lg(FS)-1);
    avma=av;
    if (!O[o]) 
      O[o]=p;
    if (o % deg == 0)
    {
      /*We try to find a power of the Frobenius which generate
	a normal subgroup just by looking at the order.*/
      if (o * Fp[1] >= n)
	/*Subgroup of smallest index are normal*/
	norm_o = o;
      else		
      {
	norm_o = 1;
	for (i = np; i > 0; i--)
	{
	  if (o % Fpe[i] == 0)
	    norm_o *= Fpe[i];
	  else
	    break;
	}
      }
      if (norm_o != 1)
      {
	if (!(group&ga_all_normal) || o > order || 
	    (o == order && (plift == 0 || norm_o > deg 
			    || (norm_o == deg && cgcd(p-1,karma_type)>karma ))))
	{
	  deg = norm_o;
	  order = o;
	  plift = p;
	  karma=(enum k_code)cgcd(p-1,karma_type);
	  pp = primepointer;
	  group |= ga_all_normal;
	}
      }
      else if (!(group&ga_all_normal) && (plift == 0 || o > order 
	    || ( o == order && cgcd(p-1,karma_type)>karma )))
      {
	order = o;
	plift = p;
	karma=(enum k_code)cgcd(p-1,karma_type);
	pp = primepointer;
      }
    }
    if (DEBUGLEVEL >= 5)
      fprintferr("GaloisAnalysis:Nbtest=%ld,p=%ld,o=%ld,n_o=%d,best p=%ld,ord=%ld,k=%ld\n",
		 nbtest, p, o, norm_o, plift, order,karma);
  }
  /* This is to avoid looping on non-wss group. 
     To be checked for large groups.  */
  /*Would it be better to disable this check if we are in a good case ?
   * (ga_all_normal and !(ga_ext_2) (e.g. 60)) ?*/
  if (plift == 0 || ((group&ga_non_wss) && order == Fp[np]))
  {
    deg = 0;
    err(warner, "Galois group almost certainly not weakly super solvable");
  }
  /*linf=(n*(n-1))>>2;*/
  linf=n;
  if (calcul_l && O[1]<=linf)
  {
    pari_sp av;
    long    l=0;
    /*we need a totally splited prime l*/
    av = avma;
    while (l == 0)
    {
      long nb;

      NEXT_PRIME_VIADIFF_CHECK(p,primepointer);
      if (p<=linf) continue;
      nb=FpX_nbroots(T,stoi(p));
      if (nb == n)
	l = p;
      else if (nb && FpX_is_squarefree(T,stoi(p)))
      {
	avma = ltop;
	if (DEBUGLEVEL >= 2)
	  fprintferr("GaloisAnalysis:non Galois for p=%ld\n", p);
	ga->p = p;
	ga->deg = 0;
	return;		/* Not a Galois polynomial */
      }
      avma = av;
    }
    O[1]=l;
  }  
  ga->p = plift;
  ga->group = (enum ga_code)group;
  ga->deg = deg;
  ga->ord = order;
  ga->l = O[1];
  ga->primepointer = pp;
  ga->ppp = Fp[1];
  ga->p4 = O[4];
  if (DEBUGLEVEL >= 4)
    fprintferr("GaloisAnalysis:p=%ld l=%ld group=%ld deg=%ld ord=%ld\n",
	       plift, O[1], group, deg, order);
  if (DEBUGLEVEL >= 1)
    msgtimer("galoisanalysis()");
  avma = ltop;
}

/* Groupe A4 */
GEN
a4galoisgen(GEN T, struct galois_test *td)
{
  pari_sp ltop = avma, av, av2;
  long    i, j, k;
  long    n;
  long    N, hop = 0;
  long  **O;
  GEN    *ar, **mt;		/* tired of casting */
  GEN     t, u;
  GEN     res, orb, ry;
  GEN     pft, pfu, pfv;
  n = degpol(T);
  res = cgetg(3, t_VEC);
  ry = cgetg(4, t_VEC);
  res[1] = (long) ry;
  pft = cgetg(n + 1, t_VECSMALL);
  pfu = cgetg(n + 1, t_VECSMALL);
  pfv = cgetg(n + 1, t_VECSMALL);
  ry[1] = (long) pft;
  ry[2] = (long) pfu;
  ry[3] = (long) pfv;
  ry = cgetg(4, t_VECSMALL);
  ry[1] = 2;
  ry[2] = 2;
  ry[3] = 3;
  res[2] = (long) ry;
  av = avma;
  ar = (GEN *) alloue_ardoise(n, 1 + lg(td->ladic));
  mt = (GEN **) td->PV[td->ordre[n]];
  t = cgetg(n + 1, t_VECSMALL) + 1;	/* Sorry for this hack */
  u = cgetg(n + 1, t_VECSMALL) + 1;	/* too lazy to correct */
  av2 = avma;
  N = itos(gdiv(mpfact(n), mpfact(n >> 1))) >> (n >> 1);
  if (DEBUGLEVEL >= 4)
    fprintferr("A4GaloisConj:I will test %ld permutations\n", N);
  avma = av2;
  for (i = 0; i < n; i++)
    t[i] = i + 1;
  for (i = 0; i < N; i++)
  {
    GEN     g;
    int     a, x, y;
    if (i == 0)
    {
      gaffect(gzero, ar[(n - 2) >> 1]);
      for (k = n - 2; k > 2; k -= 2)
	addiiz(ar[k >> 1], addii(mt[k + 1][k + 2], mt[k + 2][k + 1]),
	      ar[(k >> 1) - 1]);
    }
    else
    {
      x = i;
      y = 1;
      do
      {
	y += 2;
	a = x%y;
	x = x/y;
      }
      while (!a);
      switch (y)
      {
      case 3:
	x = t[2];
	if (a == 1)
	{
	  t[2] = t[1];
	  t[1] = x;
	}
	else
	{
	  t[2] = t[0];
	  t[0] = x;
	}
	break;
      case 5:
	x = t[0];
	t[0] = t[2];
	t[2] = t[1];
	t[1] = x;
	x = t[4];
	t[4] = t[4 - a];
	t[4 - a] = x;
	addiiz(ar[2], addii(mt[t[4]][t[5]], mt[t[5]][t[4]]), ar[1]);
	break;
      case 7:
	x = t[0];
	t[0] = t[4];
	t[4] = t[3];
	t[3] = t[1];
	t[1] = t[2];
	t[2] = x;
	x = t[6];
	t[6] = t[6 - a];
	t[6 - a] = x;
	addiiz(ar[3], addii(mt[t[6]][t[7]], mt[t[7]][t[6]]), ar[2]);
	addiiz(ar[2], addii(mt[t[4]][t[5]], mt[t[5]][t[4]]), ar[1]);
	break;
      case 9:
	x = t[0];
	t[0] = t[6];
	t[6] = t[5];
	t[5] = t[3];
	t[3] = x;
	x = t[4];
	t[4] = t[1];
	t[1] = x;
	x = t[8];
	t[8] = t[8 - a];
	t[8 - a] = x;
	addiiz(ar[4], addii(mt[t[8]][t[9]], mt[t[9]][t[8]]), ar[3]);
	addiiz(ar[3], addii(mt[t[6]][t[7]], mt[t[7]][t[6]]), ar[2]);
	addiiz(ar[2], addii(mt[t[4]][t[5]], mt[t[5]][t[4]]), ar[1]);
	break;
      default:
	y--;
	x = t[0];
	t[0] = t[2];
	t[2] = t[1];
	t[1] = x;
	for (k = 4; k < y; k += 2)
	{
	  int     j;
	  x = t[k];
	  for (j = k; j > 0; j--)
	    t[j] = t[j - 1];
	  t[0] = x;
	}
	x = t[y];
	t[y] = t[y - a];
	t[y - a] = x;
	for (k = y; k > 2; k -= 2)
	  addiiz(ar[k >> 1],
		addii(mt[t[k]][t[k + 1]], mt[t[k + 1]][t[k]]),
		ar[(k >> 1) - 1]);
      }
    }
    g = addii(ar[1], addii(addii(mt[t[0]][t[1]], mt[t[1]][t[0]]),
			 addii(mt[t[2]][t[3]], mt[t[3]][t[2]])));
    if (padicisint(g, td))
    {
      for (k = 0; k < n; k += 2)
      {
	pft[t[k]] = t[k + 1];
	pft[t[k + 1]] = t[k];
      }
      if (verifietest(pft, td))
	break;
      else
	hop++;
    }
    avma = av2;
  }
  if (i == N)
  {
    avma = ltop;
    if (DEBUGLEVEL >= 1 && hop)
      fprintferr("A4GaloisConj: %ld hop sur %ld iterations\n", hop, N);
    return gzero;
  }
  if (DEBUGLEVEL >= 1 && hop)
    fprintferr("A4GaloisConj: %ld hop sur %ld iterations\n", hop, N);
  N = itos(gdiv(mpfact(n >> 1), mpfact(n >> 2))) >> 1;
  avma = av2;
  if (DEBUGLEVEL >= 4)
    fprintferr("A4GaloisConj:sigma=%Z \n", pft);
  for (i = 0; i < N; i++)
  {
    GEN     g;
    int     a, x, y;
    if (i == 0)
    {
      for (k = 0; k < n; k += 4)
      {
	u[k + 3] = t[k + 3];
	u[k + 2] = t[k + 1];
	u[k + 1] = t[k + 2];
	u[k] = t[k];
      }
    }
    else
    {
      x = i;
      y = -2;
      do
      {
	y += 4;
	a = x%y;
	x = x/y;
      }
      while (!a);
      x = u[2];
      u[2] = u[0];
      u[0] = x;
      switch (y)
      {
      case 2:
	break;
      case 6:
	x = u[4];
	u[4] = u[6];
	u[6] = x;
	if (!(a & 1))
	{
	  a = 4 - (a >> 1);
	  x = u[6];
	  u[6] = u[a];
	  u[a] = x;
	  x = u[4];
	  u[4] = u[a - 2];
	  u[a - 2] = x;
	}
	break;
      case 10:
	x = u[6];
	u[6] = u[3];
	u[3] = u[2];
	u[2] = u[4];
	u[4] = u[1];
	u[1] = u[0];
	u[0] = x;
	if (a >= 3)
	  a += 2;
	a = 8 - a;
	x = u[10];
	u[10] = u[a];
	u[a] = x;
	x = u[8];
	u[8] = u[a - 2];
	u[a - 2] = x;
	break;
      }
    }
    g = gzero;
    for (k = 0; k < n; k += 2)
      g = addii(g, addii(mt[u[k]][u[k + 1]], mt[u[k + 1]][u[k]]));
    if (padicisint(g, td))
    {
      for (k = 0; k < n; k += 2)
      {
	pfu[u[k]] = u[k + 1];
	pfu[u[k + 1]] = u[k];
      }
      if (verifietest(pfu, td))
	break;
      else
	hop++;
    }
    avma = av2;
  }
  if (i == N)
  {
    avma = ltop;
    return gzero;
  }
  if (DEBUGLEVEL >= 1 && hop)
    fprintferr("A4GaloisConj: %ld hop sur %ld iterations\n", hop, N);
  if (DEBUGLEVEL >= 4)
    fprintferr("A4GaloisConj:tau=%Z \n", pfu);
  avma = av2;
  orb = cgetg(3, t_VEC);
  orb[1] = (long) pft;
  orb[2] = (long) pfu;
  if (DEBUGLEVEL >= 4)
    fprintferr("A4GaloisConj:orb=%Z \n", orb);
  O = (long**) vecperm_orbits(orb, 12);
  if (DEBUGLEVEL >= 4)
    fprintferr("A4GaloisConj:O=%Z \n", O);
  av2 = avma;
  for (j = 0; j < 2; j++)
  {
    pfv[O[1][1]] = O[2][1];
    pfv[O[1][2]] = O[2][3 + j];
    pfv[O[1][3]] = O[2][4 - (j << 1)];
    pfv[O[1][4]] = O[2][2 + j];
    for (i = 0; i < 4; i++)
    {
      long    x;
      GEN     g;
      switch (i)
      {
      case 0:
	break;
      case 1:
	x = O[3][1];
	O[3][1] = O[3][2];
	O[3][2] = x;
	x = O[3][3];
	O[3][3] = O[3][4];
	O[3][4] = x;
	break;
      case 2:
	x = O[3][1];
	O[3][1] = O[3][4];
	O[3][4] = x;
	x = O[3][2];
	O[3][2] = O[3][3];
	O[3][3] = x;
	break;
      case 3:
	x = O[3][1];
	O[3][1] = O[3][2];
	O[3][2] = x;
	x = O[3][3];
	O[3][3] = O[3][4];
	O[3][4] = x;
      }
      pfv[O[2][1]] = O[3][1];
      pfv[O[2][3 + j]] = O[3][4 - j];
      pfv[O[2][4 - (j << 1)]] = O[3][2 + (j << 1)];
      pfv[O[2][2 + j]] = O[3][3 - j];
      pfv[O[3][1]] = O[1][1];
      pfv[O[3][4 - j]] = O[1][2];
      pfv[O[3][2 + (j << 1)]] = O[1][3];
      pfv[O[3][3 - j]] = O[1][4];
      g = gzero;
      for (k = 1; k <= n; k++)
	g = addii(g, mt[k][pfv[k]]);
      if (padicisint(g, td) && verifietest(pfv, td))
      {
	avma = av;
	if (DEBUGLEVEL >= 1)
	  fprintferr("A4GaloisConj:%ld hop sur %d iterations max\n",
		     hop, 10395 + 68);
	return res;
      }
      else
	hop++;
      avma = av2;
    }
  }
  /* Echec? */
  avma = ltop;
  return gzero;
}

/* Groupe S4 */
static void
s4makelift(GEN u, struct galois_lift *gl, GEN liftpow)
{
  int     i;
  liftpow[1] = (long) automorphismlift(u, gl, NULL);
  for (i = 2; i < lg(liftpow); i++)
    liftpow[i] = (long) FpXQ_mul((GEN) liftpow[i - 1], (GEN) liftpow[1],gl->TQ,gl->Q);
}
static long
s4test(GEN u, GEN liftpow, struct galois_lift *gl, GEN phi)
{
  pari_sp ltop=avma;
  GEN     res;
  int     bl,i,d = lgef(u)-2;
  if (DEBUGLEVEL >= 6) (void)timer2();
  if ( !d ) return 0;
  res=(GEN)u[2];
  for (i = 1; i < d; i++)
  {
    if (lgef(liftpow[i])>2)
      res=addii(res,mulii(gmael(liftpow,i,2), (GEN) u[i + 2])); 
  }
  res=modii(mulii(res,gl->den),gl->Q);
  if (cmpii(res,gl->gb->bornesol)>0 
      && cmpii(res,subii(gl->Q,gl->gb->bornesol))<0)
  {
    avma=ltop;
    return 0;
  }
  res = (GEN) scalarpol((GEN)u[2],varn(u));
  for (i = 1; i < d ; i++)
  {
    GEN z;
    z = FpX_Fp_mul((GEN) liftpow[i], (GEN) u[i + 2],NULL);
    res = FpX_add(res,z ,gl->Q);
  }
  res = FpX_center(FpX_Fp_mul(res,gl->den,gl->Q), gl->Q);
  if (DEBUGLEVEL >= 6)
    msgtimer("s4test()");
  bl = poltopermtest(res, gl, phi);
  avma=ltop;
  return bl;
}
static GEN
s4releveauto(GEN misom,GEN Tmod,GEN Tp,GEN p,long a1,long a2,long a3,long a4,long a5,long a6)
{
  pari_sp ltop=avma;
  GEN u1,u2,u3,u4,u5;
  GEN pu1,pu2,pu3,pu4;
  pu1=FpX_mul( (GEN) Tmod[a2], (GEN) Tmod[a1],p);
  u1 = FpX_chinese_coprime(gmael(misom,a1,a2),gmael(misom,a2,a1),
			 (GEN) Tmod[a2], (GEN) Tmod[a1],pu1,p);
  pu2=FpX_mul( (GEN) Tmod[a4], (GEN) Tmod[a3],p);
  u2 = FpX_chinese_coprime(gmael(misom,a3,a4),gmael(misom,a4,a3),
			 (GEN) Tmod[a4], (GEN) Tmod[a3],pu2,p);
  pu3=FpX_mul( (GEN) Tmod[a6], (GEN) Tmod[a5],p);
  u3 = FpX_chinese_coprime(gmael(misom,a5,a6),gmael(misom,a6,a5),
			 (GEN) Tmod[a6], (GEN) Tmod[a5],pu3,p);
  pu4=FpX_mul(pu1,pu2,p);
  u4 = FpX_chinese_coprime(u1,u2,pu1,pu2,pu4,p);
  u5 = FpX_chinese_coprime(u4,u3,pu4,pu3,Tp,p);
  return gerepileupto(ltop,u5);
}
GEN
s4galoisgen(struct galois_lift *gl)
{
  struct galois_testlift gt;
  pari_sp av, ltop2, ltop = avma;
  GEN     Tmod, isom, isominv, misom;
  int     i, j;
  GEN     sg;
  GEN     sigma, tau, phi;
  GEN     res, ry;
  GEN     pj;
  GEN     p,Q,TQ,Tp;
  GEN     bezoutcoeff, pauto, liftpow, aut;

  p = gl->p;
  Q = gl->Q;
  res = cgetg(3, t_VEC);
  ry  = cgetg(5, t_VEC);
  res[1] = (long) ry;
  for (i = 1; i < lg(ry); i++)
    ry[i] = lgetg(lg(gl->L), t_VECSMALL);
  ry = cgetg(5, t_VECSMALL);
  res[2] = (long) ry;
  ry[1] = 2;
  ry[2] = 2;
  ry[3] = 3;
  ry[4] = 2;
  ltop2 = avma;
  sg = cgetg(7, t_VECSMALL);
  pj = cgetg(7, t_VECSMALL);
  sigma = cgetg(lg(gl->L), t_VECSMALL);
  tau = cgetg(lg(gl->L), t_VECSMALL);
  phi = cgetg(lg(gl->L), t_VECSMALL);
  for (i = 1; i < lg(sg); i++)
    sg[i] = i;
  Tp = FpX_red(gl->T,p);
  TQ = gl->TQ;
  Tmod = lift((GEN) factmod(gl->T, p)[1]);
  isom = cgetg(lg(Tmod), t_VEC);
  isominv = cgetg(lg(Tmod), t_VEC);
  misom = cgetg(lg(Tmod), t_MAT);
  aut=galoisdolift(gl, NULL);
  inittestlift(aut,Tmod, gl, &gt);
  bezoutcoeff = gt.bezoutcoeff;
  pauto = gt.pauto;
  for (i = 1; i < lg(pj); i++)
    pj[i] = 0;
  for (i = 1; i < lg(isom); i++)
  {
    misom[i] = lgetg(lg(Tmod), t_COL);
    isom[i] = (long) Fp_isom((GEN) Tmod[1], (GEN) Tmod[i], p);
    if (DEBUGLEVEL >= 6)
      fprintferr("S4GaloisConj:Computing isomorphisms %d:%Z\n", i,
		 (GEN) isom[i]);
    isominv[i] = (long) Fp_inv_isom((GEN) isom[i], (GEN) Tmod[i],p);
  }
  for (i = 1; i < lg(isom); i++)
    for (j = 1; j < lg(isom); j++)
      mael(misom,i,j) = (long) FpX_FpXQ_compo((GEN) isominv[i],(GEN) isom[j],
						(GEN) Tmod[j],p);
  liftpow = cgetg(24, t_VEC);
  av = avma;
  for (i = 0; i < 3; i++)
  {
    pari_sp av2, avm1, avm2;
    GEN     u;
    int     j1, j2, j3;
    GEN     u1, u2, u3;
    if (i)
    {
      int     x;
      x = sg[3];
      if (i == 1)
      {
	sg[3] = sg[2];
	sg[2] = x;
      }
      else
      {
	sg[3] = sg[1];
	sg[1] = x;
      }
    }
    u=s4releveauto(misom,Tmod,Tp,p,sg[1],sg[2],sg[3],sg[4],sg[5],sg[6]);
    s4makelift(u, gl, liftpow);
    av2 = avma;
    for (j1 = 0; j1 < 4; j1++)
    {
      u1 = FpX_add(FpXQ_mul((GEN) bezoutcoeff[sg[5]],
				 (GEN) pauto[1 + j1],TQ,Q),
		  FpXQ_mul((GEN) bezoutcoeff[sg[6]],
				 (GEN) pauto[((-j1) & 3) + 1],TQ,Q),Q);
      avm1 = avma;
      for (j2 = 0; j2 < 4; j2++)
      {
	u2 = FpX_add(u1, FpXQ_mul((GEN) bezoutcoeff[sg[3]], 
				       (GEN) pauto[1 + j2],TQ,Q),NULL);
	u2 = FpX_add(u2, FpXQ_mul((GEN) bezoutcoeff[sg[4]], (GEN)
				       pauto[((-j2) & 3) + 1],TQ,Q),Q);
	avm2 = avma;
	for (j3 = 0; j3 < 4; j3++)
	{
	  u3 = FpX_add(u2, FpXQ_mul((GEN) bezoutcoeff[sg[1]],
					 (GEN) pauto[1 + j3],TQ,Q),NULL);
	  u3 = FpX_add(u3, FpXQ_mul((GEN) bezoutcoeff[sg[2]], (GEN)
					 pauto[((-j3) & 3) + 1],TQ,Q),Q);
	  if (DEBUGLEVEL >= 4)
	    fprintferr("S4GaloisConj:Testing %d/3:%d/4:%d/4:%d/4:%Z\n",
		       i, j1,j2, j3, sg);
	  if (s4test(u3, liftpow, gl, sigma))
	  {
	    pj[1] = j3;
	    pj[2] = j2;
	    pj[3] = j1;
	    goto suites4;
	  }
	  avma = avm2;
	}
	avma = avm1;
      }
      avma = av2;
    }
    avma = av;
  }
  avma = ltop;
  return gzero;
suites4:
  if (DEBUGLEVEL >= 4)
    fprintferr("S4GaloisConj:sigma=%Z\n", sigma);
  if (DEBUGLEVEL >= 4)
    fprintferr("S4GaloisConj:pj=%Z\n", pj);
  avma = av;
  for (j = 1; j <= 3; j++)
  {
    pari_sp av2;
    GEN     u;
    int     w, l;
    int     z;
    z = sg[1]; sg[1] = sg[3]; sg[3] = sg[5]; sg[5] = z;
    z = sg[2]; sg[2] = sg[4]; sg[4] = sg[6]; sg[6] = z;
    z = pj[1]; pj[1] = pj[2]; pj[2] = pj[3]; pj[3] = z;
    for (l = 0; l < 2; l++)
    {
      u=s4releveauto(misom,Tmod,Tp,p,sg[1],sg[3],sg[2],sg[4],sg[5],sg[6]);
      s4makelift(u, gl, liftpow);
      av2 = avma;
      for (w = 0; w < 4; w += 2)
      {
	pari_sp av3;
	GEN     uu;
	pj[6] = (w + pj[3]) & 3;
	uu =FpX_add(FpXQ_mul((GEN) bezoutcoeff[sg[5]],
			  (GEN) pauto[(pj[6] & 3) + 1],TQ,Q),
		   FpXQ_mul((GEN) bezoutcoeff[sg[6]],
			  (GEN) pauto[((-pj[6]) & 3) + 1],TQ,Q),Q);
	av3 = avma;
	for (i = 0; i < 4; i++)
	{
	  GEN     u;
	  pj[4] = i;
	  pj[5] = (i + pj[2] - pj[1]) & 3;
	  if (DEBUGLEVEL >= 4)
	    fprintferr("S4GaloisConj:Testing %d/3:%d/2:%d/2:%d/4:%Z:%Z\n",
		       j - 1, w >> 1, l, i, sg, pj);
	  u = FpX_add(uu, FpXQ_mul((GEN) pauto[(pj[4] & 3) + 1],
				(GEN) bezoutcoeff[sg[1]],TQ,Q),Q);
	  u = FpX_add(u,	 FpXQ_mul((GEN) pauto[((-pj[4]) & 3) + 1],
				(GEN) bezoutcoeff[sg[3]],TQ,Q),Q);
	  u = FpX_add(u,	 FpXQ_mul((GEN) pauto[(pj[5] & 3) + 1],
				(GEN) bezoutcoeff[sg[2]],TQ,Q),Q);
	  u = FpX_add(u,	 FpXQ_mul((GEN) pauto[((-pj[5]) & 3) + 1],
				(GEN) bezoutcoeff[sg[4]],TQ,Q),Q);
	  if (s4test(u, liftpow, gl, tau))
	    goto suites4_2;
	  avma = av3;
	}
	avma = av2;
      }
      z = sg[4];
      sg[4] = sg[3];
      sg[3] = z;
      pj[2] = (-pj[2]) & 3;
      avma = av;
    }
  }
  avma = ltop;
  return gzero;
suites4_2:
  avma = av;
  {
    int     abc, abcdef;
    GEN     u;
    pari_sp av2;
    abc = (pj[1] + pj[2] + pj[3]) & 3;
    abcdef = (((abc + pj[4] + pj[5] - pj[6]) & 3) >> 1);
    u = s4releveauto(misom,Tmod,Tp,p,sg[1],sg[4],sg[2],sg[5],sg[3],sg[6]);
    s4makelift(u, gl, liftpow);
    av2 = avma;
    for (j = 0; j < 8; j++)
    {
      int     h, g, i;
      h = j & 3;
      g = abcdef + ((j & 4) >> 1);
      i = h + abc - g;
      u = FpXQ_mul((GEN) pauto[(g & 3) + 1],
		   (GEN) bezoutcoeff[sg[1]],TQ,Q);
      u = FpX_add(u, FpXQ_mul((GEN) pauto[((-g) & 3) + 1],
			      (GEN) bezoutcoeff[sg[4]],TQ,Q),NULL);
      u = FpX_add(u, FpXQ_mul((GEN) pauto[(h & 3) + 1],
			      (GEN) bezoutcoeff[sg[2]],TQ,Q),NULL);
      u = FpX_add(u, FpXQ_mul((GEN) pauto[((-h) & 3) + 1],
			      (GEN) bezoutcoeff[sg[5]],TQ,Q),NULL);
      u = FpX_add(u, FpXQ_mul((GEN) pauto[(i & 3) + 1],
			      (GEN) bezoutcoeff[sg[3]],TQ,Q),NULL);
      u = FpX_add(u, FpXQ_mul((GEN) pauto[((-i) & 3) + 1],
			      (GEN) bezoutcoeff[sg[6]],TQ,Q),Q);
      if (DEBUGLEVEL >= 4)
	fprintferr("S4GaloisConj:Testing %d/8 %d:%d:%d\n",
		   j, g & 3, h & 3, i & 3);
      if (s4test(u, liftpow, gl, phi))
	break;
      avma = av2;
    }
  }
  if (j == 8)
  {
    avma = ltop;
    return gzero;
  }
  for (i = 1; i < lg(gl->L); i++)
  {
    ((GEN **) res)[1][1][i] = sigma[tau[i]];
    ((GEN **) res)[1][2][i] = phi[sigma[tau[phi[i]]]];
    ((GEN **) res)[1][3][i] = phi[sigma[i]];
    ((GEN **) res)[1][4][i] = sigma[i];
  }
  avma = ltop2;
  return res;
}
struct galois_frobenius
{
  long p;
  long fp;
  long deg;
  GEN Tmod;
  GEN psi;
};

/*Warning : the output of this function is not gerepileupto
 * compatible...*/
static GEN
galoisfindgroups(GEN lo, GEN sg, long f)
{
  pari_sp ltop=avma;
  GEN V,W;
  long i,j,k;
  V=cgetg(lg(lo),t_VEC);
  for(j=1,i=1;i<lg(lo);i++)
  {
    pari_sp av=avma;
    GEN U;
    W=cgetg(lg(lo[i]),t_VECSMALL);
    for(k=1;k<lg(lo[i]);k++)
      W[k]=mael(lo,i,k)%f;
    vecsmall_sort(W); 
    U=vecsmall_uniq(W);
    if (gegal(U, sg))
    {
      cgiv(U);
      V[j++]=lo[i];
    }
    else
      avma=av;
  }
  setlg(V,j);
  /*warning components of V point to W*/
  return gerepileupto(ltop,V);
}

static long
galoisfrobeniustest(GEN aut, struct galois_lift *gl, GEN frob)
{
  pari_sp ltop = avma;
  GEN tlift = FpX_center(FpX_Fp_mul(aut,gl->den,gl->Q), gl->Q);
  long res = poltopermtest(tlift, gl, frob);
  avma = ltop;
  return res;
}

static GEN
galoismakepsi(long g, GEN sg, GEN pf)
{
  GEN psi=cgetg(g+1,t_VECSMALL);
  long i;
  for (i = 1; i < g; i++)
    psi[i] = sg[pf[i]];
  psi[g]=sg[1];
  return psi;
}

static GEN
galoisfrobeniuslift(GEN T, GEN den, GEN L,  GEN Lden, 
    struct galois_frobenius *gf,  struct galois_borne *gb) 
{
  pari_sp ltop=avma, av2;
  struct galois_testlift gt;
  struct galois_lift gl;
  GEN res;
  long i,j,k;
  long n=lg(L)-1, deg=1, g=lg(gf->Tmod)-1;
  GEN F,Fp,Fe;
  GEN ip=stoi(gf->p), aut, frob;
  if (DEBUGLEVEL >= 4)
    fprintferr("GaloisConj:p=%ld deg=%ld fp=%ld\n", gf->p, deg, gf->fp);
  res = cgetg(lg(L), t_VECSMALL);
  gf->psi = vecsmall_const(g,1);
  av2=avma;
  initlift(T, den, ip, L, Lden, gb, &gl);
  aut = galoisdolift(&gl, res);
  if (!aut || galoisfrobeniustest(aut,&gl,res))
  {
    avma=av2;
    gf->deg = gf->fp;
    return res;
  }
  inittestlift(aut,gf->Tmod, &gl, &gt);
  gt.C=cgetg(gf->fp+1,t_VEC);
  for (i = 1; i <= gf->fp; i++)
  {
    gt.C[i]=lgetg(gt.g+1,t_VECSMALL);
    for(j = 1; j <= gt.g; j++)
      mael(gt.C,i,j)=0;
  }
  gt.Cd=gcopy(gt.C);

  F=factor(stoi(gf->fp));
  Fp=gtovecsmall((GEN)F[1]);
  Fe=gtovecsmall((GEN)F[2]);
  frob = cgetg(lg(L), t_VECSMALL);
  for(k=lg(Fp)-1;k>=1;k--)
  {
    pari_sp btop=avma;
    GEN psi=NULL,fres=NULL,sg;
    long el=gf->fp, dg=1, dgf=1;
    long e,pr;
    sg=perm_identity(1);
    for(e=1;e<=Fe[k];e++)
    {
      long l;
      GEN lo;
      GEN pf;
      dg *= Fp[k]; el /= Fp[k];
      if ( DEBUGLEVEL>=4 )
	fprintferr("Trying degre %d.\n",dg);
      if (galoisfrobeniustest((GEN)gt.pauto[el+1],&gl,frob))
      {
	dgf = dg; 
	psi = vecsmall_const(g,1);
	fres= gcopy(frob);
	continue;
      }
      disable_dbg(0);
      lo = listsousgroupes(dg, n / gf->fp);
      disable_dbg(-1);
      if (e!=1)
	lo = galoisfindgroups(lo, sg, dgf);
      if (DEBUGLEVEL >= 4)
	fprintferr("Galoisconj:Subgroups list:%Z\n", lo);
      for (l = 1; l < lg(lo); l++)
	if ( lg(lo[l])>2 && 
	    frobeniusliftall((GEN)lo[l], el, &pf, &gl, &gt, frob))
	{
	  sg  = gcopy((GEN)lo[l]);
	  psi = galoismakepsi(g,sg,pf);
	  dgf = dg;
	  fres=gcopy(frob);
	  break;
	}
      if ( l == lg(lo) )
	break;
    }
    if (dgf==1) { avma=btop; continue; }
    pr=deg*dgf;
    if (deg==1)
    {
      for(i=1;i<lg(res);i++) res[i]=fres[i];
      for(i=1;i<lg(psi);i++) gf->psi[i]=psi[i];
    } 
    else
    {
      GEN cp=perm_mul(res,fres);
      for(i=1;i<lg(res);i++) res[i]=cp[i];
      for(i=1;i<lg(psi);i++) gf->psi[i]=(dgf*gf->psi[i]+deg*psi[i])%pr;
    }
    deg=pr;
    avma=btop;
  }
  for (i = 1; i <= gf->fp; i++)
    for (j = 1; j <= gt.g; j++)
      if (mael(gt.C,i,j))
	gunclone(gmael(gt.C,i,j));
  if (DEBUGLEVEL>=4 && res)
    fprintferr("Best lift: %d\n",deg);
  if (deg==1)
  {
    avma=ltop;
    return NULL;
  }
  else
  {
    /*We need to normalise result so that psi[g]=1*/
    long im=itos(mpinvmod(stoi(gf->psi[g]),stoi(gf->fp)));
    GEN cp=perm_pow(res, im);
    for(i=1;i<lg(res);i++) res[i]=cp[i];
    for(i=1;i<lg(gf->psi);i++) gf->psi[i]=mulssmod(im,gf->psi[i],gf->fp);
    avma=av2;
    gf->deg=deg;
    return res;
  }
}

static GEN
galoisfindfrobenius(GEN T, GEN L, GEN den, struct galois_frobenius *gf,
    struct galois_borne *gb, const struct galois_analysis *ga)
{
  pari_sp lbot, ltop=avma;
  long Try=0;
  long n = degpol(T), deg, gmask;
  byteptr primepointer = ga->primepointer;
  GEN Lden,frob;
  Lden=makeLden(L,den,gb);
  gf->deg=ga->deg;gf->p=ga->p; deg=ga->deg;
  gmask=(ga->group&ga_ext_2)?3:1;
  for (;;)
  {
    pari_sp av = avma;
    long    isram;
    long    i;
    GEN     ip,Tmod;
    ip = stoi(gf->p);
    Tmod = lift((GEN) factmod(T, ip));
    isram = 0;
    for (i = 1; i < lg(Tmod[2]) && !isram; i++)
      if (!gcmp1(gmael(Tmod,2,i)))
	isram = 1;
    if (isram == 0)
    {
      gf->fp = degpol(gmael(Tmod,1,1));
      for (i = 2; i < lg(Tmod[1]); i++)
	if (degpol(gmael(Tmod,1,i)) != gf->fp)
	{
	  avma = ltop;
	  return NULL;		/* Not Galois polynomial */
	}
      lbot=avma;
      gf->Tmod=gcopy((GEN)Tmod[1]);
      if ( ((gmask&1) && gf->fp % deg == 0) || ((gmask&2) && gf->fp % 2== 0) )
      {
	frob=galoisfrobeniuslift(T, den, L, Lden, gf, gb);
	if (frob)
	{
	  GEN *gptr[3];
	  gptr[0]=&gf->Tmod;
	  gptr[1]=&gf->psi;
	  gptr[2]=&frob;
	  gerepilemanysp(ltop,lbot,gptr,3);
	  return frob;
	}
	if ((ga->group&ga_all_normal) && gf->fp % deg == 0)
	  gmask&=~1;
	/*The first prime degree is always divisible by deg, so we don't
	 * have to worry about ext_2 being used before regular supersolvable*/
	if (!gmask)
	{
	  avma = ltop;
	  return NULL;
	}
	Try++;
	if ( (ga->group&ga_non_wss) && Try > n )
	  err(warner, "galoisconj _may_ hang up for this polynomial");
      }
    }
    NEXT_PRIME_VIADIFF_CHECK(gf->p, primepointer);
    if (DEBUGLEVEL >= 4)
      fprintferr("GaloisConj:next p=%ld\n", gf->p);
    avma = av;
  }
}

GEN
galoisgen(GEN T, GEN L, GEN M, GEN den, struct galois_borne *gb,
	  const struct galois_analysis *ga);
static GEN
galoisgenfixedfield(GEN Tp, GEN Pmod, GEN V, GEN ip, struct galois_borne *gb, GEN Pg)
{
  pari_sp ltop=avma;
  GEN     P, PL, Pden, PM, Pp, Pladicabs;
  GEN     tau, PG;
  long    g,gp;
  long    x=varn(Tp);
  P=(GEN)V[2];
  PL=(GEN)V[1];
  gp=lg(Pmod)-1;
  Pp = FpX_red(P,ip);
  if (DEBUGLEVEL>=6)
    fprintferr("GaloisConj: Fixed field %Z\n",P);
  if (degpol(P)==2)
  {
    PG=cgetg(3,t_VEC);
    PG[1]=lgetg(2,t_VEC);
    PG[2]=lgetg(2,t_VECSMALL);
    mael(PG,1,1)=lgetg(3,t_VECSMALL);
    mael(PG,2,1)=2;
    mael3(PG,1,1,1)=2;
    mael3(PG,1,1,2)=1;
    tau=deg1pol(stoi(-1),negi((GEN)P[3]),x);
    tau = lift(gmul(tau,gmodulcp(gun,ip)));
    tau = FpX_FpXQ_compo((GEN) Pmod[gp], tau,Pp,ip);
    tau = FpX_gcd(Pp, tau,ip);
    tau = FpX_Fp_mul(tau,mpinvmod((GEN) tau[lgef(tau) - 1],ip),ip);
    for (g = 1; g <= gp; g++)
      if (gegal(tau, (GEN) Pmod[g]))
	break;
    if (g == lg(Pmod))
      return NULL;
    Pg[1]=g;
  }
  else
  {
    struct galois_analysis Pga;
    struct galois_borne Pgb;
    long j;
    galoisanalysis(P, &Pga, 0, 0);
    if (Pga.deg == 0)
      return NULL;		/* Avoid computing the discriminant */
    Pgb.l = gb->l;
    Pden = galoisborne(P, NULL, &Pgb, Pga.ppp);
    Pladicabs=Pgb.ladicabs;
    if (Pgb.valabs > gb->valabs)
    {
      if (DEBUGLEVEL>=4)
	fprintferr("GaloisConj:increase prec of p-adic roots of %ld.\n"
	    ,Pgb.valabs-gb->valabs);
      PL = rootpadicliftroots(P,PL,gb->l,Pgb.valabs);
    }
    PM = vandermondeinversemod(PL, P, Pden, Pgb.ladicabs);
    PG = galoisgen(P, PL, PM, Pden, &Pgb, &Pga);
    if (PG == gzero) return NULL;
    for (j = 1; j < lg(PG[1]); j++)
    {
      pari_sp btop=avma;
      tau = permtopol(gmael(PG,1,j), PL, PM, Pden, Pladicabs, x);
      tau = lift(gmul(tau,gmodulcp(gun,ip)));
      tau = FpX_FpXQ_compo((GEN) Pmod[gp], tau,Pp,ip);
      tau = FpX_gcd(Pp, tau,ip);
      tau = FpX_Fp_mul(tau,mpinvmod((GEN) tau[lgef(tau) - 1],ip),ip);
      for (g = 1; g < lg(Pmod); g++)
	if (gegal(tau, (GEN) Pmod[g]))
	  break;
      if (g == lg(Pmod))
	return NULL;
      avma=btop;
      Pg[j]=g;
    }
  }
  return gerepilecopy(ltop,PG);
}

GEN
galoisgen(GEN T, GEN L, GEN M, GEN den, struct galois_borne *gb,
	  const struct galois_analysis *ga)
{
  struct galois_test td;
  struct galois_frobenius gf;
  pari_sp lbot, ltop2, ltop = avma;
  long    n, p, deg;
  long    fp;
  long    x;
  int     i, j;
  GEN     Lden, sigma;
  GEN     Tmod, res, pf = gzero, split, ip;
  GEN     frob;
  GEN     O;
  GEN     PG, Pg;
  n = degpol(T);
  if (!ga->deg)
    return gzero;
  x = varn(T);
  if (DEBUGLEVEL >= 9)
    fprintferr("GaloisConj:denominator:%Z\n", den);
  if (n == 12 && ga->ord==3)	/* A4 is very probable,so test it first */
  {
    pari_sp av = avma;
    if (DEBUGLEVEL >= 4)
      fprintferr("GaloisConj:Testing A4 first\n");
    inittest(L, M, gb->bornesol, gb->ladicsol, &td);
    lbot = avma;
    PG = a4galoisgen(T, &td);
    freetest(&td);
    if (PG != gzero)
      return gerepile(ltop, lbot, PG);
    avma = av;
  }
  if (n == 24 && ga->ord==3)	/* S4 is very probable,so test it first */
  {
    pari_sp av = avma;
    struct galois_lift gl;
    if (DEBUGLEVEL >= 4)
      fprintferr("GaloisConj:Testing S4 first\n");
    lbot = avma;
    Lden=makeLden(L,den,gb);
    initlift(T, den, stoi(ga->p4), L, Lden, gb, &gl);
    PG = s4galoisgen(&gl);
    if (PG != gzero)
      return gerepile(ltop, lbot, PG);
    avma = av;
  }
  frob=galoisfindfrobenius(T, L, den, &gf, gb, ga);
  if (!frob)
  {
    ltop=avma;
    return gzero;
  }
  p=gf.p;
  ip=stoi(p);
  Tmod=gf.Tmod;
  fp=gf.fp;
  O = perm_cycles(frob);
  split = splitorbite(O);
  deg=lg(O[1])-1;
  sigma = permtopol(frob, L, M, den, gb->ladicabs, x);
  if (DEBUGLEVEL >= 9)
    fprintferr("GaloisConj:Orbite:%Z\n", O);
  if (deg == n)			/* Cyclique */
  {
    lbot = avma;
    res = cgetg(3, t_VEC);
    res[1] = lgetg(lg(split[1]), t_VEC);
    res[2] = lgetg(lg(split[2]), t_VECSMALL);
    for (i = 1; i < lg(split[1]); i++)
    {
      mael(res,1,i) = lcopy(gmael(split,1,i));
      mael(res,2,i) = mael(split,2,i);
    }
    return gerepile(ltop, lbot, res);
  }
  if (DEBUGLEVEL >= 9)
    fprintferr("GaloisConj:Frobenius:%Z\n", sigma);
  Pg=cgetg(lg(O),t_VECSMALL);
  {
    pari_sp btop=avma;
    GEN     V, sym, dg, Tp, Sp, Pmod;
    sym=cgetg(lg(L),t_VECSMALL);
    dg=cgetg(lg(L),t_VECSMALL);
    V = fixedfieldsympol(O, L, gb->ladicabs, gb->l, ip, sym, dg, x);
    Tp = FpX_red(T,ip);
    Sp = fixedfieldpolsigma(sigma,ip,Tp,sym,dg,deg);
    Pmod = fixedfieldfactmod(Sp,ip,Tmod);
    PG=galoisgenfixedfield(Tp, Pmod, V, ip, gb, Pg);
    if (PG == NULL)
    {
      avma = ltop;
      return gzero;
    }
    if (DEBUGLEVEL >= 4)
      fprintferr("GaloisConj:Back to Earth:%Z\n", PG);
    PG=gerepileupto(btop, PG);
  }
  inittest(L, M, gb->bornesol, gb->ladicsol, &td);
  lbot = avma;
  res = cgetg(3, t_VEC);
  res[1] = lgetg(lg(PG[1]) + lg(split[1]) - 1, t_VEC);
  res[2] = lgetg(lg(PG[1]) + lg(split[1]) - 1, t_VECSMALL);
  for (i = 1; i < lg(split[1]); i++)
  {
    ((GEN **) res)[1][i] = gcopy(((GEN **) split)[1][i]);
    ((GEN *) res)[2][i] = ((GEN *) split)[2][i];
  }
  for (i = lg(split[1]); i < lg(res[1]); i++)
    ((GEN **) res)[1][i] = cgetg(n + 1, t_VECSMALL);
  ltop2 = avma;
  for (j = 1; j < lg(PG[1]); j++)
  {
    GEN     B;
    long    t;
    long    w, sr, dss;
    if (DEBUGLEVEL >= 6)
      fprintferr("GaloisConj:G[%d]=%Z  d'ordre relatif %d\n", j,
	  ((GEN **) PG)[1][j], ((long **) PG)[2][j]);
    B = perm_cycles(gmael(PG,1,j));
    if (DEBUGLEVEL >= 6)
      fprintferr("GaloisConj:B=%Z\n", B);
    w = gf.psi[Pg[j]];
    dss = deg / cgcd(deg, w - 1);
    sr = 1;
    for (i = 1; i < lg(B[1]) - 1; i++)
      sr = (1 + sr * w) % deg;
    sr = cgcd(sr, deg);
    if (DEBUGLEVEL >= 6)
      fprintferr("GaloisConj:w=%ld [%ld] sr=%ld dss=%ld\n", w, deg, sr, dss);
    for (t = 0; t < sr; t += dss)
    {
      pf = testpermutation(O, B, w, t, sr, &td);
      if (pf != gzero)
	break;
    }
    if (pf == gzero)
    {
      freetest(&td);
      avma = ltop;
      return gzero;
    }
    else
    {
      int     i;
      for (i = 1; i <= n; i++)
	((GEN **) res)[1][lg(split[1]) + j - 1][i] = pf[i];
      ((GEN *) res)[2][lg(split[1]) + j - 1] = ((GEN *) PG)[2][j];
    }
    avma = ltop2;
  }
  if (DEBUGLEVEL >= 4)
    fprintferr("GaloisConj:Fini!\n");
  freetest(&td);
  return gerepile(ltop, lbot, res);
}

/*
 * T: polynome ou nf den optionnel: si présent doit etre un multiple du
 * dénominateur commun des solutions Si T est un nf et den n'est pas présent,
 * le denominateur de la base d'entiers est pris pour den
 */
GEN
galoisconj4(GEN T, GEN den, long flag, long karma)
{
  pari_sp ltop = avma;
  GEN     G, L, M, res, aut, grp=NULL;/*keep gcc happy on the wall*/
  struct galois_analysis ga;
  struct galois_borne gb;
  int     n, i, j, k;
  if (typ(T) != t_POL)
  {
    T = checknf(T);
    if (!den) den = Q_denom((GEN)T[7]);
    T = (GEN) T[1];
  }
  n = degpol(T);
  if (n <= 0)
    err(constpoler, "galoisconj4");
  for (k = 2; k <= n + 2; k++)
    if (typ(T[k]) != t_INT)
      err(talker, "polynomial not in Z[X] in galoisconj4");
  if (!gcmp1((GEN) T[n + 2]))
    err(talker, "non-monic polynomial in galoisconj4");
  n = degpol(T);
  if (n == 1)			/* Too easy! */
  {
    if (!flag)
    {
      res = cgetg(2, t_COL);
      res[1] = (long) polx[varn(T)];
      return res;
    }
    ga.l = 3;
    ga.deg = 1;
    ga.ppp = 1;
    den = gun;
  }
  else
    galoisanalysis(T, &ga, 1, karma);
  if (ga.deg == 0)
  {
    avma = ltop;
    return stoi(ga.p);		/* Avoid computing the discriminant */
  }
  if (den)
  {
    if (typ(den) != t_INT)
      err(talker, "Second arg. must be integer in galoisconj4");
    den = absi(den);
  }
  gb.l = stoi(ga.l);
  if (DEBUGLEVEL >= 1) (void)timer2();
  den = galoisborne(T, den, &gb, ga.ppp);
  if (DEBUGLEVEL >= 1)
    msgtimer("galoisborne()");
  L = rootpadicfast(T, gb.l, gb.valabs);
  if (DEBUGLEVEL >= 1)
    msgtimer("rootpadicfast()");
  M = vandermondeinversemod(L, T, den, gb.ladicabs);
  if (DEBUGLEVEL >= 1)
    msgtimer("vandermondeinversemod()");
  if (n == 1)
  {
    G = cgetg(3, t_VEC);
    G[1] = lgetg(1, t_VECSMALL);
    G[2] = lgetg(1, t_VECSMALL);
  }
  else
    G = galoisgen(T, L, M, den, &gb, &ga);
  if (DEBUGLEVEL >= 6)
    fprintferr("GaloisConj:%Z\n", G);
  if (G == gzero)
  {
    avma = ltop;
    return gzero;
  }
  if (DEBUGLEVEL >= 1) (void)timer2();
  if (flag)
  {
    grp = cgetg(9, t_VEC);
    grp[1] = (long) gcopy(T);
    grp[2] = lgetg(4,t_VEC); /*Make K.B. happy(8 components)*/
    mael(grp,2,1) = lstoi(ga.l);
    mael(grp,2,2) = lstoi(gb.valabs);
    mael(grp,2,3) = licopy(gb.ladicabs);
    grp[3] = (long) gcopy(L);
    grp[4] = (long) gcopy(M);
    grp[5] = (long) gcopy(den);
    grp[7] = (long) gcopy((GEN) G[1]);
    grp[8] = (long) gcopy((GEN) G[2]);
  }
  res = cgetg(n + 1, t_VEC);
  res[1] = (long) perm_identity(n);
  k = 1;
  for (i = 1; i < lg(G[1]); i++)
  {
    int     c = k * (((long **) G)[2][i] - 1);
    for (j = 1; j <= c; j++)	/* I like it */
      res[++k] = (long) perm_mul((GEN) res[j], ((GEN **) G)[1][i]);
  }
  if (flag)
  {
    grp[6] = (long) res;
    return gerepileupto(ltop, grp);
  }
  aut = galoisgrouptopol(res,L,M,den,gb.ladicsol, varn(T));
  if (DEBUGLEVEL >= 1)
    msgtimer("Calcul polynomes");
  return gerepileupto(ltop, gen_sort(aut, 0, cmp_pol));
}

/* Calcule le nombre d'automorphisme de T avec forte probabilité */
/* pdepart premier nombre premier a tester */
long
numberofconjugates(GEN T, long pdepart)
{
  pari_sp ltop2, ltop = avma;
  long    n, p, nbmax, nbtest;
  long    card;
  byteptr primepointer;
  int     i;
  GEN     L;
  n = degpol(T);
  card = sturm(T);
  card = cgcd(card, n - card);
  nbmax = (n<<1) + 1;
  if (nbmax < 20) nbmax=20;
  nbtest = 0;
  L = cgetg(n + 1, t_VECSMALL);
  ltop2 = avma;
  for (p = 0, primepointer = diffptr; nbtest < nbmax && card > 1;)
  {
    long    s;
    long    isram;
    GEN     S;

    NEXT_PRIME_VIADIFF_CHECK(p,primepointer);
    if (p < pdepart)
      continue;
    S = (GEN) simplefactmod(T, stoi(p));
    isram = 0;
    for (i = 1; i < lg(S[2]) && !isram; i++)
      if (!gcmp1(((GEN **) S)[2][i]))
	isram = 1;
    if (isram == 0)
    {
      for (i = 1; i <= n; i++)
	L[i] = 0;
      for (i = 1; i < lg(S[1]) && !isram; i++)
	L[itos(((GEN **) S)[1][i])]++;
      s = L[1];
      for (i = 2; i <= n; i++)
	s = cgcd(s, L[i] * i);
      card = cgcd(s, card);
    }
    if (DEBUGLEVEL >= 6)
      fprintferr("NumberOfConjugates:Nbtest=%ld,card=%ld,p=%ld\n", nbtest,
		 card, p);
    nbtest++;
    avma = ltop2;
  }
  if (DEBUGLEVEL >= 2)
    fprintferr("NumberOfConjugates:card=%ld,p=%ld\n", card, p);
  avma = ltop;
  return card;
}

GEN
galoisconj0(GEN nf, long flag, GEN d, long prec)
{
  pari_sp ltop;
  GEN     G, T;
  long    card;
  if (typ(nf) != t_POL)
  {
    nf = checknf(nf);
    T = (GEN) nf[1];
  }
  else
    T = nf;
  switch (flag)
  {
  case 0:
    ltop = avma;
    G = galoisconj4(nf, d, 0, 0);
    if (typ(G) != t_INT)	/* Success */
      return G;
    else
    {
      card = numberofconjugates(T, G == gzero ? 2 : itos(G));
      avma = ltop;
      if (card != 1)
      {
	if (typ(nf) == t_POL)
	{
	  G = galoisconj2pol(nf, card, prec);
	  if (lg(G) <= card)
	    err(warner, "conjugates list may be incomplete in nfgaloisconj");
	  return G;
	}
	else
	  return galoisconj(nf);
      }
    }
    break;			/* Failure */
  case 1:
    return galoisconj(nf);
  case 2:
    return galoisconj2(nf, degpol(T), prec);
  case 4:
    G = galoisconj4(nf, d, 0, 0);
    if (typ(G) != t_INT)
      return G;
    break;			/* Failure */
  default:
    err(flagerr, "nfgaloisconj");
  }
  G = cgetg(2, t_COL);
  G[1] = (long) polx[varn(T)];
  return G;			/* Failure */
}



/******************************************************************************/
/* Isomorphism between number fields                                          */
/******************************************************************************/
long
isomborne(GEN P, GEN den, GEN p)
{
  pari_sp ltop=avma;
  struct galois_borne gb;
  gb.l=p;
  (void)galoisborne(P,den,&gb,degpol(P));
  avma=ltop;
  return gb.valsol;
}



/******************************************************************************/
/* Galois theory related algorithms                                           */
/******************************************************************************/
GEN
checkgal(GEN gal)
{
  if (typ(gal) == t_POL)
    err(talker, "please apply galoisinit first");
  if (typ(gal) != t_VEC || lg(gal) != 9)
    err(talker, "Not a Galois field in a Galois related function");
  return gal;
}

GEN
galoisinit(GEN nf, GEN den, long karma)
{
  GEN     G;
  G = galoisconj4(nf, den, 1, karma);
  if (typ(G) == t_INT)
    err(talker,
	"galoisinit: field not Galois or Galois group not weakly super solvable");
  return G;
}

GEN
galoispermtopol(GEN gal, GEN perm)
{
  GEN     v;
  long    t = typ(perm);
  int     i;
  gal = checkgal(gal);
  switch (t)
  {
  case t_VECSMALL:
    return permtopol(perm, (GEN) gal[3], (GEN) gal[4], (GEN) gal[5],
		     gmael(gal,2,3), varn((GEN) gal[1]));
  case t_VEC:
  case t_COL:
  case t_MAT:
    v = cgetg(lg(perm), t);
    for (i = 1; i < lg(v); i++)
      v[i] = (long) galoispermtopol(gal, (GEN) perm[i]);
    return v;
  }
  err(typeer, "galoispermtopol");
  return NULL;			/* not reached */
}


GEN 
galoiscosets(GEN O, GEN perm)
{
  long i,j,k,u;
  long o = lg(O)-1, f = lg(O[1])-1;
  GEN C = cgetg(lg(O),t_VECSMALL);
  pari_sp av=avma;
  GEN RC=cgetg(lg(perm),t_VECSMALL);
  for(i=1;i<lg(RC);i++)
    RC[i]=0;
  u=mael(O,1,1);
  for(i=1,j=1;j<=o;i++)
  {
    if (RC[mael(perm,i,u)])
      continue;
    for(k=1;k<=f;k++)
      RC[mael(perm,i,mael(O,1,k))]=1;
    C[j++]=i;
  }
  avma=av;
  return C;
}

GEN
fixedfieldfactor(GEN L, GEN O, GEN perm, GEN M, GEN den, GEN mod,
                 long x,long y)
{
  pari_sp ltop=avma;
  GEN     F,G,V,res,cosets;
  int     i, j, k;
  F=cgetg(lg(O[1])+1,t_COL);
  F[lg(O[1])]=un;
  G=cgetg(lg(O),t_VEC);
  for (i = 1; i < lg(O); i++)
  {
    GEN Li = cgetg(lg(O[i]),t_VEC);
    for (j = 1; j < lg(O[i]); j++)
      Li[j] = L[mael(O,i,j)];
    G[i]=(long)FpV_roots_to_pol(Li,mod,x);
  }  
  
  cosets=galoiscosets(O,perm);
  if (DEBUGLEVEL>=4) fprintferr("GaloisFixedField:cosets=%Z \n",cosets);
  V=cgetg(lg(O),t_COL);
  if (DEBUGLEVEL>=6) fprintferr("GaloisFixedField:den=%Z mod=%Z \n",den,mod);
  res=cgetg(lg(O),t_VEC);
  for (i = 1; i < lg(O); i++)
  {
    pari_sp av=avma;
    long ii,jj;
    GEN G=cgetg(lg(O),t_VEC);
    for (ii = 1; ii < lg(O); ii++)
    {
      GEN Li = cgetg(lg(O[ii]),t_VEC);
      for (jj = 1; jj < lg(O[ii]); jj++)
	Li[jj] = L[mael(perm,cosets[i],mael(O,ii,jj))];
      G[ii]=(long)FpV_roots_to_pol(Li,mod,x);
    }  
    for (j = 1; j < lg(O[1]); j++)
    {
      for(k = 1; k < lg(O); k++)
	V[k]=mael(G,k,j+1);
      F[j]=(long) vectopol(V, M, den, mod, y);
    }
    res[i]=(long)gerepileupto(av,gtopolyrev(F,x));
  }
  return gerepileupto(ltop,res);
}

GEN
galoisfixedfield(GEN gal, GEN perm, long flag, long y)
{
  pari_sp lbot, ltop = avma;
  GEN     L, P, S, PL, O, res, mod;
  long    x, n;
  int     i;
  gal = checkgal(gal);
  x = varn((GEN) gal[1]);
  L = (GEN) gal[3]; n=lg(L)-1;
  mod = gmael(gal,2,3);
  if (flag<0 || flag>2)
    err(flagerr, "galoisfixedfield");
  if (typ(perm) == t_VEC)
  {
    for (i = 1; i < lg(perm); i++)
      if (typ(perm[i]) != t_VECSMALL || lg(perm[i])!=n+1)
        err(typeer, "galoisfixedfield");
    O = vecperm_orbits(perm, n);
  }
  else if (typ(perm) != t_VECSMALL || lg(perm)!=n+1 )
  {
    err(typeer, "galoisfixedfield");
    return NULL; /* not reached */
  }
  else
    O = perm_cycles(perm);
  {
    GEN sym=cgetg(lg(L),t_VECSMALL);
    GEN dg=cgetg(lg(L),t_VECSMALL);
    GEN V;
    V = fixedfieldsympol(O, L, mod, gmael(gal,2,1), gun, sym, dg, x);
    P=(GEN)V[2];
    PL=(GEN)V[1];
  }
  if (flag==1)
    return gerepileupto(ltop,P);
  S = fixedfieldinclusion(O, PL);
  S = vectopol(S, (GEN) gal[4], (GEN) gal[5], mod, x);
  if (flag==0)
  {
    lbot = avma;
    res = cgetg(3, t_VEC);
    res[1] = (long) gcopy(P);
    res[2] = (long) gmodulcp(S, (GEN) gal[1]);
    return gerepile(ltop, lbot, res);
  }
  else
  {
    GEN PM,Pden;
    {
      struct galois_borne Pgb;
      long val=itos(gmael(gal,2,2));
      Pgb.l = gmael(gal,2,1);
      Pden = galoisborne(P, NULL, &Pgb, 1);
      if (Pgb.valabs > val)
      {
        if (DEBUGLEVEL>=4)
          fprintferr("GaloisConj:increase prec of p-adic roots of %ld.\n"
              ,Pgb.valabs-val);
        PL = rootpadicliftroots(P,PL,Pgb.l,Pgb.valabs);
        L = rootpadicliftroots((GEN) gal[1],L,Pgb.l,Pgb.valabs);
        mod = Pgb.ladicabs;
      }
    }
    PM = vandermondeinversemod(PL, P, Pden, mod);
    lbot = avma;
    if (y==-1)
      y = fetch_user_var("y");
    if (y<=x)
      err(talker,"priority of optional variable too high in galoisfixedfield");
    res = cgetg(4, t_VEC);
    res[1] = (long) gcopy(P);
    res[2] = (long) gmodulcp(S, (GEN) gal[1]);
    res[3] = (long) fixedfieldfactor(L,O,(GEN)gal[6],
        PM,Pden,mod,x,y);
    return gerepile(ltop, lbot, res);
  }
}

/*return 1 if gal is abelian, else 0*/
long 
galoistestabelian(GEN gal)
{
  pari_sp ltop=avma;
  GEN G;
  long test;
  gal = checkgal(gal);
  G=cgetg(3,t_VEC);
  G[1]=gal[7];
  G[2]=gal[8];
  test=group_isabelian(G);
  avma=ltop;
  return test;
}

GEN galoisisabelian(GEN gal, long flag)
{
  long i, j;
  long test, n;
  GEN M;
  gal = checkgal(gal);
  test=galoistestabelian(gal);
  if (!test) return gzero;
  if (flag==1)  return gun;
  if (flag) err(flagerr,"galoisisabelian");
  n=lg(gal[7]);
  M=cgetg(n,t_MAT);
  for(i=1;i<n;i++)
  {
    pari_sp btop;
    GEN P;
    long k;
    M[i]=lgetg(n,t_COL);
    btop=avma;
    P=perm_pow(gmael(gal,7,i),mael(gal,8,i));
    for(j=1;j<lg(gal[6]);j++)
      if (gegal(P,gmael(gal,6,j)))
	  break;
    avma=btop;
    if (j==lg(gal[6])) err(talker,"wrong argument in galoisisabelian");
    j--;
    for(k=1;k<i;k++)
    {
      mael(M,i,k)=lstoi(j%mael(gal,8,k));
      j/=mael(gal,8,k);
    }  
    mael(M,i,k++)=lstoi(mael(gal,8,i));
    for(  ;k<n;k++)
      mael(M,i,k)=zero;
  }
  return M;
}
GEN galoissubgroups(GEN G)
{
  pari_sp ltop=avma;
  GEN H;
  G = checkgal(G);
  H=cgetg(3,t_VEC);
  H[1]=G[7];
  H[2]=G[8];
  return gerepileupto(ltop,group_subgroups(H));
}

GEN galoissubfields(GEN G, long flag, long v)
{
  pari_sp ltop=avma;
  long i;
  GEN L = galoissubgroups(G);
  long l2 = lg(L);
  GEN p3 = cgetg(l2, t_VEC);
  for (i = 1; i < l2; ++i)
    p3[i] = (long) galoisfixedfield(G, gmael(L,i,1), flag, v);
  return gerepileupto(ltop,p3);
}

