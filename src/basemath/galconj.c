/*************************************************************************/
/**									**/
/**                           GALOIS CONJUGATES        		        **/
/**									**/
/*************************************************************************/
/* $Id$ */
#include "pari.h"
GEN
galoisconj(GEN nf)
{
  GEN     x, y, z;
  long    i, lz, v, av = avma;
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
  long    av = avma, i, n, v, nbauto;
  GEN     y, w, polr, p1, p2;
  n = lgef(x) - 3;
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
  long    av = avma, i, j, n, r1, ru, nbauto;
  GEN     x, y, w, polr, p1, p2;
  if (typ(nf) == t_POL)
    return galoisconj2pol(nf, nbmax, prec);
  nf = checknf(nf);
  x = (GEN) nf[1];
  n = lgef(x) - 3;
  if (n <= 0)
    return cgetg(1, t_VEC);
  r1 = itos(gmael(nf, 2, 1));
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
GEN vectosmall(GEN H)
{
  GEN V;
  long l,i;
  if ( typ(H) == t_VECSMALL )
    return H;
  if ( typ(H) == t_INT )
  {
    GEN u = cgetg(2, t_VECSMALL);
    u[1] = itos(H);
    return u;
  } 
  if (typ(H)!=t_VEC && typ(H)!=t_COL)
    err(typeer,"vectosmall");
  l=lg(H);
  V=cgetg(l,t_VECSMALL);
  for(i=1;i<l;i++)
    V[i]=itos((GEN)H[i]);
  return V;
}
/*Unclean*/
static GEN
myceil(GEN x)
{
  long e;
  GEN y;
  y=gcvtoi(x,&e);
  if (e<0) e=0;
  y=addii(y,shifti(gun,e));
  return y;
}

/*TODO: do it without transcendental means like sqrtint x real or
 *integer, y>=2 integer, return n long such that y^(n-1)<=x<y^n*/
long mylogint(GEN x, GEN y, long prec)
{
  ulong av=avma;
  long res=itos(myceil(gdiv(glog(x,prec),glog(y,prec))));
  avma=av;
  return res;
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
};
void
initborne(GEN T, GEN den, struct galois_borne *gb, long ppp)
{
  ulong   ltop = avma, av2;
  GEN     borne, borneroots, borneabs;
  int     i, j;
  int     n, extra;
  GEN     L, M, z;
  long    prec;
  prec = 2;
  for (i = 2; i < lg(T); i++)
    if (lg(T[i]) > prec)
      prec = lg(T[i]);
  L = roots(T, prec);
  n = lg(L) - 1;
  for (i = 1; i <= n; i++)
  {
    z = (GEN) L[i];
    if (signe(z[2]))
      break;
    L[i] = z[1];
  }
  M = vandermondeinverse(L, gmul(T, realun(prec)), den);
  borne = realzero(prec);
  for (i = 1; i <= n; i++)
  {
    z = gzero;
    for (j = 1; j <= n; j++)
      z = gadd(z, gabs(((GEN **) M)[j][i], prec));
    if (gcmp(z, borne) > 0)
      borne = z;
  }
  borneroots = realzero(prec);
  for (i = 1; i <= n; i++)
  {
    z = gabs((GEN) L[i], prec);
    if (gcmp(z, borneroots) > 0)
      borneroots = z;
  }
  borneabs = addsr(1, gpowgs(addsr(n, borneroots), n / ppp));
  borneroots = addsr(1, gmul(borne, borneroots));
  av2 = avma;
  /*We want to reduce the probability of hop. prob=2^(-2-extra) */
  extra = mylogint(mpfact(itos(racine(stoi(n))) + 2), gdeux, DEFAULTPREC);
  if (DEBUGLEVEL >= 4)
    fprintferr("GaloisConj:extra=%d are you happy?\n", extra);
  borneabs = gmul2n(gmul(borne, borneabs), 2 + extra);
  gb->valsol = mylogint(gmul2n(borneroots, 4), gb->l, prec);
  gb->valabs = mylogint(borneabs, gb->l, prec);
  gb->valabs =  max(gb->valsol,gb->valabs);
  if (DEBUGLEVEL >= 4)
    fprintferr("GaloisConj:val1=%ld val2=%ld\n", gb->valsol, gb->valabs);
  avma = av2;
  gb->bornesol = gerepileupto(ltop, myceil(borneroots));
  gb->ladicsol = gpowgs(gb->l, gb->valsol);
  gb->ladicabs = gpowgs(gb->l, gb->valabs);
}

struct galois_lift
{
  GEN     T;
  GEN     den;
  GEN     p;
  GEN     borne;
  GEN     L;
  GEN     Lden;
  GEN     ladic;
  long    e;
  GEN     Q;
  GEN     TQ;
};
/* Initialise la structure galois_lift */
GEN makeLden(GEN L,GEN den, struct galois_borne *gb)
{
  ulong ltop=avma;
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
  ulong   ltop, lbot;
  gl->T = T;
  gl->den = den;
  gl->p = p;
  gl->borne = gb->bornesol;
  gl->L = L;
  gl->Lden = Lden;
  gl->ladic = gb->ladicsol;
  ltop = avma;
  gl->e = mylogint(gmul2n(gb->bornesol, 1),p, DEFAULTPREC);
  gl->e = max(2,gl->e);
  lbot = avma;
  gl->Q = gpowgs(p, gl->e);
  gl->Q = gerepile(ltop, lbot, gl->Q);
  gl->TQ = Fp_pol_red(T,gl->Q);
}
/*
 * T est le polynome \sum t_i*X^i S est un Polmod T 
 * Retourne un vecteur Spow
 * verifiant la condition: i>=1 et t_i!=0 ==> Spow[i]=S^(i-1)*t_i 
 * Essaie d'etre efficace sur les polynomes lacunaires
 */
GEN
compoTS(GEN T, GEN S, GEN Q, GEN mod)
{
  GEN     Spow;
  int     i;
  Spow = cgetg(lgef(T) - 2, t_VEC);
  for (i = 3; i < lg(Spow); i++)
    Spow[i] = 0;
  Spow[1] = (long) polun[varn(S)];
  Spow[2] = (long) S;
  for (i = 2; i < lg(Spow) - 1; i++)
  {
    if (signe((GEN) T[i + 3]))
      for (;;)
      {
	int     k, l;
	for (k = 1; k <= (i >> 1); k++)
	  if (Spow[k + 1] && Spow[i - k + 1])
	    break;
	if ((k << 1) < i)
	{
	  Spow[i + 1] = (long) Fp_mul_mod_pol((GEN) Spow[k + 1], (GEN) Spow[i - k + 1],Q,mod);
	  break;
	}
	else if ((k << 1) == i)	
	{
	  Spow[i + 1] = (long) Fp_sqr_mod_pol((GEN) Spow[k + 1],Q,mod);
	  break;
	}
	for (k = i - 1; k > 0; k--)
	  if (Spow[k + 1])
	    break;
	if ((k << 1) < i)
	{
	  Spow[(k << 1) + 1] = (long) Fp_sqr_mod_pol((GEN) Spow[k + 1],Q,mod);
	  continue;
	}
	for (l = i - k; l > 0; l--)
	  if (Spow[l + 1])
	    break;
	if (Spow[i - l - k + 1])
	  Spow[i - k + 1] = (long) Fp_mul_mod_pol((GEN) Spow[i - l - k + 1], (GEN) Spow[l + 1],Q,mod);
	else
	  Spow[l + k + 1] = (long) Fp_mul_mod_pol((GEN) Spow[k + 1], (GEN) Spow[l + 1],Q,mod);
      }
  }
  for (i = 1; i < lg(Spow); i++)
    if (signe((GEN) T[i + 2]))
      Spow[i] = (long) Fp_mul_pol_scal((GEN) Spow[i], (GEN) T[i + 2],mod);
  return Spow;
}

/*
 * Calcule T(S) a l'aide du vecteur Spow
 */
static GEN
calcTS(GEN Spow, GEN P, GEN S, GEN Q, GEN mod)
{
  GEN     res = gzero;
  int     i;
  for (i = 1; i < lg(Spow); i++)
    if (signe((GEN) P[i + 2]))
      res = Fp_add(res, (GEN) Spow[i],NULL);
  res = Fp_mul_mod_pol(res,S,Q,mod);
  res=Fp_add_pol_scal(res,(GEN)P[2],mod);
  return res;
}

/*
 * Calcule T'(S) a l'aide du vecteur Spow
 */
static GEN
calcderivTS(GEN Spow, GEN P, GEN mod)
{
  GEN     res = gzero;
  int     i;
  for (i = 1; i < lg(Spow); i++)
    if (signe((GEN) P[i + 2]))
      res = Fp_add(res, Fp_mul_pol_scal((GEN) Spow[i], stoi(i),mod),NULL);
  return Fp_pol_red(res,mod);
}

/*
 * Soit P un polynome de \ZZ[X] , p un nombre premier , S\in\FF_p[X]/(Q) tel
 * que P(S)=0 [p,Q] Relever S en S_0 tel que P(S_0)=0 [p^e,Q]
 * Unclean stack.
 */
GEN
monomorphismlift(GEN P, GEN S, GEN Q, GEN p, long e)
{
  ulong   ltop, lbot;
  long    x;
  GEN     q, qold, qm1;
  GEN     W, Pr, Qr, Sr, Wr = gzero, Prold, Qrold, Spow;
  long    i,nb,mask;
  GEN    *gptr[2];
  if (DEBUGLEVEL >= 1)
    timer2();
  x = varn(P);
  q = p; qm1=gun; /*during the run, we have p*qm1=q*/
  nb=hensel_lift_accel(e, &mask);
  Pr = Fp_pol_red(P,q);
  Qr = (P==Q)?Pr:Fp_pol_red(Q, q);/*A little speed up for automorphismlift*/
  W=Fp_compo_mod_pol(deriv(Pr, x),S,Qr,q);
  W=Fp_inv_mod_pol(W,Qr,q);
  qold = p;
  Prold = Pr;
  Qrold = Qr;
  gptr[0] = &S;
  gptr[1] = &Wr;
  for (i=0; i<nb;i++)
  {
    qm1 = (mask&(1<<i))?sqri(qm1):mulii(qm1, q);
    q   =  mulii(qm1, p);
    Pr = Fp_pol_red(P, q);
    Qr = (P==Q)?Pr:Fp_pol_red(Q, q);/*A little speed up for automorphismlift*/
    ltop = avma;
    Sr = S;
    Spow = compoTS(Pr, Sr, Qr, q);
    if (i)
    {
      W = Fp_mul_mod_pol(Wr, calcderivTS(Spow, Prold,qold), Qrold, qold);
      W = Fp_neg(W, qold);
      W = Fp_add_pol_scal(W, gdeux, qold);
      W = Fp_mul_mod_pol(Wr, W, Qrold, qold);
    }
    Wr = W;
    S = Fp_mul_mod_pol(Wr, calcTS(Spow, Pr, Sr, Qr, q),Qr,q);
    lbot = avma;
    Wr = gcopy(Wr);
    S = Fp_sub(Sr, S,NULL);
    gerepilemanysp(ltop, lbot, gptr, 2);
    qold = q;
    Prold = Pr;
    Qrold = Qr;
  }
  if (DEBUGLEVEL >= 1)
    msgtimer("monomorphismlift()");
  return S;
}
/*
 * Soit T un polynome de \ZZ[X] , p un nombre premier , S\in\FF_p[X]/(T) tel
 * que T(S)=0 [p,T] Relever S en S_0 tel que T(S_0)=0 [T,p^e]
 * Unclean stack.
 */
GEN
automorphismlift(GEN S, struct galois_lift *gl)
{
  return  monomorphismlift(gl->T, S, gl->T, gl->p, gl->e);
}
/*
 * Verifie que S est une solution presque surement et calcule sa permutation
 */
static int
poltopermtest(GEN f, struct galois_lift *gl, GEN pf)
{
  ulong   ltop;
  GEN     fx, fp;
  long     i, j,ll;
  ll=lg(gl->L);
  fp = cgetg(ll, t_VECSMALL);
  ltop = avma;
  for (i = 1; i < ll; i++)
    fp[i] = 1;
  for (i = 1; i < ll; i++)
  {
    fx = Fp_poleval(f, (GEN) gl->L[i],gl->ladic);
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

struct galois_testlift
{
  long    n;
  long    f;
  long    g;
  GEN     bezoutcoeff;
  GEN     pauto;
};
/*
 * Si polb est un polynomes de Z[X] et pola un facteur modulo p, retourne b*v
 * telqu' il existe u et a tel que: a=pola [mod p] a*b=polb [mod p^e]
 * b*v+a*u=1 [mod p^e]
 */
GEN
bezout_lift_fact(GEN pola, GEN polb, GEN p, long e)
{
  long    i;
  GEN     ae, be, u, v, ae2, be2, s, t, pe, pe2, pem1, z, g;
  long    ltop = avma, lbot;
  long    nb, mask;
  if (DEBUGLEVEL >= 1)
    timer2();
  nb=hensel_lift_accel(e, &mask);
  ae = pola;
  be = Fp_poldivres(polb, ae, p, NULL);
  g = (GEN) Fp_pol_extgcd(ae, be, p, &u, &v)[2];	/* deg g = 0 */
  if (!gcmp1(g))
  {
    g = mpinvmod(g, p);
    u = Fp_mul_pol_scal(u,g,NULL);
    v = Fp_mul_pol_scal(v,g,NULL);
  }
  for (pe = p,pem1 = gun, i = 0; i < nb; i++)
  {
    pem1 = (mask&(1<<i))?sqri(pem1):mulii(pem1, pe);
    pe2  =  mulii(pem1, p);
    g = Fp_sub(polb, Fp_mul(ae, be,NULL),pe2);
    g = gdivexact(g, pe);
    z = Fp_mul(v, g, pe);
    t = Fp_poldivres(z, ae, pe, &s);
    t = Fp_add(Fp_mul(u, g,NULL), Fp_mul(t, be,NULL),pe);
    be2 = Fp_add(be, Fp_mul_pol_scal(t, pe,NULL),NULL);
    ae2 = Fp_add(ae, Fp_mul_pol_scal(s, pe,NULL),NULL);	/* already reduced mod pe2 */
    g = Fp_add(Fp_mul(u, ae2,NULL), Fp_mul(v, be2,NULL),pe2);
    g = Fp_add_pol_scal(Fp_neg(g,pe2),gun,pe2);
    g = gdivexact(g, pe);
    z = Fp_mul(v, g, pe);
    t = Fp_poldivres(z, ae, pe, &s);
    t = Fp_add(Fp_mul(u, g,NULL), Fp_mul(t, be,NULL),pe);
    u = Fp_add(u, Fp_mul_pol_scal(t, pe,NULL),NULL);
    v = Fp_add(v, Fp_mul_pol_scal(s, pe,NULL),NULL);
    pe = pe2;
    ae = ae2;
    be = be2;
  }
  lbot = avma;
  g = Fp_mul(v, be,NULL);
  g = gerepile(ltop, lbot, g);
  if (DEBUGLEVEL >= 1)
    msgtimer("bezout_lift_fact()");
  return g;
}
static long
inittestlift(GEN Tmod, long elift, struct galois_lift *gl,
	     struct galois_testlift *gt, GEN frob, long exit)
{
  ulong   ltop = avma;
  int     i, j;
  long    v;
  GEN     pe, autpow, plift;
  GEN     Tp, S;
  GEN    *gptr[2];
  if (DEBUGLEVEL >= 7)
    fprintferr("GaloisConj:Start of inittestlift():avma=%ld\n", avma);
  v = varn(gl->T);
  gt->n = lg(gl->L) - 1;
  gt->g = lg(Tmod) - 1;
  gt->f = gt->n / gt->g;
  Tp = Fp_pol_red(gl->T, gl->p);
  pe = gpowgs(gl->p, elift);
  S = Fp_pow_mod_pol(polx[v],pe, Tp,gl->p);
  plift = automorphismlift(S, gl);
  if (DEBUGLEVEL >= 9)
    fprintferr("GaloisConj:plift = %Z\n", plift);
  if (DEBUGLEVEL >= 7)
    fprintferr("GaloisConj:inittestlift()1:avma=%ld\n", avma);
  if (frob)
  {
    GEN     tlift;
    tlift = Fp_centermod(Fp_mul_pol_scal(plift,gl->den,gl->Q), gl->Q);
    if (poltopermtest(tlift, gl, frob))
    {
      avma = ltop;
      return 1;
    }
  }
  if (exit)
    return 0;
  if (DEBUGLEVEL >= 7)
    fprintferr("GaloisConj:inittestlift()2:avma=%ld\n", avma);
  gt->bezoutcoeff = cgetg(gt->g + 1, t_VEC);
  for (i = 1; i <= gt->g; i++)
    gt->bezoutcoeff[i] = (long) bezout_lift_fact((GEN) Tmod[i], gl->T, gl->p, gl->e);
  if (DEBUGLEVEL >= 1)
    timer2();
  gt->pauto = cgetg(gt->f + 1, t_VEC);
  gt->pauto[1] = (long) polx[v];
  gt->pauto[2] = (long) plift;
  if (DEBUGLEVEL >= 7)
    fprintferr("GaloisConj:inittestlift()3:avma=%ld\n", avma);
  if (gt->f > 2)
  {

    autpow = cgetg(gt->n, t_VEC);
    autpow[1] = (long) plift;
    for (i = 2; i < gt->n; i++)
      autpow[i] = (long) Fp_mul_mod_pol((GEN) autpow[i - 1],plift,gl->TQ,gl->Q);
    if (DEBUGLEVEL >= 7)
      fprintferr("GaloisConj:inittestlift()4:avma=%ld\n", avma);
    for (i = 3; i <= gt->f; i++)
    {
      GEN     s, P;
      int     n;
      P = (GEN) gt->pauto[i - 1];
      n = lgef(P) - 3;
      if (n == 0)
	gt->pauto[i] = (long) scalarpol((GEN)P[2],v);
      else
      {
	ulong   ltop = avma;
	GEN     p1;
	s = scalarpol((GEN) P[2],v);
	for (j = 1; j < n; j++)
	  s = Fp_add(s, Fp_mul_pol_scal((GEN) autpow[j], (GEN) P[j + 2],NULL),NULL);
	p1 = Fp_mul_pol_scal((GEN) autpow[n], (GEN) P[n + 2],NULL);
	s = Fp_add(s, p1,gl->Q);
	if (DEBUGLEVEL >= 7)
	  fprintferr("GaloisConj:inittestlift()5:avma=%ld\n", avma);
	gt->pauto[i] = (long) gerepileupto(ltop,s);
      }
    }
    if (DEBUGLEVEL >= 1)
      msgtimer("frobenius power");
  }
  gptr[0] = &gt->bezoutcoeff;
  gptr[1] = &gt->pauto;
  gerepilemany(ltop, gptr, 2);
  if (DEBUGLEVEL >= 7)
    fprintferr("GaloisConj:End of inittestlift():avma=%ld\n", avma);
  return 0;
}

/*
 * 
 */
long
frobeniusliftall(GEN sg, GEN *psi, struct galois_lift *gl,
		 struct galois_testlift *gt, GEN frob)
{
  ulong   ltop = avma, av, ltop2;
  long    d, N, z, m, c;
  int     i, j, k;
  GEN     pf, u, v, C;
  m = gt->g;
  c = lg(sg) - 1;
  d = m / c;
  pf = cgetg(m, t_VECSMALL);
  *psi = pf;
  ltop2 = avma;
  N = itos(gdiv(mpfact(m), gmul(stoi(c), gpowgs(mpfact(d), c))));
  avma = ltop2;
  C=cgetg(gt->f+1,t_VEC);
  for(i=1;i<=gt->f;i++)
  {
    C[i]=lgetg(gt->g+1,t_VECSMALL);
    for(j=1;j<=gt->g;j++)
      mael(C,i,j)=0;
  }
  v = Fp_mul_mod_pol((GEN)gt->pauto[2], (GEN) gt->bezoutcoeff[m],gl->TQ,gl->Q);
  for (i = 1; i < m; i++)
    pf[i] = 1 + i / d;
  av = avma;
  for (i = 0;; i++)
  {
    u = v;
    if (DEBUGLEVEL >= 4 && i%(1+N/100)==0)
    {
      fprintferr("GaloisConj:Testing %Z:%d:%Z:", sg, i, pf);
      timer2();
    }
    for (j = 1; j < m; j++)
    {
      long h;
      h=sg[pf[j]] + 1;
      if (!mael(C,h,j))
      {
	ulong av3=avma;
	mael(C,h,j)= lclone(Fp_mul_mod_pol((GEN) gt->pauto[sg[pf[j]] + 1], 
					   (GEN) gt->bezoutcoeff[j],gl->TQ,gl->Q));
	avma=av3;
      }
      u = Fp_add(u, gmael(C,h,j),NULL);
    }
    u = Fp_centermod(Fp_mul_pol_scal(u,gl->den,gl->Q), gl->Q);
    if (poltopermtest(u, gl, frob))
    {
      if (DEBUGLEVEL >= 4 )
	msgtimer("");
      for(i=1;i<=gt->f;i++)     
	for(j=1;j<=gt->g;j++)
	  if(mael(C,i,j))
	    gunclone(gmael(C,i,j));
      avma = ltop2;
      return 1;
    }
    if (DEBUGLEVEL >= 4 && i%(1+N/100)==N/100)
      msgtimer("");
    avma = av;
    if (i == N - 1)
      break;
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
  }
  avma = ltop;
  for(i=1;i<=gt->f;i++)     
    for(j=1;j<=gt->g;j++)
      if(mael(C,i,j))
	gunclone(gmael(C,i,j));
  *psi = NULL;
  return 0;
}
/*
  test tous les lifts possibles a l'aide de frobeniuslift,
  pour le nombre premier p, le sous-groupe sg et l'exposant e.
  F factorisation p-adique de T.
  retourne gzero ou une permutation de L
*/
#if 0
GEN frobeniusliftallsoft(GEN F,GEN sg,long e,GEN *psi,struct galois_lift *gl)
{
  ulong ltop=avma,av,ltop2;
  long d,N,z,m,c;
  long x;
  int i,j,k;
  GEN pf,u,v,xmod,ff;
  x=varn(F[1]);
  m=lg(F)-1;
  c=lg(sg)-1;
  d=m/c;
  ff=cgetg(lg(gl->L),t_VECSMALL);
  pf=cgetg(m,t_VECSMALL);
  *psi=pf;
  ltop2=avma;
  N=itos(gdiv(mpfact(m),gmul(stoi(c),gpowgs(mpfact(d),c))));
  avma=ltop2;
  for(i=1;i<m;i++)
    pf[i]=1+i/d;
  xmod=gmul(polx[varn(F[1])],gmodulcp(gun,gl->p));
  v=powgi(gmodulcp(xmod,(GEN)F[m]),gpowgs(gl->p,e));
  av=avma;
  for(i=0;;i++)
  {
    u=v;
    if (DEBUGLEVEL>=4) fprintferr("GaloisConj:Lifting %Z:%d:%Z\n",sg,i,pf);
    for(j=1;j<m;j++)
      u=chinois(u,powgi(gmodulcp(xmod,(GEN)F[j]),gpowgs(gl->p,e*sg[pf[j]])));
    frobeniuslift(u,ff,gl);
    if(frobeniuslift(u,ff,gl))
    {
      avma=ltop2;
      return ff;
    }
    avma=av;
    if(i==N-1)
      break;
    for(j=2;j<m && pf[j-1]>=pf[j];j++);
    for(k=1;k<j-k && pf[k]!=pf[j-k];k++)
    {
      z=pf[k];
      pf[k]=pf[j-k];
      pf[j-k]=z;
    }
    for(k=j-1;pf[k]>=pf[j];k--);
	z=pf[j];pf[j]=pf[k];pf[k]=z;
  }
  avma=ltop;
  *psi=NULL;
  return gzero;
}
#endif
/*
 * applique une permutation t a un vecteur s sans duplication
 * Propre si s est un VECSMALL
 */
static GEN
applyperm(GEN s, GEN t)
{
  GEN     u;
  int     i;
  if (lg(s) < lg(t))
    err(talker, "First permutation shorter than second in applyperm");
  u = cgetg(lg(s), typ(s));
  for (i = 1; i < lg(s); i++)
    u[i] = s[t[i]];
  return u;
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

/*
 * structure contenant toutes les données pour le tests des permutations:
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
  ulong   ltop = avma, lbot;
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
  ulong   ltop;
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
  td->TM = gtrans(M);
  settyp(td->TM, t_VEC);
  for (i = 1; i < lg(td->TM); i++)
    settyp(td->TM[i], t_VEC);
  if (DEBUGLEVEL >= 8)
    fprintferr("GaloisConj:Sortie Init Test\n");
}

/*
 * liberer les clones de la structure galois_test
 * 
 * Reservé a l'accreditation ultra-violet:Liberez les clones! Paranoia(tm)
 */
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
  ulong   ltop = avma;
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
  ulong   av = avma;
  GEN     P, V;
  int     i, j;
  int     n = lg(td->L) - 1;
  if (DEBUGLEVEL >= 8)
    fprintferr("GaloisConj:Entree Verifie Test\n");
  P = applyperm(td->L, pf);
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
  ulong   av, avm = avma, av2;
  long    a, b, c, d, n;
  GEN     pf, x, ar, y, *G;
  int     N, cx, p1, p2, p3, p4, p5, p6;
  int     i, j, hop = 0;
  GEN     V, W;
  if (DEBUGLEVEL >= 1)
    timer2();
  a = lg(F) - 1;
  b = lg(F[1]) - 1;
  c = lg(B) - 1;
  d = lg(B[1]) - 1;
  n = a * b;
  s = (b + s) % b;
  pf = cgetg(n + 1, t_VECSMALL);
  av = avma;
  ar = alloue_ardoise(a, 1 + lg(td->ladic));
  x = cgetg(a + 1, t_VECSMALL);
  y = cgetg(a + 1, t_VECSMALL);
  G = (GEN *) cgetg(a + 1, t_VECSMALL);	/* Don't worry */
  av2 = avma;
  W = (GEN) td->PV[td->ordre[n]];
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
  N = itos(gpowgs(stoi(b), c * (d - 1))) / cut;
  avma = av2;
  if (DEBUGLEVEL >= 4)
    fprintferr("GaloisConj:I will try %d permutations\n", N);
  for (cx = 0; cx < N; cx++)
  {
    if (DEBUGLEVEL >= 2 && cx % 1000 == 999)
      fprintferr("%d%% ", (100 * cx) / N);
    if (cx)
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
	V = gzero;
	for (p2 = 1 + p4, p3 = 1 + x[p1]; p2 <= b; p2++)
	{
	  V = addii(V, ((GEN **) W)[G[p6][p3]][G[p1][p2]]);
	  p3 += s;
	  if (p3 > b)
	    p3 -= b;
	}
	p3 = 1 + x[p1] - s;
	if (p3 <= 0)
	  p3 += b;
	for (p2 = p4; p2 >= 1; p2--)
	{
	  V = addii(V, ((GEN **) W)[G[p6][p3]][G[p1][p2]]);
	  p3 -= s;
	  if (p3 <= 0)
	    p3 += b;
	}
	gaffect((GEN) V, (GEN) ar[p1]);
      }
    V = gzero;
    for (p1 = 1; p1 <= a; p1++)
      V = addii(V, (GEN) ar[p1]);
    if (padicisint(V, td))
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
	avma = av;
	if (DEBUGLEVEL >= 1)
	  msgtimer("testpermutation(%d)", cx + 1);
	if (DEBUGLEVEL >= 2 && hop)
	  fprintferr("GaloisConj:%d hop sur %d iterations\n", hop, cx + 1);
	return pf;
      }
      else
	hop++;
    }
    avma = av2;
  }
  avma = avm;
  if (DEBUGLEVEL >= 1)
    msgtimer("testpermutation(%d)", N);
  if (DEBUGLEVEL >= 2 && hop)
    fprintferr("GaloisConj:%d hop sur %d iterations\n", hop, N);
  return gzero;
}
/* Compute generators for the subgroup of (Z/nZ)* given in HNF. 
 * I apologize for the following spec:
 * If zns=znstar(2) then
 * zn2=vectosmall((GEN)zns[2]);
 * zn3=lift((GEN)zns[3]);
 * gen and ord : VECSMALL of length lg(zn3).
 * the result is in gen. 
 * ord contains the relatives orders of the generators.
 */
GEN hnftogeneratorslist(long n, GEN zn2, GEN zn3, GEN lss, GEN gen, GEN ord)
{
  ulong ltop=avma;
  int j,h;
  GEN m=stoi(n);
  for (j = 1; j < lg(gen); j++)
  {
    gen[j] = 1;
    for (h = 1; h < lg(lss); h++)
      gen[j] = (gen[j] * itos(powmodulo((GEN)zn3[h],gmael(lss,j,h),m)))% n;
    ord[j] = zn2[j] / itos(gmael(lss,j,j));
  }
  avma=ltop;
  return gen;
}
/* Compute the elements of the subgroup of (Z/nZ)* given in HNF. 
 * I apologize for the following spec:
 * If zns=znstar(2) then
 * zn2=vectosmall((GEN)zns[2]);
 * zn3=lift((GEN)zns[3]);
 * card=cardinal of the subgroup(i.e phi(n)/det(lss))
 */
GEN
hnftoelementslist(long n, GEN zn2, GEN zn3, GEN lss, long card)
{
  ulong   ltop;
  GEN     sg, gen, ord;
  int     k, j, l;
  sg = cgetg(1 + card, t_VECSMALL);
  ltop=avma;
  gen = cgetg(lg(zn3), t_VECSMALL);
  ord = cgetg(lg(zn3), t_VECSMALL);
  sg[1] = 1;
  hnftogeneratorslist(n,zn2,zn3,lss,gen,ord);
  for (j = 1, l = 1; j < lg(gen); j++)
  {
    int     c = l * (ord[j] - 1);
    for (k = 1; k <= c; k++)	/* I like it */
      sg[++l] = (sg[k] * gen[j]) % n;
  }
  avma=ltop;
  return sg;
}

/*
 * Calcule la liste des sous groupes de \ZZ/m\ZZ d'ordre divisant p et
 * retourne la liste de leurs elements
 */
GEN
listsousgroupes(long m, long p)
{
  ulong   ltop = avma, lbot;
  GEN     zns, lss, sg, res, zn2, zn3;
  int     k, card, i, phi;
  if (m == 2)
  {
    res = cgetg(2, t_VEC);
    sg = cgetg(2, t_VECSMALL);
    res[1] = (long) sg;
    sg[1] = 1;
    return res;
  }
  zns = znstar(stoi(m));
  phi = itos((GEN) zns[1]);
  zn2 = vectosmall((GEN)zns[2]);
  zn3 = lift((GEN)zns[3]);
  lss = subgrouplist((GEN) zns[2], 0);
  lbot = avma;
  res = cgetg(lg(lss), t_VEC);
  for (k = 1, i = lg(lss) - 1; i >= 1; i--)
  {
    long    av;
    av = avma;
    card = phi / itos(det((GEN) lss[i]));
    avma = av;
    if (p % card == 0)
      res[k++] = (long) hnftoelementslist(m,zn2,zn3,(GEN)lss[i],card);
  }
  setlg(res,k);
  return gerepileupto(ltop,gcopy(res));
}

/* retourne la permutation identite */
GEN
permidentity(long l)
{
  GEN     perm;
  int     i;
  perm = cgetg(l + 1, t_VECSMALL);
  for (i = 1; i <= l; i++)
    perm[i] = i;
  return perm;
}

/* Calcule les orbites d'une permutation 
 * ou d'un ensemble de permutations donne par un vecteur.
 */
GEN
permorbite(GEN v)
{
  ulong   ltop = avma, lbot;
  int     i, j, k, l, m, n, o, p, flag;
  GEN     bit, cycle, cy, u;
  if (typ(v) == t_VECSMALL)
  {
    u = cgetg(2, t_VEC);
    u[1] = (long) v;
    v = u;
  }
  n = lg(v[1]);
  cycle = cgetg(n, t_VEC);
  bit = cgetg(n, t_VECSMALL);
  for (i = 1; i < n; i++)
    bit[i] = 0;
  for (k = 1, l = 1; k < n;)
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
	  j = ((long **) v)[o][cy[p]];
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
/* Calcule un polynome R de la variable x definissant le corps fixe de
 * T pour les orbites O tel que R est sans-facteur carre modulo mod et
 * modulo l. Retourne dans U les racines de R APRES R dans la pile*/

GEN
corpsfixeorbitemod(GEN L, GEN O, long x, GEN mod, GEN l, GEN p, GEN *U)
{
  ulong   ltop = avma, lbot=0, av=0, av2;/*keep compiler happy (2)*/
  GEN     g, p1, PL, *gptr[2],dg;
  int     i, j, d, dmax;
  PL = cgetg(lg(O), t_COL);
  av2 = avma;
  dmax = lg(L) + 1;
  d = 0;
  for(d = 0; d <= dmax; d = (d > 0 ? -d : 1 - d))
  {
    avma = av2;
    g = polun[x];
    for (i = 1; i < lg(O); i++)
    {
      p1 = addsi(d, (GEN) L[mael(O,i,1)]);
      for (j = 2; j < lg(O[i]); j++)
	p1 = modii(mulii(p1, addsi(d, (GEN) L[mael(O,i,j)])),mod);
      PL[i] = (long) p1;
      g = Fp_mul(g, deg1pol(gun,negi(p1),x),mod);
    }
    lbot = avma;
    g = Fp_centermod(g,mod);
    av = avma;
    if (DEBUGLEVEL >= 6)
      fprintferr("GaloisConj:corps fixe:%d:%Z\n", d, g);
    dg=deriv(g, x);
    if (lgef(Fp_pol_gcd(g,dg,l))==3 && (p==gun || lgef(Fp_pol_gcd(g,dg,p))==3))
      break;
  } 
  if (d > dmax)
    err(talker, "prime too small in corpsfixeorbitemod");
  avma = av;
  *U = gcopy(PL);
  gptr[0] = &g;
  gptr[1] = U;
  gerepilemanysp(ltop, lbot, gptr, 2);
  return g;
}

/*
 * Calcule l'inclusion de R dans T i.e. S telque T|R\compo S
 * Ne recopie pas PL.
 */
static GEN
corpsfixeinclusion(GEN O, GEN PL)
{
  GEN     S;
  int     i, j;
  S = cgetg((lg(O) - 1) * (lg(O[1]) - 1) + 1, t_COL);
  for (i = 1; i < lg(O); i++)
    for (j = 1; j < lg(O[i]); j++)
      S[((GEN *) O)[i][j]] = PL[i];
  return S;
}

/* Calcule l'inverse de la matrice de van der Monde de T multiplie par den */
GEN
vandermondeinverse(GEN L, GEN T, GEN den)
{
  ulong   ltop = avma, lbot;
  int     i, j, n = lg(L);
  long    x = varn(T);
  GEN     M, P, Tp;
  M = cgetg(n, t_MAT);
  Tp = deriv(T, x);
  for (i = 1; i < n; i++)
  {
    M[i] = lgetg(n, t_COL);
    P = gdiv(gdeuc(T, gsub(polx[x], (GEN) L[i])), poleval(Tp, (GEN) L[i]));
    for (j = 1; j < n; j++)
      ((GEN *) M)[i][j] = P[1 + j];
  }
  lbot = avma;
  M = gmul(den, M);
  return gerepile(ltop, lbot, M);
}
/*Usually mod is bigger than than den so there is no need to reduce it.*/
GEN
vandermondeinversemod(GEN L, GEN T, GEN den, GEN mod)
{
  ulong   av;
  int     i, j, n = lg(L);
  long    x = varn(T);
  GEN     M, P, Tp;
  M = cgetg(n, t_MAT);
  av=avma;
  Tp = gclone(Fp_pol_red(deriv(T, x),mod)); /*clone*/
  avma=av;
  for (i = 1; i < n; i++)
  {
    GEN z;
    av = avma;
    z = mpinvmod(Fp_poleval(Tp, (GEN) L[i],mod),mod);
    z = modii(mulii(den,z),mod);
    P = Fp_mul_pol_scal(Fp_deuc(T, deg1pol(gun,negi((GEN) L[i]),x),mod), z, mod); 
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
  long n = lg(v),i,k,av;
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
  long n = lg(L),i,k,av;
  GEN z = cgetg(n+1,t_POL),p1,p2,mod2;
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
/*
 * factorise partiellement n sous la forme n=d*u*f^2 ou d est un
 * discriminant fondamental et u n'est pas un carre parfait et
 * retourne u*f 
 * Note: Parfois d n'est pas un discriminant (congru a 3 mod 4).
 * Cela se produit si u est congrue a 3 mod 4.
 */
GEN
corediscpartial(GEN n)
{
  ulong   av = avma;
  long i,r,s;
  GEN fa, p1, p2, p3, res = gun, res2 = gun, res3=gun;
  /*d=res,f=res2,u=res3*/
  if (gcmp1(n))
    return gun;
  fa = auxdecomp(n, 0);
  p1 = (GEN) fa[1];
  p2 = (GEN) fa[2];
  for (i = 1; i < lg(p1) - 1; i++)
  {
    p3 = (GEN) p2[i];
    if (mod2(p3))
      res = mulii(res, (GEN) p1[i]);
    if (!gcmp1(p3))
      res2 = mulii(res2, gpow((GEN) p1[i], shifti(p3, -1), 0));
  }
  p3 = (GEN) p2[i];
  if (mod2(p3))		/* impaire: verifions */
  {
    if (!gcmp1(p3))
      res2 = mulii(res2, gpow((GEN) p1[i], shifti(p3, -1), 0));
    if (isprime((GEN) p1[i]))
      res = mulii(res, (GEN) p1[i]);
    else
      res3 = (GEN)p1[i];
  }
  else			/* paire:OK */
    res2 = mulii(res2, gpow((GEN) p1[i], shifti(p3, -1), 0));
  r = mod4(res);
  if (signe(res) < 0)
    r = 4 - r;
  s = mod4(res3);/*res2 est >0*/
  if (r == 3 && s!=3)
    /*d est n'est pas un discriminant mais res2 l'est: corrige*/
    res2 = gmul2n((GEN) res2, -1);
  return gerepileupto(av,gmul(res2,res3));
}

/* Calcule la puissance exp d'une permutation decompose en cycle */
GEN
permcyclepow(GEN O, long exp)
{
  int     j, k, n;
  GEN     p;
  for (n = 0, j = 1; j < lg(O); j++)
    n += lg(O[j]) - 1;
  p = cgetg(n + 1, t_VECSMALL);
  for (j = 1; j < lg(O); j++)
  {
    n = lg(O[j]) - 1;
    for (k = 1; k <= n; k++)
      p[((long **) O)[j][k]] = ((long **) O)[j][1 + (k + exp - 1) % n];
  }
  return p;
}

/*
 * Casse l'orbite O en sous-orbite d'ordre premier correspondant a des
 * puissance de l'element
 */
GEN
splitorbite(GEN O)
{
  ulong   ltop = avma, lbot;
  int     i, n;
  GEN     F, fc, res;
  n = lg(O[1]) - 1;
  F = factor(stoi(n));
  fc = cgetg(lg(F[1]), t_VECSMALL);
  for (i = 1; i < lg(fc); i++)
    fc[i] = itos(powgi(((GEN **) F)[1][i], ((GEN **) F)[2][i]));
  lbot = avma;
  res = cgetg(3, t_VEC);
  res[1] = lgetg(lg(fc), t_VEC);
  res[2] = lgetg(lg(fc), t_VECSMALL);
  for (i = 1; i < lg(fc); i++)
  {
    ((GEN **) res)[1][lg(fc) - i] = permcyclepow(O, n / fc[i]);
    ((GEN *) res)[2][lg(fc) - i] = fc[i];
  }
  return gerepile(ltop, lbot, res);
}

/*
 * structure qui contient l'analyse du groupe de Galois par etude des degres
 * de Frobenius:
 * 
 * p: nombre premier a relever deg: degre du lift à effectuer pgp: plus grand
 * diviseur premier du degre de T. exception: 1 si le pgp-Sylow est
 * non-cyclique. l: un nombre premier tel que T est totalement decompose
 * modulo l ppp:  plus petit diviseur premier du degre de T. primepointer:
 * permet de calculer les premiers suivant p.
 */
struct galois_analysis
{
  long    p;
  long    deg;
  long    exception;
  long    ord;
  long    l;
  long    ppp;
  long    p4;
  byteptr primepointer;
};
/* peut-etre on peut accelerer(distinct degree factorisation */
void
galoisanalysis(GEN T, struct galois_analysis *ga, long calcul_l)
{
  ulong   ltop = avma;
  long    n, p, ex, plift, nbmax, nbtest, exist6 = 0, p4 = 0;
  GEN     F, fc;
  byteptr primepointer, pp = 0;
  long    pha, ord, deg, ppp, pgp, ordmax = 0, l = 0;
  int     i;
  /* Etude du cardinal: */
  /* Calcul de l'ordre garanti d'un sous-groupe cyclique */
  /* Tout les groupes d'ordre n sont cyclique ssi gcd(n,phi(n))==1 */
  if (DEBUGLEVEL >= 1)
    timer2();
  n = degree(T);
  F = factor(stoi(n));
  fc = cgetg(lg(F[1]), t_VECSMALL);
  for (i = 1; i < lg(fc); i++)
    fc[i] = itos(powgi(((GEN **) F)[1][i], ((GEN **) F)[2][i]));
  ppp = itos(((GEN **) F)[1][1]);	/* Plus Petit diviseur Premier */
  pgp = itos(((GEN **) F)[1][lg(F[1]) - 1]);	/* Plus Grand diviseur
						 * Premier */
  pha = 1;
  ord = 1;
  ex = 0;
  for (i = lg(F[1]) - 1; i > 0; i--)
  {
    p = itos(((GEN **) F)[1][i]);
    if (pha % p != 0)
    {
      ord *= p;
      pha *= p - 1;
    }
    else
    {
      ex = 1;
      break;
    }
    if (!gcmp1(((GEN **) F)[2][i]))
      break;
  }
  plift = 0;
  /* Etude des ordres des Frobenius */
  nbmax = n >> 1;
  nbmax = max(8, nbmax);	/* Nombre maxi d'éléments à tester */
  nbtest = 0;
  deg = 0;
  for (p = 0, primepointer = diffptr; 
       plift == 0 
	 || (nbtest < nbmax && ord != n && (nbtest <=6 || ord != (n>>1))) 
	 || (n == 24 && exist6 == 0 && p4 == 0);)
  {
    long    u, s, c;
    GEN     gp;
    c = *primepointer++;
    if (!c)
      err(primer1);
    p += c;
    if (p <= (n << 1))
      continue;
    gp=stoi(p);
    if (Fp_is_squarefree(T,gp))
    {
      s=Fp_pol_nbfact(T,gp);
      if (n%s)
      {
	avma = ltop;
	if (DEBUGLEVEL >= 2)
	  fprintferr("GaloisAnalysis:non Galois for p=%ld\n", p);
	ga->p = p;
	ga->deg = 0;
	return;		/* Not a Galois polynomial */
      }
      s = n/s;
      if (l == 0 && s == 1)
	l = p;
      nbtest++;
      if (nbtest > (3 * nbmax) && (n == 60 || n == 75))
	break;
      if (s % 6 == 0)
	exist6 = 1;
      if (p4 == 0 && s == 4)
	p4 = p;
      if (DEBUGLEVEL >= 6)
	fprintferr("GaloisAnalysis:Nbtest=%ld,plift=%ld,p=%ld,s=%ld,ord=%ld\n",
		   nbtest, plift, p, s, ord);
      if (s > ordmax)
	ordmax = s;
      if (s >= ord)		/* Calcul de l'exposant distinguant minimal
				 * garanti */
      {
	if (s * ppp == n)	/* Tout sous groupe d'indice ppp est distingué */
	  u = s;
	else			/* Théorème de structure des groupes
				   * hyper-résoluble */
	{
	  u = 1;
	  for (i = lg(fc) - 1; i > 0; i--)
	  {
	    if (s % fc[i] == 0)
	      u *= fc[i];
	    else
	      break;
	  }
	}
	if (u != 1)
	{
	  if (!ex || s > ord || (s == ord && (plift == 0 || u > deg)))
	  {
	    deg = u;
	    ord = s;
	    plift = p;
	    pp = primepointer;
	    ex = 1;
	  }
	}
	else if (!ex && (plift == 0 || s > ord))
	  /*
	   * J'ai besoin de plus de connaissance sur les p-groupes, surtout
	   * pour p=2;
	   */
	{
	  deg = pgp;
	  ord = s;
	  plift = p;
	  pp = primepointer;
	  ex = 0;
	}
      }
    }
  }
  if (plift == 0 || ((n == 36 || n == 48) && !exist6)
      || (n == 56 && ordmax == 7) || (n == 60 && ordmax == 5) || (n == 72
								  && !exist6)
      || (n == 80 && ordmax == 5))
  {
    deg = 0;
    err(warner, "Galois group almost certainly not weakly super solvable");
  }
  avma = ltop;
  if (calcul_l)
  {
    ulong   av;
    long    c;
    av = avma;
    while (l == 0)
    {
      c = *primepointer++;
      if (!c)
	err(primer1);
      p += c;
      if (Fp_is_totally_split(T,stoi(p)))
	l = p;
      avma = av;
    }
    avma = ltop;
  }
  ga->p = plift;
  ga->exception = ex;
  ga->deg = deg;
  ga->ord = ord;
  ga->l = l;
  ga->primepointer = pp;
  ga->ppp = ppp;
  ga->p4 = p4;
  if (DEBUGLEVEL >= 4)
    fprintferr("GaloisAnalysis:p=%ld l=%ld exc=%ld deg=%ld ord=%ld ppp=%ld\n",
               p, l, ex, deg, ord, ppp);
  if (DEBUGLEVEL >= 1)
    msgtimer("galoisanalysis()");
}

/* Groupe A4 */
GEN
a4galoisgen(GEN T, struct galois_test *td)
{
  ulong   ltop = avma, av, av2;
  long    i, j, k;
  long    n;
  long    N, hop = 0;
  long  **O;
  GEN    *ar, **mt;		/* tired of casting */
  GEN     t, u;
  GEN     res, orb, ry;
  GEN     pft, pfu, pfv;
  n = degree(T);
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
    fprintferr("A4GaloisConj:tau=%Z \n", u);
  avma = av2;
  orb = cgetg(3, t_VEC);
  orb[1] = (long) pft;
  orb[2] = (long) pfu;
  if (DEBUGLEVEL >= 4)
    fprintferr("A4GaloisConj:orb=%Z \n", orb);
  O = (long**)permorbite(orb);
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
  liftpow[1] = (long) automorphismlift(u, gl);
  for (i = 2; i < lg(liftpow); i++)
    liftpow[i] = (long) Fp_mul_mod_pol((GEN) liftpow[i - 1], (GEN) liftpow[1],gl->TQ,gl->Q);
}
static long
s4test(GEN u, GEN liftpow, struct galois_lift *gl, GEN phi)
{
  ulong ltop=avma;
  GEN     res;
  int     bl,i,d = lgef(u)-2;
  if (DEBUGLEVEL >= 6)
    timer2();
  res = (GEN) scalarpol((GEN)u[2],varn(u));
  for (i = 1; i < d ; i++)
  {
    GEN z;
    z = Fp_mul_pol_scal((GEN) liftpow[i], (GEN) u[i + 2],NULL);
    res = Fp_add(res,z ,gl->Q);
  }
  res = Fp_centermod(Fp_mul_pol_scal(res,gl->den,gl->Q), gl->Q);
  if (DEBUGLEVEL >= 6)
    msgtimer("s4test()");
  bl = poltopermtest(res, gl, phi);
  avma=ltop;
  return bl;
}
static GEN
s4releveauto(GEN misom,GEN Tmod,GEN Tp,GEN p,long a1,long a2,long a3,long a4,long a5,long a6)
{
  ulong ltop=avma;
  GEN u1,u2,u3,u4,u5;
  GEN pu1,pu2,pu3,pu4;
  pu1=Fp_mul( (GEN) Tmod[a2], (GEN) Tmod[a1],p);
  u1 = Fp_chinese_coprime(gmael(misom,a1,a2),gmael(misom,a2,a1),
			 (GEN) Tmod[a2], (GEN) Tmod[a1],pu1,p);
  pu2=Fp_mul( (GEN) Tmod[a4], (GEN) Tmod[a3],p);
  u2 = Fp_chinese_coprime(gmael(misom,a3,a4),gmael(misom,a4,a3),
			 (GEN) Tmod[a4], (GEN) Tmod[a3],pu2,p);
  pu3=Fp_mul( (GEN) Tmod[a6], (GEN) Tmod[a5],p);
  u3 = Fp_chinese_coprime(gmael(misom,a5,a6),gmael(misom,a6,a5),
			 (GEN) Tmod[a6], (GEN) Tmod[a5],pu3,p);
  pu4=Fp_mul(pu1,pu2,p);
  u4 = Fp_chinese_coprime(u1,u2,pu1,pu2,pu4,p);
  u5 = Fp_chinese_coprime(u4,u3,pu4,pu3,Tp,p);
  return gerepileupto(ltop,u5);
}
GEN
s4galoisgen(struct galois_lift *gl)
{
  struct galois_testlift gt;
  ulong   ltop = avma, av, ltop2;
  GEN     Tmod, isom, isominv, misom;
  int     i, j;
  GEN     sg;
  GEN     sigma, tau, phi;
  GEN     res, ry;
  GEN     pj;
  GEN     p,Q,TQ,Tp;
  GEN     bezoutcoeff, pauto, liftpow;

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
  Tp = Fp_pol_red(gl->T,p);
  TQ = gl->TQ;
  Tmod = lift((GEN) factmod(gl->T, p)[1]);
  isom = cgetg(lg(Tmod), t_VEC);
  isominv = cgetg(lg(Tmod), t_VEC);
  misom = cgetg(lg(Tmod), t_MAT);
  inittestlift(Tmod, 1, gl, &gt, NULL, 0);
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
      mael(misom,i,j) = (long) Fp_compo_mod_pol((GEN) isominv[i],(GEN) isom[j],
						(GEN) Tmod[j],p);
  liftpow = cgetg(24, t_VEC);
  av = avma;
  for (i = 0; i < 3; i++)
  {
    ulong   av2;
    GEN     u;
    int     j1, j2, j3;
    ulong   avm1, avm2;
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
      u1 = Fp_add(Fp_mul_mod_pol((GEN) bezoutcoeff[sg[5]],
				 (GEN) pauto[1 + j1],TQ,Q),
		  Fp_mul_mod_pol((GEN) bezoutcoeff[sg[6]],
				 (GEN) pauto[((-j1) & 3) + 1],TQ,Q),Q);
      avm1 = avma;
      for (j2 = 0; j2 < 4; j2++)
      {
	u2 = Fp_add(u1, Fp_mul_mod_pol((GEN) bezoutcoeff[sg[3]], 
				       (GEN) pauto[1 + j2],TQ,Q),NULL);
	u2 = Fp_add(u2, Fp_mul_mod_pol((GEN) bezoutcoeff[sg[4]], (GEN)
				       pauto[((-j2) & 3) + 1],TQ,Q),Q);
	avm2 = avma;
	for (j3 = 0; j3 < 4; j3++)
	{
	  u3 = Fp_add(u2, Fp_mul_mod_pol((GEN) bezoutcoeff[sg[1]],
					 (GEN) pauto[1 + j3],TQ,Q),NULL);
	  u3 = Fp_add(u3, Fp_mul_mod_pol((GEN) bezoutcoeff[sg[2]], (GEN)
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
    ulong   av2;
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
	GEN     uu;
	long    av3;
	pj[6] = (w + pj[3]) & 3;
	uu =Fp_add(Fp_mul_mod_pol((GEN) bezoutcoeff[sg[5]],
			  (GEN) pauto[(pj[6] & 3) + 1],TQ,Q),
		   Fp_mul_mod_pol((GEN) bezoutcoeff[sg[6]],
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
	  u = Fp_add(uu, Fp_mul_mod_pol((GEN) pauto[(pj[4] & 3) + 1],
				(GEN) bezoutcoeff[sg[1]],TQ,Q),Q);
	  u = Fp_add(u,	 Fp_mul_mod_pol((GEN) pauto[((-pj[4]) & 3) + 1],
				(GEN) bezoutcoeff[sg[3]],TQ,Q),Q);
	  u = Fp_add(u,	 Fp_mul_mod_pol((GEN) pauto[(pj[5] & 3) + 1],
				(GEN) bezoutcoeff[sg[2]],TQ,Q),Q);
	  u = Fp_add(u,	 Fp_mul_mod_pol((GEN) pauto[((-pj[5]) & 3) + 1],
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
    ulong   av2;
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
      u = Fp_mul_mod_pol((GEN) pauto[(g & 3) + 1],
			 (GEN) bezoutcoeff[sg[1]],TQ,Q);
      u = Fp_add(u, Fp_mul_mod_pol((GEN) pauto[((-g) & 3) + 1],
				   (GEN) bezoutcoeff[sg[4]],TQ,Q),NULL);
      u = Fp_add(u, Fp_mul_mod_pol((GEN) pauto[(h & 3) + 1],
				   (GEN) bezoutcoeff[sg[2]],TQ,Q),NULL);
      u = Fp_add(u, Fp_mul_mod_pol((GEN) pauto[((-h) & 3) + 1],
				   (GEN) bezoutcoeff[sg[5]],TQ,Q),NULL);
      u = Fp_add(u, Fp_mul_mod_pol((GEN) pauto[(i & 3) + 1],
				   (GEN) bezoutcoeff[sg[3]],TQ,Q),NULL);
      u = Fp_add(u, Fp_mul_mod_pol((GEN) pauto[((-i) & 3) + 1],
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

GEN
galoisgen(GEN T, GEN L, GEN M, GEN den, struct galois_borne *gb,
	  const struct galois_analysis *ga)
{
  struct galois_analysis Pga;
  struct galois_borne Pgb;
  struct galois_test td;
  struct galois_testlift gt;
  struct galois_lift gl;
  ulong   ltop = avma, lbot, ltop2;
  long    n, p, deg, ex;
  byteptr primepointer;
  long    sg, Pm = 0, fp;
  long    x;
  int     i, j;
  GEN     Lden;
  GEN     Tmod, res, pf = gzero, split, psi, ip, ppsi;
  GEN     frob;
  GEN     O;
  GEN     P, PG, PL, Pden, PM, Pmod, Pp;
  GEN    *lo;			/* tired of casting */
  n = degree(T);
  if (!ga->deg)
    return gzero;
  p = ga->p;
  ex = ga->exception;
  deg = ga->deg;
  x = varn(T);
  primepointer = ga->primepointer;
  if (DEBUGLEVEL >= 9)
    fprintferr("GaloisConj:denominator:%Z\n", den);
  if (n == 12 && ga->ord == 3)	/* A4 is very probable,so test it first */
  {
    long    av = avma;
    if (DEBUGLEVEL >= 4)
      fprintferr("GaloisConj:Testing A4 first\n");
    inittest(L, M, gb->bornesol, gb->ladicsol, &td);
    lbot = avma;
    PG = a4galoisgen(T, &td);
    freetest(&td);
    if (PG != gzero)
    {
      return gerepile(ltop, lbot, PG);
    }
    avma = av;
  }
  if (n == 24 && ga->ord == 3)	/* S4 is very probable,so test it first */
  {
    long    av = avma;
    if (DEBUGLEVEL >= 4)
      fprintferr("GaloisConj:Testing S4 first\n");
    lbot = avma;
    Lden=makeLden(L,den,gb);
    initlift(T, den, stoi(ga->p4), L, Lden, gb, &gl);
    PG = s4galoisgen(&gl);
    if (PG != gzero)
    {
      return gerepile(ltop, lbot, PG);
    }
    avma = av;
  }
  frob = cgetg(lg(L), t_VECSMALL);
  Lden=makeLden(L,den,gb);
  for (;;)
  {
    ulong   av = avma;
    long    isram;
    long    c;
    ip = stoi(p);
    Tmod = lift((GEN) factmod(T, ip));
    isram = 0;
    for (i = 1; i < lg(Tmod[2]) && !isram; i++)
      if (!gcmp1(((GEN **) Tmod)[2][i]))
	isram = 1;
    if (isram == 0)
    {
      fp = degree(((GEN **) Tmod)[1][1]);
      for (i = 2; i < lg(Tmod[1]); i++)
	if (degree(((GEN **) Tmod)[1][i]) != fp)
	{
	  avma = ltop;
	  return gzero;		/* Not Galois polynomial */
	}
      if (fp % deg == 0)
      {
	if (DEBUGLEVEL >= 4)
	  fprintferr("Galoisconj:p=%ld deg=%ld fp=%ld\n", p, deg, fp);
	lo = (GEN *) listsousgroupes(deg, n / fp);
	initlift(T, den, ip, L, Lden, gb, &gl);
	if (inittestlift
	    ((GEN) Tmod[1], fp / deg, &gl, &gt, frob, lg(lo) == 2))
	{
	  int     k;
	  sg = lg(lo) - 1;
	  psi = cgetg(gt.g + 1, t_VECSMALL);
	  for (k = 1; k <= gt.g; k++)
	    psi[k] = 1;
	  goto suite;
	}
	if (DEBUGLEVEL >= 4)
	  fprintferr("Galoisconj:Subgroups list:%Z\n", (GEN) lo);
	if (deg == fp && cgcd(deg, n / deg) == 1)	/* Pretty sure it's the
							 * biggest ? */
	{
	  for (sg = 1; sg < lg(lo) - 1; sg++)
	    if (frobeniusliftall(lo[sg], &psi, &gl, &gt, frob))
	      goto suite;
	}
	else
	{
	  for (sg = lg(lo) - 2; sg >= 1; sg--)	/* else start with the
						 * fastest! */
	    if (frobeniusliftall(lo[sg], &psi, &gl, &gt, frob))
	      goto suite;
	}
	if (ex == 1 && (n == 12 || n % 12 != 0))
	{
	  avma = ltop;
	  return gzero;
	}
	else
	{
	  ex--;
	  if (n % 12 == 0)
	  {
	    if (n % 36 == 0)
	      deg = 5 - deg;
	    else
	      deg = 2;		/* For group like Z/2ZxA4 */
	  }
	  if (n % 12 == 0 && ex == -5)
	    err(warner, "galoisconj _may_ hang up for this polynomial");
	}
      }
    }
    c = *primepointer++;
    if (!c)
      err(primer1);
    p += c;
    if (DEBUGLEVEL >= 4)
      fprintferr("GaloisConj:next p=%ld\n", p);
    avma = av;
  }
suite:				/* Dijkstra probably hates me. (Linus
				 * Torvalds linux/kernel/sched.c) */
  if (deg == n)			/* Cyclique */
  {
    lbot = avma;
    res = cgetg(3, t_VEC);
    res[1] = lgetg(2, t_VEC);
    ((GEN **) res)[1][1] = gcopy(frob);
    res[2] = lgetg(2, t_VECSMALL);
    ((GEN *) res)[2][1] = deg;
    return gerepile(ltop, lbot, res);
  }
  if (DEBUGLEVEL >= 9)
    fprintferr("GaloisConj:Frobenius:%Z\n", frob);
  O = permorbite(frob);
  if (DEBUGLEVEL >= 9)
    fprintferr("GaloisConj:Orbite:%Z\n", O);
  {
    GEN     S, Tp, Fi, Sp;
    long    gp = n / fp;
    ppsi = cgetg(gp + 1, t_VECSMALL);
    P = corpsfixeorbitemod(L, O, x, gb->ladicabs, gb->l, ip, &PL);
    S = corpsfixeinclusion(O, PL);
    S = vectopol(S, M, den, gb->ladicabs, x);
    if (DEBUGLEVEL >= 9)
      fprintferr("GaloisConj:Inclusion:%Z\n", S);
    Pmod = lift((GEN)factmod(P, ip)[1]);
    Tp = Fp_pol_red(T,ip);
    /*S not in Z[X]*/
    Sp = lift(gmul(S,gmodulcp(gun,ip)));
    Pp = Fp_pol_red(P,ip);
    if (DEBUGLEVEL >= 4)
    {
      fprintferr("GaloisConj:psi=%Z\n", psi);
      fprintferr("GaloisConj:Sp=%Z\n", Sp);
      fprintferr("GaloisConj:Pmod=%Z\n", Pmod);
      fprintferr("GaloisConj:Tmod=%Z\n", Tmod);
    }
    for (i = 1; i <= gp; i++)
    {
      Fi = Fp_pol_gcd(Tp, Fp_compo_mod_pol((GEN) Pmod[i], Sp,Tp,ip),ip);
      /*normalize gcd*/
      Fi = Fp_mul_pol_scal(Fi, mpinvmod((GEN) Fi[lgef(Fi) - 1],ip),ip);
      if (DEBUGLEVEL >= 6)
	fprintferr("GaloisConj:Fi=%Z  %d", Fi, i);
      for (j = 1; j <= gp; j++)
	if (gegal(Fi, ((GEN **) Tmod)[1][j]))
	  break;
      if (DEBUGLEVEL >= 6)
	fprintferr("-->%d\n", j);
      if (j == gp + 1)
      {
	avma = ltop;
	return gzero;
      }
      if (j == gp)
      {
	Pm = i;
	ppsi[i] = 1;
      }
      else
	ppsi[i] = psi[j];
    }
    if (DEBUGLEVEL >= 4)
      fprintferr("GaloisConj:Pm=%ld   ppsi=%Z\n", Pm, ppsi);
    galoisanalysis(P, &Pga, 0);
    if (Pga.deg == 0)
    {
      avma = ltop;
      return gzero;		/* Avoid computing the discriminant */
    }
    Pden = absi(corediscpartial(discsr(P)));
    Pgb.l = gb->l;
    initborne(P, Pden, &Pgb, Pga.ppp);
    if (Pgb.valabs > gb->valabs)
    {
      if (DEBUGLEVEL>=4)
	fprintferr("GaloisConj:increase prec of p-adic roots of %ld.\n"
		   ,Pgb.valabs-gb->valabs);
      PL = rootpadicliftroots(P,PL,gb->l,Pgb.valabs);
    }
    PM = vandermondeinversemod(PL, P, Pden, Pgb.ladicabs);
    PG = galoisgen(P, PL, PM, Pden, &Pgb, &Pga);
  }
  if (DEBUGLEVEL >= 4)
    fprintferr("GaloisConj:Retour sur Terre:%Z\n", PG);
  if (PG == gzero)
  {
    avma = ltop;
    return gzero;
  }
  inittest(L, M, gb->bornesol, gb->ladicsol, &td);
  split = splitorbite(O);
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
    GEN     B, tau;
    long    t, g;
    long    w, sr, dss;
    if (DEBUGLEVEL >= 6)
      fprintferr("GaloisConj:G[%d]=%Z  d'ordre relatif %d\n", j,
		 ((GEN **) PG)[1][j], ((long **) PG)[2][j]);
    B = permorbite(((GEN **) PG)[1][j]);
    if (DEBUGLEVEL >= 6)
      fprintferr("GaloisConj:B=%Z\n", B);
    tau = permtopol(gmael(PG,1,j), PL, PM, Pden, Pgb.ladicabs, x);
    if (DEBUGLEVEL >= 6)
     fprintferr("GaloisConj:Paut=%Z\n", tau);
    /*tau not in Z[X]*/
    tau = lift(gmul(tau,gmodulcp(gun,ip)));
    tau = Fp_compo_mod_pol((GEN) Pmod[Pm], tau,Pp,ip);
    tau = Fp_pol_gcd(Pp, tau,ip);
    /*normalize gcd*/
    tau = Fp_mul_pol_scal(tau,mpinvmod((GEN) tau[lgef(tau) - 1],ip),ip);
    if (DEBUGLEVEL >= 6)
      fprintferr("GaloisConj:tau=%Z\n", tau);
    for (g = 1; g < lg(Pmod); g++)
      if (gegal(tau, (GEN) Pmod[g]))
	break;
    if (g == lg(Pmod))
    {
      freetest(&td);
      avma = ltop;
      return gzero;
    }
    w = ((long **) lo)[sg][ppsi[g]];
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
galoisconj4(GEN T, GEN den, long flag)
{
  ulong   ltop = avma;
  GEN     G, L, M, res, aut, grp=NULL;/*keep gcc happy on the wall*/
  struct galois_analysis ga;
  struct galois_borne gb;
  int     n, i, j, k;
  if (typ(T) != t_POL)
  {
    T = checknf(T);
    if (!den)
      den = gcoeff((GEN) T[8], degree((GEN) T[1]), degree((GEN) T[1]));
    T = (GEN) T[1];
  }
  n = lgef(T) - 3;
  if (n <= 0)
    err(constpoler, "galoisconj4");
  for (k = 2; k <= n + 2; k++)
    if (typ(T[k]) != t_INT)
      err(talker, "polynomial not in Z[X] in galoisconj4");
  if (!gcmp1((GEN) T[n + 2]))
    err(talker, "non-monic polynomial in galoisconj4");
  n = degree(T);
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
    galoisanalysis(T, &ga, 1);
  if (ga.deg == 0)
  {
    avma = ltop;
    return stoi(ga.p);		/* Avoid computing the discriminant */
  }
  if (!den)
    den = absi(corediscpartial(discsr(T)));
  else
  {
    if (typ(den) != t_INT)
      err(talker, "Second arg. must be integer in galoisconj4");
    den = absi(den);
  }
  gb.l = stoi(ga.l);
  if (DEBUGLEVEL >= 1)
    timer2();
  initborne(T, den, &gb, ga.ppp);
  if (DEBUGLEVEL >= 1)
    msgtimer("initborne()");
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
  if (DEBUGLEVEL >= 1)
    timer2();
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
  res[1] = (long) permidentity(n);
  k = 1;
  for (i = 1; i < lg(G[1]); i++)
  {
    int     c = k * (((long **) G)[2][i] - 1);
    for (j = 1; j <= c; j++)	/* I like it */
      res[++k] = (long) applyperm((GEN) res[j], ((GEN **) G)[1][i]);
  }
  if (flag)
  {
    grp[6] = (long) res;
    return gerepileupto(ltop, grp);
  }
  aut = cgetg(n + 1, t_COL);
  for (i = 1; i <= n; i++)
    aut[i] = (long) permtopol((GEN) res[i], L, M, den, gb.ladicsol, varn(T));
  if (DEBUGLEVEL >= 1)
    msgtimer("Calcul polynomes");
  return gerepileupto(ltop, aut);
}

/* Calcule le nombre d'automorphisme de T avec forte probabilité */
/* pdepart premier nombre premier a tester */
long
numberofconjugates(GEN T, long pdepart)
{
  ulong   ltop = avma, ltop2;
  long    n, p, nbmax, nbtest;
  long    card;
  byteptr primepointer;
  int     i;
  GEN     L;
  n = degree(T);
  card = sturm(T);
  card = cgcd(card, n - card);
  nbmax = (n<<1) + 1;
  if (nbmax < 20) nbmax=20;
  nbtest = 0;
  L = cgetg(n + 1, t_VECSMALL);
  ltop2 = avma;
  for (p = 0, primepointer = diffptr; nbtest < nbmax && card > 1;)
  {
    long    s, c;
    long    isram;
    GEN     S;
    c = *primepointer++;
    if (!c)
      err(primer1);
    p += c;
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
  ulong   ltop;
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
    G = galoisconj4(nf, d, 0);
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
    return galoisconj2(nf, degree(T), prec);
  case 4:
    G = galoisconj4(nf, d, 0);
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
  ulong ltop=avma;
  struct galois_borne gb;
  gb.l=p;
  initborne(P,den,&gb,degree(P));
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
galoisinit(GEN nf, GEN den)
{
  GEN     G;
  G = galoisconj4(nf, den, 1);
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
GEN galoiscoset(GEN perm, GEN O)
{
  ulong ltop;
  GEN coset,RO;
  int i,j,l,o;
  long u,v;
  o=lg(O)-1;   /*number of orbits and cosets*/
  l=lg(O[1])-1;/*number of elements in orbits*/
  coset=cgetg(lg(O),t_VEC);/*allocate memory*/
  for(i=1;i<=o;i++)
  {
    coset[i]=lgetg(lg(O),t_VECSMALL);
    mael(coset,i,1)=0;/*mark uncomputed*/
  }
  ltop=avma;
  RO=cgetg(lg(perm),t_VECSMALL);
  /*Reverse Orbit array: RO[u]=i <==>  u\in O[i] */
  for(i=1;i<=o;i++)
    for(j=1;j<=l;j++)
      RO[mael(O,i,j)]=i;
  if (DEBUGLEVEL>=6) fprintferr("GaloisCoset:RO=%Z\n",RO);
  u=mael(O,1,1);
  for(i=1,j=1;;i++)
  {
    long r;
    v=mael(perm,i,u);
    r=RO[v];
    if (mael(coset,r,1)==0)
    {
      int k;
      GEN pm;
      pm=(GEN)perm[i];
      for(k=1;k<=o;k++)
	mael(coset,r,k)=RO[pm[mael(O,k,1)]];
      if (j>=o)
	break;
      j++;
    }
  }
  avma=ltop;
  return coset;
}
GEN
fixedfieldfactor(GEN L, GEN O, GEN perm,GEN PL, GEN M, GEN den, GEN mod, long x,long y)
{
  ulong   ltop=avma, av;
  GEN     g;
  GEN     F,G,V,res,coset;
  int     i, j, k;
  F=cgetg(lg(O[1])+1,t_COL);
  F[lg(O[1])]=un;
  G=cgetg(lg(O),t_VEC);
  for (i = 1; i < lg(O); i++)
  {
    g=polun[x];
    for (j = 1; j < lg(O[i]); j++)
      g = Fp_mul(g, deg1pol(gun,negi((GEN) L[mael(O,i,j)]),x),mod);
    G[i]=(long)g;
  }  
  V=cgetg(lg(O),t_COL);
  coset=galoiscoset(perm,O);
  if (DEBUGLEVEL>=6) fprintferr("GaloisFixedField:cosets=%Z\n",coset);
  res=cgetg(lg(O),t_VEC);
  for (i = 1; i < lg(O); i++)
  {
    GEN pm=(GEN)coset[i];
    av=avma;
    for (j = 1; j < lg(O[1]); j++)
    {
      for(k = 1; k < lg(O); k++)
	V[k]=mael(G,pm[k],j+1);
      F[j]=(long) vectopol(V, M, den, mod, y);
    }
    res[i]=(long)gerepileupto(av,gtopolyrev(F,x));
  }
  return gerepileupto(ltop,res);
}
GEN
galoisfixedfield(GEN gal, GEN perm, long flag, long y)
{
  ulong   ltop = avma, lbot;
  GEN     P, S, PL, O, res;
  long    x;
  int     i;
  x = varn((GEN) gal[1]);
  gal = checkgal(gal);
  if (flag<0 || flag>2)
    err(flagerr, "galoisfixedfield");
  if (typ(perm) == t_VEC)
  {
    for (i = 1; i < lg(perm); i++)
      if (typ(perm[i]) != t_VECSMALL)
	err(typeer, "galoisfixedfield");
  }
  else if (typ(perm) != t_VECSMALL)
    err(typeer, "galoisfixedfield");
  O = permorbite(perm);
  P = corpsfixeorbitemod((GEN) gal[3], O, x, gmael(gal,2,3), gmael(gal,2,1), gun, &PL);
  if (flag==1)
  {
    cgiv(PL);
    return gerepileupto(ltop,P);
  }
  S = corpsfixeinclusion(O, PL);
  S = vectopol(S, (GEN) gal[4], (GEN) gal[5], gmael(gal,2,3), x);
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
    Pden = absi(corediscpartial(discsr(P)));
    /*We should check the precisions of the roots here.
      TODO*/
    PM = vandermondeinversemod(PL, P, Pden, gmael(gal,2,3));
    lbot = avma;
    if (y==-1)
      y = fetch_user_var("y");
    if (y<=x)
      err(talker,"priority of optionnal variable too high in  galoisfixedfield");
    res = cgetg(4, t_VEC);
    res[1] = (long) gcopy(P);
    res[2] = (long) gmodulcp(S, (GEN) gal[1]);
    res[3] = (long) fixedfieldfactor((GEN) gal[3],O,(GEN)gal[6],PL,PM,Pden,gmael(gal,2,1),x,y);
    return gerepile(ltop, lbot, res);
  }
}
/* Calcule les orbites d'un sous-groupe de Z/nZ donne par un
 * generateur ou d'un ensemble de generateur donne par un vecteur. 
 */
GEN
subgroupcoset(long n, GEN v)
{
  ulong   ltop = avma, lbot;
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
    while (e>1)
    {
      q=n/p;
      for(j=1;j<p;j++)
	if (!W[1+j*q]) break;
      if (j<p)
	break;
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
/* Hack to use divide_and_conquer_prod. Sometimes a copy-paste seems
 * better.  
 */
static GEN modulo;
static GEN gsmul(GEN a,GEN b){return Fp_mul(a,b,modulo);}
GEN 
galoissubcyclo(long n, GEN H, GEN Z, long v)
{
  ulong ltop=avma,av;
  GEN l,borne,le,powz,z,V;
  long i;
  long e,val;
  long u,o,j;
  GEN O,g;
  if ( v==-1 ) v=0;
  if ( n<1 ) err(arither2);
  if ( n>=VERYBIGINT) 
    err(impl,"galoissubcyclo for huge conductor");    
  if ( typ(H)==t_MAT )
  {
    GEN zn2, zn3, gen, ord;
    if (lg(H) != lg(H[1]))
      err(talker,"not a HNF matrix in galoissubcyclo");
    if (!Z)
      Z=znstar(stoi(n));
    else if (typ(Z)!=t_VEC || lg(Z)!=4) 
      err(talker,"Optionnal parameter must be as output by znstar in galoissubcyclo");
    zn2 = vectosmall((GEN)Z[2]);
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
    H=vectosmall(H);
    for (i=1;i<lg(H);i++)
      if (H[i]<0)
	H[i]=mulssmod(-H[i],n-1,n);
    /*Should check components are prime to n, but it is costly*/
  }
  V = cgetg(n, t_VECSMALL);
  if (DEBUGLEVEL >= 1)
    timer2();
  n = znconductor(n,H,V);
  if (DEBUGLEVEL >= 1)
    msgtimer("znconductor.");
  H = V;
  O = subgroupcoset(n,H);
  if (DEBUGLEVEL >= 1)
    msgtimer("subgroupcoset.");
  if (DEBUGLEVEL >= 6)
    fprintferr("Subcyclo: orbit=%Z\n",O);
  u=lg(O)-1;o=lg(O[1])-1;
  if (DEBUGLEVEL >= 4)
    fprintferr("Subcyclo: %ld orbits with %ld elements each\n",u,o);
  if (o==1)
  {
    avma=ltop;
    return cyclo(n,v);
  }
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
  i=u-(1+u)/(1+o);
  borne=mulii(binome(stoi(u),i),gpowgs(stoi(o),i));
  if (DEBUGLEVEL >= 4)
    fprintferr("Subcyclo: borne=%Z\n",borne);
  val=mylogint(shifti(borne,1),l,DEFAULTPREC);
  avma=av;
  if (DEBUGLEVEL >= 4)
    fprintferr("Subcyclo: val=%ld\n",val);
  le=gpowgs(l,val);
  z=lift(gpowgs(gener(l),e));
  z=padicsqrtnlift(gun,stoi(n),z,l,val);
  if (DEBUGLEVEL >= 1)
    msgtimer("padicsqrtnlift.");
  powz = cgetg(n,t_VEC); powz[1] = (long)z;
  for (i=2; i<n; i++) powz[i] = lmodii(mulii(z,(GEN)powz[i-1]),le);
  if (DEBUGLEVEL >= 1)
    msgtimer("computing roots.");  
  g=cgetg(u+1,t_VEC);
  for(i=1;i<=u;i++)
  {
    GEN s;
    s=gzero;
    for(j=1;j<=o;j++)
      s=addii(s,(GEN)powz[mael(O,i,j)]);
    s=modii(negi(s),le);
    g[i]=(long)deg1pol(gun,s,v);
  }
  if (DEBUGLEVEL >= 1)
    msgtimer("computing new roots."); 
  modulo=le;
  g=divide_conquer_prod(g,&gsmul);
  if (DEBUGLEVEL >= 1)
    msgtimer("computing products."); 
  g=Fp_centermod(g,le);
  return gerepileupto(ltop,g);
}
