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
  GEN x, y, z;
  long i, lz, lx, v, av = avma;
  nf = checknf(nf);
  x = (GEN) nf[1];
  v = varn(x);
  lx = lgef(x) - 2;
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
    GEN p1 = lift((GEN) z[i]);
    setvarn(p1, v);
    y[i] = (long) p1;
  }
  return gerepileupto(av, y);
}
/* nbmax: maximum number of possible conjugates */
GEN
galoisconj2pol(GEN x, long nbmax, long prec)
{
  long av = avma, i, n, v, nbauto;
  GEN y, w, polr, p1, p2;
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
  long av = avma, i, j, n, r1, ru, nbauto;
  GEN x, y, w, polr, p1, p2;
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
/**                           GALOIS4               		        **/
/**									**/
/**                                                                     **/
/**                                                                     **/
/*************************************************************************/
struct galois_lift
{
  GEN T;
  GEN den;
  GEN p;
  GEN borne;
  GEN L;
  long e;
  GEN Q;
};
/* Initialise la structure galois_lift */
void
initlift(GEN T, GEN den, GEN p, GEN borne, GEN L, struct galois_lift * gl)
{
  ulong ltop, lbot;
  gl->T = T;
  gl->den = den;
  gl->p = p;
  gl->borne = borne;
  gl->L = L;
  ltop = avma;
  gl->e = itos(gmax(gdeux, gceil(gdiv(glog(gmul2n(borne, 1), DEFAULTPREC),
				      glog(p, DEFAULTPREC)))));
  lbot = avma;
  gl->Q = gpowgs(p, gl->e);
  gl->Q = gerepile(ltop, lbot, gl->Q);
}
/*
 * T est le polynome \sum t_i*X^i S est un Polmod T Retourne un vecteur Spow
 * verifiant la condition: i>=1 et t_i!=0 ==> Spow[i]=S^(i-1)*t_i Essaie
 * d'etre efficace sur les polynomes lacunaires
 */
GEN
compoTS(GEN T, GEN S)
{
  GEN Spow;
  int i;
  Spow = cgetg(lgef(T) - 2, t_VEC);
  for (i = 3; i < lg(Spow); i++)
    Spow[i] = 0;
  Spow[1] = un;
  Spow[2] = (long) S;
  for (i = 2; i < lg(Spow) - 1; i++)
  {
    if (!gcmp0((GEN) T[i + 3]))
      for (;;)
      {
	int k, l;
	for (k = 1; k <= (i >> 1); k++)
	  if (Spow[k + 1] && Spow[i - k + 1])
	    break;
	if ((k << 1) < i)
	{
	  Spow[i + 1] = lmul((GEN) Spow[k + 1], (GEN) Spow[i - k + 1]);
	  break;
	} else if ((k << 1) == i)	/* En esperant que sqr est plus
					 * rapide... */
	{
	  Spow[i + 1] = lsqr((GEN) Spow[k + 1]);
	  break;
	}
	for (k = i - 1; k > 0; k--)
	  if (Spow[k + 1])
	    break;
	if ((k << 1) < i)
	{
	  Spow[(k << 1) + 1] = lsqr((GEN) Spow[k + 1]);
	  continue;
	}
	for (l = i - k; l > 0; l--)
	  if (Spow[l + 1])
	    break;
	if (Spow[i - l - k + 1])
	  Spow[i - k + 1] = lmul((GEN) Spow[i - l - k + 1], (GEN) Spow[l + 1]);
	else
	  Spow[l + k + 1] = lmul((GEN) Spow[k + 1], (GEN) Spow[l + 1]);
      }
  }
  for (i = 1; i < lg(Spow); i++)
    if (!gcmp0((GEN) T[i + 2]))
      Spow[i] = lmul((GEN) Spow[i], (GEN) T[i + 2]);
  return Spow;
}
/*
 * Calcule T(S) a l'aide du vecteur Spow
 */
static GEN
calcTS(GEN Spow, GEN T, GEN S)
{
  GEN res = gzero;
  int i;
  for (i = 1; i < lg(Spow); i++)
    if (!gcmp0((GEN) T[i + 2]))
      res = gadd(res, (GEN) Spow[i]);
  res = gmul(res, S);
  return gadd(res, (GEN) T[2]);
}
/*
 * Calcule T'(S) a l'aide du vecteur Spow
 */
static GEN
calcderivTS(GEN Spow, GEN T, GEN mod)
{
  GEN res = gzero;
  int i;
  for (i = 1; i < lg(Spow); i++)
    if (!gcmp0((GEN) T[i + 2]))
      res = gadd(res, gmul((GEN) Spow[i], stoi(i)));
  res = gmul(lift(lift(res)), mod);
  return gmodulcp(res, T);
}
/*
 * Verifie que S est une solution presque surement et calcule sa permutation
 */
static int
poltopermtest(GEN f, GEN L, GEN pf)
{
  ulong ltop;
  GEN fx, fp;
  int i, j;
  fp = cgetg(lg(L), t_VECSMALL);
  ltop = avma;
  for (i = 1; i < lg(fp); i++)
    fp[i] = 1;
  for (i = 1; i < lg(L); i++)
  {
    fx = gsubst(f, varn(f), (GEN) L[i]);
    for (j = 1; j < lg(L); j++)
      if (fp[j] && gegal(fx, (GEN) L[j]))
      {
	pf[i] = j;
	fp[j] = 0;
	break;
      }
    if (j == lg(L))
      return 0;
    avma = ltop;
  }
  return 1;
}
/*
 * Soit T un polynome de \ZZ[X] , p un nombre premier , S\in\FF_p[X]/(T) tel
 * que T(S)=0 [p,T] Relever S en S_0 tel que T(S_0)=0 [T,p^e]
 */
GEN
automorphismlift(GEN S, struct galois_lift * gl)
{
  ulong ltop, lbot;
  long x;
  GEN q, mod, modold;
  GEN W, Tr, Sr, Wr = gzero, Trold, Spow;
  int flag, init, ex;
  GEN *gptr[2];
  if (DEBUGLEVEL >= 1)
    timer2();
  x = varn(gl->T);
  Tr = gmul(gl->T, gmodulcp(gun, gl->p));
  W = ginv(gsubst(deriv(Tr, x), x, S));
  q = gl->p;
  modold = gl->p;
  Trold = Tr;
  ex = 1;
  flag = 1;
  init = 0;
  gptr[0] = &S;
  gptr[1] = &Wr;
  while (flag)
  {
    if (DEBUGLEVEL >= 1)
      timer2();
    q = gsqr(q);
    ex <<= 1;
    if (ex >= gl->e)
    {
      flag = 0;
      q = gl->Q;
      ex = gl->e;
    }
    mod = gmodulcp(gun, q);
    Tr = gmul(gl->T, mod);
    ltop = avma;
    Sr = gmodulcp(gmul(lift(lift(S)), mod), Tr);
    Spow = compoTS(Tr, Sr);
    if (init)
      W = gmul(Wr, gsub(gdeux, gmul(Wr, calcderivTS(Spow, Trold, modold))));
    else
      init = 1;
    Wr = gmodulcp(gmul(lift(lift(W)), mod), Tr);
    S = gmul(Wr, calcTS(Spow, Tr, Sr));
    lbot = avma;
    Wr = gcopy(Wr);
    S = gsub(Sr, S);
    gerepilemanysp(ltop, lbot, gptr, 2);
    modold = mod;
    Trold = Tr;
  }
  if (DEBUGLEVEL >= 1)
    msgtimer("automorphismlift()");
  return S;
}
struct galois_testlift
{
  long n;
  long f;
  long g;
  GEN bezoutcoeff;
  GEN pauto;
};
/*
 * Si polb est un polynomes de Z[X] et pola un facteur modulo p, retourne b*v
 * telqu' il existe u et a tel que: a=pola [mod p] a*b=polb [mod p^e]
 * b*v+a*u=1 [mod p^e]
 */
GEN
bezout_lift_fact(GEN pola, GEN polb, GEN p, GEN pev, long e)
{
  long ev;
  GEN ae, be, u, v, ae2, be2, s, t, pe, pe2, z, g;
  long ltop = avma, lbot;
  if (DEBUGLEVEL >= 1)
    timer2();
  ae = lift(pola);
  be = Fp_poldivres(polb, ae, p, NULL);
  g = (GEN) Fp_pol_extgcd(ae, be, p, &u, &v)[2];	/* deg g = 0 */
  if (!gcmp1(g))
  {
    g = mpinvmod(g, p);
    u = gmul(u, g);
    v = gmul(v, g);
  }
  for (pe = p, ev = 1; ev < e;)
  {
    ev <<= 1;
    pe2 = (ev >= e) ? pev : sqri(pe);
    g = gadd(polb, gneg_i(gmul(ae, be)));
    g = Fp_pol_red(g, pe2);
    g = gdivexact(g, pe);
    z = Fp_pol_red(gmul(v, g), pe);
    t = Fp_poldivres(z, ae, pe, &s);
    t = gadd(gmul(u, g), gmul(t, be));
    t = Fp_pol_red(t, pe);
    be2 = gadd(be, gmul(t, pe));
    ae2 = gadd(ae, gmul(s, pe));/* already reduced mod pe2 */
    g = gadd(gun, gneg_i(gadd(gmul(u, ae2), gmul(v, be2))));
    g = Fp_pol_red(g, pe2);
    g = gdivexact(g, pe);
    z = Fp_pol_red(gmul(v, g), pe);
    t = Fp_poldivres(z, ae, pe, &s);
    t = gadd(gmul(u, g), gmul(t, be));
    t = Fp_pol_red(t, pe);
    u = gadd(u, gmul(t, pe));
    v = gadd(v, gmul(s, pe));
    pe = pe2;
    ae = ae2;
    be = be2;
  }
  lbot = avma;
  g = gmul(v, be);
  g = gerepile(ltop, lbot, g);
  if (DEBUGLEVEL >= 1)
    msgtimer("bezout_lift_fact()");
  return g;
}
static long
inittestlift(GEN Tmod, long elift, struct galois_lift * gl, struct galois_testlift * gt, GEN frob)
{
  ulong ltop = avma;
  int i, j;
  long v;
  GEN pe, autpow, plift;
  GEN Tmodp, xmodp, modQ, TmodQ, xmodQ;
  GEN *gptr[2];
  v = varn(gl->T);
  gt->n = lg(gl->L) - 1;
  gt->g = lg(Tmod) - 1;
  gt->f = gt->n / gt->g;
  Tmodp = gmul(gl->T, gmodulcp(gun, gl->p));
  xmodp = gmodulcp(gmul(polx[v], gmodulcp(gun, gl->p)), Tmodp);
  pe = gpowgs(gl->p, elift);
  plift = automorphismlift(powgi(xmodp, pe), gl);
  if (frob)
  {
    GEN tlift;
    tlift = gdiv(centerlift(gmul((GEN) plift[2], gl->den)), gl->den);
    if (poltopermtest(tlift, gl->L, frob))
    {
      avma = ltop;
      return 1;
    }
  }
  modQ = gmodulcp(gun, gl->Q);
  TmodQ = gmul(gl->T, modQ);
  xmodQ = gmodulcp(gmul(polx[v], modQ), TmodQ);
  gt->bezoutcoeff = cgetg(gt->g + 1, t_VEC);
  for (i = 1; i <= gt->g; i++)
  {
    GEN blift;
    blift = bezout_lift_fact((GEN) Tmod[i], gl->T, gl->p, gl->Q, gl->e);
    gt->bezoutcoeff[i] = (long) gmodulcp(gmul(blift, modQ), TmodQ);
  }
  gt->pauto = cgetg(gt->f + 1, t_VEC);
  gt->pauto[1] = (long) xmodQ;
  gt->pauto[2] = (long) plift;
  if (gt->f > 2)
  {
    autpow = cgetg(gt->n, t_VEC);
    autpow[1] = (long) plift;
    for (i = 2; i < gt->n; i++)
      autpow[i] = lmul((GEN) autpow[i - 1], plift);
    for (i = 3; i <= gt->f; i++)
    {
      GEN s, P;
      P = ((GEN **) gt->pauto)[i - 1][2];
      s = (GEN) P[2];
      for (j = 1; j < lgef(P) - 2; j++)
	s = gadd(s, gmul((GEN) autpow[j], (GEN) P[j + 2]));
      gt->pauto[i] = (long) s;
    }
  }
  gptr[0] = &gt->bezoutcoeff;
  gptr[1] = &gt->pauto;
  gerepilemany(ltop, gptr, 2);
  return 0;
}
/*
 * 
 */
long
frobeniusliftall(GEN sg, GEN * psi, struct galois_lift * gl, struct galois_testlift * gt, GEN frob)
{
  ulong ltop = avma, av, ltop2;
  long d, N, z, m, c;
  int i, j, k;
  GEN pf, u, v;
  m = gt->g;
  c = lg(sg) - 1;
  d = m / c;
  pf = cgetg(m, t_VECSMALL);
  *psi = pf;
  ltop2 = avma;
  N = itos(gdiv(mpfact(m), gmul(stoi(c), gpowgs(mpfact(d), c))));
  avma = ltop2;
  v = gmul((GEN) gt->pauto[2], (GEN) gt->bezoutcoeff[m]);
  for (i = 1; i < m; i++)
    pf[i] = 1 + i / d;
  av = avma;
  for (i = 0;; i++)
  {
    u = v;
    if (DEBUGLEVEL >= 4)
    {
      fprintferr("GaloisConj:Testing %Z:%d:%Z:", sg, i, pf);
      timer2();
    }
    for (j = 1; j < m; j++)
      u = gadd(u, gmul((GEN) gt->pauto[sg[pf[j]] + 1], (GEN) gt->bezoutcoeff[j]));
    u = gdiv(centerlift(gmul((GEN) u[2], gl->den)), gl->den);
    if (poltopermtest(u, gl->L, frob))
    {
      if (DEBUGLEVEL >= 4)
	msgtimer("");
      avma = ltop2;
      return 1;
    }
    if (DEBUGLEVEL >= 4)
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
  *psi = NULL;
  return 0;
}
/*
 * applique une permutation t a un vecteur s sans duplication
 */
static GEN
applyperm(GEN s, GEN t)
{
  GEN u;
  int i;
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
  GEN ar;
  long i;
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
  GEN ordre;
  GEN borne, lborne, ladic;
  GEN PV, TM;
  GEN L, M;
};
/* Calcule la matrice de tests correspondant a la n-ieme ligne de V */
static GEN
Vmatrix(long n, struct galois_test * td)
{
  ulong ltop = avma, lbot;
  GEN V;
  long i;
  V = cgetg(lg(td->L), t_VEC);
  for (i = 1; i < lg(V); i++)
    V[i] = ((GEN **) td->M)[i][n][2];
  V = centerlift(gmul(td->L, V));
  lbot = avma;
  V = gmod(V, td->ladic);
  return gerepile(ltop, lbot, V);
}
/*
 * Initialise la structure galois_test
 */
static void
inittest(GEN L, GEN M, GEN borne, GEN ladic, struct galois_test * td)
{
  ulong ltop;
  long i;
  int n = lg(L) - 1;
  if (DEBUGLEVEL >= 8)
    fprintferr("GaloisConj:Entree Init Test\n");
  td->ordre = cgetg(n + 1, t_VECSMALL);
  for (i = 1; i <= n - 2; i++)
    td->ordre[i] = i + 2;
  for (; i <= n; i++)
    td->ordre[i] = i - n + 2;
  td->borne = borne;
  td->lborne = gsub(ladic, borne);
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
freetest(struct galois_test * td)
{
  int i;
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
long
padicisint(GEN P, struct galois_test * td)
{
  long r;
  ulong ltop = avma;
  GEN U;
  if (typ(P) != t_INT)
    err(typeer, "padicisint");
  U = modii(P, td->ladic);
  r = gcmp(U, (GEN) td->borne) <= 0 || gcmp(U, (GEN) td->lborne) >= 0;
  avma = ltop;
  return r;
}
/*
 * Verifie si pf est une vrai solution et non pas un "hop"
 */
static long
verifietest(GEN pf, struct galois_test * td)
{
  ulong av = avma;
  GEN P, V;
  int i, j;
  int n = lg(td->L) - 1;
  if (DEBUGLEVEL >= 8)
    fprintferr("GaloisConj:Entree Verifie Test\n");
  P = applyperm(td->L, pf);
  for (i = 1; i < n; i++)
  {
    long ord;
    GEN PW;
    ord = td->ordre[i];
    PW = (GEN) td->PV[ord];
    if (PW)
    {
      V = ((GEN **) PW)[1][pf[1]];
      for (j = 2; j <= n; j++)
	V = gadd(V, ((GEN **) PW)[j][pf[j]]);
    } else
      V = centerlift(gmul((GEN) td->TM[ord], P));
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
    if (DEBUGLEVEL >= 2)
      fprintferr("M");
  }
  if (DEBUGLEVEL >= 2)
    fprintferr("%d.", i);
  if (i > 1)
  {
    long z;
    z = td->ordre[i];
    for (j = i; j > 1; j--)
      td->ordre[j] = td->ordre[j - 1];
    td->ordre[1] = z;
    if (DEBUGLEVEL >= 6)
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
testpermutation(GEN F, GEN B, long s, long t, long cut, struct galois_test * td)
{
  ulong av, avm = avma, av2;
  long a, b, c, d, n;
  GEN pf, x, ar, y, *G;
  int N, cx, p1, p2, p3, p4, p5, p6;
  int i, j, hop = 0;
  GEN V, W;
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
	} else
	  p4 = x[p1 - 1];
	if (p5 == d - 1)
	  p6 = p1 + 1 - d;
	else
	  p6 = p1 + 1;
	y[p1] = 0;
	V = gzero;
	for (p2 = 1 + p4, p3 = 1 + x[p1]; p2 <= b; p2++)
	{
	  V = gadd(V, ((GEN **) W)[G[p6][p3]][G[p1][p2]]);
	  p3 += s;
	  if (p3 > b)
	    p3 -= b;
	}
	p3 = 1 + x[p1] - s;
	if (p3 <= 0)
	  p3 += b;
	for (p2 = p4; p2 >= 1; p2--)
	{
	  V = gadd(V, ((GEN **) W)[G[p6][p3]][G[p1][p2]]);
	  p3 -= s;
	  if (p3 <= 0)
	    p3 += b;
	}
	gaffect((GEN) V, (GEN) ar[p1]);
      }
    V = gzero;
    for (p1 = 1; p1 <= a; p1++)
      V = gadd(V, (GEN) ar[p1]);
    if (padicisint(V, td))
    {
      for (p1 = 1, p5 = d; p1 <= a; p1++, p5++)
      {
	if (p5 == d)
	{
	  p5 = 0;
	  p4 = 0;
	} else
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
      } else
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
/*
 * Calcule la liste des sous groupes de \ZZ/m\ZZ d'ordre divisant p et
 * retourne la liste de leurs elements
 */
GEN
listsousgroupes(long m, long p)
{
  ulong ltop = avma, lbot;
  GEN zns, lss, res, sg, gen, ord, res1;
  int k, card, i, j, l, n, phi, h;
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
  lss = subgrouplist((GEN) zns[2], 0);
  gen = cgetg(lg(zns[3]), t_VECSMALL);
  ord = cgetg(lg(zns[3]), t_VECSMALL);
  res1 = cgetg(lg(lss), t_VECSMALL);
  lbot = avma;
  for (k = 1, i = lg(lss) - 1; i >= 1; i--)
  {
    long av;
    av = avma;
    card = phi / itos(det((GEN) lss[i]));
    avma = av;
    if (p % card == 0)
    {
      sg = cgetg(1 + card, t_VECSMALL);
      sg[1] = 1;
      av = avma;
      for (j = 1; j < lg(gen); j++)
      {
	gen[j] = 1;
	for (h = 1; h < lg(lss[i]); h++)
	  gen[j] = (gen[j] * itos(lift(powgi(((GEN **) zns)[3][h],
					   ((GEN ***) lss)[i][j][h])))) % m;
	ord[j] = itos(((GEN **) zns)[2][j]) / itos(((GEN ***) lss)[i][j][j]);
      }
      avma = av;
      for (j = 1, l = 1; j < lg(gen); j++)
      {
	int c = l * (ord[j] - 1);
	for (n = 1; n <= c; n++)/* I like it */
	  sg[++l] = (sg[n] * gen[j]) % m;
      }
      res1[k++] = (long) sg;
    }
  }
  res = cgetg(k, t_VEC);
  for (i = 1; i < k; i++)
    res[i] = res1[i];
  return gerepile(ltop, lbot, res);
}
/* retourne la permutation identite */
GEN
permidentity(long l)
{
  GEN perm;
  int i;
  perm = cgetg(l + 1, t_VECSMALL);
  for (i = 1; i <= l; i++)
    perm[i] = i;
  return perm;
}
/* retourne la decomposition en cycle */
GEN
permtocycle(GEN p)
{
  long ltop = avma, lbot;
  int i, j, k, l, m;
  GEN bit, cycle, cy;
  cycle = cgetg(lg(p), t_VEC);
  bit = cgetg(lg(p), t_VECSMALL);
  for (i = 1; i < lg(p); i++)
    bit[i] = 0;
  for (k = 1, l = 1; k < lg(p);)
  {
    for (j = 1; bit[j]; j++);
    cy = cgetg(lg(p), t_VECSMALL);
    m = 1;
    do
    {
      bit[j] = 1;
      k++;
      cy[m++] = j;
      j = p[j];
    } while (!bit[j]);
    setlg(cy, m);
    cycle[l++] = (long) cy;
  }
  setlg(cycle, l);
  lbot = avma;
  cycle = gcopy(cycle);
  return gerepile(ltop, lbot, cycle);
}
/* Calcule les orbites d'un ensemble de permutations */
GEN
vecpermorbite(GEN v)
{
  ulong ltop = avma, lbot;
  int i, j, k, l, m, n, o, p, flag;
  GEN bit, cycle, cy;
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
    } while (flag);
    setlg(cy, m);
    cycle[l++] = (long) cy;
  }
  setlg(cycle, l);
  lbot = avma;
  cycle = gcopy(cycle);
  return gerepile(ltop, lbot, cycle);
}
/*
 * Calcule la permutation associe a un polynome f des racines L
 */
GEN
poltoperm(GEN f, GEN L)
{
  ulong ltop, ltop2;
  GEN pf, fx, fp;
  int i, j;
  pf = cgetg(lg(L), t_VECSMALL);
  ltop = avma;
  fp = cgetg(lg(L), t_VECSMALL);
  ltop2 = avma;
  for (i = 1; i < lg(fp); i++)
    fp[i] = 1;
  for (i = 1; i < lg(L); i++)
  {
    fx = gsubst(f, varn(f), (GEN) L[i]);
    for (j = 1; j < lg(L); j++)
      if (fp[j] && gegal(fx, (GEN) L[j]))
      {
	pf[i] = j;
	fp[j] = 0;
	break;
      }
    avma = ltop2;
  }
  avma = ltop;
  return pf;
}
/*
 * Calcule un polynome R definissant  le corps fixe de T pour les orbites O
 * tel que R est sans-facteur carre modulo mod et l retourne dans U les
 * racines de R
 */
GEN
corpsfixeorbitemod(GEN L, GEN O, long x, GEN mod, GEN l, GEN * U)
{
  ulong ltop = avma, lbot, av, av2;
  GEN g, p, PL, *gptr[2], gmod, gl, modl;
  GEN id;
  int i, j, d, dmax;
  PL = cgetg(lg(O), t_COL);
  modl = gmodulcp(gun, l);
  av2 = avma;
  dmax = lg(L) + 1;
  d = 0;
  do
  {
    avma = av2;
    id = stoi(d);
    g = polun[x];
    for (i = 1; i < lg(O); i++)
    {
      p = gadd(id, (GEN) L[((GEN *) O)[i][1]]);
      for (j = 2; j < lg(O[i]); j++)
	p = gmul(p, gadd(id, (GEN) L[((GEN *) O)[i][j]]));
      PL[i] = (long) p;
      g = gmul(g, gsub(polx[x], p));
    }
    lbot = avma;
    g = centerlift(g);
    av = avma;
    gmod = gmul(g, mod);
    gl = gmul(g, modl);
    if (DEBUGLEVEL >= 6)
      fprintferr("GaloisConj:corps fixe:%d:%Z\n", d, g);
    d = (d > 0 ? -d : 1 - d);
    if (d > dmax)
      err(talker, "prime too small in corpsfixeorbitemod");
  } while (degree(ggcd(deriv(gl, x), gl)) || degree(ggcd(deriv(gmod, x), gmod)));
  avma = av;
  *U = gcopy(PL);
  gptr[0] = &g;
  gptr[1] = U;
  gerepilemanysp(ltop, lbot, gptr, 2);
  return g;
}
/*
 * Calcule l'inclusion de R dans T i.e. S telque T|R\compo S
 */
GEN
corpsfixeinclusion(GEN O, GEN PL)
{
  GEN S;
  int i, j;
  S = cgetg((lg(O) - 1) * (lg(O[1]) - 1) + 1, t_COL);
  for (i = 1; i < lg(O); i++)
    for (j = 1; j < lg(O[i]); j++)
      S[((GEN *) O)[i][j]] = lcopy((GEN) PL[i]);
  return S;
}
/* Calcule l'inverse de la matrice de van der Monde de T multiplie par den */
GEN
vandermondeinverse(GEN L, GEN T, GEN den)
{
  ulong ltop = avma, lbot;
  int i, j, n = lg(L);
  long x = varn(T);
  GEN M, P, Tp;
  if (DEBUGLEVEL >= 1)
    timer2();
  M = cgetg(n, t_MAT);
  Tp = deriv(T, x);
  for (i = 1; i < n; i++)
  {
    M[i] = lgetg(n, t_COL);
    P = gdiv(gdeuc(T, gsub(polx[x], (GEN) L[i])), gsubst(Tp, x, (GEN) L[i]));
    for (j = 1; j < n; j++)
      ((GEN *) M)[i][j] = P[1 + j];
  }
  if (DEBUGLEVEL >= 1)
    msgtimer("vandermondeinverse");
  lbot = avma;
  M = gmul(den, M);
  return gerepile(ltop, lbot, M);
}
/* Calcule le polynome associe a un vecteur conjugue v */
static GEN
vectopol(GEN v, GEN L, GEN M, GEN den, long x)
{
  ulong ltop = avma, lbot;
  GEN res;
  res = gmul(M, v);
  res = gtopolyrev(centerlift(res), x);
  lbot = avma;
  res = gdiv(res, den);
  return gerepile(ltop, lbot, res);
}
/* Calcule le polynome associe a une permuation p */
static GEN
permtopol(GEN p, GEN L, GEN M, GEN den, long x)
{
  ulong ltop = avma, lbot;
  GEN res;
  res = gmul(M, applyperm(L, p));
  res = gtopolyrev(centerlift(res), x);
  lbot = avma;
  res = gdiv(res, den);
  return gerepile(ltop, lbot, res);
}
/*
 * factorise partiellement n sous la forme n=d*u*f^2 ou d est sans facteur
 * carre et u n'est pas un carre parfait et retourne u*f
 */
GEN
mycoredisc(GEN n)
{
  ulong av = avma, tetpil, r;
  GEN y, p1, p2, ret;
  {
    long av = avma, tetpil, i;
    GEN fa, p1, p2, p3, res = gun, res2 = gun, y;
    fa = auxdecomp(n, 0);
    p1 = (GEN) fa[1];
    p2 = (GEN) fa[2];
    for (i = 1; i < lg(p1) - 1; i++)
    {
      p3 = (GEN) p2[i];
      if (mod2(p3))
	res = mulii(res, (GEN) p1[i]);
      if (!gcmp1(p3))
	res2 = mulii(res2, gpui((GEN) p1[i], shifti(p3, -1), 0));
    }
    p3 = (GEN) p2[i];
    if (mod2(p3))		/* impaire: verifions */
    {
      if (!gcmp1(p3))
	res2 = mulii(res2, gpui((GEN) p1[i], shifti(p3, -1), 0));
      if (isprime((GEN) p1[i]))
	res = mulii(res, (GEN) p1[i]);
      else
	res2 = mulii(res2, (GEN) p1[i]);
    } else			/* paire:OK */
      res2 = mulii(res2, gpui((GEN) p1[i], shifti(p3, -1), 0));
    tetpil = avma;
    y = cgetg(3, t_VEC);
    y[1] = (long) icopy(res);
    y[2] = (long) icopy(res2);
    ret = gerepile(av, tetpil, y);
  }
  p2 = ret;
  p1 = (GEN) p2[1];
  r = mod4(p1);
  if (signe(p1) < 0)
    r = 4 - r;
  if (r == 1 || r == 4)
    return (GEN) p2[2];
  tetpil = avma;
  y = gmul2n((GEN) p2[2], -1);
  return gerepile(av, tetpil, y);
}
/* Calcule la puissance exp d'une permutation decompose en cycle */
GEN
permcyclepow(GEN O, long exp)
{
  int j, k, n;
  GEN p;
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
  ulong ltop = avma, lbot;
  int i, n;
  GEN F, fc, res;
  n = lg(O[1]) - 1;
  F = factor(stoi(n));
  fc = cgetg(lg(F[1]), t_VECSMALL);
  for (i = 1; i < lg(fc); i++)
    fc[i] = itos(gpow(((GEN **) F)[1][i], ((GEN **) F)[2][i], DEFAULTPREC));
  lbot = avma;
  res = cgetg(lg(fc), t_VEC);
  for (i = 1; i < lg(fc); i++)
  {
    GEN v;
    v = cgetg(3, t_VEC);
    res[i] = (long) v;
    v[1] = (long) permcyclepow(O, n / fc[i]);
    v[2] = (long) stoi(fc[i]);
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
  long p;
  long deg;
  long exception;
  long ord;
  long l;
  long ppp;
  long p4;
  byteptr primepointer;
};
/* peut-etre on peut accelerer(distinct degree factorisation */
void
galoisanalysis(GEN T, struct galois_analysis * ga, long calcul_l)
{
  ulong ltop = avma;
  long n, p, ex, plift, nbmax, nbtest, exist6 = 0, p4 = 0;
  GEN F, fc;
  byteptr primepointer, pp = 0;
  long pha, ord, deg, ppp, pgp, ordmax = 0, l = 0;
  int i;
  /* Etude du cardinal: */
  /* Calcul de l'ordre garanti d'un sous-groupe cyclique */
  /* Tout les groupes d'ordre n sont cyclique ssi gcd(n,phi(n))==1 */
  if (DEBUGLEVEL >= 1)
    timer2();
  n = degree(T);
  F = factor(stoi(n));
  fc = cgetg(lg(F[1]), t_VECSMALL);
  for (i = 1; i < lg(fc); i++)
    fc[i] = itos(gpow(((GEN **) F)[1][i], ((GEN **) F)[2][i], DEFAULTPREC));
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
    } else
    {
      ex = 1;
      break;
    }
    if (!gcmp1(((GEN **) F)[2][i]))
      break;
  }
  plift = 0;
  /* Etude des ordres des Frobenius */
  nbmax = max(4, n / 2);	/* Nombre maxi d'éléments à tester */
  nbtest = 0;
  deg = 0;
  for (p = 0, primepointer = diffptr; plift == 0 || (nbtest < nbmax && ord != n) || (n == 24 && exist6 == 0 && p4 == 0);)
  {
    long u, s, c;
    long isram;
    GEN S;
    c = *primepointer++;
    if (!c)
      err(primer1);
    p += c;
    if (p <= (n << 1))
      continue;
    S = (GEN) simplefactmod(T, stoi(p));
    isram = 0;
    for (i = 1; i < lg(S[2]) && !isram; i++)
      if (!gcmp1(((GEN **) S)[2][i]))
	isram = 1;
    if (isram == 0)
    {
      s = itos(((GEN **) S)[1][1]);
      for (i = 2; i < lg(S[1]) && !isram; i++)
	if (itos(((GEN **) S)[1][i]) != s)
	{
	  avma = ltop;
	  if (DEBUGLEVEL >= 2)
	    fprintferr("GaloisAnalysis:non Galois for p=%d\n", p);
	  ga->p = p;
	  ga->deg = 0;
	  return;		/* Not a Galois polynomial */
	}
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
	fprintferr("GaloisAnalysis:Nbtest=%d,plift=%d,p=%d,s=%d,ord=%d\n", nbtest, plift, p, s, ord);
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
	} else if (!ex && (plift == 0 || s > ord))
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
  if (plift == 0 || ((n == 36 || n == 48) && !exist6) || (n == 56 && ordmax == 7) || (n == 60 && ordmax == 5) || (n == 72 && !exist6) || (n == 80 && ordmax == 5))
  {
    deg = 0;
    err(warner, "Galois group almost certainly not weakly super solvable");
  }
  avma = ltop;
  if (calcul_l)
  {
    ulong av;
    GEN x;
    long c;
    x = cgetg(3, t_POLMOD);
    x[2] = lpolx[varn(T)];
    av = avma;
    while (l == 0)
    {
      c = *primepointer++;
      if (!c)
	err(primer1);
      p += c;
      x[1] = lmul(T, gmodulss(1, p));
      if (gegal(gpuigs(x, p), x))
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
    fprintferr("GaloisAnalysis:p=%d l=%d exc=%d deg=%d ord=%d ppp=%d\n", p, l, ex, deg, ord, ppp);
  if (DEBUGLEVEL >= 1)
    msgtimer("galoisanalysis()");
}
/* Calcule les bornes sur les coefficients a chercher */
struct galois_borne
{
  GEN l;
  long valsol;
  long valabs;
  GEN bornesol;
  GEN ladicsol;
  GEN ladicabs;
};
/*
 * recalcule L avec une precision superieur
 */
GEN
recalculeL(GEN T, GEN Tp, GEN L, struct galois_borne * gb, struct galois_borne * ngb)
{
  ulong ltop = avma, lbot = avma;
  GEN L2, y, z, lad;
  long i, val;
  if (DEBUGLEVEL >= 1)
    timer2();
  L2 = cgetg(lg(L), typ(L));
  for (i = 1; i < lg(L); i++)
  {
    ltop = avma;
    val = gb->valabs;
    lad = gb->ladicabs;
    z = (GEN) L[i];
    while (val < ngb->valabs)
    {
      val <<= 1;
      if (val >= ngb->valabs)
      {
	val = ngb->valabs;
	lad = ngb->ladicabs;
      } else
	lad = gsqr(lad);
      y = gmodulcp((GEN) z[2], lad);
      z = gdiv(poleval(T, y), poleval(Tp, y));
      lbot = avma;
      z = gsub(y, z);
    }
    L2[i] = (long) gerepile(ltop, lbot, z);
  }
  return L2;
}
void
initborne(GEN T, GEN disc, struct galois_borne * gb, long ppp)
{
  ulong ltop = avma, lbot, av2;
  GEN borne, borneroots, borneabs;
  int i, j;
  int n;
  GEN L, M, z;
  L = roots(T, DEFAULTPREC);
  n = lg(L) - 1;
  for (i = 1; i <= n; i++)
  {
    z = (GEN) L[i];
    if (signe(z[2]))
      break;
    L[i] = z[1];
  }
  M = vandermondeinverse(L, gmul(T, dbltor(1.)), disc);
  borne = gzero;
  for (i = 1; i <= n; i++)
  {
    z = gzero;
    for (j = 1; j <= n; j++)
      z = gadd(z, gabs(((GEN **) M)[j][i], DEFAULTPREC));
    if (gcmp(z, borne) > 0)
      borne = z;
  }
  borneroots = gzero;
  for (i = 1; i <= n; i++)
  {
    z = gabs((GEN) L[i], DEFAULTPREC);
    if (gcmp(z, borneroots) > 0)
      borneroots = z;
  }
  borneabs = addsr(1, gpowgs(addsr(n, borneroots), n / ppp));
  lbot = avma;
  borneroots = addsr(1, gmul(borne, borneroots));
  av2 = avma;
  borneabs = gmul2n(gmul(borne, borneabs), 4);
  gb->valsol = itos(gceil(gdiv(glog(gmul2n(borneroots, 4 + (n >> 1)), DEFAULTPREC), glog(gb->l, DEFAULTPREC))));
  if (DEBUGLEVEL >= 4)
    fprintferr("GaloisConj:val1=%d\n", gb->valsol);
  gb->valabs = max(gb->valsol, itos(gceil(gdiv(glog(borneabs, DEFAULTPREC), glog(gb->l, DEFAULTPREC)))));
  if (DEBUGLEVEL >= 4)
    fprintferr("GaloisConj:val2=%d\n", gb->valabs);
  avma = av2;
  gb->bornesol = gerepile(ltop, lbot, borneroots);
  gb->ladicsol = gpowgs(gb->l, gb->valsol);
  gb->ladicabs = gpowgs(gb->l, gb->valabs);
}
/* Groupe A4 */
GEN
a4galoisgen(GEN T, struct galois_test * td)
{
  int ltop = avma, av, av2;
  int i, j, k;
  int n;
  int N, hop = 0;
  GEN *ar, **mt;		/* tired of casting */
  GEN t, u, O;
  GEN res, orb, ry;
  GEN pft, pfu, pfv;
  n = degree(T);
  res = cgetg(4, t_VEC);
  ry = cgetg(3, t_VEC);
  res[1] = (long) ry;
  pft = cgetg(n + 1, t_VECSMALL);
  ry[1] = (long) pft;
  ry[2] = (long) stoi(2);
  ry = cgetg(3, t_VEC);
  pfu = cgetg(n + 1, t_VECSMALL);
  ry[1] = (long) pfu;
  ry[2] = (long) stoi(2);
  res[2] = (long) ry;
  ry = cgetg(3, t_VEC);
  pfv = cgetg(n + 1, t_VECSMALL);
  ry[1] = (long) pfv;
  ry[2] = (long) stoi(3);
  res[3] = (long) ry;
  av = avma;
  ar = (GEN *) alloue_ardoise(n, 1 + lg(td->ladic));
  mt = (GEN **) td->PV[td->ordre[n]];
  t = cgetg(n + 1, t_VECSMALL) + 1;	/* Sorry for this hack */
  u = cgetg(n + 1, t_VECSMALL) + 1;	/* too lazy to correct */
  av2 = avma;
  N = itos(gdiv(mpfact(n), mpfact(n >> 1))) >> (n >> 1);
  if (DEBUGLEVEL >= 4)
    fprintferr("A4GaloisConj:I will test %d permutations\n", N);
  avma = av2;
  for (i = 0; i < n; i++)
    t[i] = i + 1;
  for (i = 0; i < N; i++)
  {
    GEN g;
    int a, x, y;
    if (i == 0)
    {
      gaffect(gzero, ar[(n - 2) >> 1]);
      for (k = n - 2; k > 2; k -= 2)
	gaddz(ar[k >> 1], gadd(mt[k + 1][k + 2], mt[k + 2][k + 1]), ar[(k >> 1) - 1]);
    } else
    {
      x = i;
      y = 1;
      do
      {
	hiremainder = 0;
	y += 2;
	x = divll(x, y);
	a = hiremainder;
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
	} else
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
	gaddz(ar[2], gadd(mt[t[4]][t[5]], mt[t[5]][t[4]]), ar[1]);
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
	gaddz(ar[3], gadd(mt[t[6]][t[7]], mt[t[7]][t[6]]), ar[2]);
	gaddz(ar[2], gadd(mt[t[4]][t[5]], mt[t[5]][t[4]]), ar[1]);
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
	gaddz(ar[4], gadd(mt[t[8]][t[9]], mt[t[9]][t[8]]), ar[3]);
	gaddz(ar[3], gadd(mt[t[6]][t[7]], mt[t[7]][t[6]]), ar[2]);
	gaddz(ar[2], gadd(mt[t[4]][t[5]], mt[t[5]][t[4]]), ar[1]);
	break;
       default:
	y--;
	x = t[0];
	t[0] = t[2];
	t[2] = t[1];
	t[1] = x;
	for (k = 4; k < y; k += 2)
	{
	  int j;
	  x = t[k];
	  for (j = k; j > 0; j--)
	    t[j] = t[j - 1];
	  t[0] = x;
	}
	x = t[y];
	t[y] = t[y - a];
	t[y - a] = x;
	for (k = y; k > 2; k -= 2)
	  gaddz(ar[k >> 1], gadd(mt[t[k]][t[k + 1]], mt[t[k + 1]][t[k]]), ar[(k >> 1) - 1]);
      }
    }
    g = gadd(ar[1], gadd(gadd(mt[t[0]][t[1]], mt[t[1]][t[0]]),
			 gadd(mt[t[2]][t[3]], mt[t[3]][t[2]])));
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
      fprintferr("A4GaloisConj: %d hop sur %d iterations\n", hop, N);
    return gzero;
  }
  if (DEBUGLEVEL >= 1 && hop)
    fprintferr("A4GaloisConj: %d hop sur %d iterations\n", hop, N);
  N = itos(gdiv(mpfact(n >> 1), mpfact(n >> 2))) >> 1;
  avma = av2;
  if (DEBUGLEVEL >= 4)
    fprintferr("A4GaloisConj:sigma=%Z \n", pft);
  for (i = 0; i < N; i++)
  {
    GEN g;
    int a, x, y;
    if (i == 0)
    {
      for (k = 0; k < n; k += 4)
      {
	u[k + 3] = t[k + 3];
	u[k + 2] = t[k + 1];
	u[k + 1] = t[k + 2];
	u[k] = t[k];
      }
    } else
    {
      x = i;
      y = -2;
      do
      {
	hiremainder = 0;
	y += 4;
	x = divll(x, y);
	a = hiremainder;
      } while (!a);
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
	if (a % 2 == 0)
	{
	  a = 4 - a / 2;
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
      g = gadd(g, gadd(mt[u[k]][u[k + 1]], mt[u[k + 1]][u[k]]));
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
    fprintferr("A4GaloisConj: %d hop sur %d iterations\n", hop, N);
  if (DEBUGLEVEL >= 4)
    fprintferr("A4GaloisConj:tau=%Z \n", u);
  avma = av2;
  orb = cgetg(3, t_VEC);
  orb[1] = (long) pft;
  orb[2] = (long) pfu;
  if (DEBUGLEVEL >= 4)
    fprintferr("A4GaloisConj:orb=%Z \n", orb);
  O = vecpermorbite(orb);
  if (DEBUGLEVEL >= 4)
    fprintferr("A4GaloisConj:O=%Z \n", O);
  av2 = avma;
  for (j = 0; j < 2; j++)
  {
    pfv[((long **) O)[1][1]] = ((long **) O)[2][1];
    pfv[((long **) O)[1][2]] = ((long **) O)[2][3 + j];
    pfv[((long **) O)[1][3]] = ((long **) O)[2][4 - (j << 1)];
    pfv[((long **) O)[1][4]] = ((long **) O)[2][2 + j];
    for (i = 0; i < 4; i++)
    {
      long x;
      GEN g;
      switch (i)
      {
       case 0:
	break;
       case 1:
	x = ((long **) O)[3][1];
	((long **) O)[3][1] = ((long **) O)[3][2];
	((long **) O)[3][2] = x;
	x = ((long **) O)[3][3];
	((long **) O)[3][3] = ((long **) O)[3][4];
	((long **) O)[3][4] = x;
	break;
       case 2:
	x = ((long **) O)[3][1];
	((long **) O)[3][1] = ((long **) O)[3][4];
	((long **) O)[3][4] = x;
	x = ((long **) O)[3][2];
	((long **) O)[3][2] = ((long **) O)[3][3];
	((long **) O)[3][3] = x;
	break;
       case 3:
	x = ((long **) O)[3][1];
	((long **) O)[3][1] = ((long **) O)[3][2];
	((long **) O)[3][2] = x;
	x = ((long **) O)[3][3];
	((long **) O)[3][3] = ((long **) O)[3][4];
	((long **) O)[3][4] = x;
      }
      pfv[((long **) O)[2][1]] = ((long **) O)[3][1];
      pfv[((long **) O)[2][3 + j]] = ((long **) O)[3][4 - j];
      pfv[((long **) O)[2][4 - (j << 1)]] = ((long **) O)[3][2 + (j << 1)];
      pfv[((long **) O)[2][2 + j]] = ((long **) O)[3][3 - j];
      pfv[((long **) O)[3][1]] = ((long **) O)[1][1];
      pfv[((long **) O)[3][4 - j]] = ((long **) O)[1][2];
      pfv[((long **) O)[3][2 + (j << 1)]] = ((long **) O)[1][3];
      pfv[((long **) O)[3][3 - j]] = ((long **) O)[1][4];
      g = gzero;
      for (k = 1; k <= n; k++)
	g = gadd(g, mt[k][pfv[k]]);
      if (padicisint(g, td) && verifietest(pfv, td))
      {
	avma = av;
	if (DEBUGLEVEL >= 1)
	  fprintferr("A4GaloisConj:%d hop sur %d iterations max\n", hop, 10395 + 68);
	return res;
      } else
	hop++;
      avma = av2;
    }
  }
  /* Echec? */
  avma = ltop;
  return gzero;
}
/* Groupe S4 */
GEN
Fpisom(GEN p, GEN T1, GEN T2)
{
  ulong ltop = avma, lbot;
  GEN T, res;
  long v;
  if (T1 == T2)
    return gmodulcp(polx[varn(T1)], T1);
  v = varn(T2);
  setvarn(T2, MAXVARN);
  T = (GEN) factmod9(T1, p, T2)[1];
  setvarn(T2, v);
  lbot = avma;
  res = gneg(((GEN **) T)[1][2]);
  setvarn(res[1], v);
  setvarn(res[2], v);
  return gerepile(ltop, lbot, res);
}
GEN
Fpinvisom(GEN S)
{
  ulong ltop = avma, lbot;
  GEN M, U, V;
  int n, i, j;
  long x;
  x = varn(S[1]);
  U = gmodulcp(polun[x], (GEN) S[1]);
  n = degree((GEN) S[1]);
  M = cgetg(n + 1, t_MAT);
  for (i = 1; i <= n; i++)
  {
    int d;
    if (i > 1)
      U = gmul(U, S);
    M[i] = lgetg(n + 1, t_COL);
    d = degree((GEN) U[2]);
    for (j = 1; j <= d + 1; j++)
      ((GEN *) M)[i][j] = ((GEN *) U)[2][1 + j];
    for (j = d + 2; j <= n; j++)
      ((GEN *) M)[i][j] = zero;
  }
  V = cgetg(n + 1, t_COL);
  for (i = 1; i <= n; i++)
    V[i] = zero;
  V[2] = un;
  V = gauss(M, V);
  lbot = avma;
  V = gtopolyrev(V, x);
  return gerepile(ltop, lbot, V);
}
static void
makelift(GEN u, struct galois_lift * gl, GEN liftpow)
{
  int i;
  liftpow[1] = (long) automorphismlift(u, gl);
  for (i = 2; i < lg(liftpow); i++)
    liftpow[i] = lmul((GEN) liftpow[i - 1], (GEN) liftpow[1]);
}
static long
s4test(GEN u, GEN liftpow, struct galois_lift * gl, GEN phi)
{
  GEN res;
  int i;
  if (DEBUGLEVEL >= 6)
    timer2();
  u = (GEN) u[2];
  res = (GEN) u[2];
  for (i = 1; i < lgef(u) - 2; i++)
    res = gadd(res, gmul((GEN) liftpow[i], (GEN) u[i + 2]));
  res = gdiv(centerlift(gmul((GEN) res[2], gl->den)), gl->den);
  if (DEBUGLEVEL >= 6)
    msgtimer("s4test()");
  return poltopermtest(res, gl->L, phi);
}
GEN
s4galoisgen(struct galois_lift * gl)
{
  struct galois_testlift gt;
  ulong ltop = avma, av, ltop2;
  GEN Tmod, isom, isominv, misom;
  int i, j;
  GEN sg;
  GEN sigma, tau, phi;
  GEN res, ry;
  GEN pj;
  GEN p;
  GEN bezoutcoeff, pauto, liftpow;
  long v;
  p = gl->p;
  v = varn(gl->T);
  res = cgetg(5, t_VEC);
  ry = cgetg(3, t_VEC);
  res[1] = (long) ry;
  ry[1] = lgetg(lg(gl->L), t_VECSMALL);
  ry[2] = (long) stoi(2);
  ry = cgetg(3, t_VEC);
  res[2] = (long) ry;
  ry[1] = lgetg(lg(gl->L), t_VECSMALL);
  ry[2] = (long) stoi(2);
  ry = cgetg(3, t_VEC);
  res[3] = (long) ry;
  ry[1] = lgetg(lg(gl->L), t_VECSMALL);
  ry[2] = (long) stoi(3);
  ry = cgetg(3, t_VEC);
  res[4] = (long) ry;
  ry[1] = lgetg(lg(gl->L), t_VECSMALL);
  ry[2] = (long) stoi(2);
  ltop2 = avma;
  sg = cgetg(7, t_VECSMALL);
  pj = cgetg(7, t_VECSMALL);
  sigma = cgetg(lg(gl->L), t_VECSMALL);
  tau = cgetg(lg(gl->L), t_VECSMALL);
  phi = cgetg(lg(gl->L), t_VECSMALL);
  for (i = 1; i < lg(sg); i++)
    sg[i] = i;
  Tmod = (GEN) factmod(gl->T, p)[1];
  isom = cgetg(lg(Tmod), t_VEC);
  isominv = cgetg(lg(Tmod), t_VEC);
  misom = cgetg(lg(Tmod), t_MAT);
  inittestlift(Tmod, 1, gl, &gt, NULL);
  bezoutcoeff = gt.bezoutcoeff;
  pauto = gt.pauto;
  for (i = 1; i < lg(pj); i++)
    pj[i] = 0;
  for (i = 1; i < lg(isom); i++)
  {
    misom[i] = lgetg(lg(Tmod), t_COL);
    isom[i] = (long) Fpisom(p, (GEN) Tmod[1], (GEN) Tmod[i]);
    if (DEBUGLEVEL >= 4)
      fprintferr("S4GaloisConj:Computing isomorphisms %d:%Z\n", i, (GEN) isom[i]);
    isominv[i] = (long) lift(Fpinvisom((GEN) isom[i]));
  }
  for (i = 1; i < lg(isom); i++)
    for (j = 1; j < lg(isom); j++)
      ((GEN **) misom)[i][j] = gsubst((GEN) isominv[i], v, (GEN) isom[j]);
  liftpow = cgetg(24, t_VEC);
  av = avma;
  for (i = 0; i < 3; i++)
  {
    ulong av2;
    GEN u;
    int j1, j2, j3;
    ulong avm1, avm2;
    GEN u1, u2, u3;
    if (i)
    {
      int x;
      x = sg[3];
      if (i == 1)
      {
	sg[3] = sg[2];
	sg[2] = x;
      } else
      {
	sg[3] = sg[1];
	sg[1] = x;
      }
    }
    u = chinois(((GEN **) misom)[sg[1]][sg[2]],
		((GEN **) misom)[sg[2]][sg[1]]);
    u = chinois(u, ((GEN **) misom)[sg[3]][sg[4]]);
    u = chinois(u, ((GEN **) misom)[sg[4]][sg[3]]);
    u = chinois(u, ((GEN **) misom)[sg[5]][sg[6]]);
    u = chinois(u, ((GEN **) misom)[sg[6]][sg[5]]);
    makelift(u, gl, liftpow);
    av2 = avma;
    for (j1 = 0; j1 < 4; j1++)
    {
      u1 = gadd(gmul((GEN) bezoutcoeff[sg[5]], (GEN) pauto[1 + j1]),
	      gmul((GEN) bezoutcoeff[sg[6]], (GEN) pauto[((-j1) & 3) + 1]));
      avm1 = avma;
      for (j2 = 0; j2 < 4; j2++)
      {
	u2 = gadd(u1, gmul((GEN) bezoutcoeff[sg[3]], (GEN) pauto[1 + j2]));
	u2 = gadd(u2, gmul((GEN) bezoutcoeff[sg[4]], (GEN) pauto[((-j2) & 3) + 1]));
	avm2 = avma;
	for (j3 = 0; j3 < 4; j3++)
	{
	  u3 = gadd(u2, gmul((GEN) bezoutcoeff[sg[1]], (GEN) pauto[1 + j3]));
	  u3 = gadd(u3, gmul((GEN) bezoutcoeff[sg[2]], (GEN) pauto[((-j3) & 3) + 1]));
	  if (DEBUGLEVEL >= 4)
	    fprintferr("S4GaloisConj:Testing %d/3:%d/4:%d/4:%d/4:%Z\n", i, j1, j2, j3, sg);
	  if (s4test(u3, liftpow, gl, sigma))
	  {
	    pj[1] = j3;
	    pj[2] = j2, pj[3] = j1;
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
    ulong av2;
    GEN u;
    int w, l;
    int z;
    z = sg[1];
    sg[1] = sg[3];
    sg[3] = sg[5];
    sg[5] = z;
    z = sg[2];
    sg[2] = sg[4];
    sg[4] = sg[6];
    sg[6] = z;
    z = pj[1];
    pj[1] = pj[2];
    pj[2] = pj[3];
    pj[3] = z;
    for (l = 0; l < 2; l++)
    {
      u = chinois(((GEN **) misom)[sg[1]][sg[3]],
		  ((GEN **) misom)[sg[3]][sg[1]]);
      u = chinois(u, ((GEN **) misom)[sg[2]][sg[4]]);
      u = chinois(u, ((GEN **) misom)[sg[4]][sg[2]]);
      u = chinois(u, ((GEN **) misom)[sg[5]][sg[6]]);
      u = chinois(u, ((GEN **) misom)[sg[6]][sg[5]]);
      makelift(u, gl, liftpow);
      av2 = avma;
      for (w = 0; w < 4; w += 2)
      {
	GEN uu;
	long av3;
	pj[6] = (w + pj[3]) & 3;
	uu = gadd(gmul((GEN) bezoutcoeff[sg[5]], (GEN) pauto[(pj[6] & 3) + 1]),
	   gmul((GEN) bezoutcoeff[sg[6]], (GEN) pauto[((-pj[6]) & 3) + 1]));
	av3 = avma;
	for (i = 0; i < 4; i++)
	{
	  GEN u;
	  pj[4] = i;
	  pj[5] = (i + pj[2] - pj[1]) & 3;
	  if (DEBUGLEVEL >= 4)
	    fprintferr("S4GaloisConj:Testing %d/3:%d/2:%d/2:%d/4:%Z:%Z\n", j - 1, w >> 1, l, i, sg, pj);
	  u = gadd(uu, gmul((GEN) pauto[(pj[4] & 3) + 1], (GEN) bezoutcoeff[sg[1]]));
	  u = gadd(u, gmul((GEN) pauto[((-pj[4]) & 3) + 1], (GEN) bezoutcoeff[sg[3]]));
	  u = gadd(u, gmul((GEN) pauto[(pj[5] & 3) + 1], (GEN) bezoutcoeff[sg[2]]));
	  u = gadd(u, gmul((GEN) pauto[((-pj[5]) & 3) + 1], (GEN) bezoutcoeff[sg[4]]));
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
    int abc, abcdef;
    GEN u;
    ulong av2;
    abc = (pj[1] + pj[2] + pj[3]) & 3;
    abcdef = (((abc + pj[4] + pj[5] - pj[6]) & 3) >> 1);
    u = chinois(((GEN **) misom)[sg[1]][sg[4]],
		((GEN **) misom)[sg[4]][sg[1]]);
    u = chinois(u, ((GEN **) misom)[sg[2]][sg[5]]);
    u = chinois(u, ((GEN **) misom)[sg[5]][sg[2]]);
    u = chinois(u, ((GEN **) misom)[sg[3]][sg[6]]);
    u = chinois(u, ((GEN **) misom)[sg[6]][sg[3]]);
    makelift(u, gl, liftpow);
    av2 = avma;
    for (j = 0; j < 8; j++)
    {
      int h, g, i;
      h = j & 3;
      g = abcdef + ((j & 4) >> 1);
      i = h + abc - g;
      u = gmul((GEN) pauto[(g & 3) + 1], (GEN) bezoutcoeff[sg[1]]);
      u = gadd(u, gmul((GEN) pauto[((-g) & 3) + 1], (GEN) bezoutcoeff[sg[4]]));
      u = gadd(u, gmul((GEN) pauto[(h & 3) + 1], (GEN) bezoutcoeff[sg[2]]));
      u = gadd(u, gmul((GEN) pauto[((-h) & 3) + 1], (GEN) bezoutcoeff[sg[5]]));
      u = gadd(u, gmul((GEN) pauto[(i & 3) + 1], (GEN) bezoutcoeff[sg[3]]));
      u = gadd(u, gmul((GEN) pauto[((-i) & 3) + 1], (GEN) bezoutcoeff[sg[6]]));
      if (DEBUGLEVEL >= 4)
	fprintferr("S4GaloisConj:Testing %d/8 %d:%d:%d\n", j, g & 3, h & 3, i & 3);
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
    ((GEN **) res)[2][1][i] = phi[sigma[tau[phi[i]]]];
    ((GEN **) res)[3][1][i] = phi[sigma[i]];
    ((GEN **) res)[4][1][i] = sigma[i];
  }
  avma = ltop2;
  return res;
}
GEN
galoisgen(GEN T, GEN L, GEN M, GEN den, struct galois_borne * gb, const struct galois_analysis * ga)
{
  struct galois_analysis Pga;
  struct galois_borne Pgb;
  struct galois_test td;
  struct galois_testlift gt;
  struct galois_lift gl;
  ulong ltop = avma, lbot;
  long n, p, deg, ex;
  byteptr primepointer;
  long sg, Pm = 0, fp;
  long x = varn(T);
  int i, j;
  GEN Tmod, res, pf = gzero, split, psi, ip, mod, ppsi;
  GEN frob;
  GEN O;
  GEN P, PG, PL, Pden, PM, Pmod, Pp;
  GEN *lo;			/* tired of casting */
  n = degree(T);
  if (!ga->deg)
    return gzero;
  p = ga->p;
  ex = ga->exception;
  deg = ga->deg;
  primepointer = ga->primepointer;
  if (DEBUGLEVEL >= 9)
    fprintferr("GaloisConj:denominator:%Z\n", den);
  if (n == 12 && ga->ord == 3)	/* A4 is very probable,so test it first */
  {
    long av = avma;
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
    long av = avma;
    if (DEBUGLEVEL >= 4)
      fprintferr("GaloisConj:Testing S4 first\n");
    lbot = avma;
    initlift(T, den, stoi(ga->p4), gb->bornesol, L, &gl);
    PG = s4galoisgen(&gl);
    if (PG != gzero)
    {
      return gerepile(ltop, lbot, PG);
    }
    avma = av;
  }
  frob = cgetg(lg(L), t_VECSMALL);
  for (;;)
  {
    ulong av = avma;
    long isram;
    long c;
    ip = stoi(p);
    Tmod = (GEN) factmod(T, ip);
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
	  fprintferr("Galoisconj:p=%d deg=%d fp=%d\n", p, deg, fp);
	lo = (GEN *) listsousgroupes(deg, n / fp);
	initlift(T, den, ip, gb->bornesol, L, &gl);
	if (inittestlift((GEN) Tmod[1], fp / deg, &gl, &gt, frob))
	{
	  int k;
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
	} else
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
	} else
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
      fprintferr("GaloisConj:next p=%d\n", p);
    avma = av;
  }
suite:				/* Djikstra probably hates me. (Linus
				 * Torvalds linux/kernel/sched.c) */
  if (deg == n)			/* Cyclique */
  {
    lbot = avma;
    res = cgetg(2, t_VEC);
    res[1] = lgetg(3, t_VEC);
    ((GEN **) res)[1][1] = gcopy(frob);
    ((GEN **) res)[1][2] = stoi(deg);
    return gerepile(ltop, lbot, res);
  }
  if (DEBUGLEVEL >= 9)
    fprintferr("GaloisConj:Frobenius:%Z\n", frob);
  O = permtocycle(frob);
  if (DEBUGLEVEL >= 9)
    fprintferr("GaloisConj:Orbite:%Z\n", O);
  {
    GEN S, Tp, Fi, Sp;
    long gp = n / fp;
    ppsi = cgetg(gp + 1, t_VECSMALL);
    mod = gmodulcp(gun, ip);
    P = corpsfixeorbitemod(L, O, x, mod, gb->l, &PL);
    S = corpsfixeinclusion(O, PL);
    S = vectopol(S, L, M, den, x);
    if (DEBUGLEVEL >= 6)
      fprintferr("GaloisConj:Inclusion:%Z\n", S);
    Pmod = (GEN) factmod(P, ip)[1];
    Tp = gmul(T, mod);
    Sp = gmul(S, mod);
    Pp = gmul(P, mod);
    if (DEBUGLEVEL >= 4)
      fprintferr("GaloisConj:psi=%Z\n", psi);
    if (DEBUGLEVEL >= 4)
      fprintferr("GaloisConj:Pmod=%Z\n", Pmod);
    if (DEBUGLEVEL >= 4)
      fprintferr("GaloisConj:Tmod=%Z\n", Tmod);
    for (i = 1; i <= gp; i++)
    {
      Fi = ggcd(Tp, gsubst((GEN) Pmod[i], x, Sp));
      Fi = gdiv(Fi, (GEN) Fi[lgef(Fi) - 1]);
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
      } else
	ppsi[i] = psi[j];
    }
    if (DEBUGLEVEL >= 4)
      fprintferr("GaloisConj:Pm=%d   ppsi=%Z\n", Pm, ppsi);
    galoisanalysis(P, &Pga, 0);
    if (Pga.deg == 0)
    {
      avma = ltop;
      return gzero;		/* Avoid computing the discriminant */
    }
    Pden = gabs(mycoredisc(discsr(P)), DEFAULTPREC);
    Pgb.l = gb->l;
    initborne(P, Pden, &Pgb, Pga.ppp);
    if (Pgb.valabs > gb->valabs)
      PL = recalculeL(P, deriv(P, x), PL, gb, &Pgb);
    PM = vandermondeinverse(PL, P, Pden);
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
  res = cgetg(lg(PG) + lg(split) - 1, t_VEC);
  for (i = 1; i < lg(split); i++)
    res[i] = lcopy((GEN) split[i]);
  for (j = 1; j < lg(PG); j++)
  {
    ulong lbot = 0, av = avma;
    GEN B, tau;
    long t, g;
    long w, sr, dss;
    if (DEBUGLEVEL >= 6)
      fprintferr("GaloisConj:G[%d][1]=%Z\n", j, ((GEN **) PG)[j][1]);
    B = permtocycle(((GEN **) PG)[j][1]);
    if (DEBUGLEVEL >= 6)
      fprintferr("GaloisConj:B=%Z\n", B);
    tau = gmul(mod, permtopol(((GEN **) PG)[j][1], PL, PM, Pden, x));
    tau = gsubst((GEN) Pmod[Pm], x, tau);
    tau = ggcd(Pp, tau);
    tau = gdiv(tau, (GEN) tau[lgef(tau) - 1]);
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
      fprintferr("GaloisConj:w=%d [%d] sr=%d dss=%d\n", w, deg, sr, dss);
    for (t = 0; t < sr; t += dss)
    {
      lbot = avma;
      pf = testpermutation(O, B, w, t, sr, &td);
      if (pf != gzero)
	break;
    }
    if (pf == gzero)
    {
      freetest(&td);
      avma = ltop;
      return gzero;
    } else
    {
      GEN f;
      f = cgetg(3, t_VEC);
      f[1] = (long) pf;
      f[2] = (long) gcopy(((GEN **) PG)[j][2]);
      res[lg(split) + j - 1] = (long) gerepile(av, lbot, f);
    }
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
  ulong ltop = avma, lbot;
  GEN G, L, M, res, aut, L2, M2, grp;
  struct galois_analysis ga;
  struct galois_borne gb;
  int n, i, j, k;
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
    res = cgetg(2, t_COL);
    res[1] = (long) polx[varn(T)];
    return res;
  }
  galoisanalysis(T, &ga, 1);
  if (ga.deg == 0)
  {
    avma = ltop;
    return stoi(ga.p);		/* Avoid computing the discriminant */
  }
  if (!den)
    den = absi(mycoredisc(discsr(T)));
  else
  {
    if (typ(den) != t_INT)
      err(talker, "Second arg. must be integer in galoisconj4");
    den = absi(den);
  }
  gb.l = stoi(ga.l);
  initborne(T, den, &gb, ga.ppp);
  if (DEBUGLEVEL >= 1)
    timer2();
  {
    GEN f = rootpadic(T, gb.l, gb.valabs);
    GEN _p = gmael(f, 1, 2);
    L = gmul(gtrunc(f), gmodulcp(gun, gb.ladicabs));
    gunclone(_p);
  }
  if (DEBUGLEVEL >= 1)
    msgtimer("rootpadic()");
  M = vandermondeinverse(L, T, den);
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
  L2 = gmul(L, gmodulcp(gun, gb.ladicsol));
  M2 = gmul(M, gmodulcp(gun, gb.ladicsol));
  if (flag)
  {
    lbot = avma;
    grp = cgetg(7, t_VEC);
    grp[1] = (long) gcopy(T);
    grp[2] = (long) stoi(ga.l);
    grp[3] = (long) gcopy(L);
    grp[4] = (long) gcopy(M);
    grp[5] = (long) gcopy(den);
  }
  res = cgetg(n + 1, t_VEC);
  res[1] = (long) permidentity(n);
  k = 1;
  for (i = 1; i < lg(G); i++)
  {
    int c = k * (itos(((GEN **) G)[i][2]) - 1);
    for (j = 1; j <= c; j++)	/* I like it */
      res[++k] = (long) applyperm((GEN) res[j], ((GEN **) G)[i][1]);
  }
  if (flag)
  {
    grp[6] = (long) res;
    return gerepile(ltop, lbot, grp);
  }
  aut = cgetg(n + 1, t_COL);
  for (i = 1; i <= n; i++)
    aut[i] = (long) permtopol((GEN) res[i], L2, M2, den, varn(T));
  if (DEBUGLEVEL >= 1)
    msgtimer("Calcul polynomes");
  return gerepileupto(ltop, aut);
}
/* Calcule le nombre d'automorphisme de T avec forte probabilité */
/* pdepart premier nombre premier a tester */
long
numberofconjugates(GEN T, long pdepart)
{
  ulong ltop = avma, ltop2;
  long n, p, nbmax, nbtest;
  long card;
  byteptr primepointer;
  int i;
  GEN L;
  n = degree(T);
  card = sturm(T);
  card = cgcd(card, n - card);
  nbmax = n + 1;
  nbtest = 0;
  L = cgetg(n + 1, t_VECSMALL);
  ltop2 = avma;
  for (p = 0, primepointer = diffptr; nbtest < nbmax && card > 1;)
  {
    long s, c;
    long isram;
    GEN S;
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
      fprintferr("NumberOfConjugates:Nbtest=%d,card=%d,p=%d\n", nbtest, card, p);
    nbtest++;
    avma = ltop2;
  }
  if (DEBUGLEVEL >= 2)
    fprintferr("NumberOfConjugates:card=%d,p=%d\n", card, p);
  avma = ltop;
  return card;
}
GEN
galoisconj0(GEN nf, long flag, GEN d, long prec)
{
  GEN G, T;
  long card;
  if (typ(nf) != t_POL)
  {
    nf = checknf(nf);
    T = (GEN) nf[1];
  } else
    T = nf;
  switch (flag)
  {
   case 0:
    G = galoisconj4(nf, d, 0);
    if (typ(G) != t_INT)	/* Success */
      return G;
    else
    {
      card = G == gzero ? degree(T) : numberofconjugates(T, itos(G));
      if (card != 1)
      {
	if (typ(nf) == t_POL)
	  return galoisconj2pol(nf, card, prec);
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
/* Galois theory related algorithms                         */
/******************************************************************************/
GEN
checkgal(GEN gal)
{
  if (typ(gal) == t_POL)
    err(talker, "please apply galoisinit first");
  if (typ(gal) != t_VEC || lg(gal) != 7)
    err(talker, "Not a Galois field in a Galois related function");
  return gal;
}
GEN
galoisinit(GEN nf, GEN den)
{
  GEN G;
  G = galoisconj4(nf, den, 1);
  if (typ(G) == t_INT)
    err(talker, "galoisinit: field not Galois or Galois group not weakly super solvable");
  return G;
}
GEN
galoispermtopol(GEN gal, GEN perm)
{
  gal = checkgal(gal);
  if (typ(perm) != t_VEC)
    err(typeer, "galoispermtopol:");
  return permtopol(perm, (GEN) gal[3], (GEN) gal[4], (GEN) gal[5], varn((GEN) gal[1]));
}
GEN
galoisfixedfield(GEN gal, GEN perm, GEN p)
{
  ulong ltop = avma, lbot;
  GEN P, S, PL, O, res, mod;
  long x;
  x = varn((GEN) gal[1]);
  gal = checkgal(gal);
  if (typ(perm) != t_VEC)
    err(typeer, "galoisfixedfield:");
  if (p)
  {
    if (typ(p) != t_INT)
      err(talker, "galoisfixedfield: optionnal argument must be an prime integer");
    mod = gmodulcp(gun, p);
  } else
    mod = gun;
  O = vecpermorbite(perm);
  P = corpsfixeorbitemod((GEN) gal[3], O, x, mod, (GEN) gal[2], &PL);
  S = corpsfixeinclusion(O, PL);
  S = vectopol(S, (GEN) gal[3], (GEN) gal[4], (GEN) gal[5], x);
  lbot = avma;
  res = cgetg(3, t_VEC);
  res[1] = (long) gcopy(P);
  res[2] = (long) gmodulcp(S, (GEN) gal[1]);
  return gerepile(ltop, lbot, res);
}
