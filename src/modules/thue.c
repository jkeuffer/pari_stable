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
#include "parinf.h"

/* Thue equation solver. In all the forthcoming remarks, "paper"
 * designs the paper "Thue Equations of High Degree", by Yu. Bilu and
 * G. Hanrot, J. Number Theory (1996). Note that numbering of the constants
 * is that of Hanrot's thesis rather than that of the paper.
 * The last part of the program (bnfisintnorm) was written by K. Belabas. */

/* Check whether tnf is a valid structure */
static int
checktnf(GEN tnf)
{
  int n, R, S, T;
  if (typ(tnf)!=t_VEC || (lg(tnf)!=8 && lg(tnf)!=3)) return 0;
  if (typ(tnf[1]) != t_POL) return 0;
  if (lg(tnf) != 8) return 1; /* S=0 */

  n = degpol(tnf[1]);
  if (n <= 2) err(talker,"invalid polynomial in thue (need n>2)");
  S = sturm((GEN)tnf[1]); T = (n-S)>>1; R = S+T-1;
  (void)checkbnf((GEN)tnf[2]);
  if (typ(tnf[3]) != t_COL || lg(tnf[3]) != n+1) return 0;
  if (typ(tnf[4]) != t_COL || lg(tnf[4]) != R+1) return 0;
  if (typ(tnf[5]) != t_MAT || lg(tnf[5])!=R+1 || lg(gmael(tnf,5,1)) != n+1) return 0;
  if (typ(tnf[6]) != t_MAT || lg(tnf[6])!=R+1 || lg(gmael(tnf,6,1)) != R+1) return 0;
  if (typ(tnf[7]) != t_VEC || lg(tnf[7]) != 7) return 0;
  return 1;
}

static GEN
distoZ(GEN z)
{
  GEN p1 = gfrac(z);
  return gmin(p1, gsub(gun,p1));
}

/* Compensates rounding errors for computation/display of the constants.
 * Round up if dir > 0, down otherwise */
static GEN
myround(GEN x, long dir)
{
  GEN eps = gpowgs(stoi(dir > 0? 10: -10), -10);
  return gmul(x, gadd(gun, eps));
}

/* Returns the index of the largest element in a vector */
static GEN
_Vecmax(GEN Vec, int *ind)
{
  int k, tno = 1, l = lg(Vec);
  GEN tmax = (GEN)Vec[1];
  for (k = 2; k < l; k++)
    if (gcmp((GEN)Vec[k],tmax) > 0) { tmax = (GEN)Vec[k]; tno = k; }
  if (ind) *ind = tno;
  return tmax;
}

static GEN
Vecmax(GEN v) { return _Vecmax(v, NULL); }

static int
Vecmaxind(GEN v) { int i; (void)_Vecmax(v, &i); return i; }

static GEN
tnf_get_roots(GEN poly, long prec, int S, int T)
{
  GEN R0 = roots(poly, prec), R = cgetg(lg(R0), t_COL);
  int k;

  for (k=1; k<=S; k++) R[k] = lreal((GEN)R0[k]);
  /* swap roots to get the usual order */
  for (k=1; k<=T; k++)
  {
    R[k+S]  = R0[2*k+S-1];
    R[k+S+T]= R0[2*k+S];
  }
  return R;
}

/* Computation of the logarithmic height of x (given by embeddings) */
static GEN
LogHeight(GEN x, long prec)
{
  int i, n = lg(x)-1;
  GEN LH = gun;
  for (i=1; i<=n; i++) LH = gmul(LH, gmax(gun, gabs((GEN)x[i], prec)));
  return gdivgs(glog(LH,prec), n);
}

/* |x|^(1/n), x t_INT */
static GEN
absisqrtn(GEN x, long n, long prec) {
  GEN r = itor(x,prec);
  if (signe(r) < 0) r = negr(r);
  return mpsqrtn(r, n);
}

static GEN
get_emb(GEN x, GEN r)
{
  int l = lg(r), i, tx;
  GEN e, y = cgetg(l, t_COL);

  tx = typ(x);
  if (tx != t_INT && tx != t_POL) err(typeer,"get_emb");
  for (i=1; i<l; i++)
  {
    e = poleval(x, (GEN)r[i]);
    if (gcmp0(e)) return NULL;
    y[i] = (long)e;
  }
  return y;
}

/* Computation of the conjugates (sigma_i(v_j)), and log. heights, of elts of v */
static GEN
Conj_LH(GEN v, GEN *H, GEN r, long prec)
{
  int j, l = lg(v);
  GEN e, M = (GEN)cgetg(l,t_MAT);

  (*H) = cgetg(l,t_COL);
  for (j = 1; j < l; j++)
  {
    if (! (e = get_emb((GEN)v[j], r)) ) return NULL; /* FAIL */
    M[j] = (long)e;
    (*H)[j]= (long)LogHeight(e, prec);
  }
  return M;
}

static GEN abslog(GEN x, long prec) { return gabs(glog(x,prec), prec); }
static GEN logabs(GEN x, long prec) { return glog(gabs(x,prec), prec); }

/* Computation of M, its inverse A and precision check (see paper) */
static GEN
T_A_Matrices(GEN MatFU, int r, GEN *eps5, long prec)
{
  GEN A, p1, m1, IntM, nia, eps3, eps2, eps1 = shifti(gun, bit_accuracy(prec));

  m1 = rowextract_i(vecextract_i(MatFU, 1,r), 1,r); /* minor order r */
  m1 = logabs(m1,prec);

  A = invmat(m1);
  IntM = gsub(gmul(A,m1), idmat(r));

  eps2 = gadd(vecmax(gabs(IntM,prec)), ginv(eps1));
  nia = vecmax(gabs(A,prec));

  /* Check for the precision in matrix inversion. See paper, Lemma 2.4.2. */
  p1 = gadd(gmulsg(r, gmul(nia,eps1)), eps2);
  if (gcmp(gmulgs(p1, 2*r), gun) < 0) err(precer,"thue");

  p1 = gadd(gmulsg(r, gdiv(nia,eps1)), eps2);
  eps3 = gmul(gmulsg(2*r*r,nia), p1);
  eps3 = myround(eps3, 1);

  if (DEBUGLEVEL>1) fprintferr("epsilon_3 -> %Z\n",eps3);
  *eps5 = mulsr(r, eps3); return A;
}

/* Performs basic computations concerning the equation.
 * Returns a "tnf" structure containing
 *  1) the polynomial
 *  2) the bnf (used to solve the norm equation)
 *  3) roots, with presumably enough precision
 *  4) The logarithmic heights of units
 *  5) The matrix of conjugates of units
 *  6) its inverse
 *  7) a few technical constants */
static GEN
inithue(GEN P, GEN bnf, long flag, long prec)
{
  GEN MatFU, x0, tnf, tmp, gpmin, dP, csts, ALH, eps5, ro, c1, c2;
  int k,j, n = degpol(P);
  long s,t;

  if (!bnf)
  {
    bnf = bnfinit0(P,1,NULL,prec);
    if (bnf != checkbnf_discard(bnf)) err(talker,"non-monic polynomial in thue");
    if (flag) (void)certifybuchall(bnf);
  }
  nf_get_sign(checknf(bnf), &s, &t);
  ro = tnf_get_roots(P, prec, s, t);
  MatFU = Conj_LH(gmael(bnf,8,5), &ALH, ro, prec);
  if (!MatFU) return NULL; /* FAIL */

  dP = derivpol(P);
  c1 = NULL; /* min |P'(r_i)|, i <= s */
  for (k=1; k<=s; k++)
  {
    tmp = gabs(poleval(dP,(GEN)ro[k]),prec);
    if (!c1 || gcmp(tmp,c1) < 0) c1 = tmp;
  }
  c1 = gdiv(shifti(gun,n-1), c1);
  c1 = gprec_w(myround(c1, 1), DEFAULTPREC);

  c2 = NULL; /* max |r_i - r_j|, i!=j */
  for (k=1; k<=n; k++)
    for (j=k+1; j<=n; j++)
    {
      tmp = gabs(gsub((GEN)ro[j],(GEN)ro[k]), prec);
      if (!c2 || gcmp(c2,tmp) > 0) c2 = tmp;
    }
  c2 = gprec_w(myround(c2, -1), DEFAULTPREC);

  if (t==0) x0 = gun;
  else
  {
    gpmin = NULL; /* min |P'(r_i)|, i > s */
    for (k=1; k<=t; k++)
    {
      tmp = gabs(poleval(dP,(GEN)ro[s+k]), prec);
      if (!gpmin || gcmp(tmp,gpmin) < 0) gpmin = tmp;
    }
    gpmin = gprec_w(gpmin, DEFAULTPREC);

    /* Compute x0. See paper, Prop. 2.2.1 */
    x0 = gmul(gpmin, Vecmax(gabs(imag_i(ro), prec)));
    x0 = mpsqrtn(gdiv(shifti(gun,n-1), x0), n);
  }
  if (DEBUGLEVEL>1) fprintferr("c1 = %Z\nc2 = %Z\n", c1, c2);

  ALH = gmul2n(ALH, 1);
  tnf = cgetg(8,t_VEC); csts = cgetg(7,t_VEC);
  tnf[1] = (long)P;
  tnf[2] = (long)bnf;
  tnf[3] = (long)ro;
  tnf[4] = (long)ALH;
  tnf[5] = (long)MatFU;
  tnf[6] = (long)T_A_Matrices(MatFU, s+t-1, &eps5, prec);
  tnf[7] = (long)csts;
  csts[1] = (long)c1; csts[2] = (long)c2;   csts[3] = (long)LogHeight(ro, prec);
  csts[4] = (long)x0; csts[5] = (long)eps5; csts[6] = (long)stoi(prec);
  return tnf;
}

typedef struct {
  GEN c10, c11, c13, c15, bak, NE, ALH, hal, MatFU, ro, Hmu;
  GEN delta, lambda, errdelta;
  int r, iroot;
} baker_s;

/* Compute Baker's bound c9 and B_0, the bound for the b_i's. See Thm 2.3.1 */
static GEN
Baker(baker_s *BS)
{
  const long prec = DEFAULTPREC;
  GEN tmp, B0, hb0, c9 = gun, ro = BS->ro, ro0 = (GEN)ro[BS->iroot];
  int k, i1, i2, r = BS->r;

  switch (BS->iroot) {
    case 1: i1=2; i2=3; break;
    case 2: i1=1; i2=3; break;
   default: i1=1; i2=2; break;
  }

  /* Compute h_1....h_r */
  for (k=1; k<=r; k++)
  {
    tmp = gdiv(gcoeff(BS->MatFU,i1,k), gcoeff(BS->MatFU,i2,k));
    tmp = gmax(gun, abslog(tmp,prec));
    c9 = gmul(c9, gmax((GEN)BS->ALH[k], gdiv(tmp, BS->bak)));
  }

  /* Compute a bound for the h_0 */
  hb0 = gadd(gmul2n(BS->hal,2), gmul(gdeux, gadd(BS->Hmu,mplog2(prec))));
  tmp = gdiv(gmul(gsub(ro0, (GEN)ro[i2]), (GEN)BS->NE[i1]),
             gmul(gsub(ro0, (GEN)ro[i1]), (GEN)BS->NE[i2]));
  tmp = gmax(gun, abslog(tmp, prec));
  hb0 = gmax(hb0, gdiv(tmp, BS->bak));
  c9 = gmul(c9,hb0);
  /* Multiply c9 by the "constant" factor */
  c9 = gmul(c9, gmul(mulri(mulsr(18,mppi(prec)), gpowgs(stoi(32),4+r)),
                     gmul(gmul(mpfact(r+3), gpowgs(mulis(BS->bak,r+2), r+3)),
                          glog(mulis(BS->bak,2*(r+2)),prec))));
  c9 = gprec_w(myround(c9, 1), DEFAULTPREC);
  /* Compute B0 according to Lemma 2.3.3 */
  B0 = mulsr(2, divrr(addrr(mulrr(c9,mplog(divrr(c9,BS->c10))), mplog(BS->c11)),
                      BS->c10));
  B0 = gmax(B0, dbltor(2.71828183));

  if (DEBUGLEVEL>1) {
    fprintferr("  B0  = %Z\n",B0);
    fprintferr("  Baker = %Z\n",c9);
  }
  return B0;
}

/* || x d ||, x t_REAL, d t_INT */
static GEN
errnum(GEN x, GEN d)
{
  GEN dx = mulir(d, x);
  return mpabs(subri(dx, ground(dx)));
}

/* Try to reduce the bound through continued fractions; see paper. */
static int
CF_1stPass(GEN *B0, GEN kappa, baker_s *BS)
{
  GEN q, ql, qd, l0, denbound = mulri(*B0, kappa);

  if (gcmp(gmul(dbltor(0.1),gsqr(denbound)), ginv(BS->errdelta)) > 0) return -1;

  q = denom( bestappr(BS->delta, denbound) );
  qd = errnum(BS->delta, q);
  ql = errnum(BS->lambda,q);

  l0 = subrr(ql, addrr(mulrr(qd, *B0), divri(dbltor(0.1),kappa)));
  if (signe(l0) <= 0) return 0;

  if (BS->r > 1)
    *B0 = divrr(mplog(divrr(mulir(q,BS->c15), l0)), BS->c13);
  else
  {
    l0 = mulrr(l0,Pi2n(1, DEFAULTPREC));
    *B0 = divrr(mplog(divrr(mulir(q,BS->c11), l0)), BS->c10);
  }
  if (DEBUGLEVEL>1) fprintferr("    B0 -> %Z\n",*B0);
  return 1;
}

/* Check whether a solution has already been found */
static int
new_sol(GEN z, GEN S)
{
  int i, l = lg(S);
  for (i=1; i<l; i++)
    if (gegal(z,(GEN)S[i])) return 0;
  return 1;
}

static void
add_sol(GEN *pS, GEN x, GEN y)
{
  GEN u = cgetg(3,t_VEC); u[1] = (long)x; u[2] = (long)y;
  if (new_sol(u, *pS)) *pS = concatsp(*pS, _vec(u));
}

static void
check_sol(GEN x, GEN y, GEN P, GEN rhs, GEN *pS)
{
  if (gcmp0(y))
  { if (gegal(gpowgs(x,degpol(P)), rhs)) add_sol(pS, x, gzero); }
  else
  { if (gegal(poleval(rescale_pol(P,y),x), rhs)) add_sol(pS, x, y); }
}

/* Check whether a potential solution is a true solution. Return 0 if
 * truncation error (increase precision) */
static int
CheckSol(GEN *pS, GEN z1, GEN z2, GEN P, GEN rhs, GEN ro)
{
  GEN x, y, ro1 = (GEN)ro[1], ro2 = (GEN)ro[2];
  long e;

  y = grndtoi(real_i(gdiv(gsub(z2,z1), gsub(ro1,ro2))), &e);
  if (e > 0) return 0;
  x = gadd(z1, gmul(ro1, y));
  x = grndtoi(real_i(x), &e);
  if (e > 0) return 0;
  if (e <= -13)
  {
    check_sol(     x ,      y,  P,rhs,pS);
    check_sol(gneg(x), gneg(y), P,rhs,pS);
  }
  return 1;
}

/* find q1,q2,q3 st q1 + b q2 + c q3 ~ 0 */
static GEN
GuessQi(GEN b, GEN c, GEN *eps)
{
  GEN Q, Lat, C = gpowgs(stoi(10), 10);

  Lat = idmat(3);
  mael(Lat,1,3) = (long)C;
  mael(Lat,2,3) = lround(gmul(C,b));
  mael(Lat,3,3) = lround(gmul(C,c));

  Q = (GEN)lllint(Lat)[1];
  if (gcmp0((GEN)Q[3])) return NULL; /* FAIL */

  *eps = gadd(gadd((GEN)Q[1], gmul((GEN)Q[2],b)), gmul((GEN)Q[3],c));
  *eps = mpabs(*eps); return Q;
}

/* Check for solutions under a small bound (see paper) */
static GEN
SmallSols(GEN S, int Bx, GEN poly, GEN rhs, GEN ro)
{
  pari_sp av = avma, lim = stack_lim(av, 1);
  const long prec = DEFAULTPREC;
  GEN Hpoly, interm, X, Xn, Xnm1, Y, sqrtnRHS;
  int x, y, j, By, n = degpol(poly);
  double bndyx;

  if (DEBUGLEVEL>1) fprintferr("* Checking for small solutions\n");

  sqrtnRHS = absisqrtn(rhs, n, prec);
  bndyx = gtodouble(gadd(sqrtnRHS, Vecmax(gabs(ro,prec))));

  /* x = 0 first */
  Y = ground(sqrtnRHS);
  if (gegal(gpowgs(Y,n), rhs)) add_sol(&S, Y, gzero);
  Y = negi(Y);
  if (gegal(gpowgs(Y,n), rhs)) add_sol(&S, Y, gzero);
  /* x != 0 */
  for (x = -Bx; x <= Bx; x++)
  {
    if (!x) continue;

    X = stoi(x); Xn = gpowgs(X,n);
    interm = subii(rhs, mulii(Xn, (GEN)poly[2]));
    Xnm1 = Xn; j = 2;
    while (gcmp0(interm))
    {
      Xnm1 = divis(Xnm1, x);
      interm = mulii((GEN)poly[++j], Xnm1);
    }
    /* y | interm */

    Hpoly = rescale_pol(poly,X); /* homogenize */
    By = (int)(x>0? bndyx*x: -bndyx*x);
    if (gegal(gmul((GEN)poly[2],Xn),rhs)) add_sol(&S, gzero, X); /* y = 0 */
    for(y = -By; y <= By; y++)
    {
      if (!y || smodis(interm, y)) continue;
      Y = stoi(y);
      if (gegal(poleval(Hpoly, Y), rhs)) add_sol(&S, Y, X);
    }

    if (low_stack(lim,stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"Check_small");
      S = gerepilecopy(av, S);
    }
  }
  return S;
}

/* Computes [x]! */
static double
fact(double x)
{
  double ft = 1.0;
  x = floor(x); while (x>1) { ft *= x; x--; }
  return ft ;
}

/* From a polynomial and optionally a system of fundamental units for the
 * field defined by poly, computes all relevant constants needed to solve
 * the equation P(x,y)=a given the solutions of N_{K/Q}(x)=a (see inithue). */
GEN
thueinit(GEN poly, long flag, long prec)
{
  GEN tnf, bnf = NULL;
  pari_sp av = avma;
  long k, s;

  if (checktnf(poly)) { bnf = checkbnf((GEN)poly[2]); poly = (GEN)poly[1]; }
  if (typ(poly)!=t_POL) err(notpoler,"thueinit");
  if (degpol(poly) <= 2) err(talker,"invalid polynomial in thue (need deg>2)");

  if (!gisirreducible(poly)) err(redpoler,"thueinit");
  s = sturm(poly);
  if (s)
  {
    long PREC, n = degpol(poly);
    double d, dr, dn = (double)n;

    dr = (double)((s+n-2)>>1); /* s+t-1 */
    d = dn*(dn-1)*(dn-2);
    /* Guess precision by approximating Baker's bound. The guess is most of
     * the time not sharp, ie 10 to 30 decimal digits above what is _really_
     * necessary. Note that the limiting step is the reduction. See paper. */
    PREC = 3 + (long)((5.83 + (dr+4)*5 + log(fact(dr+3)) + (dr+3)*log(dr+2) +
		     (dr+3)*log(d) + log(log(2*d*(dr+2))) + (dr+1)) / 10.);
    if (PREC < prec) PREC = prec;
    for (;;)
    {
      if (( tnf = inithue(poly, bnf, flag, PREC) )) break;
      PREC = (PREC<<1)-2;
      if (DEBUGLEVEL>1) err(warnprec,"thueinit",PREC);
      bnf = NULL; avma = av;
    }
  }
  else
  {
    GEN c0 = gun, ro = roots(poly, DEFAULTPREC);
    for (k=1; k<lg(ro); k++) c0 = gmul(c0, imag_i((GEN)ro[k]));
    c0 = ginv( mpabs(c0) );
    tnf = cgetg(3,t_VEC);
    tnf[1] = (long)poly;
    tnf[2] = (long)c0;
  }
  return gerepilecopy(av,tnf);
}

static GEN
get_B0(int i1, GEN Delta, GEN Lambda, GEN eps5, long prec, baker_s *BS)
{
  GEN delta, lambda, errdelta, B0 = Baker(BS);
  int i2, r = BS->r;

  i2 = (i1 == 1)? 2: 1;
  for(;;) /* i2 from 1 to r unless r = 1 [then i2 = 2] */
  {
    if (r > 1)
    {
      delta = divrr((GEN)Delta[i2],(GEN)Delta[i1]);
      lambda = gdiv(gsub(gmul((GEN)Delta[i2],(GEN)Lambda[i1]),
                         gmul((GEN)Delta[i1],(GEN)Lambda[i2])),
                    (GEN)Delta[i1]);
      errdelta = mulrr(addsr(1,delta),
                       divrr(eps5, subrr(mpabs((GEN)Delta[i1]),eps5)));
    }
    else
    { /* r == 1, single fundamental unit (i1 = s = t = 1) */
      GEN p1, Pi2 = Pi2n(1, prec);
      GEN fu = (GEN)BS->MatFU[1], ro = BS->ro;

      p1 = gdiv((GEN)fu[2], (GEN)fu[3]);
      delta = divrr(garg(p1,prec), Pi2);

      p1 = gmul(gdiv(gsub((GEN)ro[1], (GEN)ro[2]),
                     gsub((GEN)ro[1], (GEN)ro[3])),
                gdiv((GEN)BS->NE[3], (GEN)BS->NE[2]));
      lambda = divrr(garg(p1,prec), Pi2);

      errdelta = gdiv(gmul2n(gun, 1 - bit_accuracy(prec)),
                      gabs((GEN)fu[2],prec));
    }
    BS->delta = delta;
    BS->lambda= lambda; BS->errdelta = errdelta;
    if (DEBUGLEVEL>1) fprintferr("  errdelta = %Z\n",errdelta);

    if (DEBUGLEVEL>1) fprintferr("  Entering CF...\n");
    /* Reduce B0 as long as we make progress: newB0 < oldB0 - 0.1 */
    for (;;)
    {
      GEN oldB0 = B0, kappa = stoi(10);
      int cf;

      for (cf = 0; cf < 10; cf++, kappa = mulis(kappa,10))
      {
        int res = CF_1stPass(&B0, kappa, BS);
        if (res < 0) return NULL; /* prec problem */
        if (res) break;
        if (DEBUGLEVEL>1) fprintferr("CF failed. Increasing kappa\n");
      }
      if (cf == 10)
      { /* Semirational or totally rational case */
        GEN Q, ep, q, l0, denbound;

        if (! (Q = GuessQi(delta, lambda, &ep)) ) break;

        denbound = gadd(B0, absi((GEN)Q[2]));
        q = denom( bestappr(delta, denbound) );
        l0 = subrr(errnum(delta, q), ep);
        if (signe(l0) <= 0) break;

        B0 = divrr(mplog(divrr(mulir((GEN)Q[3], BS->c15), l0)),  BS->c13);
        if (DEBUGLEVEL>1) fprintferr("Semirat. reduction: B0 -> %Z\n",B0);
      }
      /* if no progress, stop */
      if (gcmp(oldB0, gadd(B0,dbltor(0.1))) <= 0) return gmin(oldB0, B0);
    }
    i2++; if (i2 == i1) i2++;
    if (i2 > r) break;
  }
  err(bugparier,"thue (totally rational case)");
  return NULL; /* not reached */
}

static GEN
LargeSols(GEN tnf, GEN rhs, GEN ne, GEN *pro, GEN *pS)
{
  GEN Vect, P, ro, bnf, MatFU, A, csts, dP, vecdP;
  GEN c1,c2,c3,c4,c10,c11,c13,c14,c15, x0, x1, x2, x3, b, zp1, tmp, eps5;
  int iroot, ine, n, i, r;
  long upb, bi1, Prec, prec, s,t;
  baker_s BS;
  pari_sp av = avma;

  bnf  = (GEN)tnf[2];
  if (!ne) ne = bnfisintnorm(bnf, rhs);
  if (lg(ne)==1) return NULL;
  nf_get_sign(checknf(bnf), &s, &t);
  BS.r = r = s+t-1;
  P      = (GEN)tnf[1]; n = degpol(P);
  ro     = (GEN)tnf[3];
  BS.ALH = (GEN)tnf[4];
  MatFU  = (GEN)tnf[5];
  A      = (GEN)tnf[6];
  csts   = (GEN)tnf[7];
  c1     = (GEN)csts[1]; c1 = gmul(absi(rhs), c1);
  c2     = (GEN)csts[2];
  BS.hal = (GEN)csts[3];
  x0     = (GEN)csts[4];
  eps5   = (GEN)csts[5];
  Prec = gtolong((GEN)csts[6]);
  BS.MatFU = MatFU;
  BS.bak = mulss(n, (n-1)*(n-2)); /* safe */
  *pS = cgetg(1, t_VEC);

  if (t) x0 = gmul(x0, absisqrtn(rhs, n, Prec));
  tmp = divrr(c1,c2);
  c3 = mulrr(dbltor(1.39), tmp);
  c4 = mulsr(n-1, c3);
  x1 = gmax(x0, mpsqrtn(mulsr(2,tmp),n));

  Vect = cgetg(r+1,t_COL); for (i=1; i<=r; i++) Vect[i]=un;
  Vect = gmul(gabs(A,DEFAULTPREC), Vect);
  c14 = mulrr(c4, Vecmax(Vect));
  x2 = gmax(x1, mpsqrtn(mulsr(10,c14), n));
  if (DEBUGLEVEL>1) {
    fprintferr("x1 -> %Z\n",x1);
    fprintferr("x2 -> %Z\n",x2);
    fprintferr("c14 = %Z\n",c14);
  }

  dP = derivpol(P);
  vecdP = cgetg(s+1, t_VEC);
  for (i=1; i<=s; i++) vecdP[i] = (long)poleval(dP, (GEN)ro[i]);

  zp1 = dbltor(0.01);
  x3 = gmax(x2, mpsqrtn(mulsr(2,divrr(c14,zp1)),n));

  b = cgetg(r+1,t_COL);
  for (iroot=1; iroot<=s; iroot++)
  {
    GEN Delta, MatNE, Hmu, c5, c7;

    Vect = cgetg(r+1,t_COL); for (i=1; i<=r; i++) Vect[i] = un;
    if (iroot <= r) Vect[iroot] = lstoi(1-n);
    Delta = gmul(A,Vect);

    c5 = Vecmax(gabs(Delta,Prec));
    c5  = myround(gprec_w(c5,DEFAULTPREC), 1);
    c7  = mulsr(r,c5);
    c10 = divsr(n,c7); BS.c10 = c10;
    c13 = divsr(n,c5); BS.c13 = c13;
    if (DEBUGLEVEL>1) {
      fprintferr("* real root no %ld/%ld\n", iroot,s);
      fprintferr("  c10 = %Z\n",c10);
      fprintferr("  c13 = %Z\n",c13);
    }

    prec = Prec;
    for (;;)
    {
      if (( MatNE = Conj_LH(ne, &Hmu, ro, prec) )) break;
      prec = (prec<<1)-2;
      if (DEBUGLEVEL>1) err(warnprec,"thue",prec);
      ro = tnf_get_roots(P, prec, s, t);
    }
    BS.ro    = ro;
    BS.iroot = iroot;

    for (ine=1; ine<lg(ne); ine++)
    {
      GEN Lambda, B0, c6, c8;
      GEN NE = (GEN)MatNE[ine], Vect2 = cgetg(r+1,t_COL);
      int k, i1;

      if (DEBUGLEVEL>1) fprintferr("  - norm sol. no %ld/%ld\n",ine,lg(ne)-1);
      for (k=1; k<=r; k++)
      {
        if (k == iroot)
          tmp = gdiv(rhs, gmul((GEN)vecdP[k], (GEN)NE[k]));
        else
          tmp = gdiv(gsub((GEN)ro[iroot],(GEN)ro[k]), (GEN)NE[k]);
        Vect2[k] = llog(gabs(tmp,prec), prec);
      }
      Lambda = gmul(A,Vect2);

      c6 = addrr(dbltor(0.1), Vecmax(gabs(Lambda,DEFAULTPREC)));
      c6 = myround(c6, 1);
      c8 = addrr(dbltor(1.23), mulsr(r,c6));
      c11= mulrr(mulsr(2,c3) , mpexp(divrr(mulsr(n,c8),c7)));
      c15= mulrr(mulsr(2,c14), mpexp(divrr(mulsr(n,c6),c5)));

      if (DEBUGLEVEL>1) {
        fprintferr("  c6  = %Z\n",c6);
        fprintferr("  c8  = %Z\n",c8);
        fprintferr("  c11 = %Z\n",c11);
        fprintferr("  c15 = %Z\n",c15);
      }
      BS.c11 = c11;
      BS.c15 = c15;
      BS.NE = NE;
      BS.Hmu = (GEN)Hmu[ine];

      i1 = Vecmaxind(gabs(Delta,prec));
      if (! (B0 = get_B0(i1, Delta, Lambda, eps5, prec, &BS)) ) goto PRECPB;

     /* For each possible value of b_i1, compute the b_i's
      * and 2 conjugates of z = x - alpha y. Then check. */
      upb = gtolong(gceil(B0));
      for (bi1=-upb; bi1<=upb; bi1++)
      {
        GEN z1, z2;
        for (i=1; i<=r; i++)
        {
          b[i] = ldiv(gsub(gmul((GEN)Delta[i], stoi(bi1)),
                           gsub(gmul((GEN)Delta[i],(GEN)Lambda[i1]),
                                gmul((GEN)Delta[i1],(GEN)Lambda[i]))),
                      (GEN)Delta[i1]);
          if (gcmp(distoZ((GEN)b[i]), zp1) > 0) break;
        }
        if (i <= r) continue;

        z1 = z2 = gun;
        for(i=1; i<=r; i++)
        {
          GEN c = ground((GEN)b[i]);
          z1 = gmul(z1, powgi(gcoeff(MatFU,1,i), c));
          z2 = gmul(z2, powgi(gcoeff(MatFU,2,i), c));
        }
        z1 = gmul(z1, (GEN)NE[1]);
        z2 = gmul(z2, (GEN)NE[2]);
        if (!CheckSol(pS, z1,z2,P,rhs,ro)) goto PRECPB;
      }
    }
  }
  *pro = ro; return x3;

PRECPB:
  ne = gerepilecopy(av, ne);
  prec += 5 * (DEFAULTPREC-2);
  if (DEBUGLEVEL>1) err(warnprec,"thue",prec);
  tnf = inithue(P, bnf, 0, prec);
  return LargeSols(tnf, rhs, ne, pro, pS);
}

/* Given a tnf structure as returned by thueinit, a RHS and
 * optionally the solutions to the norm equation, returns the solutions to
 * the Thue equation F(x,y)=a
 */
GEN
thue(GEN tnf, GEN rhs, GEN ne)
{
  pari_sp av = avma;
  GEN P, ro, x3, S;

  if (!checktnf(tnf)) err(talker,"not a tnf in thue");
  if (typ(rhs) != t_INT) err(typeer,"thue");

  P = (GEN)tnf[1];
  if (lg(tnf) == 8)
  {
    x3 = LargeSols(tnf, rhs, ne, &ro, &S);
    if (!x3) { avma = av; return cgetg(1,t_VEC); }
  }
  else
  { /* Case s=0. All solutions are "small". */
    GEN c0   = (GEN)tnf[2]; /* t_REAL */
    S = cgetg(1,t_VEC);
    ro = roots(P, DEFAULTPREC);
    x3 = mpsqrtn(mulir(constant_term(P), divir(absi(rhs),c0)), degpol(P));
  }
  return gerepilecopy(av, SmallSols(S, gtolong(x3), P, rhs, ro));
}

static GEN *Relations; /* primes above a, expressed on generators of Cl(K) */
static GEN *Partial;   /* list of vvectors, Partial[i] = Relations[1..i] * u[1..i] */
static GEN *gen_ord;   /* orders of generators of Cl(K) given in bnf */

static long *f;        /* f[i] = f(Primes[i]/p), inertial degree */
static long *n;        /* a = prod p^{ n_p }. n[i]=n_p if Primes[i] divides p */
static long *inext;    /* index of first P above next p, 0 if p is last */
static long *S;        /* S[i] = n[i] - sum_{ 1<=k<=i } f[k].u[k] */
static long *u;        /* We want principal ideals I = prod Primes[i]^u[i] */
static GEN  *normsol; /* lists of copies of the u[] which are solutions */

static long Nprimes; /* length(Relations) = #{max ideal above divisors of a} */
static long sindex, smax; /* current index in normsol; max. index */

/* u[1..i] has been filled. Norm(u) is correct.
 * Check relations in class group then save it.
 */
static void
test_sol(long i)
{
  long k,*sol;

  if (Partial)
  {
    pari_sp av=avma;
    for (k=1; k<lg(Partial[1]); k++)
      if ( signe(modii( (GEN)Partial[i][k], gen_ord[k] )) )
        { avma=av; return; }
    avma=av;
  }
  if (sindex == smax)
  {
    long new_smax = smax << 1;
    GEN *new_normsol = (GEN*)new_chunk(new_smax+1);

    for (k=1; k<=smax; k++) new_normsol[k] = normsol[k];
    normsol = new_normsol; smax = new_smax;
  }
  sol = cgetg(Nprimes+1,t_VECSMALL);
  normsol[++sindex] = sol;

  for (k=1; k<=i; k++)       sol[k] = u[k];
  for (   ; k<=Nprimes; k++) sol[k] = 0;
  if (DEBUGLEVEL>2)
  {
    fprintferr("sol = %Z\n",sol);
    if (Partial) fprintferr("Partial = %Z\n",Partial);
    flusherr();
  }
}
static void
fix_Partial(long i)
{
  long k;
  pari_sp av = avma;
  for (k=1; k<lg(Partial[1]); k++)
    addiiz(
      (GEN) Partial[i-1][k],
            mulis((GEN) Relations[i][k], u[i]),
      (GEN) Partial[i][k]
    );
  avma=av;
}

/* Recursive loop. Suppose u[1..i] has been filled
 * Find possible solutions u such that, Norm(prod Prime[i]^u[i]) = a, taking
 * into account:
 *  1) the relations in the class group if need be.
 *  2) the factorization of a.
 */
static void
isintnorm_loop(long i)
{
  if (S[i] == 0) /* sum u[i].f[i] = n[i], do another prime */
  {
    int k;
    if (inext[i] == 0) { test_sol(i); return; }

    /* there are some primes left */
    if (Partial) gaffect(Partial[i], Partial[inext[i]-1]);
    for (k=i+1; k < inext[i]; k++) u[k]=0;
    i=inext[i]-1;
  }
  else if (i == inext[i]-2 || i == Nprimes-1)
  {
    /* only one Prime left above prime; change prime, fix u[i+1] */
    if (S[i] % f[i+1]) return;
    i++; u[i] = S[i-1] / f[i];
    if (Partial) fix_Partial(i);
    if (inext[i]==0) { test_sol(i); return; }
  }

  i++; u[i]=0;
  if (Partial) gaffect(Partial[i-1], Partial[i]);
  if (i == inext[i-1])
  { /* change prime */
    if (inext[i] == i+1 || i == Nprimes) /* only one Prime above p */
    {
      S[i]=0; u[i] = n[i] / f[i]; /* we already know this is exact */
      if (Partial) fix_Partial(i);
    }
    else S[i] = n[i];
  }
  else S[i] = S[i-1]; /* same prime, different Prime */
  for(;;)
  {
    isintnorm_loop(i); S[i]-=f[i]; if (S[i]<0) break;
    if (Partial)
      gaddz(Partial[i], Relations[i], Partial[i]);
    u[i]++;
  }
}

static void
get_sol_abs(GEN bnf, GEN a, GEN *ptPrimes)
{
  GEN dec, fact, primes, Primes, *Fact;
  long *gcdlist, gcd,nprimes,Ngen,i,j;

  if (gcmp1(a))
  {
    GEN sol = cgetg(Nprimes+1, t_VECSMALL);
    sindex = 1; normsol = (GEN*) new_chunk(2);
    normsol[1] = sol; for (i=1; i<=Nprimes; i++) sol[i] = 0;
    return;
  }

  fact=factor(a); primes=(GEN)fact[1];
  nprimes=lg(primes)-1; sindex = 0;
  gen_ord = (GEN *) mael3(bnf,8,1,2); Ngen = lg(gen_ord)-1;

  Fact = (GEN*) new_chunk(1+nprimes);
  gcdlist = new_chunk(1+nprimes);

  Nprimes=0;
  for (i=1; i<=nprimes; i++)
  {
    long ldec;

    dec = primedec(bnf,(GEN)primes[i]); ldec = lg(dec)-1;
    gcd = itos(gmael(dec,1,4));

    /* check that gcd_{P|p} f_P | n_p */
    for (j=2; gcd>1 && j<=ldec; j++)
      gcd = cgcd(gcd,itos(gmael(dec,j,4)));

    gcdlist[i]=gcd;

    if (gcd != 1 && smodis(gmael(fact,2,i),gcd))
    {
      if (DEBUGLEVEL>2)
        { fprintferr("gcd f_P  does not divide n_p\n"); flusherr(); }
      return;
    }
    Fact[i] = dec; Nprimes += ldec;
  }

  f = new_chunk(1+Nprimes); u = new_chunk(1+Nprimes);
  n = new_chunk(1+Nprimes); S = new_chunk(1+Nprimes);
  inext = new_chunk(1+Nprimes);
  Primes = cgetg(1+Nprimes, t_VEC);
  *ptPrimes = Primes;

  if (Ngen)
  {
    Partial   = (GEN*) new_chunk(1+Nprimes);
    Relations = (GEN*) new_chunk(1+Nprimes);
  }
  else /* trivial class group, no relations to check */
    Relations = Partial = NULL;

  j=0;
  for (i=1; i<=nprimes; i++)
  {
    long k,lim,v, vn=itos(gmael(fact,2,i));

    gcd = gcdlist[i];
    dec = Fact[i]; lim = lg(dec);
    v = (i==nprimes)? 0: j + lim;
    for (k=1; k < lim; k++)
    {
      j++; Primes[j] = dec[k];
      f[j] = itos(gmael(dec,k,4)) / gcd;
      n[j] = vn / gcd; inext[j] = v;
      if (Partial)
	Relations[j] = isprincipal(bnf, (GEN)Primes[j]);
    }
  }
  if (Partial)
  {
    for (i=1; i <= Nprimes; i++)
      if (!gcmp0(Relations[i])) break;
    if (i > Nprimes) Partial = NULL; /* all ideals dividing a are principal */
  }
  if (Partial)
    for (i=0; i<=Nprimes; i++) /* Partial[0] needs to be initialized */
    {
      Partial[i]=cgetg(Ngen+1,t_COL);
      for (j=1; j<=Ngen; j++)
      {
	Partial[i][j]=lgeti(4);
	gaffect(gzero,(GEN) Partial[i][j]);
      }
    }
  smax=511; normsol = (GEN*) new_chunk(smax+1);
  S[0]=n[1]; inext[0]=1; isintnorm_loop(0);
}

/* Look for unit of norm -1. Return 1 if it exists and set *unit, 0 otherwise */
static long
get_unit_1(GEN bnf, GEN *unit)
{
  GEN tu, v, nf = checknf(bnf);
  long i, n = degpol(nf[7]);

  if (DEBUGLEVEL > 2) fprintferr("looking for a fundamental unit of norm -1\n");

  tu = gmael3(bnf,8,4,2);
  /* torsion unit ok iff is -1 and odd degree */
  if (odd(n) && gcmp_1(tu)) { *unit = tu; return 1; }
  v = signunits(bnf);
  for (i = 1; i < lg(v); i++)
  {
    GEN s = sum((GEN)v[i], 1, lg(v[i])-1);
    if (mpodd(s)) {
      GEN fu = check_units(bnf, "bnfisintnorm");
      *unit = (GEN)fu[i]; return 1;
    }
  }
  return 0;
}

GEN
bnfisintnorm(GEN bnf, GEN a)
{
  GEN nf, res, unit, x, Primes;
  long sa, i, norm_1;
  pari_sp av = avma;

  bnf = checkbnf(bnf); nf = (GEN)bnf[7];
  if (typ(a)!=t_INT)
    err(talker,"expected an integer in bnfisintnorm");
  sa = signe(a);
  if (sa == 0)  return _vec(gzero);
  if (gcmp1(a)) return _vec(gun);

  get_sol_abs(bnf, absi(a), &Primes);

  res = cgetg(1,t_VEC); unit = NULL;
  norm_1 = 0; /* gcc -Wall */
  for (i=1; i<=sindex; i++)
  {
    long sNx;
    x = normsol[i];
    if (!Nprimes) { sNx = 1; x = gun; }
    else
    {
      x = isprincipalfact(bnf, Primes, small_to_vec(x), NULL,
                          nf_FORCE | nf_GEN_IF_PRINCIPAL);
      x = basistoalg(nf, x);
      sNx = signe(gnorm(x));
    }
    /* x solution, up to sign */
    if (sNx != sa)
    {
      if (! unit) norm_1 = get_unit_1(bnf, &unit);
      if (norm_1) x = gmul(unit,x);
      else
      {
        if (DEBUGLEVEL > 2) fprintferr("%Z eliminated because of sign\n",x);
        continue;
      }
    }
    res = concatsp(res, lift_intern(x));
  }
  return gerepilecopy(av,res);
}
