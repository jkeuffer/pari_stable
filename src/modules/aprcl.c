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
/*                    THE APRCL PRIMALITY TEST                     */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
extern GEN mulmat_pol(GEN A, GEN x);
extern GEN centermod_i(GEN x, GEN p, GEN ps2);

typedef struct Red {
/* global data */
  GEN N; /* prime we are certifying */
  GEN N2; /* floor(N/2) */
/* globa data for flexible window */
  int k, lv;
  ulong mask;
/* reduction data */
  long n;
  GEN C; /* polcyclo(n) */
  GEN (*red)(GEN x, struct Red*);
} Red;

typedef struct Cache { /* data associated to p^k */
  GEN aall, tall;
  GEN cyc; 
  GEN E;
  GEN eta;
  GEN matvite, matinvvite;
  GEN avite, pkvite;
  ulong ctsgt; /* DEBUG */
} Cache;

static GEN
makepoldeg1(GEN c, GEN d)
{
  GEN z;
  if (signe(c)) {
    z = cgetg(4,t_POL); z[1] = evalsigne(1);
    z[2] = (long)d; z[3] = (long)c;
  } else if (signe(d)) {
    z = cgetg(3,t_POL); z[1] = evalsigne(1);
    z[2] = (long)d;
  } else {
    z = cgetg(2,t_POL); z[1] = evalsigne(0);
  }
  return z;
}

/* T mod polcyclo(p), assume deg(T) < 2p */
static GEN
red_cyclop(GEN T, long p)
{
  long i, d;
  GEN y, *z;

  d = degpol(T) - p; /* < p */
  if (d <= -2) return T;

  /* reduce mod (x^p - 1) */
  y = dummycopy(T); z = (GEN*)(y+2);
  for (i = 0; i<=d; i++) z[i] = addii(z[i], z[i+p]);

  /* reduce mod x^(p-1) + ... + 1 */
  d = p-1;
  if (signe(z[d]))
    for (i=0; i<d; i++) z[i] = subii(z[i], z[d]);
  return normalizepol_i(y, d+2);
}

/* x t_VECSMALL, as red_cyclo2n_ip */
static GEN
u_red_cyclo2n_ip(GEN x, int n)
{
  long i, pow2 = 1<<(n-1);
  GEN z;

  for (i = lg(x)-1; i>pow2; i--) x[i-pow2] -= x[i];
  for (; i>0; i--)
    if (x[i]) break;
  i += 2;
  z = cgetg(i, t_POL); z[1] = evalsigne(1);
  for (i--; i>=2; i--) z[i] = lstoi(x[i-1]);
  return z;
}
/* x t_POL, n > 0. Return x mod polcyclo(2^n) = (x^(2^(n-1)) + 1). IN PLACE */
static GEN
red_cyclo2n_ip(GEN x, int n)
{
  long i, pow2 = 1<<(n-1);
  for (i = lg(x)-1; i>pow2+1; i--)
    if (signe(x[i])) x[i-pow2] = lsubii((GEN)x[i-pow2], (GEN)x[i]);
  return normalizepol_i(x, i+1);
}
static GEN
red_cyclo2n(GEN x, int n) { return red_cyclo2n_ip(dummycopy(x), n); }

/* x a non-zero VECSMALL */
static GEN
smallpolrev(GEN x)
{
  long i,j, lx = lg(x);
  GEN y;

  while (lx-- && x[lx]==0) /* empty */;
  i = lx+2; y = cgetg(i,t_POL);
  y[1] = evalsigne(1);
  for (j=2; j<i; j++) y[j] = lstoi(x[j-1]);
  return y;
}

/* x polynomial in t_VECSMALL form, T t_POL return x mod T */
static GEN
u_red(GEN x, GEN T) {
  return gres(smallpolrev(x), T);
}

/* special case R->C = polcyclo(2^n) */
static GEN
_red_cyclo2n(GEN x, Red *R) {
  return centermod_i(red_cyclo2n(x, R->n), R->N, R->N2);
}
/* special case R->C = polcyclo(p) */
static GEN
_red_cyclop(GEN x, Red *R) {
  return centermod_i(red_cyclop(x, R->n), R->N, R->N2);
}
static GEN
_red(GEN x, Red *R) {
  return centermod_i(gres(x, R->C), R->N, R->N2);
}
static GEN
_redsimple(GEN x, Red *R) { return centermodii(x, R->N, R->N2); }

static GEN
sqrmod(GEN x, Red *R) {
  return R->red(gsqr(x), R);
}

static GEN
sqrconst(GEN pol, Red *R)
{
  GEN z = cgetg(3,t_POL);
  z[2] = (long)centermodii(sqri((GEN)pol[2]), R->N, R->N2);
  z[1] = pol[1]; return z;
}

/* pol^2 mod (x^2+x+1, N) */
static GEN
sqrmod3(GEN pol, Red *R)
{
  GEN a,b,bma,A,B;
  long lv = lg(pol);

  if (lv==2) return pol;
  if (lv==3) return sqrconst(pol, R);
  a = (GEN)pol[3];
  b = (GEN)pol[2]; bma = subii(b,a);
  A = centermodii(mulii(a,addii(b,bma)), R->N, R->N2);
  B = centermodii(mulii(bma,addii(a,b)), R->N, R->N2);
  return makepoldeg1(A,B);
}

/* pol^2 mod (x^2+1,N) */
static GEN
sqrmod4(GEN pol, Red *R)
{
  GEN a,b,A,B;
  long lv = lg(pol);

  if (lv==2) return pol;
  if (lv==3) return sqrconst(pol, R);
  a = (GEN)pol[3];
  b = (GEN)pol[2];
  A = centermodii(mulii(a, shifti(b,1)), R->N, R->N2);
  B = centermodii(mulii(subii(b,a),addii(b,a)), R->N, R->N2);
  return makepoldeg1(A,B);
}

/* pol^2 mod (polcyclo(5),N) */
static GEN
sqrmod5(GEN pol, Red *R)
{
  GEN c2,b,c,d,A,B,C,D;
  long lv = lg(pol);

  if (lv==2) return pol;
  if (lv==3) return sqrconst(pol, R);
  c = (GEN)pol[3]; c2 = shifti(c,1);
  d = (GEN)pol[2];
  if (lv==4)
  {
    A = sqri(d);
    B = mulii(c2, d);
    C = sqri(c);
    A = centermodii(A, R->N, R->N2);
    B = centermodii(B, R->N, R->N2);
    C = centermodii(C, R->N, R->N2); return coefs_to_pol(3,A,B,C);
  }
  b = (GEN)pol[4];
  if (lv==5)
  {
    A = mulii(b, subii(c2,b));
    B = addii(sqri(c), mulii(b, subii(shifti(d,1),b)));
    C = subii(mulii(c2,d), sqri(b));
    D = mulii(subii(d,b), addii(d,b));
  }
  else
  { /* lv == 6 */
    GEN a = (GEN)pol[5], a2 = shifti(a,1);
    /* 2a(d - c) + b(2c - b) */
    A = addii(mulii(a2, subii(d,c)), mulii(b, subii(c2,b)));
    /* c(c - 2a) + b(2d - b) */
    B = addii(mulii(c, subii(c,a2)), mulii(b, subii(shifti(d,1),b)));
    /* (a-b)(a+b) + 2c(d - a) */
    C = addii(mulii(subii(a,b),addii(a,b)), mulii(c2,subii(d,a)));
    /* 2a(b - c) + (d-b)(d+b) */
    D = addii(mulii(a2, subii(b,c)), mulii(subii(d,b), addii(d,b)));
  }
  A = centermodii(A, R->N, R->N2);
  B = centermodii(B, R->N, R->N2);
  C = centermodii(C, R->N, R->N2);
  D = centermodii(D, R->N, R->N2); return coefs_to_pol(4,A,B,C,D);
}

static GEN
_mul(GEN x, GEN y, Red *R) { return R->red(gmul(x,y), R); }

/* jac^floor(N/pk) mod (N, cyclo(pk)), flexible window */
static GEN
_powpolmod(Cache *C, GEN jac, Red *R, GEN (*_sqr)(GEN, Red *))
{
  const GEN taba = C->aall;
  const GEN tabt = C->tall;
  const int efin = lg(taba)-1, lv = R->lv;
  GEN vz, res = jac, pol2 = _sqr(res, R);
  int f;
  pari_sp av;

  vz = cgetg(lv+1, t_VEC); vz[1] = (long)res;
  for (f=2; f<=lv; f++) vz[f] = (long)_mul((GEN)vz[f-1], pol2, R);
  av = avma;
  for (f = efin; f >= 1; f--)
  {
    GEN t = (GEN)vz[taba[f]];
    int tf = tabt[f];
    res = f==efin ? t
                  : _mul(t, res, R);
    while (tf--) res = _sqr(res, R);
    if ((f&7) == 0) res = gerepilecopy(av, res);
  }
  return res;
}

static GEN
_powpolmodsimple(Cache *C, Red *R, GEN jac)
{
  GEN w = mulmat_pol(C->matvite, jac);
  int j, ph = lg(w);

  R->red = &_redsimple;
  for (j=1; j<ph; j++)
    w[j] = (long)_powpolmod(C, centermodii((GEN)w[j], R->N, R->N2), R, &sqrmod);
  w = centermod_i( gmul(C->matinvvite, w), R->N, R->N2 );
  return vec_to_pol(w, 0);
}

static GEN
powpolmod(Cache *C, Red *R, int p, int k, GEN jac)
{
  GEN (*_sqr)(GEN, Red *);

  if (DEBUGLEVEL>2) C->ctsgt++;
  if (C->matvite) return _powpolmodsimple(C, R, jac);
  if (p == 2) /* p = 2 */
  {
    if (k == 2) _sqr = &sqrmod4;
    else        _sqr = &sqrmod;
    R->n = k;
    R->red = &_red_cyclo2n;
  } else if (k == 1)
  {
    if      (p == 3) _sqr = &sqrmod3;
    else if (p == 5) _sqr = &sqrmod5;
    else             _sqr = &sqrmod;
    R->n = p;
    R->red = &_red_cyclop;
  } else {
    R->red = &_red; _sqr = &sqrmod;
  }
  return _powpolmod(C, jac, R, _sqr);
}

static GEN
e(ulong t)
{
  GEN fa, P, E, s;
  ulong nbd, m, k, d;
  int lfa, i, j;

  fa = decomp(utoi(t));
  P = (GEN)fa[1]; settyp(P, t_VECSMALL);
  E = (GEN)fa[2]; settyp(E, t_VECSMALL); lfa = lg(P);
  nbd = 1;
  for (i=1; i<lfa; i++)
  {
    E[i] = itos((GEN)E[i]) + 1;
    P[i] = itos((GEN)P[i]);
    nbd *= E[i];
  }
  s = gdeux; /* nbd = number of divisors */
  for (k=0; k<nbd; k++)
  {
    m = k; d = 1;
    for (j=1; m; j++)
    {
      d *= u_pow(P[j], m % E[j]);
      m /= E[j];
    }
    /* d runs through the divisors of t */
    if (BSW_psp(utoi(++d)))
      s = muliu(s, (ulong)u_pow(d, 1 + u_val(t,d)));
  }
  return s;
}

static ulong
compt(GEN N)
{
  pari_sp av0 = avma;
  ulong C, t;
  GEN B;

  B = mulsr(100, divrr(glog(N,DEFAULTPREC), dbltor(log(10.))));
  C = itos( gceil(B) );
  avma = av0;
  /* C < [200*log_10 e(t)] ==> return t. For e(t) < 10^529, N < 10^1058 */
  if (C <    540) return        6;
  if (C <    963) return       12;
  if (C <   1023) return       24;
  if (C <   1330) return       48;
  if (C <   1628) return       36;
  if (C <   1967) return       60;
  if (C <   2349) return      120;
  if (C <   3083) return      180;
  if (C <   3132) return      240;
  if (C <   3270) return      504;
  if (C <   3838) return      360;
  if (C <   4115) return      420;
  if (C <   4621) return      720;
  if (C <   4987) return      840;
  if (C <   5079) return     1440;
  if (C <   6212) return     1260;
  if (C <   6686) return     1680;
  if (C <   8137) return     2520;
  if (C <   8415) return     3360;
  if (C <  10437) return     5040;
  if (C <  11643) return    13860;
  if (C <  12826) return    10080;
  if (C <  13369) return    16380;
  if (C <  13540) return    21840;
  if (C <  15060) return    18480;
  if (C <  15934) return    27720;
  if (C <  17695) return    32760;
  if (C <  18816) return    36960;
  if (C <  21338) return    55440;
  if (C <  23179) return    65520;
  if (C <  23484) return    98280;
  if (C <  27465) return   110880;
  if (C <  30380) return   131040;
  if (C <  31369) return   166320;
  if (C <  33866) return   196560;
  if (C <  34530) return   262080;
  if (C <  36195) return   277200;
  if (C <  37095) return   360360;
  if (C <  38179) return   480480;
  if (C <  41396) return   332640;
  if (C <  43301) return   554400;
  if (C <  47483) return   720720;
  if (C <  47742) return   665280;
  if (C <  50202) return   831600;
  if (C <  52502) return  1113840;
  if (C <  60245) return  1441440;
  if (C <  63112) return  1663200;
  if (C <  65395) return  2227680;
  if (C <  69895) return  2162160;
  if (C <  71567) return  2827440;
  if (C <  75708) return  3326400;
  if (C <  79377) return  3603600;
  if (C <  82703) return  6126120;
  if (C <  91180) return  4324320;
  if (C <  93978) return  6683040;
  if (C <  98840) return  7207200;
  if (C <  99282) return 11138400;
  if (C < 105811) return  8648640;

  B = racine(N);
  for (t = 8648640+840;; t+=840)
  {
    pari_sp av = avma;
    if (cmpii(e(t), B) > 0) break;
    avma = av;
  }
  avma = av0; return t;
}

extern ulong u_gener(ulong p);

/* tabdl[i] = discrete log of i+1 in (Z/q)^*, q odd prime */
static GEN
computetabdl(ulong q)
{
  GEN v = cgetg(q-1,t_VECSMALL), w = v-1; /* w[i] = dl(i) */
  ulong g,qm3s2,qm1s2,a,i;

  g = u_gener(q);
  qm3s2 = (q-3)>>1;
  qm1s2 = qm3s2+1;
  w[q-1] = qm1s2; a = 1;
  for (i=1; i<=qm3s2; i++)
  {
    a = muluumod(g,a,q);
    w[a]   = i;
    w[q-a] = i+qm1s2;
  }
  return v;
}

static void
compute_fg(ulong q, int half, GEN *tabf, GEN *tabg)
{
  const ulong qm3s2 = (q-3)>>1;
  const ulong l = half? qm3s2: q-2;
  ulong x;
  *tabf = computetabdl(q);
  *tabg = cgetg(l+1,t_VECSMALL);
  for (x=1; x<=l; x++) (*tabg)[x] = (*tabf)[x] + (*tabf)[q-x-1];
}

/* p odd prime */
static GEN
get_jac(Cache *C, ulong q, int pk, GEN tabf, GEN tabg)
{
  ulong x, qm3s2;
  GEN vpk = vecsmall_const(pk, 0);

  qm3s2 = (q-3)>>1;
  for (x=1; x<=qm3s2; x++) vpk[ tabg[x]%pk + 1 ] += 2;
  vpk[ (2*tabf[qm3s2+1])%pk + 1 ]++;
  return u_red(vpk, C->cyc);
}

/* p = 2 */
static GEN
get_jac2(GEN N, ulong q, int k, GEN *j2q, GEN *j3q)
{
  GEN jpq, vpk, tabf, tabg;
  ulong x, pk, i, qm3s2;

  if (k == 1) return NULL;

  compute_fg(q,0, &tabf,&tabg);

  pk = u_pow(2,k);
  vpk = vecsmall_const(pk, 0);

  qm3s2 = (q-3)>>1;
  for (x=1; x<=qm3s2; x++) vpk[ tabg[x]%pk + 1 ] += 2;
  vpk[ (2*tabf[qm3s2+1])%pk + 1 ]++;
  jpq = u_red_cyclo2n_ip(vpk, k);

  if (k == 2) return jpq;

  if (mod8(N) >= 5)
  {
    GEN v8 = cgetg(9,t_VECSMALL);
    for (x=1; x<=8; x++) v8[x] = 0;
    for (x=1; x<=q-2; x++) v8[ ((2*tabf[x]+tabg[x])&7) + 1 ]++;
    *j2q = polinflate(gsqr(u_red_cyclo2n_ip(v8,3)), pk>>3);
    *j2q = red_cyclo2n_ip(*j2q, k);
  }
  else *j2q = NULL;

  for (i=1; i<=pk; i++) vpk[i] = 0;
  for (x=1; x<=q-2; x++) vpk[ (tabf[x]+tabg[x])%pk + 1 ]++;
  *j3q = gmul(jpq, u_red_cyclo2n_ip(vpk,k));
  *j3q = red_cyclo2n_ip(*j3q, k);
  return jpq;
}

static void
calcjac(Cache **pC, GEN globfa, GEN *ptabfaq, GEN *ptabj)
{
  GEN J, tabf, tabg, faq, tabfaq, tabj, P, E;
  int lfaq, p, e, j;
  ulong i, q, l;
  pari_sp av;

  l = lg(globfa); settyp(globfa, t_VECSMALL);
  *ptabfaq = tabfaq= cgetg(l,t_VEC);
  *ptabj   = tabj  = cgetg(l,t_VEC);
  for (i=1; i<l; i++)
  {
    q = itos((GEN)globfa[i]); /* odd prime */
    globfa[i] = q;
    faq = decomp( utoi(q-1) ); tabfaq[i] = (long)faq;
    P = (GEN)faq[1]; settyp(P, t_VECSMALL);
    E = (GEN)faq[2]; settyp(E, t_VECSMALL); lfaq = lg(P);
    P[1] = 2;
    E[1] = itos((GEN)E[1]);

    av = avma;
    compute_fg(q, 1, &tabf, &tabg);

    J = cgetg(lfaq,t_VEC);
    J[1] = lgetg(1,t_STR); /* dummy */
    for (j=2; j<lfaq; j++) /* skip p = P[1] = 2 */
    {
      int pk;
      p = itos((GEN)P[j]); P[j] = p;
      e = itos((GEN)E[j]); E[j] = e; pk = u_pow(p,e);
      J[j] = (long)get_jac(pC[pk], q, pk, tabf, tabg);
    }
    tabj[i] = (long)gerepilecopy(av, J);
  }
}

/* N = 1 mod p^k, return an elt of order p^k in (Z/N)^* */
static GEN
finda(Cache *Cp, GEN N, int pk, int p)
{
  GEN a, pv;
  if (Cp && Cp->avite) {
    a  = Cp->avite;
    pv = Cp->pkvite;
  }
  else
  {
    GEN gp = utoi(p), ph, b, N1;
    ulong u = 2;
    int v = pvaluation(addis(N,-1), gp, &N1);
    ph = gpowgs(gp, v-1); pv = mulis(ph, p); /* N - 1 = p^v q */ 
    if (p > 2)
    {
      for (;;u++)
      {
	a = powmodulo(utoi(u), N1, N);
	b = powmodulo(a, ph, N);
	if (!gcmp1(b)) break;
      }
    }
    else
    {
      while (krosg(u,N) >= 0) u++;
      a = powmodulo(utoi(u), N1, N);
      b = powmodulo(a, ph, N);
    }
    /* checking b^p = 1 mod N done economically in caller */
    b = mppgcd(addis(b,-1), N);
    if (!gcmp1(b)) err(invmoder,"%Z",gmodulcp(b,N)); /* trap this! */
    
    if (Cp) {
      Cp->avite  = a; /* a has order p^v */
      Cp->pkvite = pv;
    }
  }
  return powmodulo(a, divis(pv, pk), N);
}

/* return 0: N not a prime, 1: no problem so far */
static int
filltabs(Cache *C, Cache *Cp, Red *R, int p, int pk, long ltab)
{
  pari_sp av;
  int i, j;
  long e;
  GEN tabt, taba, m;

  C->cyc = cyclo(pk,0);

  if (p > 2)
  {
    int LE = pk - pk/p + 1;
    GEN E = cgetg(LE, t_VECSMALL), eta = cgetg(pk+1,t_VEC);
    for (i=1,j=0; i<pk; i++)
      if (i%p) E[++j] = i;
    C->E = E;

    for (i=1; i<=pk; i++)
    {
      GEN z = FpX_rem(gpowgs(polx[0],i-1), C->cyc, R->N);
      eta[i] = (long)centermod_i(z, R->N, R->N2);
    }
    C->eta = eta;
  }
  else if (pk >= 8)
  {
    int LE = (pk>>2) + 1;
    GEN E = cgetg(LE, t_VECSMALL);
    for (i=1,j=0; i<pk; i++)
      if ((i%8)==1 || (i%8)==3) E[++j] = i;
    C->E = E;
  }

  if (pk > 2 && smodis(R->N,pk) == 1)
  {
    GEN vpa, p1, p2, p3, a2 = NULL, a = finda(Cp, R->N, pk, p);
    int jj, ph = pk - pk/p;

    vpa = cgetg(ph+1,t_COL); vpa[1] = (long)a;
    if (pk > p) a2 = centermodii(sqri(a), R->N, R->N2);
    jj = 1;
    for (i=2; i<pk; i++) /* vpa = { a^i, (i,p) = 1 } */
      if (i%p) { 
        GEN z = mulii((i%p==1) ? a2 : a, (GEN)vpa[jj]);
        vpa[++jj] = (long)centermodii(z , R->N, R->N2);
      }
    if (!gcmp1( centermodii( mulii(a, (GEN)vpa[ph]), R->N, R->N2) )) return 0;
    p1 = cgetg(ph+1,t_MAT);
    p2 = cgetg(ph+1,t_COL); p1[1] = (long)p2;
    for (i=1; i<=ph; i++) p2[i] = un;
    j = 2; p1[j] = (long)vpa; p3 = vpa;
    for (j++; j <= ph; j++)
    {
      p2 = cgetg(ph+1,t_COL); p1[j] = (long)p2;
      for (i=1; i<=ph; i++) 
        p2[i] = (long)centermodii(mulii((GEN)vpa[i],(GEN)p3[i]), R->N, R->N2);
      p3 = p2;
    }
    C->matvite = p1;
    C->matinvvite = FpM_inv(p1, R->N);
  }

  tabt = cgetg(ltab+1, t_VECSMALL);
  taba = cgetg(ltab+1, t_VECSMALL);
  av = avma; m = divis(R->N, pk);
  for (e=1; e<=ltab && signe(m); e++)
  {
    long s = vali(m); m = shifti(m,-s);
    tabt[e] = e==1? s: s + R->k;
    taba[e] = signe(m)? ((modBIL(m) & R->mask)+1)>>1: 0;
    m = shifti(m, -R->k);
  }
  setlg(taba, e); C->aall = taba;
  setlg(tabt, e); C->tall = tabt;
  avma = av; return 1;
}

static Cache *
alloc_cache()
{
  Cache *C = (Cache*)new_chunk(sizeof(Cache) / sizeof(long));
  C->matvite = NULL;
  C->avite   = NULL; 
  C->ctsgt = 0; return C;
}

static Cache **
calcglobs(Red *R, ulong t, long *pltab, GEN *pP)
{
  GEN fat, P, E;
  int lv, lfa, pk, p, e, i, k;
  long ltab, b;
  Cache **pC;

  b = bit_accuracy(lgefint(R->N)) - 1;
  while ( !bittest(R->N,b) ) b--;
  b++;

  k = 3; while (((k+1)*(k+2) << (k-1)) < b) k++;
  *pltab = ltab = (b/k) + 2;
  R->k  = k;
  R->lv = 1 << (k-1);
  R->mask = (1UL << k) - 1;

  fat = decomp(utoi(t));
  P = (GEN)fat[1]; settyp(P, t_VECSMALL);
  E = (GEN)fat[2]; settyp(E, t_VECSMALL); lfa = lg(P);
  lv = 1;
  for (i=1; i<lfa; i++)
  {
    p = itos((GEN)P[i]); P[i] = p;
    e = itos((GEN)E[i]); E[i] = e;
    pk = u_pow(p, e);
    if (pk > lv) lv = pk;
  }
  pC = (Cache**)cgetg(lv + 1, t_VEC);
  pC[1] = alloc_cache(); /* to be used as temp in step5() */
  for (i = 2; i <= lv; i++) pC[i] = NULL;
  for (i=1; i<lfa; i++)
  {
    pk = p = P[i];
    e = E[i];
    for (k=1; k<=e; k++, pk*=p)
    {
      pC[pk] = alloc_cache();
      if (!filltabs(pC[pk], pC[p], R, p,pk, ltab)) return NULL;
    }
  }
  if (DEBUGLEVEL) fprintferr("\n");
  *pP = P;
  return pC;
}

/* sig_a^{-1}(z) for z in Q(ze) and sig_a: ze -> ze^a */
static GEN
aut(int pk, GEN z, int a, GEN C)
{
  GEN v = cgetg(pk+1,t_VEC);
  int i;
  for (i=1; i<=pk; i++)
    v[i] = (long)polcoeff0(z, (a*(i-1))%pk, 0);
  return gmodulcp(gtopolyrev(v,0), C);
}

#if 0
/* z^v for v in Z[G], represented by couples [sig_x^{-1},y] */
static GEN
autvec(int pk, GEN z, GEN v, GEN C)
{
  int i, lv = lg(v);
  GEN s = gun;
  for (i=1; i<lv; i++)
  {
    long y = mael(v,i,2);
    if (y) s = gmul(s, gpowgs(aut(pk,z,mael(v,i,1), C), y));
  }
  return lift_intern(s);
}
#endif
/* z^v for v in Z[G], represented by couples [sig_x^{-1},x] */
static GEN
autvec_TH(int pk, GEN z, GEN v, GEN C)
{
  int i, lv = lg(v);
  GEN s = gun;
  for (i=1; i<lv; i++)
  {
    long y = v[i];
    if (y) s = gmul(s, gpowgs(aut(pk,z, y, C), y));
  }
  return lift_intern(s);
}

static GEN
autvec_AL(int pk, GEN z, GEN v, Red *R)
{
  const int r = smodis(R->N, pk);
  GEN s = gun;
  int i, lv = lg(v);
  for (i=1; i<lv; i++)
  {
    long y = (r*v[i]) / pk;
    if (y) s = gmul(s, gpowgs(aut(pk,z, v[i], R->C), y));
  }
  return lift_intern(s);
}

/* 0 <= i < pk, such that x^i = z mod cyclo(pk),  -1 if no such i exist */
static int
look_eta(GEN eta, int pk, GEN z)
{
  long i;
  for (i=1; i<=pk; i++)
    if (gegal(z, (GEN)eta[i])) return i-1;
  return -1;
}
/* same pk = 2^k */
static int
look_eta2(int k, GEN z)
{
  long d, s;
  if (typ(z) != t_POL) d = 0; /* t_INT */
  else
  { 
    if (!ismonome(z)) return -1;
    d = degpol(z);
    z = (GEN)z[d+2]; /* leading term */
  }
  s = signe(z);
  if (!s || !is_pm1(z)) return -1;
  return (s > 0)? d: d + (1<<(k-1));
}

static int
step4a(Cache *C, Red *R, ulong q, int p, int k, GEN jpq)
{
  const int pk = u_pow(p,k);
  int ind;
  GEN s1, s2, s3;
  
  if (!jpq)
  {
    GEN tabf, tabg;
    compute_fg(q,1, &tabf,&tabg);
    jpq = get_jac(C, q, pk, tabf, tabg);
  }
  s1 = autvec_TH(pk, jpq, C->E, C->cyc);
  s2 = powpolmod(C,R, p,k, s1);
  s3 = autvec_AL(pk, jpq, C->E, R);
  s3 = _red(gmul(s3,s2), R);

  ind = look_eta(C->eta, pk, s3);
  if (ind < 0) return -1;
  return (ind%p) != 0;
}

/* x == -1 mod N ? */
static int
is_m1(GEN x, GEN N)
{
  return egalii(addis(x,1), N);
}

/* p=2, k>=3 */
static int
step4b(Cache *C, Red *R, ulong q, int k)
{
  const int pk = u_pow(2,k);
  int ind;
  GEN s1, s2, s3, j2q, j3q;

  (void)get_jac2(R->N,q,k, &j2q,&j3q);

  s1 = autvec_TH(pk, j3q, C->E, C->cyc);
  s2 = powpolmod(C,R, 2,k, s1);
  s3 = autvec_AL(pk, j3q, C->E, R);
  s3 = _red(gmul(s3,s2), R);
  if (j2q) s3 = _red(gmul(j2q, s3), R);

  ind = look_eta2(k, s3);
  if (ind < 0) return -1;
  if ((ind&1)==0) return 0;
  if (DEBUGLEVEL>2) C->ctsgt++;
  s3 = powmodulo(utoi(q), R->N2, R->N);
  return is_m1(s3, R->N);
}

/* p=2, k=2 */
static int
step4c(Cache *C, Red *R, ulong q)
{
  int ind;
  GEN s0,s1,s3, jpq = get_jac2(R->N,q,2, NULL,NULL);

  s0 = sqrmod4(jpq, R);
  s1 = gmulsg(q,s0);
  s3 = powpolmod(C,R, 2,2, s1);
  if (mod4(R->N) == 3) s3 = _red(gmul(s0,s3), R);

  ind = look_eta2(2, s3);
  if (ind < 0) return -1;
  if ((ind&1)==0) return 0;
  if (DEBUGLEVEL>2) C->ctsgt++;
  s3 = powmodulo(utoi(q), R->N2, R->N);
  return is_m1(s3, R->N);
}

/* p=2, k=1 */
static int
step4d(Cache *C, Red *R, ulong q)
{
  GEN s1 = powmodulo(negi(utoi(q)), R->N2, R->N);
  if (DEBUGLEVEL>2) C->ctsgt++;
  if (gcmp1(s1)) return 0;
  if (is_m1(s1, R->N)) return (mod4(R->N) == 1);
  return -1;
}

/* return 1 [OK so far] or <= 0 [not a prime] */
static long
step5(Cache **pC, Red *R, int p, GEN et, ulong ltab)
{
  ulong ct = 1, q;
  int pk, k, fl = -1;
  byteptr d = diffptr+2;
  Cache *C, *Cp;

  for (q = 3; *d; )
  {
    if (q%p != 1 || smodis(et,q) == 0) goto repeat;

    if (smodis(R->N,q) == 0) return -1;
    k = u_val(q-1, p);
    pk = u_pow(p,k);
    if (pk < lg(pC) && pC[pk]) { C = pC[pk]; Cp = pC[p]; }
    else {
      C = pC[1]; C->matvite = NULL; /* re-init */
      Cp = NULL;
    }
    
    if (!filltabs(C, Cp, R, p, pk, ltab)) return 0; 
    R->C = C->cyc;
    if (p >= 3)      fl = step4a(C,R, q,p,k, NULL);
    else if (k >= 3) fl = step4b(C,R, q,k);
    else if (k == 2) fl = step4c(C,R, q);
    else             fl = step4d(C,R, q);
    if (fl == -1) return (int)(-q);
    if (fl == 1) return ct;
    ct++;
   repeat:
    NEXT_PRIME_VIADIFF(q,d);
  }
  err(bugparier,"aprcl test fails! this is highly improbable");
  return 0;
}

static GEN
step6(GEN N, ulong t, GEN et)
{
  GEN r, p1, N1 = resii(N, et);
  ulong i;
  pari_sp av = avma;

  r = gun;
  for (i=1; i<t; i++)
  {
    r = resii(mulii(r,N1), et);
    if (gcmp1(r)) break;
    if (!signe(resii(N,r)) && !egalii(r,N))
    {
      p1 = cgetg(3,t_VEC);
      p1[1] = (long)r;
      p1[2] = zero; return p1;
    }
    if ((i & 0x1f) == 0) r = gerepileuptoint(av, r);
  }
  return gun;
}

static GEN
_res(long a, long b)
{
  GEN z;
  if (b) { z=cgetg(3, t_VEC); z[1]=lstoi(a); z[2]=lstoi(b); }
  else   { z=cgetg(2, t_VEC); z[1]=lstoi(a); }
  return z;
}

GEN
aprcl(GEN N)
{
  GEN et, fat, flaglp, tabfaq, tabj, res, globfa;
  long i, j, l, ltab, lfat, lfaq, fl, ctglob = 0;
  ulong p, q, t;
  pari_sp av, av2;
  Red R;
  Cache **pC;

  if (cmpis(N,12) <= 0)
    switch(itos(N))
    {
      case 2: case 3: case 5: case 7: case 11: return gun;
      default: return _res(0,0);
    }
  t = compt(N);
  if (DEBUGLEVEL) fprintferr("Choosing t = %ld\n",t);
  et = e(t);
  if (cmpii(sqri(et),N) < 0) err(bugparier,"aprcl: e(t) too small");
  if (!gcmp1(mppgcd(N,mulsi(t,et)))) return _res(1,0);

  R.N = N;
  R.N2= shifti(N, -1);
  pC = calcglobs(&R, t, &ltab, &fat); 
  if (!pC) return _res(1,0);
  lfat = lg(fat); p = fat[lfat-1]; /* largest p | t */
  flaglp = cgetg(p+1, t_VECSMALL);
  flaglp[2] = 0;
  for (i=2; i<lfat; i++)
  {
    p = fat[i]; q = p*p;
    flaglp[p] = (powuumod(smodis(N,q),p-1,q) != 1);
  }
  globfa = (GEN)decomp(shifti(et, -vali(et)))[1];
  calcjac(pC, globfa, &tabfaq, &tabj);
  
  av = avma; l = lg(globfa);
  if (DEBUGLEVEL>2)
  {
    fprintferr("Jacobi sums and tables computed\n");
    fprintferr("Step4: q-values (# = %ld, largest = %ld): ", l-1, globfa[l-1]);
  }
  for (i=1; i<l; i++)
  {
    GEN P, E, faq;
    avma = av;
    q = globfa[i]; if (DEBUGLEVEL>2) fprintferr("%ld ",q);
    faq = (GEN)tabfaq[i];
    P = (GEN)faq[1];
    E = (GEN)faq[2]; lfaq = lg(P);
    av2 = avma;
    for (j=1; j<lfaq; j++, avma = av2)
    {
      Cache *C;
      int pk, k;
      p = P[j];
      k = E[j]; pk = u_pow(p, k); C = pC[pk];
      R.C = C->cyc;
      if (p >= 3)      fl = step4a(C,&R, q,p,k, gmael(tabj,i,j));
      else if (k >= 3) fl = step4b(C,&R, q,k);
      else if (k == 2) fl = step4c(C,&R, q);
      else             fl = step4d(C,&R, q);
      if (fl == -1) return _res(q,p);
      if (fl == 1) flaglp[p] = 1;
    }
  }
  if (DEBUGLEVEL>2) fprintferr("\nStep5: testing conditions lp\n");
  for (i=1; i<lfat; i++)
  {
    p = fat[i]; if (flaglp[p]) continue;

    fl = step5(pC, &R, p, et, ltab);
    if (!fl) return _res(1,0);
    if (fl < 0) return _res(fl,p); 
    if (fl > ctglob) ctglob = fl; /* DEBUG */
  }
  if (DEBUGLEVEL>2) fprintferr("Step6: testing potential divisors\n");
  res = step6(N, t, et);
  if (DEBUGLEVEL>2)
  {
    ulong sc = pC[1]->ctsgt;
    fprintferr("Individual Fermat powerings:\n");
    for (i=2; i<lg(pC); i++) 
      if (pC[i]) {
        fprintferr("  %-3ld: %3ld\n", i, pC[i]->ctsgt);
        sc += pC[i]->ctsgt;
      }
    fprintferr("Number of Fermat powerings = %lu\n",sc);
    fprintferr("Maximal number of nondeterministic steps = %lu\n",ctglob);
  }
  return res;
}

long
isprimeAPRCL(GEN N)
{
  pari_sp av = avma;
  GEN res = aprcl(N);
  avma = av; return (typ(res) == t_INT);
}
