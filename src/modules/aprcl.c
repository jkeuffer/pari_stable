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

static ulong ctglob, sgtaut, sgt6, sgtjac; /* DEBUG */
static GEN sgt, ctsgt;

static ulong kglob;
static int ishack;
static GEN *tabaall, *tabtall, *tabcyc, *tabmatvite, *tabmatinvvite;
static GEN tabE, tabeta, tabavite, tabpkvite;
#define pkfalse (ishack ? 1 : pk)
#define dotime (DEBUGLEVEL>=3)

typedef struct red_t {
  long n;
  GEN C; /* polcyclo(n) */
  GEN N; /* prime we are certifying */
  GEN (*red)(GEN x, struct red_t *);
} red_t;

/* powering t_POLMOD mod N, flexible window */

static GEN
makepoldeg1(GEN c, GEN d)
{
  GEN res;
  if (signe(c)) {
    res = cgetg(4,t_POL); res[1] = evalsigne(1)|evallgef(4);
    res[2] = (long)d; res[3] = (long)c;
  } else if (signe(d)) {
    res = cgetg(3,t_POL); res[1] = evalsigne(1)|evallgef(3);
    res[2] = (long)d;
  } else {
    res = cgetg(2,t_POL); res[1] = evalsigne(0)|evallgef(2);
  }
  return res;
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
  z = cgetg(i, t_POL); z[1] = evalsigne(1)|evallgef(i);
  for (i--; i>=2; i--) z[i] = lstoi(x[i-1]);
  return z;
}
/* x t_POL, n > 0. Return x mod polcyclo(2^n) = (x^(2^(n-1)) + 1). IN PLACE */
static GEN
red_cyclo2n_ip(GEN x, int n)
{
  long i, pow2 = 1<<(n-1);

  for (i = lgef(x)-1; i>pow2+1; i--)
    if (signe(x[i])) x[i-pow2] = lsubii((GEN)x[i-pow2], (GEN)x[i]);
  for (; i>1; i--)
    if (signe(x[i])) break;
  i += 1; setlgef(x,i);
  return x;
}
/* x t_POL, n > 0. Return x mod polcyclo(2^n) = (x^(2^(n-1)) + 1) */
static GEN
red_cyclo2n(GEN x, int n)
{
  long i, pow2 = 1<<(n-1);

  x = dummycopy(x);
  for (i = lgef(x)-1; i>pow2+1; i--)
    if (signe(x[i])) x[i-pow2] = lsubii((GEN)x[i-pow2], (GEN)x[i]);
  for (; i>1; i--)
    if (signe(x[i])) break;
  i += 1; setlgef(x,i);
  return x;
}

/* x a non-zero VECSMALL */
static GEN
smallpolrev(GEN x)
{
  long i,j, lx = lg(x);
  GEN y;

  while (lx-- && x[lx]==0) /* empty */;
  i = lx+2; y = cgetg(i,t_POL);
  y[1] = evallgef(i) | evalsigne(1);
  for (j=2; j<i; j++) y[j] = lstoi(x[j-1]);
  return y;
}

/* x polynomial in t_VECSMALL form, T t_POL return x mod T */
static GEN
u_red(GEN x, GEN T)
{
  return gres(smallpolrev(x), T);
}

/* special case R->C = polcyclo(2^n) */
static GEN
_red_cyclo2n(GEN x, red_t *R) {
  return FpX_red(red_cyclo2n(x, R->n), R->N);
}
/* special case R->C = polcyclo(p) */
static GEN
_red_cyclop(GEN x, red_t *R) {
  return FpX_red(red_cyclop(x, R->n), R->N);
}
static GEN
_red(GEN x, red_t *R) {
  return FpX_red(gres(x, R->C), R->N);
}

static GEN
_redsimple(GEN x, red_t *R) {
  return modii(x, R->N);
}

static GEN
sqrmod(GEN x, red_t *R) {
  return R->red(gsqr(x), R);
}

static GEN
sqrconst(GEN pol, red_t *R)
{
  GEN p1 = cgetg(3,t_POL);
  p1[2] = (long)modii(sqri((GEN)pol[2]), R->N);
  p1[1] = pol[1]; return p1;
}

/* pol^2 mod (x^2+x+1, N) */
static GEN
sqrmod3(GEN pol, red_t *R)
{
  GEN a,b,bma,A,B;
  long lv=lgef(pol);

  if (lv==2) return pol;
  if (lv==3) return sqrconst(pol, R);
  a = (GEN)pol[3];
  b = (GEN)pol[2]; bma = subii(b,a);
  A = modii(mulii(a,addii(b,bma)), R->N);
  B = modii(mulii(bma,addii(a,b)), R->N);
  return makepoldeg1(A,B);
}

/* pol^2 mod (x^2+1,N) */
static GEN
sqrmod4(GEN pol, red_t *R)
{
  GEN a,b,A,B;
  long lv=lgef(pol);

  if (lv==2) return pol;
  if (lv==3) return sqrconst(pol, R);
  a = (GEN)pol[3];
  b = (GEN)pol[2];
  A = modii(mulii(a, shifti(b,1)), R->N);
  B = modii(mulii(subii(b,a),addii(b,a)), R->N);
  return makepoldeg1(A,B);
}

/* pol^2 mod (polcyclo(5),N) */
static GEN
sqrmod5(GEN pol, red_t *R)
{
  GEN c2,b,c,d,A,B,C,D;
  long lv=lgef(pol);

  if (lv==2) return pol;
  if (lv==3) return sqrconst(pol, R);
  c = (GEN)pol[3]; c2 = shifti(c,1);
  d = (GEN)pol[2];
  if (lv==4)
  {
    A = sqri(d);
    B = mulii(c2, d);
    C = sqri(c);
    A = modii(A, R->N);
    B = modii(B, R->N);
    C = modii(C, R->N); return coefs_to_pol(3,A,B,C);
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
  A = modii(A, R->N);
  B = modii(B, R->N);
  C = modii(C, R->N);
  D = modii(D, R->N); return coefs_to_pol(4,A,B,C,D);
}

static GEN
_mul(GEN x, GEN y, red_t *R) {
  return R->red(gmul(x,y), R);
}

static GEN
_powpolmod(int pk, GEN jac, red_t *R, GEN (*_sqr)(GEN, red_t *))
{
  const GEN taba = tabaall[pkfalse];
  const GEN tabt = tabtall[pkfalse];
  const int efin = lg(taba)-1;
  GEN pol2, res = jac, *vz;
  int tf,f,i, lv = 1 << (kglob-1);
  pari_sp av;

  vz = (GEN*)cgetg(lv+1,t_VEC);
  pol2 = _sqr(res, R);
  vz[1] = res;
  for (i=2; i<=lv; i++) vz[i] = _mul(vz[i-1],pol2, R);
  av = avma;
  for (f=efin; f>=1; f--)
  {
    res = f==efin ? vz[taba[f]]
                  : _mul(vz[taba[f]],res, R);
    tf = tabt[f];
    for (i=1; i<=tf; i++) res = _sqr(res, R);
    if ((f&7) == 0) res = gerepilecopy(av, res);
  }
  return res;
}

static GEN
_powpolmodsimple(red_t *R, int pk, GEN jac)
{
  GEN w, ma = tabmatvite[pkfalse];
  int j, ph = lg(ma);

  R->red = &_redsimple;
  w = mulmat_pol(ma, jac);
  for (j=1; j<ph; j++)
    w[j] = (long)_powpolmod(pk, modii((GEN)w[j], R->N), R, &sqrmod);
  w = FpV_red( gmul(tabmatinvvite[pkfalse], w), R->N );
  return vec_to_pol(w, 0);
}

GEN
powpolmod(red_t *R, int k, int pk, GEN jac)
{
  GEN (*_sqr)(GEN, red_t *);

  if ( tabmatvite[pkfalse] ) return _powpolmodsimple(R, pk, jac);
  if ((pk & 1) == 0) /* p = 2 */
  {
    if (pk == 4) {
      R->red = &_red; _sqr = &sqrmod4;
    } else {
      R->n = k;
      R->red = &_red_cyclo2n; _sqr = &sqrmod;
    }
  } else if (pk == 3) {
    R->red = &_red; _sqr = &sqrmod3;
  } else if (pk == 5) {
    R->red = &_red; _sqr = &sqrmod5;
  } else if (k == 1) {
    R->n = pk;
    R->red = &_red_cyclop; _sqr = &sqrmod;
  } else {
    R->red = &_red; _sqr = &sqrmod;
  }
  return _powpolmod(pk, jac, R, _sqr);
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
  ulong Bint,t;
  GEN B;

  B = mulsr(100, divrr(glog(N,DEFAULTPREC), dbltor(log(10.))));
  Bint = itos(gceil(B));
  avma = av0;
  /* Bint < [200*log_10 e(t)] ==> return t. For e(t) < 10^529, N < 10^1058 */
  if (Bint <    540) return        6;
  if (Bint <    963) return       12;
  if (Bint <   1023) return       24;
  if (Bint <   1330) return       48;
  if (Bint <   1628) return       36;
  if (Bint <   1967) return       60;
  if (Bint <   2349) return      120;
  if (Bint <   3083) return      180;
  if (Bint <   3132) return      240;
  if (Bint <   3270) return      504;
  if (Bint <   3838) return      360;
  if (Bint <   4115) return      420;
  if (Bint <   4621) return      720;
  if (Bint <   4987) return      840;
  if (Bint <   5079) return     1440;
  if (Bint <   6212) return     1260;
  if (Bint <   6686) return     1680;
  if (Bint <   8137) return     2520;
  if (Bint <   8415) return     3360;
  if (Bint <  10437) return     5040;
  if (Bint <  11643) return    13860;
  if (Bint <  12826) return    10080;
  if (Bint <  11643) return    13860;
  if (Bint <  12826) return    10080;
  if (Bint <  13369) return    16380;
  if (Bint <  13540) return    21840;
  if (Bint <  15060) return    18480;
  if (Bint <  15934) return    27720;
  if (Bint <  17695) return    32760;
  if (Bint <  18816) return    36960;
  if (Bint <  21338) return    55440;
  if (Bint <  23179) return    65520;
  if (Bint <  23484) return    98280;
  if (Bint <  27465) return   110880;
  if (Bint <  30380) return   131040;
  if (Bint <  31369) return   166320;
  if (Bint <  33866) return   196560;
  if (Bint <  34530) return   262080;
  if (Bint <  36195) return   277200;
  if (Bint <  37095) return   360360;
  if (Bint <  38179) return   480480;
  if (Bint <  41396) return   332640;
  if (Bint <  43301) return   554400;
  if (Bint <  47483) return   720720;
  if (Bint <  47742) return   665280;
  if (Bint <  50202) return   831600;
  if (Bint <  52502) return  1113840;
  if (Bint <  60245) return  1441440;
  if (Bint <  63112) return  1663200;
  if (Bint <  65395) return  2227680;
  if (Bint <  69895) return  2162160;
  if (Bint <  71567) return  2827440;
  if (Bint <  75708) return  3326400;
  if (Bint <  79377) return  3603600;
  if (Bint <  82703) return  6126120;
  if (Bint <  91180) return  4324320;
  if (Bint <  93978) return  6683040;
  if (Bint <  98840) return  7207200;
  if (Bint <  99282) return 11138400;
  if (Bint < 105811) return  8648640;

  B = racine(N);
  for (t = 8648640+840;; t+=840)
  {
    pari_sp av = avma;
    if (cmpii(e(t),B) > 0) break;
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
get_jac(ulong q, ulong p, int k, GEN tabf, GEN tabg, GEN C)
{
  ulong x, qm3s2, pk = u_pow(p,k);
  GEN vpk = vecsmall_const(pk, 0);

  qm3s2 = (q-3)>>1;
  for (x=1; x<=qm3s2; x++) vpk[ tabg[x]%pk + 1 ] += 2;
  vpk[ (2*tabf[qm3s2+1])%pk + 1 ]++;
  return u_red(vpk, C);
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

  for (i=1; i<=pk; i++) vpk[i] = 0;
  for (x=1; x<=q-2; x++) vpk[ (tabf[x]+tabg[x])%pk + 1 ]++;
  *j3q = gmul(jpq, u_red_cyclo2n_ip(vpk,k));
  *j3q = red_cyclo2n_ip(*j3q, k);
  return jpq;
}

static void
calcjac(GEN globfa, GEN *ptabfaq, GEN *ptabj)
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
      p = itos((GEN)P[j]); P[j] = p;
      e = itos((GEN)E[j]); E[j] = e;
      J[j] = (long)get_jac(q, p, e, tabf, tabg, (GEN)tabcyc[u_pow(p,e)]);
    }
    tabj[i] = (long)gerepilecopy(av, J);
  }
}

static void
inittabs(int lv)
{
  int i;
  tabaall = (GEN*)cgetg(lv,t_VEC);
  tabtall = (GEN*)cgetg(lv,t_VEC);
  tabcyc  = (GEN*)cgetg(lv,t_VEC);
  for (i=1; i<lv; i++) tabcyc[i] = gzero;
  tabE = cgetg(lv,t_VEC);
  tabeta=cgetg(lv,t_VEC);
  tabmatvite = (GEN*)cgetg(lv,t_VEC);
  tabmatinvvite = (GEN*)cgetg(lv,t_VEC);
  tabavite  = cgetg(lv,t_VEC);
  tabpkvite = cgetg(lv,t_VEC);
  sgt  = cgetg(lv,t_VECSMALL);
  ctsgt= cgetg(lv,t_VECSMALL);
  for (i=1; i<lv; i++) { tabE[i] = tabeta[i] = zero; }
  for (i=1; i<lv; i++)
  {
    tabmatvite[i] = tabmatinvvite[i] = 0;
    tabavite[i] = tabpkvite[i] = sgt[i] = ctsgt[i] = 0;
  }
}

/* N = 1 mod p^k, return an elt of order p^k in (Z/N)^* */
static GEN
finda(GEN N, int pk, int p, int step5)
{
  GEN a;
  if (DEBUGLEVEL && !step5) fprintferr("%ld ",pk);
  if (!step5 && tabavite[p]) a = (GEN)tabavite[p];
  else
  {
    GEN gp = utoi(p), ph, b, N1;
    ulong u = 2;
    int v = pvaluation(addis(N,-1), gp, &N1);
    ph = gpowgs(gp, v-1); tabpkvite[p] = lmulis(ph, p); /* N - 1 = p^v q */ 
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
    
    if (!step5) tabavite[p] = (long)a; /* a has order p^v */
  }
  return powmodulo(a, divis((GEN)tabpkvite[p], pk), N);
}

/* return 0: N not a prime, 1: no problem so far */
static int
filltabs(GEN N, int p, int k, ulong ltab, int step5)
{
  const ulong mask = (1<<kglob)-1;
  pari_sp av;
  int pk, pk2, i, j;
  long e;
  GEN tabt, taba, m, p1;

  pk = u_pow(p,k);
  ishack = step5 && (pk >= lg((GEN)tabcyc) || !signe(tabcyc[pk]));
  pk2 = pkfalse;
  tabcyc[pk2] = cyclo(pk,0);

  p1 = cgetg(pk+1,t_VEC);
  for (i=1; i<=pk; i++)
    p1[i] = (long)FpX_res(gpowgs(polx[0],i-1), tabcyc[pk2], N);
  tabeta[pk2] = (long)p1;

  if (p > 2)
  {
    int LE = pk - pk/p + 1;
    GEN E = cgetg(LE, t_VECSMALL);
    for (i=1,j=0; i<pk; i++)
      if (i%p) E[++j] = i;
    tabE[pk2] = (long)E;
  }
  else if (k >= 3)
  {
    int LE = (pk>>2) + 1;
    GEN E = cgetg(LE, t_VECSMALL);
    for (i=1,j=0; i<pk; i++)
      if ((i%8)==1 || (i%8)==3) E[++j] = i;
    tabE[pk2] = (long)E;
  }

  if (pk > 2 && smodis(N,pk) == 1)
  {
    GEN vpa, p1, p2, p3, a2 = NULL, a = finda(N, pk, p, step5);
    int jj, ph = pk - pk/p;

    vpa = cgetg(ph+1,t_COL); vpa[1] = (long)a;
    if (k > 1) a2 = modii(sqri(a), N);
    jj = 1;
    for (i=2; i<pk; i++) /* vpa = { a^i, (i,p) = 1 } */
      if (i%p) { 
        jj++;
        vpa[jj] = lmodii( mulii((i%p==1) ? a2 : a, (GEN)vpa[jj-1]), N );
      }
    if (!gcmp1( modii( mulii(a, (GEN)vpa[ph]), N) )) return 0;
    p1 = cgetg(ph+1,t_MAT);
    p2 = cgetg(ph+1,t_COL); p1[1] = (long)p2;
    for (i=1; i<=ph; i++) p2[i] = un;
    j = 2; p1[j] = (long)vpa; p3 = vpa;
    for (j++; j <= ph; j++)
    {
      p2 = cgetg(ph+1,t_COL); p1[j] = (long)p2;
      for (i=1; i<=ph; i++) p2[i] = lmodii(mulii((GEN)vpa[i],(GEN)p3[i]), N);
      p3 = p2;
    }
    tabmatvite[pk2] = p1;
    tabmatinvvite[pk2] = FpM_inv(p1, N);
  }

  tabt = cgetg(ltab+1, t_VECSMALL);
  taba = cgetg(ltab+1, t_VECSMALL);
  av = avma; m = divis(N,pk);
  for (e=1; e<=ltab && signe(m); e++)
  {
    long s = vali(m); m = shifti(m,-s);
    tabt[e] = e==1? s: s+kglob;
    taba[e] = signe(m)? ((modBIL(m) & mask)+1)>>1: 0;
    m = shifti(m, -kglob);
  }
  avma = av;
  if (e > ltab) err(bugparier,"filltabs");
  setlg(taba, e); tabaall[pk2] = taba;
  setlg(tabt, e); tabtall[pk2] = tabt;
  return 1;
}


static GEN
calcglobs(GEN N, ulong t, ulong *pltab)
{
  GEN fat, P, E;
  int lfa, pk, p, e, i, k;
  ulong ltab, ltaball, NBITSN;

  NBITSN = bit_accuracy(lgefint(N)) - 1;
  while (bittest(N,NBITSN)==0) NBITSN--;
  NBITSN++;
  kglob=3; while (((kglob+1)*(kglob+2) << (kglob-1)) < NBITSN) kglob++;
  *pltab = ltab = (NBITSN/kglob) + 2;

  fat = decomp(utoi(t));
  P = (GEN)fat[1]; settyp(P, t_VECSMALL);
  E = (GEN)fat[2]; settyp(E, t_VECSMALL); lfa = lg(P);
  ltaball = 1;
  for (i=1; i<lfa; i++)
  {
    p = itos((GEN)P[i]); P[i] = p;
    e = itos((GEN)E[i]); E[i] = e;
    pk = u_pow(p, e);
    if ((ulong)pk > ltaball) ltaball = (ulong)pk;
  }
  inittabs(ltaball+1);
  if (DEBUGLEVEL) fprintferr("Fast pk-values: ");
  for (i=1; i<lfa; i++)
  {
    p = P[i];
    e = E[i];
    for (k=1; k<=e; k++)
      if (!filltabs(N,p,k,ltab, 0)) return NULL;
  }
  if (DEBUGLEVEL) fprintferr("\n");
  return P;
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

/* z^v for v in Z[G], represented by couples [sig_x^{-1},y] */
static GEN
autvec(int pk, GEN z, GEN v, GEN C)
{
  int i,lv = lg(v);
  GEN s = gun;
  for (i=1; i<lv; i++)
  {
    long y = mael(v,i,2);
    if (y) s = gmul(s, gpowgs(aut(pk,z,mael(v,i,1), C), y));
  }
  return s;
}
/* z^v for v in Z[G], represented by couples [sig_x^{-1},x] */
static GEN
autvec_TH(int pk, GEN z, GEN v, GEN C)
{
  int i,lv = lg(v);
  GEN s = gun;
  for (i=1; i<lv; i++)
  {
    long y = v[i];
    if (y) s = gmul(s, gpowgs(aut(pk,z,y, C), y));
  }
  return s;
}

static GEN
get_AL(GEN N, int pk)
{
  const int r = smodis(N, pk);
  GEN AL, E = (GEN)tabE[pkfalse];
  int i, LE = lg(E);

  AL = cgetg(LE,t_VEC);
  for (i=1; i<LE; i++)
  {
    GEN p1 = cgetg(3,t_VECSMALL); AL[i] = (long)p1;
    p1[1] = E[i];
    p1[2] = (r*E[i]) / pk;
  }
  return AL;
}

static int
look_eta(int pk, GEN s)
{
  GEN etats = (GEN)tabeta[pkfalse];
  long i;
  for (i=1; i<=pk; i++)
    if (gegal(s, (GEN)etats[i])) return i-1;
  return pk;
}

static int
step4a(GEN N, ulong q, int p, int k, GEN jpq)
{
  const int pk = u_pow(p,k);
  int ind, pk2;
  GEN s1, s2, s3;
  red_t R;
  
  pk2 = pkfalse;
  R.N = N;
  R.C = tabcyc[pk2];

  if (dotime) (void)timer2();
  if (!jpq)
  {
    GEN tabf, tabg;
    compute_fg(q,1, &tabf,&tabg);
    jpq = get_jac(q, p, k, tabf, tabg, R.C);
    if (dotime) sgtjac+=timer2();
  }

  s1 = autvec_TH(pk,jpq,(GEN)tabE[pk2], R.C);
  if (dotime) sgtaut+=timer2();
  s2 = powpolmod(&R, k,pk, lift_intern(s1));
  if (dotime) {sgt[pk2]+=timer2();ctsgt[pk2]++;};
  s3 = autvec(pk, jpq, get_AL(N, pk), R.C);
  if (dotime) sgtaut+=timer2();
  s3 = _red(gmul(lift(s3),s2), &R);
  if (dotime) sgt[pk2]+=timer2();

  ind = look_eta(pk, s3);
  if (ind == pk) return -1;
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
step4b(GEN N, ulong q, int k)
{
  const int pk = u_pow(2,k);
  int ind, pk2;
  GEN s1, s2, s3, j2q, j3q;
  red_t R;

  pk2 = pkfalse;
  R.N = N;
  R.C = tabcyc[pk2];

  if (dotime) (void)timer2();
  (void)get_jac2(N,q,k, &j2q,&j3q);
  if (dotime) sgtjac+=timer2();

  s1 = autvec_TH(pk,j3q,(GEN)tabE[pk2], R.C);
  if (dotime) sgtaut+=timer2();
  s2 = powpolmod(&R, k,pk, lift_intern(s1));
  if (dotime) {sgt[pk2]+=timer2();ctsgt[pk2]++;}
  s3 = autvec(pk, j3q, get_AL(N, pk), R.C);
  if (dotime) sgtaut+=timer2();
  s3 = _red(gmul(lift(s3),s2), &R);
  if (mod8(N) >= 5) s3 = _red(gmul(j2q, s3), &R);
  if (dotime) sgt[pk2]+=timer2();

  ind = look_eta(pk, s3);
  if (ind == pk) return -1;
  if ((ind&1)==0) return 0;
  else
  {
    s3 = powmodulo(utoi(q), shifti(N,-1), N);
    if (dotime) {sgt[pk2]+=timer2();ctsgt[pk2]++;}
    return is_m1(s3, N);
  }
}

/* p=2, k=2 */
static int
step4c(GEN N, ulong q)
{
  const int pk = 4;
  int ind,pk2;
  GEN s0,s1,s3, jpq = get_jac2(N,q,2, NULL,NULL);
  red_t R;

  pk2 = pkfalse;
  R.N = N;
  R.C = tabcyc[pk2];

  if (dotime) (void)timer2();
  s0 = sqrmod4(jpq, &R);
  s1 = gmulsg(q,s0);
  s3 = powpolmod(&R, 2,pk, s1);
  if (mod4(N) == 3) s3 = _red(gmul(s0,s3), &R);
  if (dotime) {sgt[pk2]+=timer2();ctsgt[pk2]++;}

  ind = look_eta(pk, s3);
  if (ind == pk) return -1;
  if ((ind&1)==0) return 0;
  else
  {
    s3 = powmodulo(utoi(q), shifti(N,-1), N);
    if (dotime) sgt[pk2]+=timer2();
    return is_m1(s3,N);
  }
}

/* p=2, k=1 */
static int
step4d(GEN N, ulong q)
{
  GEN s1;

  if (dotime) (void)timer2();
  s1 = powmodulo(negi(utoi(q)), shifti(N,-1), N);
  if (dotime) {sgt[2]+=timer2();ctsgt[2]++;}
  if (gcmp1(s1)) return 0;
  if (is_m1(s1,N)) return (mod4(N) == 1);
  return -1;
}

/* return 1 [OK so far],0 [APRCL fails] or < 0 [not a prime] */
static int
step5(GEN N, int p, GEN et, ulong ltab)
{
  ulong ct = 0, q;
  pari_sp av;
  int k, fl = -1;
  byteptr d = diffptr+2;

  av = avma;
  for (q = 3; *d; )
  {
    if (q%p != 1 || smodis(et,q) == 0) goto repeat;

    if (smodis(N,q) == 0) return -1;
    k = u_val(q-1, p);
    if (!filltabs(N,p,k,ltab, 1)) return 0; 
    if (p >= 3)      fl = step4a(N,q,p,k, NULL);
    else if (k >= 3) fl = step4b(N,q,k);
    else if (k == 2) fl = step4c(N,q);
    else             fl = step4d(N,q);
    tabmatvite[1] = 0;
    if (fl == -1) return (int)(-q);
    if (fl == 1) {ctglob = max(ctglob,ct); return 1;}
    ct++; avma = av;
   repeat:
    NEXT_PRIME_VIADIFF(q,d);
  }
  err(bugparier,"aprcl test fails! this is highly improbable");
  return 0;
}

static GEN
step6(GEN N, ulong t, GEN et)
{
  GEN N1,r,p1;
  ulong i;
  pari_sp av;

  if (dotime) (void)timer2();
  N1 = resii(N, et);
  r = gun; av = avma;
  for (i=1; i<t; i++)
  {
    r = resii(mulii(r,N1), et);
    if (!signe(resii(N,r)) && !gcmp1(r) && !egalii(r,N))
    {
      p1 = cgetg(3,t_VEC);
      p1[1] = (long)r;
      p1[2] = zero; return p1;
    }
    if ((i & 0x1f) == 0) r = gerepileuptoint(av, r);
  }
  if (dotime) sgt6 = timer2();
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

static void
seetimes()
{
  int i;
  ulong s,sc;

  s = sc = 0; for (i=1; i<lg(sgt); i++) {s+=sgt[i]; sc+=ctsgt[i];}
  printf("Timings in ms:\nJacobi sums = %lu, Galois Automorphisms = %lu\n",sgtjac,sgtaut);
  printf("Global Fermat powerings = %lu\n",s);
  printf("Number of Fermat powerings = %lu\n",sc);
  printf("Individual Fermat powerings = "); output(gtovec(sgt));
  printf("Number of individual Fermat powerings = "); output(gtovec(ctsgt));
  printf("Final trial divisions = %lu\n",sgt6);
  printf("Maximal number of nondeterministic steps = %lu\n",ctglob);
}

GEN
aprcl(GEN N)
{
  GEN et, fat, flaglp, tabfaq, tabj, res, globfa;
  long fl;
  ulong ltab, lfat, p, q, lfaq, k, t, i, j, l;
  pari_sp av, av2;

  if (cmpis(N,12) <= 0)
    switch(itos(N))
    {
      case 2: case 3: case 5: case 7: case 11: return gun;
      default: return _res(0,0);
    }
  ctglob = 0;
  if (dotime) (void)timer2();
  t = compt(N);
  if (DEBUGLEVEL) fprintferr("Choosing t = %ld\n",t);
  et = e(t);
  if (cmpii(sqri(et),N) < 0) err(bugparier,"aprcl: e(t) too small");
  if (!gcmp1(mppgcd(N,mulsi(t,et)))) return _res(1,0);

  fat = calcglobs(N, t, &ltab); 
  if (!fat) return _res(1,0);
  lfat = lg(fat); p = fat[lfat-1]; /* largest p | t */
  flaglp = cgetg(p+1, t_VECSMALL);
  flaglp[2] = 0;
  for (i=2; i<lfat; i++)
  {
    p = fat[i]; q = p*p;
    flaglp[p] = (powuumod(smodis(N,q),p-1,q) != 1);
  }
  globfa = (GEN)decomp(shifti(et, -vali(et)))[1];
  calcjac(globfa, &tabfaq, &tabj);
  
  sgtaut = 0;
  av = avma; l = lg(globfa);
  if (dotime)
  {
    sgtjac = timer2();
    fprintferr("Jacobi sums and tables computed\n");
    fprintferr("q-values (# = %ld, largest = %ld): ", l-1, globfa[l-1]);
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
      p = P[j];
      k = E[j];
      if (p >= 3)      fl = step4a(N,q,p,k, gmael(tabj,i,j));
      else if (k >= 3) fl = step4b(N,q,k);
      else if (k == 2) fl = step4c(N,q);
      else             fl = step4d(N,q);
      if (fl == -1) return _res(q,p);
      if (fl == 1) flaglp[p] = 1;
    }
  }
  if (dotime) fprintferr("\nNormal test done; testing conditions lp\n");
  for (i=1; i<lfat; i++)
  {
    p = fat[i]; if (flaglp[p]) continue;

    fl = step5(N, p, et, ltab);
    if (!fl) return _res(1,0);
    if (fl < 0) return _res(fl,p);
  }
  if (dotime) fprintferr("Conditions lp done, doing step6\n");
  res = step6(N,t,et);
  if (dotime && (typ(res) == t_INT)) seetimes();
  return res;
}

long
isprimeAPRCL(GEN N)
{
  pari_sp av = avma;
  GEN res = aprcl(N);
  avma = av; return (typ(res) == t_INT);
}
