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

static ulong kglob,NBITSN;
static GEN *tabaall,*tabtall,*tabcyc,tabE,tabTH,tabeta,globfa,tabfaq,tabj,sgt,ctsgt;

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
red_mod_cyclo(GEN T, long p)
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

/* x t_VECSMALL, n > 0. Return x mod polcyclo(2^n) = (x^(2^(n-1)) + 1). DESTROY x */
static GEN
u_red_mod_cyclo2n(GEN x, int n)
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
/* x t_POL, n > 0. Return x mod polcyclo(2^n) = (x^(2^(n-1)) + 1). DESTROY x */
static GEN
red_mod_cyclo2n(GEN x, int n)
{
  long i, pow2 = 1<<(n-1);

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

/* special case R->C = polcyclo(p) */
static GEN
_red2(GEN x, red_t *R) {
  return FpX_red(red_mod_cyclo(x, R->n), R->N);
}
static GEN
_red(GEN x, red_t *R) {
  return FpX_red(gres(x, R->C), R->N);
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
  b = (GEN)pol[4];
  c = (GEN)pol[3]; c2 = shifti(c,1);
  d = (GEN)pol[2];
  if (lv==4)
  {
    A = mulii(b, subii(c2,b));
    B = addii(sqri(c), mulii(b, subii(shifti(d,1),b)));
    C = subii(mulii(c2,d), sqri(b));
    D = mulii(subii(d,b), addii(d,b));
  }
  else
  {
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
  D = modii(D, R->N);
  return coefs_to_pol(4,A,B,C,D);
}

static GEN
_mul(GEN x, GEN y, red_t *R) {
  return R->red(gmul(x,y), R);
}

static GEN
_powpolmod(int pk, GEN jac, red_t *R, GEN (*_sqr)(GEN, red_t *))
{
  const GEN taba = tabaall[pk];
  const GEN tabt = tabtall[pk];
  const int efin = lg(taba)-1;
  GEN res,pol2, *vz;
  int lv,tf,f,i;
  ulong av;

  lv = 1 << (kglob-1);
  vz = (GEN*)cgetg(lv+1,t_VEC);
  res = lift(jac); pol2 = _sqr(res, R);
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

GEN
powpolmod(red_t *R, int k, int pk, GEN jac)
{
  GEN (*_sqr)(GEN, red_t *);

  if (pk == 3) {
    R->red = &_red; _sqr = &sqrmod3;
  } else if (pk == 4) {
    R->red = &_red; _sqr = &sqrmod4;
  } else if (pk == 5) {
    R->red = &_red; _sqr = &sqrmod5;
  } else if (k == 1 && pk >= 7) {
    R->n = pk;
    R->red = &_red2; _sqr = &sqrmod;
  } else {
    R->red = &_red; _sqr = &sqrmod;
  }
  return _powpolmod(pk,jac, R, _sqr);
}

/* FIXME: these 2 could be exported */
static long
u_val(ulong n, ulong p)
{
  ulong dummy;
  return svaluation(n,p,&dummy);
}
static int
u_pow(int p, int k)
{
  int i, pk;

  if (!k) return 1;
  if (p == 2) return 1<<k;
  pk = p; for (i=2; i<=k; i++) pk *= p;
  return pk;
}

static GEN
e(ulong t)
{
  GEN fa,pr,ex,s;
  ulong nbd,m,k,d;
  int lfa,i,j;

  fa = decomp(stoi(t));
  pr = (GEN)fa[1]; settyp(pr, t_VECSMALL);
  ex = (GEN)fa[2]; settyp(ex, t_VECSMALL); lfa = lg(pr);
  nbd = 1;
  for (i=1; i<lfa; i++)
  {
    ex[i] = itos((GEN)ex[i]) + 1;
    pr[i] = itos((GEN)pr[i]);
    nbd *= ex[i];
  }
  s = gdeux; /* nbd = number of divisors */
  for (k=0; k<nbd; k++)
  {
    m = k; d = 1;
    for (j=1; m; j++)
    {
      d *= u_pow(pr[j], m % ex[j]);
      m /= ex[j];
    }
    /* d runs through the divisors of t */
    if (isprime(stoi(++d))) s = muliu(s, u_pow(d, 1 + u_val(t,d)));
  }
  return s;
}

static ulong
compt(GEN N)
{
  ulong Bint,t;
  GEN B;

  B = mulsr(100, divrr(glog(N,DEFAULTPREC), dbltor(log(10.))));
  Bint = itos(gceil(B));
/* Bint < [200*log_10 e(t)] ==> return t. For e(t) < 10^529, good for N < 10^1058 */
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
    if (cmpii(e(t),B) > 0) break;
  return t;
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
    a = mulssmod(g,a,q);
    w[a]   = i;
    w[q-a] = i+qm1s2;
  }
  return v;
}

static void
compute_fg(ulong q, int half, GEN *tabf, GEN *tabg)
{
  const long qm3s2 = (q-3)>>1;
  const long l = half? qm3s2: q-2;
  ulong x;
  *tabf = computetabdl(q);
  *tabg = cgetg(l+1,t_VECSMALL);
  for (x=1; x<=l; x++) (*tabg)[x] = (*tabf)[x] + (*tabf)[q-x-1];
}

/* p odd prime */
static GEN
get_jac(GEN N, ulong q, ulong p, int k, GEN tabf, GEN tabg)
{
  GEN ze, vpk;
  long i, qm3s2;
  ulong x, pk;

  pk = u_pow(p,k);
  vpk = cgetg(pk+1,t_VECSMALL);
  for (i=1; i<=pk; i++) vpk[i] = 0;
  ze = tabcyc[pk];

  qm3s2 = (q-3)>>1;
  for (x=1; x<=qm3s2; x++) vpk[ tabg[x]%pk + 1 ] += 2;
  vpk[ (2*tabf[qm3s2+1])%pk + 1 ]++;
  return u_red(vpk,ze);
}

/* p = 2 */
static GEN
get_jac2(GEN N, ulong q, int k, GEN *j2q, GEN *j3q)
{
  GEN jpq, vpk, tabf, tabg;
  long i, qm3s2;
  ulong x, pk;

  if (k == 1) return NULL;

  compute_fg(q,0, &tabf,&tabg);

  pk = u_pow(2,k);
  vpk = cgetg(pk+1,t_VECSMALL);
  for (i=1; i<=pk; i++) vpk[i] = 0;

  qm3s2 = (q-3)>>1;
  for (x=1; x<=qm3s2; x++) vpk[ tabg[x]%pk + 1 ] += 2;
  vpk[ (2*tabf[qm3s2+1])%pk + 1 ]++;
  jpq = u_red_mod_cyclo2n(vpk, k);

  if (k == 2) return jpq;

  if (mod8(N) >= 5)
  {
    GEN v8 = cgetg(9,t_VECSMALL);
    for (x=1; x<=8; x++) v8[x] = 0;
    for (x=1; x<=q-2; x++) v8[ ((2*tabf[x]+tabg[x])&7) + 1 ]++;
    *j2q = polinflate(gsqr(u_red_mod_cyclo2n(v8,3)), pk>>3);
    *j2q = red_mod_cyclo2n(*j2q, k);
  }

  for (i=1; i<=pk; i++) vpk[i] = 0;
  for (x=1; x<=q-2; x++) vpk[ (tabf[x]+tabg[x])%pk + 1 ]++;
  *j3q = gmul(jpq, u_red_mod_cyclo2n(vpk,k));
  *j3q = red_mod_cyclo2n(*j3q, k);
  return jpq;
}

static void
calcjac(GEN N, GEN et)
{
  ulong q, l;
  int lfaq,p,k,i,j;
  GEN J,tabf,tabg,faq,faqpr,faqex;

  globfa = (GEN)decomp(shifti(et,-vali(et)))[1];
  l = lg(globfa);
  tabfaq= cgetg(l,t_VEC);
  tabj  = cgetg(l,t_VEC);
  for (i=1; i<l; i++)
  {
    q = itos((GEN)globfa[i]); /* odd prime */
    faq = decomp(stoi(q-1)); tabfaq[i] = (long)faq;
    faqpr = (GEN)faq[1];
    faqex = (GEN)faq[2]; lfaq = lg(faqpr);
    k = itos((GEN)faqex[1]);

    compute_fg(q, 1, &tabf, &tabg); /* faqpr[1] = 2 */

    J = cgetg(lfaq,t_VEC); tabj[i] = (long)J;
    for (j=2; j<lfaq; j++) /* skip p = 2 */
    {
      p = itos((GEN)faqpr[j]);
      k = itos((GEN)faqex[j]);
      J[j] = (long)get_jac(N,q,p,k,tabf,tabg);
    }
  }
}

static void
inittabs(int lv)
{
  int i;
  tabaall = (GEN*)cgetg(lv,t_VECSMALL);
  tabtall = (GEN*)cgetg(lv,t_VECSMALL);
  tabcyc  = (GEN*)cgetg(lv,t_VEC);
  tabE = cgetg(lv,t_VEC);
  tabTH= cgetg(lv,t_VEC);
  tabeta=cgetg(lv,t_VEC);
  sgt  = cgetg(lv,t_VECSMALL);
  ctsgt= cgetg(lv,t_VECSMALL);
  for (i=1; i<lv; i++) sgt[i] = ctsgt[i] = 0;
}

static void
filltabs(GEN N, int p, int k, ulong ltab)
{
  const ulong mask = (1<<kglob)-1;
  int pk,i,j,LE=0;
  ulong s,e;
  GEN tabt,taba,m,E=gzero,p1;

  pk = u_pow(p,k);
  tabcyc[pk] = cyclo(pk,0);

  p1 = cgetg(pk+1,t_VEC);
  for (i=1; i<=pk; i++) p1[i] = lmod(gpowgs(polx[0],i-1), tabcyc[pk]);
  tabeta[pk] = lmul(gmodulcp(gun,N),p1);

  if (p > 2)
  {
    LE = pk - pk/p + 1; E = cgetg(LE,t_VECSMALL);
    for (i=1,j=0; i<pk; i++)
      if (i%p) E[++j] = i;
  }
  else if (k >= 3)
  {
    LE = (pk>>2) + 1; E = cgetg(LE,t_VECSMALL);
    for (i=1,j=0; i<pk; i++)
      if ((i%8)==1 || (i%8)==3) E[++j] = i;
  }
  if (p>2 || k>=3)
  {
    tabE[pk] = (long)E;
    p1 = cgetg(LE,t_VEC);
    for (i=1; i<LE; i++)
    {
      GEN p2 = cgetg(3,t_VECSMALL);
      p2[1] = p2[2] = E[i];
      p1[i] = (long)p2;
    }
    tabTH[pk] = (long)p1;
  }

  tabt = cgetg(ltab+1,t_VECSMALL);
  taba = cgetg(ltab+1,t_VECSMALL);
  m = divis(N,pk);
  for (e=1; e<=ltab && signe(m); e++)
  {
    s = vali(m); m = shifti(m,-s);
    tabt[e] = e==1? s: s+kglob;
    taba[e] = signe(m)? ((modBIL(m) & mask)+1)>>1: 0;
    m = shifti(m, -kglob);
  }
  if (e > ltab) err(bugparier,"filltabs");
  setlg(taba, e); tabaall[pk] = taba;
  setlg(tabt, e); tabtall[pk] = tabt;
}

static void
extend(GEN *ptv, int lz)
{
  GEN w, v = *ptv;
  long l = lg(v), tv = typ(v), L = l+lz, i;

  *ptv = w = cgetg(L,tv);
  if (tv == t_VEC)
  {
    for (i=1; i<l; i++) w[i] = lcopy((GEN)v[i]);
    for (   ; i<L; i++) w[i] = zero;
  }
  else
  {
    for (i=1; i<l; i++) w[i] = v[i];
    for (   ; i<L; i++) w[i] = 0;
  }
}

static void
extendtabs(GEN N, int p, int k)
{
  const int pk = u_pow(p,k), L = lg(tabaall)-1, lz = pk - L;
  const ulong ltab = (NBITSN/kglob)+2;

  if (lz <= 0)
  {
    if (tabcyc[pk]==0) filltabs(N,p,k,ltab);
    return;
  }
  extend((GEN*)&tabaall, lz);
  extend((GEN*)&tabtall, lz);
  extend((GEN*)&tabcyc, lz);
  extend(&tabE, lz);
  extend(&tabTH, lz);
  extend(&tabeta, lz);
  extend(&sgt, lz);
  extend(&ctsgt, lz);
  filltabs(N,p,k, ltab);
}

static GEN
calcglobs(GEN N, ulong t)
{
  GEN fat,fapr,faex;
  int lfa,pk,p,ex,i,k;
  ulong ltab, ltaball;

  NBITSN = bit_accuracy(lgefint(N)) - 1;
  while (bittest(N,NBITSN)==0) NBITSN--;
  NBITSN++;
  kglob=3; while (((kglob+1)*(kglob+2) << (kglob-1)) < NBITSN) kglob++;
  ltab = (NBITSN/kglob) + 2;

  fat = decomp(stoi(t));
  fapr = (GEN)fat[1];
  faex = (GEN)fat[2];
  lfa = lg(fapr); ltaball = 1;
  for (i=1; i<lfa; i++)
  {
    pk = u_pow(itos((GEN)fapr[i]), itos((GEN)faex[i]));
    if (pk > ltaball) ltaball = pk;
  }
  inittabs(ltaball+1);
  for (i=1; i<lfa; i++)
  {
    p = itos((GEN)fapr[i]);
    ex= itos((GEN)faex[i]);
    for (k=1; k<=ex; k++) filltabs(N,p,k,ltab);
  }
  return fapr;
}

/* Calculer sig_a^{-1}(z) pour z dans Q(ze) et sig_a: ze -> ze^a */
static GEN
aut(int pk, GEN z,int a)
{
  GEN v = cgetg(pk+1,t_VEC);
  int i;
  for (i=1; i<=pk; i++)
    v[i] = (long)polcoeff0(z, (a*(i-1))%pk, 0);
  return gmodulcp(gtopolyrev(v,0), tabcyc[pk]);
}

/* calculer z^v pour v dans Z[G] represente par des couples [sig_x^{-1},y] */
static GEN
autvec(int pk, GEN z, GEN v)
{
  int i,lv = lg(v);
  GEN s = gun;
  for (i=1; i<lv; i++)
    if (((GEN)v[i])[2])
      s = gmul(s, gpowgs(aut(pk,z,((GEN)v[i])[1]), ((GEN)v[i])[2]));
  return s;
}

static GEN
get_AL(GEN N, int pk)
{
  const int r = smodis(N, pk);
  GEN AL, E = (GEN)tabE[pk];
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
  GEN etats = (GEN)tabeta[pk];
  long i;
  for (i=1; i<=pk; i++)
    if (gegal(s, (GEN)etats[i])) return i-1;
  return pk;
}

static int
step4a(GEN N, ulong q, int p, int k, GEN jpq)
{
  int pk,ind;
  GEN AL,s1,s2,s3;
  red_t R;

  if (!jpq)
  {
    GEN tabf, tabg;
    compute_fg(q,1, &tabf,&tabg);
    jpq = get_jac(N,q,p,k,tabf,tabg);
  }
  pk = u_pow(p,k);
  R.N = N;
  R.C = tabcyc[pk];
  AL = get_AL(N, pk);

  s1 = autvec(pk,jpq,(GEN)tabTH[pk]);
  if (DEBUGLEVEL) timer();
  s2 = powpolmod(&R, k,pk,s1);
  if (DEBUGLEVEL) {sgt[pk]+=timer();ctsgt[pk]++;};
  s3 = autvec(pk,jpq,AL);
  s3 = _red(gmul(lift(s3),s2), &R);

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
  int ind;
  GEN AL,s1,s2,s3, j2q,j3q;
  red_t R;

  (void)get_jac2(N,q,k, &j2q,&j3q);

  R.N = N;
  R.C = tabcyc[pk];
  AL = get_AL(N, pk);

  s1 = autvec(pk,j3q,(GEN)tabTH[pk]);
  if (DEBUGLEVEL) timer();
  s2 = powpolmod(&R, k,pk,s1);
  if (DEBUGLEVEL) {sgt[pk]+=timer();ctsgt[pk]++;}
  s3 = autvec(pk,j3q,AL);
  s3 = _red(gmul(lift(s3),s2), &R);
  if (mod8(N) >= 5) s3 = _red(gmul(j2q, s3), &R);

  ind = look_eta(pk, s3);
  if (ind == pk) return -1;
  if ((ind&1)==0) return 0;
  else
  {
    s3 = powmodulo(stoi(q), shifti(N,-1), N);
    return is_m1(s3, N);
  }
}

/* p=2, k=2 */
static int
step4c(GEN N, ulong q)
{
  const int pk = 4;
  int ind;
  GEN s0,s1,s3, jpq = get_jac2(N,q,2, NULL,NULL);
  red_t R;

  R.N = N;
  R.C = tabcyc[pk];

  s0 = sqrmod4(jpq, &R);
  s1 = gmulsg(q,s0);
  if (DEBUGLEVEL) timer();
  s3 = powpolmod(&R, 2,pk,s1);
  if (DEBUGLEVEL) {sgt[pk]+=timer();ctsgt[pk]++;}
  if (mod4(N) == 3) s3 = _red(gmul(s0,s3), &R);

  ind = look_eta(pk, s3);
  if (ind == pk) return -1;
  if ((ind&1)==0) return 0;
  else
  {
    s3 = powmodulo(stoi(q), shifti(N,-1), N);
    return is_m1(s3,N);
  }
}

/* p=2, k=1 */
static int
step4d(GEN N, ulong q)
{
  GEN s1;

  s1 = powmodulo(negi(stoi(q)), shifti(N,-1), N);
  if (gcmp1(s1)) return 0;
  if (is_m1(s1,N)) return (mod4(N) == 1);
  return -1;
}

/* return 1 [OK so far],0 [APRCL fails] or < 0 [not a prime] */
static int
step5(GEN N, int p, GEN et)
{
  ulong q,av;
  int k, fl = -1;
  byteptr d = diffptr+2;

  av = avma;
  for (q = 3; *d; q += *d++)
  {
    avma = av;
    if (q%p != 1 || smodis(et,q) == 0) continue;

    if (smodis(N,q) == 0) return -1;
    k = u_val(q-1, p);
    extendtabs(N,p,k);

    if (p>=3)        fl = step4a(N,q,p,k, NULL);
    else if (k >= 3) fl = step4b(N,q,k);
    else if (k == 2) fl = step4c(N,q);
    else             fl = step4d(N,q);
    if (fl == -1) return (int)(-q);
    if (fl == 1) return 1;
  }
  return 0;
}

static GEN
step6(GEN N, ulong t, GEN et)
{
  GEN N1,r,p1;
  ulong i,av;

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
  return gun;
}

static GEN
_res(long a, long b)
{
  GEN z;
  if (b) { z=cgetg(4, t_VEC); z[1]=lstoi(a); z[2]=lstoi(b); z[3]=zero; }
  else   { z=cgetg(3, t_VEC); z[1]=lstoi(a); z[2]=zero; }
  return z;
}

GEN
aprcl(GEN N)
{
  GEN et,fat,flaglp,faq,faqpr,faqex;
  long fl;
  ulong lfat,p,q,lfaq,k,t,i,j,l;
  ulong av;

  if (cmpis(N,12) <= 0)
    switch(itos(N))
    {
      case 2: case 3: case 5: case 7: case 11: return gun;
      default: return _res(0,0);
    }
  t = compt(N);
  if (DEBUGLEVEL>=2) fprintferr("choosing t = %ld\n",t);
  et = e(t);
  if (cmpii(sqri(et),N) < 0) err(bugparier,"aprcl: e(t) too small");
  if (!gcmp1(mppgcd(N,mulsi(t,et)))) return _res(1,0);

  fat = calcglobs(N,t); lfat = lg(fat);
  p = itos((GEN)fat[lfat-1]); /* largest p | t */
  flaglp = cgetg(p+1, t_VECSMALL);
  flaglp[2] = 0;
  for (i=2; i<lfat; i++)
  {
    p = itos((GEN)fat[i]); q = p*p;
    flaglp[p] = (powuumod(smodis(N,q),p-1,q) != 1);
  }
  calcjac(N, et);
  if (DEBUGLEVEL>=3) fprintferr("Jacobi sums and tables computed\nq-values: ");
  av = avma; l = lg(globfa);
  for (i=1; i<l; i++)
  {
    avma = av;
    q = itos((GEN)globfa[i]);
    if (DEBUGLEVEL>=3) fprintferr("%ld ",q);
    faq = (GEN)tabfaq[i];
    faqpr = (GEN)faq[1];
    faqex = (GEN)faq[2]; lfaq = lg(faqpr);
    for (j=1; j<lfaq; j++)
    {
      p = itos((GEN)faqpr[j]);
      k = itos((GEN)faqex[j]);
      if (p >= 3)      fl = step4a(N,q,p,k, gmael(tabj,i,j));
      else if (k >= 3) fl = step4b(N,q,k);
      else if (k == 2) fl = step4c(N,q);
      else             fl = step4d(N,q);
      if (fl == -1) return _res(q,p);
      if (fl == 1) flaglp[p] = 1;
    }
  }
  if (DEBUGLEVEL>=3) fprintferr("\nnormal test done; testing conditions lp\n");
  for (i=1; i<lfat; i++)
  {
    p = itos((GEN)fat[i]);
    if (flaglp[p] == 0)
    {
      fl = step5(N,p,et);
      if (fl < 0) return _res(fl,p);
      if (fl==0) err(talker,"aprcl test fails! this is highly improbable");
    }
  }
  if (DEBUGLEVEL>=3) fprintferr("conditions lp done, doing step6\n");
  return step6(N,t,et);
}

/* si flag=0 retourne une reponse vrai/faux, sinon retourne des details
quand N non premier */

GEN
istrueprime(GEN N, int flag)
{
  ulong av = avma;
  GEN res = aprcl(N);
  if (typ(res) == t_INT) { avma = av; return gun; }
  if (flag) return gerepilecopy(av, res);
  avma = av; return gzero;
}
