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

static ulong sgtaut,sgt6,sgtjac,kglob,NBITSN;
static GEN globfa,tabfaq,tabj,tabj2,tabj3,sgt,ctsgt;
static GEN *tabaall,*tabtall,tabefin,*tabcyc,tabE,tabTH,tabeta;

/* contains [t,floor(200*log(e(t))/log(10))] for e(t) < 10^529, good for
 N<10^1058 */

static ulong vet[61][2] =
{{6,540},{12,963},{24,1023},{48,1330},{36,1628},{60,1967},{120,2349},{180,3083},{240,3132},{504,3270},{360,3838},{420,4115},{720,4621},{840,4987},{1440,5079},{1260,6212},{1680,6686},{2520,8137},{3360,8415},{5040,10437},{13860,11643},{10080,12826},{13860,11643},{10080,12826},{16380,13369},{21840,13540},{18480,15060},{27720,15934},{32760,17695},{36960,18816},{55440,21338},{65520,23179},{98280,23484},{110880,27465},{131040,30380},{131040,30380},{166320,31369},{196560,33866},{262080,34530},{277200,36195},{360360,37095},{480480,38179},{332640,41396},{554400,43301},{720720,47483},{665280,47742},{831600,50202},{1113840,52502},{1441440,60245},{1663200,63112},{2227680,65395},{2162160,69895},{2827440,71567},{3326400,75708},{3603600,79377},{6126120,82703},{4324320,91180},{6683040,93978},{7207200,98840},{11138400,99282},{8648640,105811}};

static int tabfaux[12]={0,1,1,0,1,0,1,0,0,0,1,0};

typedef struct red_t {
  GEN T; /* x^n - 1 */
  GEN C; /* polcyclo(n) */
  GEN N; /* prime we are certifying */
  GEN (*red)(GEN x, struct red_t *);
} red_t;

/* programmes de puissances de polmods mod N, fenetre flexible */
/* la donnee est un polmod, la sortie est un pol entiers. */

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

static GEN
_red2(GEN x, red_t *R) {
  return FpX_red(gmod(gmod(x, R->T), R->C), R->N);
}
static GEN
_red(GEN x, red_t *R) {
  return FpX_red(gmod(x, R->C), R->N);
}

static GEN
sqrmod(GEN x, red_t *R) {
  return R->red(gsqr(x), R);
}

/* pol^2 mod (x^2+x+1, N) */
static GEN
sqrmod3(GEN pol, red_t *R)
{
  GEN a,b,bma,c,d,p1;
  long lv=lgef(pol);

  if (lv==2) return pol;
  if (lv==3)
  {
    p1 = cgetg(3,t_POL);
    p1[2] = (long)modii(sqri((GEN)pol[2]), R->N);
    p1[1] = pol[1]; return p1;
  }
  a = (GEN)pol[3];
  b = (GEN)pol[2];
  bma = subii(b,a);
  c = modii(mulii(a,addii(b,bma)), R->N);
  d = modii(mulii(bma,addii(a,b)), R->N);
  return makepoldeg1(c,d);
}

/* pol^2 mod (x^4+1,N) */
static GEN
sqrmod4(GEN pol, red_t *R)
{
  GEN a,b,c,d,p1;
  long lv=lgef(pol);

  if (lv==2) return pol;
  if (lv==3)
  {
    p1 = cgetg(3,t_POL);
    p1[2] = (long)modii(sqri((GEN)pol[2]), R->N);
    p1[1] = pol[1]; return p1;
  }
  a = (GEN)pol[3];
  b = (GEN)pol[2];
  c = modii(mulii(a, shifti(b,1)), R->N);
  d = modii(mulii(subii(b,a),addii(b,a)), R->N);
  return makepoldeg1(c,d);
}

/* x^n - 1 */
static GEN
xn_1(long n)
{
  GEN T = cgetg(n+3,t_POL);
  long i;
  T[1] = evalsigne(1)|evallgef(n+3);
  T[2] = lstoi(-1);
  for (i=3; i<=n+1; i++) T[i] = zero;
  T[i] = un; return T;
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
  const int efin = tabefin[pk];
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
  } else if (k == 1 && pk >= 5) {
    R->T = xn_1(pk);
    R->red = &_red2; _sqr = &sqrmod;
  } else {
    R->red = &_red; _sqr = &sqrmod;
  }
  return _powpolmod(pk,jac, R, _sqr);
}

static GEN
e(ulong t)
{
  GEN fa,fapr,faex,s,dp1, T = stoi(t);
  ulong nbd,m,k,ex,d;
  int lfa,i,j;

  fa = decomp(T);
  fapr = (GEN)fa[1];
  faex = (GEN)fa[2]; lfa = lg(fapr);
  nbd=1; for (i=1; i<lfa; i++) nbd *= itos((GEN)faex[i])+1;
  s = stoi(2);
  for (k=0; k<nbd; k++)
  {
    m = k; d = 1;
    for (j=1; j<lfa; j++)
    {
      ex = itos((GEN)faex[j])+1;
      d *= itos(gpowgs((GEN)fapr[j], m%ex));
      m /= ex;
    }
    dp1 = stoi(d+1);
    if (isprime(dp1)) s = mulii(s, gpuigs(dp1, 1 + ggval(T,dp1)));
  }
  return s;
}

static ulong
compt(GEN N)
{
  int lvet,i;
  ulong lim,Bint,t;
  GEN B,LN = glog(N,DEFAULTPREC);

  Bint = itos(gceil(mulsr(100,divrr(LN, glog(stoi(10),DEFAULTPREC)))));
  lvet = 61;
  for (i=0; i<lvet; i++)
    if (vet[i][1]>Bint) return vet[i][0];
  B = racine(N); lim = 0xffffffff;
  for (t = vet[lvet-1][0]+840; t<=lim; t+=840)
    if (cmpii(e(t),B) > 0) return t;
  err(talker,"no t < 2^32 found in compt");
  return 0; /* not reached */
}

/* x a non-zero VECSMALL */
GEN
smallpolrev(GEN x)
{
  long i,j, lx = lg(x);
  GEN y;

  while (lx-- && x[lx]==0);
  i = lx+2; y = cgetg(i,t_POL);
  y[1] = evallgef(i) | evalsigne(1);
  for (j=2; j<i; j++) y[j] = lstoi(x[j-1]);
  return y;
}

/* tabdl[i] = discrete log of i+1 */
static GEN
computetabdl(ulong q)
{
  GEN v = cgetg(q-1,t_VECSMALL);
  ulong h,qm3s2,qm1s2,qm1,a,i;
  ulong av = avma;

  h = itos(lift(gener(stoi(q))));
  avma = av;
  qm3s2 = (q-3)>>1;
  qm1s2 = qm3s2+1;
  qm1 = q-1;
  v[q-2]=qm1s2; a=1;
  for (i=1; i<=qm3s2; i++)
  {
    a = mulssmod(h,a,q);
    v[a-1]   = i;
    v[qm1-a] = i+qm1s2;
  }
  return v;
}

static int
_pk(int p, int k)
{
  int i, pk;
  pk = p; for (i=2; i<=k; i++) pk *= p;
  return pk;
}

static void
calcjac(GEN et)
{
  ulong q,ltabg,qm3s2,x, l;
  int lfaq,p,k,ii,i,j,pk;
  GEN T,ze8,tabf,tabg,faq,faqpr,faqex,ze,vpk,v8;

  globfa = (GEN)decomp(shifti(et,-vali(et)))[1];
  l = lg(globfa);
  tabfaq= cgetg(l,t_VEC);
  tabj  = cgetg(l,t_VEC);
  tabj2 = cgetg(l,t_VEC);
  tabj3 = cgetg(l,t_VEC);
  ze8 = cyclo(8,0);
  v8 = cgetg(9,t_VECSMALL);
  for (i=1; i<l; i++)
  {
    q = itos((GEN)globfa[i]);
    tabf = computetabdl(q);
    qm3s2 = (q-3)>>1;
    faq = decomp(stoi(q-1)); tabfaq[i] = (long)faq;
    faqpr = (GEN)faq[1];
    faqex = (GEN)faq[2]; lfaq = lg(faqpr);
    ltabg = itos((GEN)faqex[1]) == 2? qm3s2: q-2;
    tabg = cgetg(ltabg+1,t_VECSMALL);
    for (x=1; x<=ltabg; x++) tabg[x] = tabf[x] + tabf[q-x-1];
    T = cgetg(lfaq,t_VEC); tabj[i] = (long)T;
    for (j=1; j<lfaq; j++)
    {
      p = itos((GEN)faqpr[j]);
      k = itos((GEN)faqex[j]);
      pk = _pk(p,k);
      vpk = cgetg(pk+1,t_VECSMALL); for (ii=1; ii<=pk; ii++) vpk[ii] = 0;
      ze = tabcyc[pk];
      if (p>=3 || k>=2)
      {
	for (x=1; x<=qm3s2; x++) vpk[ tabg[x]%pk + 1 ]++;
	for (x=1; x<=pk;    x++) vpk[x] <<= 1;
	vpk[ (2*tabf[qm3s2+1])%pk + 1 ]++;
	T[j] = lmod(smallpolrev(vpk),ze);
      }
      if (p==2 && k>=3)
      {
	for (x=1; x<=ltabg; x++) tabg[x] += tabf[x];

	for (x=1; x<=8; x++) v8[x] = 0;
	for (x=1; x<=q-2; x++) v8[ ((tabf[x]+tabg[x])&7) + 1 ]++;
	tabj2[i] = lmod(polinflate(gsqr(gmod(smallpolrev(v8),ze8)), pk>>3),ze);

	for (x=1; x<=pk; x++) vpk[x] = 0;
	for (x=1; x<=q-2; x++) vpk[ tabg[x]%pk + 1 ]++;
	tabj3[i] = lmod(gmul((GEN)T[1], gmod(smallpolrev(vpk),ze)), ze);
      }
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
  tabefin = cgetg(lv,t_VECSMALL);
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
  int pk,efin,i,j,LE=0;
  ulong s,mask=(1<<kglob)-1,ee,lp1;
  GEN tabt,taba,m,E=gzero,p1,p2;

  pk = _pk(p,k);
  tabcyc[pk] = cyclo(pk,0);

  p1 = cgetg(pk+1,t_VEC);
  for (i=1; i<=pk; i++) p1[i] = lmod(gpuigs(polx[0],i-1), tabcyc[pk]);
  tabeta[pk] = lmul(gmodulcp(gun,N),p1);

  if (p > 2)
  {
    LE = pk-pk/p+1; E = cgetg(LE,t_VECSMALL);
    for (i=1,j=0; i<pk; i++)
      if (i%p) E[++j]=i;
  }
  else if (k >= 3)
  {
    LE = (pk>>2) + 1; E = cgetg(LE,t_VECSMALL);
    for (i=1,j=0; i<pk; i++)
      if ((i%8)==1 || (i%8)==3) E[++j]=i;
  }
  if (p>2 || k>=3)
  {
    tabE[pk] = (long)E;
    p1 = cgetg(LE,t_VEC);
    for (i=1; i<LE; i++)
    {
      p2=cgetg(3,t_VECSMALL);
      p2[1] = p2[2] = E[i];
      p1[i] = (long)p2;
    }
    tabTH[pk] = (long)p1;
  }

  tabt = cgetg(ltab+1,t_VECSMALL);
  taba = cgetg(ltab+1,t_VECSMALL);
  m = divis(N,pk);
  s = vali(m); tabt[1] = s; efin = ltab+1;
  for (ee=1; ee<=ltab; ee++)
  {
    p1 = shifti(m,-s); lp1 = lgefint(p1);
    taba[ee] = lp1==2? 0: (((p1[lp1-1])&mask)+1)>>1;
    m = shifti(m, -(s+kglob));
    if (!signe(m)) { efin = ee; break; }
    s = vali(m);
    tabt[ee+1] = s+kglob;
  }
  if (efin > ltab) err(bugparier,"filltabs");
  tabaall[pk] = taba;
  tabtall[pk] = tabt;
  tabefin[pk] = efin;
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
  const int pk = _pk(p,k), L = lg(tabaall)-1, lz = pk - L;
  const ulong ltab = (NBITSN/kglob)+2;

  if (lz <= 0)
  {
    if (tabcyc[pk]==0) filltabs(N,p,k,ltab);
    return;
  }
  extend((GEN*)&tabaall, lz);
  extend((GEN*)&tabtall, lz);
  extend((GEN*)&tabcyc, lz);
  extend(&tabefin, lz);
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
    pk = _pk(itos((GEN)fapr[i]), itos((GEN)faex[i]));
    if (pk > ltaball) ltaball = pk;
  }
  inittabs(ltaball+1);
  for (i=1; i<lfa; i++)
  {
    p = itos((GEN)fapr[i]); ex = itos((GEN)faex[i]);
    for (k=1; k<=ex; k++) filltabs(N,p,k,ltab);
  }
  return fapr;
}

/* Calculer sig_a^{-1}(z) pour z dans Q(ze) et sig_a: ze -> ze^a */
static GEN
aut(int pk, GEN z,int x)
{
  GEN v = cgetg(pk+1,t_VEC);
  int i;
  for (i=1; i<=pk; i++)
    v[i] = (long)polcoeff0(z, (x*(i-1))%pk, 0);
  return gmodulcp(gtopolyrev(v,0), tabcyc[pk]);
}

/* calculer z^v pour v dans Z[G] represente par des couples [sig_x^{-1},y] */
static GEN
autvec(int pk, GEN z, GEN v)
{
  int i,lv = lg(v);
  GEN s = gun;
  for (i=1; i<lv; i++)
    s = gmul(s, gpuigs(aut(pk,z,((GEN)v[i])[1]), ((GEN)v[i])[2]));
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
step4a(GEN N, int p, int k, GEN jpq)
{
  int pk,i,ind;
  GEN AL,s1,s2,s3,etats;
  red_t R;

  pk = _pk(p,k);
  R.N = N;
  R.C = tabcyc[pk];
  AL = get_AL(N, pk);

  if (DEBUGLEVEL) timer();
  s1 = autvec(pk,jpq,(GEN)tabTH[pk]);
  if (DEBUGLEVEL) sgtaut+=timer();
  s2 = powpolmod(&R, k,pk,s1);
  if (DEBUGLEVEL) {sgt[pk]+=timer();ctsgt[pk]++;};
  s3 = autvec(pk,jpq,AL);
  if (DEBUGLEVEL) sgtaut+=timer();
  s3 = _red(gmul(lift(s3),s2), &R);
  if (DEBUGLEVEL) sgt[pk]+=timer();

  etats = (GEN)tabeta[pk]; ind=pk;
  for (i=1; i<=pk; i++)
    if (gegal(s3,(GEN)etats[i])) { ind = i-1; break; }
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
step4b(GEN N, ulong q, int k, GEN j2q, GEN j3q)
{
  const int pk = 1<<k;
  int ind,i;
  GEN AL,s1,s2,s3,etats;
  red_t R;

  R.N = N;
  R.C = tabcyc[pk];
  AL = get_AL(N, pk);

  if (DEBUGLEVEL) timer();
  s1 = autvec(pk,j3q,(GEN)tabTH[pk]);
  if (DEBUGLEVEL) sgtaut+=timer();
  s2 = powpolmod(&R, k,pk,s1);
  if (DEBUGLEVEL) {sgt[pk]+=timer();ctsgt[pk]++;}
  s3 = autvec(pk,j3q,AL);
  if (DEBUGLEVEL) sgtaut+=timer();
  s3 = _red(gmul(lift(s3),s2), &R);
  if (mod8(N) >= 5) s3 = _red(gmul(j2q, s3), &R);

  if (DEBUGLEVEL) sgt[pk]+=timer();
  etats = (GEN)tabeta[pk]; ind = pk;
  for (i=1; i<=pk; i++)
    if (gegal(s3,(GEN)etats[i])) { ind = i-1; break; }
  if (ind==pk) return -1;
  if ((ind&1)==0) return 0;
  else
  {
    if (DEBUGLEVEL) timer();
    s3 = powmodulo(stoi(q), shifti(N,-1), N);
    if (DEBUGLEVEL) {sgt[pk]+=timer();ctsgt[pk]++;}
    return is_m1(s3, N);
  }
}

/* p=2, k=2 */
static int
step4c(GEN N, ulong q, GEN jpq)
{
  const int pk = 4;
  int ind,i;
  GEN s0,s1,s3,etats;
  red_t R;

  R.N = N;
  R.C = tabcyc[pk];

  s0 = sqrmod4(jpq, &R);
  s1 = gmulsg(q,s0);
  if (DEBUGLEVEL) timer();
  s3 = powpolmod(&R, 2,pk,s1);
  if (mod4(N) == 3) s3 = _red(gmul(s0,s3), &R);

  if (DEBUGLEVEL) {sgt[pk]+=timer();ctsgt[pk]++;}
  etats = (GEN)tabeta[pk]; ind = pk;
  for (i=1; i<=pk; i++)
    if (gegal(s3,(GEN)etats[i])) { ind = i-1; break; }
  if (ind==pk) return -1;
  if ((ind&1)==0) return 0;
  else
  {
    if (DEBUGLEVEL) timer();
    s3 = powmodulo(stoi(q), shifti(N,-1), N);
    if (DEBUGLEVEL) {sgt[pk]+=timer();ctsgt[pk]++;}
    return is_m1(s3,N);
  }
}

/* p=2, k=1 */
static int
step4d(GEN N, ulong q)
{
  GEN s1;

  if (DEBUGLEVEL) timer();
  s1 = powmodulo(negi(stoi(q)), shifti(N,-1), N);
  if (DEBUGLEVEL) {sgt[2]+=timer();ctsgt[2]++;}
  if (gcmp1(s1)) return 0;
  if (is_m1(s1,N)) return (mod4(N) == 1);
  return -1;
}

static int
step5(GEN N, int p, GEN et)
{
  ulong qm3s2,ltabg,q,qp,x,av;
  int k,pk,fl=-1,i,qf;
  GEN ze8,tabf,tabg,ze,jpq=gun,j3q,j2q,vpk,v8;
  byteptr d=diffptr+1;

  ze8 = cyclo(8,0);
  v8 = cgetg(9,t_VECSMALL);
  av = avma; q = 2;
  while (*d && q<=10000)
  {
    avma = av; q += *d++;
    if (q%p == 1 && smodis(et,q))
    {
      if (smodis(N,q) == 0) return -1;
      k = 1; qp = (q-1)/p; pk = p;
      while (qp%p==0) { k++; pk *= p; qp /= p; }
      extendtabs(N,p,k);
      tabf = computetabdl(q);
      qm3s2 = (q-3)>>1;
      ltabg = (p==2 && k>=3)? q-2: qm3s2;
      tabg = cgetg(ltabg+1,t_VECSMALL);
      for (x=1; x<=ltabg; x++) tabg[x] = tabf[x] + tabf[q-x-1];

      vpk = cgetg(pk+1,t_VECSMALL); for (i=1; i<=pk; i++) vpk[i] = 0;
      ze = tabcyc[pk];
      if (p>=3 || k>=2)
      {
	for (x=1; x<=qm3s2; x++) vpk[ tabg[x]%pk + 1 ]++;
	for (x=1; x<=pk;    x++) vpk[x] <<= 1;
	vpk[ (2*tabf[qm3s2+1])%pk + 1 ]++;
	jpq = gmod(smallpolrev(vpk),ze);
      }
      if (p>=3) fl = step4a(N,p,k,jpq);
      else if (k>=3) /* p == 2 */
      {
        for (x=1; x<=pk; x++) vpk[x] = 0;
        for (x=1; x<=ltabg; x++) tabg[x] += tabf[x];

        for (x=1; x<=q-2; x++) vpk[ tabg[x]%pk + 1 ]++;
        j3q = gmod(gmul(jpq,gmod(smallpolrev(vpk),ze)),ze);
        if (mod8(N) >= 5)
        {
          for (x=1; x<=8; x++) v8[x] = 0;
          for (x=1; x<=q-2; x++) v8[ ((tabf[x]+tabg[x])&7) + 1 ]++;
          j2q = gmod(polinflate(gsqr(gmod(smallpolrev(v8),ze8)), pk>>3), ze);
        }
        else j2q = gun;
        fl = step4b(N,q,k,j2q,j3q);
      }
      else fl = (k==2)? step4c(N,q,jpq): step4d(N,q);
    }
    if (fl == -1) { qf = (int)(-q); return qf; }
    if (fl == 1) return 1;
  }
  return 0;
}

static GEN
step6(GEN N, ulong t, GEN et)
{
  GEN N1,r,p1;
  ulong i,av;

  if (DEBUGLEVEL) timer();
  N1 = modii(N, et);
  r = gun; av = avma;
  for (i=1; i<t; i++)
  {
    avma = av;
    r = modii(mulii(r,N1), et);
    if (!signe(modii(N,r)) && !gcmp1(r) && !egalii(r,N))
    {
      p1 = cgetg(3,t_VEC);
      p1[1] = (long)r;
      p1[2] = zero; return p1;
    }
  }
  if (DEBUGLEVEL) sgt6=timer();
  return gun;
}

GEN
aprcl(GEN N)
{
  GEN et,fat,flaglp,faq,faqpr,faqex,p1;
  long fl;
  ulong lfat,p,q,lfaq,k,t,i,j,l;
  ulong av, av0 = avma;

  if (cmpis(N,12)<=0)
  {
    if (tabfaux[itos(N)]) return gun;
    else
    {
      p1 = cgetg(3,t_VEC);
      p1[1] = zero;
      p1[2] = zero; return p1;
    }
  }
  if (DEBUGLEVEL) timer();
  t = compt(N);
  if (DEBUGLEVEL>=2) fprintferr("choosing t = %ld\n",t);
  et = e(t);
  if (cmpii(sqri(et),N) < 0) err(talker,"e(t) not large enough in aprcl");
  if (!gcmp1(mppgcd(N,mulsi(t,et))))
  {
    avma = av0; p1=cgetg(3,t_VEC);
    p1[1] = un;
    p1[2] = zero; return p1;
  }
  fat=calcglobs(N,t); lfat=lg(fat);
  flaglp = cgetg(itos((GEN)fat[lfat-1])+1, t_VECSMALL);
  for (i=2; i<lfat; i++)
  {
    p = itos((GEN)fat[i]);
    flaglp[p] = ! gcmp1(powmodulo(N,stoi(p-1),stoi(p*p)));
  }
  calcjac(et);
  if (DEBUGLEVEL) sgtjac=timer();
  if (DEBUGLEVEL>=3)
    fprintferr("Jacobi sums and tables computed in %ld ms\nq-values: ",sgtjac);
  sgtaut=0;
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
      if (p >= 3) fl = step4a(N,p,k,gmael(tabj,i,j));
      else
      {
	if (k >= 3) fl = step4b(N,q,k,(GEN)tabj2[i],(GEN)tabj3[i]);
	else
	{
	  if (k == 2) fl = step4c(N,q,gmael(tabj,i,1)); else fl = step4d(N,q);
	}
      }
      if (fl == -1)
      {
        avma = av0; p1 = cgetg(4,t_VEC);
        p1[1] = lstoi(q);
        p1[2] = lstoi(p);
        p1[3] = zero; return p1;
      }
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
     if (fl < 0)
     {
       avma = av0; p1=cgetg(4,t_VEC);
       p1[1] = lstoi(fl);
       p1[2] = lstoi(p);
       p1[3] = zero; return p1;
     }
     if (fl==1) continue;
     if (fl==0) err(talker,"aprcl test fails! this is highly improbable");
   }
 }
 if (DEBUGLEVEL>=3) fprintferr("conditions lp done, doing step6\n");
 return gerepilecopy(av0, step6(N,t,et));
}

/* si flag=0 retourne une reponse vrai/faux, sinon retourne des details
quand N non premier */

GEN
istrueprime(GEN N, int flag)
{
  GEN res;

  res=aprcl(N);
  if (gcmp1(res)) return gun;
  return flag ? res : gzero;
}
