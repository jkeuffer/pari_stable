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
/*         CLASS GROUP AND REGULATOR (McCURLEY, BUCHMANN)          */
/*                   QUADRATIC FIELDS                              */
/*                                                                 */
/*******************************************************************/
#include "pari.h"

const int narrow = 0; /* should set narrow = flag in buchquad, but buggy */

/* For largeprime() hashtable. Note that hashed pseudoprimes are odd (unless
 * 2 | index), hence the low order bit is not useful. So we hash
 * HASHBITS bits starting at bit 1, not bit 0 */
#define HASHBITS 10
const int HASHT = 1 << HASHBITS;

static long
hash(long q) { return (q & ((1 << (HASHBITS+1)) - 1)) >> 1; }
#undef HASHBITS

/* See buch2.c:
 * precision en digits decimaux=2*(#digits decimaux de Disc)+50
 * on prendra les p decomposes tels que prod(p)>lim dans la subFB
 * LIMC=Max(c.(log(Disc))^2,exp((1/8).sqrt(log(Disc).loglog(Disc))))
 * LIMC2=Max(6.(log(Disc))^2,exp((1/8).sqrt(log(Disc).loglog(Disc))))
 * subFB contient les indices des p decomposes tels que prod(p) > sqrt(Disc)
 * powsubFB est la table des puissances des formes dans subFB
 */

#define RANDOM_BITS 4
static const long CBUCH = (1<<RANDOM_BITS)-1;
static const long randshift=BITS_IN_RANDOM-1 - RANDOM_BITS;
#undef RANDOM_BITS

static long KC,KC2,limhash,RELSUP,PRECREG;
static long *primfact,*exprimfact,*badprim;
static long *FB,*numFB, **hashtab;
static GEN  powsubFB,vperm,subFB,Disc,sqrtD,isqrtD;

GEN buchquad(GEN D, double c, double c2, long RELSUP0, long flag, long prec);
extern GEN roots_to_pol_intern(GEN L, GEN a, long v, int plus);
extern GEN colreducemodHNF(GEN x, GEN y, GEN *Q);
extern GEN quadhilbertreal(GEN D, GEN flag, long prec);
extern void comp_gen(GEN z,GEN x,GEN y);
extern GEN codeform5(GEN x, long prec);
extern GEN comprealform5(GEN x, GEN y, GEN D, GEN sqrtD, GEN isqrtD);
extern GEN redrealform5(GEN x, GEN D, GEN sqrtD, GEN isqrtD);
extern GEN rhoreal_aux(GEN x, GEN D, GEN sqrtD, GEN isqrtD);
extern GEN cgetalloc(GEN x, size_t l, long t);

GEN
quadclassunit0(GEN x, long flag, GEN data, long prec)
{
  long lx,RELSUP0;
  double cbach, cbach2;

  if (!data) lx=1;
  else
  {
    lx = lg(data);
    if (typ(data)!=t_VEC || lx > 7)
      err(talker,"incorrect parameters in quadclassunit");
    if (lx > 4) lx = 4;
  }
  cbach = cbach2 = 0.1; RELSUP0 = 5;
  switch(lx)
  {
    case 4: RELSUP0 = itos((GEN)data[3]);
    case 3: cbach2 = gtodouble((GEN)data[2]);
    case 2: cbach  = gtodouble((GEN)data[1]);
  }
  return buchquad(x,cbach,cbach2,RELSUP0,flag,prec);
}

/*******************************************************************/
/*                                                                 */
/*       Hilbert and Ray Class field using CM (Schertz)            */
/*                                                                 */
/*******************************************************************/

int
isoforder2(GEN form)
{
  GEN a=(GEN)form[1],b=(GEN)form[2],c=(GEN)form[3];
  return !signe(b) || absi_equal(a,b) || egalii(a,c);
}

GEN
getallforms(GEN D, long *pth, GEN *ptz)
{
  long d = itos(D), t, b2, a, b, c, h, dover3 = labs(d)/3;
  GEN z, L=cgetg(labs(d), t_VEC);
  b2 = b = (d&1); h = 0; z=gun;
  while (b2 <= dover3)
  {
    t = (b2-d)/4;
    for (a=b?b:1; a*a<=t; a++)
      if (t%a == 0)
      {
	c = t/a; z = mulsi(a,z);
        L[++h] = (long)qfi(stoi(a),stoi(b),stoi(c));
	if (b && a != b && a*a != t)
          L[++h] = (long)qfi(stoi(a),stoi(-b),stoi(c));
      }
    b+=2; b2=b*b;
  }
  *pth = h; *ptz = z; setlg(L,h+1); return L;
}

#define MOD4(x) ((((GEN)x)[2])&3)
#define MAXL 300
/* find P and Q two non principal prime ideals (above p,q) such that
 *   (pq, z) = 1  [coprime to all class group representatives]
 *   cl(P) = cl(Q) if P has order 2 in Cl(K)
 * Try to have e = 24 / gcd(24, (p-1)(q-1)) as small as possible */
void
get_pq(GEN D, GEN z, GEN flag, GEN *ptp, GEN *ptq)
{
  GEN wp=cgetg(MAXL,t_VEC), wlf=cgetg(MAXL,t_VEC), court=icopy(gun);
  GEN p, form;
  long i, ell, l = 1, d = itos(D);
  byteptr diffell = diffptr + 2;

  if (typ(flag)==t_VEC)
  { /* assume flag = [p,q]. Check nevertheless */
    for (i=1; i<lg(flag); i++)
    {
      ell = itos((GEN)flag[i]);
      if (smodis(z,ell) && kross(d,ell) > 0)
      {
	form = redimag(primeform(D,(GEN)flag[i],0));
	if (!gcmp1((GEN)form[1])) {
	  wp[l]  = flag[i];
          l++; if (l == 3) break;
	}
      }
    }
    if (l<3) err(talker,"[quadhilbert] incorrect values in flag: %Z", flag);
    *ptp = (GEN)wp[1];
    *ptq = (GEN)wp[2]; return;
  }

  ell = 3;
  while (l < 3 || ell<=MAXL)
  {
    NEXT_PRIME_VIADIFF_CHECK(ell, diffell);
    if (smodis(z,ell) && kross(d,ell) > 0)
    {
      court[2]=ell; form = redimag(primeform(D,court,0));
      if (!gcmp1((GEN)form[1])) {
        wp[l]  = licopy(court);
        wlf[l] = (long)form; l++;
      }
    }
  }
  setlg(wp,l); setlg(wlf,l);

  for (i=1; i<l; i++)
    if (smodis((GEN)wp[i],3) == 1) break;
  if (i==l) i = 1;
  p = (GEN)wp[i]; form = (GEN)wlf[i];
  i = l;
  if (isoforder2(form))
  {
    long oki = 0;
    for (i=1; i<l; i++)
      if (gegal((GEN)wlf[i],form))
      {
        if (MOD4(p) == 1 || MOD4(wp[i]) == 1) break;
        if (!oki) oki = i; /* not too bad, still e = 2 */
      }
    if (i==l) i = oki;
    if (!i) err(bugparier,"quadhilbertimag (can't find p,q)");
  }
  else
  {
    if (MOD4(p) == 3)
    {
      for (i=1; i<l; i++)
        if (MOD4(wp[i]) == 1) break;
    }
    if (i==l) i = 1;
  }
  *ptp = p;
  *ptq = (GEN)wp[i];
}
#undef MAXL

static GEN
gpq(GEN form, GEN p, GEN q, long e, GEN sqd, GEN u, long prec)
{
  GEN a2 = shifti((GEN)form[1], 1);
  GEN b = (GEN)form[2], p1,p2,p3,p4;
  GEN w = lift(chinois(gmodulcp(negi(b),a2), u));
  GEN al = cgetg(3,t_COMPLEX);
  al[1] = lneg(gdiv(w,a2));
  al[2] = ldiv(sqd,a2);
  p1 = trueeta(gdiv(al,p),prec);
  p2 = egalii(p,q)? p1: trueeta(gdiv(al,q),prec);
  p3 = trueeta(gdiv(al,mulii(p,q)),prec);
  p4 = trueeta(al,prec);
  return gpowgs(gdiv(gmul(p1,p2),gmul(p3,p4)), e);
}

/* returns an equation for the Hilbert class field of the imaginary
 *  quadratic field of discriminant D if flag=0, a vector of
 *  two-component vectors [form,g(form)] where g() is the root of the equation
 *  if flag is non-zero.
 */
static GEN
quadhilbertimag(GEN D, GEN flag)
{
  long h, i, e, prec;
  gpmem_t av=avma;
  GEN z,L,P,p,q,qfp,qfq,up,uq,u;
  int raw = ((typ(flag)==t_INT && signe(flag)));

  if (DEBUGLEVEL>=2) (void)timer2();
  if (gcmpgs(D,-11) >= 0) return polx[0];
  L = getallforms(D,&h,&z);
  if (DEBUGLEVEL>=2) msgtimer("class number = %ld",h);
  if (h == 1) { avma=av; return polx[0]; }

  get_pq(D, z, flag, &p, &q);
  e = 24 / cgcd((smodis(p,24)-1) * (smodis(q,24)-1), 24);
  if(DEBUGLEVEL>=2) fprintferr("p = %Z, q = %Z, e = %ld\n",p,q,e);
  qfp = primeform(D,p,0); up = gmodulcp((GEN)qfp[2],shifti(p,1));
  if (egalii(p,q))
  {
    u = (GEN)compimagraw(qfp,qfp)[2];
    u = gmodulcp(u, shifti(mulii(p,q),1));
  }
  else
  {
    qfq = primeform(D,q,0); uq = gmodulcp((GEN)qfq[2],shifti(q,1));
    u = chinois(up,uq);
  }
  prec = raw? DEFAULTPREC: 3;
  for(;;)
  {
    long ex, exmax = 0;
    gpmem_t av0 = avma;
    GEN lead, sqd = gsqrt(negi(D),prec);
    P = cgetg(h+1,t_VEC);
    for (i=1; i<=h; i++)
    {
      GEN v, s = gpq((GEN)L[i], p, q, e, sqd, u, prec);
      if (raw)
      {
        v = cgetg(3,t_VEC); P[i] = (long)v;
        v[1] = L[i];
        v[2] = (long)s;
      }
      else P[i] = (long)s;
      ex = gexpo(s); if (ex > 0) exmax += ex;
    }
    if (DEBUGLEVEL>=2) msgtimer("roots");
    if (raw) { P = gcopy(P); break; }
    /* to avoid integer overflow (1 + 0.) */
    lead = (exmax < bit_accuracy(prec))? gun: realun(prec);

    P = greal(roots_to_pol_intern(lead,P,0,0));
    P = grndtoi(P,&exmax);
    if (DEBUGLEVEL>=2) msgtimer("product, error bits = %ld",exmax);
    if (exmax <= -10)
    {
      if (typ(flag)==t_VEC && !issquarefree(P)) { avma=av; return gzero; }
      break;
    }
    avma = av0; prec += (DEFAULTPREC-2) + (1 + (exmax >> TWOPOTBITS_IN_LONG));
    if (DEBUGLEVEL) err(warnprec,"quadhilbertimag",prec);
  }
  return gerepileupto(av,P);
}

GEN
quadhilbert(GEN D, GEN flag, long prec)
{
  if (!flag) flag = gzero;
  if (typ(D)!=t_INT)
  {
    D = checkbnf(D);
    if (degpol(gmael(D,7,1)) != 2)
      err(talker,"not a polynomial of degree 2 in quadhilbert");
    D=gmael(D,7,3);
  }
  else
  {
    if (!isfundamental(D))
      err(talker,"quadhilbert needs a fundamental discriminant");
  }
  return (signe(D)>0)? quadhilbertreal(D,flag,prec)
                     : quadhilbertimag(D,flag);
}

/* AUXILLIARY ROUTINES FOR QUADRAYIMAGWEI */
#define to_approx(nf,a) ((GEN)gmul(gmael((nf),5,1), (a))[1])

/* Z-basis for a (over C) */
static GEN
get_om(GEN nf, GEN a)
{
  GEN om = cgetg(3,t_VEC);
  om[1] = (long)to_approx(nf,(GEN)a[2]);
  om[2] = (long)to_approx(nf,(GEN)a[1]);
  return om;
}

/* Compute all elts in class group G = [|G|,c,g], c=cyclic factors, g=gens.
 * Set list[j + 1] = g1^e1...gk^ek where j is the integer
 *   ek + ck [ e(k-1) + c(k-1) [... + c2 [e1]]...] */
static GEN
getallelts(GEN bnr)
{
  GEN nf,G,C,c,g, *list, **pows, *gk;
  long lc,i,j,k,no;

  nf = checknf(bnr);
  G = (GEN)bnr[5];

  no = itos((GEN)G[1]);
  c = (GEN)G[2];
  g = (GEN)G[3]; lc = lg(c)-1;
  list = (GEN*) cgetg(no+1,t_VEC);
  if (!lc)
  {
    list[1] = idealhermite(nf,gun);
    return (GEN)list;
  }
  pows = (GEN**)cgetg(lc+1,t_VEC);
  c = dummycopy(c); settyp(c, t_VECSMALL);
  for (i=1; i<=lc; i++)
  {
    c[i] = k = itos((GEN)c[i]);
    gk = (GEN*)cgetg(k, t_VEC); gk[1] = (GEN)g[i];
    for (j=2; j<k; j++)
      gk[j] = idealmodidele(bnr, idealmul(nf, gk[j-1], gk[1]));
    pows[i] = gk; /* powers of g[i] */
  }

  C = cgetg(lc+1, t_VECSMALL); C[1] = c[lc];
  for (i=2; i<=lc; i++) C[i] = C[i-1] * c[lc-i+1];
  /* C[i] = c(k-i+1) * ... * ck */
  /* j < C[i+1] <==> j only involves g(k-i)...gk */
  i = 1; list[1] = 0; /* dummy */
  for (j=1; j < C[1]; j++)
    list[j + 1] = pows[lc][j];
  for (   ; j<no; j++)
  {
    GEN p1,p2;
    if (j == C[i+1]) i++;
    p2 = pows[lc-i][j/C[i]];
    p1 = list[j%C[i] + 1];
    if (p1) p2 = idealmodidele(bnr, idealmul(nf,p2,p1));
    list[j + 1] = p2;
  }
  list[1] = idealhermite(nf,gun);
  return (GEN)list;
}

/* x quadratic integer (approximate), recognize it. If error return NULL */
static GEN
findbezk(GEN nf, GEN x)
{
  GEN a,b, M = gmael(nf,5,1), y = cgetg(3, t_COL), u = gcoeff(M,1,2);
  long ea,eb;

  b = grndtoi(gdiv(gimag(x), gimag(u)), &eb);
  a = grndtoi(greal(gsub(x, gmul(b,u))),&ea);
  if (ea>-20 || eb>-20) return NULL;
  if (!signe(b)) return a;
  y[1] = (long)a;
  y[2] = (long)b; return basistoalg(nf,y);
}

static GEN
findbezk_pol(GEN nf, GEN x)
{
  long i, lx = lgef(x);
  GEN y = cgetg(lx,t_POL);
  for (i=2; i<lx; i++)
    if (! (y[i] = (long)findbezk(nf,(GEN)x[i])) ) return NULL;
  y[1] = x[1]; return y;
}

GEN
form_to_ideal(GEN x)
{
  long tx = typ(x);
  GEN b,c, y = cgetg(3, t_MAT);
  if (tx != t_QFR && tx != t_QFI) err(typeer,"form_to_ideal");
  c = cgetg(3,t_COL); y[1] = (long)c;
  c[1] = x[1]; c[2] = zero;
  c = cgetg(3,t_COL); y[2] = (long)c;
  b = negi((GEN)x[2]);
  if (mpodd(b)) b = addis(b,1);
  c[1] = lshifti(b,-1); c[2] = un; return y;
}

/* P as output by quadhilbertimag, convert forms to ideals */
static void
convert_to_id(GEN P)
{
  long i,l = lg(P);
  for (i=1; i<l; i++)
  {
    GEN p1 = (GEN)P[i];
    p1[1] = (long)form_to_ideal((GEN)p1[1]);
  }
}

/* P approximation computed at initial precision prec. Compute needed prec
 * to know P with 1 word worth of trailing decimals */
static long
get_prec(GEN P, long prec)
{
  long k = gprecision(P);
  if (k == 3) return (prec<<1)-2; /* approximation not trustworthy */
  k = prec - k; /* lost precision when computing P */
  if (k < 0) k = 0;
  k += MEDDEFAULTPREC + (gexpo(P) >> TWOPOTBITS_IN_LONG);
  if (k <= prec) k = (prec<<1)-2; /* dubious: old prec should have worked */
  return k;
}

/* AUXILLIARY ROUTINES FOR QUADRAYSIGMA */

/* Compute data for ellphist */
static GEN
ellphistinit(GEN om, long prec)
{
  GEN p1,res,om1b,om2b, om1 = (GEN)om[1], om2 = (GEN)om[2];

  if (gsigne(gimag(gdiv(om1,om2))) < 0)
  {
    p1 = om1; om1 = om2; om2 = p1;
    om = cgetg(3,t_VEC);
    om[1] = (long)om1;
    om[2] = (long)om2;
  }
  om1b = gconj(om1);
  om2b = gconj(om2); res = cgetg(4,t_VEC);
  res[1] = ldivgs(elleisnum(om,2,0,prec),12);
  res[2] = ldiv(PiI2(prec), gmul(om2, gimag(gmul(om1b,om2))));
  res[3] = (long)om2b; return res;
}

/* Computes log(phi^*(z,om)), using res computed by ellphistinit */
static GEN
ellphist(GEN om, GEN res, GEN z, long prec)
{
  GEN u = gimag(gmul(z, (GEN)res[3]));
  GEN zst = gsub(gmul(u, (GEN)res[2]), gmul(z,(GEN)res[1]));
  return gsub(ellsigma(om,z,1,prec),gmul2n(gmul(z,zst),-1));
}

/* Computes phi^*(la,om)/phi^*(1,om) where (1,om) is an oriented basis of the
   ideal gf*gc^{-1} */
static GEN
computeth2(GEN om, GEN la, long prec)
{
  GEN p1,p2,res = ellphistinit(om,prec);

  p1 = gsub(ellphist(om,res,la,prec), ellphist(om,res,gun,prec));
  p2 = gimag(p1);
  if (gexpo(greal(p1))>20 || gexpo(p2)> bit_accuracy(min(prec,lg(p2)))-10)
    return NULL;
  return gexp(p1,prec);
}

/* Computes P_2(X)=polynomial in Z_K[X] closest to prod_gc(X-th2(gc)) where
   the product is over the ray class group bnr.*/
static GEN
computeP2(GEN bnr, GEN la, int raw, long prec)
{
  long clrayno, i, first = 1;
  gpmem_t av=avma, av2;
  GEN listray,P0,P,f,lanum, nf = checknf(bnr);

  f = gmael3(bnr,2,1,1);
  if (typ(la) != t_COL) la = algtobasis(nf,la);
  listray = getallelts(bnr);
  clrayno = lg(listray)-1; av2 = avma;
PRECPB:
  if (!first)
  {
    if (DEBUGLEVEL) err(warnprec,"computeP2",prec);
    nf = gerepileupto(av2, nfnewprec(checknf(bnr),prec));
  }
  first = 0; lanum = to_approx(nf,la);
  P = cgetg(clrayno+1,t_VEC);
  for (i=1; i<=clrayno; i++)
  {
    GEN om = get_om(nf, idealdiv(nf,f,(GEN)listray[i]));
    GEN v, s = computeth2(om,lanum,prec);
    if (!s) { prec = (prec<<1)-2; goto PRECPB; }
    if (raw)
    {
      v = cgetg(3,t_VEC); P[i] = (long)v;
      v[1] = (long)listray[i];
      v[2] = (long)s;
    }
    else P[i] = (long)s;
  }
  if (!raw)
  {
    P0 = roots_to_pol(P, 0);
    P = findbezk_pol(nf, P0);
    if (!P) { prec = get_prec(P0, prec); goto PRECPB; }
  }
  return gerepilecopy(av, P);
}

#define nexta(a) (a>0 ? -a : 1-a)
static GEN
do_compo(GEN x, GEN y)
{
  long a, ph = degpol(y);
  GEN z;
  y = gmul(gpowgs(polx[0],ph), gsubst(y,0,gdiv(polx[MAXVARN],polx[0])));
  for  (a = 0;; a = nexta(a))
  {
    if (a) x = gsubst(x, 0, gaddsg(a, polx[0]));
    z = subres(x,y);
    z = gsubst(z, MAXVARN, polx[0]);
    if (issquarefree(z)) return z;
  }
}
#undef nexta

static GEN
galoisapplypol(GEN nf, GEN s, GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx,t_POL);

  for (i=2; i<lx; i++) y[i] = (long)galoisapply(nf,s,(GEN)x[i]);
  y[1] = x[1]; return y;
}

/* x quadratic, write it as ua + v, u,v rational */
static GEN
findquad(GEN a, GEN x, GEN p)
{
  long tu, tv;
  gpmem_t av = avma;
  GEN u,v;
  if (typ(x) == t_POLMOD) x = (GEN)x[2];
  if (typ(a) == t_POLMOD) a = (GEN)a[2];
  u = poldivres(x, a, &v);
  u = simplify(u); tu = typ(u);
  v = simplify(v); tv = typ(v);
  if (!is_scalar_t(tu) || !is_scalar_t(tv))
    err(talker, "incorrect data in findquad");
  x = v;
  if (!gcmp0(u)) x = gadd(gmul(u, polx[varn(a)]), x);
  if (typ(x) == t_POL) x = gmodulcp(x,p);
  return gerepileupto(av, x);
}

static GEN
findquad_pol(GEN nf, GEN a, GEN x)
{
  long i, lx = lg(x);
  GEN p = (GEN)nf[1], y = cgetg(lx,t_POL);
  for (i=2; i<lx; i++) y[i] = (long)findquad(a, (GEN)x[i], p);
  y[1] = x[1]; return y;
}

static GEN
compocyclo(GEN nf, long m, long d, long prec)
{
  GEN sb,a,b,s,p1,p2,p3,res,polL,polLK,nfL, D = (GEN)nf[3];
  long ell,vx;

  p1 = quadhilbertimag(D, gzero);
  p2 = cyclo(m,0);
  if (d==1) return do_compo(p1,p2);

  ell = m&1 ? m : (m>>2);
  if (!cmpsi(-ell,D)) /* ell = |D| */
  {
    p2 = gcoeff(nffactor(nf,p2),1,1);
    return do_compo(p1,p2);
  }
  if (ell%4 == 3) ell = -ell;
  /* nf = K = Q(a), L = K(b) quadratic extension = Q(t) */
  polLK = quadpoly(stoi(ell)); /* relative polynomial */
  res = rnfequation2(nf, polLK);
  vx = varn(nf[1]);
  polL = gsubst((GEN)res[1],0,polx[vx]); /* = charpoly(t) */
  a = gsubst(lift((GEN)res[2]), 0,polx[vx]);
  b = gsub(polx[vx], gmul((GEN)res[3], a));
  nfL = initalg(polL,prec);
  p1 = gcoeff(nffactor(nfL,p1),1,1);
  p2 = gcoeff(nffactor(nfL,p2),1,1);
  p3 = do_compo(p1,p2); /* relative equation over L */
  /* compute non trivial s in Gal(L / K) */
  sb= gneg(gadd(b, truecoeff(polLK,1))); /* s(b) = Tr(b) - b */
  s = gadd(polx[vx], gsub(sb, b)); /* s(t) = t + s(b) - b */
  p3 = gmul(p3, galoisapplypol(nfL, s, p3));
  return findquad_pol(nf, a, p3);
}

/* I integral ideal in HNF. (x) = I, x small in Z ? */
static long
isZ(GEN I)
{
  GEN x = gcoeff(I,1,1);
  if (signe(gcoeff(I,1,2)) || !egalii(x, gcoeff(I,2,2))) return 0;
  return is_bigint(x)? -1: itos(x);
}

/* Treat special cases directly. return NULL if not special case */
static GEN
treatspecialsigma(GEN nf, GEN gf, int raw, long prec)
{
  GEN p1,p2,tryf, D = (GEN)nf[3];
  long Ds,fl,i;

  if (raw)
    err(talker,"special case in Schertz's theorem. Odd flag meaningless");
  i = isZ(gf);
  if (cmpis(D,-3)==0)
  {
    if (i == 4 || i == 5 || i == 7) return cyclo(i,0);
    if (cmpis(gcoeff(gf,1,1), 9) || cmpis(content(gf),3)) return NULL;
    p1 = (GEN)nfroots(nf,cyclo(3,0))[1]; /* f = P_3^3 */
    return gadd(gpowgs(polx[0],3), p1); /* x^3+j */
  }
  if (cmpis(D,-4)==0)
  {
    if (i == 3 || i == 5) return cyclo(i,0);
    if (i != 4) return NULL;
    p1 = (GEN)nfroots(nf,cyclo(4,0))[1];
    return gadd(gpowgs(polx[0],2), p1); /* x^2+i */
  }
  Ds = smodis(D,48);
  if (i)
  {
    if (i==2 && Ds%16== 8) return compocyclo(nf, 4,1,prec);
    if (i==3 && Ds% 3== 1) return compocyclo(nf, 3,1,prec);
    if (i==4 && Ds% 8== 1) return compocyclo(nf, 4,1,prec);
    if (i==6 && Ds   ==40) return compocyclo(nf,12,1,prec);
    return NULL;
  }

  p1 = gcoeff(gf,1,1); /* integer > 0 */
  p2 = gcoeff(gf,2,2);
  if (gcmp1(p2)) { fl = 0; tryf = p1; }
  else {
    if (Ds % 16 != 8 || !egalii(content(gf),gdeux)) return NULL;
    fl = 1; tryf = shifti(p1,-1);
  }
  /* tryf integer > 0 */
  if (cmpis(tryf, 3) <= 0 || signe(resii(D, tryf)) || !isprime(tryf))
    return NULL;

  i = itos(tryf); if (fl) i *= 4;
  return compocyclo(nf,i,2,prec);
}

static GEN
getallrootsof1(GEN bnf)
{
  GEN z, u, nf = checknf(bnf), racunit = gmael3(bnf,8,4,2);
  long i, n = itos(gmael3(bnf,8,4,1));

  u = cgetg(n+1, t_VEC);
  z = basistoalg(nf, racunit);
  for (i=1; ; i++)
  {
    u[i] = (long)algtobasis(nf,z);
    if (i == n) return u;
    z = gmul(z, racunit);
  }
}

/* Compute ray class field polynomial using sigma; if raw=1, pairs
   [ideals,roots] are given instead so that congruence subgroups can be used */
static GEN
quadrayimagsigma(GEN bnr, int raw, long prec)
{
  GEN allf,bnf,nf,pol,w,f,la,P,labas,lamodf,u;
  long a,b,f2,i,lu;

  allf = conductor(bnr,gzero,2); bnr = (GEN)allf[2];
  f = gmael(allf,1,1);
  bnf= (GEN)bnr[1];
  nf = (GEN)bnf[7];
  pol= (GEN)nf[1];
  if (gcmp1(gcoeff(f,1,1))) /* f = 1 ? */
  {
    P = quadhilbertimag((GEN)nf[3], stoi(raw));
    if (raw) convert_to_id(P);
    return gcopy(P);
  }
  P = treatspecialsigma(nf,f,raw,prec);
  if (P) return P;

  w = gmodulcp(polx[varn(pol)], pol);
  f2 = 2 * itos(gcoeff(f,1,1));
  u = getallrootsof1(bnf); lu = lg(u);
  for (i=1; i<lu; i++)
    u[i] = (long)colreducemodHNF((GEN)u[i], f, NULL); /* roots of 1, mod f */
  if (DEBUGLEVEL>1)
    fprintferr("quadray: looking for [a,b] != unit mod 2f\n[a,b] = ");
  for (a=0; a<f2; a++)
    for (b=0; b<f2; b++)
    {
      la = gaddgs(gmulsg(a,w),b);
      if (smodis(gnorm(la), f2) != 1) continue;
      if (DEBUGLEVEL>1) fprintferr("[%ld,%ld] ",a,b);

      labas = algtobasis(nf, la);
      lamodf = colreducemodHNF(labas, f, NULL);
      for (i=1; i<lu; i++)
        if (gegal(lamodf, (GEN)u[i])) break;
      if (i < lu) continue; /* la = unit mod f */
      if (DEBUGLEVEL)
      {
        if (DEBUGLEVEL>1) fprintferr("\n");
        fprintferr("lambda = %Z\n",la);
      }
      return computeP2(bnr,labas,raw,prec);
    }
  err(bugparier,"quadrayimagsigma");
  return NULL;
}

GEN
quadray(GEN D, GEN f, GEN flag, long prec)
{
  GEN bnr,y,p1,pol,bnf,lambda;
  long raw;
  gpmem_t av = avma;

  if (!flag) flag = gzero;
  if (typ(flag)==t_INT) lambda = NULL;
  else
  {
    if (typ(flag)!=t_VEC || lg(flag)!=3) err(flagerr,"quadray");
    lambda = (GEN)flag[1]; flag = (GEN)flag[2];
    if (typ(flag)!=t_INT) err(flagerr,"quadray");
  }
  if (typ(D)!=t_INT)
  {
    bnf = checkbnf(D);
    if (degpol(gmael(bnf,7,1)) != 2)
      err(talker,"not a polynomial of degree 2 in quadray");
    D=gmael(bnf,7,3);
  }
  else
  {
    if (!isfundamental(D))
      err(talker,"quadray needs a fundamental discriminant");
    pol = quadpoly(D); setvarn(pol, fetch_user_var("y"));
    bnf = bnfinit0(pol,signe(D)>0?1:0,NULL,prec);
  }
  raw = (mpodd(flag) && signe(D) < 0);
  bnr = bnrinit0(bnf,f,1);
  if (gcmp1(gmael(bnr,5,1)))
  {
    avma = av; if (!raw) return polx[0];
    y = cgetg(2,t_VEC); p1 = cgetg(3,t_VEC); y[1] = (long)p1;
    p1[1]=(long)idmat(2);
    p1[2]=(long)polx[0]; return y;
  }
  if (signe(D) > 0)
    y = bnrstark(bnr,gzero, gcmp0(flag)?1:5, prec);
  else
  {
    if (lambda)
      y = computeP2(bnr,lambda,raw,prec);
    else
      y = quadrayimagsigma(bnr,raw,prec);
  }
  return gerepileupto(av, y);
}

/*******************************************************************/
/*                                                                 */
/*  Routines related to binary quadratic forms (for internal use)  */
/*                                                                 */
/*******************************************************************/
#define rhorealform(x) rhoreal_aux(x,Disc,sqrtD,isqrtD)
#define redrealform(x) gcopy(fix_signs(redrealform5(x,Disc,sqrtD,isqrtD)))

static GEN
fix_signs(GEN x)
{
  GEN a = (GEN)x[1];
  GEN c = (GEN)x[3];
  if (signe(a) < 0)
  {
    if (narrow || absi_equal(a,c)) return rhorealform(x);
    setsigne(a,1); setsigne(c,-1);
  }
  return x;
}

static GEN
comprealform(GEN x,GEN y) {
  return fix_signs( comprealform5(x,y,Disc,sqrtD,isqrtD) );
}

/* compute rho^n(x) */
static GEN
rhoreal_pow(GEN x, long n)
{
  long i;
  gpmem_t av = avma, lim = stack_lim(av, 1);
  for (i=1; i<=n; i++)
  {
    x = rhorealform(x);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"rhoreal_pow");
      x = gerepilecopy(av, x);
    }
  }
  return gerepilecopy(av, x);
}

static GEN
realpf5(GEN D, long p)
{
  gpmem_t av = avma;
  GEN y = primeform(D,stoi(p),PRECREG);
  y = codeform5(y,PRECREG);
  return gerepileupto(av, redrealform(y));
}

static GEN
realpf(GEN D, long p)
{
  gpmem_t av = avma;
  GEN y = primeform(D,stoi(p),PRECREG);
  return gerepileupto(av, redrealform(y));
}

static GEN
imagpf(GEN D, long p) { return primeform(D,stoi(p),0); }

static GEN
comprealform3(GEN x, GEN y)
{
  gpmem_t av = avma;
  GEN z = cgetg(4,t_VEC); comp_gen(z,x,y);
  return gerepileupto(av, redrealform(z));
}

/* Warning: ex[0] not set */
static GEN
init_form(long *ex, GEN (*comp)(GEN,GEN))
{
  long i, l = lg(powsubFB);
  GEN F = NULL;
  for (i=1; i<l; i++)
    if (ex[i])
    {
      GEN t = gmael(powsubFB,i,ex[i]);
      F = F? comp(F,t): t;
    }
  return F;
}
static GEN
initrealform5(long *ex) { return init_form(ex, &comprealform); }
static GEN
initimagform(long *ex) { return init_form(ex, &compimag); }

static GEN
random_form(GEN ex, GEN (*comp)(GEN,GEN))
{
  long i, l = lg(ex);
  gpmem_t av = avma;
  GEN F;
  for(;;)
  {
    for (i=1; i<l; i++) ex[i] = mymyrand()>>randshift;
    if ((F = init_form(ex, comp))) return F;
    avma = av;
  }
}

static GEN
real_random_form(GEN ex) { return random_form(ex, &comprealform3); }
static GEN
imag_random_form(GEN ex) { return random_form(ex, &compimag); }

/*******************************************************************/
/*                                                                 */
/*                     Common subroutines                          */
/*                                                                 */
/*******************************************************************/
static void
buch_init(void)
{
  if (DEBUGLEVEL) (void)timer2();
  primfact  = new_chunk(100);
  exprimfact  = new_chunk(100);
  badprim = new_chunk(100);
  hashtab = (long**) new_chunk(HASHT);
}

double
check_bach(double cbach, double B)
{
  if (cbach >= B)
   err(talker,"sorry, buchxxx couldn't deal with this field PLEASE REPORT!");
  cbach *= 2; if (cbach > B) cbach = B;
  if (DEBUGLEVEL) fprintferr("\n*** Bach constant: %f\n", cbach);
  return cbach;
}

static long
factorquad(GEN f, long kcz, long limp)
{
  long i, p, k, lo;
  gpmem_t av;
  GEN q,r, x = (GEN)f[1];

  if (is_pm1(x)) { primfact[0]=0; return 1; }
  av=avma; lo=0;
  if (signe(x) < 0) x = absi(x);
  for (i=1; ; i++)
  {
    p=FB[i]; q=dvmdis(x,p,&r);
    if (!signe(r))
    {
      for (k=0; !signe(r); k++) { x=q; q=dvmdis(x,p,&r); }
      primfact[++lo]=p; exprimfact[lo]=k;
    }
    if (cmpis(q,p)<=0) break;
    if (i==kcz) { avma=av; return 0; }
  }
  avma=av;
  if (lgefint(x)!=3 || (p=x[2]) > limhash) return 0;

  if (p != 1 && p <= limp)
  {
    for (i=1; i<=badprim[0]; i++)
      if (p % badprim[i] == 0) return 0;
    primfact[++lo]=p; exprimfact[lo]=1;
    p = 1;
  }
  primfact[0]=lo; return p;
}

/* q may not be prime, but check for a "large prime relation" involving q */
static long *
largeprime(long q, long *ex, long np, long nrho)
{
  const long hashv = hash(q);
  long *pt, i, l = lg(subFB);

  for (pt = hashtab[hashv]; ; pt = (long*) pt[0])
  {
    if (!pt)
    {
      pt = (long*) gpmalloc((l+3)<<TWOPOTBYTES_IN_LONG);
      *pt++ = nrho; /* nrho = pt[-3] */
      *pt++ = np;   /* np   = pt[-2] */
      *pt++ = q;    /* q    = pt[-1] */
      pt[0] = (long)hashtab[hashv];
      for (i=1; i<l; i++) pt[i]=ex[i];
      hashtab[hashv]=pt; return NULL;
    }
    if (pt[-1] == q) break;
  }
  for(i=1; i<l; i++)
    if (pt[i] != ex[i]) return pt;
  return (pt[-2]==np)? (GEN)NULL: pt;
}

/* p | conductor of order of disc D ? */
static int
is_bad(GEN D, ulong p)
{
  gpmem_t av = avma;
  int r;
  if (p == 2)
  {
    r = mod16(D) >> 1;
    if (r && signe(D) < 0) r = 8-r;
    return (r < 4);
  }
  r = (resii(D, muluu(p,p)) == gzero); /* p^2 | D ? */
  avma = av; return r;
}

/* create FB, numFB; fill badprim. Return L(kro_D, 1) */
static GEN
FBquad(GEN Disc, long n2, long n)
{
  GEN Res = realun(DEFAULTPREC);
  long i, p, bad, s;
  gpmem_t av;
  byteptr d = diffptr;

  numFB = cgetg(n2+1, t_VECSMALL);
  FB    = cgetg(n2+1, t_VECSMALL);
  av = avma;
  KC = 0; bad = 0; i = 0;
  maxprime_check((ulong)n2);
  for (p = 0;;) /* p <= n2 */
  {
    NEXT_PRIME_VIADIFF(p, d);
    if (!KC && p > n) KC = i;
    if (p > n2) break;
    s = krogs(Disc,p);
    switch (s)
    {
      case -1: break; /* inert */
      case  0: /* ramified */
        if (is_bad(Disc, (ulong)p)) { badprim[++bad]=p; break; }
        /* fall through */
      default:  /* split */
        i++; numFB[p]=i; FB[i] = p; break;
    }
    Res = mulsr(p, divrs(Res, p - s));
  }
  if (!KC) return NULL;
  Res = gerepileupto(av, Res);
  KC2 = i;
  setlg(FB, KC2+1);
  if (DEBUGLEVEL)
  {
    msgtimer("factor base");
    if (DEBUGLEVEL>7)
    {
      fprintferr("FB:\n");
      for (i=1; i<=KC; i++) fprintferr("%ld ", FB[i]);
      fprintferr("\n");
    }
  }
  badprim[0] = bad; return Res;
}

/* create vperm, return subFB */
static GEN
subFBquad(GEN D, double PROD, long KC)
{
  long i, j, lgsub, ino, lv = KC+1;
  double prod = 1.;
  gpmem_t av;
  GEN no;

  vperm = cgetg(lv, t_VECSMALL);
  av = avma;
  no    = cgetg(lv, t_VECSMALL); ino = 1;
  for (i=j=1; j < lv; j++)
  {
    long p = FB[j];
    if (smodis(D, p) == 0) no[ino++] = j; /* ramified */
    else
    {
      vperm[i] = j; i++;
      prod *= p;
      if (prod > PROD) break;
    }
  }
  if (j == lv) return NULL;
  lgsub = i;
  for (j = 1; j <ino; i++,j++) vperm[i] = no[j];
  for (     ; i < lv; i++)     vperm[i] = i;
  avma = av;
  if (DEBUGLEVEL) msgtimer("subFBquad (%ld elt.)", lgsub-1);
  return vecextract_i(vperm, 1, lgsub-1);
}

/* assume n >= 1, x[i][j] = subFB[i]^j, for j = 1..n */
static GEN
powsubFBquad(long n)
{
  long i,j, l = lg(subFB);
  GEN F, y, x = cgetg(l, t_VEC);

  if (PRECREG) /* real */
  {
    for (i=1; i<l; i++)
    {
      F = realpf5(Disc, FB[subFB[i]]);
      y = cgetg(n+1, t_VEC); x[i] = (long)y;
      y[1] = (long)F;
      for (j=2; j<=n; j++) y[j] = (long)comprealform((GEN)y[j-1], F);
    }
  }
  else /* imaginary */
  {
    for (i=1; i<l; i++)
    {
      F = imagpf(Disc, FB[subFB[i]]);
      y = cgetg(n+1, t_VEC); x[i] = (long)y;
      y[1] = (long)F;
      for (j=2; j<=n; j++) y[j] = (long)compimag((GEN)y[j-1], F);
    }
  }
  if (DEBUGLEVEL) msgtimer("powsubFBquad");
  return x;
}

static void
desalloc(long **mat)
{
  long i,*p,*q;
  for (i=1; i<lg(mat); i++) free(mat[i]);
  free(mat);
  for (i=1; i<HASHT; i++)
    for (p = hashtab[i]; p; p = q) { q=(long*)p[0]; free(p-3); }
}

static void
sub_fact(GEN col, GEN F)
{
  GEN b = (GEN)F[2];
  long i, p, e;
  for (i=1; i<=primfact[0]; i++)
  {
    p = primfact[i]; e = exprimfact[i];
    if (smodis(b, p<<1) > p) e = -e;
    col[numFB[p]] -= e;
  }
}
static void
add_fact(GEN col, GEN F)
{
  GEN b = (GEN)F[2];
  long i, p, e;
  for (i=1; i<=primfact[0]; i++)
  {
    p = primfact[i]; e = exprimfact[i];
    if (smodis(b, p<<1) > p) e = -e;
    col[numFB[p]] += e;
  }
}

#define comp(x,y) x? (PRECREG? compreal(x,y): compimag(x,y)): y
static GEN
get_clgp(GEN Disc, GEN W, GEN *ptmet, long prec)
{
  GEN res,*init, u1, met = smithrel(W,NULL,&u1);
  long c,i,j, l = lg(W);

  c = lg(met);
  if (DEBUGLEVEL) msgtimer("smith/class group");
  res=cgetg(c,t_VEC); init = (GEN*)cgetg(l,t_VEC);
  for (i=1; i<l; i++)
    init[i] = primeform(Disc,stoi(FB[vperm[i]]),prec);
  for (j=1; j<c; j++)
  {
    GEN p1 = NULL;
    for (i=1; i<l; i++)
      p1 = comp(p1, powgi(init[i], gcoeff(u1,i,j)));
    res[j] = (long)p1;
  }
  if (DEBUGLEVEL) msgtimer("generators");
  *ptmet = met; return res;
}

static GEN
extra_relations(long LIMC, long nlze, GEN *ptextraC)
{
  long fpc, i, k, nlze2;
  long s = 0, extrarel = nlze+2, lgsub = lg(subFB);
  gpmem_t av;
  long MAXRELSUP = min(50,4*KC);
  GEN p1, form, ex, extramat, extraC, col;

  extramat = cgetg(extrarel+1, t_MAT);
  extraC   = cgetg(extrarel+1, t_VEC);
  for (i=1; i<=extrarel; i++) extramat[i] = lgetg(KC+1,t_VECSMALL);
  if (!PRECREG)
    for (i=1; i<=extrarel; i++) extraC[i] = lgetg(1,t_COL);

  if (DEBUGLEVEL) fprintferr("looking for %ld extra relations\n",extrarel);
  nlze2 = PRECREG? max(nlze,lgsub-1): min(nlze+1,KC);
  if (nlze2 < 3 && KC > 2) nlze2 = 3;
  ex = cgetg(nlze2+1, t_VECSMALL);
  av = avma;
  while (s<extrarel)
  {
    form = NULL;
    for (i=1; i<=nlze2; i++)
    {
      ex[i] = mymyrand()>>randshift;
      if (ex[i])
      {
        p1 = primeform(Disc,stoi(FB[vperm[i]]),PRECREG);
        p1 = gpowgs(p1,ex[i]); form = comp(form,p1);
      }
    }
    if (!form) continue;

    fpc = factorquad(form,KC,LIMC);
    if (fpc==1)
    {
      s++; col = (GEN)extramat[s];
      for (i=1; i<=nlze2; i++) col[vperm[i]] = -ex[i];
      for (   ; i<=KC;    i++) col[vperm[i]] = 0;
      add_fact(col, form);
      for (i=1; i<=KC; i++)
        if (col[i]) break;
      if (i>KC)
      {
        s--; avma = av;
        if (--MAXRELSUP == 0) return NULL;
      }
      else { av = avma; if (PRECREG) extraC[s] = form[4]; }
    }
    else avma = av;
    if (DEBUGLEVEL)
    {
      if (fpc == 1) fprintferr(" %ld",s);
      else if (DEBUGLEVEL>1) fprintferr(".");
    }
  }

  for (i=1; i<=extrarel; i++)
  {
    GEN colg = cgetg(KC+1,t_COL);
    col = (GEN)extramat[i];
    extramat[i] = (long)colg;
    for (k=1; k<=KC; k++) colg[k] = lstoi(col[vperm[k]]);
  }
  if (DEBUGLEVEL) { fprintferr("\n"); msgtimer("extra relations"); }
  *ptextraC = extraC; return extramat;
}
#undef comp

static long
trivial_relations(long **mat, GEN C)
{
  long i, s = 0;
  GEN col;
  for (i=1; i<=KC; i++) 
  {
    if (smodis(Disc, FB[i])) continue;
    /* ramified prime ==> trivial relation */
    col = mat[++s];
    col[i] = 2;
    if (C) affsr(0, (GEN)C[s]);
  }
  return s;
}

static void
dbg_all(long phase, long s, long n)
{
  if (DEBUGLEVEL>1) fprintferr("\n");
  msgtimer("%s rel [#rel/#test = %ld/%ld]", phase? "random": "initial", s, n);
}

void
wr_rel(GEN col)
{
  long i, l = lg(col);
  fprintferr("\nrel = ");
  for (i=1; i<l; i++)
    if (col[i]) fprintferr("%ld^%ld ",i,col[i]);
  fprintferr("\n");
}

void
dbg_rel(long s, GEN col)
{
  if (DEBUGLEVEL == 1) fprintferr("%4ld",s);
  else { fprintferr("cglob = %ld. ", s); wr_rel(col); }
  flusherr(); 
}
/*******************************************************************/
/*                                                                 */
/*                    Imaginary Quadratic fields                   */
/*                                                                 */
/*******************************************************************/

/* Strategy 1 until lim relation found, then Strategy 2 until LIM. */
static GEN
imag_relations(long LIM, long lim, long LIMC, long **mat)
{
  long lgsub = lg(subFB), i, s, fpc, current, nbtest = 0;
  int first = 1;
  gpmem_t av;
  GEN C, col, form, ex = cgetg(lgsub, t_VECSMALL);
  GEN dummy = cgetg(1,t_COL);

  C = cgetg(LIM+1, t_VEC);
  for (i=1; i<=LIM; i++) C[i] = (long)dummy;
  av = avma;
  s = trivial_relations(mat, NULL);
  lim += s; if (lim > LIM) lim = LIM;
  for(;;)
  {
    if (s >= lim) {
      if (s >= LIM) break;
      lim = LIM; first = 0;
      if (DEBUGLEVEL) dbg_all(0, s, nbtest);
    }
    avma = av; current = first? 1+(s%KC): 1+s-RELSUP;
    form = imagpf(Disc, FB[current]);
    form = compimag(form, imag_random_form(ex));
    nbtest++; fpc = factorquad(form,KC,LIMC);
    if (!fpc)
    {
      if (DEBUGLEVEL>1) fprintferr(".");
      continue;
    }
    if (fpc > 1)
    {
      long *fpd = largeprime(fpc,ex,current,0);
      long b1, b2, p;
      GEN form2;
      if (!fpd)
      {
        if (DEBUGLEVEL>1) fprintferr(".");
        continue;
      }
      form2 = initimagform(fpd);
      form2 = compimag(form2, imagpf(Disc, FB[fpd[-2]]));
      p = fpc << 1;
      b1 = smodis((GEN)form2[2], p);
      b2 = smodis((GEN)form[2],  p);
      if (b1 != b2 && b1+b2 != p) continue;

      col = mat[++s];
      add_fact(col, form);
      (void)factorquad(form2,KC,LIMC);
      if (b1==b2)
      {
        for (i=1; i<lgsub; i++) col[subFB[i]] += fpd[i]-ex[i];
        sub_fact(col, form2); col[fpd[-2]]++;
      }
      else
      {
        for (i=1; i<lgsub; i++) col[subFB[i]] += -fpd[i]-ex[i];
        add_fact(col, form2); col[fpd[-2]]--;
      }
    }
    else
    {
      col = mat[++s];
      for (i=1; i<lgsub; i++) col[subFB[i]] = -ex[i];
      add_fact(col, form);
    }
    col[current]--;
    if (DEBUGLEVEL) dbg_rel(s, col);
    if (!first && fpc == 1 && col[current] == 0)
    {
      s--; for (i=1; i<=KC; i++) col[i]=0;
    }
  }
  if (DEBUGLEVEL) dbg_all(1, s, nbtest);
  return C;
}

static int
imag_be_honest()
{
  long p, fpc, s = KC, nbtest = 0;
  GEN F, ex = cgetg(lg(subFB), t_VECSMALL);
  gpmem_t av = avma;

  while (s<KC2)
  {
    p = FB[s+1]; if (DEBUGLEVEL) fprintferr(" %ld",p);
    F = compimag(imagpf(Disc, p), imag_random_form(ex));
    fpc = factorquad(F,s,p-1);
    if (fpc == 1) { nbtest=0; s++; }
    else
      if (++nbtest > 20) return 0;
    avma = av;
  }
  return 1;
}

/*******************************************************************/
/*                                                                 */
/*                      Real Quadratic fields                      */
/*                                                                 */
/*******************************************************************/

/* (1/2) log (d * 2^{e * EXP220}) */
GEN
get_dist(GEN e, GEN d, long prec)
{
  GEN t = mplog(absr(d));
  if (signe(e)) t = addrr(t, mulir(mulsi(EXP220,e), mplog2(prec)));
  return shiftr(t, -1);
}

static GEN
real_relations(long LIM, long lim, long LIMC, long **mat)
{
  long lgsub = lg(subFB), i, s, fpc, current, nbtest = 0, endcycle, rhoacc, rho;
  int first = 1;
  gpmem_t av, av1, limstack;
  GEN C, d, col, form, form0, form1, ex = cgetg(lgsub, t_VECSMALL);

  C = cgetg(LIM+1, t_VEC);
  for (i=1; i<=LIM; i++) C[i] = lgetr(PRECREG);

  current = 0;
  av = avma; limstack = stack_lim(av,1);
  s = trivial_relations(mat, C);
  lim += s; if (lim > LIM) lim = LIM;
NEW:
  for(;;)
  {
    if (s >= lim) {
      if (lim == LIM) break;
      lim = LIM; first = 0;
      if (DEBUGLEVEL) dbg_all(0, s, nbtest);
    }
    avma = av;
    form = real_random_form(ex);
    if (!first)
    {
      current = 1+s-RELSUP;
      form = comprealform3(form, realpf(Disc, FB[current]));
    }
    av1 = avma;
    form0 = form; form1 = NULL;
    endcycle = rhoacc = 0;
    rho = -1;

CYCLE:
    if (endcycle) goto NEW;
    if (low_stack(limstack, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"real_relations");
      gerepileall(av1, form1? 2: 1, &form, &form1);
    }
    if (rho < 0) rho = 0; /* first time in */
    else
    {
      form = rhorealform(form); rho++;
      rhoacc++;
      if (first)
        endcycle = (absi_equal((GEN)form[1],(GEN)form0[1])
             && egalii((GEN)form[2],(GEN)form0[2])
             && (!narrow || signe(form0[1])==signe(form[1])));
      else
      {
        if (narrow)
          { form = rhorealform(form); rho++; }
        else if (absi_equal((GEN)form[1], (GEN)form[3])) /* a = -c */
        {
          if (absi_equal((GEN)form[1],(GEN)form0[1]) &&
                  egalii((GEN)form[2],(GEN)form0[2])) goto NEW;
          form = rhorealform(form); rho++;
        }
        else
          { setsigne(form[1],1); setsigne(form[3],-1); }
        if (egalii((GEN)form[1],(GEN)form0[1]) &&
            egalii((GEN)form[2],(GEN)form0[2])) goto NEW;
      }
    }
    nbtest++; fpc = factorquad(form,KC,LIMC);
    if (!fpc)
    {
      if (DEBUGLEVEL>1) fprintferr(".");
      goto CYCLE;
    }
    if (fpc > 1)
    { /* look for Large Prime relation */
      long *fpd = largeprime(fpc,ex,current,rhoacc);
      long b1, b2, p;
      GEN form2;
      if (!fpd)
      {
        if (DEBUGLEVEL>1) fprintferr(".");
        goto CYCLE;
      }
      if (!form1) form1 = initrealform5(ex);
      if (!first) form1 = comprealform(form1, realpf5(Disc, FB[current]));
      form1 = rhoreal_pow(form1, rho);
      rho = 0;

      form2 = initrealform5(fpd);
      if (fpd[-2]) form2 = comprealform(form2, realpf5(Disc, FB[fpd[-2]]));
      form2 = rhoreal_pow(form2, fpd[-3]);
      if (!narrow && !absi_equal((GEN)form2[1],(GEN)form2[3]))
      {
        setsigne(form2[1],1);
        setsigne(form2[3],-1);
      }
      p = fpc << 1;
      b1 = smodis((GEN)form2[2], p);
      b2 = smodis((GEN)form1[2], p);
      if (b1 != b2 && b1+b2 != p) goto CYCLE;

      col = mat[++s];
      add_fact(col, form1);
      (void)factorquad(form2,KC,LIMC);
      if (b1==b2)
      {
        for (i=1; i<lgsub; i++) col[subFB[i]] += fpd[i]-ex[i];
        sub_fact(col, form2);
        if (fpd[-2]) col[fpd[-2]]++; /* implies !first */
        d = get_dist(subii((GEN)form1[4],(GEN)form2[4]),
                     divrr((GEN)form1[5],(GEN)form2[5]), PRECREG);
      }
      else
      {
        for (i=1; i<lgsub; i++) col[subFB[i]] += -fpd[i]-ex[i];
        add_fact(col, form2);
        if (fpd[-2]) col[fpd[-2]]--;
        d = get_dist(addii((GEN)form1[4],(GEN)form2[4]),
                     mulrr((GEN)form1[5],(GEN)form2[5]), PRECREG);
      }
    }
    else
    { /* standard relation */
      if (!form1) form1 = initrealform5(ex);
      if (!first) form1 = comprealform(form1, realpf5(Disc, FB[current]));
      form1 = rhoreal_pow(form1,rho);
      rho = 0;

      col = mat[++s];
      for (i=1; i<lgsub; i++) col[subFB[i]] = -ex[i];
      add_fact(col, form1);
      d = get_dist((GEN)form1[4], (GEN)form1[5], PRECREG);
    }
    if (DEBUGLEVEL) fprintferr(" %ld",s);
    affrr(d, (GEN)C[s]);
    if (first)
    {
      if (s >= lim) goto NEW;
      goto CYCLE;
    }
    else
    {
      col[current]--;
      if (fpc == 1 && col[current] == 0)
      {
        s--; for (i=1; i<=KC; i++) col[i]=0;
      }
    }
  }
  if (DEBUGLEVEL) dbg_all(1, s, nbtest);
  return C;
}

static int
real_be_honest()
{
  long p, fpc, s = KC, nbtest = 0;
  GEN F,F0, ex = cgetg(lg(subFB), t_VECSMALL);
  gpmem_t av = avma;

  while (s<KC2)
  {
    p = FB[s+1]; if (DEBUGLEVEL) fprintferr(" %ld",p);
    F = comprealform3(realpf(Disc, p), real_random_form(ex));
    for (F0 = F;;)
    {
      fpc = factorquad(F,s,p-1);
      if (fpc == 1) { nbtest=0; s++; break; }
      if (++nbtest > 20) return 0;
      F = fix_signs( rhorealform(F) );
      if (egalii((GEN)F[1],(GEN)F0[1])
       && egalii((GEN)F[2],(GEN)F0[2])) break;
    }
    avma = av;
  }
  return 1;
}

static GEN
gcdreal(GEN a,GEN b)
{
  long e;
  GEN k1,r;

  if (!signe(a)) return mpabs(b);
  if (!signe(b)) return mpabs(a);

  if (typ(a)==t_INT)
  {
    if (typ(b)==t_INT) return mppgcd(a,b);
    a = itor(a, lg(b));
  }
  else if (typ(b)==t_INT)
  {
    b = itor(b, lg(a));
  }
  if (expo(a)<-5) return absr(b);
  if (expo(b)<-5) return absr(a);
  a=absr(a); b=absr(b);
  while (expo(b) >= -5  && signe(b))
  {
    k1 = gcvtoi(divrr(a,b),&e);
    if (e > 0) return NULL;
    r=subrr(a,mulir(k1,b)); a=b; b=r;
  }
  return absr(a);
}

enum { RELAT, LARGE, PRECI };

static int
get_R(GEN C, long sreg, GEN z, GEN *ptR)
{
  GEN R = gun;
  double c;
  long i;

  if (PRECREG)
  {
    R = mpabs((GEN)C[1]);
    for (i=2; i<=sreg; i++)
    {
      R = gcdreal((GEN)C[i], R);
      if (!R) return PRECI;
    }
    if (DEBUGLEVEL)
    {
      if (DEBUGLEVEL>7) fprintferr("R = %Z",R);
      msgtimer("regulator");
    }
    if (gexpo(R) <= -3)
    {
      if (DEBUGLEVEL) fprintferr("regulator is zero.\n");
      return RELAT;
    }
  }
  c = gtodouble(gmul(z, R));
  if (c < 0.75 || c > 1.5) return RELAT;
  *ptR = R; return LARGE;
}

static int
quad_be_honest()
{
  int r;
  if (KC2 <= KC) return 1;
  if (DEBUGLEVEL)
    fprintferr("be honest for primes from %ld to %ld\n", FB[KC+1],FB[KC2]);
  r = PRECREG? real_be_honest(): imag_be_honest();
  if (DEBUGLEVEL) { fprintferr("\n"); msgtimer("be honest"); }
  return r;
}

GEN
buchquad(GEN D, double cbach, double cbach2, long RELSUP0, long flag, long prec)
{
  gpmem_t av0 = avma, av;
  long KCCO, i, j, s, **mat;
  long nrelsup, nreldep, LIMC, LIMC2, cp, nlze;
  GEN h, W, cyc, res, gen, dep, C, B, extramat, extraC;
  GEN R, resc, Res, z;
  double drc, lim, LOGD, LOGD2;
  const long MAXRELSUP = 7;

  Disc = D; if (typ(Disc)!=t_INT) err(typeer,"buchquad");
  s = mod4(Disc);
  switch(signe(Disc))
  {
    case -1:
      if (cmpis(Disc,-4) >= 0)
      {
        GEN p1=cgetg(6,t_VEC); p1[1]=p1[4]=p1[5]=un;
        p1[2]=p1[3]=lgetg(1,t_VEC); return p1;
      }
      if (s==2 || s==1) err(funder2,"buchquad");
      PRECREG=0; break;

    case 1:
      if (s==2 || s==3) err(funder2,"buchquad");
      if (flag)
        err(talker,"sorry, narrow class group not implemented. Use bnfnarrow");
      PRECREG=1; break;

    default: err(talker,"zero discriminant in quadclassunit");
  }
  if (carreparfait(Disc)) err(talker,"square argument in quadclassunit");
  if (!isfundamental(Disc))
    err(warner,"not a fundamental discriminant in quadclassunit");
  buch_init(); RELSUP = RELSUP0;
  drc = fabs(gtodouble(Disc));
  LOGD = log(drc);
  LOGD2 = LOGD * LOGD;

  lim = sqrt(drc);
  /* resc = sqrt(D) w / 2^r1 (2pi)^r2 ~ hR / L(chi,1) */
  if (PRECREG) resc = dbltor(lim / 2.);
  else         resc = dbltor(lim / PI);
  if (!PRECREG) lim /= sqrt(3.);
  R = gun;
  cp = (long)exp(sqrt(LOGD*log(LOGD)/8.0));
  if (cp < 13) cp = 13;
  av = avma; cbach /= 2;
  mat = NULL;

START: avma = av; cbach = check_bach(cbach,6.);
  if (mat) { desalloc(mat); mat = NULL; }
  nreldep = nrelsup = 0;
  LIMC = (long)(cbach*LOGD2);
  if (LIMC < cp) { LIMC = cp; cbach = LIMC / LOGD2; }
  LIMC2 = (long)(max(cbach,cbach2)*LOGD2);
  if (LIMC2 < LIMC) LIMC2 = LIMC;
  if (PRECREG)
  {
    PRECREG = max(prec+1, MEDDEFAULTPREC + 2*(expi(Disc)>>TWOPOTBITS_IN_LONG));
    sqrtD  = gsqrt(Disc,PRECREG);
    isqrtD = gfloor(sqrtD);
  }

  Res = FBquad(Disc,LIMC2,LIMC);
  if (!Res) goto START;
  subFB = subFBquad(Disc, lim + 0.5, KC);
  if (!subFB) goto START;
  powsubFB = powsubFBquad(CBUCH+1);
  limhash = ((ulong)LIMC < (MAXHALFULONG>>1))? LIMC*LIMC: HIGHBIT>>1;
  for (i=0; i<HASHT; i++) hashtab[i]=NULL;

  KCCO = KC + RELSUP;
  if (DEBUGLEVEL) fprintferr("KC = %ld, KCCO = %ld\n",KC,KCCO);
  mat = (long**)cgetalloc(NULL, KCCO+1, t_VEC);
  for (i=1; i<=KCCO; i++)
  {
    GEN t = cgetalloc(NULL, KC+1, t_VECSMALL);
    for (j=1; j<=KC; j++) t[j]=0;
    mat[i] = t;
  }

  s = lg(subFB)-1 + RELSUP;
  C = PRECREG? real_relations(KCCO,s,LIMC,mat)
             : imag_relations(KCCO,s,LIMC,mat);
  W = hnfspec(mat,vperm,&dep,&B,&C,lg(subFB)-1);
  nlze = lg(dep)>1? lg(dep[1])-1: lg(B[1])-1;

  if (nlze)
  {
MORE:
    extramat = extra_relations(LIMC,nlze, &extraC);
    if (!extramat) { goto START; }
    W = hnfadd(W,vperm,&dep,&B,&C, extramat,extraC);
    nlze = lg(dep)>1? lg(dep[1])-1: lg(B[1])-1;
    KCCO += lg(extramat)-1;
    if (nlze)
    {
      if (++nreldep > 5) goto START;
      goto MORE;
    }
  }

  h = dethnf_i(W);
  if (DEBUGLEVEL) fprintferr("\n#### Tentative class number: %Z\n", h);

  z = mulrr(Res, resc); /* ~ hR if enough relations, a multiple otherwise */
  switch(get_R(C, KCCO - (lg(B)-1) - (lg(W)-1), divir(h,z), &R))
  {
    case PRECI:
      prec = (PRECREG<<1)-2;
      goto START;

    case RELAT:
      if (++nrelsup <= MAXRELSUP) { nlze = min(KC, nrelsup); goto MORE; }
      goto START;
  }
  /* DONE */
  if (!quad_be_honest()) goto START;

  gen = get_clgp(Disc,W,&cyc,PRECREG);
  desalloc(mat);

  res=cgetg(6,t_VEC);
  res[1]=(long)h;
  res[2]=(long)cyc;
  res[3]=(long)gen;
  res[4]=(long)R;
  res[5]=ldiv(mpmul(R,h), z); return gerepilecopy(av0,res);
}

GEN
buchimag(GEN D, GEN c, GEN c2, GEN REL)
{
  return buchquad(D,gtodouble(c),gtodouble(c2),itos(REL), 0,0);
}

GEN
buchreal(GEN D, GEN sens0, GEN c, GEN c2, GEN REL, long prec)
{
  return buchquad(D,gtodouble(c),gtodouble(c2),itos(REL), itos(sens0),prec);
}
