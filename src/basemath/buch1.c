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
#include "paripriv.h"

/*******************************************************************/
/*                                                                 */
/*       Hilbert and Ray Class field using CM (Schertz)            */
/*                                                                 */
/*******************************************************************/
static int
isoforder2(GEN form)
{
  GEN a = gel(form,1), b = gel(form,2), c = gel(form,3);
  return !signe(b) || absi_equal(a,b) || equalii(a,c);
}

GEN
getallforms(GEN D, GEN *ptz)
{
  ulong d = itou(D), dover3 = d/3, t, b2, a, b, c, h;
  GEN z, L = cgetg((long)(sqrt(d) * log2(d)), t_VEC);
  b2 = b = (d&1); h = 0; z = gen_1;
  if (!b) /* b = 0 treated separately to avoid special cases */
  {
    t = d >> 2; /* (b^2 - D) / 4*/
    for (a=1; a*a<=t; a++)
      if (c = t/a, t == c*a)
      {
	z = mului(a,z);
	gel(L,++h) = mkvecsmall3(a,b,c);
      }
    b = 2; b2 = 4;
  }
  /* now b > 0 */
  for ( ; b2 <= dover3; b += 2, b2 = b*b)
  {
    t = (b2 + d) >> 2; /* (b^2 - D) / 4*/
    /* b = a */
    if (c = t/b, t == c*b)
    {
      z = mului(b,z);
      gel(L,++h) = mkvecsmall3(b,b,c);
    }
    /* b < a < c */
    for (a = b+1; a*a < t; a++)
      if (c = t/a, t == c*a)
      {
	z = mului(a,z);
	gel(L,++h) = mkvecsmall3(a, b,c);
	gel(L,++h) = mkvecsmall3(a,-b,c);
      }
    /* a = c */
    if (a * a == t) { z = mului(a,z); gel(L,++h) = mkvecsmall3(a,b,c); }
  }
  *ptz = z; setlg(L,h+1); return L;
}

#define MOD4(x) ((x)&3)
/* find P and Q two non principal prime ideals (above p,q) such that
 *   (pq, 2z) = 1  [coprime to all class group representatives]
 *   cl(P) = cl(Q) if P has order 2 in Cl(K)
 * Try to have e = 24 / gcd(24, (p-1)(q-1)) as small as possible */
static void
get_pq(GEN D, GEN z, ulong *ptp, ulong *ptq)
{
  const long MAXL = 50;
  GEN form, wp = cgetg(MAXL,t_VECSMALL), wlf = cgetg(MAXL,t_VEC);
  long i, ell, p, l = 1, d = itos(D);
  byteptr diffell = diffptr + 2;

  ell = 3;
  while (l < MAXL)
  {
    NEXT_PRIME_VIADIFF_CHECK(ell, diffell);
    if (umodiu(z,ell) && kross(d,ell) > 0)
    {
      form = redimag(primeform_u(D,ell));
      if (gcmp1(gel(form,1))) continue;
      gel(wlf,l) = form;
      wp[l]  = ell; l++;
    }
  }
  setlg(wp,l); setlg(wlf,l);

  for (i=1; i<l; i++)
    if (wp[i] % 3 == 1) break;
  if (i==l) i = 1;
  p = wp[i]; form = gel(wlf,i);
  i = l;
  if (isoforder2(form))
  {
    long oki = 0;
    for (i=1; i<l; i++)
      if (gequal(gel(wlf,i),form))
      {
	if (MOD4(p) == 1 || MOD4(wp[i]) == 1) break;
	if (!oki) oki = i; /* not too bad, still e = 2 */
      }
    if (i==l) i = oki;
    if (!i) pari_err(bugparier,"quadhilbertimag (can't find p,q)");
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
  *ptq = wp[i];
}

struct gpq_data {
  ulong p, q;
  long e;
  GEN sqd, u, pq, pq2;
};

static GEN
gpq(GEN form, struct gpq_data *D, long prec)
{
  long a = form[1], a2 = a << 1; /* gcd(a2, u) = 2 */
  GEN p1,p2,p3,p4;
  GEN w = Z_chinese(D->u, stoi(-form[2]), D->pq2, stoi(a2));
  GEN al = mkcomplex(gdivgs(w, -a2), gdivgs(D->sqd, a2));
  p1 = trueeta(gdivgs(al,D->p), prec);
  p2 = D->p == D->q? p1: trueeta(gdivgs(al,D->q), prec);
  p3 = trueeta(gdiv(al, D->pq), prec);
  p4 = trueeta(al, prec);
  return gpowgs(gdiv(gmul(p1,p2),gmul(p3,p4)), D->e);
}

/* returns an equation for the Hilbert class field of Q(sqrt(D)), D < 0 */
static GEN
quadhilbertimag(GEN D)
{
  GEN z, L, P, qfp, u;
  pari_sp av = avma;
  long h, i, prec;
  struct gpq_data T;
  ulong p, q;

  if (DEBUGLEVEL>1) (void)timer2();
  if (lgefint(D) == 3)
  {
    long d = D[2]; /* = |D| */
    if (d <= 11 || d == 19 || d == 43 || d == 67 || d == 163) return pol_x(0);
  }
  L = getallforms(D,&z);
  h = lg(L)-1;
  if (DEBUGLEVEL>1) msgtimer("class number = %ld",h);
  get_pq(D, z, &p, &q);
  T.p = p;
  T.q = q;
  T.e = 24 / ugcd((p%24 - 1) * (q%24 - 1), 24);
  if(DEBUGLEVEL>1) fprintferr("p = %lu, q = %lu, e = %ld\n",p,q,T.e);
  qfp = primeform_u(D, p);
  T.pq =  muluu(p, q);
  T.pq2 = shifti(T.pq,1);
  if (p == q)
  {
    u = gel(qficompraw(qfp, qfp),2);
    T.u = modii(u, T.pq2);
  }
  else
  {
    GEN qfq = primeform_u(D, q), bp = gel(qfp,2), bq = gel(qfq,2);
    T.u = Z_chinese_coprime(bp, bq, utoipos(p), utoipos(q), T.pq);
    if (mpodd(bp) != mpodd(T.u)) T.u = addii(T.u, T.pq);
    /* T.u = bp (mod 2p), T.u = bq (mod 2q) */
  }
  /* u modulo 2pq */
  prec = 3;
  for(;;)
  {
    long ex, exmax = 0;
    pari_sp av0 = avma;
    T.sqd = sqrtr_abs(itor(D, prec));
    P = cgetg(h+1,t_VEC);
    for (i=1; i<=h; i++)
    {
      GEN s = gpq(gel(L,i), &T, prec);
      if (DEBUGLEVEL>3) fprintferr("%ld ", i);
      gel(P,i) = s; ex = gexpo(s); if (ex > 0) exmax += ex;
    }
    if (DEBUGLEVEL>1) msgtimer("roots");
    P = real_i( roots_to_pol(P,0) );
    P = grndtoi(P,&exmax);
    if (DEBUGLEVEL>1) msgtimer("product, error bits = %ld",exmax);
    if (exmax <= -10) break;
    avma = av0; prec += (DEFAULTPREC-2) + nbits2nlong(exmax);
    if (DEBUGLEVEL) pari_warn(warnprec,"quadhilbertimag",prec);
  }
  return gerepileupto(av,P);
}

GEN
quadhilbert(GEN D, long prec)
{
  if (typ(D) != t_INT)
  {
    D = checkbnf(D);
    if (degpol(gmael(D,7,1)) != 2)
      pari_err(talker,"not a polynomial of degree 2 in quadhilbert");
    D = gmael(D,7,3);
  }
  else if (!Z_isfundamental(D))
    pari_err(talker,"quadhilbert needs a fundamental discriminant");
  return (signe(D)>0)? quadhilbertreal(D,prec)
		     : quadhilbertimag(D);
}

/* return a vector of all roots of 1 in bnf [not necessarily quadratic] */
static GEN
getallrootsof1(GEN bnf)
{
  GEN T, u, nf = checknf(bnf), tu;
  long i, n = itos(gmael3(bnf,8,4,1));

  if (n == 2) {
    long N = nf_get_degree(nf);
    return mkvec2(scalarcol_shallow(gen_m1, N),
		  scalarcol_shallow(gen_1, N));
  }
  tu = poltobasis(nf, gmael3(bnf,8,4,2));
  T = zk_multable(nf, tu);
  u = cgetg(n+1, t_VEC); gel(u,1) = tu;
  for (i=2; i <= n; i++) gel(u,i) = ZM_ZC_mul(T, gel(u,i-1));
  return u;
}
/* assume bnr has the right conductor */
static GEN
get_lambda(GEN bnr)
{
  GEN bnf = gel(bnr,1), nf = gel(bnf,7), pol = nf_get_pol(nf), f = gmael3(bnr,2,1,1);
  GEN labas, lamodf, u;
  long a, b, f2, i, lu, v = varn(pol);

  f2 = 2 * itos(gcoeff(f,1,1));
  u = getallrootsof1(bnf); lu = lg(u);
  for (i=1; i<lu; i++)
    gel(u,i) = ZC_hnfrem(gel(u,i), f); /* roots of 1, mod f */
  if (DEBUGLEVEL>1)
    fprintferr("quadray: looking for [a,b] != unit mod 2f\n[a,b] = ");
  for (a=0; a<f2; a++)
    for (b=0; b<f2; b++)
    {
      GEN la = deg1pol_shallow(stoi(a), stoi(b), v); /* ax + b */
      if (umodiu(gnorm(mkpolmod(la, pol)), f2) != 1) continue;
      if (DEBUGLEVEL>1) fprintferr("[%ld,%ld] ",a,b);

      labas = poltobasis(nf, la);
      lamodf = ZC_hnfrem(labas, f);
      for (i=1; i<lu; i++)
	if (ZV_equal(lamodf, gel(u,i))) break;
      if (i < lu) continue; /* la = unit mod f */
      if (DEBUGLEVEL)
      {
	if (DEBUGLEVEL>1) fprintferr("\n");
	fprintferr("lambda = %Ps\n",la);
      }
      return labas;
    }
  pari_err(bugparier,"get_lambda");
  return NULL;
}

static GEN
to_approx(GEN nf, GEN a)
{
  GEN M = nf_get_M(nf);
  return gadd(gel(a,1), gmul(gcoeff(M,1,2),gel(a,2)));
}
/* Z-basis for a (over C) */
static GEN
get_om(GEN nf, GEN a) {
  return mkvec2(to_approx(nf,gel(a,2)),
		to_approx(nf,gel(a,1)));
}

/* Compute all elts in class group G = [|G|,c,g], c=cyclic factors, g=gens.
 * Set list[j + 1] = g1^e1...gk^ek where j is the integer
 *   ek + ck [ e(k-1) + c(k-1) [... + c2 [e1]]...] */
static GEN
getallelts(GEN bnr)
{
  GEN nf, G, C, c, g, list, pows, gk;
  long lc, i, j, no;

  nf = checknf(bnr);
  G = gel(bnr,5);

  no = itos(gel(G,1));
  c = gel(G,2);
  g = gel(G,3); lc = lg(c)-1;
  list = cgetg(no+1,t_VEC);
  gel(list,1) = matid(nf_get_degree(nf)); /* (1) */
  if (!no) return list;

  pows = cgetg(lc+1,t_VEC);
  c = leafcopy(c); settyp(c, t_VECSMALL);
  for (i=1; i<=lc; i++)
  {
    long k = itos(gel(c,i));
    c[i] = k;
    gk = cgetg(k, t_VEC); gel(gk,1) = gel(g,i);
    for (j=2; j<k; j++)
      gel(gk,j) = idealmoddivisor(bnr, idealmul(nf, gel(gk,j-1), gel(gk,1)));
    gel(pows,i) = gk; /* powers of g[i] */
  }

  C = cgetg(lc+1, t_VECSMALL); C[1] = c[lc];
  for (i=2; i<=lc; i++) C[i] = C[i-1] * c[lc-i+1];
  /* C[i] = c(k-i+1) * ... * ck */
  /* j < C[i+1] <==> j only involves g(k-i)...gk */
  i = 1;
  for (j=1; j < C[1]; j++)
    gel(list, j+1) = gmael(pows,lc,j);
  while(j<no)
  {
    long k;
    GEN a;
    if (j == C[i+1]) i++;
    a = gmael(pows,lc-i,j/C[i]);
    k = j%C[i] + 1;
    if (k > 1) a = idealmoddivisor(bnr, idealmul(nf, a, gel(list,k)));
    gel(list, ++j) = a;
  }
  return list;
}

/* x quadratic integer (approximate), recognize it. If error return NULL */
static GEN
findbezk(GEN nf, GEN x)
{
  GEN a,b, M = nf_get_M(nf), u = gcoeff(M,1,2);
  long ea, eb;

  /* u t_COMPLEX generator of nf.zk, write x ~ a + b u, a,b in Z */
  b = grndtoi(mpdiv(imag_i(x), gel(u,2)), &eb);
  if (eb > -20) return NULL;
  a = grndtoi(mpsub(real_i(x), mpmul(b,gel(u,1))), &ea);
  if (ea > -20) return NULL;
  return signe(b)? coltoalg(nf, mkcol2(a,b)): a;
}

static GEN
findbezk_pol(GEN nf, GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx,t_POL);
  for (i=2; i<lx; i++)
    if (! (gel(y,i) = findbezk(nf,gel(x,i))) ) return NULL;
  y[1] = x[1]; return y;
}

/* allow t_QF[IR], and t_VEC/t_COL with 3 components */
GEN
form_to_ideal(GEN x)
{
  long tx = typ(x);
  GEN b;
  if ((is_vec_t(tx) || lg(x) != 4)
       && tx != t_QFR && tx != t_QFI) pari_err(typeer,"form_to_ideal");
  b = negi(gel(x,2)); if (mpodd(b)) b = addis(b,1);
  return mkmat2( mkcol2(gel(x,1), gen_0),
		 mkcol2(shifti(b,-1), gen_1) );
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
  k += MEDDEFAULTPREC + (gexpo(P) / BITS_IN_LONG);
  if (k <= prec) k = (prec<<1)-2; /* dubious: old prec should have worked */
  return k;
}

/* Compute data for ellphist */
static GEN
ellphistinit(GEN om, long prec)
{
  GEN res,om1b,om2b, om1 = gel(om,1), om2 = gel(om,2);

  if (gsigne(imag_i(gdiv(om1,om2))) < 0) { swap(om1,om2); om = mkvec2(om1,om2); }
  om1b = gconj(om1);
  om2b = gconj(om2); res = cgetg(4,t_VEC);
  gel(res,1) = gdivgs(elleisnum(om,2,0,prec),12);
  gel(res,2) = gdiv(PiI2(prec), gmul(om2, imag_i(gmul(om1b,om2))));
  gel(res,3) = om2b; return res;
}

/* Computes log(phi^*(z,om)), using res computed by ellphistinit */
static GEN
ellphist(GEN om, GEN res, GEN z, long prec)
{
  GEN u = imag_i(gmul(z, gel(res,3)));
  GEN zst = gsub(gmul(u, gel(res,2)), gmul(z,gel(res,1)));
  return gsub(ellsigma(om,z,1,prec),gmul2n(gmul(z,zst),-1));
}

/* Computes phi^*(la,om)/phi^*(1,om) where (1,om) is an oriented basis of the
   ideal gf*gc^{-1} */
static GEN
computeth2(GEN om, GEN la, long prec)
{
  GEN p1,p2,res = ellphistinit(om,prec);

  p1 = gsub(ellphist(om,res,la,prec), ellphist(om,res,gen_1,prec));
  p2 = imag_i(p1);
  if (gexpo(real_i(p1))>20 || gexpo(p2)> bit_accuracy(minss(prec,lg(p2)))-10)
    return NULL;
  return gexp(p1,prec);
}

/* Computes P_2(X)=polynomial in Z_K[X] closest to prod_gc(X-th2(gc)) where
   the product is over the ray class group bnr.*/
static GEN
computeP2(GEN bnr, long prec)
{
  long clrayno, i, first = 1;
  pari_sp av=avma, av2;
  GEN listray,P0,P,f,lanum, la = get_lambda(bnr), nf = checknf(bnr);

  f = gmael3(bnr,2,1,1);
  listray = getallelts(bnr);
  clrayno = lg(listray)-1; av2 = avma;
PRECPB:
  if (!first)
  {
    if (DEBUGLEVEL) pari_warn(warnprec,"computeP2",prec);
    nf = gerepilecopy(av2, nfnewprec_shallow(checknf(bnr),prec));
  }
  first = 0; lanum = to_approx(nf,la);
  P = cgetg(clrayno+1,t_VEC);
  for (i=1; i<=clrayno; i++)
  {
    GEN om = get_om(nf, idealdiv(nf,f,gel(listray,i)));
    GEN s = computeth2(om,lanum,prec);
    if (!s) { prec = (prec<<1)-2; goto PRECPB; }
    gel(P,i) = s;
  }
  P0 = roots_to_pol(P, 0);
  P = findbezk_pol(nf, P0);
  if (!P) { prec = get_prec(P0, prec); goto PRECPB; }
  return gerepilecopy(av, P);
}

#define nexta(a) (a>0 ? -a : 1-a)
static GEN
do_compo(GEN x, GEN y)
{
  long a, i, l = lg(y);
  GEN z;
  y = leafcopy(y); /* y := t^deg(y) y(#/t) */
  for (i = 2; i < l; i++)
    if (signe(y[i])) gel(y,i) = monomial(gel(y,i), l-i-1, MAXVARN);
  for  (a = 0;; a = nexta(a))
  {
    if (a) x = gsubst(x, 0, gaddsg(a, pol_x(0)));
    z = gsubst(resultant(x,y), MAXVARN, pol_x(0));
    if (issquarefree(z)) return z;
  }
}
#undef nexta

static GEN
galoisapplypol(GEN nf, GEN s, GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx,t_POL);

  for (i=2; i<lx; i++) gel(y,i) = galoisapply(nf,s,gel(x,i));
  y[1] = x[1]; return y;
}

/* x quadratic, write it as ua + v, u,v rational */
static GEN
findquad(GEN a, GEN x, GEN p)
{
  long tu, tv;
  pari_sp av = avma;
  GEN u,v;
  if (typ(x) == t_POLMOD) x = gel(x,2);
  if (typ(a) == t_POLMOD) a = gel(a,2);
  u = poldivrem(x, a, &v);
  u = simplify_shallow(u); tu = typ(u);
  v = simplify_shallow(v); tv = typ(v);
  if (!is_scalar_t(tu) || !is_scalar_t(tv))
    pari_err(talker, "incorrect data in findquad");
  x = deg1pol(v, u, varn(a));
  if (typ(x) == t_POL) x = gmodulo(x,p);
  return gerepileupto(av, x);
}

static GEN
findquad_pol(GEN p, GEN a, GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx,t_POL);
  for (i=2; i<lx; i++) gel(y,i) = findquad(a, gel(x,i), p);
  y[1] = x[1]; return y;
}

static GEN
compocyclo(GEN nf, long m, long d)
{
  GEN sb,a,b,s,p1,p2,p3,res,polL,polLK,nfL, D = nf_get_disc(nf);
  long ell,vx;

  p1 = quadhilbertimag(D);
  p2 = polcyclo(m,0);
  if (d==1) return do_compo(p1,p2);

  ell = m&1 ? m : (m>>2);
  if (equalui(ell,D)) /* ell = |D| */
  {
    p2 = gcoeff(nffactor(nf,p2),1,1);
    return do_compo(p1,p2);
  }
  if (ell%4 == 3) ell = -ell;
  /* nf = K = Q(a), L = K(b) quadratic extension = Q(t) */
  polLK = quadpoly(stoi(ell)); /* relative polynomial */
  res = rnfequation2(nf, polLK);
  vx = nf_get_varn(nf);
  polL = gsubst(gel(res,1),0,pol_x(vx)); /* = charpoly(t) */
  a = gsubst(lift(gel(res,2)), 0,pol_x(vx));
  b = gsub(pol_x(vx), gmul(gel(res,3), a));
  nfL = nfinit(polL, DEFAULTPREC);
  p1 = gcoeff(nffactor(nfL,p1),1,1);
  p2 = gcoeff(nffactor(nfL,p2),1,1);
  p3 = do_compo(p1,p2); /* relative equation over L */
  /* compute non trivial s in Gal(L / K) */
  sb= gneg(gadd(b, truecoeff(polLK,1))); /* s(b) = Tr(b) - b */
  s = gadd(pol_x(vx), gsub(sb, b)); /* s(t) = t + s(b) - b */
  p3 = gmul(p3, galoisapplypol(nfL, s, p3));
  return findquad_pol(nf_get_pol(nf), a, p3);
}

/* I integral ideal in HNF. (x) = I, x small in Z ? */
static long
isZ(GEN I)
{
  GEN x = gcoeff(I,1,1);
  if (signe(gcoeff(I,1,2)) || !equalii(x, gcoeff(I,2,2))) return 0;
  return is_bigint(x)? -1: itos(x);
}

/* Treat special cases directly. return NULL if not special case */
static GEN
treatspecialsigma(GEN bnr)
{
  GEN f = gmael3(bnr,2,1,1), nf = gmael(bnr,1,7), D = nf_get_disc(nf), p1, p2, tryf;
  long Ds, fl, i = isZ(f);

  if (i == 1) return quadhilbertimag(D); /* f = 1 */

  if (equaliu(D,3))
  {
    if (i == 4 || i == 5 || i == 7) return polcyclo(i,0);
    if (!equaliu(gcoeff(f,1,1),9) || !equaliu(content(f),3)) return NULL;
    p1 = gel(nfroots(nf, mkpoln(3,gen_1,gen_1,gen_1)),1); /* f = P_3^3 */
    return gadd(monomial(gen_1,3,0), p1); /* x^3+j */
  }
  if (equaliu(D,4))
  {
    if (i == 3 || i == 5) return polcyclo(i,0);
    if (i != 4) return NULL;
    p1 = gel(nfroots(nf, mkpoln(3,gen_1,gen_0,gen_1)),1);
    return gadd(monomial(gen_1,2,0), p1); /* x^2+i */
  }
  Ds = smodis(D,48);
  if (i)
  {
    if (i==2 && Ds%16== 8) return compocyclo(nf, 4,1);
    if (i==3 && Ds% 3== 1) return compocyclo(nf, 3,1);
    if (i==4 && Ds% 8== 1) return compocyclo(nf, 4,1);
    if (i==6 && Ds   ==40) return compocyclo(nf,12,1);
    return NULL;
  }

  p1 = gcoeff(f,1,1); /* integer > 0 */
  p2 = gcoeff(f,2,2);
  if (gcmp1(p2)) { fl = 0; tryf = p1; }
  else {
    if (Ds % 16 != 8 || !equaliu(Q_content(f),2)) return NULL;
    fl = 1; tryf = shifti(p1,-1);
  }
  /* tryf integer > 0 */
  if (cmpiu(tryf, 3) <= 0 || signe(remii(D, tryf)) || !isprime(tryf))
    return NULL;

  i = itos(tryf); if (fl) i *= 4;
  return compocyclo(nf,i,2);
}

GEN
quadray(GEN D, GEN f, long prec)
{
  GEN bnr, y, pol, bnf;
  pari_sp av = avma;

  if (typ(D) == t_INT)
  {
    long v = gvar(f);
    if (!Z_isfundamental(D))
      pari_err(talker,"quadray needs a fundamental discriminant");
    if (v == NO_VARIABLE) v = fetch_user_var("y");
    pol = quadpoly0(D, v);
    bnf = Buchall(pol, nf_FORCE, prec);
  }
  else
  {
    GEN nf;
    bnf = checkbnf(D); nf = gel(bnf,7);
    if (nf_get_degree(nf) != 2)
      pari_err(talker,"not a polynomial of degree 2 in quadray");
    D = nf_get_disc(nf);
  }
  bnr = Buchray(bnf, f, nf_INIT|nf_GEN);
  if (gcmp1(gmael(bnr,5,1))) { avma = av; return pol_x(0); }
  if (signe(D) > 0)
    y = bnrstark(bnr,NULL,prec);
  else
  {
    bnr = gel(bnrconductor(bnr,NULL,2), 2);
    y = treatspecialsigma(bnr);
    if (!y) y = computeP2(bnr, prec);
  }
  return gerepileupto(av, y);
}

/*******************************************************************/
/*                                                                 */
/*         CLASS GROUP AND REGULATOR (McCURLEY, BUCHMANN)          */
/*                   QUADRATIC FIELDS                              */
/*                                                                 */
/*******************************************************************/
/* For largeprime() hashtable. Note that hashed pseudoprimes are odd (unless
 * 2 | index), hence the low order bit is not useful. So we hash
 * HASHBITS bits starting at bit 1, not bit 0 */
#define HASHBITS 10
static const long HASHT = 1 << HASHBITS;

static long
hash(long q) { return (q & ((1 << (HASHBITS+1)) - 1)) >> 1; }
#undef HASHBITS

/* See buch2.c:
 * B->subFB contains split p such that \prod p > sqrt(B->Disc)
 * B->powsubFB contains powers of forms in B->subFB */
#define RANDOM_BITS 4
static const long CBUCH = (1<<RANDOM_BITS)-1;

struct buch_quad
{
  ulong limhash;
  long KC, KC2, PRECREG;
  long *primfact, *exprimfact, *FB, *numFB, **hashtab;
  GEN powsubFB, vperm, subFB, badprim;
  struct qfr_data *QFR;
};

/*******************************************************************/
/*                                                                 */
/*  Routines related to binary quadratic forms (for internal use)  */
/*                                                                 */
/*******************************************************************/
/* output canonical representative wrt projection Cl^+ --> Cl (a > 0) */
static GEN
qfr3_canon(GEN x, struct qfr_data *S)
{
  GEN a = gel(x,1), c = gel(x,3);
  if (signe(a) < 0) {
    if (absi_equal(a,c)) return qfr3_rho(x, S);
    setsigne(a, 1);
    setsigne(c,-1);
  }
  return x;
}
static GEN
qfr5_canon(GEN x, struct qfr_data *S)
{
  GEN a = gel(x,1), c = gel(x,3);
  if (signe(a) < 0) {
    if (absi_equal(a,c)) return qfr5_rho(x, S);
    setsigne(a, 1);
    setsigne(c,-1);
  }
  return x;
}
static GEN
QFR5_comp(GEN x,GEN y, struct qfr_data *S)
{ return qfr5_canon(qfr5_comp(x,y,S), S); }
static GEN
QFR3_comp(GEN x, GEN y, struct qfr_data *S)
{ return qfr3_canon(qfr3_comp(x,y,S), S); }

/* compute rho^n(x) */
static GEN
qrf5_rho_pow(GEN x, long n, struct qfr_data *S)
{
  long i;
  pari_sp av = avma, lim = stack_lim(av, 1);
  for (i=1; i<=n; i++)
  {
    x = qfr5_rho(x,S);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"qrf5_rho_pow");
      x = gerepilecopy(av, x);
    }
  }
  return gerepilecopy(av, x);
}

static GEN
qfr5_pf(struct qfr_data *S, long p, long prec)
{
  GEN y = primeform_u(S->D,p);
  return qfr5_canon(qfr5_red(qfr_to_qfr5(y,prec), S), S);
}

static GEN
qfr3_pf(struct qfr_data *S, long p)
{
  GEN y = primeform_u(S->D,p);
  return qfr3_canon(qfr3_red(y, S), S);
}

#define qfi_pf primeform_u

/* Warning: ex[0] not set in general */
static GEN
init_form(struct buch_quad *B, long *ex,
          GEN (*comp)(GEN,GEN,struct qfr_data *S))
{
  long i, l = lg(B->powsubFB);
  GEN F = NULL;
  for (i=1; i<l; i++)
    if (ex[i])
    {
      GEN t = gmael(B->powsubFB,i,ex[i]);
      F = F? comp(F, t, B->QFR): t;
    }
  return F;
}
static GEN
qfr5_factorback(struct buch_quad *B, long *ex) { return init_form(B, ex, &QFR5_comp); }

static GEN
QFI_comp(GEN x, GEN y, struct qfr_data *S) { (void)S; return qficomp(x,y); }

static GEN
qfi_factorback(struct buch_quad *B, long *ex) { return init_form(B, ex, &QFI_comp); }

static GEN
random_form(struct buch_quad *B, GEN ex,
            GEN (*comp)(GEN,GEN, struct qfr_data *S))
{
  long i, l = lg(ex);
  pari_sp av = avma;
  GEN F;
  for(;;)
  {
    for (i=1; i<l; i++) ex[i] = random_bits(RANDOM_BITS);
    if ((F = init_form(B, ex, comp))) return F;
    avma = av;
  }
}
static GEN
qfr3_random(struct buch_quad *B,GEN ex){ return random_form(B, ex, &QFR3_comp); }
static GEN
qfi_random(struct buch_quad *B,GEN ex) { return random_form(B, ex, &QFI_comp); }

/*******************************************************************/
/*                                                                 */
/*                     Common subroutines                          */
/*                                                                 */
/*******************************************************************/
double
check_bach(double cbach, double B)
{
  if (cbach >= B)
   pari_err(talker,"sorry, couldn't deal with this field. PLEASE REPORT");
  if (cbach <= 0.3)
    cbach *= 2;
  else
    cbach += 0.2;
  if (cbach > B) cbach = B;
  if (DEBUGLEVEL) fprintferr("\n*** Bach constant: %f\n", cbach);
  return cbach;
}

/* Is |q| <= p ? */
static int
isless_iu(GEN q, ulong p) {
  long l = lgefint(q);
  return l==2 || (l == 3 && (ulong)q[2] <= p);
}

static long
factorquad(struct buch_quad *B, GEN f, long nFB, ulong limp)
{
  ulong X;
  long i, lo = 0;
  GEN x = gel(f,1), FB = B->FB, P = B->primfact, E = B->exprimfact;

  for (i=1; lgefint(x) > 3; i++)
  {
    ulong p = (ulong)FB[i], r;
    GEN q = diviu_rem(x, p, &r);
    if (!r)
    {
      long k = 0;
      do { k++; x = q; q = diviu_rem(x, p, &r); } while (!r);
      lo++; P[lo] = p; E[lo] = k;
    }
    if (isless_iu(q,p)) {
      if (lgefint(x) == 3) { X = (ulong)x[2]; goto END; }
      return 0;
    }
    if (i == nFB) return 0;
  }
  X = (ulong)x[2];
  if (X == 1) { P[0] = 0; return 1; }
  for (;; i++)
  { /* single precision affair, split for efficiency */
    ulong p = (ulong)FB[i];
    ulong q = X / p, r = X % p; /* gcc makes a single div */
    if (!r)
    {
      long k = 0;
      do { k++; X = q; q = X / p; r = X % p; } while (!r);
      lo++; P[lo] = p; E[lo] = k;
    }
    if (q <= p) break;
    if (i == nFB) return 0;
  }
END:
  if (X > B->limhash) return 0;
  if (X != 1 && X <= limp)
  {
    if (B->badprim && ugcd(X, umodiu(B->badprim,X)) > 1) return 0;
    lo++; P[lo] = X; E[lo] = 1;
    X = 1;
  }
  P[0] = lo; return X;
}

/* Check for a "large prime relation" involving q; q may not be prime */
static long *
largeprime(struct buch_quad *B, long q, long *ex, long np, long nrho)
{
  const long hashv = hash(q);
  long *pt, i, l = lg(B->subFB);

  for (pt = B->hashtab[hashv]; ; pt = (long*) pt[0])
  {
    if (!pt)
    {
      pt = (long*) pari_malloc((l+3) * sizeof(long));
      *pt++ = nrho; /* nrho = pt[-3] */
      *pt++ = np;   /* np   = pt[-2] */
      *pt++ = q;    /* q    = pt[-1] */
      pt[0] = (long)B->hashtab[hashv];
      for (i=1; i<l; i++) pt[i]=ex[i];
      B->hashtab[hashv]=pt; return NULL;
    }
    if (pt[-1] == q) break;
  }
  for(i=1; i<l; i++)
    if (pt[i] != ex[i]) return pt;
  return (pt[-2]==np)? NULL: pt;
}

static void
clearhash(long **hash)
{
  long *pt;
  long i;
  for (i=0; i<HASHT; i++) {
    for (pt = hash[i]; pt; ) {
      void *z = (void*)(pt - 3);
      pt = (long*) pt[0]; pari_free(z);
    }
    hash[i] = NULL;
  }
}

/* p | conductor of order of disc D ? */
static int
is_bad(GEN D, ulong p)
{
  pari_sp av = avma;
  int r;
  if (p == 2)
  {
    r = mod16(D) >> 1;
    if (r && signe(D) < 0) r = 8-r;
    return (r < 4);
  }
  r = (remii(D, muluu(p,p)) == gen_0); /* p^2 | D ? */
  avma = av; return r;
}

/* create B->FB, B->numFB; set B->badprim. Return L(kro_D, 1) */
static GEN
FBquad(struct buch_quad *B, long C2, long C1, GRHcheck_t *S)
{
  GEN Res = real_1(DEFAULTPREC), D = B->QFR->D;
  double L = log((double)C2), SA = 0, SB = 0;
  long i, p, s, LIM;
  pari_sp av;
  byteptr d = diffptr;

  B->numFB = cgetg(C2+1, t_VECSMALL);
  B->FB    = cgetg(C2+1, t_VECSMALL);
  av = avma;
  B->KC = 0; i = 0;
  maxprime_check((ulong)C2);
  B->badprim = gen_1;
  for (p = 0;;) /* p <= C2 */
  {
    NEXT_PRIME_VIADIFF(p, d);
    if (!B->KC && p > C1) B->KC = i;
    if (p > C2) break;
    s = krois(D,p);
    if (s) Res = mulur(p, divru(Res, p - s));
    switch (s)
    {
      case -1: break; /* inert */
      case  0: /* ramified */
	if (is_bad(D, (ulong)p)) { B->badprim = muliu(B->badprim, p); break; }
	/* fall through */
      default:  /* split */
	i++; B->numFB[p] = i; B->FB[i] = p; break;
    }
    if (S)
    {
      double logp = log((double)p);
      double logNP = s < 0? 2*logp: logp;
      double q = s < 0? 1/(double)p: 1/sqrt((double)p);
      double A = logNP * q, B = logNP * A;
      long M = (long)(L/logNP);
      if (M > 1)
      {
	double inv1_q = 1 / (1-q);
	A *= (1 - pow(q, M)) * inv1_q;
	B *= (1 - pow(q, M)*(M+1 - M*q)) * inv1_q * inv1_q;
      }
      if (s > 0) { SA += 2 * A; SB += 2 * B; } else { SA += A; SB += B; }
    }
  }
  if (!B->KC) return NULL;
  if (!GRHok(S, L, SA, SB)) return NULL;
  B->KC2 = i;
  setlg(B->FB, B->KC2+1);
  if (DEBUGLEVEL)
  {
    msgtimer("factor base");
    if (DEBUGLEVEL>7) fprintferr("FB = %Ps\n", B->FB);
  }
  LIM = (expi(D) < 16)? 100: 1000;
  while (p < LIM)
  {
    s = krois(D,p);
    Res = mulur(p, divru(Res, p - s));
    NEXT_PRIME_VIADIFF(p, d);
  }
  if (B->badprim != gen_1)
    gerepileall(av, 2, &Res, &B->badprim);
  else
  {
    B->badprim = NULL;
    Res = gerepileuptoleaf(av, Res);
  }
  return Res;
}

/* create B->vperm, return B->subFB */
static GEN
subFBquad(struct buch_quad *B, GEN D, double PROD)
{
  long i, j, minSFB, lgsub = 1, ino = 1, lv = B->KC+1;
  double prod = 1.;
  pari_sp av;
  GEN no;

  minSFB = (expi(D) > 15)? 3: 2;
  B->vperm = cgetg(lv, t_VECSMALL);
  av = avma;
  no    = cgetg(lv, t_VECSMALL);
  for (j = 1; j < lv; j++)
  {
    ulong p = B->FB[j];
    if (!umodiu(D, p)) no[ino++] = j; /* ramified */
    else
    {
      B->vperm[lgsub++] = j;
      prod *= p;
      if (lgsub > minSFB && prod > PROD) break;
    }
  }
  if (j == lv) return NULL;
  i = lgsub;
  for (j = 1; j < ino;i++,j++) B->vperm[i] = no[j];
  for (     ; i < lv; i++)     B->vperm[i] = i;
  if (DEBUGLEVEL) msgtimer("B->subFBquad (%ld elt.)", lgsub-1);
  no = gclone(vecslice(B->vperm, 1, lgsub-1));
  avma = av; return no;
}

/* assume n >= 1, x[i][j] = B->subFB[i]^j, for j = 1..n */
static GEN
powsubFBquad(struct buch_quad *B, long n)
{
  pari_sp av = avma;
  long i,j, l = lg(B->subFB);
  GEN F, y, x = cgetg(l, t_VEC), D = B->QFR->D;

  if (B->PRECREG) /* real */
  {
    for (i=1; i<l; i++)
    {
      F = qfr5_pf(B->QFR, B->FB[B->subFB[i]], B->PRECREG);
      y = cgetg(n+1, t_VEC); gel(x,i) = y;
      gel(y,1) = F;
      for (j=2; j<=n; j++) gel(y,j) = QFR5_comp(gel(y,j-1), F, B->QFR);
    }
  }
  else /* imaginary */
  {
    for (i=1; i<l; i++)
    {
      F = qfi_pf(D, B->FB[B->subFB[i]]);
      y = cgetg(n+1, t_VEC); gel(x,i) = y;
      gel(y,1) = F;
      for (j=2; j<=n; j++) gel(y,j) = qficomp(gel(y,j-1), F);
    }
  }
  if (DEBUGLEVEL) msgtimer("B->powsubFBquad");
  x = gclone(x); avma = av; return x;
}

static void
sub_fact(struct buch_quad *B, GEN col, GEN F)
{
  GEN b = gel(F,2);
  long i;
  for (i=1; i<=B->primfact[0]; i++)
  {
    ulong p = B->primfact[i], k = B->numFB[p];
    long e = B->exprimfact[i];
    if (umodiu(b, p<<1) > p) e = -e;
    col[k] -= e;
  }
}
static void
add_fact(struct buch_quad *B, GEN col, GEN F)
{
  GEN b = gel(F,2);
  long i;
  for (i=1; i<=B->primfact[0]; i++)
  {
    ulong p = B->primfact[i], k = B->numFB[p];
    long e = B->exprimfact[i];
    if (umodiu(b, p<<1) > p) e = -e;
    col[k] += e;
  }
}

static GEN
get_clgp(struct buch_quad *B, GEN W, GEN *ptD, long prec)
{
  GEN res, init, u1, D = ZM_snf_group(W,NULL,&u1), Z = prec? real_0(prec): NULL;
  long i, j, l = lg(W), c = lg(D);

  if (DEBUGLEVEL) msgtimer("smith/class group");
  res=cgetg(c,t_VEC); init = cgetg(l,t_VEC);
  for (i=1; i<l; i++) gel(init,i) = primeform_u(B->QFR->D, B->FB[B->vperm[i]]);
  for (j=1; j<c; j++)
  {
    GEN g = NULL;
    if (prec)
    {
      for (i=1; i<l; i++)
      {
	GEN t, u = gcoeff(u1,i,j);
	if (!signe(u)) continue;
	t = qfr3_pow(gel(init,i), u, B->QFR);
	g = g? qfr3_comp(g, t, B->QFR): t;
      }
      g = qfr3_to_qfr(qfr3_canon(qfr3_red(g, B->QFR), B->QFR), Z);
    }
    else
    {
      for (i=1; i<l; i++)
      {
	GEN t, u = gcoeff(u1,i,j);
	if (!signe(u)) continue;
	t = powgi(gel(init,i), u);
	g = g? qficomp(g, t): t;
      }
    }
    gel(res,j) = g;
  }
  if (DEBUGLEVEL) msgtimer("generators");
  *ptD = D; return res;
}

static long
trivial_relations(struct buch_quad *B, GEN mat, GEN C)
{
  long i, j = 0;
  GEN col, D = B->QFR->D;
  for (i = 1; i <= B->KC; i++)
  { /* ramified prime ==> trivial relation */
    if (umodiu(D, B->FB[i])) continue;
    col = const_vecsmall(B->KC, 0);
    col[i] = 2; j++;
    gel(mat,j) = col;
    gel(C,j) = gen_0;
  }
  return j;
}

static void
dbg_all(const char *phase, long s, long n)
{
  fprintferr("\nTime %s rel [#rel/#test = %ld/%ld]: %ld\n", phase,s,n,timer2());
}

/* Imaginary Quadratic fields */

static void
imag_relations(struct buch_quad *B, long need, long *pc, long lim, ulong LIMC, GEN mat)
{
  long lgsub = lg(B->subFB), current = *pc, nbtest = 0, s = 0;
  long i, fpc;
  pari_sp av;
  GEN col, form, ex = cgetg(lgsub, t_VECSMALL);

  if (!current) current = 1;
  av = avma;
  for(;;)
  {
    if (s >= need) break;
    avma = av;
    form = qfi_random(B,ex);
    form = qficomp(form, qfi_pf(B->QFR->D, B->FB[current]));
    nbtest++; fpc = factorquad(B,form,B->KC,LIMC);
    if (!fpc)
    {
      if (DEBUGLEVEL>1) fprintferr(".");
      continue;
    }
    if (fpc > 1)
    {
      long *fpd = largeprime(B,fpc,ex,current,0);
      ulong b1, b2, p;
      GEN form2;
      if (!fpd)
      {
	if (DEBUGLEVEL>1) fprintferr(".");
	continue;
      }
      form2 = qficomp(qfi_factorback(B,fpd), qfi_pf(B->QFR->D, B->FB[fpd[-2]]));
      p = fpc << 1;
      b1 = umodiu(gel(form2,2), p);
      b2 = umodiu(gel(form,2),  p);
      if (b1 != b2 && b1+b2 != p) continue;

      col = gel(mat,++s);
      add_fact(B,col, form);
      (void)factorquad(B,form2,B->KC,LIMC);
      if (b1==b2)
      {
	for (i=1; i<lgsub; i++) col[B->subFB[i]] += fpd[i]-ex[i];
	sub_fact(B, col, form2); col[fpd[-2]]++;
      }
      else
      {
	for (i=1; i<lgsub; i++) col[B->subFB[i]] += -fpd[i]-ex[i];
	add_fact(B, col, form2); col[fpd[-2]]--;
      }
    }
    else
    {
      col = gel(mat,++s);
      for (i=1; i<lgsub; i++) col[B->subFB[i]] = -ex[i];
      add_fact(B, col, form);
    }
    col[current]--;
    if (++current > B->KC) current = 1;
  }
  if (DEBUGLEVEL) dbg_all("random", s, nbtest);
  *pc = current;
}

static int
imag_be_honest(struct buch_quad *B)
{
  long p, fpc, s = B->KC, nbtest = 0;
  GEN F, ex = cgetg(lg(B->subFB), t_VECSMALL);
  pari_sp av = avma;

  while (s<B->KC2)
  {
    p = B->FB[s+1]; if (DEBUGLEVEL) fprintferr(" %ld",p);
    F = qficomp(qfi_pf(B->QFR->D, p), qfi_random(B, ex));
    fpc = factorquad(B,F,s,p-1);
    if (fpc == 1) { nbtest=0; s++; }
    else
      if (++nbtest > 40) return 0;
    avma = av;
  }
  return 1;
}

/* Real Quadratic fields */

static void
real_relations(struct buch_quad *B, long need, long *pc, long lim, ulong LIMC, GEN mat, GEN C)
{
  long lgsub = lg(B->subFB), prec = B->PRECREG, current = *pc, nbtest=0, s=0;
  long i, fpc, endcycle, rhoacc, rho;
  /* in a 2nd phase, don't include FB[current] but run along the cyle
   * ==> get more units */
  int first = (current == 0);
  pari_sp av, av1, limstack;
  GEN d, col, form, form0, form1, ex = cgetg(lgsub, t_VECSMALL);

  if (!current) current = 1;
  if (lim > need) lim = need;
  av = avma; limstack = stack_lim(av,1);
  for(;;)
  {
    if (s >= need) break;
    if (first && s >= lim) {
      first = 0;
      if (DEBUGLEVEL) dbg_all("initial", s, nbtest);
    }
    avma = av; form = qfr3_random(B, ex);
    if (!first)
      form = QFR3_comp(form, qfr3_pf(B->QFR, B->FB[current]), B->QFR);
    av1 = avma;
    form0 = form; form1 = NULL;
    endcycle = rhoacc = 0;
    rho = -1;

CYCLE:
    if (endcycle || rho > 5000) continue;
    if (low_stack(limstack, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"real_relations");
      gerepileall(av1, form1? 2: 1, &form, &form1);
    }
    if (rho < 0) rho = 0; /* first time in */
    else
    {
      form = qfr3_rho(form, B->QFR); rho++;
      rhoacc++;
      if (first)
	endcycle = (absi_equal(gel(form,1),gel(form0,1))
	     && equalii(gel(form,2),gel(form0,2)));
      else
      {
	if (absi_equal(gel(form,1), gel(form,3))) /* a = -c */
	{
	  if (absi_equal(gel(form,1),gel(form0,1)) &&
		  equalii(gel(form,2),gel(form0,2))) continue;
	  form = qfr3_rho(form, B->QFR); rho++;
	}
	else
	  { setsigne(form[1],1); setsigne(form[3],-1); }
	if (equalii(gel(form,1),gel(form0,1)) &&
	    equalii(gel(form,2),gel(form0,2))) continue;
      }
    }
    nbtest++; fpc = factorquad(B,form,B->KC,LIMC);
    if (!fpc)
    {
      if (DEBUGLEVEL>1) fprintferr(".");
      goto CYCLE;
    }
    if (fpc > 1)
    { /* look for Large Prime relation */
      long *fpd = largeprime(B,fpc,ex,first? 0: current,rhoacc);
      ulong b1, b2, p;
      GEN form2;
      if (!fpd)
      {
	if (DEBUGLEVEL>1) fprintferr(".");
	goto CYCLE;
      }
      if (!form1)
      {
	form1 = qfr5_factorback(B,ex);
	if (!first)
          form1 = QFR5_comp(form1, qfr5_pf(B->QFR, B->FB[current], prec), B->QFR);
      }
      form1 = qrf5_rho_pow(form1, rho, B->QFR);
      rho = 0;

      form2 = qfr5_factorback(B,fpd);
      if (fpd[-2])
        form2 = QFR5_comp(form2, qfr5_pf(B->QFR, B->FB[fpd[-2]], prec), B->QFR);
      form2 = qrf5_rho_pow(form2, fpd[-3], B->QFR);
      if (!absi_equal(gel(form2,1),gel(form2,3)))
      {
	setsigne(form2[1], 1);
	setsigne(form2[3],-1);
      }
      p = fpc << 1;
      b1 = umodiu(gel(form2,2), p);
      b2 = umodiu(gel(form1,2), p);
      if (b1 != b2 && b1+b2 != p) goto CYCLE;

      col = gel(mat,++s);
      add_fact(B, col, form1);
      (void)factorquad(B,form2,B->KC,LIMC);
      if (b1==b2)
      {
	for (i=1; i<lgsub; i++) col[B->subFB[i]] += fpd[i]-ex[i];
	sub_fact(B,col, form2);
	if (fpd[-2]) col[fpd[-2]]++;
	d = qfr5_dist(subii(gel(form1,4),gel(form2,4)),
		      divrr(gel(form1,5),gel(form2,5)), prec);
      }
      else
      {
	for (i=1; i<lgsub; i++) col[B->subFB[i]] += -fpd[i]-ex[i];
	add_fact(B, col, form2);
	if (fpd[-2]) col[fpd[-2]]--;
	d = qfr5_dist(addii(gel(form1,4),gel(form2,4)),
		      mulrr(gel(form1,5),gel(form2,5)), prec);
      }
      if (DEBUGLEVEL) fprintferr(" %ldP",s);
    }
    else
    { /* standard relation */
      if (!form1)
      {
	form1 = qfr5_factorback(B, ex);
	if (!first)
          form1 = QFR5_comp(form1, qfr5_pf(B->QFR, B->FB[current], prec), B->QFR);
      }
      form1 = qrf5_rho_pow(form1, rho, B->QFR);
      rho = 0;

      col = gel(mat,++s);
      for (i=1; i<lgsub; i++) col[B->subFB[i]] = -ex[i];
      add_fact(B, col, form1);
      d = qfr5_dist(gel(form1,4), gel(form1,5), prec);
      if (DEBUGLEVEL) fprintferr(" %ld",s);
    }
    affrr(d, gel(C,s));
    if (first)
    {
      if (s >= lim) continue;
      goto CYCLE;
    }
    else
    {
      col[current]--;
      if (++current > B->KC) current = 1;
    }
  }
  if (DEBUGLEVEL) dbg_all("random", s, nbtest);
  *pc = current;
}

static int
real_be_honest(struct buch_quad *B)
{
  long p, fpc, s = B->KC, nbtest = 0;
  GEN F,F0, ex = cgetg(lg(B->subFB), t_VECSMALL);
  pari_sp av = avma;

  while (s<B->KC2)
  {
    p = B->FB[s+1]; if (DEBUGLEVEL) fprintferr(" %ld",p);
    F = QFR3_comp(qfr3_random(B, ex), qfr3_pf(B->QFR, p), B->QFR);
    for (F0 = F;;)
    {
      fpc = factorquad(B,F,s,p-1);
      if (fpc == 1) { nbtest=0; s++; break; }
      if (++nbtest > 40) return 0;
      F = qfr3_canon(qfr3_rho(F, B->QFR), B->QFR);
      if (equalii(gel(F,1),gel(F0,1))
       && equalii(gel(F,2),gel(F0,2))) break;
    }
    avma = av;
  }
  return 1;
}

static GEN
gcdreal(GEN a,GEN b)
{
  if (!signe(a)) return mpabs(b);
  if (!signe(b)) return mpabs(a);
  if (typ(a)==t_INT)
  {
    if (typ(b)==t_INT) return gcdii(a,b);
    a = itor(a, lg(b));
  }
  else if (typ(b)==t_INT)
    b = itor(b, lg(a));
  if (expo(a)<-5) return absr(b);
  if (expo(b)<-5) return absr(a);
  a = absr(a); b = absr(b);
  while (expo(b) >= -5  && signe(b))
  {
    long e;
    GEN r, q = gcvtoi(divrr(a,b),&e);
    if (e > 0) return NULL;
    r = subrr(a, mulir(q,b)); a = b; b = r;
  }
  return absr(a);
}

static int
get_R(struct buch_quad *B, GEN C, long sreg, GEN z, GEN *ptR)
{
  GEN R = gen_1;
  double c;
  long i;

  if (B->PRECREG)
  {
    R = mpabs(gel(C,1));
    for (i=2; i<=sreg; i++)
    {
      R = gcdreal(gel(C,i), R);
      if (!R) return fupb_PRECI;
    }
    if (gexpo(R) <= -3)
    {
      if (DEBUGLEVEL) fprintferr("regulator is zero.\n");
      return fupb_RELAT;
    }
    if (DEBUGLEVEL) fprintferr("#### Tentative regulator: %Ps\n",R);
  }
  c = gtodouble(gmul(z, R));
  if (c < 0.8 || c > 1.3) return fupb_RELAT;
  *ptR = R; return fupb_NONE;
}

static int
quad_be_honest(struct buch_quad *B)
{
  int r;
  if (B->KC2 <= B->KC) return 1;
  if (DEBUGLEVEL)
    fprintferr("be honest for primes from %ld to %ld\n", B->FB[B->KC+1],B->FB[B->KC2]);
  r = B->PRECREG? real_be_honest(B): imag_be_honest(B);
  if (DEBUGLEVEL) { fprintferr("\n"); msgtimer("be honest"); }
  return r;
}

GEN
Buchquad(GEN D, double cbach, double cbach2, long prec)
{
  pari_sp av0 = avma, av, av2;
  const long RELSUP = 5;
  long i, s, current, triv, nrelsup, nreldep, need, nsubFB;
  ulong LIMC, LIMC2, cp;
  GEN h, W, cyc, res, gen, dep, mat, C, extraC, B, R, resc, Res, z;
  double drc, lim, LOGD, LOGD2;
  GRHcheck_t G, *GRHcheck = &G;
  struct qfr_data QFR;
  struct buch_quad BQ;
  int FIRST = 1;

  check_quaddisc(D, &s, /*junk*/&i, "Buchquad");
  BQ.QFR = &QFR;
  QFR.D = D;
  if (s < 0)
  {
    if (cmpiu(QFR.D,4) <= 0)
    {
      GEN z = cgetg(5,t_VEC);
      gel(z,1) = gel(z,4) = gen_1; gel(z,2) = gel(z,3) = cgetg(1,t_VEC);
      return z;
    }
    BQ.PRECREG = 0;
  } else {
    BQ.PRECREG = maxss(prec+1, MEDDEFAULTPREC + 2*(expi(QFR.D)/BITS_IN_LONG));
  }
  if (DEBUGLEVEL) (void)timer2();
  BQ.primfact   = new_chunk(100);
  BQ.exprimfact = new_chunk(100);
  BQ.hashtab = (long**) new_chunk(HASHT);
  for (i=0; i<HASHT; i++) BQ.hashtab[i] = NULL;

  drc = fabs(gtodouble(QFR.D));
  LOGD = log(drc);
  LOGD2 = LOGD * LOGD;

  lim = sqrt(drc);
  /* resc = sqrt(D) w / 2^r1 (2pi)^r2 ~ hR / L(chi,1) */
  if (BQ.PRECREG) resc = dbltor(lim / 2.);
  else         resc = dbltor(lim / PI);
  if (!BQ.PRECREG) lim /= sqrt(3.);
  cp = (ulong)exp(sqrt(LOGD*log(LOGD)/8.0));
  if (cp < 20) cp = 20;
  if (cbach > 6.) {
    if (cbach2 < cbach) cbach2 = cbach;
    cbach = 6.;
  }
  if (cbach <= 0.) pari_err(talker,"Bach constant <= 0 in Buchquad");
  av = avma;
  BQ.powsubFB = BQ.subFB = NULL;
  init_GRHcheck(GRHcheck, 2, BQ.PRECREG? 2: 0, LOGD);

/* LIMC = Max(cbach*(log D)^2, exp(sqrt(log D loglog D) / 8)) */
START:
  if (!FIRST) cbach = check_bach(cbach,6.);
  FIRST = 0; avma = av;
  if (BQ.subFB) gunclone(BQ.subFB);
  if (BQ.powsubFB) gunclone(BQ.powsubFB);
  clearhash(BQ.hashtab);
  nreldep = nrelsup = 0;
  LIMC = (ulong)(cbach*LOGD2);
  if (LIMC < cp) { LIMC = cp; cbach = (double)LIMC / LOGD2; }
  LIMC2 = (ulong)(maxdd(cbach,cbach2)*LOGD2);
  if (LIMC2 < LIMC) LIMC2 = LIMC;
  if (BQ.PRECREG) qfr_data_init(QFR.D, BQ.PRECREG, &QFR);

  Res = FBquad(&BQ, LIMC2, LIMC, GRHcheck);
  if (!Res) goto START;
  GRHcheck = NULL;
  BQ.subFB = subFBquad(&BQ, QFR.D, lim + 0.5);
  if (!BQ.subFB) goto START;
  nsubFB = lg(BQ.subFB) - 1;
  BQ.powsubFB = powsubFBquad(&BQ,CBUCH+1);
  BQ.limhash = (LIMC & HIGHMASK)? (HIGHBIT>>1): LIMC*LIMC;

  need = BQ.KC + RELSUP - 2;
  current = 0;
  W = NULL;
  s = nsubFB + RELSUP;
  av2 = avma;

MORE:
  if ((nreldep & 3) == 1 || (nrelsup & 7) == 1) {
    if (DEBUGLEVEL) fprintferr("*** Changing sub factor base\n");
    gunclone(BQ.subFB);
    gunclone(BQ.powsubFB);
    BQ.subFB = gclone(vecslice(BQ.vperm, 1, nsubFB));
    BQ.powsubFB = powsubFBquad(&BQ,CBUCH+1);
    clearhash(BQ.hashtab);
  }
  need += 2;
  mat    = cgetg(need+1, t_MAT);
  extraC = cgetg(need+1, t_VEC);
  if (!W) { /* first time */
    C = extraC;
    triv = trivial_relations(&BQ, mat, C);
    if (DEBUGLEVEL) fprintferr("KC = %ld, need %ld relations\n", BQ.KC, need);
  } else {
    triv = 0;
    if (DEBUGLEVEL) fprintferr("...need %ld more relations\n", need);
  }
  if (BQ.PRECREG) {
    for (i = triv+1; i<=need; i++) {
      gel(mat,i) = const_vecsmall(BQ.KC, 0);
      gel(extraC,i) = cgetr(BQ.PRECREG);
    }
    real_relations(&BQ, need - triv, &current, s,LIMC,mat + triv,extraC + triv);
  } else {
    for (i = triv+1; i<=need; i++) {
      gel(mat,i) = const_vecsmall(BQ.KC, 0);
      gel(extraC,i) = gen_0;
    }
    imag_relations(&BQ, need - triv, &current, s,LIMC,mat + triv);
  }

  if (!W)
    W = hnfspec_i(mat,BQ.vperm,&dep,&B,&C,nsubFB);
  else
    W = hnfadd_i(W,BQ.vperm,&dep,&B,&C, mat,extraC);
  gerepileall(av2, 4, &W,&C,&B,&dep);
  need = lg(dep)>1? lg(dep[1])-1: lg(B[1])-1;
  if (need)
  {
    if (++nreldep > 15 && cbach < 1) goto START;
    goto MORE;
  }

  h = ZM_det_triangular(W);
  if (DEBUGLEVEL) fprintferr("\n#### Tentative class number: %Ps\n", h);

  z = mulrr(Res, resc); /* ~ hR if enough relations, a multiple otherwise */
  switch(get_R(&BQ, C, (lg(C)-1) - (lg(B)-1) - (lg(W)-1), divir(h,z), &R))
  {
    case fupb_PRECI:
      BQ.PRECREG = (BQ.PRECREG<<1)-2;
      cbach /= 2; goto START;

    case fupb_RELAT:
      if (++nrelsup <= 7 || cbach > 1) {
	need = minss(BQ.KC, nrelsup);
	if (cbach > 1 && nsubFB < 3 && lg(BQ.vperm) > 3) nsubFB++;
	goto MORE;
      }
      goto START;
  }
  /* DONE */
  if (!quad_be_honest(&BQ)) goto START;
  clearhash(BQ.hashtab);

  gen = get_clgp(&BQ,W,&cyc,BQ.PRECREG);
  gunclone(BQ.subFB);
  gunclone(BQ.powsubFB);
  res = cgetg(5,t_VEC);
  gel(res,1) = h;
  gel(res,2) = cyc;
  gel(res,3) = gen;
  gel(res,4) = R; return gerepilecopy(av0,res);
}

GEN
buchimag(GEN D, GEN c, GEN c2, GEN REL)
{ (void)REL; return Buchquad(D,gtodouble(c),gtodouble(c2),0); }

GEN
buchreal(GEN D, GEN flag, GEN c, GEN c2, GEN REL, long prec) {
  if (signe(flag)) pari_err(impl,"narrow class group");
  (void)REL; return Buchquad(D,gtodouble(c),gtodouble(c2),prec);
}

GEN
quadclassunit0(GEN x, long flag, GEN data, long prec)
{
  long lx;
  double c1 = 0.2, c2 = 0.2;

  if (!data) lx=1;
  else
  {
    lx = lg(data);
    if (typ(data)!=t_VEC || lx > 7)
      pari_err(talker,"incorrect parameters in quadclassunit");
    if (lx > 3) lx = 3;
  }
  switch(lx)
  {
    case 3: c2 = gtodouble(gel(data,2));
    case 2: c1 = gtodouble(gel(data,1));
  }
  if (flag) pari_err(impl,"narrow class group");
  return Buchquad(x,c1,c2,prec);
}
