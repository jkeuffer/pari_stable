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

/**************************************************************/
/*                                                            */
/*                        NUMBER FIELDS                       */
/*                                                            */
/**************************************************************/
#include "pari.h"
#include "paripriv.h"

int new_galois_format = 0;

void
checkrnf(GEN rnf)
{
  if (typ(rnf)!=t_VEC || lg(rnf)!=13) pari_err(typeer,"checkrnf");
}

GEN
checkbnf_i(GEN X)
{
  if (typ(X) == t_VEC)
    switch (lg(X))
    {
      case 11: return X;
      case 7:  return checkbnf_i(bnr_get_bnf(X));
    }
  return NULL;
}

GEN
checknf_i(GEN X)
{
  if (typ(X)==t_VEC)
    switch(lg(X))
    {
      case 10: return X;
      case 11: return checknf_i(bnf_get_nf(X));
      case 7:  return checknf_i(bnr_get_bnf(X));
      case 3: if (typ(gel(X,2)) == t_POLMOD) return checknf_i(gel(X,1));
    }
  return NULL;
}

GEN
checkbnf(GEN x)
{
  GEN bnf = checkbnf_i(x);
  if (!bnf)
  {
    if (checknf_i(x)) pari_err(talker,"please apply bnfinit first");
    pari_err(typeer,"checkbnf");
  }
  return bnf;
}

GEN
checknf(GEN x)
{
  GEN nf = checknf_i(x);
  if (!nf)
  {
    if (typ(x)==t_POL) pari_err(talker,"please apply nfinit first");
    pari_err(typeer,"checknf");
  }
  return nf;
}

void
checkbnr(GEN bnr)
{
  if (typ(bnr)!=t_VEC || lg(bnr)!=7)
    pari_err(talker,"incorrect bigray field");
  (void)checkbnf(bnr_get_bnf(bnr));
}

void
checkbnrgen(GEN bnr)
{
  checkbnr(bnr);
  if (lg(bnr[5])<=3)
    pari_err(talker,"please apply bnrinit(,,1) and not bnrinit(,)");
}

void
checksqmat(GEN x, long N)
{
  if (typ(x)!=t_MAT) pari_err(talker,"incorrect ideal");
  if (lg(x) == 1 || lg(x[1]) != N+1)
    pari_err(talker,"incorrect matrix for ideal");
}

GEN
checkbid_i(GEN bid)
{
  if (typ(bid)!=t_VEC || lg(bid)!=6 || lg(bid[1])!=3) return NULL;
  return bid;
}
void
checkbid(GEN bid)
{
  if (!checkbid_i(bid)) pari_err(typeer,"checkbid");
}

void
checkprid(GEN id)
{
  if (typ(id) != t_VEC || lg(id) != 6 || typ(id[2]) != t_COL)
    pari_err(talker,"incorrect prime ideal");
}
GEN
get_prid(GEN x)
{
  long lx;
  if (typ(x) != t_VEC) return NULL;
  lx = lg(x);
  if (lx == 3) { x = gel(x,1); lx = lg(x); }
  if (lx != 6 || typ(x[3]) != t_INT) return NULL;
  return x;
}

GEN
checknfelt_mod(GEN nf, GEN x, const char *s)
{
  GEN T = gel(x,1), a = gel(x,2);
  if (!RgX_equal_var(T, nf_get_pol(nf)))
    pari_err(talker, "incompatible modulus in %s:\n  mod = %Ps,\n  nf  = %Ps",
             s, a, T);
  return a;
}

void
check_ZKmodule(GEN x, const char *s)
{
  if (typ(x) != t_VEC || lg(x) < 3) pari_err(talker,"not a module in %s", s);
  if (typ(x[1]) != t_MAT) pari_err(talker,"not a matrix in %s", s);
  if (typ(x[2]) != t_VEC || lg(x[2]) != lg(x[1]))
    pari_err(talker,"not a correct ideal list in %s", s);
}

GEN
get_bnf(GEN x, long *t)
{
  switch(typ(x))
  {
    case t_POL: *t = typ_POL;  return NULL;
    case t_QUAD: *t = typ_Q  ; return NULL;
    case t_VEC:
      switch(lg(x))
      {
        case 5 : *t = typ_QUA; return NULL;
        case 6 :
          if (typ(x[1]) != t_VEC || typ(x[3]) != t_MAT) break;
          *t = typ_BID; return NULL;
        case 10: *t = typ_NF; return NULL;
        case 11: *t = typ_BNF; return x;
        case 7 : *t = typ_BNR;
          x = bnr_get_bnf(x); if (typ(x)!=t_VEC || lg(x)!=11) break;
          return x;
        case 9 :
          x = gel(x,2);
          if (typ(x) == t_VEC && lg(x) == 4) *t = typ_GAL;
          return NULL;
        case 13:
          *t = typ_RNF; return NULL;
        case 14: case 20:
          *t = typ_ELL; return NULL;
      }
  }
  *t = typ_NULL; return NULL;
}

GEN
get_nf(GEN x, long *t)
{
  switch(typ(x))
  {
    case t_POL : *t = typ_POL; return NULL;
    case t_QUAD: *t = typ_Q  ; return NULL;
    case t_VEC:
      switch(lg(x))
      {
        case 3:
          if (typ(x[2]) != t_POLMOD) break;
          return get_nf(gel(x,1),t);
        case 10: *t = typ_NF; return x;
        case 11: *t = typ_BNF;
          x = bnf_get_nf(x); if (typ(x)!=t_VEC || lg(x)!=10) break;
          return x;
        case 7 : *t = typ_BNR;
          x = bnr_get_bnf(x); if (typ(x)!=t_VEC || lg(x)!=11) break;
          x = bnf_get_nf(x);  if (typ(x)!=t_VEC || lg(x)!=10) break;
          return x;
        case 6 :
          if (typ(x[1]) != t_VEC || typ(x[3]) != t_MAT) break;
          *t = typ_BID; return NULL;
        case 9 :
          x = gel(x,2);
          if (typ(x) == t_VEC && lg(x) == 4) *t = typ_GAL;
          return NULL;
        case 13:
          *t = typ_RNF; return NULL;
        case 14: case 20:
          *t = typ_ELL; return NULL;
      }break;
  }
  *t = typ_NULL; return NULL;
}

long
nftyp(GEN x)
{
  switch(typ(x))
  {
    case t_POL : return typ_POL;
    case t_QUAD: return typ_Q;
    case t_VEC:
      switch(lg(x))
      {
        case 10: return typ_NF;
        case 11:
          x = bnf_get_nf(x); if (typ(x)!=t_VEC || lg(x)!=10) break;
          return typ_BNF;
        case 7 :
          x = bnr_get_bnf(x); if (typ(x)!=t_VEC || lg(x)!=11) break;
          x = bnf_get_nf(x);  if (typ(x)!=t_VEC || lg(x)!=10) break;
          return typ_BNR;
        case 6 :
          if (typ(x[1]) != t_VEC || typ(x[3]) != t_MAT) break;
          return typ_BID;
        case 9 :
          x = gel(x,2);
          if (typ(x) == t_VEC && lg(x) == 4) return typ_GAL;
        case 14: case 20:
          return typ_ELL;
      }break;
  }
  return typ_NULL;
}

/*************************************************************************/
/**                                                                     **/
/**                           GALOIS GROUP                              **/
/**                                                                     **/
/*************************************************************************/

/* exchange elements i and j in vector x */
static GEN
transroot(GEN x, int i, int j)
{ x = leafcopy(x); swap(gel(x,i), gel(x,j)); return x; }

GEN
tschirnhaus(GEN x)
{
  pari_sp av = avma, av2;
  long a, v = varn(x);
  GEN u, y = cgetg(5,t_POL);

  if (typ(x)!=t_POL) pari_err(notpoler,"tschirnhaus");
  if (lg(x) < 4) pari_err(constpoler,"tschirnhaus");
  if (v) { u = leafcopy(x); setvarn(u,0); x=u; }
  y[1] = evalsigne(1)|evalvarn(0);
  do
  {
    a = random_bits(2); if (a==0) a  = 1; gel(y,4) = stoi(a);
    a = random_bits(3); if (a>=4) a -= 8; gel(y,3) = stoi(a);
    a = random_bits(3); if (a>=4) a -= 8; gel(y,2) = stoi(a);
    u = RgXQ_charpoly(y,x,v); av2 = avma;
  }
  while (degpol(RgX_gcd(u,RgX_deriv(u)))); /* while u not separable */
  if (DEBUGLEVEL>1)
    fprintferr("Tschirnhaus transform. New pol: %Ps",u);
  avma=av2; return gerepileupto(av,u);
}

/* Assume pol in Z[X], monic of degree n. Find L in Z such that
 * POL = L^(-n) pol(L x) is monic in Z[X]. Return POL and set *ptk = L.
 * No GC. */
GEN
ZX_Z_normalize(GEN pol, GEN *ptk)
{
  long i,j, sk, n = degpol(pol); /* > 0 */
  GEN k, fa, P, E, a, POL;

  a = pol + 2; k = gel(a,n-1); /* a[i] = coeff of degree i */
  for (i = n-2; i >= 0; i--)
  {
    k = gcdii(k, gel(a,i));
    if (is_pm1(k)) { if (ptk) *ptk = gen_1; return pol; }
  }
  sk = signe(k);
  if (!sk) { if (ptk) *ptk = gen_1; return pol; /* monomial! */ }
  if (sk < 0) k = absi(k);
  fa = Z_factor_limit(k, 0); k = gen_1;
  P = gel(fa,1);
  E = gel(fa,2);
  POL = leafcopy(pol); a = POL+2;
  for (i = lg(P)-1; i > 0; i--)
  {
    GEN p = gel(P,i), pv, pvj;
    long vmin = itos(gel(E,i));
    /* find v_p(k) = min floor( v_p(a[i]) / (n-i)) */
    for (j=n-1; j>=0; j--)
    {
      long v;
      if (!signe(a[j])) continue;
      v = Z_pval(gel(a,j), p) / (n - j);
      if (v < vmin) vmin = v;
    }
    if (!vmin) continue;
    pvj = pv = powiu(p,vmin); k = mulii(k, pv);
    /* a[j] /= p^(v*(n-j)) */
    for (j=n-1; j>=0; j--)
    {
      if (j < n-1) pvj = mulii(pvj, pv);
      gel(a,j) = diviiexact(gel(a,j), pvj);
    }
  }
  if (ptk) *ptk = k; return POL;
}

/* Assume pol != 0 in Z[X]. Find C, L in Z such that POL = C pol(x/L) monic
 * in Z[X]. Return POL and set *ptlc = L. Wasteful (but correct) if pol is not
 * primitive: better if caller used Q_primpart already. No GC. */
GEN
ZX_primitive_to_monic(GEN pol, GEN *ptlc)
{
  long i,j, n = degpol(pol);
  GEN lc, fa, P, E, a, POL = leafcopy(pol);

  a = POL + 2; lc = gel(a,n);
  if (signe(lc) < 0) { POL = ZX_neg(POL); a = POL+2; lc = gel(a,n); }
  if (is_pm1(lc)) return ZX_Z_normalize(pol, ptlc);
  fa = Z_factor_limit(lc,0); lc = gen_1;
  P = gel(fa,1);
  E = gel(fa,2);
  for (i = lg(P)-1; i > 0; i--)
  {
    GEN p = gel(P,i), pk, pku;
    long v, j0, e = itos(gel(E,i)), k = e/n, d = k*n - e;

    if (d < 0) { k++; d += n; }
    /* k = ceil(e[i] / n); find d, k such that  p^d pol(x / p^k) monic */
    for (j=n-1; j>0; j--)
    {
      if (!signe(a[j])) continue;
      v = Z_pval(gel(a,j), p);
      while (v + d < k * j) { k++; d += n; }
    }
    pk = powiu(p,k); j0 = d/k;
    lc = mulii(lc, pk);

    pku = powiu(p,d - k*j0);
    /* a[j] *= p^(d - kj) */
    for (j=j0; j>=0; j--)
    {
      if (j < j0) pku = mulii(pku, pk);
      gel(a,j) = mulii(gel(a,j), pku);
    }
    j0++;
    pku = powiu(p,k*j0 - d);
    /* a[j] /= p^(kj - d) */
    for (j=j0; j<=n; j++)
    {
      if (j > j0) pku = mulii(pku, pk);
      gel(a,j) = diviiexact(gel(a,j), pku);
    }
  }
  POL = ZX_Z_normalize(POL, ptlc);
  if (ptlc) *ptlc = mul_denom(*ptlc, lc);
  return POL;
}
/* pol != 0 in Z[x], returns a monic polynomial POL in Z[x] generating the
 * same field: there exist C in Q, L in Z such that POL(x) = C pol(x/L).
 * Set *L = NULL if L = 1, and to L otherwise. No garbage collecting. */
GEN
ZX_to_monic(GEN pol, GEN *L)
{
  long n = lg(pol)-1;
  GEN lc = gel(pol,n);
  if (is_pm1(lc)) { *L = gen_1; return signe(lc) > 0? pol: ZX_neg(pol); }
  return ZX_primitive_to_monic(Q_primpart(pol), L);
}

/* x1*x2^2 + x2*x3^2 + x3*x4^2 + x4*x1^2 */
static GEN
F4(GEN x)
{
  return gadd(
    gmul(gel(x,1), gadd(gsqr(gel(x,2)), gmul(gel(x,4),gel(x,1)))),
    gmul(gel(x,3), gadd(gsqr(gel(x,4)), gmul(gel(x,2),gel(x,3)))));
}

static GEN
roots_to_ZX(GEN z, long *e)
{
  GEN a = roots_to_pol(z,0);
  GEN b = grndtoi(real_i(a),e);
  long e1 = gexpo(imag_i(a));
  if (e1 > *e) *e = e1;
  return b;
}

static GEN
polgaloisnames(long a, long b)
{
  const char * const t[]={"S1", "S2", "A3", "S3",
       "C(4) = 4", "E(4) = 2[x]2", "D(4)", "A4", "S4",
       "C(5) = 5", "D(5) = 5:2", "F(5) = 5:4", "A5", "S5",
       "C(6) = 6 = 3[x]2", "D_6(6) = [3]2", "D(6) = S(3)[x]2",
             "A_4(6) = [2^2]3", "F_18(6) = [3^2]2 = 3 wr 2",
             "2A_4(6) = [2^3]3 = 2 wr 3", "S_4(6d) = [2^2]S(3)",
             "S_4(6c) = 1/2[2^3]S(3)", "F_18(6):2 = [1/2.S(3)^2]2",
             "F_36(6) = 1/2[S(3)^2]2", "2S_4(6) = [2^3]S(3) = 2 wr S(3)",
             "L(6) = PSL(2,5) = A_5(6)", "F_36(6):2 = [S(3)^2]2 = S(3) wr 2",
             "L(6):2 = PGL(2,5) = S_5(6)", "A6", "S6",
       "C(7) = 7", "D(7) = 7:2", "F_21(7) = 7:3", "F_42(7) = 7:6",
             "L(7) = L(3,2)", "A7", "S7"};

   const long idx[]={0,1,2,4,9,14,30};
   return strtoGENstr(t[idx[a-1]+b-1]);
}

static GEN
galois_res(long d, long n, long s, long k)
{
  long kk = k;
  GEN z = cgetg(5,t_VEC);
  if (!new_galois_format)
  {
    switch (d) {
      case 6:
        kk = (k == 6 || k == 2)? 2: 1;
        break;
      case 3:
        kk = (k == 2)? 1: 2;
        break;
      default:
        kk = 1;
    }
  }
  gel(z,1) = stoi(n);
  gel(z,2) = stoi(s);
  gel(z,3) = stoi(kk);
  gel(z,4) = polgaloisnames(d,k);
  return z;
}

GEN
polgalois(GEN x, long prec)
{
  pari_sp av = avma, av1;
  long i,j,k,n,f,l,l2,e,e1,pr,ind;
  GEN x1,p1,p2,p3,p4,p5,w,z,ee;
  const int ind5[20]={2,5,3,4, 1,3,4,5, 1,5,2,4, 1,2,3,5, 1,4,2,3};
  const int ind6[60]={3,5,4,6, 2,6,4,5, 2,3,5,6, 2,4,3,6, 2,5,3,4,
                      1,4,5,6, 1,5,3,6, 1,6,3,4, 1,3,4,5, 1,6,2,5,
                      1,2,4,6, 1,5,2,4, 1,3,2,6, 1,2,3,5, 1,4,2,3};
  if (typ(x)!=t_POL) pari_err(notpoler,"galois");
  n=degpol(x); if (n<=0) pari_err(constpoler,"galois");
  if (n>11) pari_err(impl,"galois of degree higher than 11");
  x = Q_primpart(x);
  RgX_check_ZX(x, "galois");
  if (!ZX_is_irred(x)) pari_err(impl,"galois of reducible polynomial");

  if (n<4)
  {
    if (n == 1) { avma = av; return galois_res(n,1, 1,1); }
    if (n == 2) { avma = av; return galois_res(n,2,-1,1); }
    /* n = 3 */
    f = Z_issquare(ZX_disc(x));
    avma = av;
    return f? galois_res(n,3,1,1):
              galois_res(n,6,-1,2);
  }
  x1 = x = ZX_primitive_to_monic(x,NULL); av1=avma;
  if (n > 7) return galoisbig(x, prec);
  for(;;)
  {
    double cb = cauchy_bound(x);
    switch(n)
    {
      case 4: z = cgetg(7,t_VEC);
        prec = DEFAULTPREC + (long)(cb*(18./ LOG2 / BITS_IN_LONG));
        for(;;)
        {
          p1=cleanroots(x,prec);
          gel(z,1) = F4(p1);
          gel(z,2) = F4(transroot(p1,1,2));
          gel(z,3) = F4(transroot(p1,1,3));
          gel(z,4) = F4(transroot(p1,1,4));
          gel(z,5) = F4(transroot(p1,2,3));
          gel(z,6) = F4(transroot(p1,3,4));
          p5 = roots_to_ZX(z, &e); if (e <= -10) break;
          prec = (prec<<1)-2;
        }
        if (!ZX_is_squarefree(p5)) goto tchi;
        p2 = gel(ZX_factor(p5),1);
        switch(lg(p2)-1)
        {
          case 1: f = Z_issquare(ZX_disc(x)); avma = av;
            return f? galois_res(n,12,1,4): galois_res(n,24,-1,5);

          case 2: avma = av; return galois_res(n,8,-1,3);

          case 3: avma = av;
            return (degpol(gel(p2,1))==2)? galois_res(n,4,1,2)
                                         : galois_res(n,4,-1,1);

          default: pari_err(bugparier,"galois (bug1)");
        }

      case 5: z = cgetg(7,t_VEC);
        ee= cgetg(7,t_VECSMALL);
        w = cgetg(7,t_VECSMALL);
        prec = DEFAULTPREC + (long)(cb*(21. / LOG2/ BITS_IN_LONG));
        for(;;)
        {
          for(;;)
          {
            p1=cleanroots(x,prec);
            for (l=1; l<=6; l++)
            {
              p2=(l==1)?p1: ((l<6)?transroot(p1,1,l): transroot(p1,2,5));
              p3=gen_0;
              for (k=0,i=1; i<=5; i++,k+=4)
              {
                p5 = gadd(gmul(gel(p2,ind5[k]),gel(p2,ind5[k+1])),
                          gmul(gel(p2,ind5[k+2]),gel(p2,ind5[k+3])));
                p3 = gadd(p3, gmul(gsqr(gel(p2,i)),p5));
              }
              gel(w,l) = grndtoi(real_i(p3),&e);
              e1 = gexpo(imag_i(p3)); if (e1>e) e=e1;
              ee[l]=e; gel(z,l) = p3;
            }
            p5 = roots_to_ZX(z, &e); if (e <= -10) break;
            prec = (prec<<1)-2;
          }
          if (!ZX_is_squarefree(p5)) goto tchi;
          p3=gel(ZX_factor(p5),1);
          f=Z_issquare(ZX_disc(x));
          if (lg(p3)-1==1)
          {
            avma = av;
            return f? galois_res(n,60,1,4): galois_res(n,120,-1,5);
          }
          if (!f) { avma = av; return galois_res(n,20,-1,3); }

          pr = - (bit_accuracy(prec) >> 1);
          for (l=1; l<=6; l++)
            if (ee[l] <= pr && gequal0(poleval(p5,gel(w,l)))) break;
          if (l>6) pari_err(bugparier,"galois (bug4)");
          p2=(l==6)? transroot(p1,2,5):transroot(p1,1,l);
          p3=gen_0;
          for (i=1; i<=5; i++)
          {
            j = (i == 5)? 1: i+1;
            p3 = gadd(p3,gmul(gmul(gel(p2,i),gel(p2,j)),
                              gsub(gel(p2,j),gel(p2,i))));
          }
          p5=gsqr(p3); p4=grndtoi(real_i(p5),&e);
          e1 = gexpo(imag_i(p5)); if (e1>e) e=e1;
          if (e <= -10)
          {
            if (gequal0(p4)) goto tchi;
            f = Z_issquare(p4); avma = av;
            return f? galois_res(n,5,1,1): galois_res(n,10,1,2);
          }
          prec=(prec<<1)-2;
        }

      case 6: z = cgetg(7, t_VEC);
        prec = DEFAULTPREC + (long)(cb * (42. / LOG2 / BITS_IN_LONG));
        for(;;)
        {
          for(;;)
          {
            p1=cleanroots(x,prec);
            for (l=1; l<=6; l++)
            {
              p2=(l==1)?p1:transroot(p1,1,l);
              p3=gen_0; k=0;
              for (i=1; i<=5; i++) for (j=i+1; j<=6; j++)
              {
                p5=gadd(gmul(gel(p2,ind6[k]),gel(p2,ind6[k+1])),
                        gmul(gel(p2,ind6[k+2]),gel(p2,ind6[k+3])));
                p3=gadd(p3,gmul(gsqr(gmul(gel(p2,i),gel(p2,j))),p5));
                k += 4;
              }
              gel(z,l) = p3;
            }
            p5 = roots_to_ZX(z, &e); if (e <= -10) break;
            prec=(prec<<1)-2;
          }
          if (!ZX_is_squarefree(p5)) goto tchi;
          p2=gel(ZX_factor(p5),1);
          switch(lg(p2)-1)
          {
            case 1:
              z = cgetg(11,t_VEC); ind=0;
              p3=gadd(gmul(gmul(gel(p1,1),gel(p1,2)),gel(p1,3)),
                      gmul(gmul(gel(p1,4),gel(p1,5)),gel(p1,6)));
              gel(z,++ind) = p3;
              for (i=1; i<=3; i++)
                for (j=4; j<=6; j++)
                {
                  p2=transroot(p1,i,j);
                  p3=gadd(gmul(gmul(gel(p2,1),gel(p2,2)),gel(p2,3)),
                          gmul(gmul(gel(p2,4),gel(p2,5)),gel(p2,6)));
                  gel(z,++ind) = p3;
                }
              p5 = roots_to_ZX(z, &e);
              if (e <= -10)
              {
                if (!ZX_is_squarefree(p5)) goto tchi;
                p2 = gel(ZX_factor(p5),1);
                f = Z_issquare(ZX_disc(x));
                avma = av;
                if (lg(p2)-1==1)
                  return f? galois_res(n,360,1,15): galois_res(n,720,-1,16);
                else
                  return f? galois_res(n,36,1,10): galois_res(n,72,-1,13);
              }
              prec=(prec<<1)-2; break;

            case 2: l2=degpol(gel(p2,1)); if (l2>3) l2=6-l2;
              switch(l2)
              {
                case 1: f = Z_issquare(ZX_disc(x));
                  avma = av;
                  return f? galois_res(n,60,1,12): galois_res(n,120,-1,14);
                case 2: f = Z_issquare(ZX_disc(x));
                  if (f) { avma = av; return galois_res(n,24,1,7); }
                  p3 = (degpol(gel(p2,1))==2)? gel(p2,2): gel(p2,1);
                  f = Z_issquare(ZX_disc(p3));
                  avma = av;
                  return f? galois_res(n,24,-1,6): galois_res(n,48,-1,11);
                case 3: f = Z_issquare(ZX_disc(gel(p2,1)))
                         || Z_issquare(ZX_disc(gel(p2,2)));
                  avma = av;
                  return f? galois_res(n,18,-1,5): galois_res(n,36,-1,9);
              }
            case 3:
              for (l2=1; l2<=3; l2++)
                if (degpol(gel(p2,l2)) >= 3) p3 = gel(p2,l2);
              if (degpol(p3) == 3)
              {
                f = Z_issquare(ZX_disc(p3)); avma = av;
                return f? galois_res(n,6,-1,1): galois_res(n,12,-1,3);
              }
              else
              {
                f = Z_issquare(ZX_disc(x)); avma = av;
                return f? galois_res(n,12,1,4): galois_res(n,24,-1,8);
              }
            case 4: avma = av; return galois_res(n,6,-1,2);
            default: pari_err(bugparier,"galois (bug3)");
          }
        }

      case 7: z = cgetg(36,t_VEC);
        prec = DEFAULTPREC + (long)(cb*(7. / LOG2 / BITS_IN_LONG));
        for(;;)
        {
          ind = 0; p1=cleanroots(x,prec);
          for (i=1; i<=5; i++)
            for (j=i+1; j<=6; j++)
            {
              GEN t = gadd(gel(p1,i),gel(p1,j));
              for (k=j+1; k<=7; k++) gel(z,++ind) = gadd(t, gel(p1,k));
            }
          p5 = roots_to_ZX(z, &e); if (e <= -10) break;
          prec = (prec<<1)-2;
        }
        if (!ZX_is_squarefree(p5)) goto tchi;
        p2=gel(ZX_factor(p5),1);
        switch(lg(p2)-1)
        {
          case 1: f = Z_issquare(ZX_disc(x)); avma = av;
            return f? galois_res(n,2520,1,6): galois_res(n,5040,-1,7);
          case 2: f = degpol(gel(p2,1)); avma = av;
            return (f==7 || f==28)? galois_res(n,168,1,5): galois_res(n,42,-1,4);
          case 3: avma = av; return galois_res(n,21,1,3);
          case 4: avma = av; return galois_res(n,14,-1,2);
          case 5: avma = av; return galois_res(n,7,1,1);
          default: pari_err(bugparier,"galois (bug2)");
        }
    }
    tchi: avma = av1; x = tschirnhaus(x1);
  }
}

#undef _res

/* Evaluate pol in a using nfelt arithmetic and Horner rule */

GEN
nfpoleval(GEN nf, GEN pol, GEN a)
{
  pari_sp av=avma;
  long i=lg(pol)-1;
  GEN res;
  if (i==1) return gen_0;
  res = nf_to_scalar_or_basis(nf, gel(pol,i));
  for (i-- ; i>=2; i--)
    res = nfadd(nf, nfmul(nf, a, res), gel(pol,i));
  return gerepileupto(av, res);
}

GEN
FpX_FpC_nfpoleval(GEN nf, GEN pol, GEN a, GEN p)
{
  pari_sp av=avma;
  long i=lg(pol)-1, n=nf_get_degree(nf);
  GEN res, Ma;
  if (i==1) return zerocol(n);
  Ma = FpM_red(zk_multable(nf, a), p);
  res = scalarcol(gel(pol,i),n);
  for (i-- ; i>=2; i--)
  {
    res = FpM_FpC_mul(Ma, res, p);
    gel(res,1) = Fp_add(gel(res,1), gel(pol,i), p);
  }
  return gerepileupto(av, res);
}

static GEN
ZC_galoisapply(GEN nf, GEN x, GEN s)
{
  x = nf_to_scalar_or_alg(nf, x);
  if (typ(x) != t_POL) return scalarcol(x, degpol(nf_get_pol(nf)));
  return nfpoleval(nf,x,s);
}

static GEN
QX_galoisapplymod(GEN nf, GEN pol, GEN S, GEN p)
{
  GEN den, P = Q_remove_denom(pol,&den);
  GEN pe, pe1, denpe, R;
  if (den)
  {
    ulong e = Z_pval(den, p);
    pe = powiu(p, e); pe1 = mulii(pe, p);
    denpe = Fp_inv(diviiexact(den, pe), pe1);
  } else {
    pe = gen_1; pe1 = p; denpe = gen_1;
  }
  R = FpX_FpC_nfpoleval(nf, FpX_red(P, pe1), FpC_red(S, pe1), pe1);
  return gdivexact(FpC_Fp_mul(R, denpe, pe1), pe);
}

static GEN
pr_galoisapply(GEN nf, GEN pr, GEN aut)
{
  GEN p, b, u;
  if (typ(pr_get_tau(pr)) == t_INT) return pr; /* inert */
  p = pr_get_p(pr);
  u = QX_galoisapplymod(nf, coltoliftalg(nf, pr_get_gen(pr)), aut, p);
#if 1
  b = FpM_deplin(zk_multable(nf, u), p);
#else /* Slower */
  b = QX_galoisapplymod(nf, coltoliftalg(nf, pr_get_tau(pr)), aut, p);
#endif
  return mkvec5(p, u, gel(pr,3), gel(pr,4), b);
}

static GEN
fa_galoisapply(GEN nf, GEN fa, GEN aut)
{
  long i, lx = lg(fa);
  GEN G, g;
  if (typ(fa) != t_MAT) pari_err(typeer, "galoisapply");
  if (lx == 1) return cgetg(1, t_MAT);
  if (lx != 3) pari_err(typeer, "galoisapply");
  g = gel(fa,1); G = cgetg_copy(g, &lx);
  for (i = 1; i < lx; i++) gel(G,i) = galoisapply(nf, aut, gel(g,i));
  return mkmat2(g, ZC_copy(gel(fa,2)));
}

GEN
galoisapply(GEN nf, GEN aut, GEN x)
{
  pari_sp av = avma;
  long lx, j, N;
  GEN y, T;

  nf = checknf(nf); T = nf_get_pol(nf);
  aut = algtobasis(nf, aut);
  switch(typ(x))
  {
    case t_INT: case t_INTMOD: case t_FRAC:
      avma = av; return gcopy(x);

    case t_POLMOD: x = gel(x,2); /* fall through */
    case t_POL:
      y = basistoalg(nf,ZC_galoisapply(nf,x, aut));
      return gerepileupto(av,y);

    case t_VEC:
      switch(lg(x))
      {
        case 6: return gerepilecopy(av, pr_galoisapply(nf, x, aut));
        case 3: y = cgetg(3,t_VEC);
          gel(y,1) = galoisapply(nf, aut, gel(x,1));
          gel(y,2) = fa_galoisapply(nf, aut, gel(x,2));
          return gerepileupto(av, y);
      }
      break;

    case t_COL:
      return gerepileupto(av, ZC_galoisapply(nf,x, aut));

    case t_MAT:
      lx=lg(x); if (lx==1) return cgetg(1,t_MAT);
      N = degpol(T); if (lg(x[1])!=N+1) break;
      y = cgetg(lx,t_MAT);
      for (j=1; j<lx; j++) gel(y,j) = ZC_galoisapply(nf,gel(x,j), aut);
      return gerepileupto(av, idealhnf_shallow(nf,y));
  }
  pari_err(typeer,"galoisapply");
  return NULL; /* not reached */
}

/* x = relative polynomial nf = absolute nf, bnf = absolute bnf */
GEN
get_bnfpol(GEN x, GEN *bnf, GEN *nf)
{
  *bnf = checkbnf_i(x);
  *nf  = checknf_i(x);
  if (*nf) x = nf_get_pol(*nf);
  if (typ(x) != t_POL) pari_err(typeer,"get_bnfpol");
  return x;
}

GEN
get_nfpol(GEN x, GEN *nf)
{
  if (typ(x) == t_POL) { *nf = NULL; return x; }
  *nf = checknf(x); return nf_get_pol(*nf);
}

/* is isomorphism / inclusion (a \subset b) compatible with what we know about
 * basic invariants ? (degree, signature, discriminant) */
static int
tests_OK(GEN a, GEN nfa, GEN b, GEN nfb, long fliso)
{
  GEN da, db, fa, P, E, U;
  long i, nP, m = degpol(a), n = degpol(b), q = m / n; /* relative degree */

  if (m <= 0 || n <= 0) pari_err(constpoler, "nfisincl");
  if (fliso) { if (n != m) return 0; } else { if (n % m) return 0; }
  if (m == 1) return 1;

  if (nfa && nfb) /* both nf structures available */
  {
    long r1a = nf_get_r1(nfa), r1b = nf_get_r1(nfb) ;
    if (fliso)
      return (r1a == r1b && equalii(nf_get_disc(nfa), nf_get_disc(nfb)));
    else
      return (r1a <= r1b * q &&
              dvdii(nf_get_disc(nfb), powiu(nf_get_disc(nfa), q)));
  }
  da = nfa? nf_get_disc(nfa): ZX_disc(a);
  db = nfb? nf_get_disc(nfb): ZX_disc(b);
  if (fliso) return (gissquare(gdiv(da,db)) == gen_1);

  if (odd(q) && signe(da) != signe(db)) return 0;
  fa = Z_factor_limit(absi(da), 0);
  P = gel(fa,1);
  E = gel(fa,2); nP = lg(P) - 1;
  if (!nP) pari_err(talker,"inconsistent data in nfisincl");
  for (i=1; i<nP; i++)
    if (mod2(gel(E,i)) && !dvdii(db, powiu(gel(P,i),q))) return 0;
  U = gel(P,nP);
  if (expi(U) < 150) /* "unfactored" cofactor is small, finish */
  {
    if (cmpiu(U, maxprime()) > 0)
    {
      fa = Z_factor(U);
      P = gel(fa,1);
      E = gel(fa,2);
    }
    else
    {
      P = mkvec(U);
      E = mkvec(gel(E,nP));
    }
    nP = lg(P) - 1;
    for (i=1; i<=nP; i++)
      if (mod2(gel(E,i)) && !dvdii(db, powiu(gel(P,i),q))) return 0;
  }
  return 1;
}

/* if fliso test for isomorphism, for inclusion otherwise. */
static GEN
nfiso0(GEN a, GEN b, long fliso)
{
  pari_sp av = avma;
  long i, vb, lx;
  GEN nfa, nfb, y, la, lb;

  a = get_nfpol(a, &nfa);
  b = get_nfpol(b, &nfb);
  if (!nfa) { a = Q_primpart(a); RgX_check_ZX(a, "nsiso0"); }
  if (!nfb) { b = Q_primpart(b); RgX_check_ZX(b, "nsiso0"); }
  if (fliso && nfa && !nfb) { swap(a,b); nfb = nfa; nfa = NULL; }
  if (!tests_OK(a, nfa, b, nfb, fliso)) { avma = av; return gen_0; }

  if (nfb) lb = gen_1; else b = ZX_primitive_to_monic(b,&lb);
  if (nfa) la = gen_1; else a = ZX_primitive_to_monic(a,&la);
  a = leafcopy(a); setvarn(a,0);
  b = leafcopy(b); vb = varn(b);
  if (nfb)
  {
    if (vb == 0) nfb = gsubst(nfb, 0, pol_x(MAXVARN));
    y = lift_intern(nfroots(nfb,a));
  }
  else
  {
    if (vb == 0) setvarn(b, fetch_var());
    y = gel(polfnf(a,b),1); lx = lg(y);
    for (i=1; i<lx; i++)
    {
      GEN t = gel(y,i);
      if (degpol(t) != 1) { setlg(y,i); break; }
      gel(y,i) = gneg_i(lift_intern(gel(t,2)));
    }
    if (vb == 0) (void)delete_var();
    settyp(y, t_VEC);
    gen_sort_inplace(y, (void*)&cmp_RgX, &cmp_nodata, NULL);
  }
  lx = lg(y); if (lx==1) { avma=av; return gen_0; }
  for (i=1; i<lx; i++)
  {
    GEN t = gel(y,i);
    if (typ(t) == t_POL) setvarn(t, vb); else t = scalarpol(t, vb);
    if (lb != gen_1) t = RgX_unscale(t, lb);
    if (la != gen_1) t = RgX_Rg_div(t, la);
    gel(y,i) = t;
  }
  return gerepilecopy(av,y);
}

GEN
nfisisom(GEN a, GEN b) { return nfiso0(a,b,1); }

GEN
nfisincl(GEN a, GEN b) { return nfiso0(a,b,0); }

/*************************************************************************/
/**                                                                     **/
/**                               INITALG                               **/
/**                                                                     **/
/*************************************************************************/

GEN
get_roots(GEN x, long r1, long prec)
{
  GEN roo = (typ(x)!=t_POL)? leafcopy(x): cleanroots(x,prec);
  long i, ru = (lg(roo)-1 + r1) >> 1;

  for (i=r1+1; i<=ru; i++) gel(roo,i) = gel(roo, (i<<1)-r1);
  roo[0]=evaltyp(t_VEC)|evallg(ru+1); return roo;
}

GEN
nf_get_allroots(GEN nf)
{
  long i, j, n, r1, r2;
  GEN ro = nf_get_roots(nf), v;
  nf_get_sign(nf, &r1,&r2);
  n = r1 + (r2<<1);
  v = cgetg(n+1, t_VEC);
  for (i = 1; i <= r1; i++) gel(v,i) = gel(ro,i);
  for (j = i; j <= n; i++)
  {
    GEN z = gel(ro,i);
    gel(v,j++) = z;
    gel(v,j++) = mkcomplex(gel(z,1), gneg(gel(z,2)));
  }
  return v;
}

/* For internal use. compute trace(x mod pol), sym=polsym(pol,deg(pol)-1) */
GEN
quicktrace(GEN x, GEN sym)
{
  GEN p1 = gen_0;
  long i;

  if (typ(x) != t_POL) return gmul(x, gel(sym,1));
  if (signe(x))
  {
    sym--;
    for (i=lg(x)-1; i>1; i--)
      p1 = gadd(p1, gmul(gel(x,i),gel(sym,i)));
  }
  return p1;
}

static GEN
get_Tr(GEN mul, GEN x, GEN basden)
{
  GEN t, bas = gel(basden,1), den = gel(basden,2);
  long i, j, n = lg(bas)-1;
  GEN T = cgetg(n+1,t_MAT), TW = cgetg(n+1,t_COL), sym = polsym(x, n-1);

  gel(TW,1) = utoipos(n);
  for (i=2; i<=n; i++)
  {
    t = quicktrace(gel(bas,i), sym);
    if (den && den[i]) t = diviiexact(t,gel(den,i));
    gel(TW,i) = t; /* tr(w[i]) */
  }
  gel(T,1) = TW;
  for (i=2; i<=n; i++)
  {
    gel(T,i) = cgetg(n+1,t_COL); gcoeff(T,1,i) = gel(TW,i);
    for (j=2; j<=i; j++) /* Tr(W[i]W[j]) */
      gcoeff(T,i,j) = gcoeff(T,j,i) = ZV_dotproduct(gel(mul,j+(i-1)*n), TW);
  }
  return T;
}

/* return [bas[i]*denom(bas[i]), denom(bas[i])], denom 1 is given as NULL */
GEN
get_bas_den(GEN bas)
{
  GEN b,d,den, dbas = leafcopy(bas);
  long i, l = lg(bas);
  int power = 1;
  den = cgetg(l,t_VEC);
  for (i=1; i<l; i++)
  {
    b = Q_remove_denom(gel(bas,i), &d);
    gel(dbas,i) = b;
    gel(den,i) = d; if (d) power = 0;
  }
  if (power) den = NULL; /* power basis */
  return mkvec2(dbas, den);
}

/* Internal: nf partially filled. Require pol; fill zk, invzk, multable */
void
nf_set_multable(GEN nf, GEN bas, GEN basden)
{
  GEN T = nf_get_pol(nf), invbas, basM;
  long i,j, n = degpol(T);
  GEN w, den, mul = cgetg(n*n+1,t_MAT);

  if (typ(bas) == t_MAT)
  { basM = bas; bas = RgM_to_RgXV(basM, varn(T)); }
  else
    basM = RgXV_to_RgM(bas, n);
  gel(nf,7) = bas;
  gel(nf,8) = invbas = QM_inv(basM, gen_1);
  gel(nf,9) = mul;

  if (!basden) basden = get_bas_den(nf_get_zk(nf)); /*integral basis*/
  w   = gel(basden,1);
  den = gel(basden,2);
  /* i = 1 split for efficiency, assume w[1] = 1 */
  for (j=1; j<=n; j++)
    gel(mul,j) = gel(mul,1+(j-1)*n) = col_ei(n, j);
  for (i=2; i<=n; i++)
    for (j=i; j<=n; j++)
    {
      pari_sp av = avma;
      GEN z = (i == j)? ZXQ_sqr(gel(w,i), T): ZXQ_mul(gel(w,i),gel(w,j), T);
      z = mulmat_pol(invbas, z); /* integral column */
      if (den)
      {
        GEN d = mul_denom(gel(den,i), gel(den,j));
        if (d) z = ZC_Z_divexact(z, d);
      }
      gel(mul,j+(i-1)*n) = gel(mul,i+(j-1)*n) = gerepileupto(av,z);
    }
}

/* as get_Tr, mul_table not precomputed */
static GEN
make_Tr(GEN x, GEN basden)
{
  long i,j, n = degpol(x);
  GEN c, t, d;
  GEN T   = cgetg(n+1,t_MAT);
  GEN sym = polsym(x, n-1);
  GEN w   = gel(basden,1); /* W[i] = w[i]/den[i] */
  GEN den = gel(basden,2);
  /* assume W[1] = 1, case i = 1 split for efficiency */
  c = cgetg(n+1,t_COL); gel(T,1) = c;
  gel(c, 1) = utoipos(n);
  for (j=2; j<=n; j++)
  {
    pari_sp av = avma;
    t = quicktrace(gel(w,j), sym);
    if (den)
    {
      d = gel(den,j);
      if (d) t = diviiexact(t, d);
    }
    gel(c,j) = gerepileuptoint(av, t);
  }
  for (i=2; i<=n; i++)
  {
    c = cgetg(n+1,t_COL); gel(T,i) = c;
    for (j=1; j<i ; j++) gel(c,j) = gcoeff(T,i,j);
    for (   ; j<=n; j++)
    {
      pari_sp av = avma;
      t = (i == j)? ZXQ_sqr(gel(w,i), x): ZXQ_mul(gel(w,i),gel(w,j), x);
      t = quicktrace(t, sym);
      if (den)
      {
        d = mul_denom(gel(den,i),gel(den,j));
        if (d) t = diviiexact(t, d);
      }
      gel(c,j) = gerepileuptoint(av, t); /* Tr (W[i]W[j]) */
    }
  }
  return T;
}

/* compute roots so that _absolute_ accuracy of M >= prec [also holds for G] */
static void
get_roots_for_M(nffp_t *F)
{
  long n, eBD, PREC;

  if (F->extraprec < 0)
  { /* not initialized yet */
    double er;
    n = degpol(F->x);
    eBD = 1 + gexpo(gel(F->basden,1));
    er  = F->ro? (1+gexpo(F->ro)): cauchy_bound(F->x)/LOG2;
    if (er < 0) er = 0;
    F->extraprec = (long)((n*er + eBD + log2(n)) / BITS_IN_LONG);
  }

  PREC = F->prec + F->extraprec;
  if (F->ro && gprecision(gel(F->ro,1)) >= PREC) return;
  F->ro = get_roots(F->x, F->r1, PREC);
}

/* [bas[i]/den[i]]= integer basis. roo = real part of the roots */
static void
make_M(nffp_t *F, int trunc)
{
  GEN bas = gel(F->basden,1), den = gel(F->basden,2), ro = F->ro;
  GEN m, d, M;
  long i, j, l = lg(ro), n = lg(bas);
  M = cgetg(n,t_MAT);
  gel(M,1) = const_col(l-1, gen_1); /* bas[1] = 1 */
  for (j=2; j<n; j++)
  {
    m = cgetg(l,t_COL); gel(M,j) = m;
    for (i=1; i<l; i++) gel(m,i) = poleval(gel(bas,j), gel(ro,i));
  }
  if (den)
  {
    GEN invd, rd = cgetr(F->prec + F->extraprec);
    for (j=2; j<n; j++)
    {
      d = gel(den,j); if (!d) continue;
      m = gel(M,j); affir(d,rd); invd = invr(rd);
      for (i=1; i<l; i++) gel(m,i) = gmul(gel(m,i), invd);
    }
  }

  if (trunc && gprecision(M) > F->prec)
  {
    M     = gprec_w(M, F->prec);
    F->ro = gprec_w(ro,F->prec);
  }
  if (DEBUGLEVEL>4) msgtimer("matrix M");
  F->M = M;
}

/* return G real such that G~ * G = T_2 */
static void
make_G(nffp_t *F)
{
  GEN G, M = F->M;
  long i, j, k, r1 = F->r1, l = lg(M);

  G = cgetg(l, t_MAT);
  for (j=1; j<l; j++)
  {
    GEN g = cgetg(l, t_COL);
    GEN m = gel(M,j);
    gel(G,j) = g;
    for (k=i=1; i<=r1; i++) g[k++] = m[i];
    for (     ; k < l; i++)
    {
      GEN r = gel(m,i);
      if (typ(r) == t_COMPLEX)
      {
        gel(g,k++) = mpadd(gel(r,1), gel(r,2));
        gel(g,k++) = mpsub(gel(r,1), gel(r,2));
      }
      else
      {
        gel(g,k++) = r;
        gel(g,k++) = r;
      }
    }
  }
  F->G = G;
}

static void
make_M_G(nffp_t *F, int trunc)
{
  get_roots_for_M(F);
  make_M(F, trunc);
  make_G(F);
}

void
remake_GM(GEN nf, nffp_t *F, long prec)
{
  F->x  = nf_get_pol(nf);
  F->ro = NULL;
  F->r1 = nf_get_r1(nf);
  F->basden = get_bas_den(nf_get_zk(nf));
  F->extraprec = -1;
  F->prec = prec; make_M_G(F, 1);
}

static void
nffp_init(nffp_t *F, nfbasic_t *T, GEN ro, long prec)
{
  F->x  = T->x;
  F->ro = ro;
  F->r1 = T->r1;
  if (!T->basden) T->basden = get_bas_den(T->bas);
  F->basden = T->basden;
  F->extraprec = -1;
  F->prec = prec;
}

static void
get_nf_fp_compo(nfbasic_t *T, nffp_t *F, GEN ro, long prec)
{
  nffp_init(F,T,ro,prec);
  make_M_G(F, 1);
}

static GEN
get_sign(long r1, long n) { return mkvec2s(r1, (n-r1)>>1); }

GEN
nfbasic_to_nf(nfbasic_t *T, GEN ro, long prec)
{
  GEN nf = cgetg(10,t_VEC);
  GEN x = T->x, absdK, Tr, D, TI, A, dA, MDI, mat = cgetg(8,t_VEC);
  long n = degpol(T->x);
  nffp_t F;
  get_nf_fp_compo(T, &F, ro, prec);

  gel(nf,1) = T->x;
  gel(nf,2) = get_sign(T->r1, n);
  gel(nf,3) = T->dK;
  gel(nf,4) = T->index;
  gel(nf,6) = F.ro;
  gel(nf,5) = mat;

  gel(mat,1) = F.M;
  gel(mat,2) = F.G;

  nf_set_multable(nf, T->bas, F.basden);
  if (DEBUGLEVEL) msgtimer("mult. table");

  Tr = get_Tr(gel(nf,9), x, F.basden);
  absdK = T->dK; if (signe(absdK) < 0) absdK = negi(absdK);
  TI = ZM_inv(Tr, absdK); /* dK T^-1 */
  A = Q_primitive_part(TI, &dA);
  gel(mat,6) = A; /* primitive part of codifferent, dA its content */
  dA = dA? diviiexact(absdK, dA): absdK;
  A = ZM_hnfmodid(A, dA);
  MDI = idealtwoelt(nf, A);
  gel(MDI,2) = zk_scalar_or_multable(nf, gel(MDI,2));
  gel(mat,7) = MDI;
  if (is_pm1(T->index)) /* principal ideal (x'), whose norm is |dK| */
  {
    D = zk_scalar_or_multable(nf, ZX_deriv(x));
    if (typ(D) == t_MAT) D = ZM_hnfmod(D, absdK);
  }
  else
    D = RgM_Rg_mul(idealinv(nf, A), dA);
  gel(mat,3) = RM_round_maxrank(F.G);
  gel(mat,4) = Tr;
  gel(mat,5) = D;
  if (DEBUGLEVEL) msgtimer("matrices");
  return nf;
}

static GEN
hnffromLLL(GEN nf)
{
  GEN d, x;
  x = RgXV_to_RgM(nf_get_zk(nf), nf_get_degree(nf));
  x = Q_remove_denom(x, &d);
  if (!d) return x; /* power basis */
  return RgM_solve(ZM_hnfmodid(x, d), x);
}

static GEN
nfbasechange(GEN u, GEN x)
{
  long i,lx;
  GEN y;
  switch(typ(x))
  {
    case t_COL: /* nfelt */
      return RgM_RgC_mul(u, x);

    case t_MAT: /* ideal */
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = RgM_RgC_mul(u, gel(x,i));
      break;

    case t_VEC: /* pr */
      checkprid(x); y = leafcopy(x);
      gel(y,2) = RgM_RgC_mul(u, gel(y,2));
      gel(y,5) = RgM_RgC_mul(u, gel(y,5));
      break;
    default: y = x;
  }
  return y;
}

GEN
nffromhnfbasis(GEN nf, GEN x)
{
  long tx = typ(x);
  pari_sp av = avma;
  GEN u;
  if (!is_vec_t(tx)) return gcopy(x);
  nf = checknf(nf);
  u = hnffromLLL(nf);
  return gerepilecopy(av, nfbasechange(u, x));
}

GEN
nftohnfbasis(GEN nf, GEN x)
{
  long tx = typ(x);
  pari_sp av = avma;
  GEN u;
  if (!is_vec_t(tx)) return gcopy(x);
  nf = checknf(nf);
  u = ZM_inv(hnffromLLL(nf), gen_1);
  return gerepilecopy(av, nfbasechange(u, x));
}

/* set *pro to roots of T->x */
static GEN
get_red_G(nfbasic_t *T, GEN *pro)
{
  GEN G, u, u0 = NULL;
  pari_sp av;
  long i, prec, extraprec, n = degpol(T->x);
  nffp_t F;

  extraprec = (long) (0.25 * n / (sizeof(long) / 4));
  prec = DEFAULTPREC + extraprec;
  nffp_init(&F, T, NULL, prec);
  av = avma;
  for (i=1; ; i++)
  {
    F.prec = prec; make_M_G(&F, 0); G = F.G;
    if (u0) G = RgM_mul(G, u0);
    if (DEBUGLEVEL)
      fprintferr("get_red_G: starting LLL, prec = %ld (%ld + %ld)\n",
                  prec + F.extraprec, prec, F.extraprec);
    if ((u = lllfp(G, 0.99, LLL_KEEP_FIRST)))
    {
      if (lg(u)-1 == n) break;
      /* singular ==> loss of accuracy */
      if (u0) u0 = gerepileupto(av, RgM_mul(u0,u));
      else    u0 = gerepilecopy(av, u);
    }
    prec = (prec<<1)-2 + divsBIL(gexpo(u0));
    F.ro = NULL;
    if (DEBUGLEVEL) pari_warn(warnprec,"get_red_G", prec);
  }
  if (u0) u = RgM_mul(u0,u);
  *pro = F.ro; return u;
}

/* Compute an LLL-reduced basis for the integer basis of nf(T).
 * set *pro = roots of x if computed [NULL if not computed] */
static void
set_LLL_basis(nfbasic_t *T, GEN *pro, double DELTA)
{
  GEN B = T->bas;
  if (T->r1 == degpol(T->x)) {
    pari_sp av = avma;
    GEN u, basden = T->basden;
    if (!basden) basden = get_bas_den(B);
    u = ZM_lll(make_Tr(T->x,basden), DELTA, LLL_GRAM|LLL_KEEP_FIRST|LLL_IM);
    B = gerepileupto(av, RgV_RgM_mul(B, u));
    *pro = NULL;
  }
  else
    B = RgV_RgM_mul(B, get_red_G(T, pro));
  T->bas = B;
  T->basden = get_bas_den(B);
  if (DEBUGLEVEL) msgtimer("LLL basis");
}

static int
cmp_abs_ZX(GEN x, GEN y) { return gen_cmp_RgX((void*)&absi_cmp, x, y); }
/* current best: ZX x of discriminant *dx, is ZX y better than x ?
 * (if so update *dx) */
static int
ZX_is_better(GEN y, GEN x, GEN *dx)
{
  GEN d = ZX_disc(y);
  long cmp = absi_cmp(d, *dx);
  if (cmp < 0) { *dx = d; return 1; }
  if (cmp == 0) return cmp_abs_ZX(y, x) < 0;
  return 0;
}

static GEN polred_aux(nfbasic_t *T, GEN *pro, long flag);
/* Seek a simpler, polynomial pol defining the same number field as
 * x (assumed to be monic at this point) */
static GEN
nfpolred(nfbasic_t *T, GEN *pro)
{
  GEN x = T->x, dx = T->dx, a, z, rev, pow, dpow;
  long i, n = degpol(x), v = varn(x);

  if (n == 1) {
    T->x = deg1pol_shallow(gen_1, gen_m1, v);
    *pro = NULL; return pol_1(v);
  }
  z = polred_aux(T, pro, nf_ORIG | nf_RED);
  if (typ(z) != t_VEC || !ZX_is_better(gel(z,1),x,&dx))
    return NULL; /* no improvement */

  rev = QXQ_reverse(gel(z,2), x);
  x = gel(z,1); if (DEBUGLEVEL>1) fprintferr("xbest = %Ps\n",x);

  /* update T */
  pow = QXQ_powers(rev, n-1, x);
  pow = Q_remove_denom(pow, &dpow);
  a = T->bas;
  for (i=2; i<=n; i++) gel(a,i) = QX_ZXQV_eval(gel(a,i), pow, dpow);
  (void)Z_issquareall(diviiexact(dx,T->dK), &(T->index));
  T->basden = get_bas_den(a);
  T->dx = dx; T->x = x; *pro = NULL; return rev;
}

/* let bas a t_VEC of QX giving a Z-basis of O_K. Return the index of the
 * basis. Assume bas[1] is 1 and that the leading coefficient of elements
 * of bas are of the form 1/b for a t_INT b */
GEN
get_nfindex(GEN bas)
{
  pari_sp av = avma;
  long n = lg(bas)-1, i;
  GEN D, d, mat;

  D = gen_1; /* assume bas[1] = 1 */
  for (i = 2; i <= n; i++)
  { /* in most cases [e.g after nfbasis] basis is upper triangular! */
    GEN B = gel(bas,i), lc;
    if (degpol(B) != i-1) break;
    lc = gel(B, i+1);
    switch (typ(lc))
    {
      case t_INT: continue;
      case t_FRAC: lc = gel(lc,2); break;
      default: pari_err(typeer,"get_nfindex");
    }
    D = mulii(D, lc);
  }
  if (i <= n)
  { /* not triangular after all */
    bas = Q_remove_denom(bas, &d);
    if (!d) { avma = av; return D; }
    mat = RgXV_to_RgM(bas, n);
    d = diviiexact(powiu(d, n), det(mat));
    D = mulii(D,d);
  }
  return gerepileuptoint(av, D);
}

/* monic integral polynomial + integer basis */
static int
is_polbas(GEN x)
{
  return (typ(x) == t_VEC && lg(x)==3
          && typ(gel(x,1))==t_POL && lg(gel(x,2))-1 == degpol(gel(x,1)));
}

void
nfbasic_add_disc(nfbasic_t *T)
{
  if (!T->index) T->index = get_nfindex(T->bas);
  if (!T->dx) T->dx = ZX_disc(T->x);
  if (!T->dK) T->dK = diviiexact(T->dx, sqri(T->index));
}

void
nfbasic_init(GEN x, long flag, GEN fa, nfbasic_t *T)
{
  GEN bas, dK, dx, index;
  long r1;

  T->basden = NULL;
  T->lead   = gen_1;
  if (DEBUGLEVEL) (void)timer2();
  if (typ(x) == t_POL)
  {
    nfmaxord_t S;
    x = Q_primpart(x);
    RgX_check_ZX(x, "nfinit");
    if (!ZX_is_irred(x)) pari_err(redpoler, "nfinit");
    if (flag & nf_RED || !gequal1(gel(x,lg(x)-1)))
      x = ZX_primitive_to_monic(x, &(T->lead));
    nfmaxord(&S, x, flag, fa);
    if (DEBUGLEVEL) msgtimer("round4");
    index = S.index;
    dx = S.dT;
    dK = S.dK;
    bas = S.basis;
    r1 = sturm(x);
  }
  else if (is_polbas(x))
  { /* monic integral polynomial + integer basis */
    bas = gel(x,2); x = gel(x,1);
    if (typ(bas) == t_MAT) bas = RgM_to_RgXV(bas,varn(x));
    index = NULL;
    dx = NULL;
    dK = NULL;
    r1 = sturm(x);
  }
  else
  { /* nf, bnf, bnr */
    GEN nf = checknf(x);
    x     = nf_get_pol(nf);
    dK    = nf_get_disc(nf);
    index = nf_get_index(nf);
    bas   = nf_get_zk(nf);
    dx = NULL;
    r1 = nf_get_r1(nf);
  }

  T->x     = x;
  T->r1    = r1;
  T->dx    = dx;
  T->dK    = dK;
  T->bas   = bas;
  T->index = index;
}

/* Initialize the number field defined by the polynomial x (in variable v)
 * flag & nf_RED:     try a polred first.
 * flag & nf_ORIG
 *    do a polred and return [nfinit(x), Mod(a,red)], where
 *    Mod(a,red) = Mod(v,x) (i.e return the base change). */
GEN
nfinitall(GEN x, long flag, long prec)
{
  const pari_sp av = avma;
  GEN nf;
  nfbasic_t T;

  nfbasic_init(x, flag, NULL, &T);
  nfbasic_add_disc(&T); /* more expensive after set_LLL_basis */
  if (T.lead != gen_1 && !(flag & nf_RED))
  {
    pari_warn(warner,"non-monic polynomial. Result of the form [nf,c]");
    flag |= nf_RED | nf_ORIG;
  }
  if (flag & nf_RED)
  {
    GEN ro, rev = nfpolred(&T, &ro);
    if (DEBUGLEVEL) msgtimer("polred");
    nf = nfbasic_to_nf(&T, ro, prec);
    if (flag & nf_ORIG)
    {
      if (!rev) rev = pol_x(varn(T.x)); /* no improvement */
      if (T.lead != gen_1) rev = RgX_Rg_div(rev, T.lead);
      nf = mkvec2(nf, mkpolmod(rev, T.x));
    }
  } else {
    GEN ro; set_LLL_basis(&T, &ro, 0.99);
    nf = nfbasic_to_nf(&T, ro, prec);
  }
  return gerepilecopy(av, nf);
}

GEN
nfinitred(GEN x, long prec)  { return nfinitall(x, nf_RED, prec); }
GEN
nfinitred2(GEN x, long prec) { return nfinitall(x, nf_RED|nf_ORIG, prec); }
GEN
nfinit(GEN x, long prec)     { return nfinitall(x, 0, prec); }

GEN
nfinit0(GEN x, long flag,long prec)
{
  switch(flag)
  {
    case 0:
    case 1: return nfinitall(x,0,prec);
    case 2: case 4: return nfinitall(x,nf_RED,prec);
    case 3: case 5: return nfinitall(x,nf_RED|nf_ORIG,prec);
    default: pari_err(flagerr,"nfinit");
  }
  return NULL; /* not reached */
}

/* assume x a bnr/bnf/nf */
long
nf_get_prec(GEN x)
{
  GEN nf = checknf(x), ro = nf_get_roots(nf);
  return (typ(ro)==t_VEC)? precision(gel(ro,1)): DEFAULTPREC;
}

/* assume nf is an nf */
GEN
nfnewprec_shallow(GEN nf, long prec)
{
  GEN NF = leafcopy(nf);
  nffp_t F;
  gel(NF,5) = leafcopy(gel(NF,5));
  remake_GM(NF, &F, prec);
  gel(NF,6) = F.ro;
  gmael(NF,5,1) = F.M;
  gmael(NF,5,2) = F.G;
  return NF;
}

GEN
nfnewprec(GEN nf, long prec)
{
  GEN z;
  switch(nftyp(nf))
  {
    default: pari_err(talker,"incorrect nf in nfnewprec");
    case typ_BNF: z = bnfnewprec(nf,prec); break;
    case typ_BNR: z = bnrnewprec(nf,prec); break;
    case typ_NF: {
      pari_sp av = avma;
      z = gerepilecopy(av, nfnewprec_shallow(checknf(nf), prec));
      break;
    }
  }
  return z;
}

/********************************************************************/
/**                                                                **/
/**                           POLRED                               **/
/**                                                                **/
/********************************************************************/
GEN
T2_from_embed_norm(GEN x, long r1)
{
  GEN p = RgV_sumpart(x, r1);
  GEN q = RgV_sumpart2(x,r1+1, lg(x)-1);
  if (q != gen_0) p = gadd(p, gmul2n(q,1));
  return p;
}
GEN
T2_from_embed(GEN x, long r1) { return T2_from_embed_norm(gnorm(x), r1); }

typedef struct {
  long r1, v, prec;
  GEN ZKembed; /* embeddings of fincke-pohst-reduced Zk basis */
  GEN u; /* matrix giving fincke-pohst-reduced Zk basis */
  GEN M; /* embeddings of initial (LLL-reduced) Zk basis */
  GEN bound; /* T2 norm of the polynomial defining nf */
} CG_data;

/* characteristic pol of x (given by embeddings) */
static GEN
get_pol(CG_data *d, GEN x)
{
  long e;
  GEN g = grndtoi(roots_to_pol_r1(x, d->v, d->r1), &e);
  return (e > -5)? NULL: g;
}

/* characteristic pol of x (given as vector on (w_i)) */
static GEN
get_polchar(CG_data *d, GEN x)
{ return get_pol(d, RgM_RgC_mul(d->ZKembed,x)); }

/* return a defining polynomial for Q(w_i) */
static GEN
get_polmin_w(CG_data *d, long k)
{
  GEN g = get_pol(d, gel(d->ZKembed,k));
  if (g) (void)ZX_gcd_all(g, ZX_deriv(g), &g);
  return g;
}

/* does x generate the correct field ? */
static GEN
chk_gen(void *data, GEN x)
{
  pari_sp av = avma, av1;
  GEN h, g = get_polchar((CG_data*)data,x);
  if (!g) pari_err(precer,"chk_gen");
  av1 = avma;
  h = ZX_gcd(g, ZX_deriv(g));
  if (degpol(h)) { avma = av; return NULL; }
  if (DEBUGLEVEL>3) fprintferr("  generator: %Ps\n",g);
  avma = av1; return gerepileupto(av, g);
}

static long
chk_gen_prec(long N, long bit)
{ return nbits2prec(10 + (long)log2((double)N) + bit); }

/* Remove duplicate polynomials in P, updating A (same indices), in place.
 * Among elements having the same characteristic pol, choose the smallest
 * according to ZV_abscmp */
static void
remove_duplicates(GEN P, GEN A)
{
  long k, i, l = lg(P);
  pari_sp av = avma;
  GEN x, a;

  if (l < 2) return;
  (void)sort_factor_pol(mkmat2(P, A), cmpii);
  x = gel(P,1); a = gel(A,1);
  for  (k=1,i=2; i<l; i++)
    if (ZX_equal(gel(P,i), x))
    {
      if (ZV_abscmp(gel(A,i), a) < 0) a = gel(A,i);
    }
    else
    {
      gel(A,k) = a;
      gel(P,k) = x;
      k++;
      x = gel(P,i); a = gel(A,i);
    }
  gel(A,k) = a;
  gel(P,k) = x;
  l = k+1; setlg(A,l); setlg(P,l);
  avma = av;
}

/* Choose a canonical polynomial in the pair { z(X), (+/-)z(-X) }.
 * z a ZX with lc(z) > 0. We want to keep that property, while
 * ensuring that the leading coeff of the odd (resp. even) part of z is < 0
 * if deg z is even (resp. odd).
 * Either leave z alone (return 1) or set z <-- (-1)^deg(z) z(-X). In place. */
static int
ZX_canon_neg(GEN z)
{
  long i,s;

  for (i = lg(z)-2; i >= 2; i -= 2)
  { /* examine the odd (resp. even) part of z if deg(z) even (resp. odd). */
    s = signe(z[i]);
    if (!s) continue;
    /* non trivial */
    if (s < 0) break; /* the condition is already satisfied */

    for (; i>=2; i-=2) gel(z,i) = negi(gel(z,i));
    return 1;
  }
  return 0;
}
static long
polred_init(nfbasic_t *T, nffp_t *F, CG_data *d)
{
  long e, prec, n = degpol(T->x);
  double log2rho;
  GEN ro;
  set_LLL_basis(T, &ro, 0.9999);
  /* || polchar ||_oo < 2^e ~ 2 (n * rho)^n, rho = max modulus of root */
  log2rho = ro ? (double)gexpo(ro): cauchy_bound(T->x) / LOG2;
  e = n * (long)(log2rho + log2((double)n)) + 1;
  prec = chk_gen_prec(n, e);
  get_nf_fp_compo(T, F, ro, prec);
  d->v = varn(T->x);
  d->r1= T->r1; return prec;
}
static GEN
polred_aux(nfbasic_t *T, GEN *pro, long flag)
{
  GEN b, y, x = T->x;
  long i, v = varn(x), l = lg(T->bas);
  const long orig = flag & nf_ORIG;
  const long nfred = flag & nf_RED;
  nffp_t F;
  CG_data d;

  (void)polred_init(T, &F, &d);
  *pro = F.ro;
  d.ZKembed = F.M;

  y = cgetg(l, t_VEC);
  b = cgetg(l, t_COL);
  gel(y,1) = deg1pol_shallow(gen_1, gen_m1, v);
  gel(b,1) = gen_1;
  for (i = 2; i < l; i++)
  {
    GEN ch, ai = gel(T->bas,i);
    ch = get_polmin_w(&d, i);
    /* if accuracy too low, compute algebraically */
    if (!ch) ch = ZXQ_charpoly(ai, x, v);
    if (ZX_canon_neg(ch) && orig) ai = RgX_neg(ai);
    if (nfred && degpol(ch) == l-1) return mkvec2(ch, ai);
    if (DEBUGLEVEL>3) fprintferr("polred: generator %Ps\n", ch);
    if (T->lead != gen_1 && orig) ai = RgX_unscale(ai, ginv(T->lead));
    gel(y,i) = ch;
    gel(b,i) = ai;
  }
  if (!orig) return gen_sort_uniq(y, (void*)cmpii, &gen_cmp_RgX);
  (void)sort_factor_pol(mkmat2(y, b), cmpii);
  settyp(y, t_COL); return mkmat2(b, y);
}

GEN
Polred(GEN x, long flag, GEN fa)
{
  pari_sp av = avma;
  GEN ro;
  nfbasic_t T; nfbasic_init(x, flag & (nf_PARTIALFACT|nf_RED), fa, &T);
  return gerepilecopy(av, polred_aux(&T, &ro, flag & nf_ORIG));
}

/* FIXME: backward compatibility */
GEN
polred0(GEN x, long flag, GEN fa)
{
  long fl = 0;
  if (flag & 1) fl |= nf_PARTIALFACT;
  if (flag & 2) fl |= nf_ORIG;
  return Polred(x, fl, fa);
}

GEN
ordred(GEN x)
{
  pari_sp av = avma;
  GEN y;

  if (typ(x) != t_POL) pari_err(typeer,"ordred");
  if (!gequal1(leading_term(x))) pari_err(impl,"ordred");
  if (!signe(x)) return gcopy(x);
  y = mkvec2(x, matid(degpol(x)));
  return gerepileupto(av, Polred(y, 0, NULL));
}

GEN
polred(GEN x) { return Polred(x, 0, NULL); }
GEN
smallpolred(GEN x) { return Polred(x, nf_PARTIALFACT, NULL); }
GEN
factoredpolred(GEN x, GEN fa) { return Polred(x, 0, fa); }
GEN
polred2(GEN x) { return Polred(x, nf_ORIG, NULL); }
GEN
smallpolred2(GEN x) { return Polred(x, nf_PARTIALFACT|nf_ORIG, NULL); }
GEN
factoredpolred2(GEN x, GEN fa) { return Polred(x, nf_PARTIALFACT, fa); }

/********************************************************************/
/**                                                                **/
/**                           POLREDABS                            **/
/**                                                                **/
/********************************************************************/
/* set V[k] := matrix of multiplication by nk.zk[k] */
static GEN
set_mulid(GEN V, GEN M, GEN Mi, long r1, long r2, long N, long k)
{
  GEN v, Mk = cgetg(N+1, t_MAT);
  long i, e;
  for (i = 1; i < k; i++) gel(Mk,i) = gmael(V, i, k);
  for (     ; i <=N; i++)
  {
    v = vecmul(gel(M,k), gel(M,i));
    v = RgM_RgC_mul(Mi, split_realimag(v, r1, r2));
    gel(Mk,i) = grndtoi(v, &e);
    if (e > -5) return NULL;
  }
  gel(V,k) = Mk; return Mk;
}

/* U = base change matrix, R = Cholesky form of the quadratic form [matrix
 * Q from algo 2.7.6] */
static GEN
chk_gen_init(FP_chk_fun *chk, GEN R, GEN U)
{
  CG_data *d = (CG_data*)chk->data;
  GEN P, V, S, inv, bound, M;
  long N = lg(U)-1, r1 = d->r1, r2 = (N-r1)>>1;
  long i, j, prec, firstprim = 0, skipfirst = 0;
  pari_sp av;

  d->u = U;
  d->ZKembed = RgM_mul(d->M, U);

  av = avma; bound = d->bound;
  S = cgetg(N+1, t_VECSMALL);
  for (i = 1; i <= N; i++)
  {
    P = get_polmin_w(d, i); if (!P) pari_err(precer,"chk_gen_init");
    S[i] = degpol(P);
    if (S[i] == N)
    { /* primitive element */
      GEN B = T2_from_embed(gel(d->ZKembed,i), r1);
      if (gcmp(B,bound) < 0) bound = B ;
      if (!firstprim) firstprim = i; /* index of first primitive element */
      if (DEBUGLEVEL>2) fprintferr("chk_gen_init: generator %Ps\n",P);
    }
    else
    {
      if (DEBUGLEVEL>2) fprintferr("chk_gen_init: subfield %Ps\n",P);
      if (firstprim)
      { /* cycle basis vectors so that primitive elements come last */
        GEN u = d->u, e = d->ZKembed;
        GEN te = gel(e,i), tu = gel(u,i), tR = gel(R,i);
        long tS = S[i];
        for (j = i; j > firstprim; j--)
        {
          u[j] = u[j-1];
          e[j] = e[j-1];
          R[j] = R[j-1];
          S[j] = S[j-1];
        }
        gel(u,firstprim) = tu;
        gel(e,firstprim) = te;
        gel(R,firstprim) = tR;
        S[firstprim] = tS; firstprim++;
      }
    }
  }
  if (!firstprim)
  { /* try (a little) to find primitive elements to improve bound */
    GEN x = cgetg(N+1, t_VECSMALL), e, B;
    if (DEBUGLEVEL>1)
      fprintferr("chk_gen_init: difficult field, trying random elements\n");
    for (i = 0; i < 10; i++)
    {
      for (j = 1; j <= N; j++) x[j] = (long)random_Fl(7) - 3;
      e = RgM_zc_mul(d->ZKembed, x);
      P = get_pol(d, e); if (!P) pari_err(precer, "chk_gen_init");
      if (!ZX_is_squarefree(P)) continue;
      if (DEBUGLEVEL>2) fprintferr("chk_gen_init: generator %Ps\n",P);
      B = T2_from_embed(e, r1);
      if (gcmp(B,bound) < 0) bound = B ;
    }
  }

  if (firstprim != 1)
  {
    inv = ginv( split_realimag(d->ZKembed, r1, r2) ); /*TODO: use QR?*/
    V = gel(inv,1);
    for (i = 2; i <= r1+r2; i++) V = gadd(V, gel(inv,i));
    /* V corresponds to 1_Z */
    V = grndtoi(V, &j);
    if (j > -5) pari_err(bugparier,"precision too low in chk_gen_init");
    M = mkmat(V); /* 1 */

    V = cgetg(N+1, t_VEC);
    for (i = 1; i <= N; i++,skipfirst++)
    { /* M = Q-basis of subfield generated by nf.zk[1..i-1] */
      GEN Mx, M2;
      long j, k, h, rkM, dP = S[i];

      if (dP == N) break; /* primitive */
      Mx = set_mulid(V, d->ZKembed, inv, r1, r2, N, i);
      if (!Mx) break; /* prec. problem. Stop */
      if (dP == 1) continue;
      rkM = lg(M)-1;
      M2 = cgetg(N+1, t_MAT); /* we will add to M the elts of M2 */
      gel(M2,1) = col_ei(N, i); /* nf.zk[i] */
      k = 2;
      for (h = 1; h < dP; h++)
      {
        long r; /* add to M2 the elts of M * nf.zk[i]  */
        for (j = 1; j <= rkM; j++) gel(M2,k++) = RgM_RgC_mul(Mx, gel(M,j));
        setlg(M2, k); k = 1;
        M = image(shallowconcat(M, M2));
        r = lg(M) - 1;
        if (r == rkM) break;
        if (r > rkM)
        {
          rkM = r;
          if (rkM == N) break;
        }
      }
      if (rkM == N) break;
      /* Q(w[1],...,w[i-1]) is a strict subfield of nf */
    }
  }
  /* x_1,...,x_skipfirst generate a strict subfield [unless N=skipfirst=1] */
  chk->skipfirst = skipfirst;
  if (DEBUGLEVEL>2) fprintferr("chk_gen_init: skipfirst = %ld\n",skipfirst);

  /* should be DEF + gexpo( max_k C^n_k (bound/k)^(k/2) ) */
  bound = gerepileuptoleaf(av, bound);
  prec = chk_gen_prec(N, (gexpo(bound)*N)/2);
  if (DEBUGLEVEL)
    fprintferr("chk_gen_init: new prec = %ld (initially %ld)\n", prec, d->prec);
  if (prec > d->prec) pari_err(bugparier, "polredabs (precision problem)");
  if (prec < d->prec) d->ZKembed = gprec_w(d->ZKembed, prec);
  return bound;
}

static GEN
findmindisc(GEN y, GEN *pa)
{
  GEN a = *pa, x = gel(y,1), b = gel(a,1), dx;
  long i, l = lg(y);

  if (l == 2) { *pa = b; return x; }
  dx = ZX_disc(x);
  for (i = 2; i < l; i++)
  {
    GEN yi = gel(y,i);
    if (ZX_is_better(yi,x,&dx)) { x = yi; b = gel(a,i); }
  }
  *pa = b; return x;
}

/* z "small" minimal polynomial of Mod(a,x), deg z = deg x */
static GEN
store(GEN x, GEN z, GEN a, nfbasic_t *T, long flag, GEN u)
{
  GEN y, b;

  if (u) a = RgV_RgC_mul(T->bas, ZM_ZC_mul(u, a));
  if (flag & (nf_ORIG|nf_ADDZK))
  {
    b = QXQ_reverse(a, x);
    if (T->lead != gen_1) b = RgX_Rg_div(b, T->lead);
  }
  else
    b = NULL;

  if (flag & nf_RAW)
    y = mkvec2(z, a);
  else if (flag & nf_ORIG) /* store phi(b mod z). */
    y = mkvec2(z, mkpolmod(b,z));
  else
    y = z;
  if (flag & nf_ADDZK)
  { /* append integral basis for number field Q[X]/(z) to result */
    long n = degpol(x);
    GEN t = RgV_RgM_mul(RgXQ_powers(b, n-1, z), RgXV_to_RgM(T->bas,n));
    y = mkvec2(y, t);
  }
  return y;
}
static GEN
polredabs_aux(nfbasic_t *T, GEN *u)
{
  long prec;
  GEN v;
  FP_chk_fun chk = { &chk_gen, &chk_gen_init, NULL, NULL, 0 };
  nffp_t F;
  CG_data d; chk.data = (void*)&d;

  prec = polred_init(T, &F, &d);
  d.bound = T2_from_embed(F.ro, T->r1);
  for (;;)
  {
    GEN R = R_from_QR(F.G, prec);
    if (R)
    {
      d.prec = prec;
      d.M    = F.M;
      v = fincke_pohst(mkvec(R),NULL,-1, 0, &chk);
      if (v) break;
    }
    prec = (prec<<1)-2;
    get_nf_fp_compo(T, &F, NULL, prec);
    if (DEBUGLEVEL) pari_warn(warnprec,"polredabs0",prec);
  }
  *u = d.u; return v;
}

GEN
polredabs0(GEN x, long flag)
{
  pari_sp av = avma;
  long i, l, vx;
  GEN y, a, u;
  nfbasic_t T;

  nfbasic_init(x, flag & (nf_PARTIALFACT|nf_RED), NULL, &T);
  x = T.x; vx = varn(x);

  if (degpol(x) == 1)
  {
    u = NULL;
    y = mkvec( pol_x(vx) );
    a = mkvec( deg1pol_shallow(gen_1, negi(gel(x,2)), vx) );
    l = 2;
  }
  else
  {
    GEN v = polredabs_aux(&T, &u);
    y = gel(v,1);
    a = gel(v,2); l = lg(a);
    for (i=1; i<l; i++)
      if (ZX_canon_neg(gel(y,i))) gel(a,i) = ZC_neg(gel(a,i));
    remove_duplicates(y,a);
    l = lg(a);
  }
  if (DEBUGLEVEL) fprintferr("Found %ld minimal polynomials.\n",l-1);
  if (flag & nf_ALL) {
    for (i=1; i<l; i++) gel(y,i) = store(x, gel(y,i), gel(a,i), &T, flag, u);
  } else {
    GEN z = findmindisc(y, &a);
    y = store(x, z, a, &T, flag, u);
  }
  return gerepilecopy(av, y);
}

GEN
polredabsall(GEN x, long flun) { return polredabs0(x, flun | nf_ALL); }
GEN
polredabs(GEN x) { return polredabs0(x,0); }
GEN
polredabs2(GEN x) { return polredabs0(x,nf_ORIG); }
