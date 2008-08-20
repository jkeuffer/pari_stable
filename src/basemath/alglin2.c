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

/********************************************************************/
/**                                                                **/
/**                         LINEAR ALGEBRA                         **/
/**                         (second part)                          **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"
/*******************************************************************/
/*                                                                 */
/*                   CHARACTERISTIC POLYNOMIAL                     */
/*                                                                 */
/*******************************************************************/

GEN
charpoly0(GEN x, long v, long flag)
{
  if (v<0) v = 0;
  switch(flag)
  {
    case 0: return caradj(x,v,NULL);
    case 1: return caract(x,v);
    case 2: return carhess(x,v);
    case 3: return carberkowitz(x,v);
    case 4:
      if (typ(x) != t_MAT) pari_err(typeer,"charpoly");
      RgM_check_ZM(x, "charpoly");
      x = ZM_charpoly(x); setvarn(x, v); return x;
  }
  pari_err(flagerr,"charpoly"); return NULL; /* not reached */
}

/* characteristic pol. Easy cases. Return NULL in case it's not so easy. */
static GEN
easychar(GEN x, long v, GEN *py)
{
  pari_sp av;
  long lx;
  GEN p1;

  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_INTMOD:
    case t_FRAC: case t_PADIC:
      p1=cgetg(4,t_POL);
      p1[1]=evalsigne(1) | evalvarn(v);
      gel(p1,2) = gneg(x); gel(p1,3) = gen_1;
      if (py) { *py = cgetg(2, t_MAT); gel(*py,1) = mkcolcopy(x); }
      return p1;

    case t_COMPLEX: case t_QUAD:
      if (py) pari_err(typeer,"easychar");
      p1 = cgetg(5,t_POL);
      p1[1] = evalsigne(1) | evalvarn(v);
      gel(p1,2) = gnorm(x); av = avma;
      gel(p1,3) = gerepileupto(av, gneg(gtrace(x)));
      gel(p1,4) = gen_1; return p1;

    case t_FFELT: {
      pari_sp ltop=avma;
      if (py) pari_err(typeer,"easychar");
      p1 = FpX_to_mod(FF_charpoly(x), FF_p_i(x));
      setvarn(p1,v); return gerepileupto(ltop,p1);
    }

    case t_POLMOD:
      if (py) pari_err(typeer,"easychar");
      return RgXQ_caract(gel(x,2), gel(x,1), v);

    case t_MAT:
      lx=lg(x);
      if (lx==1)
      {
	if (py) *py = cgetg(1,t_MAT);
	return pol_1(v);
      }
      if (lg(x[1]) != lx) break;
      return NULL;
  }
  pari_err(mattype1,"easychar");
  return NULL; /* not reached */
}

/* We possibly worked with an "invalid" polynomial p, satisfying
 * varn(p) > gvar2(p). Fix this. */
static GEN
fix_pol(pari_sp av, GEN p)
{
  long w = gvar2(p), v = varn(p);
  if (w == v) pari_err(talker,"incorrect variable in charpoly");
  if (varncmp(w,v) < 0) p = gerepileupto(av, poleval(p, pol_x(v)));
  return p;
}
GEN
caract(GEN x, long v)
{
  pari_sp av = avma;
  GEN  T, C, x_k, Q;
  long k, n;

  if ((T = easychar(x,v,NULL))) return T;

  n = lg(x)-1;
  if (n == 1) return fix_pol(av, deg1pol(gen_1, gneg(gcoeff(x,1,1)), v));

  x_k = pol_x(v); /* to be modified in place */
  T = scalarpol(det(x), v); C = utoineg(n); Q = pol_x(v);
  for (k=1; k<=n; k++)
  {
    GEN mk = utoineg(k), d;
    gel(x_k,2) = mk;
    d = det(RgM_Rg_add_shallow(x, mk));
    T = RgX_add(RgX_mul(T, x_k), RgX_Rg_mul(Q, gmul(C, d)));
    if (k == n) break;

    Q = RgX_mul(Q, x_k);
    C = diviuexact(mulsi(k-n,C), k+1); /* (-1)^k binomial(n,k) */
  }
  return fix_pol(av, RgX_Rg_div(T, mpfact(n)));
}

/* assume x square matrice */
static GEN
mattrace(GEN x)
{
  long i, lx = lg(x);
  GEN t;
  if (lx < 3) return lx == 1? gen_0: gcopy(gcoeff(x,1,1));
  t = gcoeff(x,1,1);
  for (i = 2; i < lx; i++) t = gadd(t, gcoeff(x,i,i));
  return t;
}
/* Using traces: return the characteristic polynomial of x (in variable v).
 * If py != NULL, the adjoint matrix is put there. */
GEN
caradj(GEN x, long v, GEN *py)
{
  pari_sp av, av0;
  long i, k, l;
  GEN p, y, t;

  if ((p = easychar(x, v, py))) return p;

  l = lg(x); av0 = avma;
  p = cgetg(l+2,t_POL); p[1] = evalsigne(1) | evalvarn(v);
  gel(p,l+1) = gen_1;
  if (l == 1) { if (py) *py = cgetg(1,t_MAT); return p; }
  av = avma; t = gerepileupto(av, gneg(mattrace(x)));
  gel(p,l) = t;
  if (l == 2) {
    p = fix_pol(av0, p);
    if (py) *py = matid(1); return p;
  }
  if (l == 3) {
    GEN a = gcoeff(x,1,1), b = gcoeff(x,1,2);
    GEN c = gcoeff(x,2,1), d = gcoeff(x,2,2);
    av = avma;
    gel(p,2) = gerepileupto(av, gsub(gmul(a,d), gmul(b,c)));
    p = fix_pol(av0, p);
    if (py) {
      y = cgetg(3, t_MAT);
      gel(y,1) = mkcol2(gcopy(d), gneg(c));
      gel(y,2) = mkcol2(gneg(b), gcopy(a));
      *py = y;
    }
    return p;
  }
  /* l > 3 */
  av = avma; y = RgM_shallowcopy(x);
  for (i = 1; i < l; i++) gcoeff(y,i,i) = gadd(gcoeff(y,i,i), t);
  for (k = 2; k < l-1; k++)
  {
    GEN y0 = y;
    y = RgM_mul(y, x);
    t = gdivgs(mattrace(y), -k);
    for (i = 1; i < l; i++) gcoeff(y,i,i) = gadd(gcoeff(y,i,i), t);
    y = gclone(y);
    gel(p,l-k+1) = gerepilecopy(av, t); av = avma;
    if (k > 2) gunclone(y0);
  }
  t = gmul(gcoeff(x,1,1),gcoeff(y,1,1));
  for (i=2; i<l; i++) t = gadd(t, gmul(gcoeff(x,1,i),gcoeff(y,i,1)));
  gel(p,2) = gerepileupto(av, gneg(t));
  p = fix_pol(av0, p);
  if (py) *py = (l & 1)? RgM_neg(y): gcopy(y);
  gunclone(y); return p;
}

GEN
adj(GEN x)
{
  GEN y;
  (void)caradj(x,MAXVARN,&y); return y;
}

/*******************************************************************/
/*                                                                 */
/*                       MINIMAL POLYNOMIAL                        */
/*                                                                 */
/*******************************************************************/

static GEN
easymin(GEN x, long v)
{
  pari_sp ltop=avma;
  GEN G, R, dR;
  if (typ(x)==t_POLMOD && !issquarefree(gel(x,1)))
    return NULL;
  R=easychar(x, v, NULL);
  if (!R) return R;
  dR=RgX_deriv(R);
  if (!lgpol(dR)) {avma=ltop; return NULL;}
  G=RgX_gcd(R,dR);
  G=RgX_Rg_div(G,leading_term(G));
  G=gdeuc(R,G);
  return gerepileupto(ltop,G);
}

GEN
minpoly(GEN x, long v)
{
  pari_sp ltop=avma;
  GEN P;
  if (v<0) v = 0;
  if (typ(x)==t_FFELT)
  {
      GEN p1 = FpX_to_mod(FF_minpoly(x), FF_p_i(x));
      setvarn(p1,v); return gerepileupto(ltop,p1);
  }

  P=easymin(x,v);
  if (P) return P;
  if (typ(x)==t_POLMOD)
  {
    P = gcopy(RgXQ_minpoly_naive(gel(x,2), gel(x,1)));
    setvarn(P,v);
    return gerepileupto(ltop,P);
  }
  if (typ(x)!=t_MAT) pari_err(typeer,"minpoly");
  if (lg(x) == 1) return pol_1(v);
  return gerepilecopy(ltop,gel(matfrobenius(x,1,v),1));
}

/*******************************************************************/
/*                                                                 */
/*                       HESSENBERG FORM                           */
/*                                                                 */
/*******************************************************************/
GEN
hess(GEN x)
{
  pari_sp av = avma, lim;
  long lx = lg(x), m, i, j;

  if (typ(x) != t_MAT) pari_err(mattype1,"hess");
  if (lx == 1) return cgetg(1,t_MAT);
  if (lg(x[1]) != lx) pari_err(mattype1,"hess");

  x = RgM_shallowcopy(x); lim = stack_lim(av,2);
  for (m=2; m<lx-1; m++)
  {
    GEN t = NULL;
    for (i=m+1; i<lx; i++) { t = gcoeff(x,i,m-1); if (!gcmp0(t)) break; }
    if (i == lx) continue;
    for (j=m-1; j<lx; j++) swap(gcoeff(x,i,j), gcoeff(x,m,j));
    swap(gel(x,i), gel(x,m)); t = ginv(t);

    for (i=m+1; i<lx; i++)
    {
      GEN c = gcoeff(x,i,m-1);
      if (gcmp0(c)) continue;

      c = gmul(c,t); gcoeff(x,i,m-1) = gen_0;
      for (j=m; j<lx; j++)
        gcoeff(x,i,j) = gsub(gcoeff(x,i,j), gmul(c,gcoeff(x,m,j)));
      for (j=1; j<lx; j++)
        gcoeff(x,j,m) = gadd(gcoeff(x,j,m), gmul(c,gcoeff(x,j,i)));
      if (low_stack(lim, stack_lim(av,2)))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"hess, m = %ld", m);
        x = gerepilecopy(av, x);
      }
    }
  }
  return gerepilecopy(av,x);
}

GEN
Flm_hess(GEN x, ulong p)
{
  pari_sp av = avma, lim;
  long lx = lg(x), m, i, j;

  if (typ(x) != t_MAT) pari_err(mattype1,"hess");
  if (lx == 1) return cgetg(1,t_MAT);
  if (lg(x[1]) != lx) pari_err(mattype1,"hess");

  x = Flm_copy(x); lim = stack_lim(av,2);
  for (m=2; m<lx-1; m++)
  {
    ulong t = 0;
    for (i=m+1; i<lx; i++) { t = ucoeff(x,i,m-1); if (t) break; }
    if (i == lx) continue;
    for (j=m-1; j<lx; j++) lswap(ucoeff(x,i,j), ucoeff(x,m,j));
    swap(gel(x,i), gel(x,m)); t = Fl_inv(t, p);

    for (i=m+1; i<lx; i++)
    {
      ulong c = ucoeff(x,i,m-1);
      if (!c) continue;

      c = Fl_mul(c,t,p); ucoeff(x,i,m-1) = 0;
      for (j=m; j<lx; j++)
        ucoeff(x,i,j) = Fl_sub(ucoeff(x,i,j), Fl_mul(c,ucoeff(x,m,j), p), p);
      for (j=1; j<lx; j++)
        ucoeff(x,j,m) = Fl_add(ucoeff(x,j,m), Fl_mul(c,ucoeff(x,j,i), p), p);
    }
  }
  return gerepilecopy(av,x);
}

GEN
carhess(GEN x, long v)
{
  pari_sp av;
  long lx, r, i;
  GEN y, H;

  if ((H = easychar(x,v,NULL))) return H;

  lx = lg(x); av = avma; y = cgetg(lx+1, t_VEC);
  gel(y,1) = pol_1(v); H = hess(x);
  for (r = 1; r < lx; r++)
  {
    pari_sp av2 = avma;
    GEN z, a = gen_1, b = zeropol(v);
    for (i = r-1; i; i--)
    {
      a = gmul(a, gcoeff(H,i+1,i));
      if (gcmp0(a)) break;
      b = RgX_add(b, RgX_Rg_mul(gel(y,i), gmul(a,gcoeff(H,i,r))));
    }
    z = RgX_sub(RgX_shift_shallow(gel(y,r), 1),
                RgX_Rg_mul(gel(y,r), gcoeff(H,r,r)));
    gel(y,r+1) = gerepileupto(av2, RgX_sub(z, b)); /* (X - H[r,r])y[r] - b */
  }
  return fix_pol(av, gel(y,lx));
}
GEN
Flm_charpoly(GEN x, long p)
{
  pari_sp av;
  long lx, r, i;
  GEN y, H;

  lx = lg(x); av = avma; y = cgetg(lx+1, t_VEC);
  gel(y,1) = pol1_Flx(0); H = Flm_hess(x, p);
  for (r = 1; r < lx; r++)
  {
    pari_sp av2 = avma;
    ulong a = 1;
    GEN z, b = zero_Flx(0);
    for (i = r-1; i; i--)
    {
      a = Fl_mul(a, ucoeff(H,i+1,i), p);
      if (!a) break;
      b = Flx_add(b, Flx_Fl_mul(gel(y,i), Fl_mul(a,ucoeff(H,i,r),p), p), p);
    }
    z = Flx_sub(Flx_shift(gel(y,r), 1),
                Flx_Fl_mul(gel(y,r), ucoeff(H,r,r), p), p);
    /* (X - H[r,r])y[r] - b */
    gel(y,r+1) = gerepileuptoleaf(av2, Flx_sub(z, b, p));
  }
  return gerepileuptoleaf(av, gel(y,lx));
}

/* s = max_k binomial(n,k) (kB^2)^(k/2),  B = |M|oo. Return ceil(log2(s)) */
static double
charpoly_bound(GEN M)
{
  pari_sp av = avma;
  GEN s = real_0(3), bin, B2 = itor(sqri(ZM_supnorm(M)), 3);
  long n = lg(M)-1, k = (n+1)>>1;
  double d;
  bin = gen_1;
  for (k = n; k >= (n+1)>>1; k--)
  {
    GEN t = mulri(powruhalf(mulur(k, B2), k), bin);
    if (absr_cmp(t, s) > 0) s = t;
    bin = diviuexact(muliu(bin, k), n-k+1);
  }
  d = dbllog2(s); avma = av; return ceil(d);
}

GEN 
ZM_charpoly(GEN M)
{
  pari_sp av = avma;
  long l = lg(M), n = l-1, bit;
  GEN q = NULL, H = NULL, Hp;
  ulong p;
  byteptr d;
  if (!n) return pol_1(0);

  bit = (long)charpoly_bound(M) + 1;
  if (DEBUGLEVEL>5) {
    fprintferr("ZM_charpoly: bit-bound 2^%ld\n", bit);
    (void)timer2();
  }
  d = init_modular(&p);
  for(;;)
  {
    NEXT_PRIME_VIADIFF_CHECK(p,d);
    Hp = Flm_charpoly(ZM_to_Flm(M, p), p);
    if (!H)
    {
      H = ZX_init_CRT(Hp, p, 0);
      if (DEBUGLEVEL>5)
        msgtimer("charpoly mod %lu, bound = 2^%ld", p, expu(p));
      if (expu(p) > bit) break;
      q = utoipos(p);
    }
    else
    { 
      GEN qp = muliu(q, p);
      int stable = ZX_incremental_CRT(&H, Hp, q,qp, p);
      if (DEBUGLEVEL>5)
        msgtimer("charpoly mod %lu (stable=%ld), bound = 2^%ld",
                 p, stable, expi(qp));
      if (stable && expi(qp) > bit) break;
      q = qp;
    }
  }
  return gerepilecopy(av, H);
}

/*******************************************************************/
/*                                                                 */
/*        CHARACTERISTIC POLYNOMIAL (BERKOWITZ'S ALGORITHM)        */
/*                                                                 */
/*******************************************************************/
GEN
carberkowitz(GEN x, long v)
{
  long lx, i, j, k, r;
  GEN V, S, C, Q;
  pari_sp av0;
  if ((V = easychar(x,v,NULL))) return V;

  lx = lg(x); av0 = avma;
  V = cgetg(lx+1, t_VEC);
  S = cgetg(lx+1, t_VEC);
  C = cgetg(lx+1, t_VEC);
  Q = cgetg(lx+1, t_VEC);
  gel(V,1) = gen_m1;
  gel(V,2) = gcoeff(x,1,1);
  for (i=2;i<=lx; i++) gel(S,i) = gen_0;
  for (i=2;i<=lx; i++) gel(C,i) = gen_0;
  for (i=2;i<=lx; i++) gel(Q,i) = gen_0;
  gel(C,1) = gen_m1;
  for (r = 2; r < lx; r++)
  {
    pari_sp av;
    GEN t;

    for (i = 1; i < r; i++) gel(S,i) = gcoeff(x,i,r);
    gel(C,2) = gcoeff(x,r,r);
    for (i = 1; i < r-1; i++)
    {
      av = avma; t = gmul(gcoeff(x,r,1), gel(S,1));
      for (j = 2; j < r; j++) t = gadd(t, gmul(gcoeff(x,r,j), gel(S,j)));
      gel(C,i+2) = gerepileupto(av, t);
      for (j = 1; j < r; j++)
      {
	av = avma; t = gmul(gcoeff(x,j,1), gel(S,1));
	for (k = 2; k < r; k++) t = gadd(t, gmul(gcoeff(x,j,k), gel(S,k)));
	gel(Q,j) = gerepileupto(av, t);
      }
      for (j = 1; j < r; j++) gel(S,j) = gel(Q,j);
    }
    av = avma; t = gmul(gcoeff(x,r,1), gel(S,1));
    for (j = 2; j < r; j++) t = gadd(t, gmul(gcoeff(x,r,j), gel(S,j)));
    gel(C,r+1) = gerepileupto(av, t);

    for (i = 1; i <= r+1; i++)
    {
      av = avma; t = gmul(gel(C,i), gel(V,1));
      for (j = 2; j <= minss(r,i); j++)
        t = gadd(t, gmul(gel(C,i+1-j), gel(V,j)));
      gel(Q,i) = gerepileupto(av, t);
    }
    for (i = 1; i <= r+1; i++) V[i] = Q[i];
  }
  V = RgX_recip_shallow( RgV_to_RgX(V, v) ); /* not gtopoly: fail if v > gvar(V) */
  V = odd(lx)? gcopy(V): RgX_neg(V);
  return fix_pol(av0, V);
}

/*******************************************************************/
/*                                                                 */
/*                            NORM                                 */
/*                                                                 */
/*******************************************************************/
GEN
cxnorm(GEN x) { return gadd(gsqr(gel(x,1)), gsqr(gel(x,2))); }
/* q t_QUAD */
GEN
quadnorm(GEN q)
{
  GEN X = gel(q,1), b = gel(X,3), c = gel(X,2);
  GEN z, u = gel(q,3), v = gel(q,2);
  if (typ(u) == t_INT && typ(v) == t_INT) /* generic case */
  {
    z = signe(b)? mulii(v, addii(u,v)): sqri(v);
    return addii(z, mulii(c, sqri(u)));
  }
  else
  {
    z = signe(b)? gmul(v, gadd(u,v)): gsqr(v);
    return gadd(z, gmul(c, gsqr(u)));
  }
}

GEN
gnorm(GEN x)
{
  pari_sp av;
  long lx, i;
  GEN y;

  switch(typ(x))
  {
    case t_INT:  return sqri(x);
    case t_REAL: return mulrr(x,x);
    case t_FRAC: return gsqr(x);
    case t_COMPLEX: av = avma; return gerepileupto(av, cxnorm(x));
    case t_QUAD:    av = avma; return gerepileupto(av, quadnorm(x));

    case t_POL: case t_SER: case t_RFRAC: av = avma;
      return gerepileupto(av, greal(gmul(gconj(x),x)));

    case t_FFELT:
      y=cgetg(3, t_INTMOD);
      gel(y,1) = FF_p(x);
      gel(y,2) = FF_norm(x);
      return y;
    case t_POLMOD:
      return RgXQ_norm(gel(x,2), gel(x,1));

    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = gnorm(gel(x,i));
      return y;
  }
  pari_err(typeer,"gnorm");
  return NULL; /* not reached */
}

GEN
gnorml2(GEN x)
{
  pari_sp av,lim;
  GEN y;
  long i,tx=typ(x),lx;

  if (! is_matvec_t(tx)) return gnorm(x);
  lx=lg(x); if (lx==1) return gen_0;

  av=avma; lim = stack_lim(av,1); y = gnorml2(gel(x,1));
  for (i=2; i<lx; i++)
  {
    y = gadd(y, gnorml2(gel(x,i)));
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"gnorml2");
      y = gerepileupto(av, y);
    }
  }
  return gerepileupto(av,y);
}

GEN
QuickNormL2(GEN x, long prec)
{
  pari_sp av = avma;
  GEN y = gmul(x, real_1(prec));
  if (typ(x) == t_POL) *++y = evaltyp(t_VEC) | evallg(lg(x)-1);
  return gerepileupto(av, gnorml2(y));
}

GEN
gnorml1(GEN x,long prec)
{
  pari_sp av = avma;
  long lx,i;
  GEN s;
  switch(typ(x))
  {
    case t_INT: case t_REAL:
      return mpabs(x);
    
    case t_COMPLEX: case t_FRAC: case t_QUAD:
      return gabs(x,prec);

    case t_POL:
      lx = lg(x); s = gen_0;
      for (i=2; i<lx; i++) s = gadd(s, gabs(gel(x,i),prec));
      break;

    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); s = gen_0;
      for (i=1; i<lx; i++) s = gadd(s, gabs(gel(x,i),prec));
      break;

    default: pari_err(typeer,"gnorml1");
      return NULL; /* not reached */
  }
  return gerepileupto(av, s);
}

GEN
QuickNormL1(GEN x,long prec)
{
  pari_sp av = avma;
  long lx,i;
  GEN p1,p2,s;
  switch(typ(x))
  {
    case t_INT: case t_REAL:
      return mpabs(x);
    
    case t_FRAC:
      return gabs(x,prec);

    case t_INTMOD: case t_PADIC: case t_POLMOD: case t_SER: case t_RFRAC:
      return gcopy(x);

    case t_COMPLEX:
      p1=gabs(gel(x,1),prec); p2=gabs(gel(x,2),prec);
      return gerepileupto(av, gadd(p1,p2));

    case t_QUAD:
      p1=gabs(gel(x,2),prec); p2=gabs(gel(x,3),prec);
      return gerepileupto(av, gadd(p1,p2));

    case t_POL:
      lx=lg(x); s=gen_0;
      for (i=2; i<lx; i++) s=gadd(s,QuickNormL1(gel(x,i),prec));
      return gerepileupto(av, s);

    case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); s=gen_0;
      for (i=1; i<lx; i++) s=gadd(s,QuickNormL1(gel(x,i),prec));
      return gerepileupto(av, s);
  }
  pari_err(typeer,"QuickNormL1");
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                            TRACES                               */
/*                                                                 */
/*******************************************************************/
GEN
matcompanion(GEN x)
{
  long n = degpol(x), j;
  GEN y, c;

  if (typ(x)!=t_POL) pari_err(notpoler,"matcompanion");
  if (n == 0) return cgetg(1, t_MAT);
  if (gcmp0(x)) pari_err(zeropoler,"matcompanion");

  y = cgetg(n+1,t_MAT);
  for (j=1; j < n; j++) gel(y,j) = col_ei(n, j+1);
  c = cgetg(n+1,t_COL); gel(y,n) = c;
  if (gcmp1(gel(x, n+2)))
    for (j=1; j<=n; j++) gel(c,j) = gneg(gel(x,j+1));
  else
  { /* not monic. Hardly ever used */
    pari_sp av = avma;
    GEN d = gclone(gneg(gel(x,n+2)));
    avma = av;
    for (j=1; j<=n; j++) gel(c,j) = gdiv(gel(x,j+1), d);
    gunclone(d);
  }
  return y;
}

GEN
gtrace(GEN x)
{
  pari_sp av;
  long i, lx, tx = typ(x);
  GEN y, z;

  switch(tx)
  {
    case t_INT: case t_REAL: case t_FRAC:
      return gmul2n(x,1);

    case t_COMPLEX:
      return gmul2n(gel(x,1),1);

    case t_QUAD:
      y = gel(x,1);
      if (!gcmp0(gel(y,3)))
      { /* assume quad. polynomial is either x^2 + d or x^2 - x + d */
	av = avma;
	return gerepileupto(av, gadd(gel(x,3), gmul2n(gel(x,2),1)));
      }
      return gmul2n(gel(x,2),1);

    case t_POL: case t_SER:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = gtrace(gel(x,i));
      return y;

    case t_POLMOD:
      y = gel(x,1); z = gel(x,2);
      if (typ(z) != t_POL || varn(y) != varn(z)) return gmulsg(degpol(y), z);
      av = avma;
      return gerepileupto(av, quicktrace(z, polsym(y, degpol(y)-1)));

    case t_FFELT:
      y=cgetg(3, t_INTMOD);
      gel(y,1) = FF_p(x);
      gel(y,2) = FF_trace(x);
      return y;


    case t_RFRAC:
      return gadd(x, gconj(x));

    case t_VEC: case t_COL:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = gtrace(gel(x,i));
      return y;

    case t_MAT:
      lx = lg(x); if (lx == 1) return gen_0;
      /*now lx >= 2*/
      if (lx != lg(x[1])) pari_err(mattype1,"gtrace");
      av = avma; return gerepileupto(av, mattrace(x));
  }
  pari_err(typeer,"gtrace");
  return NULL; /* not reached */
}

/* Gauss decomposition for positive definite matrix a [matrix Q, Algo 2.7.6]
 * If a is not positive definite return NULL. */
GEN
qfgaussred_positive(GEN a)
{
  pari_sp av = avma, lim=stack_lim(av,1);
  GEN b;
  long i,j,k, n = lg(a);

  if (typ(a)!=t_MAT) pari_err(typeer,"qfgaussred_positive");
  if (n == 1) return cgetg(1, t_MAT);
  if (lg(a[1])!=n) pari_err(mattype1,"qfgaussred_positive");
  b = cgetg(n,t_MAT);
  for (j=1; j<n; j++)
  {
    GEN p1=cgetg(n,t_COL), p2=gel(a,j);

    gel(b,j) = p1;
    for (i=1; i<=j; i++) p1[i] = p2[i];
    for (   ; i<n ; i++) gel(p1,i) = gen_0;
  }
  for (k=1; k<n; k++)
  {
    GEN bk, p = gcoeff(b,k,k), invp;
    if (gsigne(p)<=0) { avma = av; return NULL; } /* not positive definite */
    invp = ginv(p);
    bk = row(b, k);
    for (i=k+1; i<n; i++) gcoeff(b,k,i) = gmul(gel(bk,i), invp);
    for (i=k+1; i<n; i++)
    {
      GEN c = gel(bk, i);
      for (j=i; j<n; j++)
	gcoeff(b,i,j) = gsub(gcoeff(b,i,j), gmul(c,gcoeff(b,k,j)));
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"qfgaussred_positive");
      b=gerepilecopy(av,b);
    }
  }
  return gerepilecopy(av,b);
}

/* Gauss reduction (arbitrary symetric matrix, only the part above the
 * diagonal is considered). If signature is non-zero, return only the
 * signature, in which case gsigne() should be defined for elements of a. */
static GEN
gaussred(GEN a, long signature)
{
  GEN r, p, invp, ak, al;
  pari_sp av, av1, lim;
  long n = lg(a), i, j, k, l, sp, sn, t;

  if (typ(a) != t_MAT) pari_err(typeer,"gaussred");
  if (n == 1) return signature? mkvec2(gen_0, gen_0): cgetg(1, t_MAT);
  if (lg(a[1]) != n) pari_err(mattype1,"gaussred");
  n--;

  av = avma;
  r = const_vecsmall(n, 1);
  av1= avma; lim = stack_lim(av1,1);
  a = RgM_shallowcopy(a);
  t = n; sp = sn = 0;
  while (t)
  {
    k=1; while (k<=n && (!r[k] || gcmp0(gcoeff(a,k,k)))) k++;
    if (k <= n)
    {
      p = gcoeff(a,k,k); invp = ginv(p); /* != 0 */
      if (signature) { /* skip if (!signature): gsigne may fail ! */
	if (gsigne(p) > 0) sp++; else sn++;
      }
      r[k] = 0; t--;
      ak = row(a, k);
      for (i=1; i<=n; i++)
	gcoeff(a,k,i) = r[i]? gmul(gcoeff(a,k,i), invp): gen_0;

      for (i=1; i<=n; i++) if (r[i])
      {
	GEN c = gel(ak,i); /* - p * a[k,i] */
	if (gcmp0(c)) continue;
	for (j=1; j<=n; j++) if (r[j])
	  gcoeff(a,i,j) = gsub(gcoeff(a,i,j), gmul(c,gcoeff(a,k,j)));
      }
      gcoeff(a,k,k) = p;
    }
    else
    { /* all remaining diagonal coeffs are currently 0 */
      for (k=1; k<=n; k++) if (r[k])
      {
	l=k+1; while (l<=n && (!r[l] || gcmp0(gcoeff(a,k,l)))) l++;
	if (l > n) continue;

	p = gcoeff(a,k,l); invp = ginv(p);
	sp++; sn++;
	r[k] = r[l] = 0; t -= 2;
	ak = row(a, k);
	al = row(a, l);
	for (i=1; i<=n; i++) if (r[i])
	{
	  gcoeff(a,k,i) = gmul(gcoeff(a,k,i), p);
	  gcoeff(a,l,i) = gmul(gcoeff(a,l,i), p);
	} else {
	  gcoeff(a,k,i) = gen_0;
	  gcoeff(a,l,i) = gen_0;
	}

	for (i=1; i<=n; i++) if (r[i])
	{ /* c = a[k,i] * p, d = a[l,i] * p; */
	  GEN c = gel(ak,i), d = gel(al,i);
	  for (j=1; j<=n; j++) if (r[j])
	    gcoeff(a,i,j) = gsub(gcoeff(a,i,j),
			         gadd(gmul(gcoeff(a,l,j), c),
				      gmul(gcoeff(a,k,j), d)));
	}
	for (i=1; i<=n; i++) if (r[i])
	{
	  GEN c = gcoeff(a,k,i), d = gcoeff(a,l,i);
	  gcoeff(a,k,i) = gadd(c, d);
	  gcoeff(a,l,i) = gsub(c, d);
	}
	gcoeff(a,k,l) = gen_1;
	gcoeff(a,l,k) = gen_m1;
	gcoeff(a,k,k) = gmul2n(p,-1);
	gcoeff(a,l,l) = gneg(gcoeff(a,k,k));
	if (low_stack(lim, stack_lim(av1,1)))
	{
	  if(DEBUGMEM>1) pari_warn(warnmem,"gaussred");
	  a = gerepilecopy(av1, a);
	}
	break;
      }
      if (k > n) break;
    }
  }
  if (!signature) return gerepilecopy(av, a);
  avma = av; return mkvec2s(sp, sn);
}

GEN
qfgaussred(GEN a) { return gaussred(a,0); }

GEN
qfsign(GEN a) { return gaussred(a,1); }

static void
rot(GEN x, GEN y, GEN s, GEN u) {
  GEN x1 = subrr(x,mulrr(s,addrr(y,mulrr(u,x))));
  GEN y1 = addrr(y,mulrr(s,subrr(x,mulrr(u,y))));
  affrr(x1,x); affrr(y1,y);
}

/* Diagonalization of a REAL symetric matrix. Return a vector [L, r]:
 * L = vector of eigenvalues
 * r = matrix of eigenvectors */
GEN
jacobi(GEN a, long prec)
{
  pari_sp av1;
  long de, e, e1, e2, i, j, p, q, l = lg(a);
  GEN c, s, t, u, ja, L, r, unr, x, y;

  if (typ(a) != t_MAT) pari_err(mattype1,"jacobi");
  ja = cgetg(3,t_VEC);
  L = cgetg(l,t_COL); gel(ja,1) = L;
  r = cgetg(l,t_MAT); gel(ja,2) = r;
  if (l == 1) return ja;
  if (lg(a[1]) != l) pari_err(mattype1,"jacobi");

  e1 = HIGHEXPOBIT-1;
  for (j=1; j<l; j++)
  {
    gel(L,j) = gtofp(gcoeff(a,j,j), prec);
    e = expo(L[j]); if (e < e1) e1 = e;
  }
  for (j=1; j<l; j++)
  {
    gel(r,j) = cgetg(l,t_COL);
    for (i=1; i<l; i++) gcoeff(r,i,j) = utor(i==j? 1: 0, prec);
  }
  av1 = avma;

  e2 = -(long)HIGHEXPOBIT; p = q = 1;
  c = cgetg(l,t_MAT);
  for (j=1; j<l; j++)
  {
    gel(c,j) = cgetg(j,t_COL);
    for (i=1; i<j; i++)
    {
      gcoeff(c,i,j) = gtofp(gcoeff(a,i,j), prec);
      e = expo(gcoeff(c,i,j)); if (e > e2) { e2 = e; p = i; q = j; }
    }
  }
  a = c; unr = real_1(prec);
  de = bit_accuracy(prec);

 /* e1 = min expo(a[i,i])
  * e2 = max expo(a[i,j]), i != j */
  while (e1-e2 < de)
  {
    pari_sp av2 = avma;
    /* compute associated rotation in the plane formed by basis vectors number
     * p and q */
    x = divrr(subrr(gel(L,q),gel(L,p)), shiftr(gcoeff(a,p,q),1));
    y = sqrtr(addrr(unr, mulrr(x,x)));
    t = divrr(unr, (signe(x)>0)? addrr(x,y): subrr(x,y));
    c = sqrtr(addrr(unr,mulrr(t,t)));
    s = divrr(t,c);
    u = divrr(t,addrr(unr,c));

    /* compute successive transforms of a and the matrix of accumulated
     * rotations (r) */
    for (i=1; i<p; i++)   rot(gcoeff(a,i,p), gcoeff(a,i,q), s,u);
    for (i=p+1; i<q; i++) rot(gcoeff(a,p,i), gcoeff(a,i,q), s,u);
    for (i=q+1; i<l; i++) rot(gcoeff(a,p,i), gcoeff(a,q,i), s,u);
    y = gcoeff(a,p,q);
    t = mulrr(t, y); setexpo(y, expo(y)-de-1);
    x = gel(L,p); subrrz(x,t, x);
    y = gel(L,q); addrrz(y,t, y);
    for (i=1; i<l; i++) rot(gcoeff(r,i,p), gcoeff(r,i,q), s,u);

    e2 = expo(gcoeff(a,1,2)); p = 1; q = 2;
    for (j=1; j<l; j++)
    {
      for (i=1; i<j; i++)
	if ((e=expo(gcoeff(a,i,j))) > e2) { e2=e; p=i; q=j; }
      for (i=j+1; i<l; i++)
	if ((e=expo(gcoeff(a,j,i))) > e2) { e2=e; p=j; q=i; }
    }
    avma = av2;
  }
  avma = av1; return ja;
}

/*************************************************************************/
/**									**/
/**		    MATRICE RATIONNELLE --> ENTIERE			**/
/**									**/
/*************************************************************************/

GEN
matrixqz0(GEN x,GEN p)
{
  if (typ(x) != t_MAT) pari_err(typeer,"QM_minors_coprime");
  if (!p) return QM_minors_coprime(x,NULL);
  if (typ(p) != t_INT) pari_err(typeer,"QM_minors_coprime");
  if (signe(p)>=0) return QM_minors_coprime(x,p);
  if (equaliu(p,1)) return QM_ImZ_hnf(x); /* p = -1 */
  if (equaliu(p,2)) return QM_ImQ_hnf(x); /* p = -2 */
  pari_err(flagerr,"QM_minors_coprime"); return NULL; /* not reached */
}

GEN
QM_minors_coprime(GEN x, GEN D)
{
  pari_sp av = avma, av1, lim;
  long i, j, m, n, lP;
  GEN P, y;

  n = lg(x)-1; if (!n) return gcopy(x);
  m = lg(x[1])-1;
  if (n > m) pari_err(talker,"need more rows than columns in QM_minors_coprime");
  if (n==m)
  {
    D = det(x);
    if (gcmp0(D)) pari_err(talker,"matrix of non-maximal rank in QM_minors_coprime");
    avma = av; return matid(n);
  }
  /* m > n */
  y = x; x = cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++)
  {
    gel(x,j) = Q_primpart(gel(y,j));
    RgV_check_ZV(gel(x,j), "QM_minors_coprime");
  }

  /* x now a ZM */
  if (!D || gcmp0(D))
  {
    pari_sp av2 = avma;
    D = ZM_detmult(shallowtrans(x));
    if (is_pm1(D)) { avma = av2; return ZM_copy(x); }
  }
  P = gel(Z_factor(D), 1); lP = lg(P);
  av1 = avma; lim = stack_lim(av1,1);
  for (i=1; i < lP; i++)
  {
    GEN p = gel(P,i), pov2 = shifti(p, -1);
    for(;;)
    {
      GEN N, M = FpM_ker(x, p);
      long lM = lg(M);
      if (lM==1) break;

      M = FpM_center(M, p, pov2);
      N = ZM_Z_divexact(ZM_mul(x,M), p);
      for (j=1; j<lM; j++)
      {
	long k = n; while (!signe(gcoeff(M,k,j))) k--;
	gel(x,k) = gel(N,j);
      }
      if (low_stack(lim, stack_lim(av1,1)))
      {
	if (DEBUGMEM>1) pari_warn(warnmem,"QM_minors_coprime, prime p = %Ps", p);
	x = gerepilecopy(av1, x);
      }
    }
  }
  return gerepilecopy(av, x);
}

static GEN
RgC_Z_mul(GEN A, GEN u)
{
  long s = signe(u);
  if (is_pm1(u)) return s > 0? A: RgC_neg(A);
  return s? gmul(u,A): zerocol(lg(A)-1);
}

/* u,v integral, A,B RgC */
static GEN
RgC_lincomb(GEN u, GEN v, GEN A, GEN B)
{
  if (!signe(u)) return RgC_Z_mul(B,v);
  if (!signe(v)) return RgC_Z_mul(A,u);
  return RgC_add(RgC_Z_mul(A,u), RgC_Z_mul(B,v));
}

/* cf ZC_elem */
/* zero aj = Aij (!= 0)  using  ak = Aik (maybe 0), via linear combination of
 * A[j] and A[k] of determinant 1. */
static void
QC_elem(GEN aj, GEN ak, GEN A, long j, long k)
{
  GEN p1, u, v, d;

  if (gcmp0(ak)) { swap(gel(A,j), gel(A,k)); return; }
  if (typ(aj) == t_INT) {
    if (typ(ak) != t_INT) { aj = mulii(aj, gel(ak,2)); ak = gel(ak,1); }
  } else {
    if (typ(ak) == t_INT) { ak = mulii(ak, gel(aj,2)); aj = gel(aj,1); }
    else {
      GEN daj = gel(aj,2), dak = gel(ak,2), D = gcdii(daj, dak);
      aj = gel(aj,1); ak = gel(ak,1);
      if (!is_pm1(D)) { daj = diviiexact(daj, D); dak = diviiexact(dak, D); }
      if (!is_pm1(dak)) aj = mulii(aj, dak);
      if (!is_pm1(daj)) ak = mulii(ak, daj);
    }
  }
  /* aj,ak were multiplied by their least common denominator */

  d = bezout(aj,ak,&u,&v);
  /* frequent special case (u,v) = (1,0) or (0,1) */
  if (!signe(u))
  { /* ak | aj */
    GEN c = negi(diviiexact(aj,ak));
    gel(A,j) = RgC_lincomb(gen_1, c, gel(A,j), gel(A,k));
    return;
  }
  if (!signe(v))
  { /* aj | ak */
    GEN c = negi(diviiexact(ak,aj));
    gel(A,k) = RgC_lincomb(gen_1, c, gel(A,k), gel(A,j));
    swap(gel(A,j), gel(A,k));
    return;
  }

  if (!is_pm1(d)) { aj = diviiexact(aj,d); ak = diviiexact(ak,d); }
  p1 = gel(A,k);
  gel(A,k) = RgC_lincomb(u,v, gel(A,j),p1);
  gel(A,j) = RgC_lincomb(negi(aj),ak, p1,gel(A,j));
}

static GEN
QM_imZ_hnf_aux(GEN A)
{
  pari_sp av = avma, lim = stack_lim(av,1);
  long i,j,k,n,m;
  GEN a;

  n = lg(A);
  if (n == 1) return cgetg(1,t_MAT);
  if (n == 2) {
    A = Q_primpart(A);
    if ( ZV_cmp0(gel(A,1)) ) A = cgetg(1,t_MAT);
    return A;
  }
  m = lg(A[1]);
  for (i=1; i<m; i++)
  {
    for (j = k = 1; j<n; j++)
    {
      GEN a = gcoeff(A,i,j);
      if (gcmp0(a)) continue;

      k = j+1; if (k == n) k = 1;
      /* zero a = Aij  using  b = Aik */
      QC_elem(a, gcoeff(A,i,k), A, j,k);
    }
    a = gcoeff(A,i,k);
    if (!gcmp0(a))
    {
      a = Q_denom(a);
      if (!is_pm1(a)) gel(A,k) = RgC_Rg_mul(gel(A,k), a);
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"QM_imZ_hnf_aux");
      A = gerepilecopy(av,A);
    }
  }
  return ZM_hnf(A);
}

GEN
QM_ImZ_hnf(GEN x)
{
  pari_sp av = avma;
  return gerepileupto(av, QM_imZ_hnf_aux( RgM_shallowcopy(x) ));
}

GEN
QM_ImQ_hnf(GEN x)
{
  pari_sp av = avma, av1, lim;
  long j,j1,k,m,n;
  GEN c;

  n = lg(x); if (n==1) return gcopy(x);
  m = lg(x[1]); x = RgM_shallowcopy(x);
  c = const_vecsmall(n-1, 0);
  av1 = avma; lim = stack_lim(av1,1);
  for (k=1; k<m; k++)
  {
    j=1; while (j<n && (c[j] || gcmp0(gcoeff(x,k,j)))) j++;
    if (j==n) continue;

    c[j]=k; gel(x,j) = RgC_Rg_div(gel(x,j),gcoeff(x,k,j));
    for (j1=1; j1<n; j1++)
      if (j1!=j)
      {
	GEN t = gcoeff(x,k,j1);
	if (!gcmp0(t)) gel(x,j1) = RgC_sub(gel(x,j1), RgC_Rg_mul(gel(x,j),t));
      }
    if (low_stack(lim, stack_lim(av1,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"QM_ImQ_hnf");
      x = gerepilecopy(av1,x);
    }
  }
  return gerepileupto(av, QM_imZ_hnf_aux(x));
}

GEN
intersect(GEN x, GEN y)
{
  long j, lx = lg(x);
  pari_sp av;
  GEN z;

  if (typ(x)!=t_MAT || typ(y)!=t_MAT) pari_err(typeer,"intersect");
  if (lx==1 || lg(y)==1) return cgetg(1,t_MAT);

  av = avma; z = ker(shallowconcat(x,y));
  for (j=lg(z)-1; j; j--) setlg(z[j], lx);
  return gerepileupto(av, RgM_mul(x,z));
}
