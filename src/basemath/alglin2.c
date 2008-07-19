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
  }
  pari_err(flagerr,"charpoly"); return NULL; /* not reached */
}

/* (v - x)^d */
static GEN
caract_const(pari_sp av, GEN x, long v, long d)
{
  return gerepileupto(av, gpowgs(deg1pol_shallow(gen_1, gneg_i(x), v), d));
}

/* return caract(Mod(x,p)) in variable v */
GEN
caract2(GEN p, GEN x, long v)
{
  pari_sp av = avma;
  long d = degpol(p), dx;
  GEN ch, L;

  if (typ(x) != t_POL) return caract_const(av, x, v, d);
  dx = degpol(x);
  if (dx <= 0)
    return dx? monomial(gen_1, d, v): caract_const(av, gel(x,2), v, d);

  x = gneg_i(x);
  if (varn(x) == MAXVARN) { setvarn(x, 0); p = shallowcopy(p); setvarn(p, 0); }
  gel(x,2) = gadd(gel(x,2), pol_x(MAXVARN));
  ch = resultant_all(p, x, NULL);
  if (v != MAXVARN)
  {
    if (typ(ch) == t_POL && varn(ch) == MAXVARN)
      setvarn(ch, v);
    else
      ch = gsubst(ch, MAXVARN, pol_x(v));
  }
  L = leading_term(ch);
  if (!gcmp1(L)) ch = RgX_Rg_div(ch, L);
  return gerepileupto(av, ch);
}

/* characteristic polynomial (in v) of x over nf, where x is an element of the
 * algebra nf[t]/(Q(t)) */
GEN
rnfcharpoly(GEN nf, GEN Q, GEN x, long v)
{
  long tx = typ(x), vQ = varn(Q), dQ = degpol(Q), vx, vT;
  pari_sp av = avma;
  GEN T;

  if (v < 0) v = 0;
  nf = checknf(nf); T = gel(nf,1); vT = varn(T);
  Q = fix_relative_pol(T,Q,0);
  if (tx == t_POLMOD) {
    GEN M = gel(x,1);
    long vM = varn(M);
    int ok = 1;
    if      (vM == vQ) { if (!RgX_equal(M, Q)) ok = 0; }
    else if (vM == vT) { if (!RgX_equal(M, T)) ok = 0; }
    else ok = 0;
    if (!ok) pari_err(consister,"rnfcharpoly");
    x = gel(x, 2); tx = typ(x);
  }
  if (tx != t_POL) {
    if (!is_rational_t(tx)) pari_err(typeer,"rnfcharpoly");
    return caract_const(av, x, v, dQ);
  }
  vx = varn(x);
  if (vx == vT) return caract_const(av, mkpolmod(x,T), v, dQ);
  if (vx != vQ) pari_err(typeer,"rnfcharpoly");
  x = fix_relative_pol(T,x,0);
  if (degpol(x) >= dQ) x = RgX_rem(x, Q);
  if (dQ <= 1) return caract_const(av, constant_term(x), v, 1);
  return gerepilecopy(av, lift_if_rational( caract2(Q, x, v) ));
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
      return caract2(gel(x,1), gel(x,2), v);

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

GEN
caract(GEN x, long v)
{
  long k, n;
  pari_sp av=avma;
  GEN  T, C, x_k, Q;

  if ((T = easychar(x,v,NULL))) return T;

  n = lg(x)-1;
  if (n == 1) return gerepileupto(av, deg1pol(gen_1, gneg(gcoeff(x,1,1)), v));

  x_k = pol_x(v); /* to be modified in place */
  T = det(x); C = utoineg(n); Q = pol_x(v);
  for (k=1; k<=n; k++)
  {
    GEN mk = utoineg(k), d;
    gel(x_k,2) = mk;
    d = det(RgM_Rg_add_shallow(x, mk));
    T = RgX_add(gmul(T, x_k), RgX_Rg_mul(Q, gmul(C, d)));
    if (k == n) break;

    Q = RgX_mul(Q, x_k);
    C = diviuexact(mulsi(k-n,C), k+1); /* (-1)^k binomial(n,k) */
  }
  return gerepileupto(av, RgX_Rg_div(T, mpfact(n)));
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
  if (l == 2) { if (py) *py = matid(1); return p; }
  if (l == 3) {
    GEN a = gcoeff(x,1,1), b = gcoeff(x,1,2);
    GEN c = gcoeff(x,2,1), d = gcoeff(x,2,2);
    if (py) {
      y = cgetg(3, t_MAT);
      gel(y,1) = mkcol2(gcopy(d), gneg(c));
      gel(y,2) = mkcol2(gneg(b), gcopy(a));
      *py = y;
    }
    av = avma;
    gel(p,2) = gerepileupto(av, gsub(gmul(a,d), gmul(b,c)));
    return p;
  }
  /* l > 3 */
  av = avma; y = shallowcopy(x);
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
  i = gvar2(p);
  if (i == v) pari_err(talker,"incorrect variable in caradj");
  if (i < v) p = gerepileupto(av0, poleval(p, pol_x(v)));
  if (py) *py = (l & 1)? gneg(y): gcopy(y);
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
  pari_sp av = avma, av2 = avma, lim;
  long lx = lg(x), m, i, j;
  GEN p, p1;

  if (typ(x) != t_MAT) pari_err(mattype1,"hess");
  if (lx == 1) return cgetg(1,t_MAT);
  if (lg(x[1]) != lx) pari_err(mattype1,"hess");
  x = shallowcopy(x); lim = stack_lim(av,1);

  for (m=2; m<lx-1; m++)
    for (i=m+1; i<lx; i++)
    {
      p = gcoeff(x,i,m-1);
      if (gcmp0(p)) continue;

      for (j=m-1; j<lx; j++) swap(gcoeff(x,i,j), gcoeff(x,m,j));
      swap(gel(x,i), gel(x,m)); p = ginv(p);
      for (i=m+1; i<lx; i++)
      {
	p1 = gcoeff(x,i,m-1);
	if (gcmp0(p1)) continue;

	p1 = gmul(p1,p);
	gcoeff(x,i,m-1) = gen_0;
	for (j=m; j<lx; j++)
	  gcoeff(x,i,j) = gsub(gcoeff(x,i,j), gmul(p1,gcoeff(x,m,j)));
	for (j=1; j<lx; j++)
	  gcoeff(x,j,m) = gadd(gcoeff(x,j,m), gmul(p1,gcoeff(x,j,i)));
      }
      if (low_stack(lim, stack_lim(av,1)))
      {
	if (DEBUGMEM>1) pari_warn(warnmem,"hess, m = %ld", m);
	x = gerepilecopy(av2, x);
      }
      break;
    }
  return gerepilecopy(av,x);
}

GEN
carhess(GEN x, long v)
{
  pari_sp av;
  long lx, r, i;
  GEN y, H, X_h;

  if ((H = easychar(x,v,NULL))) return H;

  lx = lg(x); av = avma; y = cgetg(lx+1, t_VEC);
  gel(y,1) = pol_1(v); H = hess(x);
  X_h = pol_x(v);
  for (r = 1; r < lx; r++)
  {
    GEN p3 = gen_1, p4 = gen_0;
    for (i = r-1; i; i--)
    {
      p3 = gmul(p3, gcoeff(H,i+1,i));
      p4 = gadd(p4, gmul(gmul(p3,gcoeff(H,i,r)), gel(y,i)));
    }
    gel(X_h,2) = gneg(gcoeff(H,r,r));
    gel(y,r+1) = gsub(gmul(gel(y,r), X_h), p4);
  }
  return gerepileupto(av, gel(y,lx));
}

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
      for (j = 2; j <= min(r,i); j++) t = gadd(t, gmul(gel(C,i+1-j), gel(V,j)));
      gel(Q,i) = gerepileupto(av, t);
    }
    for (i = 1; i <= r+1; i++) V[i] = Q[i];
  }
  V = gtopoly(V, v);
  if (!odd(lx)) V = gneg(V);
  return gerepileupto(av0, V);
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
  long lx, i, tx=typ(x);
  GEN y;

  switch(tx)
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
      lx=lg(x); y=cgetg(lx,tx);
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
    case t_INT: case t_REAL: case t_COMPLEX: case t_FRAC: case t_QUAD:
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
    case t_INT: case t_REAL: case t_FRAC:
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
/*                          CONJUGATION                            */
/*                                                                 */
/*******************************************************************/

/* lift( conj(Mod(x, y)) ), assuming degpol(y) = 2, degpol(x) < 2 */
GEN
quad_polmod_conj(GEN x, GEN y)
{
  GEN z, u, v, a, b;
  pari_sp av;
  if (typ(x) != t_POL || varn(x) != varn(y) || degpol(x) <= 0)
    return gcopy(x);
  a = gel(y,4); u = gel(x,3); /*Mod(ux + v, ax^2 + bx + c)*/
  b = gel(y,3); v = gel(x,2);
  z = cgetg(4, t_POL); z[1] = x[1]; av = avma;
  gel(z,2) = gerepileupto(av, gsub(v, gdiv(gmul(u,b), a)));
  gel(z,3) = gneg(u); return z;
}
GEN
quad_polmod_norm(GEN x, GEN y)
{
  GEN z, u, v, a, b, c;
  pari_sp av;
  if (typ(x) != t_POL || varn(x) != varn(y) || degpol(x) <= 0)
    return gsqr(x);
  a = gel(y,4); u = gel(x,3); /*Mod(ux + v, ax^2 + bx + c)*/
  b = gel(y,3); v = gel(x,2);
  c = gel(y,2); av = avma;
  z = gmul(u, gsub(gmul(c,u), gmul(b,v)));
  if (!gcmp1(a)) z = gdiv(z, a);
  return gerepileupto(av, gadd(z, gsqr(v)));
}

GEN
gconj(GEN x)
{
  long lx, i, tx = typ(x);
  GEN z;

  switch(tx)
  {
    case t_INT: case t_REAL: case t_INTMOD: case t_FRAC: case t_PADIC:
      return gcopy(x);

    case t_COMPLEX:
      z = cgetg(3,t_COMPLEX);
      gel(z,1) = gcopy(gel(x,1));
      gel(z,2) = gneg(gel(x,2));
      break;

    case t_QUAD:
      z = cgetg(4,t_QUAD);
      gel(z,1) = gcopy(gel(x,1));
      gel(z,2) = gcmp0(gmael(x,1,3))? gcopy(gel(x,2))
				    : gadd(gel(x,2), gel(x,3));
      gel(z,3) = gneg(gel(x,3));
      break;

    case t_POL: case t_SER: case t_RFRAC: case t_VEC: case t_COL: case t_MAT:
      z = init_gen_op(x, tx, &lx, &i);
      for (; i<lx; i++) gel(z,i) = gconj(gel(x,i));
      break;

    case t_POLMOD:
    {
      GEN z, X = gel(x,1);
      long d = degpol(X);
      if (d < 2) return gcopy(x);
      if (d == 2) {
	z = cgetg(3, t_POLMOD);
	gel(z,1) = gcopy(X);
	gel(z,2) = quad_polmod_conj(gel(x,2), X); return z;
      }
    }
    default:
      pari_err(typeer,"gconj");
      return NULL; /* not reached */
  }
  return z;
}

GEN
conjvec(GEN x,long prec)
{
  long lx, s, i;
  GEN z;

  switch(typ(x))
  {
    case t_INT: case t_INTMOD: case t_FRAC:
      return mkcolcopy(x);

    case t_COMPLEX: case t_QUAD:
      z=cgetg(3,t_COL); gel(z,1) = gcopy(x); gel(z,2) = gconj(x); break;

    case t_VEC: case t_COL:
      lx = lg(x); z = cgetg(lx,t_MAT);
      if (lx == 1) return z;
      gel(z,1) = conjvec(gel(x,1),prec);
      s = lg(gel(z,1));
      for (i=2; i<lx; i++)
      {
        gel(z,i) = conjvec(gel(x,i),prec);
        if (lg(gel(z,i)) != s)
          pari_err(talker,"incompatible field degrees in conjvec");
      }
      break;

    case t_POLMOD: {
      GEN T = gel(x,1), r;
      pari_sp av;

      lx = lg(T);
      if (lx <= 3) return cgetg(1,t_COL);
      x = gel(x,2);
      for (i=2; i<lx; i++)
      {
        GEN c = gel(T,i);
        switch(typ(c)) {
	  case t_INTMOD: {
            GEN p = gel(c,1);
            T = RgX_to_FpX(T,p); /* left on stack */
            z = cgetg(lx-2,t_COL);
            if (typ(x) == t_POL) {
              x = RgX_to_FpX(x, p);
              if (varn(x) != varn(T))
                pari_err(talker,"not a rational polynomial in conjvec");
              gel(z,1) = x;
              for (i=2; i<=lx-3; i++) gel(z,i) = FpXQ_pow(gel(z,i-1), p, T, p);
            } else {
              x = Rg_to_Fp(x, p);
              for (i=1; i<=lx-3; i++) gel(z,i) = x;
            }
            return z;
          }
          case t_INT:
          case t_FRAC: break;
          default: pari_err(talker,"not a rational polynomial in conjvec");
        }
      }
      av = avma;
      if (varn(x) != varn(T))
        pari_err(talker,"inconsistent variables in conjvec");
      r = cleanroots(T,prec);
      z = cgetg(lx-2,t_COL);
      for (i=1; i<=lx-3; i++) gel(z,i) = poleval(x, gel(r,i));
      return gerepileupto(av, z);
    }

    default:
      pari_err(typeer,"conjvec");
      return NULL; /* not reached */
  }
  return z;
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
      lx = lg(x); y = cgetg(lx,tx); y[1] = x[1];
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
      lx = lg(x); y = cgetg(lx,tx);
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
  a = shallowcopy(a);
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
  return gerepileupto(av, QM_imZ_hnf_aux( shallowcopy(x) ));
}

GEN
QM_ImQ_hnf(GEN x)
{
  pari_sp av = avma, av1, lim;
  long j,j1,k,m,n;
  GEN c;

  n = lg(x); if (n==1) return gcopy(x);
  m = lg(x[1]); x = shallowcopy(x);
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

/**************************************************************/
/**                                                          **/
/**		   HERMITE NORMAL FORM REDUCTION	     **/
/**							     **/
/**************************************************************/
GEN
mathnf0(GEN x, long flag)
{
  if (typ(x)!=t_MAT) pari_err(typeer,"mathnf0");
  RgM_check_ZM(x, "mathnf0");
  switch(flag)
  {
    case 0: return ZM_hnf(x);
    case 1: return hnfall(x);
    case 3: return hnfperm(x);
    case 4: return hnflll(x);
    default: pari_err(flagerr,"mathnf");
  }
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                SPECIAL HNF (FOR INTERNAL USE !!!)               */
/*                                                                 */
/*******************************************************************/
static int
count(GEN mat, long row, long len, long *firstnonzero)
{
  long j, n = 0;

  for (j=1; j<=len; j++)
  {
    long p = mael(mat,j,row);
    if (p)
    {
      if (labs(p)!=1) return -1;
      n++; *firstnonzero=j;
    }
  }
  return n;
}

static int
count2(GEN mat, long row, long len)
{
  long j;
  for (j=len; j; j--)
    if (labs(mael(mat,j,row)) == 1) return j;
  return 0;
}

static GEN
hnffinal(GEN matgen,GEN perm,GEN* ptdep,GEN* ptB,GEN* ptC)
{
  GEN p1,p2,U,H,Hnew,Bnew,Cnew,diagH1;
  GEN B = *ptB, C = *ptC, dep = *ptdep, depnew;
  pari_sp av, lim;
  long i,j,k,s,i1,j1,zc;
  long co = lg(C);
  long col = lg(matgen)-1;
  long lnz, nlze, lig;

  if (col == 0) return matgen;
  lnz = lg(matgen[1])-1; /* was called lnz-1 - nr in hnfspec */
  nlze = lg(dep[1])-1;
  lig = nlze + lnz;
  if (DEBUGLEVEL>5)
  {
    fprintferr("Entering hnffinal:\n");
    if (DEBUGLEVEL>6)
    {
      if (nlze) fprintferr("dep = %Ps\n",dep);
      fprintferr("mit = %Ps\n",matgen);
      fprintferr("B = %Ps\n",B);
    }
  }
  /* H: lnz x lnz [disregarding initial 0 cols], U: col x col */
  H = ZM_hnflll(matgen, &U, 0);
  H += (lg(H)-1 - lnz); H[0] = evaltyp(t_MAT) | evallg(lnz+1);
  /* Only keep the part above the H (above the 0s is 0 since the dep rows
   * are dependent from the ones in matgen) */
  zc = col - lnz; /* # of 0 columns, correspond to units */
  if (nlze) { dep = ZM_mul(dep,U); dep += zc; }

  diagH1 = new_chunk(lnz+1); /* diagH1[i] = 0 iff H[i,i] != 1 (set later) */

  av = avma; lim = stack_lim(av,1);
  Cnew = cgetg(co, typ(C));
  setlg(C, col+1); p1 = gmul(C,U);
  for (j=1; j<=col; j++) Cnew[j] = p1[j];
  for (   ; j<co ; j++)  Cnew[j] = C[j];
  if (DEBUGLEVEL>5) fprintferr("    hnflll done\n");

  /* Clean up B using new H */
  for (s=0,i=lnz; i; i--)
  {
    GEN Di = gel(dep,i), Hi = gel(H,i);
    GEN h = gel(Hi,i); /* H[i,i] */
    if ( (diagH1[i] = gcmp1(h)) ) { h = NULL; s++; }
    for (j=col+1; j<co; j++)
    {
      GEN z = gel(B,j-col);
      p1 = gel(z,i+nlze); if (!signe(p1)) continue;

      if (h) p1 = gdivent(p1,h);
      for (k=1; k<=nlze; k++) gel(z,k) = subii(gel(z,k), mulii(p1, gel(Di,k)));
      for (   ; k<=lig;  k++) gel(z,k) = subii(gel(z,k), mulii(p1, gel(Hi,k-nlze)));
      gel(Cnew,j) = gsub(gel(Cnew,j), gmul(p1, gel(Cnew,i+zc)));
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"hnffinal, i = %ld",i);
      gerepileall(av, 2, &Cnew, &B);
    }
  }
  p1 = cgetg(lnz+1,t_VEC); p2 = perm + nlze;
  for (i1=0, j1=lnz-s, i=1; i<=lnz; i++) /* push the 1 rows down */
    if (diagH1[i])
      p1[++j1] = p2[i];
    else
      p2[++i1] = p2[i];
  for (i=i1+1; i<=lnz; i++) p2[i] = p1[i];
  if (DEBUGLEVEL>5) fprintferr("    first pass in hnffinal done\n");

  /* s = # extra redundant generators taken from H
   *          zc  col-s  co   zc = col - lnz
   *       [ 0 |dep |     ]    i = lnze + lnz - s = lig - s
   *  nlze [--------|  B' ]
   *       [ 0 | H' |     ]    H' = H minus the s rows with a 1 on diagonal
   *     i [--------|-----] lig-s           (= "1-rows")
   *       [   0    | Id  ]
   *       [        |     ] li */
  lig -= s; col -= s; lnz -= s;
  Hnew = cgetg(lnz+1,t_MAT);
  depnew = cgetg(lnz+1,t_MAT); /* only used if nlze > 0 */
  Bnew = cgetg(co-col,t_MAT);
  C = shallowcopy(Cnew);
  for (j=1,i1=j1=0; j<=lnz+s; j++)
  {
    GEN z = gel(H,j);
    if (diagH1[j])
    { /* hit exactly s times */
      i1++; C[i1+col] = Cnew[j+zc];
      p1 = cgetg(lig+1,t_COL); gel(Bnew,i1) = p1;
      for (i=1; i<=nlze; i++) gel(p1,i) = gcoeff(dep,i,j);
      p1 += nlze;
    }
    else
    {
      j1++; C[j1+zc] = Cnew[j+zc];
      p1 = cgetg(lnz+1,t_COL); gel(Hnew,j1) = p1;
      depnew[j1] = dep[j];
    }
    for (i=k=1; k<=lnz; i++)
      if (!diagH1[i]) p1[k++] = z[i];
  }
  for (j=s+1; j<co-col; j++)
  {
    GEN z = gel(B,j-s);
    p1 = cgetg(lig+1,t_COL); gel(Bnew,j) = p1;
    for (i=1; i<=nlze; i++) p1[i] = z[i];
    z += nlze; p1 += nlze;
    for (i=k=1; k<=lnz; i++)
      if (!diagH1[i]) p1[k++] = z[i];
  }
  if (DEBUGLEVEL>5)
  {
    fprintferr("Leaving hnffinal\n");
    if (DEBUGLEVEL>6)
    {
      if (nlze) fprintferr("dep = %Ps\n",depnew);
      fprintferr("mit = %Ps\nB = %Ps\nC = %Ps\n", Hnew, Bnew, C);
    }
  }
  *ptdep = depnew;
  *ptC = C;
  *ptB = Bnew; return Hnew;
}

/* for debugging */
static void
p_mat(GEN mat, GEN perm, long k)
{
  pari_sp av = avma;
  perm = vecslice(perm, k+1, lg(perm)-1);
  fprintferr("Permutation: %Ps\n",perm);
  if (DEBUGLEVEL > 6)
    fprintferr("matgen = %Ps\n", zm_to_ZM( rowpermute(mat, perm) ));
  avma = av;
}

static GEN
col_dup(long l, GEN col)
{
  GEN c = new_chunk(l);
  memcpy(c,col,l * sizeof(long)); return c;
}

/* HNF reduce a relation matrix (column operations + row permutation)
** Input:
**   mat = (li-1) x (co-1) matrix of long
**   C   = r x (co-1) matrix of GEN
**   perm= permutation vector (length li-1), indexing the rows of mat: easier
**     to maintain perm than to copy rows. For columns we can do it directly
**     using e.g. swap(mat[i], mat[j])
**   k0 = integer. The k0 first lines of mat are dense, the others are sparse.
** Output: cf ASCII art in the function body
**
** row permutations applied to perm
** column operations applied to C. IN PLACE
**/
GEN
hnfspec_i(GEN mat0, GEN perm, GEN* ptdep, GEN* ptB, GEN* ptC, long k0)
{
  pari_sp av, lim;
  long co, n, s, nlze, lnz, nr, i, j, k, lk0, col, lig, *p;
  GEN matj, mat;
  GEN p1, p2, matb, matbnew, vmax, matt, T, extramat, B, C, H, dep, permpro;
  const long li = lg(perm); /* = lg(mat0[1]) */
  const long CO = lg(mat0);

  n = 0; /* -Wall */

  C = *ptC; co = CO;
  if (co > 300 && co > 1.5 * li)
  { /* treat the rest at the end */
    co = (long)(1.2 * li);
    setlg(C, co);
  }

  if (DEBUGLEVEL>5)
  {
    fprintferr("Entering hnfspec\n");
    p_mat(mat0,perm,0);
  }
  matt = cgetg(co, t_MAT); /* dense part of mat (top) */
  mat = cgetg(co, t_MAT);
  for (j = 1; j < co; j++)
  {
    matj = col_dup(li, gel(mat0,j));
    p1 = cgetg(k0+1,t_COL); gel(matt,j) = p1; gel(mat,j) = matj;
    for (i=1; i<=k0; i++) gel(p1,i) = stoi(matj[perm[i]]);
  }
  vmax = cgetg(co,t_VECSMALL);
  av = avma; lim = stack_lim(av,1);

  i = lig = li-1; col = co-1; lk0 = k0;
  T = (k0 || (lg(C) > 1 && lg(C[1]) > 1))? matid(col): NULL;
  /* Look for lines with a single non-0 entry, equal to 1 in absolute value */
  while (i > lk0)
    switch( count(mat,perm[i],col,&n) )
    {
      case 0: /* move zero lines between k0+1 and lk0 */
	lk0++; lswap(perm[i], perm[lk0]);
	i = lig; continue;

      case 1: /* move trivial generator between lig+1 and li */
	lswap(perm[i], perm[lig]);
	if (T) swap(gel(T,n), gel(T,col));
	swap(gel(mat,n), gel(mat,col)); p = gel(mat,col);
	if (p[perm[lig]] < 0) /* = -1 */
	{ /* convert relation -g = 0 to g = 0 */
	  for (i=lk0+1; i<lig; i++) p[perm[i]] = -p[perm[i]];
	  if (T)
	  {
	    p1 = gel(T,col);
	    for (i=1; ; i++) /* T is a permuted identity: single non-0 entry */
	      if (signe(gel(p1,i))) { togglesign_safe(&gel(p1,i)); break; }
	  }
	}
	lig--; col--; i = lig; continue;

      default: i--;
    }
  if (DEBUGLEVEL>5)
  {
    fprintferr("    after phase1:\n");
    p_mat(mat,perm,0);
  }

#define absmax(s,z) {long _z; _z = labs(z); if (_z > s) s = _z;}
  /* Get rid of all lines containing only 0 and +/- 1, keeping track of column
   * operations in T. Leave the rows 1..lk0 alone [up to k0, coefficient
   * explosion, between k0+1 and lk0, row is 0] */
  s = 0;
  while (lig > lk0 && s < (long)(HIGHBIT>>1))
  {
    for (i=lig; i>lk0; i--)
      if (count(mat,perm[i],col,&n) > 0) break;
    if (i == lk0) break;

    /* only 0, +/- 1 entries, at least 2 of them non-zero */
    lswap(perm[i], perm[lig]);
    swap(gel(mat,n), gel(mat,col)); p = gel(mat,col);
    if (T) swap(gel(T,n), gel(T,col));
    if (p[perm[lig]] < 0)
    {
      for (i=lk0+1; i<=lig; i++) p[perm[i]] = -p[perm[i]];
      if (T) ZV_togglesign(gel(T,col));
    }
    for (j=1; j<col; j++)
    {
      long t;
      matj = gel(mat,j);
      if (! (t = matj[perm[lig]]) ) continue;
      if (t == 1) {
	for (i=lk0+1; i<=lig; i++) absmax(s, matj[perm[i]] -= p[perm[i]]);
      }
      else { /* t = -1 */
	for (i=lk0+1; i<=lig; i++) absmax(s, matj[perm[i]] += p[perm[i]]);
      }
      if (T) ZC_lincomb1_inplace(gel(T,j), gel(T,col), stoi(-t));
    }
    lig--; col--;
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"hnfspec[1]");
      if (T) T = gerepilecopy(av, T); else avma = av;
    }
  }
  /* As above with lines containing a +/- 1 (no other assumption).
   * Stop when single precision becomes dangerous */
  for (j=1; j<=col; j++)
  {
    matj = gel(mat,j);
    for (s=0, i=lk0+1; i<=lig; i++) absmax(s, matj[i]);
    vmax[j] = s;
  }
  while (lig > lk0)
  {
    for (i=lig; i>lk0; i--)
      if ( (n = count2(mat,perm[i],col)) ) break;
    if (i == lk0) break;

    lswap(vmax[n], vmax[col]);
    lswap(perm[i], perm[lig]);
    swap(gel(mat,n), gel(mat,col)); p = gel(mat,col);
    if (T) swap(gel(T,n), gel(T,col));
    if (p[perm[lig]] < 0)
    {
      for (i=lk0+1; i<=lig; i++) p[perm[i]] = -p[perm[i]];
      if (T) ZV_togglesign(gel(T,col));
    }
    for (j=1; j<col; j++)
    {
      long t;
      matj = gel(mat,j);
      if (! (t = matj[perm[lig]]) ) continue;
      if (vmax[col] && (ulong)labs(t) >= (HIGHBIT-vmax[j]) / vmax[col])
	goto END2;

      for (s=0, i=lk0+1; i<=lig; i++) absmax(s, matj[perm[i]] -= t*p[perm[i]]);
      vmax[j] = s;
      if (T) ZC_lincomb1_inplace(gel(T,j), gel(T,col), stoi(-t));
    }
    lig--; col--;
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"hnfspec[2]");
      if (T) T = gerepilecopy(av,T); else avma = av;
    }
  }

END2: /* clean up mat: remove everything to the right of the 1s on diagonal */
  /* go multiprecision first */
  matb = cgetg(co,t_MAT); /* bottom part (complement of matt) */
  for (j=1; j<co; j++)
  {
    p1 = cgetg(li-k0,t_COL); gel(matb,j) = p1;
    p1 -= k0; matj = gel(mat,j);
    for (i=k0+1; i<li; i++) gel(p1,i) = stoi(matj[perm[i]]);
  }
  if (DEBUGLEVEL>5)
  {
    fprintferr("    after phase2:\n");
    p_mat(mat,perm,lk0);
  }
  for (i=li-2; i>lig; i--)
  {
    long h, i0 = i - k0, k = i + co-li;
    GEN Bk = gel(matb,k);
    for (j=k+1; j<co; j++)
    {
      GEN Bj = gel(matb,j), v = gel(Bj,i0);
      s = signe(v); if (!s) continue;

      gel(Bj,i0) = gen_0;
      if (is_pm1(v))
      {
	if (s > 0) /* v = 1 */
	{ for (h=1; h<i0; h++) gel(Bj,h) = subii(gel(Bj,h), gel(Bk,h)); }
	else /* v = -1 */
	{ for (h=1; h<i0; h++) gel(Bj,h) = addii(gel(Bj,h), gel(Bk,h)); }
      }
      else {
	for (h=1; h<i0; h++) gel(Bj,h) = subii(gel(Bj,h), mulii(v,gel(Bk,h)));
      }
      if (T) ZC_lincomb1_inplace(gel(T,j), gel(T,k), negi(v));
      if (low_stack(lim, stack_lim(av,1)))
      {
	if(DEBUGMEM>1) pari_warn(warnmem,"hnfspec[3], (i,j) = %ld,%ld", i,j);
	for (h=1; h<co; h++) setlg(matb[h], i0+1); /* bottom can be forgotten */
	gerepileall(av, T? 2: 1, &matb, &T);
	Bk = gel(matb,k);
      }
    }
  }
  for (j=1; j<co; j++) setlg(matb[j], lig-k0+1); /* bottom can be forgotten */
  gerepileall(av, T? 2: 1, &matb, &T);
  if (DEBUGLEVEL>5) fprintferr("    matb cleaned up (using Id block)\n");

  nlze = lk0 - k0;  /* # of 0 rows */
  lnz = lig-nlze+1; /* 1 + # of non-0 rows (!= 0...0 1 0 ... 0) */
  if (T) matt = ZM_mul(matt,T); /* update top rows */
  extramat = cgetg(col+1,t_MAT); /* = new C minus the 0 rows */
  for (j=1; j<=col; j++)
  {
    GEN z = gel(matt,j);
    GEN t = (gel(matb,j)) + nlze - k0;
    p2=cgetg(lnz,t_COL); gel(extramat,j) = p2;
    for (i=1; i<=k0; i++) p2[i] = z[i]; /* top k0 rows */
    for (   ; i<lnz; i++) p2[i] = t[i]; /* other non-0 rows */
  }
  permpro = imagecomplspec(extramat, &nr); /* lnz = lg(permpro) */

  if (nlze)
  { /* put the nlze 0 rows (trivial generators) at the top */
    p1 = new_chunk(lk0+1);
    for (i=1; i<=nlze; i++) p1[i] = perm[i + k0];
    for (   ; i<=lk0; i++)  p1[i] = perm[i - nlze];
    for (i=1; i<=lk0; i++)  perm[i] = p1[i];
  }
  /* sort other rows according to permpro (nr redundant generators first) */
  p1 = new_chunk(lnz); p2 = perm + nlze;
  for (i=1; i<lnz; i++) p1[i] = p2[permpro[i]];
  for (i=1; i<lnz; i++) p2[i] = p1[i];
  /* perm indexes the rows of mat
   *   |_0__|__redund__|__dense__|__too big__|_____done______|
   *   0  nlze                              lig             li
   *         \___nr___/ \___k0__/
   *         \____________lnz ______________/
   *
   *               col   co
   *       [dep     |     ]
   *    i0 [--------|  B  ] (i0 = nlze + nr)
   *       [matbnew |     ] matbnew has maximal rank = lnz-1 - nr
   * mat = [--------|-----] lig
   *       [   0    | Id  ]
   *       [        |     ] li */

  matbnew = cgetg(col+1,t_MAT); /* dense+toobig, maximal rank. For hnffinal */
  dep    = cgetg(col+1,t_MAT); /* rows dependent from the ones in matbnew */
  for (j=1; j<=col; j++)
  {
    GEN z = gel(extramat,j);
    p1 = cgetg(nlze+nr+1,t_COL); gel(dep,j) = p1;
    p2 = cgetg(lnz-nr,t_COL); gel(matbnew,j) = p2;
    for (i=1; i<=nlze; i++) gel(p1,i) = gen_0;
    p1 += nlze; for (i=1; i<=nr; i++) p1[i] = z[permpro[i]];
    p2 -= nr;   for (   ; i<lnz; i++) p2[i] = z[permpro[i]];
  }

  /* redundant generators in terms of the genuine generators
   * (x_i) = - (g_i) B */
  B = cgetg(co-col,t_MAT);
  for (j=col+1; j<co; j++)
  {
    GEN y = gel(matt,j);
    GEN z = gel(matb,j);
    p1=cgetg(lig+1,t_COL); gel(B,j-col) = p1;
    for (i=1; i<=nlze; i++) p1[i] = z[i];
    p1 += nlze; z += nlze-k0;
    for (k=1; k<lnz; k++)
    {
      i = permpro[k];
      p1[k] = (i <= k0)? y[i]: z[i];
    }
  }
  if (T) C = typ(C)==t_MAT? RgM_mul(C,T): RgV_RgM_mul(C,T);
  *ptdep = dep;
  *ptB = B;
  H = hnffinal(matbnew, perm, ptdep, ptB, &C);
  if (DEBUGLEVEL)
    msgtimer("hnfspec [%ld x %ld] --> [%ld x %ld]",li-1,co-1, lig-1,col-1);
  if (CO > co)
  { /* treat the rest, N cols at a time (hnflll slow otherwise) */
    const long N = 300;
    long a, L = CO - co, l = min(L, N); /* L columns to add */
    GEN CC = *ptC, m0 = mat0;
    setlg(CC, CO); /* restore */
    CC += co-1;
    m0 += co-1;
    for (a = l;;)
    {
      GEN MAT = cgetg(l + 1, t_MAT), emb = cgetg(l + 1, t_MAT);
      for (j = 1 ; j <= l; j++)
      {
	MAT[j] = m0[j];
	emb[j] = CC[j];
      }
      H = hnfadd_i(H, perm, ptdep, ptB, &C, MAT, emb);
      if (a == L) break;
      CC += l;
      m0 += l;
      a += l; if (a > L) { l = L - (a - l); a = L; }
      gerepileall(av, 4, &H,&C,ptB,ptdep);
    }
  }
  *ptC = C; return H;
}

GEN
hnfspec(GEN mat, GEN perm, GEN* ptdep, GEN* ptB, GEN* ptC, long k0)
{
  pari_sp av = avma;
  GEN H = hnfspec_i(mat, perm, ptdep, ptB, ptC, k0);
  gerepileall(av, 4, ptC, ptdep, ptB, &H); return H;
}

/* HNF reduce x, apply same transforms to C */
GEN
mathnfspec(GEN x, GEN *ptperm, GEN *ptdep, GEN *ptB, GEN *ptC)
{
  long i,j,k,ly,lx = lg(x);
  GEN p1,p2,z,perm;
  if (lx == 1) return gcopy(x);
  ly = lg(x[1]);
  z = cgetg(lx,t_MAT);
  perm = cgetg(ly,t_VECSMALL); *ptperm = perm;
  for (i=1; i<ly; i++) perm[i] = i;
  for (i=1; i<lx; i++)
  {
    p1 = cgetg(ly,t_COL); gel(z,i) = p1;
    p2 = gel(x,i);
    for (j=1; j<ly; j++)
    {
      if (is_bigint(p2[j])) goto TOOLARGE;
      p1[j] = itos(gel(p2,j));
    }
  }
  /*  [ dep |     ]
   *  [-----|  B  ]
   *  [  H  |     ]
   *  [-----|-----]
   *  [  0  | Id  ] */
  return hnfspec(z,perm, ptdep, ptB, ptC, 0);

TOOLARGE:
  if (lg(*ptC) > 1 && lg((*ptC)[1]) > 1)
    pari_err(impl,"mathnfspec with large entries");
  x = ZM_hnf(x); lx = lg(x); j = ly; k = 0;
  for (i=1; i<ly; i++)
  {
    if (gcmp1(gcoeff(x,i,i + lx-ly)))
      perm[--j] = i;
    else
      perm[++k] = i;
  }
  setlg(perm,k+1);
  x = rowpermute(x, perm); /* upper part */
  setlg(perm,ly);
  *ptB = vecslice(x, j+lx-ly, lx-1);
  setlg(x, j);
  *ptdep = rowslice(x, 1, lx-ly);
  return rowslice(x, lx-ly+1, k); /* H */
}

/* add new relations to a matrix treated by hnfspec (extramat / extraC) */
GEN
hnfadd_i(GEN H, GEN perm, GEN* ptdep, GEN* ptB, GEN* ptC, /* cf hnfspec */
       GEN extramat,GEN extraC)
{
  GEN matb, extratop, Cnew, permpro, B = *ptB, C = *ptC, dep = *ptdep;
  long i;
  long lH = lg(H)-1;
  long lB = lg(B)-1;
  long li = lg(perm)-1, lig = li - lB;
  long co = lg(C)-1,    col = co - lB;
  long nlze = lH? lg(dep[1])-1: lg(B[1])-1;

 /*               col    co
  *       [ 0 |dep |     ]
  *  nlze [--------|  B  ]
  *       [ 0 | H  |     ]
  *       [--------|-----] lig
  *       [   0    | Id  ]
  *       [        |     ] li */
  extratop = zm_to_ZM( rowslicepermute(extramat, perm, 1, lig) );
  if (li != lig)
  { /* zero out bottom part, using the Id block */
    GEN A = vecslice(C, col+1, co);
    GEN c = rowslicepermute(extramat, perm, lig+1, li);
    extraC   = gsub(extraC, typ(A)==t_MAT? RgM_zm_mul(A, c): RgV_zm_mul(A,c));
    extratop = ZM_sub(extratop, ZM_zm_mul(B, c));
  }

  extramat = shallowconcat(extratop, vconcat(dep, H));
  Cnew     = shallowconcat(extraC, vecslice(C, col-lH+1, co));
  if (DEBUGLEVEL>5) fprintferr("    1st phase done\n");
  permpro = imagecomplspec(extramat, &nlze);
  extramat = rowpermute(extramat, permpro);
  *ptB     = rowpermute(B,        permpro);
  permpro = vecpermute(perm, permpro);
  for (i=1; i<=lig; i++) perm[i] = permpro[i]; /* perm o= permpro */

  *ptdep  = rowslice(extramat, 1, nlze);
  matb    = rowslice(extramat, nlze+1, lig);
  if (DEBUGLEVEL>5) fprintferr("    2nd phase done\n");
  H = hnffinal(matb,perm,ptdep,ptB,&Cnew);
  *ptC = shallowconcat(vecslice(C, 1, col-lH), Cnew);
  if (DEBUGLEVEL)
  {
    msgtimer("hnfadd (%ld + %ld)", lg(extratop)-1, lg(dep)-1);
    if (DEBUGLEVEL>7) fprintferr("H = %Ps\nC = %Ps\n",H,*ptC);
  }
  return H;
}

GEN
hnfadd(GEN H, GEN perm, GEN* ptdep, GEN* ptB, GEN* ptC, /* cf hnfspec */
       GEN extramat,GEN extraC)
{
  pari_sp av = avma;
  H = hnfadd_i(H, perm, ptdep, ptB, ptC, ZM_to_zm(extramat), extraC);
  gerepileall(av, 4, ptC, ptdep, ptB, &H); return H;
}

/* zero aj = Aij (!= 0)  using  ak = Aik (maybe 0), via linear combination of
 * A[j] and A[k] of determinant 1. If U != NULL, likewise update its columns */
static void
ZC_elem(GEN aj, GEN ak, GEN A, GEN U, long j, long k)
{
  GEN p1,u,v,d;

  if (!signe(ak)) {
    swap(gel(A,j), gel(A,k));
    if (U) swap(gel(U,j), gel(U,k));
    return;
  }
  d = bezout(aj,ak,&u,&v);
  /* frequent special case (u,v) = (1,0) or (0,1) */
  if (!signe(u))
  { /* ak | aj */
    p1 = diviiexact(aj,ak); togglesign(p1);
    ZC_lincomb1_inplace(gel(A,j), gel(A,k), p1);
    if (U)
      ZC_lincomb1_inplace(gel(U,j), gel(U,k), p1);
    return;
  }
  if (!signe(v))
  { /* aj | ak */
    p1 = diviiexact(ak,aj); togglesign(p1);
    ZC_lincomb1_inplace(gel(A,k), gel(A,j), p1);
    swap(gel(A,j), gel(A,k));
    if (U) {
      ZC_lincomb1_inplace(gel(U,k), gel(U,j), p1);
      swap(gel(U,j), gel(U,k));
    }
    return;
  }

  if (!is_pm1(d)) { aj = diviiexact(aj, d); ak = diviiexact(ak, d); }
  p1 = gel(A,k); aj = negi(aj);
  gel(A,k) = ZC_lincomb(u,v, gel(A,j),p1);
  gel(A,j) = ZC_lincomb(aj,ak, p1,gel(A,j));
  if (U)
  {
    p1 = gel(U,k);
    gel(U,k) = ZC_lincomb(u,v, gel(U,j),p1);
    gel(U,j) = ZC_lincomb(aj,ak, p1,gel(U,j));
  }
}

/* reduce A[i,j] mod A[i,j0] for j=j0+1... via column operations */
static void
ZM_reduce(GEN A, GEN U, long i, long j0)
{
  long j, lA = lg(A);
  GEN d = gcoeff(A,i,j0);
  if (signe(d) < 0)
  {
    ZV_neg_inplace(gel(A,j0));
    if (U) ZV_togglesign(gel(U,j0));
    d = gcoeff(A,i,j0);
  }
  for (j=j0+1; j<lA; j++)
  {
    GEN q = truedivii(gcoeff(A,i,j), d);
    if (!signe(q)) continue;

    q = negi(q);
    ZC_lincomb1_inplace(gel(A,j), gel(A,j0), q);
    if (U) ZC_lincomb1_inplace(gel(U,j), gel(U,j0), q);
  }
}

/* A,B integral ideals in HNF. Return Au in Z^n (v in Z^n not computed), such
 * that Au + Bv = 1 */
GEN
hnfmerge_get_1(GEN A, GEN B)
{
  pari_sp av = avma;
  long j, k, c, l = lg(A), lb;
  GEN b, t, U = cgetg(l + 1, t_MAT), C = cgetg(l + 1, t_VEC);

  t = NULL; /* -Wall */
  b = gcoeff(B,1,1); lb = lgefint(b);
  if (!signe(b)) {
    if (gcmp1(gcoeff(A,1,1))) return scalarcol_shallow(gen_1, l-1);
    l = 0; /* trigger error */
  }
  for (j = 1; j < l; j++)
  {
    c = j+1;
    gel(U,j) = col_ei(l-1, j);
    gel(U,c) = zerocol(l-1); /* dummy */
    gel(C,j) = vecslice(gel(A,j), 1,j);
    gel(C,c) = vecslice(gel(B,j), 1,j);
    for (k = j; k > 0; k--)
    {
      t = gcoeff(C,k,c);
      if (gcmp0(t)) continue;
      setlg(C[c], k+1);
      ZC_elem(t, gcoeff(C,k,k), C, U, c, k);
      if (lgefint(gcoeff(C,k,k)) > lb) gel(C,k) = FpC_red(gel(C,k), b);
      if (j > 4)
      {
	GEN u = gel(U,k);
	long h;
	for (h=1; h<l; h++)
	  if (lgefint(u[h]) > lb) gel(u,h) = remii(gel(u,h), b);
      }
    }
    if (j == 1)
      t = gcoeff(C,1,1);
    else
    {
      GEN u,v;
      t = bezout(b, gcoeff(C,1,1), &u, &v); /* >= 0 */
      if (signe(v) && !gcmp1(v)) gel(U,1) = ZC_Z_mul(gel(U,1), v);
      gcoeff(C,1,1) = t;
    }
    if (signe(t) && is_pm1(t)) break;
  }
  if (j >= l) pari_err(talker, "non coprime ideals in hnfmerge");
  return gerepileupto(av, ZM_ZC_mul(A,gel(U,1)));

}

/* Inefficient compared to hnfall. 'remove' = throw away lin.dep columns */
static GEN
hnf_i(GEN A, int remove)
{
  pari_sp av0 = avma, av, lim;
  long s, m, n = lg(A)-1, i, j, k, li, def, ldef;
  GEN a;

  if (!n) return cgetg(1,t_MAT);
  av = avma; A = shallowcopy(A);
  m = lg(A[1])-1;

  lim = stack_lim(av,1);
  def = n; ldef = (m>n)? m-n: 0;
  for (li=m; li>ldef; li--)
  {
    for (j=def-1; j; j--)
    {
      a = gcoeff(A,li,j);
      if (!signe(a)) continue;

      /* zero a = Aij  using  b = Aik */
      k = (j==1)? def: j-1;
      ZC_elem(a,gcoeff(A,li,k), A,NULL, j,k);
      if (low_stack(lim, stack_lim(av,1)))
      {
	if (DEBUGMEM>1) pari_warn(warnmem,"ZM_hnf[1]. li=%ld",li);
	A = gerepilecopy(av, A);
      }
    }
    s = signe(gcoeff(A,li,def));
    if (s)
    {
      if (s < 0) ZV_neg_inplace(gel(A,def));
      ZM_reduce(A, NULL, li,def);
      def--;
    }
    else
      if (ldef) ldef--;
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"ZM_hnf[2]. li=%ld",li);
      A = gerepilecopy(av, A);
    }
  }
  if (remove)
  { /* remove 0 columns */
    for (i=1,j=1; j<=n; j++)
      if (!ZV_cmp0(gel(A,j))) A[i++] = A[j];
    setlg(A,i);
  }
  return gerepileupto(av0, ZM_copy(A));
}

GEN
ZM_hnf(GEN x) { return lg(x) > 8? ZM_hnfall(x, NULL, 1): hnf_i(x, 1); }

static GEN
ZC_Cei(long n, long i, GEN c) { GEN e = zerocol(n); gel(e,i) = c; return e; }

enum { hnf_MODID = 1, hnf_PART = 2 };

/* u*z[1..k] mod b, in place */
static void
FpV_Fp_mul_part_ip(GEN z, GEN u, GEN p, long k)
{
  long i;
  if (is_pm1(u)) {
    if (signe(u) > 0) {
      for (i = 1; i <= k; i++)
	if (signe(z[i])) gel(z,i) = modii(gel(z,i), p);
    } else {
      for (i = 1; i <= k; i++)
	if (signe(z[i])) gel(z,i) = modii(negi(gel(z,i)), p);
    }
  }
  else {
    for (i = 1; i <= k; i++)
      if (signe(z[i])) gel(z,i) = Fp_mul(u,gel(z,i), p);
  }
}
static void
FpV_red_part_ip(GEN z, GEN p, long k)
{
  long i;
  for (i = 1; i <= k; i++) gel(z,i) = modii(gel(z,i), p);
}
/* dm = multiple of diag element (usually detint(x))
 * flag & hnf_MODID: reduce mod dm * matid [ otherwise as above ].
 * flag & hnf_PART: don't reduce once diagonal is known; */

/* x a ZM, dm a t_INT */
static GEN
ZM_hnfmod_i(GEN x, GEN dm, int flag)
{
  pari_sp av0 = avma, av, lim;
  const int modid = (flag & hnf_MODID);
  long li, co, i, j, k, def, ldef, ldm;
  GEN a, b, p1, p2, u, v, dm2;

  co = lg(x); if (co == 1) return cgetg(1,t_MAT);
  li = lg(x[1]); dm2 = shifti(dm, -1);
  av = avma; lim = stack_lim(av,1);
  x = shallowcopy(x);

  ldef = 0;
  if (li > co)
  {
    ldef = li - co;
    if (!modid) pari_err(talker,"nb lines > nb columns in ZM_hnfmod");
  }
  /* To prevent coeffs explosion, only reduce mod dm when lg() > ldm */
  ldm = lgefint(dm);
  for (def = co-1,i = li-1; i > ldef; i--,def--)
  {
    gcoeff(x,i,def) = centermodii(gcoeff(x,i,def), dm,dm2);
    for (j = def-1; j; j--)
    {
      gcoeff(x,i,j) = centermodii(gcoeff(x,i,j), dm,dm2);
      a = gcoeff(x,i,j);
      if (!signe(a)) continue;

      k = (j==1)? def: j-1;
      gcoeff(x,i,k) = centermodii(gcoeff(x,i,k), dm,dm2);
      ZC_elem(a,gcoeff(x,i,k), x,NULL, j,k);
      p1 = gel(x,j);
      p2 = gel(x,k);
      for (k = 1; k < i; k++)
      {
	if (lgefint(p1[k]) > ldm) gel(p1,k) = centermodii(gel(p1,k), dm,dm2);
	if (lgefint(p2[k]) > ldm) gel(p2,k) = centermodii(gel(p2,k), dm,dm2);
      }
      if (low_stack(lim, stack_lim(av,1)))
      {
	if (DEBUGMEM>1) pari_warn(warnmem,"ZM_hnfmod[1]. i=%ld",i);
	x = gerepilecopy(av, x);
      }
    }
    if (modid && !signe(gcoeff(x,i,def)))
    { /* missing pivot on line i, insert column */
      GEN a = cgetg(co + 1, t_MAT);
      for (k = 1; k <= def; k++) a[k] = x[k];
      gel(a,k++) = ZC_Cei(li-1, i, dm);
      for (     ; k <= co;  k++) a[k] = x[k-1];
      ldef--; if (ldef < 0) ldef = 0;
      co++; def++; x = a;
    }
  }
  x += co - li;
  if (modid)
  { /* w[li] is an accumulator, discarded at the end */
    GEN w = cgetg(li+1, t_MAT);
    for (i = li-1; i > ldef; i--) w[i] = x[i];
    for (        ; i > 0;    i--) gel(w,i) = ZC_Cei(li-1, i, dm);
    x = w;
    for (i = li-1; i > 0; i--)
    { /* check that dm*Id \subset L + add up missing dm*Id components */
      GEN d, c;
      d = bezout(gcoeff(x,i,i),dm, &u,&v);
      gcoeff(x,i,i) = d;
      if (is_pm1(d))
      {
	FpV_Fp_mul_part_ip(gel(x,i), u, dm, i-1);
	continue;
      }
      c = cgetg(li, t_COL);
      for (j = 1; j < i; j++) gel(c,j) = remii(gcoeff(x,j,i),d);
      for (     ; j <li; j++) gel(c,j) = gen_0;
      if (!equalii(dm, d)) c = ZC_Z_mul(c, diviiexact(dm, d));
      gel(x,li) = c;
      FpV_Fp_mul_part_ip(gel(x,i), u, dm, i-1);
      for (j = i - 1; j > ldef; j--)
      {
	GEN a = gcoeff(x, j, li);
	if (!signe(a)) continue;
	ZC_elem(a, gcoeff(x,j,j), x, NULL, li,j);
	FpV_red_part_ip(gel(x,li), dm, j-1);
	FpV_red_part_ip(gel(x,j),  dm, j-1);
	if (low_stack(lim, stack_lim(av,1)))
	{
	  if (DEBUGMEM>1) pari_warn(warnmem,"ZM_hnfmod[2]. i=%ld", i);
	  x = gerepilecopy(av, x);
	}
      }
    }
  }
  else
  {
    b = dm;
    for (i = li-1; i > 0; i--)
    {
      GEN d = bezout(gcoeff(x,i,i),b, &u,&v);
      gcoeff(x,i,i) = d;
      FpV_Fp_mul_part_ip(gel(x,i), u, b, i-1);
      if (i > 1) b = diviiexact(b,d);
    }
  }
  x[0] = evaltyp(t_MAT) | evallg(li); /* kill 0 columns / discard accumulator */
  if (flag & hnf_PART) return x;

  if (modid) b = const_vec(li-1, dm);
  else
  { /* compute optimal value for dm */
    b = cgetg(li, t_VEC); gel(b,1) = gcoeff(x,1,1);
    for (i = 2; i < li; i++) gel(b,i) = mulii(gel(b,i-1), gcoeff(x,i,i));
  }
  dm = b;

  for (i = li-2; i > 0; i--)
  {
    GEN diag = gcoeff(x,i,i);
    ldm = lgefint(dm[i]);
    for (j = i+1; j < li; j++)
    {
      b = negi(truedivii(gcoeff(x,i,j), diag));
      ZC_lincomb1_inplace(gel(x,j), gel(x,i),b);
      p1 = gel(x,j);
      for (k=1; k<i; k++)
	if (lgefint(p1[k]) > ldm) gel(p1,k) = remii(gel(p1,k), gel(dm,i));
      if (low_stack(lim, stack_lim(av,1)))
      {
	if (DEBUGMEM>1) pari_warn(warnmem,"ZM_hnfmod[3]. i=%ld", i);
	gerepileall(av, 2, &x, &dm); diag = gcoeff(x,i,i);
      }
    }
  }
  return gerepilecopy(av0, x);
}
GEN
ZM_hnfmod(GEN x, GEN d) { return ZM_hnfmod_i(x,d,0); }
GEN
ZM_hnfmodid(GEN x, GEN d) { return ZM_hnfmod_i(x,d,hnf_MODID); }
GEN
ZM_hnfmodidpart(GEN x, GEN d) { return ZM_hnfmod_i(x, d, hnf_MODID|hnf_PART); }

static GEN
allhnfmod(GEN x, GEN dm, int flag)
{
  if (typ(dm)!=t_INT) pari_err(typeer,"allhnfmod");
  if (typ(x)!=t_MAT) pari_err(typeer,"allhnfmod");
  RgM_check_ZM(x, "allhnfmod");
  return signe(dm)? ZM_hnfmod_i(x, dm, flag): ZM_hnf(x);
}
GEN
hnfmod(GEN x, GEN d) { return allhnfmod(x, d, 0); }
GEN
hnfmodid(GEN x, GEN d) { return allhnfmod(x, d, hnf_MODID); }

/* M a ZM in HNF. Normalize with *centered* residues */
GEN
ZM_hnfcenter(GEN M)
{
  long i, j, k, N = lg(M)-1;
  pari_sp av = avma, lim = stack_lim(av,1);

  for (j=N-1; j>0; j--) /* skip last line */
  {
    GEN Mj = gel(M,j), a = gel(Mj,j);
    for (k = j+1; k <= N; k++)
    {
      GEN Mk = gel(M,k), q = diviiround(gel(Mk,j), a);
      long s = signe(q);
      if (!s) continue;
      if (is_pm1(q))
      {
        if (s < 0)
          for (i = 1; i <= j; i++) gel(Mk,i) = addii(gel(Mk,i), gel(Mj,i));
        else
          for (i = 1; i <= j; i++) gel(Mk,i) = subii(gel(Mk,i), gel(Mj,i));
      }
      else
        for (i = 1; i <= j; i++) gel(Mk,i) = subii(gel(Mk,i), mulii(q,gel(Mj,i)));
      if (low_stack(lim, stack_lim(av,1)))
      {
        if (DEBUGMEM) pari_warn(warnmem,"ZM_hnfcenter, j = %ld",j);
        M = gerepilecopy(av, M);
      }
    }
  }
  return M;
}

/***********************************************************************/
/*                                                                     */
/*                 HNFLLL (Havas, Majewski, Mathews)                   */
/*                                                                     */
/***********************************************************************/

static void
Minus(long j, GEN lambda)
{
  long k, n = lg(lambda);

  for (k=1  ; k<j; k++) togglesign_safe(&gcoeff(lambda,k,j));
  for (k=j+1; k<n; k++) togglesign_safe(&gcoeff(lambda,j,k));
}

/* index of first non-zero entry */
static long
findi(GEN M)
{
  long i, n = lg(M);
  for (i=1; i<n; i++)
    if (signe(M[i])) return i;
  return 0;
}

static long
findi_normalize(GEN Aj, GEN B, long j, GEN lambda)
{
  long r = findi(Aj);
  if (r && signe(Aj[r]) < 0)
  {
    ZV_togglesign(Aj); if (B) ZV_togglesign(gel(B,j));
    Minus(j,lambda);
  }
  return r;
}

static void
reduce2(GEN A, GEN B, long k, long j, long *row0, long *row1, GEN lambda, GEN D)
{
  GEN q;
  long i;

  *row0 = findi_normalize(gel(A,j), B,j,lambda);
  *row1 = findi_normalize(gel(A,k), B,k,lambda);
  if (*row0)
    q = truedivii(gcoeff(A,*row0,k), gcoeff(A,*row0,j));
  else if (absi_cmp(shifti(gcoeff(lambda,j,k), 1), gel(D,j)) > 0)
    q = diviiround(gcoeff(lambda,j,k), gel(D,j));
  else
    return;

  if (signe(q))
  {
    GEN Lk = gel(lambda,k), Lj = gel(lambda,j);
    togglesign_safe(&q);
    if (*row0) ZC_lincomb1_inplace(gel(A,k),gel(A,j),q);
    if (B) ZC_lincomb1_inplace(gel(B,k),gel(B,j),q);
    gel(Lk,j) = addii(gel(Lk,j), mulii(q,gel(D,j)));
    if (is_pm1(q))
    {
      if (signe(q) > 0)
      {
	for (i=1; i<j; i++)
	  if (signe(Lj[i])) gel(Lk,i) = addii(gel(Lk,i), gel(Lj,i));
      }
      else
      {
	for (i=1; i<j; i++)
	  if (signe(Lj[i])) gel(Lk,i) = subii(gel(Lk,i), gel(Lj,i));
      }
    }
    else
    {
      for (i=1; i<j; i++)
	if (signe(Lj[i])) gel(Lk,i) = addii(gel(Lk,i), mulii(q,gel(Lj,i)));
    }
  }
}

static void
hnfswap(GEN A, GEN B, long k, GEN lambda, GEN D)
{
  GEN t, p1, p2, Lk = gel(lambda,k);
  long i,j,n = lg(A);

  swap(gel(A,k), gel(A,k-1));
  if (B) swap(gel(B,k), gel(B,k-1));
  for (j=k-2; j; j--) swap(gcoeff(lambda,j,k-1), gel(Lk,j));
  for (i=k+1; i<n; i++)
  {
    GEN Li = gel(lambda,i);
    p1 = mulii(gel(Li,k-1), gel(D,k));
    p2 = mulii(gel(Li,k), gel(Lk,k-1));
    t = subii(p1,p2);

    p1 = mulii(gel(Li,k), gel(D,k-2));
    p2 = mulii(gel(Li,k-1), gel(Lk,k-1));
    gel(Li,k-1) = diviiexact(addii(p1,p2), gel(D,k-1));
    gel(Li,k) = diviiexact(t, gel(D,k-1));
  }
  p1 = mulii(gel(D,k-2), gel(D,k));
  p2 = sqri(gel(Lk,k-1));
  gel(D,k-1) = diviiexact(addii(p1,p2), gel(D,k-1));
}

/* reverse row order in matrix A */
static GEN
fix_rows(GEN A)
{
  long i,j, h,n = lg(A);
  GEN cB,cA,B = cgetg(n,t_MAT);
  if (n == 1) return B;
  h = lg(A[1]);
  for (j=1; j<n; j++)
  {
    cB = cgetg(h, t_COL);
    cA = gel(A,j); gel(B,j) = cB;
    for (i=h>>1; i; i--) { cB[h-i] = cA[i]; cB[i] = cA[h-i]; }
  }
  return B;
}

/* remove the first r columns */
static void
remove_0cols(long r, GEN *pA, GEN *pB, long remove)
{
  GEN A = *pA, B = *pB;
  long l = lg(A);
  A += r; A[0] = evaltyp(t_MAT) | evallg(l-r);
  if (B && remove == 2) { B += r; B[0] = A[0]; }
  *pA = A; *pB = B;
}

GEN
ZM_hnflll(GEN A, GEN *ptB, int remove)
{
  pari_sp av = avma, lim = stack_lim(av,3);
  long m1 = 1, n1 = 1; /* alpha = m1/n1. Maybe 3/4 here ? */
  long do_swap, i, n, k, kmax;
  GEN z, B, lambda, D;

  n = lg(A);
  A = ZM_copy(fix_rows(A)); /* ZM_copy for in place findi_normalize() */
  B = ptB? matid(n-1): NULL;
  D = const_vec(n, gen_1) + 1;
  lambda = zeromatcopy(n-1,n-1);
  k = kmax = 2;
  while (k < n)
  {
    long row0, row1;
    reduce2(A,B,k,k-1,&row0,&row1,lambda,D);
    if (row0)
      do_swap = (!row1 || row0 <= row1);
    else if (!row1)
    { /* row0 == row1 == 0 */
      pari_sp av1 = avma;
      z = addii(mulii(gel(D,k-2),gel(D,k)), sqri(gcoeff(lambda,k-1,k)));
      do_swap = (cmpii(mului(n1,z), mului(m1,sqri(gel(D,k-1)))) < 0);
      avma = av1;
    }
    else
      do_swap = 0;
    if (do_swap)
    {
      hnfswap(A,B,k,lambda,D);
      if (k > 2) k--;
    }
    else
    {
      for (i=k-2; i; i--)
      {
	long row0, row1;
	reduce2(A,B,k,i,&row0,&row1,lambda,D);
	if (low_stack(lim, stack_lim(av,3)))
	{
	  GEN b = D-1;
	  if (DEBUGMEM) pari_warn(warnmem,"hnflll (reducing), kmax = %ld",kmax);
	  gerepileall(av, B? 4: 3, &A, &lambda, &b, &B);
	  D = b+1;
	}
      }
      if (++k > kmax) kmax = k;
    }
    if (low_stack(lim, stack_lim(av,3)))
    {
      GEN b = D-1;
      if (DEBUGMEM) pari_warn(warnmem,"hnflll, kmax = %ld / %ld",kmax,n-1);
      gerepileall(av, B? 4: 3, &A, &lambda, &b, &B);
      D = b+1;
    }
  }
  /* handle trivial case: return negative diag coefficient otherwise */
  if (n == 2) (void)findi_normalize(gel(A,1), B,1,lambda);
  A = fix_rows(A);
  if (remove)
  {
    for (i = 1; i < n; i++)
      if (!ZV_cmp0(gel(A,i))) break;
    remove_0cols(i-1, &A, &B, remove);
  }
  gerepileall(av, B? 2: 1, &A, &B);
  if (B) *ptB = B;
  return A;
}

GEN
hnflll(GEN x)
{
  GEN z = cgetg(3, t_VEC);
  gel(z,1) = ZM_hnflll(x, &gel(z,2), 0);
  return z;
}

/* Variation on HNFLLL: Extended GCD */

static void
reduce1(GEN A, GEN B, long k, long j, GEN lambda, GEN D)
{
  GEN q;
  long i;

  if (signe(A[j]))
    q = diviiround(gel(A,k),gel(A,j));
  else if (absi_cmp(shifti(gcoeff(lambda,j,k), 1), gel(D,j)) > 0)
    q = diviiround(gcoeff(lambda,j,k), gel(D,j));
  else
    return;

  if (signe(q))
  {
    GEN Lk = gel(lambda,k), Lj = gel(lambda,j);
    togglesign_safe(&q);
    gel(A,k) = addii(gel(A,k), mulii(q,gel(A,j)));
    ZC_lincomb1_inplace(gel(B,k),gel(B,j),q);
    gel(Lk,j) = addii(gel(Lk,j), mulii(q,gel(D,j)));
    for (i=1; i<j; i++)
      if (signe(Lj[i])) gel(Lk,i) = addii(gel(Lk,i), mulii(q,gel(Lj,i)));
  }
}

GEN
extendedgcd(GEN A)
{
  long m1 = 1, n1 = 1; /* alpha = m1/n1. Maybe 3/4 here ? */
  pari_sp av = avma;
  long do_swap,i,n,k;
  GEN z, B, lambda, D;

  n = lg(A);
  for (i=1; i<n; i++)
    if (typ(A[i]) != t_INT) pari_err(typeer,"extendedgcd");
  A = shallowcopy(A);
  B = matid(n-1);
  lambda = zeromatcopy(n-1,n-1);
  D = const_vec(n, gen_1);
  k = 2;
  while (k < n)
  {
    reduce1(A,B,k,k-1,lambda,D);
    if (signe(A[k-1])) do_swap = 1;
    else if (!signe(A[k]))
    {
      pari_sp av1 = avma;
      z = addii(mulii(gel(D,k-2),gel(D,k)), sqri(gcoeff(lambda,k-1,k)));
      do_swap = (cmpii(mului(n1,z), mului(m1,sqri(gel(D,k-1)))) < 0);
      avma = av1;
    }
    else do_swap = 0;

    if (do_swap)
    {
      hnfswap(A,B,k,lambda,D);
      if (k > 2) k--;
    }
    else
    {
      for (i=k-2; i; i--) reduce1(A,B,k,i,lambda,D);
      k++;
    }
  }
  if (signe(A[n-1]) < 0)
  {
    togglesign_safe(&gel(A,n-1));
    ZV_togglesign(gel(B,n-1));
  }
  return gerepilecopy(av, mkvec2(gel(A,n-1), B));
}

/* HNF with permutation. */
GEN
ZM_hnfperm(GEN A, GEN *ptU, GEN *ptperm)
{
  GEN U, c, l, perm, d, p, q, b;
  pari_sp av = avma, av1, lim;
  long r, t, i, j, j1, k, m, n;

  n = lg(A)-1;
  if (!n)
  {
    if (ptU) *ptU = cgetg(1,t_MAT);
    if (ptperm) *ptperm = cgetg(1,t_VEC);
    return cgetg(1, t_MAT);
  }
  m = lg(A[1])-1;
  c = const_vecsmall(m, 0);
  l = const_vecsmall(n, 0);
  perm = cgetg(m+1, t_VECSMALL);
  av1 = avma; lim = stack_lim(av1,1);
  A = shallowcopy(A);
  U = ptU? matid(n): NULL;
  /* U base change matrix : A0*U = A all along */
  for (r=0, k=1; k <= n; k++)
  {
    for (j=1; j<k; j++)
    {
      if (!l[j]) continue;
      t=l[j]; b=gcoeff(A,t,k);
      if (!signe(b)) continue;

      ZC_elem(b,gcoeff(A,t,j), A,U,k,j);
      d = gcoeff(A,t,j);
      if (signe(d) < 0)
      {
	ZV_neg_inplace(gel(A,j));
	if (U) ZV_togglesign(gel(U,j));
	d = gcoeff(A,t,j);
      }
      for (j1=1; j1<j; j1++)
      {
	if (!l[j1]) continue;
	q = truedivii(gcoeff(A,t,j1),d);
	if (!signe(q)) continue;

	q = negi(q);
	ZC_lincomb1_inplace(gel(A,j1), gel(A,j), q);
	if (U) ZC_lincomb1_inplace(gel(U,j1), gel(U,j), q);
      }
    }
    t = m; while (t && (c[t] || !signe(gcoeff(A,t,k)))) t--;
    if (t)
    {
      p = gcoeff(A,t,k);
      for (i=t-1; i; i--)
      {
	q = gcoeff(A,i,k);
	if (signe(q) && absi_cmp(p,q) > 0) { p = q; t = i; }
      }
      perm[++r] = l[k] = t; c[t] = k;
      if (signe(p) < 0)
      {
	ZV_neg_inplace(gel(A,k));
	if (U) ZV_togglesign(gel(U,k));
	p = gcoeff(A,t,k);
      }
      /* p > 0 */
      for (j=1; j<k; j++)
      {
	if (!l[j]) continue;
	q = truedivii(gcoeff(A,t,j),p);
	if (!signe(q)) continue;

	q = negi(q);
	ZC_lincomb1_inplace(gel(A,j), gel(A,k), q);
	if (U) ZC_lincomb1_inplace(gel(U,j), gel(U,k), q);
      }
    }
    if (low_stack(lim, stack_lim(av1,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"hnfperm");
      gerepileall(av1, U? 2: 1, &A, &U);
    }
  }
  if (r < m)
  {
    for (i=1,k=r; i<=m; i++)
      if (!c[i]) perm[++k] = i;
  }

/* We have A0*U=A, U in Gl(n,Z)
 * basis for Im(A):  columns of A s.t l[j]>0 (r   cols)
 * basis for Ker(A): columns of U s.t l[j]=0 (n-r cols) */
  p = cgetg(r+1,t_MAT);
  for (i=1; i<=m/2; i++) lswap(perm[i], perm[m+1-i]);
  if (U)
  {
    GEN u = cgetg(n+1,t_MAT);
    for (t=1,k=r,j=1; j<=n; j++)
      if (l[j])
      {
	u[k + n-r] = U[j];
	gel(p,k--) = vecpermute(gel(A,j), perm);
      }
      else
	u[t++] = U[j];
    *ptU = u;
    if (ptperm) *ptperm = perm;
    gerepileall(av, ptperm? 3: 2, &p, ptU, ptperm);
  }
  else
  {
    for (k=r,j=1; j<=n; j++)
      if (l[j]) gel(p,k--) = vecpermute(gel(A,j), perm);
    if (ptperm) *ptperm = perm;
    gerepileall(av, ptperm? 2: 1, &p, ptperm);
  }
  return p;
}

GEN
hnfperm(GEN A)
{
  GEN y = cgetg(4, t_VEC);
  gel(y,1) = ZM_hnfperm(A, &gel(y,2), &gel(y,3));
  return y;
}

/* Hermite Normal Form, with base change matrix if ptB != NULL.
 * If 'remove' = 1, remove 0 columns (do NOT update *ptB accordingly)
 * If 'remove' = 2, remove 0 columns and update *ptB accordingly */
GEN
ZM_hnfall(GEN A, GEN *ptB, long remove)
{
  pari_sp av = avma, av1, lim;
  long m, n, r, i, j, k, li;
  GEN B, c, h, a;

  n = lg(A)-1;
  if (!n)
  {
    if (ptB) *ptB = cgetg(1,t_MAT);
    return cgetg(1,t_MAT);
  }
  m = lg(A[1])-1;
  c = const_vecsmall(m, 0);
  h = const_vecsmall(n, m);
  av1 = avma; lim = stack_lim(av1,1);
  A = shallowcopy(A);
  B = ptB? matid(n): NULL;
  r = n+1;
  for (li=m; li; li--)
  {
    for (j=1; j<r; j++)
    {
      for (i=h[j]; i>li; i--)
      {
	a = gcoeff(A,i,j);
	if (!signe(a)) continue;

	k = c[i]; /* zero a = Aij  using  Aik */
	ZC_elem(a,gcoeff(A,i,k), A,B,j,k);
	ZM_reduce(A,B, i,k);
	if (low_stack(lim, stack_lim(av1,1)))
	{
	  if (DEBUGMEM>1) pari_warn(warnmem,"hnfall[1], li = %ld", li);
	  gerepileall(av1, B? 2: 1, &A, &B);
	}
      }
      if (signe( gcoeff(A,li,j) )) break;
      h[j] = li-1;
    }
    if (j == r) continue;
    r--;
    if (j < r) /* A[j] != 0 */
    {
      swap(gel(A,j), gel(A,r));
      if (B) swap(gel(B,j), gel(B,r));
      h[j] = h[r]; h[r] = li; c[li] = r;
    }
    if (signe(gcoeff(A,li,r)) < 0)
    {
      ZV_neg_inplace(gel(A,r));
      if (B) ZV_togglesign(gel(B,r));
    }
    ZM_reduce(A,B, li,r);
    if (low_stack(lim, stack_lim(av1,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"hnfall[2], li = %ld", li);
      gerepileall(av1, B? 2: 1, &A, &B);
    }
  }

  if (DEBUGLEVEL>5) fprintferr("\nhnfall, final phase: ");
  r--; /* first r cols are in the image the n-r (independent) last ones */
  for (j=1; j<=r; j++)
    for (i=h[j]; i; i--)
    {
      a = gcoeff(A,i,j);
      k = c[i];
      if (signe(a)) ZC_elem(a,gcoeff(A,i,k), A,B, j,k);
      ZM_reduce(A,B, i,k); /* ensure non-negative entries, even if a = 0 */
      if (low_stack(lim, stack_lim(av1,1)))
      {
	if (DEBUGMEM>1) pari_warn(warnmem,"hnfall[3], j = %ld", j);
	gerepileall(av1, B? 2: 1, &A, &B);
      }
    }
  if (DEBUGLEVEL>5) fprintferr("\n");
  if (remove) remove_0cols(r, &A, &B, remove);
  gerepileall(av, B? 2: 1, &A, &B);
  if (B) *ptB = B;
  return A;
}

GEN
hnfall(GEN x)
{
  GEN z = cgetg(3, t_VEC);
  gel(z,1) = ZM_hnfall(x, (GEN*)(z+2), 1);
  return z;
}
GEN
hnf(GEN x) { return mathnf0(x,0); }

/***************************************************************/
/**							      **/
/**      	    SMITH NORMAL FORM REDUCTION	              **/
/**							      **/
/***************************************************************/

static GEN
col_mul(GEN x, GEN c)
{
  if (typ(x) == t_INT)
  {
    long s = signe(x);
    if (!s) return NULL;
    if (is_pm1(x)) return (s > 0)? c: RgC_neg(c);
  }
  return RgC_Rg_mul(c, x);
}

static void
do_zero(GEN x)
{
  long i, lx = lg(x);
  for (i=1; i<lx; i++) gel(x,i) = gen_0;
}

/* c1 <-- u.c1 + v.c2; c2 <-- a.c2 - b.c1 */
static void
update(GEN u, GEN v, GEN a, GEN b, GEN *c1, GEN *c2)
{
  GEN p1,p2;

  u = col_mul(u,*c1);
  v = col_mul(v,*c2);
  if (u) p1 = v? gadd(u,v): u;
  else   p1 = v? v: NULL;

  a = col_mul(a,*c2);
  b = col_mul(gneg_i(b),*c1);
  if (a) p2 = b? RgC_add(a,b): a;
  else   p2 = b? b: NULL;

  if (!p1) do_zero(*c1); else *c1 = p1;
  if (!p2) do_zero(*c2); else *c2 = p2;
}

static GEN
trivsmith(long all)
{
  GEN z;
  if (!all) return cgetg(1,t_VEC);
  z=cgetg(4,t_VEC);
  gel(z,1) = cgetg(1,t_MAT);
  gel(z,2) = cgetg(1,t_MAT);
  gel(z,3) = cgetg(1,t_MAT); return z;
}

static void
snf_pile(pari_sp av, GEN *x, GEN *U, GEN *V)
{
  GEN *gptr[3];
  int c = 1; gptr[0]=x;
  if (*U) gptr[c++] = U;
  if (*V) gptr[c++] = V;
  gerepilemany(av,gptr,c);
}

static GEN
bezout_step(GEN *pa, GEN *pb, GEN *pu, GEN *pv)
{
  GEN a = *pa, b = *pb, d;
  if (absi_equal(a,b))
  {
    long sa = signe(a), sb = signe(b);
    *pv = gen_0;
    if (sb == sa) {
      *pa = *pb = gen_1;
      if (sa > 0) {*pu=gen_1; return a;} else {*pu=gen_m1; return absi(a);}
    }
    if (sa > 0) { *pa = *pu = gen_1; *pb = gen_m1; return a; }
    *pa = *pu = gen_m1; *pb = gen_1; return b;
  }
  d = bezout(a,b, pu,pv);
  *pa = diviiexact(a, d);
  *pb = diviiexact(b, d); return d;
}

static int
negcmpii(void *E, GEN x, GEN y) { (void)E; return -cmpii(x,y); }

/* Return the SNF D of matrix X. If ptU/ptV non-NULL set them to U/V
 * to that D = UXV */
GEN
ZM_snfall_i(GEN x, GEN *ptU, GEN *ptV, int return_vec)
{
  pari_sp av0 = avma, av, lim = stack_lim(av0,1);
  long i, j, k, m0, m, n0, n;
  GEN p1, u, v, U, V, V0, mdet, ys, perm = NULL;

  n0 = n = lg(x)-1;
  if (!n) {
    if (ptU) *ptU = cgetg(1,t_MAT);
    if (ptV) *ptV = cgetg(1,t_MAT);
    return cgetg(1, return_vec? t_VEC: t_MAT);
  }
  av = avma;
  m0 = m = lg(x[1])-1;

  U = ptU? gen_1: NULL; /* TRANSPOSE of row transform matrix [act on columns]*/
  V = ptV? gen_1: NULL;
  V0 = NULL;
  x = shallowcopy(x);
  if (m == n && ZM_ishnf(x))
  {
    mdet = ZM_det_triangular(x);
    if (V) *ptV = matid(n);
  }
  else
  {
    mdet = ZM_detmult(x);
    if (signe(mdet))
    {
      if (!V)
	p1 = ZM_hnfmod(x,mdet);
      else
      {
	if (m == n)
	{
	  p1 = ZM_hnfmod(x,mdet);
	  *ptV = RgM_solve(x,p1);
	}
	else
	  p1 = ZM_hnfperm(x, ptV, ptU? &perm: NULL);
      }
      mdet = ZM_det_triangular(p1);
    }
    else
      p1 = ZM_hnfperm(x, ptV, ptU? &perm: NULL);
    x = p1;
  }
  n = lg(x)-1;
  if (V)
  {
    V = *ptV;
    if (n != n0)
    {
      V0 = vecslice(V, 1, n0 - n); /* kernel */
      V  = vecslice(V, n0-n+1, n0);
      av = avma;
    }
  }
  /* independent columns */
  if (!signe(mdet))
  {
    if (n)
    {
      x = ZM_snfall_i(shallowtrans(x), ptV, ptU, return_vec); /* swap ptV,ptU */
      if (typ(x) == t_MAT && n != m) x = shallowtrans(x);
      if (V) V = ZM_mul(V, shallowtrans(*ptV));
      if (U) U = *ptU; /* TRANSPOSE */
    }
    else /* 0 matrix */
    {
      x = cgetg(1,t_MAT);
      if (V) V = cgetg(1, t_MAT);
      if (U) U = matid(m);
    }
    goto THEEND;
  }
  if (U) U = matid(n);

  /* square, maximal rank n */
  p1 = gen_indexsort(RgM_diagonal_shallow(x), NULL, &negcmpii);
  ys = cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++) gel(ys,j) = vecpermute(gel(x, p1[j]), p1);
  x = ys;
  if (U) U = vecpermute(U, p1);
  if (V) V = vecpermute(V, p1);

  p1 = ZM_hnfmod(x, mdet);
  if (V) V = ZM_mul(V, RgM_solve(x,p1));
  x = p1;

  if (DEBUGLEVEL>7) fprintferr("starting SNF loop");
  for (i=n; i>1; i--)
  {
    if (DEBUGLEVEL>7) fprintferr("\ni = %ld: ",i);
    for(;;)
    {
      int c = 0;
      GEN a, b;
      for (j=i-1; j>=1; j--)
      {
	b = gcoeff(x,i,j); if (!signe(b)) continue;
	a = gcoeff(x,i,i);
	ZC_elem(b, a, x,V, j,i);
	if (low_stack(lim, stack_lim(av,1)))
	{
	  if (DEBUGMEM>1) pari_warn(warnmem,"[1]: ZM_snfall i = %ld", i);
	  snf_pile(av, &x,&U,&V);
	}
      }
      if (DEBUGLEVEL>7) fprintferr("; ");
      for (j=i-1; j>=1; j--)
      {
	GEN d;
	b = gcoeff(x,j,i); if (!signe(b)) continue;
	a = gcoeff(x,i,i);
	d = bezout_step(&a, &b, &u, &v);
	for (k = 1; k < i; k++)
	{
	  GEN t = addii(mulii(u,gcoeff(x,i,k)),mulii(v,gcoeff(x,j,k)));
	  gcoeff(x,j,k) = subii(mulii(a,gcoeff(x,j,k)),
				mulii(b,gcoeff(x,i,k)));
	  gcoeff(x,i,k) = t;
	}
	gcoeff(x,j,i) = gen_0;
	gcoeff(x,i,i) = d;
	if (U) update(u,v,a,b,(GEN*)(U+i),(GEN*)(U+j));
	if (low_stack(lim, stack_lim(av,1)))
	{
	  if (DEBUGMEM>1) pari_warn(warnmem,"[2]: ZM_snfall, i = %ld", i);
	  snf_pile(av, &x,&U,&V);
	}
	c = 1;
      }
      if (!c)
      {
	b = gcoeff(x,i,i); if (!signe(b) || is_pm1(b)) break;

	for (k=1; k<i; k++)
	{
	  for (j=1; j<i; j++)
	    if (signe(remii(gcoeff(x,k,j),b))) break;
	  if (j != i) break;
	}
	if (k == i) break;

	/* x[k,j] != 0 mod b */
	for (j=1; j<=i; j++)
	  gcoeff(x,i,j) = addii(gcoeff(x,i,j),gcoeff(x,k,j));
	if (U) gel(U,i) = gadd(gel(U,i),gel(U,k));
      }
      if (low_stack(lim, stack_lim(av,1)))
      {
	if (DEBUGMEM>1) pari_warn(warnmem,"[3]: ZM_snfall");
	snf_pile(av, &x,&U,&V);
      }
    }
  }
  if (DEBUGLEVEL>7) fprintferr("\n");
  for (k=1; k<=n; k++)
    if (signe(gcoeff(x,k,k)) < 0)
    {
      if (V) ZV_togglesign(gel(V,k));
      gcoeff(x,k,k) = negi(gcoeff(x,k,k));
    }
THEEND:
  if (return_vec)
  {
    long l = lg(x)-1;
    if (typ(x) == t_MAT) x = RgM_diagonal_shallow(x);
    if (m0 > l) x = shallowconcat(zerovec(m0-l), x);
  }

  if (V0)
  {
    if (!return_vec) x = shallowconcat(zeromat(m,n0-n), x);
    if (V) V = shallowconcat(V0, V);
  }
  if (U)
  {
    U = shallowtrans(U);
    if (perm) U = vecpermute(U, perm_inv(perm));
  }
  snf_pile(av0, &x,&U,&V);
  if (ptU) *ptU = U;
  if (ptV) *ptV = V;
  return x;
}
GEN
ZM_snfall(GEN x, GEN *U, GEN *V) { return ZM_snfall_i(x, U, V, 0); }
GEN
ZM_snf(GEN x) { return ZM_snfall_i(x, NULL,NULL, 1); }

GEN
smith(GEN x) {
  if (typ(x)!=t_MAT) pari_err(typeer,"smith");
  RgM_check_ZM(x, "smith");
  return ZM_snfall_i(x, NULL,NULL, 1);
}
GEN
smithall(GEN x)
{
  GEN z = cgetg(4, t_VEC);
  if (typ(x)!=t_MAT) pari_err(typeer,"smithall");
  RgM_check_ZM(x, "smithall");
  gel(z,3) = ZM_snfall_i(x, (GEN*)(z+1),(GEN*)(z+2), 0);
  return z;
}

void
ZM_snfclean(GEN d, GEN u, GEN v)
{
  long i, c, l = lg(d);

  if (typ(d) == t_VEC)
    for (c=1; c<l; c++) { GEN t = gel(d,c); if (is_pm1(t)) break; }
  else
  {
    for (c=1; c<l; c++) { GEN t = gcoeff(d,c,c); if (is_pm1(t)) break; }
    if (c < l) for (i = 1; i < c; i++) setlg(gel(d,i), c);
  }
  setlg(d, c);
  if (u) for (i=1; i<l; i++) setlg(gel(u,i), c);
  if (v) setlg(v, c);
}

/* Assume z was computed by [g]smithall(). Remove the 1s on the diagonal */
GEN
smithclean(GEN z)
{
  long i,j,l,c;
  GEN u,v,y,d,p1;

  if (typ(z) != t_VEC) pari_err(typeer,"smithclean");
  l = lg(z); if (l == 1) return cgetg(1,t_VEC);
  u=gel(z,1);
  if (l != 4 || typ(u) != t_MAT)
  {
    for (c=1; c<l; c++)
      if (gcmp1(gel(z,c))) break;
    return gcopy_i(z, c);
  }
  v=gel(z,2); d=gel(z,3); l = lg(d);
  for (c=1; c<l; c++)
    if (gcmp1(gcoeff(d,c,c))) break;

  y=cgetg(4,t_VEC);
  gel(y,1) = p1 = cgetg(l,t_MAT);
  for (i=1; i<l; i++) gel(p1,i) = gcopy_i(gel(u,i), c);
  gel(y,2) = gcopy_i(v, c);
  gel(y,3) = p1 = cgetg(c,t_MAT);
  for (i=1; i<c; i++)
  {
    GEN p2 = cgetg(c,t_COL); gel(p1,i) = p2;
    for (j=1; j<c; j++) gel(p2,j) = i==j? gcopy(gcoeff(d,i,i)): gen_0;
  }
  return y;
}

static GEN
gbezout_step(GEN *pa, GEN *pb, GEN *pu, GEN *pv)
{
  GEN a = *pa, b = *pb, d;
  if (!signe(a))
  {
    *pa = gen_0; *pu = gen_0;
    *pb = gen_1; *pv = gen_1; return b;
  }
  if (typ(a) == t_POL) a = RgX_renormalize(a);
  if (typ(b) == t_POL) b = RgX_renormalize(b);
  d = RgX_extgcd(a,b, pu,pv);
  if (typ(d) == t_POL)
  {
    if (degpol(d)) { a = RgX_div(a, d); b = RgX_div(b, d); }
    else if (typ(d[2]) == t_REAL && lg(d[2]) == 3)
#if 1
    { /* possible accuracy problem */
      GEN D = RgX_gcd_simple(a,b);
      if (degpol(D)) {
	D = RgX_Rg_div(D, leading_term(D));
	a = RgX_div(a, D);
        b = RgX_div(b, D);
	d = RgX_extgcd(a,b, pu,pv); /* retry now */
	d = RgX_mul(d, D);
      }
    }
#else
    { /* less stable */
      d = RgX_extgcd_simple(a,b, pu,pv);
      if (degpol(d)) { a = RgX_div(a, d); b = RgX_div(b, d); }
    }
#endif
  }
  *pa = a;
  *pb = b; return d;
}

static GEN
gsmithall_i(GEN x,long all)
{
  pari_sp av, lim;
  long i, j, k, n;
  GEN z, u, v, U, V;

  if (typ(x)!=t_MAT) pari_err(typeer,"gsmithall");
  n = lg(x)-1;
  if (!n) return trivsmith(all);
  if (lg(x[1]) != n+1) pari_err(mattype1,"gsmithall");
  av = avma; lim = stack_lim(av,1);
  x = shallowcopy(x);
  if (all) { U = matid(n); V = matid(n); }
  for (i=n; i>=2; i--)
  {
    for(;;)
    {
      GEN a, b, d;
      int c = 0;
      for (j=i-1; j>=1; j--)
      {
	b = gcoeff(x,i,j); if (gcmp0(b)) continue;
	a = gcoeff(x,i,i);
	d = gbezout_step(&b, &a, &v, &u);
	for (k = 1; k < i; k++)
	{
	  GEN t = gadd(gmul(u,gcoeff(x,k,i)),gmul(v,gcoeff(x,k,j)));
	  gcoeff(x,k,j) = gsub(gmul(a,gcoeff(x,k,j)),gmul(b,gcoeff(x,k,i)));
	  gcoeff(x,k,i) = t;
	}
	gcoeff(x,i,j) = gen_0;
	gcoeff(x,i,i) = d;
	if (all) update(u,v,a,b,(GEN*)(V+i),(GEN*)(V+j));
      }
      for (j=i-1; j>=1; j--)
      {
	b = gcoeff(x,j,i); if (gcmp0(b)) continue;
	a = gcoeff(x,i,i);
	d = gbezout_step(&b, &a, &v, &u);
	for (k = 1; k < i; k++)
	{
	  GEN t = gadd(gmul(u,gcoeff(x,i,k)),gmul(v,gcoeff(x,j,k)));
	  gcoeff(x,j,k) = gsub(gmul(a,gcoeff(x,j,k)),gmul(b,gcoeff(x,i,k)));
	  gcoeff(x,i,k) = t;
	}
	gcoeff(x,j,i) = gen_0;
	gcoeff(x,i,i) = d;
	if (all) update(u,v,a,b,(GEN*)(U+i),(GEN*)(U+j));
	c = 1;
      }
      if (!c)
      {
	b = gcoeff(x,i,i); if (degpol(b) <= 0) break;

	for (k=1; k<i; k++)
	{
	  for (j=1; j<i; j++)
	  {
	    GEN r = gmod(gcoeff(x,k,j), b);
	    if (signe(r) && (! isinexactreal(r) ||
		   gexpo(r) > 16 + gexpo(b) - bit_accuracy(gprecision(r)))
	       ) break;
	  }
	  if (j != i) break;
	}
	if (k == i) break;

	for (j=1; j<=i; j++)
	  gcoeff(x,i,j) = gadd(gcoeff(x,i,j),gcoeff(x,k,j));
	if (all) gel(U,i) = gadd(gel(U,i),gel(U,k));
      }
      if (low_stack(lim, stack_lim(av,1)))
      {
	if (DEBUGMEM>1) pari_warn(warnmem,"gsmithall");
	gerepileall(av, all? 3: 1, &x, &U, &V);
      }
    }
  }
  for (k=1; k<=n; k++)
  {
    GEN T = gcoeff(x,k,k);
    if (typ(T) == t_POL && signe(T))
    {
      GEN d = leading_term(T);
      while (gcmp0(d) || ( typ(d) == t_REAL && lg(d) == 3
			   && gexpo(T) - expo(d) > (long)BITS_IN_LONG)) {
	 T = normalizepol_i(T, lg(T)-1);
	 if (!signe(T)) { gcoeff(x,k,k) = T; continue; }
	 d = leading_term(T);
      }
      if (!gcmp1(d))
      {
	gcoeff(x,k,k) = RgX_Rg_div(T,d);
	if (all) gel(V,k) = RgC_Rg_div(gel(V,k), d);
      }
    }
  }
  z = all? mkvec3(shallowtrans(U), V, x): RgM_diagonal_shallow(x);
  return gerepilecopy(av, z);
}

GEN
matsnf0(GEN x,long flag)
{
  pari_sp av = avma;
  if (flag > 7) pari_err(flagerr,"matsnf");
  if (typ(x) == t_VEC && flag & 4) return smithclean(x);
  if (flag & 2) x = flag&1 ? gsmithall(x): gsmith(x);
  else          x = flag&1 ?  smithall(x):  smith(x);
  if (flag & 4) x = gerepileupto(av, smithclean(x));
  return x;
}

GEN
gsmith(GEN x) { return gsmithall_i(x,0); }

GEN
gsmithall(GEN x) { return gsmithall_i(x,1); }

/* H relation matrix among row of generators g in HNF.  Let URV = D its SNF,
 * newU R newV = newD its clean SNF (no 1 in Dnew). Return the diagonal of
 * newD, newU and newUi such that  1/U = (newUi, ?).
 * Rationale: let (G,0) = g Ui be the new generators then
 * 0 = G U R --> G D = 0,  g = G newU  and  G = g newUi */
GEN
ZM_snf_group(GEN H, GEN *newU, GEN *newUi)
{
  GEN D = ZM_snfall_i(H, newU, newUi, 1);
  long i, j, l;

  ZM_snfclean(D, newU? *newU: NULL, newUi? *newUi: NULL);
  l = lg(D);
  if (newU) {
    GEN U = *newU;
    for (i = 1; i < l; i++)
    {
      GEN d = gel(D,i), d2 = shifti(d, 1);
      for (j = 1; j < lg(U); j++)
	gcoeff(U,i,j) = centermodii(gcoeff(U,i,j), d, d2);
    }
    *newU = U;
  }
  if (newUi) { /* UHV=D -> U^-1 = HVD^-1 -> U^-1 = H(VD^-1 mod 1) mod H */
    if (l > 1)
    { /* Ui = ZM_inv(U, gen_1); setlg(Ui, l); */
      GEN V = FpM_red(*newUi, gel(D,1));
      GEN Ui = ZM_mul(H, V);
      for (i = 1; i < l; i++) gel(Ui,i) = ZC_Z_divexact(gel(Ui,i), gel(D,i));
      *newUi = ZM_hnfrem(Ui, H);
    }
  }
  return D;
}

/***********************************************************************
 ****                                                               ****
 ****         Frobenius form and Jordan form of a matrix            ****
 ****                                                               ****
 ***********************************************************************/
GEN
Frobeniusform(GEN V, long n)
{
  long i, j, k;
  GEN M = zeromatcopy(n,n);
  for (k=1,i=1;i<lg(V);i++,k++)
  {
    GEN  P = gel(V,i);
    long d = degpol(P);
    if (k+d-1 > n) pari_err(talker, "accuracy lost in matfrobenius");
    for (j=0; j<d-1; j++, k++) gcoeff(M,k+1,k) = gen_1;
    for (j=0; j<d; j++) gcoeff(M,k-j,k) = gneg(gel(P, 1+d-j));
  }
  return M;
}

static GEN
build_frobeniusbc(GEN V, long n)
{
  long i, j, k, l, m = lg(V)-1;
  GEN M = zeromatcopy(n,n), z = monomial(gen_m1, 1, 0); /* -x */
  for (k=1,l=1+m,i=1;i<=m;i++,k++)
  {
    GEN  P = gel(V,i);
    long d = degpol(P);
    if (d <= 0) continue;
    if (l+d-2 > n) pari_err(talker, "accuracy lost in matfrobenius");
    gcoeff(M,k,i) = gen_1;
    for (j=1; j<d; j++,k++,l++)
    {
      gcoeff(M,k,l)   = z;
      gcoeff(M,k+1,l) = gen_1;
    }
  }
  return M;
}

static GEN
build_basischange(GEN N, GEN U)
{
  long i, j, n = lg(N);
  GEN p2 = cgetg(n, t_MAT);
  for (j = 1; j < n; ++j)
  {
    pari_sp btop = avma;
    GEN p3 = gen_0;
    for (i = 1; i < n; ++i)
      p3 = gadd(p3, gel(gsubst(gcoeff(U, i, j), 0, N),i));
    gel(p2,j) = gerepileupto(btop, p3);
  }
  return p2;
}

GEN
matfrobenius(GEN M, long flag, long v)
{
  pari_sp ltop=avma;
  long n;
  GEN D, A, N, B, R, M_x;
  if (typ(M)!=t_MAT) pari_err(typeer,"matfrobenius");
  if (v<0) v=0;
  if (varncmp(gvar(M), v) <= 0)
    pari_err(talker,"variable must have higher priority in matfrobenius");
  n = lg(M)-1;
  if (n && lg(M[1])!=n+1) pari_err(mattype1,"matfrobenius");
  M_x = RgM_Rg_add_shallow(M, monomial(gen_m1, 1, v));
  if (flag<2)
  {
    D = matsnf0(M_x,6);
    if (flag != 1) D = Frobeniusform(D, n);
    return gerepileupto(ltop, D);
  }
  if (flag>2) pari_err(flagerr,"matfrobenius");
  A = matsnf0(M_x,3);
  D = smithclean(RgM_diagonal_shallow(gel(A,3)));
  N = Frobeniusform(D, n);
  B = build_frobeniusbc(D, n);
  R = build_basischange(N, RgM_mul(B,gel(A,1)));
  return gerepilecopy(ltop, mkvec2(N,R));
}
