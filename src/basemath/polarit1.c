/* $Id$

Copyright (C) 2000-2004  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

/***********************************************************************/
/**                                                                   **/
/**               ARITHMETIC OPERATIONS ON POLYNOMIALS                **/
/**                         (first part)                              **/
/**                                                                   **/
/***********************************************************************/
#include "pari.h"
#include "paripriv.h"

/*******************************************************************/
/*                                                                 */
/*                  POLYNOMIAL EUCLIDEAN DIVISION                  */
/*                                                                 */
/*******************************************************************/
GEN
poldivrem(GEN x, GEN y, GEN *pr)
{
  long ty = typ(y), tx, vx = gvar(x), vy = gvar(y);
  GEN p1;

  if (is_scalar_t(ty) || varncmp(vx, vy) < 0)
  {
    if (pr == ONLY_REM) {
      if (gequal0(y)) pari_err(gdiver);
      return gen_0;
    }
    if (pr && pr != ONLY_DIVIDES) *pr=gen_0;
    return gdiv(x,y);
  }
  if (ty != t_POL) pari_err(typeer,"euclidean division (poldivrem)");
  tx = typ(x);
  if (is_scalar_t(tx) || varncmp(vx, vy) > 0)
  {
    if (!signe(y)) pari_err(gdiver);
    if (!degpol(y)) /* constant */
    {
      if (pr == ONLY_REM) return zeropol(vy);
      p1 = gdiv(x, gel(y,2));
      if (pr == ONLY_DIVIDES) return p1;
      if (pr) *pr = zeropol(vy);
      return p1;
    }
    if (pr == ONLY_REM) return gcopy(x);
    if (pr == ONLY_DIVIDES) return gequal0(x)? gen_0: NULL;
    if (pr) *pr = gcopy(x);
    return gen_0;
  }
  if (tx != t_POL) pari_err(typeer,"euclidean division (poldivrem)");

  if (varncmp(vx, vy) < 0)
  {
    if (pr && pr != ONLY_DIVIDES)
    {
      p1 = zeropol(vx); if (pr == ONLY_REM) return p1;
      *pr = p1;
    }
    return gdiv(x,y);
  }
  return RgX_divrem(x, y, pr);
}
GEN
gdeuc(GEN x, GEN y)
{
  long ty = typ(y), tx, vx = gvar(x), vy = gvar(y);

  if (is_scalar_t(ty) || varncmp(vx, vy) < 0) return gdiv(x,y);
  if (ty != t_POL) pari_err(typeer,"euclidean division (poldivrem)");
  tx = typ(x);
  if (is_scalar_t(tx) || varncmp(vx, vy) > 0)
  {
    if (!signe(y)) pari_err(gdiver);
    if (!degpol(y)) return gdiv(x, gel(y,2)); /* constant */
    return gen_0;
  }
  if (tx != t_POL) pari_err(typeer,"euclidean division (poldivrem)");
  if (varncmp(vx, vy) < 0) return gdiv(x,y);
  return RgX_div(x, y);
}
GEN
grem(GEN x, GEN y)
{
  long ty = typ(y), tx, vx = gvar(x), vy = gvar(y);

  if (is_scalar_t(ty) || varncmp(vx, vy) < 0)
  {
    if (gequal0(y)) pari_err(gdiver);
    return gen_0;
  }
  if (ty != t_POL) pari_err(typeer,"euclidean division (poldivrem)");
  tx = typ(x);
  if (is_scalar_t(tx) || varncmp(vx, vy) > 0)
  {
    if (!signe(y)) pari_err(gdiver);
    if (!degpol(y)) return zeropol(vy); /* constant */
    return gcopy(x);
  }
  if (tx != t_POL) pari_err(typeer,"euclidean division (poldivrem)");

  if (varncmp(vx, vy) < 0) return zeropol(vx);
  return RgX_rem(x, y);
}

/*******************************************************************/
/*                                                                 */
/*           ROOTS MODULO a prime p (no multiplicities)            */
/*                                                                 */
/*******************************************************************/
static ulong
init_p(GEN pp)
{
  ulong p;
  if ((ulong)expi(pp) > BITS_IN_LONG - 3) p = 0;
  else
  {
    p = itou(pp);
    if (p < 2 || signe(pp) < 0) pari_err(talker,"not a prime in factmod");
  }
  return p;
}

static long
factmod_init(GEN *F, GEN p)
{
  long d;
  if (typ(*F)!=t_POL || typ(p)!=t_INT) pari_err(typeer,"factmod");
  *F = FpX_normalize(RgX_to_FpX(*F, p), p);
  d = degpol(*F); if (d < 0) pari_err(zeropoler,"factmod");
  return d;
}

static GEN
root_mod_2(GEN f)
{
  int z1, z0 = !signe(constant_term(f));
  long i,n;
  GEN y;

  for (i=2, n=1; i < lg(f); i++)
    if (signe(f[i])) n++;
  z1 = n & 1;
  y = cgetg(z0+z1+1, t_COL); i = 1;
  if (z0) gel(y,i++) = gen_0;
  if (z1) gel(y,i) = gen_1;
  return y;
}

#define i_mod4(x) (signe(x)? mod4((GEN)(x)): 0)
static GEN
root_mod_4(GEN f)
{
  long i, no, ne;
  GEN y, t;
  int z0, z1, z2, z3;

  t = constant_term(f);
  z0 = !signe(t);
  z2 = ((i_mod4(t) + 2*i_mod4(f[3])) & 3) == 0;

  for (ne=0,i=2; i<lg(f); i+=2)
  {
    t = gel(f,i);
    if (signe(t)) ne += *int_LSW(t);
  }
  for (no=0,i=3; i<lg(f); i+=2)
  {
    t = gel(f,i);
    if (signe(t)) ne += *int_LSW(t);
  }
  no &= 3; ne &= 3;
  z3 = (no == ne);
  z1 = (no == ((4-ne)&3));
  y=cgetg(1+z0+z1+z2+z3,t_COL); i = 1;
  if (z0) gel(y,i++) = gen_0;
  if (z1) gel(y,i++) = gen_1;
  if (z2) gel(y,i++) = gen_2;
  if (z3) gel(y,i) = utoipos(3);
  return y;
}
#undef i_mod4

/* p even, accept p = 4 for p-adic stuff */
INLINE GEN
root_mod_even(GEN f, ulong p)
{
  switch(p)
  {
    case 2: return root_mod_2(f);
    case 4: return root_mod_4(f);
  }
  pari_err(talker,"not a prime in rootmod");
  return NULL; /* not reached */
}

/* by checking f(0..p-1) */
GEN
Flx_roots_naive(GEN f, ulong p)
{
  long d = degpol(f), n = 0;
  ulong s = 1UL, r;
  GEN q, y = cgetg(d + 1, t_VECSMALL);
  pari_sp av2, av = avma;

  if (Flx_valrem(f, &f)) { y[++n] = 0; d = degpol(f); }
  av2 = avma;
  while (d > 1) /* d = current degree of f */
  {
    q = Flx_div_by_X_x(f, s, p, &r); /* TODO: FFT-type multi-evaluation */
    if (r) avma = av2; else { y[++n] = s; d--; f = q; av2 = avma; }
    if (++s == p) break;
  }
  if (d == 1)
  { /* -f[2]/f[3], root of deg 1 polynomial */
    r = Fl_mul(p - Fl_inv(f[3], p), f[2], p);
    if (r >= s) y[++n] = r; /* otherwise double root */
  }
  avma = av; fixlg(y, n+1); return y;
}

GEN
rootmod2(GEN f, GEN pp)
{
  pari_sp av = avma;
  ulong p;
  GEN y;

  if (!factmod_init(&f, pp)) { avma = av; return cgetg(1,t_COL); }
  p = init_p(pp); if (!p) pari_err(talker,"prime too big in rootmod2");
  if (p & 1)
    y = Flc_to_ZC(Flx_roots_naive(ZX_to_Flx(f,p), p));
  else
    y = root_mod_even(f,p);
  return gerepileupto(av, FpC_to_mod(y, pp));
}

/* assume x reduced mod p, monic. */
static int
FpX_quad_factortype(GEN x, GEN p)
{
  GEN b = gel(x,3), c = gel(x,2);
  GEN D;

  if (equaliu(p, 2)) {
    if (!signe(b)) return 0;
    return signe(c)? -1: 1;
  }
  D = subii(sqri(b), shifti(c,2));
  return kronecker(D,p);
}
/* assume x reduced mod p, monic. Return one root, or NULL if irreducible */
GEN
FpX_quad_root(GEN x, GEN p, int unknown)
{
  GEN s, u, D, b = gel(x,3), c = gel(x,2);

  if (equaliu(p, 2)) {
    if (!signe(b)) return c;
    return signe(c)? NULL: gen_1;
  }
  D = subii(sqri(b), shifti(c,2));
  D = remii(D,p);
  if (unknown && kronecker(D,p) == -1) return NULL;

  s = Fp_sqrt(D,p);
  /* p is not prime, go on and give e.g. maxord a chance to recover */
  if (!s) return NULL;
  u = addis(shifti(p,-1), 1); /* = 1/2 */
  return Fp_mul(u, subii(s,b), p);
}
static GEN
otherroot(GEN x, GEN r, GEN p)
{
  GEN s = addii(gel(x,3), r);
  if (!signe(s)) return s;
  s = subii(p, s); if (signe(s) < 0) s = addii(s,p);
  return s;
}

/* by splitting, assume p > 2 prime, deg(f) > 0, and f monic */
static GEN
FpX_roots_i(GEN f, GEN p)
{
  long n, j, da, db;
  GEN y, pol, pol0, a, b, q = shifti(p,-1);

  n = ZX_valrem(f, &f)? 1: 0;
  y = cgetg(lg(f), t_COL);
  j = 1;
  if (n) {
    gel(y, j++) = gen_0;
    if (lg(f) <= 3) { setlg(y, 2); return y; }
    n = 1;
  }
  da = degpol(f);
  if (da == 1) { gel(y,j++) = subii(p, gel(f,2)); setlg(y,j); return y; }
  if (da == 2) {
    GEN s, r = FpX_quad_root(f, p, 1);
    if (r) {
      gel(y, j++) = r;
      s = otherroot(f,r, p);
      if (!equalii(r, s)) gel(y, j++) = s;
    }
    setlg(y, j); return sort(y);
  }

  /* take gcd(x^(p-1) - 1, f) by splitting (x^q-1) * (x^q+1) */
  b = FpXQ_pow(pol_x(varn(f)),q, f,p);
  if (lg(b) < 3) pari_err(talker,"not a prime in rootmod");
  b = ZX_Z_add(b, gen_m1); /* b = x^((p-1)/2) - 1 mod f */
  a = FpX_gcd(f,b, p);
  b = ZX_Z_add(b, gen_2); /* b = x^((p-1)/2) + 1 mod f */
  b = FpX_gcd(f,b, p);
  da = degpol(a);
  db = degpol(b); n += da + db; setlg(y, n+1);
  if (db) gel(y,j)    = FpX_normalize(b,p);
  if (da) gel(y,j+db) = FpX_normalize(a,p);
  pol0 = icopy(gen_1); /* constant term, will vary in place */
  pol = deg1pol_shallow(gen_1, pol0, varn(f));
  while (j <= n)
  { /* cf FpX_split_Berlekamp */
    a = gel(y,j); da = degpol(a);
    if (da==1)
      gel(y,j++) = subii(p, gel(a,2));
    else if (da==2)
    {
      GEN r = FpX_quad_root(a, p, 0);
      gel(y, j++) = r;
      gel(y, j++) = otherroot(a,r, p);
    }
    else for (pol0[2]=1; ; pol0[2]++)
    {
      b = ZX_Z_add(FpXQ_pow(pol,q, a,p), gen_m1); /* pol^(p-1)/2 - 1 */
      b = FpX_gcd(a,b, p); db = degpol(b);
      if (db && db < da)
      {
        b = FpX_normalize(b, p);
        gel(y,j+db) = FpX_div(a,b, p);
        gel(y,j)    = b; break;
      }
      if (pol0[2] == 100 && !BPSW_psp(p))
        pari_err(talker, "not a prime in polrootsmod");
    }
  }
  return sort(y);
}
static GEN
FpX_oneroot_i(GEN f, GEN p)
{
  long da, db;
  GEN pol, pol0, a, b, q = shifti(p,-1);

  if (ZX_val(f)) return gen_0;
  da = degpol(f);
  if (da == 1) return subii(p, gel(f,2));
  if (da == 2) return FpX_quad_root(f, p, 1);

  /* take gcd(x^(p-1) - 1, f) by splitting (x^q-1) * (x^q+1) */
  b = FpXQ_pow(pol_x(varn(f)),q, f,p);
  if (lg(b) < 3) pari_err(talker,"not a prime in rootmod");
  b = ZX_Z_add(b, gen_m1); /* b = x^((p-1)/2) - 1 mod f */
  a = FpX_gcd(f,b, p);
  b = ZX_Z_add(b, gen_2); /* b = x^((p-1)/2) + 1 mod f */
  b = FpX_gcd(f,b, p);
  da = degpol(a);
  db = degpol(b);
  if (!da)
  {
    if (!db) return NULL;
    a = b;
  }
  else
    if (db && db < da) a = b;
  a = FpX_normalize(a,p);
  pol0 = icopy(gen_1); /* constant term, will vary in place */
  pol = deg1pol_shallow(gen_1, pol0, varn(f));
  for(;;)
  { /* cf FpX_split_Berlekamp */
    da = degpol(a);
    if (da==1)
      return subii(p, gel(a,2));
    if (da==2)
      return FpX_quad_root(a, p, 0);
    for (pol0[2]=1; ; pol0[2]++)
    {
      b = ZX_Z_add(FpXQ_pow(pol,q, a,p), gen_m1); /* pol^(p-1)/2 - 1 */
      b = FpX_gcd(a,b, p); db = degpol(b);
      if (db && db < da)
      {
        b = FpX_normalize(b, p);
        a = (db <= (da >> 1))? b: FpX_div(a,b, p);
        break;
      }
      if (pol0[2] == 100 && !BPSW_psp(p))
        pari_err(talker, "not a prime in polrootsmod");
    }
  }
}

static GEN
FpX_factmod_init(GEN f, GEN p) { return FpX_normalize(FpX_red(f,p), p); }
GEN
FpX_roots(GEN f, GEN p) {
  pari_sp av = avma;
  long q = mod2BIL(p);
  GEN F = FpX_factmod_init(f,p);
  switch(degpol(F))
  {
    case -1: pari_err(zeropoler,"factmod");
    case 0: avma = av; return cgetg(1, t_COL);
  }
  return gerepileupto(av, odd(q)? FpX_roots_i(F, p): root_mod_even(F,q));
}
GEN
FpX_oneroot(GEN f, GEN p) {
  pari_sp av = avma;
  long q = mod2BIL(p);
  GEN F = FpX_factmod_init(f,p);
  switch(degpol(F))
  {
    case -1: pari_err(zeropoler,"factmod");
    case 0: avma = av; return NULL;
  }
  if (!odd(q))
  {
    F = root_mod_even(F,q); avma = av;
    return (lg(F) == 1)? NULL: gel(F,1);
  }
  F = FpX_oneroot_i(F, p);
  if (!F) { avma = av; return NULL; }
  return gerepileuptoint(av, F);
}

GEN
rootmod(GEN f, GEN p)
{
  ulong q;
  pari_sp av = avma;
  GEN y;

  if (!factmod_init(&f, p)) { avma=av; return cgetg(1,t_COL); }
  q = init_p(p); if (!q) q = mod2BIL(p);
  if (q & 1)
    y = FpX_roots_i(f, p);
  else
    y = root_mod_even(f,q);
  return gerepileupto(av, FpC_to_mod(y, p));
}

GEN
rootmod0(GEN f, GEN p, long flag)
{
  switch(flag)
  {
    case 0: return rootmod(f,p);
    case 1: return rootmod2(f,p);
    default: pari_err(flagerr,"polrootsmod");
  }
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                     FACTORISATION MODULO p                      */
/*                                                                 */
/*******************************************************************/
static GEN spec_FpXQ_pow(GEN x, GEN p, GEN S);

/* Functions giving information on the factorisation. */

/* u in Z[X], return kernel of (Frob - Id) over Fp[X] / u */
GEN
FpX_Berlekamp_ker(GEN u, GEN p)
{
  pari_sp ltop=avma;
  long j,N = degpol(u);
  GEN XP = FpXQ_pow(pol_x(varn(u)),p,u,p);
  GEN Q  = FpXQ_matrix_pow(XP,N,N,u,p);
  for (j=1; j<=N; j++)
    gcoeff(Q,j,j) = Fp_sub(gcoeff(Q,j,j), gen_1, p);
  return gerepileupto(ltop, FpM_ker(Q,p));
}

GEN
F2x_Berlekamp_ker(GEN u)
{
  pari_sp ltop=avma;
  long j,N = F2x_degree(u);
  GEN Q, XP;
  pari_timer T;
  TIMERstart(&T);
  XP = F2xq_sqr(polx_F2x(u[1]),u);
  Q  = F2xq_matrix_pow(XP,N,N,u);
  for (j=1; j<=N; j++)
    F2m_flip(Q,j,j);
  if(DEBUGLEVEL>=9) msgTIMER(&T,"Berlekamp matrix");
  Q = F2m_ker_sp(Q,0);
  if(DEBUGLEVEL>=9) msgTIMER(&T,"kernel");
  return gerepileupto(ltop,Q);
}

GEN
Flx_Berlekamp_ker(GEN u, ulong l)
{
  pari_sp ltop=avma;
  long j,N = degpol(u);
  GEN Q, XP;
  pari_timer T;
  TIMERstart(&T);
  XP = Flxq_pow(polx_Flx(u[1]),utoipos(l),u,l);
  Q  = Flxq_matrix_pow(XP,N,N,u,l);
  for (j=1; j<=N; j++)
    coeff(Q,j,j) = Fl_sub(coeff(Q,j,j),1,l);
  if(DEBUGLEVEL>=9) msgTIMER(&T,"Berlekamp matrix");
  Q = Flm_ker_sp(Q,l,0);
  if(DEBUGLEVEL>=9) msgTIMER(&T,"kernel");
  return gerepileupto(ltop,Q);
}

GEN
FqX_Berlekamp_ker(GEN u, GEN T, GEN q, GEN p)
{
  pari_sp ltop=avma;
  long j,N = degpol(u);
  GEN v,w,Q,p1;
  pari_timer Ti;
  if (DEBUGLEVEL>=4) TIMERstart(&Ti);
  Q = cgetg(N+1,t_MAT); gel(Q,1) = zerocol(N);
  w = v = FpXQYQ_pow(pol_x(varn(u)), q, u, T, p);
  if (DEBUGLEVEL>=4) msgTIMER(&Ti, "FpXQYQ_pow");
  for (j=2; j<=N; j++)
  {
    p1 = RgX_to_RgV(w, N);
    gel(p1,j) = gaddgs(gel(p1,j), -1);
    gel(Q,j) = p1;
    if (j < N)
    {
      pari_sp av = avma;
      w = gerepileupto(av, FpXQX_divrem(FpXQX_mul(w,v, T,p), u,T,p,ONLY_REM));
    }
  }
  if (DEBUGLEVEL>=4) msgTIMER(&Ti, "Berlekamp_matrix");
  p1 = FqM_ker(Q,T,p);
  if (DEBUGLEVEL>=4) msgTIMER(&Ti, "Berlekamp_ker");
  return gerepileupto(ltop,p1);
}

GEN
FqX_deriv(GEN f, /*unused*/GEN T, GEN p) {
  (void)T; return FpXX_red(RgX_deriv(f), p);
}

/* product of terms of degree 1 in factorization of f */
static GEN
FpX_split_part(GEN f, GEN p)
{
  long n = degpol(f);
  GEN z, X = pol_x(varn(f));
  if (n <= 1) return f;
  f = FpX_red(f, p);
  z = FpXQ_pow(X, p, f, p);
  z = FpX_sub(z, X, p);
  return FpX_gcd(z,f,p);
}

static GEN
FqX_split_part(GEN f, GEN T, GEN p)
{
  long n = degpol(f);
  GEN z, X = pol_x(varn(f));
  if (n <= 1) return f;
  f = FpXQX_red(f, T, p);
  z = FpXQYQ_pow(X, powiu(p, degpol(T)), f, T, p);
  z = gsub(z, X);
  return FqX_gcd(z, f, T, p);
}

/* Compute the number of roots in Fq without counting multiplicity
 * return -1 for 0 polynomial. lc(f) must be prime to p. */
long
FpX_nbroots(GEN f, GEN p)
{
  pari_sp av = avma;
  GEN z = FpX_split_part(f, p);
  avma = av; return degpol(z);
}

long
FqX_nbroots(GEN f, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z = FqX_split_part(f, T, p);
  avma = av; return degpol(z);
}

int
FpX_is_totally_split(GEN f, GEN p)
{
  long n=degpol(f);
  pari_sp av = avma;
  GEN z;
  if (n <= 1) return 1;
  if (cmpui(n, p) > 0) return 0;
  f = FpX_red(f, p);
  z = FpXQ_pow(pol_x(varn(f)), p, f, p);
  avma = av;
  return degpol(z) == 1 && gequal1(gel(z,3)) && !signe(z[2]); /* x^p = x ? */
}

/* Flv_Flx( Flm_Flc_mul(x, Flx_Flv(y), p) ) */
static GEN
Flm_Flx_mul(GEN x, GEN y, ulong p)
{
  long i,k,l, ly = lg(y)-1;
  GEN z;
  long vs=y[1];
  if (ly==1) return zero_Flx(vs);
  l = lg(x[1]);
  y++;
  z = const_vecsmall(l,0) + 1;
  if (SMALL_ULONG(p))
  {
    for (k=1; k<ly; k++)
    {
      GEN c;
      if (!y[k]) continue;
      c = gel(x,k);
      if (y[k] == 1)
        for (i=1; i<l; i++)
        {
          z[i] += c[i];
          if (z[i] & HIGHBIT) z[i] %= p;
        }
      else
        for (i=1; i<l; i++)
        {
          z[i] += c[i] * y[k];
          if (z[i] & HIGHBIT) z[i] %= p;
        }
    }
    for (i=1; i<l; i++) z[i] %= p;
  }
  else
  {
    for (k=1; k<ly; k++)
    {
      GEN c;
      if (!y[k]) continue;
      c = gel(x,k);
      if (y[k] == 1)
        for (i=1; i<l; i++)
          z[i] = Fl_add(z[i], c[i], p);
      else
        for (i=1; i<l; i++)
          z[i] = Fl_add(z[i], Fl_mul(c[i],y[k],p), p);
    }
  }
  while (--l && !z[l]);
  if (!l) return zero_Flx(vs);
  *z-- = vs; return z;
}

/* assume deg(u) > 0 */
static GEN
Flx_Frobenius(GEN u, ulong p)
{
  long j,N = degpol(u);
  GEN v,w,Q;
  pari_timer T;

  if (DEBUGLEVEL > 7) TIMERstart(&T);
  Q = cgetg(N+1,t_MAT);
  gel(Q,1) = const_vecsmall(N, 0);
  coeff(Q,1,1) = 1;
  w = v = Flxq_pow(polx_Flx(u[1]), utoipos(p), u, p);
  for (j=2; j<=N; j++)
  {
    gel(Q,j) = Flx_to_Flv(w, N);
    if (j < N)
    {
      pari_sp av = avma;
      w = gerepileupto(av, Flxq_mul(w, v, u, p));
    }
  }
  if (DEBUGLEVEL > 7) msgTIMER(&T, "frobenius");
  return Q;
}

/* z must be squarefree mod p*/
GEN
Flx_nbfact_by_degree(GEN z, long *nb, ulong p)
{
  long lgg, d = 0, e = degpol(z);
  GEN D = const_vecsmall(e, 0);
  pari_sp av = avma;
  GEN g, w, MP = Flx_Frobenius(z, p), PolX = polx_Flx(z[1]);

  w = PolX; *nb = 0;
  while (d < (e>>1))
  { /* here e = degpol(z) */
    d++;
    w = Flm_Flx_mul(MP, w, p); /* w^p mod (z,p) */
    g = Flx_gcd(z, Flx_sub(w, PolX, p), p);
    lgg = degpol(g); if (!lgg) continue;

    e -= lgg;
    D[d] = lgg/d; *nb += D[d];
    if (DEBUGLEVEL>5) fprintferr("   %3ld fact. of degree %3ld\n", D[d], d);
    if (!e) break;
    z = Flx_div(z, g, p);
    w = Flx_rem(w, z, p);
  }
  if (e)
  {
    if (DEBUGLEVEL>5) fprintferr("   %3ld fact. of degree %3ld\n",1,e);
    D[e] = 1; (*nb)++;
  }
  avma = av; return D;
}

/* z must be squarefree mod p*/
long
Flx_nbfact(GEN z, ulong p)
{
  pari_sp av = avma;
  long nb; (void)Flx_nbfact_by_degree(z, &nb, p);
  avma = av; return nb;
}

long
Flx_nbroots(GEN f, ulong p)
{
  long n = degpol(f);
  pari_sp av = avma;
  GEN z, X;
  if (n <= 1) return n;
  X = polx_Flx(f[1]);
  z = Flxq_pow(X, utoipos(p), f, p);
  z = Flx_sub(z, X, p);
  z = Flx_gcd(z, f, p);
  avma = av; return degpol(z);
}

long
FpX_nbfact(GEN u, GEN p)
{
  pari_sp av = avma;
  GEN vker = FpX_Berlekamp_ker(u, p);
  avma = av; return lg(vker)-1;
}

long
FqX_nbfact(GEN u, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN vker;
  if (!T) return FpX_nbfact(u, p);
  vker = FqX_Berlekamp_ker(u, T, powiu(p, degpol(T)), p);
  avma = av; return lg(vker)-1;
}

/************************************************************/
GEN
trivfact(void)
{
  GEN y = cgetg(3,t_MAT);
  gel(y,1) = gel(y,2) = cgetg(1,t_COL); return y;
}

/* polynomial in variable v, whose coeffs are the digits of m in base p */
static GEN
stoFpX(ulong m, ulong p, long v)
{
  GEN y = new_chunk(BITS_IN_LONG + 2);
  long l = 2;
  do { ulong q = m/p; gel(y,l++) = utoi(m - q*p); m=q; } while (m);
  y[1] = evalsigne(1) | evalvarn(v);
  y[0] = evaltyp(t_POL) | evallg(l); return y;
}
static GEN
itoFpX(GEN m, GEN p, long v)
{
  GEN y = new_chunk(bit_accuracy(lgefint(m))+2);
  long l = 2;
  do { m = dvmdii(m, p, &gel(y,l)); l++; } while (signe(m));
  y[1] = evalsigne(1) | evalvarn(v);
  y[0] = evaltyp(t_POL) | evallg(l); return y;
}

static GEN
try_pow(GEN w0, GEN pol, GEN p, GEN q, long r)
{
  GEN w2, w = FpXQ_pow(w0,q, pol,p);
  long s;
  if (gequal1(w)) return w0;
  for (s=1; s<r; s++,w=w2)
  {
    w2 = gsqr(w);
    w2 = FpX_rem(w2, pol, p);
    if (gequal1(w2)) break;
  }
  return gequalm1(w)? NULL: w;
}

/* INPUT:
 *  m integer (converted to polynomial w in Z[X] by stoFpX)
 *  p prime; q = (p^d-1) / 2^r
 *  t[0] polynomial of degree k*d product of k irreducible factors of degree d
 *  t[0] is expected to be normalized (leading coeff = 1)
 * OUTPUT:
 *  t[0],t[1]...t[k-1] the k factors, normalized */
static void
split(ulong m, GEN *t, long d, GEN p, GEN q, long r, GEN S)
{
  long l, v, dv;
  ulong ps;
  pari_sp av0, av;
  GEN w,w0;

  dv=degpol(*t); if (dv==d) return;
  v=varn(*t); av0=avma; ps = (ulong)p[2];
  for(av=avma;;avma=av)
  {
    if (ps==2)
    {
      w0 = w = FpXQ_pow(pol_x(v), utoi(m-1), *t, gen_2); m += 2;
      for (l=1; l<d; l++)
        w = ZX_add(w0, spec_FpXQ_pow(w, p, S));
    }
    else
    {
      w = FpX_rem(stoFpX(m,ps,v),*t, p);
      m++; w = try_pow(w,*t,p,q,r);
      if (!w) continue;
      w = ZX_Z_add(w, gen_m1);
    }
    w = FpX_gcd(*t,w, p);
    l = degpol(w); if (l && l!=dv) break;
  }
  w = FpX_normalize(w, p);
  w = gerepileupto(av0, w);
  l /= d; t[l]=FpX_div(*t,w,p); *t=w;
  split(m,t+l,d,p,q,r,S);
  split(m,t,  d,p,q,r,S);
}

static void
splitgen(GEN m, GEN *t, long d, GEN  p, GEN q, long r)
{
  long l, v, dv = degpol(*t);
  pari_sp av;
  GEN w;

  if (dv==d) return;
  v = varn(*t);
  m = setloop(m);
  av = avma;
  for(;; avma = av)
  {
    m = incloop(m);
    w = FpX_rem(itoFpX(m,p,v),*t, p);
    w = try_pow(w,*t,p,q,r);
    if (!w) continue;
    w = ZX_Z_add(w, gen_m1);
    w = FpX_gcd(*t,w, p); l=degpol(w);
    if (l && l!=dv) break;
  }
  w = FpX_normalize(w, p);
  w = gerepileupto(av, w);
  l /= d; t[l]=FpX_div(*t,w,p); *t=w;
  splitgen(m,t+l,d,p,q,r);
  splitgen(m,t,  d,p,q,r);
}

/* return S = [ x^p, x^2p, ... x^(n-1)p ] mod (p, T), n = degree(T) > 0 */
static GEN
init_spec_FpXQ_pow(GEN p, GEN T)
{
  long i, n = degpol(T), v = varn(T);
  GEN S = cgetg(n, t_VEC), x;
  if (n == 1) return S;
  x = FpXQ_pow(pol_x(v), p, T, p);
  gel(S,1) = x;
  if ((degpol(x)<<1) < degpol(T)) {
    for (i=2; i < n; i++)
      gel(S,i) = FpXQ_mul(gel(S,i-1), x, T,p);
  } else {
    for (i=2; i < n; i++)
      gel(S,i) = (i&1)? FpXQ_mul(gel(S,i-1), x, T,p)
                      : FpXQ_sqr(gel(S,i>>1), T, p);
  }
  return S;
}

/* compute x^p, S is as above */
static GEN
spec_FpXQ_pow(GEN x, GEN p, GEN S)
{
  long i, dx = degpol(x);
  pari_sp av = avma, lim = stack_lim(av, 1);
  GEN x0 = x+2, z = gel(x0,0);
  if (dx < 0) pari_err(talker, "zero polynomial in FpXQ_pow. %Ps not prime", p);
  for (i = 1; i <= dx; i++)
  {
    GEN d, c = gel(x0,i); /* assume coeffs in [0, p-1] */
    if (!signe(c)) continue;
    d = gel(S,i); if (!gequal1(c)) d = ZX_Z_mul(d, c);
    z = typ(z) == t_INT? ZX_Z_add(d,z): ZX_add(d,z);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"spec_FpXQ_pow");
      z = gerepileupto(av, z);
    }
  }
  return gerepileupto(av, FpX_red(z, p));
}

static int
cmpGsGs(GEN a, GEN b) { return (long)a - (long)b; }

static GEN
FpX_is_irred_2(GEN f, GEN p, long d)
{
  if (!d) return NULL;
  if (d == 1) return gen_1;
  return FpX_quad_factortype(f, p) == -1? gen_1: NULL;
}
static GEN
FpX_degfact_2(GEN f, GEN p, long d)
{
  if (!d) return trivfact();
  if (d == 1) return mkvec2(mkvecsmall(1), mkvecsmall(1));
  switch(FpX_quad_factortype(f, p)) {
    case 1: return mkvec2(mkvecsmall2(1,1), mkvecsmall2(1,1));
    case -1:return mkvec2(mkvecsmall(2), mkvecsmall(1));
    default: return mkvec2(mkvecsmall(1), mkvecsmall(2));
  }
}
static GEN
FpX_factor_2(GEN f, GEN p, long d)
{
  GEN r, s, R, S;
  long v;
  int sgn;
  if (d < 0) pari_err(zeropoler,"FpX_factor_2");
  if (!d) return mkvec2(cgetg(1,t_COL), cgetg(1,t_VECSMALL));
  if (d == 1) return mkvec2(mkcol(f), mkvecsmall(1));
  r = FpX_quad_root(f, p, 1);
  if (!r) return mkvec2(mkcol(f), mkvecsmall(1));
  v = varn(f);
  s = otherroot(f, r, p);
  if (signe(r)) r = subii(p, r);
  if (signe(s)) s = subii(p, s);
  sgn = cmpii(s, r); if (sgn < 0) swap(s,r);
  R = deg1pol_shallow(gen_1, r, v);
  if (!sgn) return mkvec2(mkcol(R), mkvecsmall(2));
  S = deg1pol_shallow(gen_1, s, v);
  return mkvec2(mkcol2(R,S), mkvecsmall2(1,1));
}

/* factor f mod pp.
 * flag = 1: return the degrees, not the factors
 * flag = 2: return NULL if f is not irreducible */
static GEN
FpX_factcantor_i(GEN f, GEN pp, long flag)
{
  long j, e, vf, nbfact, d = degpol(f);
  ulong p, k;
  GEN E,y,f2,g,g1,u,v,pd,q;
  GEN *t;

  if (d <= 2) switch(flag) {
    case 2: return FpX_is_irred_2(f, pp, d);
    case 1: return FpX_degfact_2(f, pp, d);
    default: return FpX_factor_2(f, pp, d);
  }
  p = init_p(pp);

  /* to hold factors and exponents */
  t = (GEN*)cgetg(d+1,t_VEC);
  E = cgetg(d+1, t_VECSMALL);
  vf=varn(f); e = nbfact = 1;
  for(;;)
  {
    f2 = FpX_gcd(f,ZX_deriv(f), pp);
    if (flag > 1 && lg(f2) > 3) return NULL;
    g1 = FpX_div(f,f2,pp);
    k = 0;
    while (lg(g1)>3)
    {
      long du,dg;
      GEN S;
      k++; if (p && !(k%p)) { k++; f2 = FpX_div(f2,g1,pp); }
      u = g1; g1 = FpX_gcd(f2,g1, pp);
      if (lg(g1)>3)
      {
        u = FpX_div( u,g1,pp);
        f2= FpX_div(f2,g1,pp);
      }
      du = degpol(u);
      if (du <= 0) continue;

      /* here u is square-free (product of irred. of multiplicity e * k) */
      S = init_spec_FpXQ_pow(pp, u);
      pd=gen_1; v=pol_x(vf);
      for (d=1; d <= du>>1; d++)
      {
        if (!flag) pd = mulii(pd,pp);
        v = spec_FpXQ_pow(v, pp, S);
        g = FpX_gcd(ZX_sub(v, pol_x(vf)), u, pp);
        dg = degpol(g);
        if (dg <= 0) continue;

        /* g is a product of irred. pols, all of which have degree d */
        j = nbfact+dg/d;
        if (flag)
        {
          if (flag > 1) return NULL;
          for ( ; nbfact<j; nbfact++) { t[nbfact]=(GEN)d; E[nbfact]=e*k; }
        }
        else
        {
          long r;
          g = FpX_normalize(g, pp);
          t[nbfact]=g; q = subis(pd,1); /* also ok for p=2: unused */
          r = vali(q); q = shifti(q,-r);
         /* First parameter is an integer m, converted to polynomial w_m, whose
          * coeffs are its digits in base p (initially m = p --> w_m = X). Take
          * gcd(g, w_m^(p^d-1)/2), m++, until a factor is found. p = 2 is
          * treated separately */
          if (p)
            split(p,t+nbfact,d,pp,q,r,S);
          else
            splitgen(pp,t+nbfact,d,pp,q,r);
          for (; nbfact<j; nbfact++) E[nbfact]=e*k;
        }
        du -= dg;
        u = FpX_div(u,g,pp);
        v = FpX_rem(v,u,pp);
      }
      if (du)
      {
        t[nbfact] = flag? (GEN)du: FpX_normalize(u, pp);
        E[nbfact++]=e*k;
      }
    }
    j = lg(f2); if (j==3) break;
    e *= p; f = RgX_deflate(f2, p);
  }
  if (flag > 1) return gen_1; /* irreducible */
  setlg(t, nbfact);
  setlg(E, nbfact); y = mkvec2((GEN)t, E);
  return flag ? sort_factor(y, (void*)&cmpGsGs, cmp_nodata)
              : sort_factor_pol(y, cmpii);
}
GEN
FpX_factcantor(GEN f, GEN pp, long flag)
{
  pari_sp av = avma;
  GEN z = FpX_factcantor_i(FpX_factmod_init(f,pp),pp,flag);
  if (flag == 2) { avma = av; return z; }
  return gerepileupto(av, z);
}
GEN
factcantor0(GEN f, GEN pp, long flag)
{
  pari_sp av = avma;
  long j, nbfact;
  GEN z, y, t, E, u, v;
  if (! factmod_init(&f, pp)) { avma=av; return trivfact(); }
  z = FpX_factcantor_i(f,pp,flag); t = gel(z,1); E = gel(z,2);
  y = cgetg(3, t_MAT); nbfact = lg(t);
  u = cgetg(nbfact,t_COL); gel(y,1) = u;
  v = cgetg(nbfact,t_COL); gel(y,2) = v;
  if (flag)
    for (j=1; j<nbfact; j++)
    {
      gel(u,j) = utoi((ulong)t[j]);
      gel(v,j) = utoi((ulong)E[j]);
    }
  else
    for (j=1; j<nbfact; j++)
    {
      gel(u,j) = FpX_to_mod(gel(t,j), pp);
      gel(v,j) = utoi((ulong)E[j]);
    }
  return gerepileupto(av, y);
}

/* Use this function when you think f is reducible, and that there are lots of
 * factors. If you believe f has few factors, use FpX_nbfact(f,p)==1 instead */
int
FpX_is_irred(GEN f, GEN p) {
  return !!FpX_factcantor_i(FpX_factmod_init(f,p),p,2);
}
GEN
FpX_degfact(GEN f, GEN p) {
  pari_sp av = avma;
  GEN z = FpX_factcantor_i(FpX_factmod_init(f,p),p,1);
  settyp(z[1], t_VECSMALL);
  settyp(z, t_MAT); return gerepilecopy(av, z);
}
GEN
factcantor(GEN f, GEN p) { return factcantor0(f,p,0); }
GEN
simplefactmod(GEN f, GEN p) { return factcantor0(f,p,1); }

/* set x <-- x + c*y mod p */
/* x is not required to be normalized.*/
static void
Flx_addmul_inplace(GEN gx, GEN gy, ulong c, ulong p)
{
  long i, lx, ly;
  ulong *x=(ulong *)gx;
  ulong *y=(ulong *)gy;
  if (!c) return;
  lx = lg(gx);
  ly = lg(gy);
  if (lx<ly) pari_err(bugparier,"lx<ly in Flx_addmul_inplace");
  if (SMALL_ULONG(p))
    for (i=2; i<ly;  i++) x[i] = (x[i] + c*y[i]) % p;
  else
    for (i=2; i<ly;  i++) x[i] = Fl_add(x[i], Fl_mul(c,y[i],p),p);
}

/* return a random polynomial in F_q[v], degree < d1 */
GEN
FqX_rand(long d1, long v, GEN T, GEN p)
{
  long i, d = d1+2, k = degpol(T), w = varn(T);
  GEN y = cgetg(d,t_POL); y[1] = evalsigne(1) | evalvarn(v);
  for (i=2; i<d; i++) gel(y,i) = random_FpX(k, w, p);
  (void)normalizepol_lg(y,d); return y;
}

#define set_irred(i) { if ((i)>ir) swap(t[i],t[ir]); ir++;}

long
FpX_split_Berlekamp(GEN *t, GEN p)
{
  GEN u = *t, a,b,po2,vker;
  long d, i, ir, L, la, lb, vu = varn(u), sv = evalvarn(vu);
  long l = lg(u);
  ulong ps = itou_or_0(p);
  if (ps==2)
    vker = F2x_Berlekamp_ker(ZX_to_F2x(u));
  else if (ps)
  {
    vker = Flx_Berlekamp_ker(ZX_to_Flx(u,ps),ps);
    vker = Flm_to_FlxV(vker, sv);
  }
  else
  {
    vker = FpX_Berlekamp_ker(u,p);
    vker = RgM_to_RgXV(vker,vu);
  }
  d = lg(vker)-1;
  po2 = shifti(p, -1); /* (p-1) / 2 */
  ir = 0;
  /* t[i] irreducible for i <= ir, still to be treated for i < L */
  for (L=1; L<d; )
  {
    GEN polt;
    if (ps==2)
    {
      long lb = nbits2prec(l-2);
      GEN pol = const_vecsmall(lb-1,0);
      pol[1] = sv;
      pol[2] = random_Fl(2); /*Assume vker[1]=1*/
      for (i=2; i<=d; i++)
        if (random_Fl(2))
          F2v_add_inplace(pol, gel(vker,i));
      (void)F2x_renormalize(pol,lb);
      polt = F2x_to_ZX(pol);
    } else if (ps) {
      GEN pol = const_vecsmall(l-2,0);
      pol[1] = sv;
      pol[2] = random_Fl(ps); /*Assume vker[1]=1*/
      for (i=2; i<=d; i++)
        Flx_addmul_inplace(pol, gel(vker,i), random_Fl(ps), ps);
      (void)Flx_renormalize(pol,l-1);

      polt = Flx_to_ZX(pol);
    } else {
      GEN pol = scalar_ZX_shallow(randomi(p), vu);
      for (i=2; i<=d; i++)
        pol = ZX_add(pol, ZX_Z_mul(gel(vker,i), randomi(p)));
      polt = FpX_red(pol,p);
    }
    for (i=ir; i<L && L<d; i++)
    {
      a = t[i]; la = degpol(a);
      if (la == 1) { set_irred(i); }
      else if (la == 2)
      {
        GEN r = FpX_quad_root(a,p,1);
        if (r)
        {
          t[i] = deg1pol_shallow(gen_1, subii(p,r), vu); r = otherroot(a,r,p);
          t[L] = deg1pol_shallow(gen_1, subii(p,r), vu); L++;
        }
        set_irred(i);
      }
      else
      {
        pari_sp av = avma;
        b = FpX_rem(polt, a, p);
        if (degpol(b) <= 0) { avma=av; continue; }
        b = ZX_Z_add(FpXQ_pow(b,po2, a,p), gen_m1);
        b = FpX_gcd(a,b, p); lb = degpol(b);
        if (lb && lb < la)
        {
          b = FpX_normalize(b, p);
          t[L] = FpX_div(a,b,p);
          t[i]= b; L++;
        }
        else avma = av;
      }
    }
  }
  return d;
}

GEN
FqX_gcd(GEN P,GEN Q,GEN T,GEN p) {return T? FpXQX_gcd(P,Q,T,p): FpX_gcd(P,Q,p);}
long
FqX_is_squarefree(GEN P, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z = FqX_gcd(P, FqX_deriv(P, T, p), T, p);
  avma = av;
  return degpol(z)==0;
}

long
FqX_split_Berlekamp(GEN *t, GEN q, GEN T, GEN p)
{
  GEN u = *t, a,b,qo2,vker,pol;
  long N = degpol(u), vu = varn(u), vT = varn(T), dT = degpol(T);
  long d, i, ir, L, la, lb;

  vker = FqX_Berlekamp_ker(u,T,q,p);
  vker = RgM_to_RgXV(vker,vu);
  d = lg(vker)-1;
  qo2 = shifti(q, -1); /* (q-1) / 2 */
  pol = cgetg(N+3,t_POL);
  ir = 0;
  /* t[i] irreducible for i < ir, still to be treated for i < L */
  for (L=1; L<d; )
  {
    GEN polt;
    gel(pol,2) = random_FpX(dT,vT,p);
    setlg(pol, signe(pol[2])? 3: 2);
    pol[1] = u[1];
    for (i=2; i<=d; i++)
      pol = gadd(pol, gmul(gel(vker,i), random_FpX(dT,vT,p)));
    polt = FpXQX_red(pol,T,p);
    for (i=ir; i<L && L<d; i++)
    {
      a = t[i]; la = degpol(a);
      if (la == 1) { set_irred(i); }
      else
      {
        pari_sp av = avma;
        b = FqX_rem(polt, a, T,p);
        if (!degpol(b)) { avma=av; continue; }
        b = FpXQYQ_pow(b,qo2, a,T,p);
        if (!degpol(b)) { avma=av; continue; }
        gel(b,2) = gadd(gel(b,2), gen_1);
        b = FqX_gcd(a,b, T,p); lb = degpol(b);
        if (lb && lb < la)
        {
          b = FqX_normalize(b, T,p);
          t[L] = FqX_div(a,b,T,p);
          t[i]= b; L++;
        }
        else avma = av;
      }
    }
  }
  return d;
}

static GEN
FpX_factor_i(GEN f, GEN pp)
{
  long e, N, nbfact, val, d = degpol(f);
  ulong p, k, j;
  GEN E, f2, g1, u, *t;

  if (d <= 2) return FpX_factor_2(f, pp, d);
  p = init_p(pp);

  /* to hold factors and exponents */
  t = (GEN*)cgetg(d+1,t_COL); E = cgetg(d+1,t_VECSMALL);
  val = ZX_valrem(f, &f);
  e = nbfact = 1;
  if (val) { t[1] = pol_x(varn(f)); E[1] = val; nbfact++; }

  for(;;)
  {
    f2 = FpX_gcd(f,ZX_deriv(f), pp);
    g1 = lg(f2)==3? f: FpX_div(f,f2,pp); /* is squarefree */
    k = 0;
    while (lg(g1)>3)
    {
      k++; if (p && !(k%p)) { k++; f2 = FpX_div(f2,g1,pp); }
      u = g1;
      if (!degpol(f2)) g1 = pol_1(0); /* only its degree (= 0) matters */
      else
      {
        g1 = FpX_gcd(f2,g1, pp);
        if (degpol(g1))
        {
          u = FpX_div( u,g1,pp);
          f2= FpX_div(f2,g1,pp);
        }
      }
      /* u is square-free (product of irred. of multiplicity e * k) */
      N = degpol(u);
      if (N > 0)
      {
        t[nbfact] = FpX_normalize(u,pp);
        d = (N==1)? 1: FpX_split_Berlekamp(t+nbfact, pp);
        for (j=0; j<(ulong)d; j++) E[nbfact+j] = e*k;
        nbfact += d;
      }
    }
    if (!p) break;
    j = degpol(f2); if (!j) break;
    if (j % p) pari_err(talker, "factmod: %lu is not prime", p);
    e *= p; f = RgX_deflate(f2, p);
  }
  setlg(t, nbfact);
  setlg(E, nbfact); return sort_factor_pol(mkvec2((GEN)t,E), cmpii);
}
GEN
FpX_factor(GEN f, GEN p)
{
  pari_sp av = avma;
  return gerepilecopy(av, FpX_factor_i(FpX_factmod_init(f, p), p));
}

GEN
factmod(GEN f, GEN p)
{
  pari_sp av = avma;
  long nbfact;
  long j;
  GEN y, u, v, z, t, E;

  if (!factmod_init(&f, p)) { avma = av; return trivfact(); }
  z = FpX_factor_i(f, p); t = gel(z,1); E = gel(z,2);
  y = cgetg(3,t_MAT); nbfact = lg(t);
  u = cgetg(nbfact,t_COL); gel(y,1) = u;
  v = cgetg(nbfact,t_COL); gel(y,2) = v;
  for (j=1; j<nbfact; j++)
  {
    gel(u,j) = FpX_to_mod(gel(t,j), p);
    gel(v,j) = utoi((ulong)E[j]);
  }
  return gerepileupto(av, y);
}
GEN
factormod0(GEN f, GEN p, long flag)
{
  switch(flag)
  {
    case 0: return factmod(f,p);
    case 1: return simplefactmod(f,p);
    default: pari_err(flagerr,"factormod");
  }
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                  CONVERSIONS RELATED TO p-ADICS                 */
/*                                                                 */
/*******************************************************************/
static GEN
Zp_to_Z(GEN x) {
  switch(typ(x))
  {
    case t_INT: break;
    case t_PADIC: x = gtrunc(x); break;
    default: pari_err(typeer,"QpX_to_ZX");
  }
  return x;
}
static GEN
ZpX_to_ZX(GEN f) {
  long i, l = lg(f);
  GEN F = cgetg(l, t_POL); F[1] = f[1];
  for (i=2; i<l; i++) gel(f,i) = Zp_to_Z(gel(f,i));
  return f;
}
/* make f suitable for [root|factor]padic */
static GEN
QpX_to_ZX(GEN f)
{
  GEN c = content(f);
  if (gequal0(c)) /*  O(p^n) can occur */
  {
    if (typ(c) != t_PADIC) pari_err(typeer,"QpX_to_ZX");
    c = powis(gel(c,2), valp(c));
  }
  f = RgX_Rg_div(f,c);
  return ZpX_to_ZX(f);
}

/* x in Z return x + O(pr), pr = p^r. Return gen_0 instead of zeropadic */
static GEN
Z_to_Zp(GEN x, GEN p, GEN pr, long r)
{
  GEN y;
  long v, sx = signe(x);

  if (!sx) return gen_0;
  v = Z_pvalrem(x,p,&x);
  r -= v; if (r <= 0) return gen_0;
  y = cgetg(5,t_PADIC);
  y[1] = evalprecp(r)|evalvalp(v);
  gel(y,2) = p;
  gel(y,3) = pr;
  gel(y,4) = modii(x,pr); return y;
}
static GEN
ZV_to_ZpV(GEN z, GEN p, long prec)
{
  long i, l = lg(z);
  GEN Z = cgetg(l, typ(z)), q = powiu(p, prec);
  for (i=1; i<lg(z); i++) gel(Z,i) = Z_to_Zp(gel(z,i),p,q,prec);
  return Z;
}
static GEN
ZX_to_ZpX(GEN z, GEN p, GEN q, long prec)
{
  long i, l = lg(z);
  GEN Z = cgetg(l, t_POL); Z[1] = z[1];
  for (i=2; i<lg(z); i++) gel(Z,i) = Z_to_Zp(gel(z,i),p,q,prec);
  return Z;
}
/* return (x + O(p^r)) normalized (multiply by a unit such that leading coeff
 * is a power of p), x in Z[X] (or Z_p[X]) */
static GEN
ZX_to_ZpX_normalized(GEN x, GEN p, GEN pr, long r)
{
  long i, lx = lg(x);
  GEN z, lead = leading_term(x);

  if (gequal1(lead)) return ZX_to_ZpX(x, p, pr, r);
  (void)Z_pvalrem(lead, p, &lead); lead = Fp_inv(lead, pr);
  z = cgetg(lx,t_POL);
  for (i=2; i < lx; i++) gel(z,i) = Z_to_Zp(mulii(lead,gel(x,i)),p,pr,r);
  z[1] = x[1]; return z;
}
static GEN
ZXV_to_ZpXQV(GEN z, GEN T, GEN p, long prec)
{
  long i, l = lg(z);
  GEN Z = cgetg(l, typ(z)), q = powiu(p, prec);
  T = ZX_copy(T);
  for (i=1; i<lg(z); i++) gel(Z,i) = mkpolmod(ZX_to_ZpX(gel(z,i),p,q,prec),T);
  return Z;
}

static GEN
QpXQ_to_ZXY(GEN f)
{
  GEN c = content(f);
  long i, l = lg(f);
  if (gequal0(c)) /*  O(p^n) can occur */
  {
    if (typ(c) != t_PADIC) pari_err(typeer,"QpXQ_to_ZXY");
    c = powis(gel(c,2), valp(c));
  }
  f = RgX_Rg_div(f,c);
  for (i=2; i<l; i++)
  {
    GEN t = gel(f,i);
    switch(typ(t))
    {
      case t_POL: t = ZpX_to_ZX(t); break;
      default: t = Zp_to_Z(t); break;
    }
    gel(f,i) = t;
  }
  return f;
}

/*******************************************************************/
/*                                                                 */
/*                         p-ADIC ROOTS                            */
/*                                                                 */
/*******************************************************************/

/* f primitive ZX, squarefree, leading term prime to p. a in Z such that
 * f(a) = 0 mod p. Return p-adic roots of f equal to a mod p, in
 * precision >= prec */
static GEN
ZX_Zp_root(GEN f, GEN a, GEN p, long prec)
{
  GEN z, R, a0 = modii(a, p);
  long i, j, k;

  if (signe(FpX_eval(FpX_deriv(f, p), a0, p)))
  { /* simple zero mod p, go all the way to p^prec */
    if (prec > 1) a0 = ZpX_liftroot(f, a0, p, prec);
    return mkcol(a0);
  }

  f = poleval(f, deg1pol_shallow(p, a, varn(f)));
  f = ZX_Z_divexact(f, powiu(p,ggval(f, p)));
  z = cgetg(degpol(f)+1,t_COL);

  R = FpX_roots(f, p);
  for (j=i=1; i<lg(R); i++)
  {
    GEN u = ZX_Zp_root(f, gel(R,i), p, prec-1);
    for (k=1; k<lg(u); k++) gel(z,j++) = addii(a, mulii(p, gel(u,k)));
  }
  setlg(z,j); return z;
}

/* a t_PADIC, return vector of p-adic roots of f equal to a (mod p)
 * We assume 1) f(a) = 0 mod p (mod 4 if p=2).
 *           2) leading coeff prime to p. */
GEN
Zp_appr(GEN f, GEN a)
{
  pari_sp av = avma;
  long prec;
  GEN z, p;
  if (typ(f) != t_POL) pari_err(notpoler,"Zp_appr");
  if (typ(a) != t_PADIC) pari_err(typeer,"Zp_appr");
  p = gel(a,2); prec = gequal0(a)? valp(a): precp(a);
  f = QpX_to_ZX(f);
  if (degpol(f) <= 0) pari_err(constpoler,"Zp_appr");
  (void)ZX_gcd_all(f, ZX_deriv(f), &f);
  z = ZX_Zp_root(f, gtrunc(a), p, prec);
  return gerepilecopy(av, ZV_to_ZpV(z, p, prec));
}
/* vector of p-adic roots of the ZX f, leading term prime to p */
static GEN
ZX_Zp_roots(GEN f, GEN p, long prec)
{
  GEN y, z, rac;
  long lx, i, j, k;

  (void)ZX_gcd_all(f, ZX_deriv(f), &f);
  rac = FpX_roots(f, p);
  lx = lg(rac); if (lx == 1) return rac;
  y = cgetg(degpol(f)+1,t_COL);
  for (j=i=1; i<lx; i++)
  {
    z = ZX_Zp_root(f, gel(rac,i), p, prec);
    for (k=1; k<lg(z); k++,j++) gel(y,j) = gel(z,k);
  }
  setlg(y,j); return ZV_to_ZpV(y, p, prec);
}

/* f a ZX */
static GEN
pnormalize(GEN f, GEN p, long prec, long n, GEN *plead, long *pprec, int *prev)
{
  *plead = leading_term(f);
  *pprec = prec;
  *prev = 0;
  if (!is_pm1(*plead))
  {
    long v = Z_pval(*plead,p), v1 = Z_pval(constant_term(f),p);
    if (v1 < v)
    {
      *prev = 1; f = RgX_recip_shallow(f);
     /* beware loss of precision from lc(factor), whose valuation is <= v */
      *pprec += v; v = v1;
    }
    *pprec += v * n;
  }
  return ZX_to_monic(f, plead);
}

/* return p-adic roots of f, precision prec */
GEN
rootpadic(GEN f, GEN p, long prec)
{
  pari_sp av = avma;
  GEN lead,y;
  long PREC,i,k;
  int reverse;

  if (typ(p)!=t_INT) pari_err(typeer,"rootpadic");
  if (typ(f)!=t_POL) pari_err(notpoler,"rootpadic");
  if (gequal0(f)) pari_err(zeropoler,"rootpadic");
  if (prec <= 0) pari_err(talker,"non-positive precision in rootpadic");
  f = QpX_to_ZX(f);
  f = pnormalize(f, p, prec, 1, &lead, &PREC, &reverse);
  y = ZX_Zp_roots(f,p,PREC);
  k = lg(y);
  if (lead != gen_1)
    for (i=1; i<k; i++) gel(y,i) = gdiv(gel(y,i), lead);
  if (reverse)
    for (i=1; i<k; i++) gel(y,i) = ginv(gel(y,i));
  return gerepilecopy(av, y);
}
/* p is prime
 * f in a ZX, with leading term prime to p.
 * f must have no multiple roots mod p.
 *
 * return p-adics roots of f with prec p^e, as integers (implicitly mod p^e) */
GEN
rootpadicfast(GEN f, GEN p, long e)
{
  pari_sp av = avma;
  GEN y, S = FpX_roots(f, p); /*no multiplicity*/
  if (lg(S)==1) { avma = av; return cgetg(1,t_COL); }
  S = gclone(S); avma = av;
  y = ZpX_liftroots(f,S,p,e);
  gunclone(S); return y;
}
/**************************************************************************/

static void
scalar_getprec(GEN x, long *pprec, GEN *pp)
{
  if (typ(x)==t_PADIC)
  {
    long e = valp(x); if (signe(x[4])) e += precp(x);
    if (e < *pprec) *pprec = e;
    if (*pp && !equalii(*pp, gel(x,2))) pari_err(consister,"apprpadic");
    *pp = gel(x,2);
  }
}
static void
getprec(GEN x, long *pprec, GEN *pp)
{
  long i;
  if (typ(x) != t_POL) scalar_getprec(x, pprec, pp);
  else
    for (i = lg(x)-1; i>1; i--) scalar_getprec(gel(x,i), pprec, pp);
}

static GEN FqX_roots_i(GEN f, GEN T, GEN p);
static GEN
ZXY_ZpQ_root(GEN f, GEN a, GEN T, GEN p, long prec)
{
  GEN z, R;
  long i, j, k, lR;
  if (signe(FqX_eval(FqX_deriv(f,T,p), a, T,p)))
  { /* simple zero mod (T,p), go all the way to p^prec */
    if (prec > 1) a = ZpXQX_liftroot(f, a, T, p, prec);
    return mkcol(a);
  }
  /* TODO: need RgX_RgYQX_compo ? */
  f = lift_intern(poleval(f, deg1pol_shallow(p, mkpolmod(a,T), varn(f))));
  f = gdiv(f, powiu(p, ggval(f,p)));
  z = cgetg(degpol(f)+1,t_COL);
  R = FqX_roots_i(FqX_red(f,T,p), T, p); lR = lg(R);
  for(j=i=1; i<lR; i++)
  {
    GEN u = ZXY_ZpQ_root(f, gel(R,i), T, p, prec-1);
    for (k=1; k<lg(u); k++) gel(z,j++) = gadd(a, gmul(p, gel(u,k)));
  }
  setlg(z,j); return z;
}

/* a belongs to finite extension of Q_p, return all roots of f equal to a
 * mod p. We assume f(a) = 0 (mod p) [mod 4 if p=2] */
GEN
padicappr(GEN f, GEN a)
{
  GEN p, z, T;
  long prec;
  pari_sp av = avma;

  switch(typ(a)) {
    case t_PADIC: return Zp_appr(f,a);
    case t_POLMOD: break;
    default: pari_err(typeer,"padicappr");
  }
  if (typ(f)!=t_POL) pari_err(notpoler,"padicappr");
  if (gequal0(f)) pari_err(zeropoler,"padicappr");
  z = RgX_gcd(f, RgX_deriv(f));
  if (degpol(z) > 0) f = RgX_div(f,z);
  T = gel(a,1); a = gel(a,2);
  p = NULL; prec = LONG_MAX;
  getprec(a, &prec, &p);
  getprec(T, &prec, &p); if (!p) pari_err(typeer,"padicappr");
  f = QpXQ_to_ZXY(lift_intern(f));
  a = QpX_to_ZX(a);
  T = QpX_to_ZX(T);
  z = ZXY_ZpQ_root(f, a, T, p, prec);
  return gerepilecopy(av, ZXV_to_ZpXQV(z, T, p, prec));
}

/*******************************************************************/
/*                                                                 */
/*                      FACTORIZATION in Zp[X]                     */
/*                                                                 */
/*******************************************************************/

int
cmp_padic(GEN x, GEN y)
{
  long vx, vy;
  if (x == gen_0) return -1;
  if (y == gen_0) return  1;
  vx = valp(x);
  vy = valp(y);
  if (vx < vy) return  1;
  if (vx > vy) return -1;
  return cmpii(gel(x,4), gel(y,4));
}

/*******************************/
/*   Using Buchmann--Lenstra   */
/*******************************/

/* factor T = nf_get_pol(nf) in Zp to precision k */
static GEN
padicff2(GEN nf,GEN p,long k)
{
  GEN z, mat, D, U, fa, pk, dec_p, Ui, mulx;
  long i, l;

  mulx = zk_scalar_or_multable(nf, gmael(nf,8,2)); /* mul by (x mod T) */
  dec_p = idealprimedec(nf,p);
  fa = cgetg_copy(dec_p, &l);
  D = NULL; /* -Wall */
  for (i=1; i<l; i++)
  {
    GEN P = gel(dec_p,i);
    long e = pr_get_e(P), ef = e * pr_get_f(P);
    D = ZM_snfall_i(idealpows(nf,P, k*e), &U, NULL, 1);
    Ui= ZM_inv(U, gen_1); setlg(Ui, ef+1); /* cf ZM_snf_group */
    U = rowslice(U, 1, ef);
    mat = ZM_mul(U, ZM_mul(mulx, Ui));
    gel(fa,i) = ZM_charpoly(mat);
  }
  pk = gel(D,1); /* = p^k */
  z = cgetg(l,t_COL); pk = icopy(pk);
  for (i=1; i<l; i++)
    gel(z,i) = ZX_to_ZpX_normalized(gel(fa,i),p,pk,k);
  return z;
}

static GEN
padicff(GEN x,GEN p,long pr)
{
  pari_sp av = avma;
  GEN q, nf, g, e;
  long v = Z_pvalrem(absi(ZX_disc(x)), p, &q);
  nfmaxord_t S;

  if (is_pm1(q)) {
    e = mkcol(utoi(v));
    g = mkcol(p);
  } else {
    e = mkcol2(utoi(v), gen_1);
    g = mkcol2(p, q);
  }
  nfmaxord(&S, x, 0, mkmat2(g,e));

  nf = cgetg(10,t_VEC);
  gel(nf,1) = x;
  gel(nf,3) = S.dK;
  gel(nf,4) = dvdii(S.index, p)? p: gen_1;
  gel(nf,2) = gel(nf,5) = gel(nf,6) = gen_0;
  nf_set_multable(nf, S.basis, NULL);
  return gerepileupto(av, padicff2(nf,p,pr));
}

static GEN
padic_trivfact(GEN x, GEN p, long r)
{
  return mkmat2(mkcol(ZX_to_ZpX_normalized(x, p, powiu(p,r), r)),
                mkcol(gen_1));
}

static GEN
factorpadic2(GEN f, GEN p, long prec)
{
  pari_sp av = avma;
  GEN fa,ex,y;
  long n,i,l;

  if (typ(f)!=t_POL) pari_err(notpoler,"factorpadic");
  if (typ(p)!=t_INT) pari_err(arither1);
  if (gequal0(f)) pari_err(zeropoler,"factorpadic");
  if (prec <= 0) pari_err(talker,"non-positive precision in factorpadic");

  n = degpol(f);
  if (n==0) return trivfact();
  f = QpX_to_ZX(f);
  if (n==1) return gerepilecopy(av, padic_trivfact(f,p,prec));
  if (!gequal1(leading_term(f)))
    pari_err(impl,"factorpadic2 for non-monic polynomial");

  fa = ZX_squff(f, &ex);
  l = lg(fa); n = 0;
  for (i=1; i<l; i++)
  {
    gel(fa,i) = padicff(gel(fa,i),p,prec);
    n += lg(fa[i])-1;
  }

  y = fact_from_DDF(fa,ex,n);
  return gerepileupto(av, sort_factor_pol(y, cmp_padic));
}

/***********************/
/*   Using ROUND 4     */
/***********************/
static int
expo_is_squarefree(GEN e)
{
  long i, l = lg(e);
  for (i=1; i<l; i++)
    if (e[i] != 1) return 0;
  return 1;
}

/* assume f a ZX with leading_term 1, degree > 0 */
GEN
ZX_monic_factorpadic(GEN f, GEN p, long prec)
{
  GEN w, poly, p1, p2, ex, P, E;
  long n=degpol(f), i, k, j;

  if (n==1) return mkmat2(mkcol(f), mkcol(gen_1));

  poly = ZX_squff(f,&ex);
  P = cgetg(n+1,t_COL);
  E = cgetg(n+1,t_COL); n = lg(poly);
  for (j=i=1; i<n; i++)
  {
    pari_sp av1 = avma;
    GEN fx = gel(poly,i), fa = FpX_factor(fx,p);
    w = gel(fa,1);
    if (expo_is_squarefree(gel(fa,2)))
    { /* no repeated factors: Hensel lift */
      p1 = ZpX_liftfact(fx, w, NULL, p, prec, powiu(p,prec));
      p2 = utoipos(ex[i]);
      for (k=1; k<lg(p1); k++,j++)
      {
        P[j] = p1[k];
        gel(E,j) = p2;
      }
      continue;
    }
    /* use Round 4 */
    p2 = maxord_i(p, fx, ZpX_disc_val(fx,p), w, prec);
    if (p2)
    {
      p2 = gerepilecopy(av1,p2);
      p1 = gel(p2,1);
      p2 = gel(p2,2);
      for (k=1; k<lg(p1); k++,j++)
      {
        P[j] = p1[k];
        gel(E,j) = muliu(gel(p2,k),ex[i]);
      }
    }
    else
    {
      avma = av1;
      gel(P,j) = fx;
      gel(E,j) = utoipos(ex[i]); j++;
    }
  }
  setlg(P,j);
  setlg(E,j); return mkmat2(P, E);
}

GEN
factorpadic(GEN f,GEN p,long prec)
{
  pari_sp av = avma;
  GEN y, P, ppow, lead, lt;
  long i, l, pr, n = degpol(f);
  int reverse = 0;

  if (typ(f)!=t_POL) pari_err(notpoler,"factorpadic");
  if (typ(p)!=t_INT) pari_err(arither1);
  if (gequal0(f)) pari_err(zeropoler,"factorpadic");
  if (prec <= 0) pari_err(talker,"non-positive precision in factorpadic");
  if (n == 0) return trivfact();

  f = QpX_to_ZX(f); (void)Z_pvalrem(leading_term(f), p, &lt);
  f = pnormalize(f, p, prec, n-1, &lead, &pr, &reverse);
  y = ZX_monic_factorpadic(f, p, pr);
  P = gel(y,1); l = lg(P);
  if (lead != gen_1)
    for (i=1; i<l; i++) gel(P,i) = Q_primpart( RgX_unscale(gel(P,i), lead) );
  ppow = powiu(p,prec);
  for (i=1; i<l; i++)
  {
    GEN t = gel(P,i);
    if (reverse) t = normalizepol(RgX_recip_shallow(t));
    gel(P,i) = ZX_to_ZpX_normalized(t,p,ppow,prec);
  }
  if (!gequal1(lt)) gel(P,1) = gmul(gel(P,1), lt);
  return gerepilecopy(av, sort_factor_pol(y, cmp_padic));
}

GEN
factorpadic0(GEN f,GEN p,long r,long flag)
{
  switch(flag)
  {
     case 0: return factorpadic(f,p,r);
     case 1: return factorpadic2(f,p,r);
     default: pari_err(flagerr,"factorpadic");
  }
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                     FACTORIZATION IN F_q                        */
/*                                                                 */
/*******************************************************************/
static GEN spec_FqXQ_pow(GEN x, GEN S, GEN T, GEN p);

static GEN
to_Fq(GEN x, GEN T, GEN p)
{
  long i, lx, tx = typ(x);
  GEN y;

  if (tx == t_INT)
    y = mkintmod(x,p);
  else
  {
    if (tx != t_POL) pari_err(typeer,"to_Fq");
    lx = lg(x);
    y = cgetg(lx,t_POL); y[1] = x[1];
    for (i=2; i<lx; i++) gel(y,i) = mkintmod(gel(x,i), p);
  }
  return mkpolmod(y, T);
}

static GEN
to_Fq_pol(GEN x, GEN T, GEN p)
{
  long i, lx = lg(x);
  for (i=2; i<lx; i++) gel(x,i) = to_Fq(gel(x,i),T,p);
  return x;
}

static GEN
to_Fq_fact(GEN P, GEN E, GEN T, GEN p, pari_sp av)
{
  GEN y, u, v;
  long j, l = lg(P), nbf = lg(P);

  u = cgetg(nbf,t_COL);
  v = cgetg(nbf,t_COL);
  for (j=1; j<l; j++)
  {
    gel(u,j) = simplify_shallow(gel(P,j)); /* may contain pols of degree 0 */
    gel(v,j) = utoi((ulong)E[j]);
  }
  y = gerepilecopy(av, mkmat2(u, v));
  u = gel(y,1);
  p = icopy(p);
  T = FpX_to_mod(T, p);
  for (j=1; j<nbf; j++) gel(u,j) = to_Fq_pol(gel(u,j), T,p);
  return y;
}
static GEN
to_Fq_vec(GEN P, GEN T, GEN p, pari_sp av)
{
  GEN u;
  long j, l = lg(P), nbf = lg(P);

  u = cgetg(nbf,t_VEC);
  for (j=1; j<l; j++)
    gel(u,j) = simplify_shallow(gel(P,j)); /* may contain pols of degree 0 */
  u = gerepilecopy(av, u);
  p = icopy(p);
  T = FpX_to_mod(T, p);
  for (j=1; j<nbf; j++) gel(u,j) = to_Fq(gel(u,j), T,p);
  return u;
}

/* split into r factors of degree d */
static void
FqX_split(GEN *t, long d, GEN q, GEN S, GEN T, GEN p)
{
  long l, v, is2, cnt, dt = degpol(*t), dT = degpol(T);
  pari_sp av;
  GEN w,w0;

  if (dt == d) return;
  v = varn(*t);
  if (DEBUGLEVEL > 6) (void)timer2();
  av = avma; is2 = equaliu(p, 2);
  for(cnt = 1;;cnt++, avma = av)
  { /* splits *t with probability ~ 1 - 2^(1-r) */
    w = w0 = FqX_rand(dt,v, T,p);
    if (degpol(w) <= 0) continue;
    for (l=1; l<d; l++) /* sum_{0<i<d} w^(q^i), result in (F_q)^r */
      w = gadd(w0, spec_FqXQ_pow(w, S, T, p));
    w = FpXQX_red(w, T,p);
    if (is2)
    {
      w0 = w;
      for (l=1; l<dT; l++) /* sum_{0<i<k} w^(2^i), result in (F_2)^r */
      {
        w = FqX_rem(FqX_sqr(w,T,p), *t, T,p);
        w = FpXX_red(gadd(w0,w), p);
      }
    }
    else
    {
      w = FpXQYQ_pow(w, shifti(q,-1), *t, T, p);
      /* w in {-1,0,1}^r */
      if (degpol(w) <= 0) continue;
      gel(w,2) = gadd(gel(w,2), gen_1);
    }
    w = FqX_gcd(*t,w, T,p); l = degpol(w);
    if (l && l != dt) break;
  }
  w = gerepileupto(av,w);
  if (DEBUGLEVEL > 6)
    fprintferr("[FqX_split] splitting time: %ld (%ld trials)\n",timer2(),cnt);
  l /= d; t[l] = FqX_div(*t,w, T,p); *t = w;
  FqX_split(t+l,d,q,S,T,p);
  FqX_split(t  ,d,q,S,T,p);
}

/*******************************************************************/
/*                                                                 */
/*                  FACTOR USING TRAGER'S TRICK                    */
/*                                                                 */
/*******************************************************************/
static GEN
FqX_frob_deflate(GEN f, GEN T, GEN p)
{
  GEN F = RgX_deflate(f, itos(p)), frobinv = powiu(p, degpol(T)-1);
  long i, l = lg(F);
  for (i=2; i<l; i++) gel(F,i) = Fq_pow(gel(F,i), frobinv, T,p);
  return F;
}
/* Factor _sqfree_ polynomial a on the finite field Fp[X]/(T) */
static GEN
FqX_split_Trager(GEN A, GEN T, GEN p)
{
  GEN x0, P, u, fa, n;
  long lx, i, k;

  u = A;
  n = NULL;
  for (k = 0; cmpui(k, p) < 0; k++)
  {
    GEN U = poleval(u, deg1pol_shallow(gen_1, gmulsg(k, pol_x(varn(T))), varn(A)));
    n = FpX_FpXY_resultant(T, U, p);
    if (FpX_is_squarefree(n, p)) break;
    n = NULL;
  }
  if (!n) return NULL;
  if (DEBUGLEVEL>4) fprintferr("FqX_split_Trager: choosing k = %ld\n",k);
  /* n guaranteed to be squarefree */
  fa = FpX_factor(n, p); fa = gel(fa,1); lx = lg(fa);
  if (lx == 2) return mkcol(A); /* P^k, P irreducible */

  P = cgetg(lx,t_COL);
  x0 = gadd(pol_x(varn(A)), gmulsg(-k, mkpolmod(pol_x(varn(T)), T)));
  for (i=lx-1; i>1; i--)
  {
    GEN f = gel(fa,i), F = lift_intern(poleval(f, x0));
    F = FqX_gcd(u, F, T, p);
    if (typ(F) != t_POL || degpol(F) == 0)
      pari_err(talker,"reducible modulus in factornf");
    u = FqX_div(u, F, T, p);
    gel(P,i) = F;
  }
  gel(P,1) = u; return P;
}

/* assume n = deg(u) > 1, X over FqX */
/* return S = [ X^q, X^2q, ... X^(n-1)q ] mod u (in Fq[X]) in Kronecker form */
static GEN
init_spec_FqXQ_pow(GEN X, GEN q, GEN u, GEN T, GEN p)
{
  long i, n = degpol(u);
  GEN x, S = cgetg(n, t_VEC);

  if (n == 1) return S;
  x = FpXQYQ_pow(X, q, u, T, p);
  gel(S,1) = x;
  if ((degpol(x)<<1) < degpol(T)) {
    for (i=2; i < n; i++)
      gel(S,i) = FqX_rem(FqX_mul(gel(S,i-1), x, T,p), u, T,p);
  } else {
    for (i=2; i < n; i++)
      gel(S,i) = (i&1)? FqX_rem(FqX_mul(gel(S,i-1), x, T,p), u, T,p)
                      : FqX_rem(FqX_sqr(gel(S,i>>1), T,p), u, T,p);
  }
  for (i=1; i < n; i++) gel(S,i) = mod_to_Kronecker(gel(S,i), T);
  return S;
}

/* compute x^q, x an FqX. S is as above (vector of FpX, Kronecker forms) */
static GEN
spec_FqXQ_pow(GEN x, GEN S, GEN T, GEN p)
{
  pari_sp av = avma, lim = stack_lim(av, 1);
  GEN x0 = x+2, z = gel(x0,0);
  long i, dx = degpol(x);

  for (i = 1; i <= dx; i++)
  { /* NB: variables are inconsistant in there. Coefficients of x must be
     * treated as if they had the same variable as S */
    GEN d = gel(S,i), c = gel(x0,i);
    if (!signe(c)) continue;
    if (typ(c) == t_INT)
    {
      if (is_pm1(c)) { if (signe(c) < 0) d = FpX_neg(d,p); }
      else d = FpX_Fp_mul(d, c, p);
    }
    else /* FpX */
    {
      if (!degpol(c)) d = FpX_Fp_mul(d, gel(c,2), p);
      else d = FpX_mul(d, c, p);
    }
    z = FpX_add(z, d, p);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"spec_FqXQ_pow");
      z = gerepileupto(av, z);
    }
  }
  z[1] = x[1]; /* make sure variable number is sane */
  z = Kronecker_to_FpXQX(z, T, p);
  return gerepileupto(av, z);
}

static long
isabsolutepol(GEN f)
{
  long i, l = lg(f);
  for(i=2; i<l; i++)
  {
    GEN c = gel(f,i);
    if (typ(c) == t_POL && degpol(c) > 0) return 0;
  }
  return 1;
}

typedef struct {
  GEN S, L, Xq;
  GEN q;    /* p^deg(T) */
  GEN p, T; /* split mod (p, T(X)) */
} FqX_split_t;

static void
add(GEN z, GEN g, long d) { vectrunc_append(z, mkvec2(utoipos(d), g)); }
/* return number of roots of u; assume deg u >= 0 */
long
FqX_split_deg1(GEN *pz, GEN u, GEN q, GEN T, GEN p)
{
  long dg, N = degpol(u);
  GEN v, S, g, X, z = vectrunc_init(N+1);

  *pz = z;
  if (N == 0) return 0;
  if (N == 1) return 1;
  v = X = pol_x(varn(u));
  S = init_spec_FqXQ_pow(X, q, u, T, p);
  vectrunc_append(z, S);
  v = spec_FqXQ_pow(v, S, T, p);
  g = FqX_gcd(gsub(v,X),u, T,p);
  dg = degpol(g);
  if (dg > 0) add(z, g, dg);
  return dg;
}

/* return number of factors; z not properly initialized if deg(u) <= 1 */
long
FqX_split_by_degree(GEN *pz, GEN u, GEN q, GEN T, GEN p)
{
  long nb = 0, d, dg, N = degpol(u);
  GEN v, S, g, X, z = vectrunc_init(N+1);

  *pz = z;
  if (N <= 1) return 1;
  v = X = pol_x(varn(u));
  S = init_spec_FqXQ_pow(X, q, u, T, p);
  vectrunc_append(z, S);
  for (d=1; d <= N>>1; d++)
  {
    v = spec_FqXQ_pow(v, S, T, p);
    g = FqX_gcd(gsub(v,X),u, T,p);
    dg = degpol(g); if (dg <= 0) continue;
    /* all factors of g have degree d */
    add(z, g, dg / d); nb += dg / d;
    N -= dg;
    if (N)
    {
      u = FqX_div(u,g, T,p);
      v = FqX_rem(v,u, T,p);
    }
  }
  if (N) { add(z, u, 1); nb++; }
  return nb;
}

/* see roots_from_deg1() */
static GEN
FqXV_roots_from_deg1(GEN x, GEN T, GEN p)
{
  long i,l = lg(x);
  GEN r = cgetg(l,t_VEC);
  for (i=1; i<l; i++) { GEN P = gel(x,i); gel(r,i) = Fq_neg(gel(P,2), T, p); }
  return r;
}

static GEN
FqX_split_equal(GEN L, GEN S, GEN T, GEN p)
{
  long n = itos(gel(L,1));
  GEN u = gel(L,2), z = cgetg(n + 1, t_VEC);
  gel(z,1) = u;
  FqX_split((GEN*)(z+1), degpol(u) / n, powiu(p, degpol(T)), S, T, p);
  return z;
}
GEN
FqX_split_roots(GEN z, GEN T, GEN p, GEN pol)
{
  GEN S = gel(z,1), L = gel(z,2), rep = FqX_split_equal(L, S, T, p);
  if (pol) rep = shallowconcat(rep, FqX_div(pol, gel(L,2), T,p));
  return rep;
}
GEN
FqX_split_all(GEN z, GEN T, GEN p)
{
  GEN S = gel(z,1), rep = cgetg(1, t_VEC);
  long i, l = lg(z);
  for (i = 2; i < l; i++)
    rep = shallowconcat(rep, FqX_split_equal(gel(z,i), S, T, p));
  return rep;
}

/* not memory-clean, as FpX_factorff_i, returning only linear factors */
static GEN
FpX_rootsff_i(GEN P, GEN p, GEN T)
{
  GEN V, F = gel(FpX_factor(P,p), 1);
  long i, lfact = 1, nmax = lgpol(P), n = lg(F), dT = degpol(T);

  V = cgetg(nmax,t_VEC);
  for(i=1;i<n;i++)
  {
    GEN R, Fi = gel(F,i);
    long di = degpol(Fi), j, r;
    if (dT % di) continue;
    R = FpX_factorff_irred(gel(F,i),T,p);
    r = lg(R);
    for (j=1; j<r; j++,lfact++)
      gel(V,lfact) = Fq_neg(gmael(R,j, 2), T, p);
  }
  setlg(V,lfact);
  gen_sort_inplace(V, (void*) &cmp_RgX, &cmp_nodata, NULL);
  return V;
}
GEN
FpX_rootsff(GEN P, GEN p, GEN T)
{
  pari_sp av = avma;
  return gerepilecopy(av, FpX_rootsff_i(P, p, T));
}

static GEN
FqX_roots_i(GEN f, GEN T, GEN p)
{
  GEN R;
  f = FqX_normalize(f, T, p);
  if (!signe(f)) pari_err(zeropoler,"FqX_roots");
  if (isabsolutepol(f)) return FpX_rootsff_i(simplify_shallow(f), p, T);
  switch( FqX_split_deg1(&R, f, powiu(p, degpol(T)), T, p) )
  {
  case 0: return cgetg(1, t_VEC);
  case 1: if (lg(R) == 1) { R = mkvec(f); break; }
            /* fall through */
  default: R = FqX_split_roots(R, T, p, NULL);
  }
  R = FqXV_roots_from_deg1(R, T, p);
  gen_sort_inplace(R, (void*) &cmp_RgX, &cmp_nodata, NULL);
  return R;
}
GEN
FqX_roots(GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  if (!T) return FpX_roots(x, p);
  return gerepileupto(av, FqX_roots_i(x, T, p));
}

static long
FqX_sqf_split(GEN *t0, GEN q, GEN T, GEN p)
{
  GEN *t = t0, u = *t, v, S, g, X;
  long d, dg, N = degpol(u);

  if (N == 1) return 1;
  v = X = pol_x(varn(u));
  S = init_spec_FqXQ_pow(X, q, u, T, p);
  for (d=1; d <= N>>1; d++)
  {
    v = spec_FqXQ_pow(v, S, T, p);
    g = FqX_gcd(gsub(v,X),u, T,p);
    dg = degpol(g); if (dg <= 0) continue;

    /* all factors of g have degree d */
    *t = g;
    FqX_split(t, d, q, S, T, p);
    t += dg / d;
    N -= dg;
    if (N)
    {
      u = FqX_div(u,g, T,p);
      v = FqX_rem(v,u, T,p);
    }
  }
  if (N) *t++ = u;
  return t - t0;
}

/* not memory-clean */
static GEN
FpX_factorff_i(GEN P, GEN p, GEN T)
{
  GEN V, E, F = FpX_factor(P,p);
  long i, lfact = 1, nmax = lgpol(P), n = lg(gel(F,1));

  V = cgetg(nmax,t_VEC);
  E = cgetg(nmax,t_VECSMALL);
  for(i=1;i<n;i++)
  {
    GEN R = FpX_factorff_irred(gmael(F,1,i),T,p), e = gmael(F,2,i);
    long j, r = lg(R);
    for (j=1; j<r; j++,lfact++)
    {
      gel(V,lfact) = gel(R,j);
      gel(E,lfact) = e;
    }
  }
  setlg(V,lfact);
  setlg(E,lfact); return sort_factor_pol(mkvec2(V,E), cmp_RgX);
}
GEN
FpX_factorff(GEN P, GEN p, GEN T)
{
  pari_sp av = avma;
  return gerepilecopy(av, FpX_factorff_i(P, p, T));
}

static GEN
FqX_factor_i(GEN f, GEN T, GEN p)
{
  long pg, j, k, d, e, N, nbfact, pk;
  GEN E, f2, f3, df1, df2, g1, u, q, *t;

  if (!signe(f)) pari_err(zeropoler,"FqX_factor");
  d = degpol(f); if (!d) return trivfact();
  T = FpX_normalize(T, p);
  f = FqX_normalize(f, T, p);
  if (isabsolutepol(f)) return FpX_factorff_i(simplify_shallow(f), p, T);

  pg = itos_or_0(p);
  df2  = NULL; /* gcc -Wall */
  t = (GEN*)cgetg(d+1,t_VEC);
  E = cgetg(d+1, t_VECSMALL);

  q = powiu(p, degpol(T));
  e = nbfact = 1;
  pk = 1;
  f3 = NULL;
  df1 = FqX_deriv(f, T, p);
  for(;;)
  {
    long nb0;
    while (!signe(df1))
    { /* needs d >= p: pg = 0 can't happen  */
      pk *= pg; e = pk;
      f = FqX_frob_deflate(f, T, p);
      df1 = FqX_deriv(f, T, p); f3 = NULL;
    }
    f2 = f3? f3: FqX_gcd(f,df1, T,p);
    if (!degpol(f2)) u = f;
    else
    {
      g1 = FqX_div(f,f2, T,p);
      df2 = FqX_deriv(f2, T,p);
      if (gequal0(df2)) { u = g1; f3 = f2; }
      else
      {
        f3 = FqX_gcd(f2,df2, T,p);
        u = degpol(f3)? FqX_div(f2, f3, T,p): f2;
        u = FqX_div(g1, u, T,p);
      }
    }
    /* u is square-free (product of irreducibles of multiplicity e) */
    N = degpol(u);
    if (N) {
      nb0 = nbfact;
      t[nbfact] = FqX_normalize(u, T,p);
      if (N == 1) nbfact++;
      else
      {
#if 0
        nbfact += FqX_split_Berlekamp(t+nbfact, q, T, p);
#else
        GEN P = FqX_split_Trager(t[nbfact], T, p);
        if (P) {
          for (j = 1; j < lg(P); j++) t[nbfact++] = gel(P,j);
        } else {
          if (DEBUGLEVEL) pari_warn(warner, "FqX_split_Trager failed!");
          nbfact += FqX_sqf_split(t+nbfact, q, T, p);
        }
#endif
      }
      for (j = nb0; j < nbfact; j++) E[j] = e;
    }

    if (!degpol(f2)) break;
    f = f2; df1 = df2; e += pk;
  }

  for (j=1; j<nbfact; j++)
  {
    t[j] = FqX_normalize(gel(t,j), T,p);
    for (k=1; k<j; k++)
      if (RgX_equal(gel(t,j), gel(t,k)))
      {
        E[k] += E[j]; nbfact--;
        E[j] = E[nbfact];
        gel(t,j) = gel(t,nbfact); break;
      }
  }
  setlg(t, nbfact);
  setlg(E, nbfact); return sort_factor_pol(mkvec2((GEN)t, E), cmp_RgX);
}

static void
ffcheck(pari_sp *av, GEN *f, GEN *T, GEN p)
{
  long v;
  if (typ(*T)!=t_POL || typ(*f)!=t_POL || typ(p)!=t_INT)
    pari_err(typeer,"factorff");
  v = varn(*T);
  if (varncmp(v, varn(*f)) <= 0)
    pari_err(talker,"polynomial variable must have higher priority in factorff");
  *T = RgX_to_FpX(*T, p); *av = avma;
  *f = RgX_to_FqX(*f, *T,p);
}
GEN
factorff(GEN f, GEN p, GEN T)
{
  pari_sp av;
  GEN z;
  if (!p || !T)
  {
    long pa, t;
    if (typ(f) != t_POL) pari_err(typeer, "factorff");
    T = p = NULL;
    t = RgX_type(f, &p, &T, &pa);
    if (t != t_FFELT) pari_err(typeer, "factorff");
    return FFX_factor(f,T);
  }
  ffcheck(&av, &f, &T, p); z = FqX_factor_i(f, T, p);
  return to_Fq_fact(gel(z,1),gel(z,2), T,p, av);
}
GEN
polrootsff(GEN f, GEN p, GEN T)
{
  pari_sp av;
  GEN z;
  if (!p || !T)
  {
    long pa, t;
    if (typ(f) != t_POL) pari_err(typeer, "polrootsff");
    T = p = NULL;
    t = RgX_type(f, &p, &T, &pa);
    if (t != t_FFELT) pari_err(typeer, "factorff");
    return FFX_roots(f,T);
  }
  ffcheck(&av, &f, &T, p); z = FqX_roots_i(f, T, p);
  return to_Fq_vec(z, T,p, av);
}

/* factorization of x modulo (T,p). Assume x already reduced */
GEN
FqX_factor(GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  if (!T) return FpX_factor(x, p);
  return gerepilecopy(av, FqX_factor_i(x, T, p));
}
/* See also: Isomorphisms between finite field and relative
 * factorization in polarit3.c */
