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
/*                       BASIC NF OPERATIONS                       */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"

/*******************************************************************/
/*                                                                 */
/*                OPERATIONS OVER NUMBER FIELD ELEMENTS.           */
/*  represented as column vectors over the integral basis nf[7]    */
/*                                                                 */
/*******************************************************************/
static GEN
get_tab(GEN nf, long *N)
{
  GEN tab = (typ(nf) == t_MAT)? nf: gel(nf,9);
  *N = lg(tab[1])-1; return tab;
}

/* x != 0 t_INT. Return x * y (not memory clean) */
static GEN
_mulix(GEN x, GEN y) {
  return is_pm1(x)? (signe(x) < 0)? gneg(y): y
		  : gmul(x, y);
}
/* x != 0, y t_INT. Return x * y (not memory clean) */
static GEN
_mulii(GEN x, GEN y) {
  return is_pm1(x)? (signe(x) < 0)? negi(y): y
		  : mulii(x, y);
}

/* compute xy as ( sum_i x_i sum_j y_j m^{i,j}_k )_k.
 * Assume tab in M_{N x N^2}(Z), with x, y R^N (R arbitrary) */
static GEN
mul_by_tabi(GEN tab, GEN x, GEN y)
{
  long i, j, k, N = lg(x)-1;
  GEN s, v = cgetg(N+1,t_COL);

  for (k=1; k<=N; k++)
  {
    pari_sp av = avma;
    if (k == 1)
      s = gmul(gel(x,1),gel(y,1));
    else
      s = gadd(gmul(gel(x,1),gel(y,k)),
	       gmul(gel(x,k),gel(y,1)));
    for (i=2; i<=N; i++)
    {
      GEN t, xi = gel(x,i);
      long base;
      if (gcmp0(xi)) continue;

      base = (i-1)*N;
      t = NULL;
      for (j=2; j<=N; j++)
      {
	GEN p1, c = gcoeff(tab,k,base+j); /* m^{i,j}_k */
	if (!signe(c)) continue;
	p1 = _mulix(c, gel(y,j));
	t = t? gadd(t, p1): p1;
      }
      if (t) s = gadd(s, gmul(xi, t));
    }
    gel(v,k) = gerepileupto(av,s);
  }
  return v;
}

GEN
element_mulidid(GEN nf, long i, long j)
{
  long N;
  GEN tab = get_tab(nf, &N);
  tab += (i-1)*N; return gel(tab,j);
}

/* Outputs x.w_i, where w_i is the i-th elt of the integral basis.
 * Assume x a RgV of correct length */
GEN
element_mulid(GEN nf, GEN x, long i)
{
  long j, k, N;
  GEN v, tab;

  if (i==1) return gcopy(x);
  tab = get_tab(nf, &N); tab += (i-1)*N;
  v = cgetg(N+1,t_COL);
  for (k=1; k<=N; k++)
  {
    pari_sp av = avma;
    GEN s = gen_0;
    for (j=1; j<=N; j++)
    {
      GEN c = gcoeff(tab,k,j);
      if (signe(c)) s = gadd(s, _mulix(c, gel(x,j)));
    }
    gel(v,k) = gerepileupto(av,s);
  }
  return v;
}
/* as element_mulid, assume x a ZV of correct length */
GEN
elementi_mulid(GEN nf, GEN x, long i)
{
  long j, k, N;
  GEN v, tab;

  if (i==1) return ZC_copy(x);
  tab = get_tab(nf, &N); tab += (i-1)*N;
  v = cgetg(N+1,t_COL);
  for (k=1; k<=N; k++)
  {
    pari_sp av = avma;
    GEN s = gen_0;
    for (j=1; j<=N; j++)
    {
      GEN c = gcoeff(tab,k,j);
      if (signe(c)) s = addii(s, _mulii(c, gel(x,j)));
    }
    gel(v,k) = gerepileuptoint(av, s);
  }
  return v;
}

/* table of multiplication by wi in ZK = Z[w1,..., wN] */
GEN
eltmulid_get_table(GEN nf, long i)
{
  long k,N;
  GEN m, tab = get_tab(nf, &N);
  tab += (i-1)*N;
  m = cgetg(N+1,t_COL);
  for (k=1; k<=N; k++) m[k] = tab[k];
  return m;
}

static GEN
RgC_mul_get_table(GEN nf, GEN x)
{
  long i, l = lg(x);
  GEN mul = cgetg(l,t_MAT);
  gel(mul,1) = x; /* assume w_1 = 1 */
  for (i=2; i<l; i++) gel(mul,i) = element_mulid(nf,x,i);
  return mul;
}
static GEN
ZC_mul_get_table(GEN nf, GEN x)
{
  long i, l = lg(x);
  GEN mul = cgetg(l,t_MAT);
  gel(mul,1) = x; /* assume w_1 = 1 */
  for (i=2; i<l; i++) gel(mul,i) = elementi_mulid(nf,x,i);
  return mul;
}

/* table of multiplication by x in ZK = Z[w1,..., wN] */
GEN
eltmul_get_table(GEN nf, GEN x)
{
  if (typ(x) == t_MAT) return x;
  x = nf_to_scalar_or_basis(nf, x);
  if (typ(x) != t_COL) return scalarmat_shallow(x, degpol(nf[1]));
  return RgC_mul_get_table(nf, x);
}
/* as eltmul_get_table, x integral */
GEN
eltimul_get_table(GEN nf, GEN x)
{
  if (typ(x) == t_MAT) return x;
  x = nf_to_scalar_or_basis(nf, x);
  if (typ(x) != t_COL) return scalarmat_shallow(x, degpol(nf[1]));
  return ZC_mul_get_table(nf, x);
}

/* product of x and y in nf */
GEN
element_mul(GEN nf, GEN x, GEN y)
{
  long N;
  GEN z;
  pari_sp av = avma;

  if (x == y) return element_sqr(nf,x);

  nf = checknf(nf);
  x = nf_to_scalar_or_basis(nf, x);
  y = nf_to_scalar_or_basis(nf, y);
  if (typ(x) != t_COL)
  {
    if (typ(y) == t_COL) z = RgC_Rg_mul(y, x);
    else {
      N = degpol(gel(nf,1));
      z = zerocol(N); gel(z,1) = gmul(x,y);
    }
  }
  else
  {
    if (typ(y) != t_COL) z = RgC_Rg_mul(x, y);
    else {
      GEN tab = get_tab(nf, &N);
      z = mul_by_tabi(tab,x,y);
    }
  }
  return gerepileupto(av, z);
}

GEN
element_mulvec(GEN nf, GEN x, GEN v)
{
  long l, i;
  GEN y;

  x = nf_to_scalar_or_basis(nf, x);
  if (typ(x) != t_COL) {
    if (gcmp1(x)) return shallowcopy(v);
    if (gcmp_1(x)) return gneg(v);
  }
  else
    x = RgC_mul_get_table(nf, x);
  l = lg(v); y = cgetg(l, typ(v));
  for (i=1; i < l; i++) gel(y,i) = gmul(x, gel(v,i));
  return y;
}

/* inverse of x in nf */
GEN
element_inv(GEN nf, GEN x)
{
  pari_sp av = avma;
  GEN T, z;

  nf = checknf(nf); T = gel(nf,1);
  x = nf_to_scalar_or_alg(nf, x);
  if (typ(x) == t_POL)
    z = poltobasis(nf, QXQ_inv(x, T));
  else {
    z = zerocol(degpol(T)); gel(z,1) = ginv(x);
  }
  return gerepileupto(av, z);
}

/* quotient of x and y in nf */
GEN
element_div(GEN nf, GEN x, GEN y)
{
  pari_sp av = avma;
  GEN T, z;

  nf = checknf(nf); T = gel(nf,1);
  y = nf_to_scalar_or_alg(nf, y);
  if (typ(y) != t_POL) {
    x = nf_to_scalar_or_basis(nf, x);
    if (typ(x) == t_COL) z = RgC_Rg_div(x, y);
    else {
      z = zerocol(degpol(T)); gel(z,1) = gdiv(x,y);
    }
  }
  else
  {
    x = nf_to_scalar_or_alg(nf, x);
    z = QXQ_inv(y, T);
    z = (typ(x) == t_POL)? RgXQ_mul(z, x, T): RgX_Rg_mul(z, x);
    z = poltobasis(nf, z);
  }
  return gerepileupto(av, z);
}

/* product of INTEGERS (i.e vectors with integral coeffs) x and y in nf */
GEN
element_muli(GEN nf, GEN x, GEN y)
{
  long i, j, k, N, tx = typ(x), ty = typ(y);
  GEN s, v, tab = get_tab(nf, &N);

  if (tx == t_INT)
  {
    if (ty == t_INT) return scalarcol(mulii(x,y), N);
    if (ty != t_COL || lg(y) != N+1) pari_err(typeer,"element_muli");
    return ZC_Z_mul(y, x);
  }
  if (tx != t_COL || lg(x) != N+1) pari_err(typeer,"element_muli");
  if (ty == t_INT) return ZC_Z_mul(x, y);
  if (ty != t_COL || lg(y) != N+1) pari_err(typeer,"element_muli");
  v = cgetg(N+1,t_COL);
  for (k=1; k<=N; k++)
  {
    pari_sp av = avma;
    if (k == 1)
      s = mulii(gel(x,1),gel(y,1));
    else
      s = addii(mulii(gel(x,1),gel(y,k)),
		mulii(gel(x,k),gel(y,1)));
    for (i=2; i<=N; i++)
    {
      GEN t, xi = gel(x,i);
      long base;
      if (!signe(xi)) continue;

      base = (i-1)*N;
      t = NULL;
      for (j=2; j<=N; j++)
      {
	GEN p1, c = gcoeff(tab,k,base+j); /* m^{i,j}_k */
	if (!signe(c)) continue;
	p1 = _mulii(c, gel(y,j));
	t = t? addii(t, p1): p1;
      }
      if (t) s = addii(s, mulii(xi, t));
    }
    gel(v,k) = gerepileuptoint(av,s);
  }
  return v;
}

/* product of INTEGERS (i.e vectors with integral coeffs) x and y in nf */
GEN
element_sqri(GEN nf, GEN x)
{
  long i, j, k, N;
  GEN s, v, tab = get_tab(nf, &N);

  v = cgetg(N+1,t_COL);
  for (k=1; k<=N; k++)
  {
    pari_sp av = avma;
    if (k == 1)
      s = sqri(gel(x,1));
    else
      s = shifti(mulii(gel(x,1),gel(x,k)), 1);
    for (i=2; i<=N; i++)
    {
      GEN p1, c, t, xi = gel(x,i);
      long base;
      if (!signe(xi)) continue;

      base = (i-1)*N;
      c = gcoeff(tab,k,base+i);
      t = signe(c)? _mulii(c,xi): NULL;
      for (j=i+1; j<=N; j++)
      {
	c = gcoeff(tab,k,base+j);
	if (!signe(c)) continue;
	p1 = _mulii(c, shifti(gel(x,j),1));
	t = t? addii(t, p1): p1;
      }
      if (t) s = addii(s, mulii(xi, t));
    }
    gel(v,k) = gerepileuptoint(av,s);
  }
  return v;
}

/* cf mul_by_tabi */
static GEN
sqr_by_tabi(GEN tab, GEN x)
{
  long i, j, k, N = lg(x)-1;
  GEN s, v = cgetg(N+1,t_COL);

  for (k=1; k<=N; k++)
  {
    pari_sp av = avma;
    if (k == 1)
      s = gsqr(gel(x,1));
    else
      s = gmul2n(gmul(gel(x,1),gel(x,k)), 1);
    for (i=2; i<=N; i++)
    {
      GEN p1, c, t, xi = gel(x,i);
      long base;
      if (gcmp0(xi)) continue;

      base = (i-1)*N;
      c = gcoeff(tab,k,base+i);
      t = signe(c)? _mulix(c,xi): NULL;
      for (j=i+1; j<=N; j++)
      {
	c = gcoeff(tab,k,(i-1)*N+j);
	if (!signe(c)) continue;
	p1 = gmul(shifti(c,1), gel(x,j));
	t = t? gadd(t, p1): p1;
      }
      if (t) s = gadd(s, gmul(xi, t));
    }
    gel(v,k) = gerepileupto(av,s);
  }
  return v;
}

/* cf sqr_by_tab. Assume nothing about tab */
GEN
sqr_by_tab(GEN tab, GEN x)
{
  long i, j, k, N = lg(x)-1;
  GEN s, v = cgetg(N+1,t_COL);

  for (k=1; k<=N; k++)
  {
    pari_sp av = avma;
    if (k == 1)
      s = gsqr(gel(x,1));
    else
      s = gmul2n(gmul(gel(x,1),gel(x,k)), 1);
    for (i=2; i<=N; i++)
    {
      GEN p1, c, t, xi = gel(x,i);
      long base;
      if (gcmp0(xi)) continue;

      base = (i-1)*N;
      c = gcoeff(tab,k,base+i);
      t = !gcmp0(c)? gmul(c,xi): NULL;
      for (j=i+1; j<=N; j++)
      {
	c = gcoeff(tab,k,(i-1)*N+j);
	if (gcmp0(c)) continue;
	p1 = gmul(gmul2n(c,1), gel(x,j));
	t = t? gadd(t, p1): p1;
      }
      if (t) s = gadd(s, gmul(xi, t));
    }
    gel(v,k) = gerepileupto(av,s);
  }
  return v;
}

/* square of x in nf */
GEN
element_sqr(GEN nf, GEN x)
{
  pari_sp av = avma;
  long N;
  GEN z;

  nf = checknf(nf);
  x = nf_to_scalar_or_basis(nf, x);
  if (typ(x) != t_COL) 
  {
    N = degpol(gel(nf,1));
    z = zerocol(N); gel(z,1) = gsqr(x);
  }
  else
  {
    GEN tab = get_tab(nf, &N);
    z = sqr_by_tabi(tab,x);
  }
  return gerepileupto(av, z);
}

static GEN
_mul(void *data, GEN x, GEN y) { return element_muli((GEN)data,x,y); }
static GEN
_sqr(void *data, GEN x) { return element_sqri((GEN)data,x); }

/* Compute x^n in nf, left-shift binary powering */
GEN
element_pow(GEN nf, GEN x, GEN n)
{
  pari_sp av = avma;
  long s,N;
  GEN y, cx;

  if (typ(n)!=t_INT) pari_err(talker,"not an integer exponent in nfpow");
  nf = checknf(nf); N = degpol(nf[1]);
  s = signe(n); if (!s) return scalarcol_shallow(gen_1,N);
  x = nf_to_scalar_or_basis(nf, x);
  if (typ(x) != t_COL) { y = zerocol(N); gel(y,1) = powgi(x,n); return y; }
  x = primitive_part(x, &cx);
  y = leftright_pow(x, n, (void*)nf, _sqr, _mul);
  if (s < 0) y = element_inv(nf, y);
  if (cx) y = gmul(y, powgi(cx, n));
  return av==avma? gcopy(y): gerepileupto(av,y);
}

typedef struct {
  GEN nf, p;
  long I;
} eltmod_muldata;

static GEN
_mulidmod(void *data, GEN x, GEN y)
{
  eltmod_muldata *D = (eltmod_muldata*)data;
  (void)y; /* ignored */
  return FpC_red(element_mulid(D->nf, x, D->I), D->p);
}
static GEN
_sqrmod(void *data, GEN x)
{
  eltmod_muldata *D = (eltmod_muldata*)data;
  return FpC_red(element_sqri(D->nf, x), D->p);
}

/* x = I-th vector of the Z-basis of Z_K, in Z^n, compute lift(x^n mod p) */
GEN
element_powid_mod_p(GEN nf, long I, GEN n, GEN p)
{
  pari_sp av = avma;
  eltmod_muldata D;
  long s,N;
  GEN y;

  if (typ(n) != t_INT) pari_err(talker,"not an integer exponent in nfpow");
  nf = checknf(nf); N = degpol(nf[1]);
  s = signe(n);
  if (s < 0) pari_err(talker,"negative power in element_powid_mod_p");
  if (!s || I == 1) return scalarcol_shallow(gen_1,N);
  D.nf = nf;
  D.p = p;
  D.I = I;
  y = leftright_pow(col_ei(N, I), n, (void*)&D, &_sqrmod, &_mulidmod);
  return gerepileupto(av,y);
}

/* valuation of integer x, with resp. to prime ideal P above p.
 * p.P^(-1) = b Z_K
 * [b may be given as the 'multiplication by b' matrix]
 */
long
int_elt_val(GEN nf, GEN x, GEN p, GEN b, GEN *newx)
{
  long i, k, w, N = degpol(nf[1]);
  GEN r, a, y, mul = eltimul_get_table(nf, b);

  y = cgetg(N+1, t_COL); /* will hold the new x */
  x = shallowcopy(x);
  for(w=0;; w++)
  {
    for (i=1; i<=N; i++)
    { /* compute (x.b)_i */
      a = mulii(gel(x,1), gcoeff(mul,i,1));
      for (k=2; k<=N; k++) a = addii(a, mulii(gel(x,k), gcoeff(mul,i,k)));
      /* is it divisible by p ? */
      gel(y,i) = dvmdii(a,p,&r);
      if (signe(r))
      {
	if (newx) *newx = x;
	return w;
      }
    }
    swap(x, y);
  }
}

long
element_val(GEN nf, GEN x, GEN vp)
{
  pari_sp av = avma;
  long w, e;
  GEN cx,p;

  if (gcmp0(x)) return LONG_MAX;
  nf = checknf(nf);
  checkprimeid(vp);
  p = gel(vp,1);
  e = itos(gel(vp,3));
  x = nf_to_scalar_or_basis(nf, x);
  switch(typ(x))
  {
    case t_INT: return e * Z_pval(x,p);
    case t_FRAC:return e * Q_pval(x,p);
  }
  x = Q_primitive_part(x, &cx);
  w = int_elt_val(nf,x,p,gel(vp,5),NULL);
  avma = av; return w + e * (cx? Q_pval(cx,p): 0);
}

GEN
coltoalg(GEN nf, GEN x)
{
  return mkpolmod( coltoliftalg(nf, x), gel(nf,1) );
}

GEN
basistoalg(GEN nf, GEN x)
{
  long tx = typ(x);
  GEN z, T;

  nf = checknf(nf);
  switch(tx)
  {
    case t_COL: {
      pari_sp av = avma;
      return gerepilecopy(av, coltoalg(nf, x));
    }
    case t_POLMOD:
      if (!RgX_equal_var(gel(nf,1),gel(x,1)))
	pari_err(talker,"not the same number field in basistoalg");
      return gcopy(x);
    case t_POL:
      T = gel(nf,1);
      if (varn(T) != varn(x)) pari_err(consister,"basistoalg");
      z = cgetg(3,t_POLMOD);
      gel(z,1) = gcopy(T);
      gel(z,2) = RgX_rem(x, T); return z;
    case t_INT:
    case t_FRAC:
      T = gel(nf,1);
      z = cgetg(3,t_POLMOD);
      gel(z,1) = gcopy(T);
      gel(z,2) = gcopy(x); return z;
    default:
      pari_err(typeer,"basistoalg");
      return NULL; /* not reached */
  }
}

/* The following shallow functions do what the public functions should do,
 * without sanity checks.
 * Assume nf is a genuine nf. */
GEN
basistoalg_i(GEN nf, GEN x)
{
  switch(typ(x))
  {
    case t_COL: return coltoliftalg(nf, x);
    case t_POLMOD: return gel(x,2);
    case t_POL:
    case t_INT:
    case t_FRAC: return x;
  }
  pari_err(typeer,"basistoalg_i");
  return NULL; /* not reached */
}
GEN
algtobasis_i(GEN nf, GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_FRAC:
      return scalarcol_shallow(x, degpol( gel(nf,1) ));
    case t_POLMOD:
      x = gel(x,2);
      if (typ(x) != t_POL) return scalarcol_shallow(x, degpol( gel(nf,1) ));
      /* fall through */
    case t_POL:
      return poltobasis(nf,x);
    case t_COL:
      if (lg(x) == lg(gel(nf,7))) break;
    default: pari_err(typeer,"algtobasis_i");
  }
  return x;
}
GEN
nf_to_scalar_or_basis(GEN nf, GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_FRAC:
      return x;
    case t_POLMOD:
      x = checknfelt_mod(nf,x,"nf_to_scalar_or_basis");
      if (typ(x) != t_POL) return x;
      /* fall through */
    case t_POL:
    {
      GEN T = gel(nf,1);
      long l = lg(x);
      if (varn(x) != varn(T))
        pari_err(talker,"incompatible variables in nf_to_scalar_or_alg");
      if (l >= lg(T)) { x = RgX_rem(x, T); l = lg(x); }
      if (l == 2) return gen_0;
      if (l == 3) return gel(x,2);
      return poltobasis(nf,x);
    }
    case t_COL:
      if (lg(x) != lg(gel(nf,7))) break;
      return RgV_isscalar(x)? gel(x,1): x;
  }
  pari_err(typeer,"nf_to_scalar_or_basis");
  return NULL; /* not reached */
}
/* Let x be a polynomial with coefficients in Q or nf. Return the same
 * polynomial with coefficients expressed as vectors (on the integral basis).
 * No consistency checks, not memory-clean. */
GEN
RgX_to_nfX(GEN nf, GEN x)
{
  long i, l = lg(x);
  GEN y = cgetg(l,t_POL); y[1] = x[1];
  for (i=2; i<l; i++) gel(y,i) = nf_to_scalar_or_basis(nf, gel(x,i));
  return y;
}

GEN
nf_to_scalar_or_alg(GEN nf, GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_FRAC:
      return x;
    case t_POLMOD:
      x = checknfelt_mod(nf,x,"nf_to_scalar_or_alg");
      if (typ(x) != t_POL) return x;
      /* fall through */
    case t_POL:
    {
      GEN T = gel(nf,1);
      long l = lg(x);
      if (varn(x) != varn(T))
        pari_err(talker,"incompatible variables in nf_to_scalar_or_alg");
      if (l >= lg(T)) { x = RgX_rem(x, T); l = lg(x); }
      if (l == 2) return gen_0;
      if (l == 3) return gel(x,2);
      return x;
    }
    case t_COL:
      if (lg(x) != lg(gel(nf,7))) break;
      return RgV_isscalar(x)? gel(x,1): coltoliftalg(nf, x);
  }
  pari_err(typeer,"nf_to_scalar_or_alg");
  return NULL; /* not reached */
}

/* gmul(A, RgX_to_RgV(x)), A t_MAT (or t_VEC) of compatible dimensions */
GEN
mulmat_pol(GEN A, GEN x)
{
  long i,l;
  GEN z;
  if (typ(x) != t_POL) return gmul(x,gel(A,1)); /* scalar */
  l=lg(x)-1; if (l == 1) return typ(A)==t_VEC? gen_0: zerocol(lg(A[1])-1);
  x++; z = gmul(gel(x,1), gel(A,1));
  for (i=2; i<l ; i++)
    if (!gcmp0(gel(x,i))) z = gadd(z, gmul(gel(x,i), gel(A,i)));
  return z;
}

/* valid for t_POL, nf a genuine nf or an rnf !
 * No garbage collecting. No check.  */
GEN
poltobasis(GEN nf, GEN x)
{
  GEN P = gel(nf,1);
  if (varn(x) != varn(P))
    pari_err(talker, "incompatible variables in poltobasis");
  if (degpol(x) >= degpol(P)) x = RgX_rem(x,P);
  return mulmat_pol(gel(nf,8), x);
}

GEN
algtobasis(GEN nf, GEN x)
{
  long tx = typ(x);
  pari_sp av;

  nf = checknf(nf);
  switch(tx)
  {
    case t_POLMOD:
      if (!RgX_equal_var(gel(nf,1),gel(x,1)))
	pari_err(talker,"not the same number field in algtobasis");
      x = gel(x,2); tx = typ(x);
      switch(tx)
      {
        case t_INT:
        case t_FRAC: return scalarcol(x, degpol(nf[1]));
        case t_POL: 
          av = avma;
          return gerepileupto(av,poltobasis(nf,x));
      }
      break;

    case t_POL:
      av = avma;
      return gerepileupto(av,poltobasis(nf,x));

    case t_COL:
      return gcopy(x);

    case t_INT:
    case t_FRAC: return scalarcol(x, degpol(nf[1]));
  }
  pari_err(typeer,"algtobasis");
  return NULL; /* not reached */
}

GEN
rnfbasistoalg(GEN rnf,GEN x)
{
  long tx = typ(x), lx = lg(x), i;
  pari_sp av = avma;
  GEN p1, z, nf;

  checkrnf(rnf);
  switch(tx)
  {
    case t_VEC: case t_COL:
      p1 = cgetg(lx,t_COL); nf = gel(rnf,10);
      for (i=1; i<lx; i++) gel(p1,i) = basistoalg_i(nf, gel(x,i));
      p1 = gmul(gmael(rnf,7,1), p1);
      return gerepileupto(av, gmodulo(p1,gel(rnf,1)));

    case t_MAT:
      z = cgetg(lx,tx);
      for (i=1; i<lx; i++) gel(z,i) = rnfbasistoalg(rnf,gel(x,i));
      return z;

    case t_POLMOD:
      if (!RgX_equal_var(gel(rnf,1),gel(x,1)))
        pari_err(talker,"not the same number field in rnfbasistoalg");
      return gcopy(x);

    default: z = cgetg(3,t_POLMOD);
      gel(z,1) = gcopy(gel(rnf,1));
      gel(z,2) = gtopoly(x, varn(rnf[1])); return z;
  }
}

GEN
matbasistoalg(GEN nf,GEN x)
{
  long i, j, li, lx = lg(x), tx = typ(x);
  GEN z = cgetg(lx, tx);

  if (lx == 1) return z;
  switch(tx)
  {
    case t_VEC: case t_COL:
      for (i=1; i<lx; i++) gel(z,i) = basistoalg(nf, gel(x,i));
      return z;
    case t_MAT: break;
    default: pari_err(typeer, "matbasistoalg");
  }
  li = lg(x[1]);
  for (j=1; j<lx; j++)
  {
    GEN c = cgetg(li,t_COL), xj = gel(x,j);
    gel(z,j) = c;
    for (i=1; i<li; i++) gel(c,i) = basistoalg(nf, gel(xj,i));
  }
  return z;
}

GEN
matalgtobasis(GEN nf,GEN x)
{
  long i, j, li, lx = lg(x), tx = typ(x);
  GEN z = cgetg(lx, tx);

  if (lx == 1) return z;
  switch(tx)
  {
    case t_VEC: case t_COL:
      for (i=1; i<lx; i++) gel(z,i) = algtobasis(nf, gel(x,i));
      return z;
    case t_MAT: break;
    default: pari_err(typeer, "matalgtobasis");
  }
  li = lg(x[1]);
  for (j=1; j<lx; j++)
  {
    GEN c = cgetg(li,t_COL), xj = gel(x,j);
    gel(z,j) = c;
    for (i=1; i<li; i++) gel(c,i) = algtobasis(nf, gel(xj,i));
  }
  return z;
}

GEN
rnfalgtobasis(GEN rnf,GEN x)
{
  long tx = typ(x), i, lx;
  GEN z;

  checkrnf(rnf);
  switch(tx)
  {
    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); z = cgetg(lx,tx);
      for (i=1; i<lx; i++) gel(z,i) = rnfalgtobasis(rnf,gel(x,i));
      return z;

    case t_POLMOD:
      if (!RgX_equal_var(gel(rnf,1),gel(x,1)))
	pari_err(talker,"not the same number field in rnfalgtobasis");
      x = gel(x,2);
      if (typ(x) != t_POL) { GEN A = gel(rnf,8); return gmul(x, gel(A,1)); }
      /* fall through */
    case t_POL: {
      pari_sp av = avma;
      return gerepileupto(av, poltobasis(rnf, x));
    }
  }
  return scalarcol(x, degpol(rnf[1]));
}

/* Given a and b in nf, gives an algebraic integer y in nf such that a-b.y
 * is "small"
 */
GEN
nfdiveuc(GEN nf, GEN a, GEN b)
{
  pari_sp av = avma;
  a = element_div(nf,a,b);
  return gerepileupto(av, ground(a));
}

/* Given a and b in nf, gives a "small" algebraic integer r in nf
 * of the form a-b.y
 */
GEN
nfmod(GEN nf, GEN a, GEN b)
{
  pari_sp av = avma;
  GEN p1 = gneg_i(element_mul(nf,b,ground(element_div(nf,a,b))));
  return gerepileupto(av, gadd(a,p1));
}

/* Given a and b in nf, gives a two-component vector [y,r] in nf such
 * that r=a-b.y is "small". */
GEN
nfdivrem(GEN nf, GEN a, GEN b)
{
  pari_sp av = avma;
  GEN p1,z, y = ground(element_div(nf,a,b));

  p1 = gneg_i(element_mul(nf,b,y));
  z = cgetg(3,t_VEC);
  gel(z,1) = gcopy(y);
  gel(z,2) = gadd(a,p1); return gerepileupto(av, z);
}

/*************************************************************************/
/**									**/
/**			      (Z_K/I)^*					**/
/**									**/
/*************************************************************************/
/* return sign(sigma_k(x)), x t_COL (integral, primitive) */
static long
eval_sign(GEN M, GEN x, long k)
{
  long i, l = lg(x);
  GEN z = mpmul(gcoeff(M,k,1), gel(x,1));
  for (i = 2; i < l; i++)
    z = mpadd(z, mpmul(gcoeff(M,k,i), gel(x,i)));
  if (lg(z) < DEFAULTPREC) pari_err(precer,"zsigne");
  return signe(z);
}

GEN
arch_to_perm(GEN arch)
{
  long i, k, l;
  GEN perm;

  if (!arch) return cgetg(1, t_VECSMALL);
  switch (typ(arch))
  {
   case t_VECSMALL: return arch;
   case t_VEC: break;
   default: pari_err(typeer,"arch_to_perm");
  }
  l = lg(arch);
  perm = cgetg(l, t_VECSMALL);
  for (k=1, i=1; i < l; i++)
    if (signe(arch[i])) perm[k++] = i;
  setlg(perm, k); return perm;
}
GEN
perm_to_arch(GEN nf, GEN archp)
{
  long i, l;
  GEN v;
  if (typ(archp) == t_VEC) return archp;

  l = lg(archp); nf = checknf(nf);
  v = zerovec( nf_get_r1(nf) );
  for (i = 1; i < l; i++) gel(v, archp[i]) = gen_1;
  return v;
}

/* reduce mod 2 in place */
GEN
F2V_red_ip(GEN v)
{
  long i, l = lg(v);
  for (i = 1; i < l; i++) gel(v,i) = mpodd(gel(v,i))? gen_1: gen_0;
  return v;
}

/* return (column) vector of R1 signatures of x (0 or 1)
 * if arch = NULL, assume arch = [0,..0] */
GEN
zsigne(GEN nf,GEN x,GEN arch)
{
  GEN M, V, archp = arch_to_perm(arch);
  long i, s, l = lg(archp);
  pari_sp av;

  if (l == 1) return cgetg(1,t_COL);
  V = cgetg(l,t_COL); av = avma;
  nf = checknf(nf);
  if (typ(x) == t_MAT)
  { /* factorisation */
    GEN g = gel(x,1), e = gel(x,2), z = vec_setconst(V, gen_0);
    for (i=1; i<lg(g); i++)
      if (mpodd(gel(e,i))) z = ZC_add(z, zsigne(nf,gel(g,i),archp));
    for (i=1; i<l; i++) gel(V,i) = mpodd(gel(z,i))? gen_1: gen_0;
    avma = av; return V;
  }
  x = nf_to_scalar_or_basis(nf, x);
  if (typ(x) != t_COL)
  { /* scalar: INT or FRAC */
    s = gsigne(x); if (!s) pari_err(talker,"zero element in zsigne");
    return vec_setconst(V, (s < 0)? gen_1: gen_0);
  }
  x = Q_primpart(x); M = gmael(nf,5,1);
  for (i = 1; i < l; i++)
    gel(V,i) = (eval_sign(M, x, archp[i]) > 0)? gen_0: gen_1;
  avma = av; return V;
}

/* return the t_COL vector of signs of x; the matrix of such if x is a vector
 * of nf elements */
GEN
zsigns(GEN nf, GEN x)
{
  long r1, i, l;
  GEN arch, S;

  nf = checknf(nf); r1 = nf_get_r1(nf);
  arch = cgetg(r1+1, t_VECSMALL); for (i=1; i<=r1; i++) arch[i] = i;
  if (typ(x) != t_VEC) return zsigne(nf, x, arch);
  l = lg(x); S = cgetg(l, t_MAT);
  for (i=1; i<l; i++) gel(S,i) = zsigne(nf, gel(x,i), arch);
  return S;
}

/* For internal use. Reduce x modulo (invertible) y */
GEN
closemodinvertible(GEN x, GEN y)
{
  return gmul(y, ground(gauss(y,x)));
}
GEN
reducemodinvertible(GEN x, GEN y)
{
  return gsub(x, closemodinvertible(x,y));
}
GEN
reducemodlll(GEN x,GEN y)
{
  return reducemodinvertible(x, ZM_lll(y, 0.75, LLL_INPLACE));
}

/* multiply y by t = 1 mod^* f such that sign(x) = sign(y) at arch = idele[2].
 * If x == NULL, make y >> 0 at sarch */
GEN
set_sign_mod_idele(GEN nf, GEN x, GEN y, GEN idele, GEN sarch)
{
  GEN s, archp, gen;
  long nba,i;
  if (!sarch) return y;
  gen = gel(sarch,2); nba = lg(gen);
  if (nba == 1) return y;

  archp = arch_to_perm(gel(idele,2));
  s = zsigne(nf, y, archp);
  if (x) s = ZC_add(s, zsigne(nf, x, archp));
  s = ZM_ZC_mul(gel(sarch,3), s);
  for (i=1; i<nba; i++)
    if (mpodd(gel(s,i))) y = element_mul(nf,y,gel(gen,i));
  return y;
}

/* given an element x in Z_K and an integral ideal y in HNF, coprime with x,
   outputs an element inverse of x modulo y */
GEN
element_invmodideal(GEN nf, GEN x, GEN y)
{
  pari_sp av = avma;
  GEN a, xh, yZ = gcoeff(y,1,1);

  nf = checknf(nf);
  if (is_pm1(yZ)) return zerocol( degpol(nf[1]) );

  x = nf_to_scalar_or_basis(nf, x);
  if (typ(x) == t_INT) return gerepileupto(av, Fp_inv(x, yZ));

  xh = idealhermite_aux(nf,x);
  a = element_div(nf, hnfmerge_get_1(xh, y), x);
  return gerepileupto(av, ZC_hnfrem(a, y));
}

static GEN
element_sqrmodideal(GEN nf, GEN x, GEN id) {
  return ZC_hnfrem(element_sqri(nf,x), id);
}
static GEN
element_mulmodideal(GEN nf, GEN x, GEN y, GEN id) {
  return x? ZC_hnfrem(element_muli(nf,x,y), id): y;
}
/* assume k >= 0, ideal in HNF */
GEN
element_powmodideal(GEN nf,GEN x,GEN k,GEN ideal)
{
  GEN y;
  if (!signe(k)) return scalarcol_shallow(gen_1, degpol(nf[1]));
  x = nf_to_scalar_or_basis(nf, x);
  if (typ(x) != t_COL) {
    x = Fp_pow(x, k, gcoeff(ideal,1,1));
    return scalarcol_shallow(x, degpol(nf[1]));
  }
  for(y = NULL;;)
  {
    if (mpodd(k)) y = element_mulmodideal(nf,y,x,ideal);
    k = shifti(k,-1); if (!signe(k)) break;
    x = element_sqrmodideal(nf,x,ideal);
  }
  return y;
}

/* a * g^n mod id */
static GEN
elt_mulpow_modideal(GEN nf, GEN a, GEN g, GEN n, GEN id)
{
  return element_mulmodideal(nf, a, element_powmodideal(nf,g,n,id), id);
}

/* assume (num(g[i]), id) = 1 for all i. Return prod g[i]^e[i] mod id.
 * EX = multiple of exponent of (O_K/id)^* */
GEN
famat_to_nf_modideal_coprime(GEN nf, GEN g, GEN e, GEN id, GEN EX)
{
  GEN dh, h, n, plus = NULL, minus = NULL, idZ = gcoeff(id,1,1);
  long i, lx = lg(g);
  GEN EXo2 = (expi(EX) > 10)? shifti(EX,-1): NULL;

  if (is_pm1(idZ)) lx = 1; /* id = Z_K */
  for (i=1; i<lx; i++)
  {
    long sn;
    n = centermodii(gel(e,i), EX, EXo2);
    sn = signe(n); if (!sn) continue;

    h = nf_to_scalar_or_basis(nf, gel(g,i));
    switch(typ(h))
    {
      case t_INT: break;
      case t_FRAC:
        h = Fp_div(gel(h,1), gel(h,2), idZ); break;
      default:
        h = Q_remove_denom(h, &dh);
        if (dh) h = FpC_Fp_mul(h, Fp_inv(dh,idZ), idZ);
    }
    if (sn > 0)
      plus = elt_mulpow_modideal(nf, plus, h, n, id);
    else /* sn < 0 */
      minus = elt_mulpow_modideal(nf, minus, h, negi(n), id);
  }
  if (minus)
    plus = element_mulmodideal(nf, plus, element_invmodideal(nf,minus,id), id);
  return plus? plus: scalarcol_shallow(gen_1, lg(id)-1);
}

/* given 2 integral ideals x, y in HNF s.t x | y | x^2, compute the quotient
   (1+x)/(1+y) in the form [[cyc],[gen]], if U != NULL, set *U := ux^-1 */
static GEN
zidealij(GEN x, GEN y, GEN *U)
{
  GEN G, cyc;
  long j, N;

  /* x^(-1) y = relations between the 1 + x_i (HNF) */
  cyc = smithrel(hnf_gauss(x, y), U, &G);
  N = lg(cyc); G = ZM_mul(x,G); settyp(G, t_VEC); /* new generators */
  for (j=1; j<N; j++)
  {
    GEN c = gel(G,j);
    gel(c,1) = addsi(1, gel(c,1)); /* 1 + g_j */
  }
  if (U) *U = gmul(*U, ginv(x));
  return mkvec2(cyc, G);
}

static GEN
Fq_FpXQ_log(GEN a, GEN g, GEN ord, GEN T, GEN p)
{
  if (!T)
    return Fp_log(a,g,ord,p);
  if (typ(a)==t_INT)
    return Fp_FpXQ_log(a,g,ord,T,p);
  return FpXQ_log(a,g,ord,T,p);
}

/* same in nf.zk / pr */
static GEN
nf_log(GEN nf, GEN a, GEN g, GEN pr)
{
  pari_sp av = avma;
  GEN T,p, modpr = nf_to_Fq_init(nf, &pr, &T, &p);
  GEN A = nf_to_Fq(nf,a,modpr);
  GEN G = nf_to_Fq(nf,g,modpr);
  GEN ord = addis(T?powiu(p,degpol(T)):p,-1);
  return gerepileuptoint(av, Fq_FpXQ_log(A,G,ord,T,p));
}

/* Product of cyc entries, with cyc = diagonal(Smith Normal Form), assumed != 0.
 * Set L to the index of the last non-trivial (!= 1) entry */
GEN
detcyc(GEN cyc, long *L)
{
  pari_sp av = avma;
  long i, l = lg(cyc);
  GEN s = gel(cyc,1);

  if (l == 1) { *L = 1; return gen_1; }
  for (i=2; i<l; i++)
  {
    GEN t = gel(cyc,i);
    if (is_pm1(t)) break;
    s = mulii(s, t);
  }
  *L = i; return i <= 2? icopy(s): gerepileuptoint(av,s);
}

/* (U,V) = 1. Return y = x mod U, = 1 mod V (uv: u + v = 1, u in U, v in V).
 * mv = multiplication table by v */
static GEN
makeprimetoideal(GEN UV, GEN u,GEN mv, GEN x)
{ return ZC_hnfrem(ZC_add(u, ZM_ZC_mul(mv,x)), UV); }

static GEN
makeprimetoidealvec(GEN nf, GEN UV, GEN u,GEN v, GEN gen)
{
  long i, lx = lg(gen);
  GEN y = cgetg(lx,t_VEC), mv = eltimul_get_table(nf, v);
  for (i=1; i<lx; i++) gel(y,i) = makeprimetoideal(UV,u,mv, gel(gen,i));
  return y;
}

/* Given an ideal pr^ep, and an integral ideal x (in HNF form) compute a list
 * of vectors,corresponding to the abelian groups (O_K/pr)^*, and
 * 1 + pr^i/ 1 + pr^min(2i, ep), i = 1,...
 * Each vector has 5 components as follows :
 * [[cyc],[g],[g'],[sign],U.X^-1].
 * cyc   = type as abelian group
 * g, g' = generators. (g',x) = 1, not necessarily so for g
 * sign  = vector of the sign(g') at arch.
 * If x = NULL, the original ideal was a prime power */
static GEN
zprimestar(GEN nf, GEN pr, GEN ep, GEN x, GEN arch)
{
  pari_sp av = avma;
  long a, b, e = itos(ep), f = itos(gel(pr,4));
  GEN p = gel(pr,1), list, g, g0, y, u,v, prh, prb, pre;

  if(DEBUGLEVEL>3) fprintferr("treating pr^%ld, pr = %Zs\n",e,pr);
  if (f == 1)
    g = scalarcol_shallow(pgener_Fp(p), degpol(nf[1]));
  else
  {
    GEN T, modpr = zk_to_Fq_init(nf, &pr, &T, &p);
    g = Fq_to_nf(gener_FpXQ(T,p,NULL), modpr);
    g = poltobasis(nf, g);
  }
  /* g generates  (Z_K / pr)^* */
  prh = prime_to_ideal(nf,pr);
  pre = (e==1)? prh: idealpow(nf,pr,ep);
  g0 = g;
  u = v = NULL; /* gcc -Wall */
  if (x)
  {
    GEN uv = idealaddtoone(nf,pre, idealdivpowprime(nf,x,pr,ep));
    u = gel(uv,1);
    v = eltimul_get_table(nf, gel(uv,2));
    g0 = makeprimetoideal(x,u,v,g);
  }

  list = cget1(e+1, t_VEC);
  y = cgetg(6,t_VEC); appendL(list, y);
  gel(y,1) = mkvec(addis(powiu(p,f), -1));
  gel(y,2) = mkvec(g);
  gel(y,3) = mkvec(g0);
  gel(y,4) = mkvec(zsigne(nf,g0,arch));
  gel(y,5) = gen_1;
  prb = prh;
  for (a = b = 1; a < e; a = b)
  {
    GEN pra = prb, gen, z, s, U;
    long i, l;

    b <<= 1;
    /* compute 1 + pr^a / 1 + pr^b, 2a <= b */
    if(DEBUGLEVEL>3) fprintferr("  treating a = %ld, b = %ld\n",a,b);
    prb = (b >= e)? pre: idealpows(nf,pr,b);
    z = zidealij(pra, prb, &U);
    gen = shallowcopy(gel(z,2));
    l = lg(gen); s = cgetg(l, t_VEC);
    if(DEBUGLEVEL>3) fprintferr("zidealij done\n");
    for (i = 1; i < l; i++)
    {
      if (x) gel(gen,i) = makeprimetoideal(x,u,v,gel(gen,i));
      gel(s,i) = zsigne(nf,gel(gen,i),arch);
    }
    y = cgetg(6,t_VEC); appendL(list, y);
    gel(y,1) = gel(z,1);
    gel(y,2) = gel(z,2);
    gel(y,3) = gen;
    gel(y,4) = s;
    gel(y,5) = U;
  }
  return gerepilecopy(av, list);
}

/* increment y, which runs through [-d,d]^k. Return 0 when done. */
static int
increment(GEN y, long k, long d)
{
  long i = 0, j;
  do
  {
    if (++i > k) return 0;
    y[i]++;
  } while (y[i] > d);
  for (j = 1; j < i; j++) y[j] = -d;
  return 1;
}

GEN
archstar_full_rk(GEN x, GEN bas, GEN v, GEN gen)
{
  long i, r, lgmat, N = lg(bas)-1, nba = lg(v[1]) - 1;
  GEN lambda = cgetg(N+1, t_VECSMALL), mat = cgetg(nba+1,t_MAT);

  lgmat = lg(v); setlg(mat, lgmat+1);
  for (i = 1; i < lgmat; i++) mat[i] = v[i];
  for (     ; i <= nba; i++)  gel(mat,i) = cgetg(nba+1, t_VECSMALL);

  if (x) { x = ZM_lll(x, 0.75, LLL_INPLACE); bas = gmul(bas, x); }

  for (r=1;; r++)
  { /* reset */
    (void)vec_setconst(lambda, (GEN)0);
    if (!x) lambda[1] = r;
    while (increment(lambda, N, r))
    {
      pari_sp av1 = avma;
      GEN a = RgM_zc_mul(bas, lambda), c = gel(mat,lgmat);
      for (i = 1; i <= nba; i++)
      {
	GEN t = x? gadd(gel(a,i), gen_1): gel(a,i);
	c[i] = (gsigne(t) < 0)? 1: 0;
      }
      avma = av1; if (Flm_deplin(mat, 2)) continue;

      /* c independant of previous sign vectors */
      if (!x) a = zc_to_ZC(lambda);
      else
      {
	a = ZM_zc_mul(x, lambda);
	gel(a,1) = addis(gel(a,1), 1);
      }
      gel(gen,lgmat) = a;
      if (lgmat++ == nba) return Flm_to_ZM( Flm_inv(mat,2) ); /* full rank */
      setlg(mat,lgmat+1);
    }
  }
}

/* x integral ideal, compute elements in 1+x (in x, if x = zk) whose sign
 * matrix is invertible */
GEN
zarchstar(GEN nf, GEN x, GEN archp)
{
  long nba;
  GEN cyc, gen, mat;

  archp = arch_to_perm(archp);
  nba = lg(archp) - 1;
  if (!nba)
  {
    cyc = gen = cgetg(1, t_VEC);
    mat = cgetg(1, t_MAT);
  }
  else
  {
    GEN xZ = gcoeff(x,1,1), gZ;
    pari_sp av = avma;
    if (gcmp1(xZ)) x = NULL; /* x = O_K */
    gZ = x? subsi(1, xZ): gen_m1; /* gZ << 0, gZ = 1 mod x */
    if (nba == 1)
    {
      gen = mkvec(gZ);
      mat = scalarmat(gen_1,1);
    }
    else
    {
      GEN bas = gmael(nf,5,1);
      if (lg(bas[1]) > lg(archp)) bas = rowpermute(bas, archp);
      gen = cgetg(nba+1,t_VEC);
      gel(gen,1) = gZ;
      mat = archstar_full_rk(x, bas, mkmat(const_vecsmall(nba,1)), gen);
      gerepileall(av,2,&gen,&mat);
    }
    cyc = const_vec(nba, gen_2);
  }
  return mkvec3(cyc,gen,mat);
}

static GEN
zlog_pk(GEN nf, GEN a0, GEN y, GEN pr, GEN prk, GEN list, GEN *psigne)
{
  GEN a = a0, L, e, cyc, gen, s, U;
  long i,j, llist = lg(list)-1;

  for (j = 1; j <= llist; j++)
  {
    L = gel(list,j);
    cyc = gel(L,1);
    gen = gel(L,2);
    s   = gel(L,4);
    U   = gel(L,5);
    if (j == 1)
      e = mkcol( nf_log(nf, a, gel(gen,1), pr) );
    else if (typ(a) == t_INT)
      e = gmul(subis(a, 1), gel(U,1));
    else
    { /* t_COL */
      GEN t = gel(a,1);
      gel(a,1) = addsi(-1, gel(a,1)); /* a -= 1 */
      e = gmul(U, a);
      gel(a,1) = t; /* restore */
    }
    /* here lg(e) == lg(cyc) */
    for (i = 1; i < lg(cyc); i++)
    {
      GEN t = modii(negi(gel(e,i)), gel(cyc,i));
      gel(++y,0) = negi(t); if (!signe(t)) continue;

      if (mod2(t)) *psigne = *psigne? ZC_add(*psigne, gel(s,i)): gel(s,i);
      if (j != llist) a = elt_mulpow_modideal(nf, a, gel(gen,i), t, prk);
    }
  }
  return y;
}

static void
zlog_add_sign(GEN y0, GEN sgn, GEN lists)
{
  GEN y, s;
  long i;
  if (!sgn) return;
  y = y0 + lg(y0);
  s = ZM_ZC_mul(gmael(lists, lg(lists)-1, 3), sgn);
  for (i = lg(s)-1; i > 0; i--) gel(--y,0) = mpodd(gel(s,i))? gen_1: gen_0;
}

static GEN
famat_zlog(GEN nf, GEN g, GEN e, GEN sgn, GEN bid)
{
  GEN vp = gmael(bid, 3,1), ep = gmael(bid, 3,2), arch = gmael(bid,1,2);
  GEN cyc = gmael(bid,2,2), lists = gel(bid,4), U = gel(bid,5);
  GEN y0, x, y, EX = gel(cyc,1);
  long i, l;

  y0 = y = cgetg(lg(U), t_COL);
  if (!sgn) sgn = zsigne(nf, to_famat(g,e), arch);
  l = lg(vp);
  for (i=1; i < l; i++)
  {
    GEN pr = gel(vp,i), prk;
    prk = (l==2)? gmael(bid,1,1): idealpow(nf, pr, gel(ep,i));
    /* FIXME: FIX group exponent (should be mod prk, not f !) */
    x = famat_makecoprime(nf, g, e, pr, prk, EX);
    y = zlog_pk(nf, x, y, pr, prk, gel(lists,i), &sgn);
  }
  zlog_add_sign(y0, sgn, lists);
  return y0;
}

static GEN
get_index(GEN lists)
{
  long t = 0, j, k, l = lg(lists)-1;
  GEN L, ind = cgetg(l+1, t_VECSMALL);

  for (k = 1; k < l; k++)
  {
    L = gel(lists,k);
    ind[k] = t;
    for (j=1; j<lg(L); j++) t += lg(gmael(L,j,1)) - 1;
  }
  /* for arch. components */
  ind[k] = t; return ind;
}

static void
init_zlog(zlog_S *S, long n, GEN P, GEN e, GEN arch, GEN lists, GEN U)
{
  S->n = n;
  S->U = U;
  S->P = P;
  S->e = e;
  S->archp = arch_to_perm(arch);
  S->lists = lists;
  S->ind = get_index(lists);
}
void
init_zlog_bid(zlog_S *S, GEN bid)
{
  GEN ideal = gel(bid,1), fa = gel(bid,3), fa2 = gel(bid,4), U = gel(bid,5);
  GEN arch = (typ(ideal)==t_VEC && lg(ideal)==3)? gel(ideal,2): NULL;
  init_zlog(S, lg(U)-1, gel(fa,1), gel(fa,2), arch, fa2, U);
}

/* Return decomposition of a on the S->nf successive generators contained in
 * S->lists. If index !=0, do the computation for the corresponding prime
 * ideal and set to 0 the other components. */
static GEN
zlog_ind(GEN nf, GEN a, zlog_S *S, GEN sgn, long index)
{
  GEN y0 = zerocol(S->n), y, list, pr, prk;
  pari_sp av = avma;
  long i, k, kmin, kmax;

  a = nf_to_scalar_or_basis(nf,a);
  if (DEBUGLEVEL>3)
  {
    fprintferr("entering zlog, "); flusherr();
    if (DEBUGLEVEL>5) fprintferr("with a = %Zs\n",a);
  }
  if (index)
  {
    kmin = kmax = index;
    y = y0 + S->ind[index];
  }
  else
  {
    kmin = 1; kmax = lg(S->P)-1;
    y = y0;
  }
  if (!sgn) sgn = zsigne(nf, a, S->archp);
  for (k = kmin; k <= kmax; k++)
  {
    list= gel(S->lists,k);
    pr  = gel(S->P,k);
    prk = idealpow(nf, pr, gel(S->e,k));
    y = zlog_pk(nf, a, y, pr, prk, list, &sgn);
  }
  zlog_add_sign(y0, sgn, S->lists);
  if (DEBUGLEVEL>3) { fprintferr("leaving\n"); flusherr(); }
  avma = av;
  for (i=1; i <= S->n; i++) gel(y0,i) = icopy(gel(y0,i));
  return y0;
}
/* sgn = sign(a, S->arch) or NULL if unknown */
GEN
zlog(GEN nf, GEN a, GEN sgn, zlog_S *S) { return zlog_ind(nf, a, S, sgn, 0); }

/* Log on bid.gen of generators of P_{1,I pr^{e-1}} / P_{1,I pr^e} (I,pr) = 1,
 * defined implicitly via CRT. 'index' is the index of pr in modulus
 * factorization */
GEN
log_gen_pr(zlog_S *S, long index, GEN nf, long e)
{
  long i, l, yind = S->ind[index];
  GEN y, A, L, L2 = gel(S->lists,index);

  if (e == 1)
  {
    L = gel(L2,1);
    y = zerocol(S->n); gel(y, yind+1) = gen_1;
    zlog_add_sign(y, gmael(L,4,1), S->lists);
    A = mkmat(y);
  }
  else
  {
    GEN pr = gel(S->P,index), prk, g;

    if (e == 2)
      L = gel(L2,2);
    else
      L = zidealij(idealpows(nf,pr,e-1), idealpows(nf,pr,e), NULL);
    g = gel(L,2);
    l = lg(g);
    A = cgetg(l, t_MAT);
    prk = idealpow(nf, pr, gel(S->e,index));
    for (i = 1; i < l; i++)
    {
      GEN G = gel(g,i), sgn = NULL; /* positive at f_oo */
      y = zerocol(S->n);
      (void)zlog_pk(nf, G, y + yind, pr, prk, L2, &sgn);
      zlog_add_sign(y, sgn, S->lists);
      gel(A,i) = y;
    }
  }
  return gmul(S->U, A);
}
/* Log on bid.gen of generator of P_{1,f} / P_{1,f v[index]}
 * v = vector of r1 real places */
GEN
log_gen_arch(zlog_S *S, long index)
{
  GEN y = zerocol(S->n);
  zlog_add_sign(y, col_ei(lg(S->archp)-1, index), S->lists);
  return gmul(S->U, y);
}

/* add [h,cyc] or [h,cyc,gen] to bid */
static void
add_grp(GEN nf, GEN u1, GEN cyc, GEN gen, GEN bid)
{
  GEN h = ZV_prod(cyc);
  if (u1)
  {
    GEN G = mkvec3(h,cyc,NULL/*dummy, bid[2] needed below*/);
    gel(bid,2) = G;
    if (u1 != gen_1)
    {
      long i, c = lg(u1);
      GEN g = cgetg(c,t_VEC);
      for (i=1; i<c; i++)
        gel(g,i) = famat_to_nf_modidele(nf, gen, gel(u1,i), bid);
      gen = g;
    }
    gel(G,3) = gen; /* replace dummy */
  }
  else
    gel(bid,2) = mkvec2(h,cyc);
}

/* Compute [[ideal,arch], [h,[cyc],[gen]], idealfact, [liste], U]
   flag may include nf_GEN | nf_INIT */
GEN
Idealstar(GEN nf, GEN ideal, long flag)
{
  pari_sp av = avma;
  long i, j, k, nbp, R1, nbgen;
  GEN t, y, cyc, U, u1 = NULL, fa, lists, x, arch, archp, E, P, sarch, gen;

  nf = checknf(nf);
  R1 = nf_get_r1(nf);
  if (typ(ideal) == t_VEC && lg(ideal) == 3)
  {
    arch = gel(ideal,2); ideal = gel(ideal,1);
    i = typ(arch);
    if (!is_vec_t(i) || lg(arch) != R1+1)
      pari_err(talker,"incorrect archimedean component in Idealstar");
    archp = arch_to_perm(arch);
  }
  else
  {
    arch = zerovec(R1);
    archp = cgetg(1, t_VECSMALL);
  }
  x = idealhermite_aux(nf, ideal);
  if (lg(x) == 1 || typ(gcoeff(x,1,1)) != t_INT)
    pari_err(talker,"Idealstar needs an integral non-zero ideal: %Zs",x);
  sarch = zarchstar(nf, x, archp);
  fa = idealfactor(nf, ideal);
  P = gel(fa,1);
  E = gel(fa,2); nbp = lg(P)-1;
  if (nbp)
  {
    GEN h;
    long cp = 0;
    zlog_S S;

    lists = cgetg(nbp+2,t_VEC);
    /* rough upper bound */
    nbgen = nbp + 1; for (i=1; i<=nbp; i++) nbgen += itos(gel(E,i));
    gen = cgetg(nbgen+1,t_VEC);
    nbgen = 1;
    t = (nbp==1)? NULL: x;
    for (i=1; i<=nbp; i++)
    {
      GEN L = zprimestar(nf, gel(P,i), gel(E,i), t, archp);
      gel(lists,i) = L;
      for (j = 1; j < lg(L); j++) gel(gen, nbgen++) = gmael(L,j,3);
    }
    gel(lists,i) = sarch;
    gel(gen, nbgen++) = gel(sarch,2); setlg(gen, nbgen);
    gen = shallowconcat1(gen); nbgen = lg(gen)-1;

    h = cgetg(nbgen+1,t_MAT);
    init_zlog(&S, nbgen, P, E, archp, lists, NULL);
    for (i=1; i<=nbp; i++)
    {
      GEN L2 = gel(lists,i);
      for (j=1; j < lg(L2); j++)
      {
	GEN L = gel(L2,j), F = gel(L,1), G = gel(L,3);
	for (k=1; k<lg(G); k++)
	{ /* log(g^f) mod idele */
	  GEN g = gel(G,k), f = gel(F,k), a = element_powmodideal(nf,g,f,x);
	  GEN sgn = mpodd(f)? zsigne(nf, g, S.archp): zerocol(lg(S.archp)-1);
	  gel(h,++cp) = gneg(zlog_ind(nf, a, &S, sgn, i));
	  coeff(h,cp,cp) = F[k];
	}
      }
    }
    for (j=1; j<lg(archp); j++)
    {
      gel(h,++cp) = zerocol(nbgen);
      gcoeff(h,cp,cp) = gen_2;
    }
    /* assert(cp == nbgen) */
    h = ZM_hnfall(h,NULL,0);
    cyc = smithrel(h, &U, (flag & nf_GEN)? &u1: NULL);
  }
  else
  {
    lists = mkvec(sarch);
    gen = gel(sarch,2); nbgen = lg(gen)-1;
    cyc = const_vec(nbgen, gen_2);
    U = matid(nbgen);
    if (flag & nf_GEN) u1 = gen_1;
  }

  y = cgetg(6,t_VEC);
  gel(y,1) = mkvec2(x, arch);
  gel(y,3) = fa;
  gel(y,4) = lists;
  gel(y,5) = U;
  add_grp(nf, u1, cyc, gen, y);
  if (!(flag & nf_INIT)) y = gel(y,2);
  return gerepilecopy(av, y);
}

/* FIXME: obsolete */
GEN
zidealstarinitgen(GEN nf, GEN ideal)
{ return Idealstar(nf,ideal, nf_INIT|nf_GEN); }
GEN
zidealstarinit(GEN nf, GEN ideal)
{ return Idealstar(nf,ideal, nf_INIT); }
GEN
zidealstar(GEN nf, GEN ideal)
{ return Idealstar(nf,ideal, nf_GEN); }

GEN
idealstar0(GEN nf, GEN ideal,long flag)
{
  switch(flag)
  {
    case 0: return Idealstar(nf,ideal, nf_GEN);
    case 1: return Idealstar(nf,ideal, nf_INIT);
    case 2: return Idealstar(nf,ideal, nf_INIT|nf_GEN);
    default: pari_err(flagerr,"idealstar");
  }
  return NULL; /* not reached */
}

void
check_nfelt(GEN x, GEN *den)
{
  long l = lg(x), i;
  GEN t, d = NULL;
  if (typ(x) != t_COL) pari_err(talker,"%Zs not a nfelt", x);
  for (i=1; i<l; i++)
  {
    t = gel(x,i);
    switch (typ(t))
    {
      case t_INT: break;
      case t_FRAC:
	if (!d) d = gel(t,2); else d = lcmii(d, gel(t,2));
	break;
      default: pari_err(talker,"%Zs not a nfelt", x);
    }
  }
  *den = d;
}

GEN
vecmodii(GEN a, GEN b)
{
  long i, l = lg(a);
  GEN c = cgetg(l, typ(a));
  for (i = 1; i < l; i++) gel(c,i) = modii(gel(a,i), gel(b,i));
  return c;
}

/* Given x (not necessarily integral), and bid as output by zidealstarinit,
 * compute the vector of components on the generators bid[2].
 * Assume (x,bid) = 1 and sgn is either NULL or zsigne(x, bid) */
GEN
zideallog_sgn(GEN nf, GEN x, GEN sgn, GEN bid)
{
  pari_sp av;
  long N, lcyc;
  GEN den, cyc, y;
  int ok = 0;

  nf = checknf(nf); checkbid(bid);
  cyc = gmael(bid,2,2);
  lcyc = lg(cyc); if (lcyc == 1) return cgetg(1, t_COL);
  av = avma;
  N = degpol(nf[1]);
  switch(typ(x))
  {
    case t_INT: case t_FRAC:
      ok = 1; den = denom(x);
      break;
    case t_POLMOD: case t_POL:
      x = algtobasis(nf,x); break;
    case t_COL: break;
    case t_MAT:
      if (lg(x) == 1) return zerocol(lcyc-1);
      y = famat_zlog(nf, gel(x,1), gel(x,2), sgn, bid);
      goto END;

    default: pari_err(talker,"not an element in zideallog");
  }
  if (!ok)
  {
    if (lg(x) != N+1) pari_err(talker,"not an element in zideallog");
    check_nfelt(x, &den);
  }
  if (den)
  {
    GEN g = mkcol2(Q_muli_to_int(x,den), den);
    GEN e = mkcol2(gen_1, gen_m1);
    y = famat_zlog(nf, g, e, sgn, bid);
  }
  else
  {
    zlog_S S; init_zlog_bid(&S, bid);
    y = zlog(nf, x, sgn, &S);
  }
END:
  y = ZM_ZC_mul(gel(bid,5), y);
  return gerepileupto(av, vecmodii(y, cyc));
}
GEN
zideallog(GEN nf, GEN x, GEN bid) { return zideallog_sgn(nf, x, NULL, bid); }

/*************************************************************************/
/**									**/
/**		  JOIN BID STRUCTURES, IDEAL LISTS                      **/
/**									**/
/*************************************************************************/

/* bid1, bid2: for coprime modules m1 and m2 (without arch. part).
 * Output: bid [[m1 m2,arch],[h,[cyc],[gen]],idealfact,[liste],U] for m1 m2 */
static GEN
join_bid(GEN nf, GEN bid1, GEN bid2)
{
  pari_sp av = avma;
  long i, nbgen, lx, lx1,lx2, l1,l2;
  GEN I1,I2, f1,f2, G1,G2, fa1,fa2, lists1,lists2, cyc1,cyc2;
  GEN lists, fa, U, cyc, y, u1 = NULL, x, gen;

  f1 = gel(bid1,1); I1 = gel(f1,1);
  f2 = gel(bid2,1); I2 = gel(f2,1);
  if (gcmp1(gcoeff(I1,1,1))) return bid2; /* frequent trivial case */
  G1 = gel(bid1,2); G2 = gel(bid2,2);
  fa1= gel(bid1,3); fa2= gel(bid2,3); x = idealmul(nf, I1,I2);
  fa = concat_factor(fa1, fa2);

  lists1 = gel(bid1,4); lx1 = lg(lists1);
  lists2 = gel(bid2,4); lx2 = lg(lists2);
  /* concat (lists1 - last elt [zarchstar]) + lists2 */
  lx = lx1+lx2-2; lists = cgetg(lx,t_VEC);
  for (i=1; i<lx1-1; i++) lists[i] = lists1[i];
  for (   ; i<lx; i++)    lists[i] = lists2[i-lx1+2];

  cyc1 = gel(G1,2); l1 = lg(cyc1);
  cyc2 = gel(G2,2); l2 = lg(cyc2);
  gen = (lg(G1)>3 && lg(G2)>3)? gen_1: NULL;
  nbgen = l1+l2-2;
  cyc = smithrel(diagonal_i(shallowconcat(cyc1,cyc2)),
		 &U, gen? &u1: NULL);
  if (nbgen) {
    GEN U1 = gel(bid1,5), U2 = gel(bid2,5);
    U1 = l1 == 1? zeromat(nbgen,lg(U1)-1): ZM_mul(vecslice(U, 1, l1-1),   U1);
    U2 = l2 == 1? zeromat(nbgen,lg(U2)-1): ZM_mul(vecslice(U, l1, nbgen), U2);
    U = shallowconcat(U1, U2);
  }
  else
    U = zeromat(0, lx-2);

  if (gen)
  {
    GEN u, v, uv = idealaddtoone(nf,gel(f1,1),gel(f2,1));
    u = gel(uv,1);
    v = gel(uv,2);
    gen = shallowconcat(makeprimetoidealvec(nf,x,u,v, gel(G1,3)),
		        makeprimetoidealvec(nf,x,v,u, gel(G2,3)));
  }
  y = cgetg(6,t_VEC);
  gel(y,1) = mkvec2(x, gel(f1,2));
  gel(y,3) = fa;
  gel(y,4) = lists;
  gel(y,5) = U;
  add_grp(nf, u1, cyc, gen, y);
  return gerepilecopy(av,y);
}

typedef struct _ideal_data {
  GEN nf, emb, L, pr, prL, arch, sgnU;
} ideal_data;

/* z <- ( z | f(v[i])_{i=1..#v} ) */
static void
concat_join(GEN *pz, GEN v, GEN (*f)(ideal_data*,GEN), ideal_data *data)
{
  long i, nz, lv = lg(v);
  GEN z, Z, Zt;
  if (lv == 1) return;
  z = *pz; nz = lg(z)-1;
  Z = cgetg(lv + nz, typ(z));
  for (i = 1; i <=nz; i++) Z[i] = z[i];
  Zt = Z + nz;
  for (i = 1; i < lv; i++) gel(Zt,i) = f(data, gel(v,i));
  *pz = Z;
}
static GEN
join_idealinit(ideal_data *D, GEN x) {
  return join_bid(D->nf, x, D->prL);
}
static GEN
join_ideal(ideal_data *D, GEN x) {
  return idealmulpowprime(D->nf, x, D->pr, D->L);
}
static GEN
join_unit(ideal_data *D, GEN x) {
  return mkvec2(join_idealinit(D, gel(x,1)), vconcat(gel(x,2), D->emb));
}

/* compute matrix of zlogs of units */
GEN
zlog_units(GEN nf, GEN U, GEN sgnU, GEN bid)
{
  long j, l = lg(U);
  GEN m = cgetg(l, t_MAT);
  zlog_S S; init_zlog_bid(&S, bid);
  for (j = 1; j < l; j++)
    gel(m,j) = zlog(nf, gel(U,j), vecpermute(gel(sgnU,j), S.archp), &S);
  return m;
}
/* compute matrix of zlogs of units, assuming S.archp = [] */
GEN
zlog_units_noarch(GEN nf, GEN U, GEN bid)
{
  long j, l = lg(U);
  GEN m = cgetg(l, t_MAT), empty = cgetg(1, t_COL);
  zlog_S S; init_zlog_bid(&S, bid);
  for (j = 1; j < l; j++) gel(m,j) = zlog(nf, gel(U,j), empty, &S);
  return m;
}

/* calcule la matrice des zlog des unites */
static GEN
zlog_unitsarch(GEN sgnU, GEN bid)
{
  GEN U, liste = gel(bid,4), arch = gmael(bid,1,2);
  long i;
  U = ZM_ZC_mul(gmael(liste, lg(liste)-1, 3),
	        rowpermute(sgnU, arch_to_perm(arch)));
  for (i = 1; i < lg(U); i++) (void)F2V_red_ip(gel(U,i));
  return U;
}

/*  flag & nf_GEN : generators, otherwise no
 *  flag &2 : units, otherwise no
 *  flag &4 : ideals in HNF, otherwise bid */
static GEN
Ideallist(GEN bnf, ulong bound, long flag)
{
  const long do_units = flag & 2, big_id = !(flag & 4);
  const long istar_flag = (flag & nf_GEN) | nf_INIT;
  byteptr ptdif = diffptr;
  pari_sp lim, av, av0 = avma;
  long i, j, l;
  GEN nf, z, p, fa, id, U, empty = cgetg(1,t_VEC);
  ideal_data ID;
  GEN (*join_z)(ideal_data*, GEN) =
    do_units? &join_unit
	      : (big_id? &join_idealinit: &join_ideal);

  nf = checknf(bnf);
  if ((long)bound <= 0) return empty;
  id = matid(degpol(nf[1]));
  if (big_id) id = Idealstar(nf,id, istar_flag);

  /* z[i] will contain all "objects" of norm i. Depending on flag, this means
   * an ideal, a bid, or a couple [bid, log(units)]. Such objects are stored
   * in vectors, computed one primary component at a time; join_z
   * reconstructs the global object */
  z = cgetg(bound+1,t_VEC);
  if (do_units) {
    U = init_units(bnf);
    gel(z,1) = mkvec( mkvec2(id, zlog_units_noarch(nf, U, id)) );
  } else {
    U = NULL; /* -Wall */
    gel(z,1) = mkvec(id);
  }
  for (i=2; i<=(long)bound; i++) gel(z,i) = empty;
  ID.nf = nf;

  p = cgetipos(3);
  av = avma; lim = stack_lim(av,1);
  maxprime_check(bound);
  for (p[2] = 0; (ulong)p[2] <= bound; )
  {
    NEXT_PRIME_VIADIFF(p[2], ptdif);
    if (DEBUGLEVEL>1) { fprintferr("%ld ",p[2]); flusherr(); }
    fa = primedec(nf, p);
    for (j=1; j<lg(fa); j++)
    {
      GEN pr = gel(fa,j), z2;
      ulong q, iQ, Q = itou_or_0(pr_norm(pr));
      if (!Q || Q > bound) break;

      z2 = shallowcopy(z);
      q = Q;
      ID.pr = ID.prL = pr;
      for (l=1; Q <= bound; l++, Q *= q) /* add pr^l */
      {
	ID.L = utoipos(l);
	if (big_id) {
	  if (l > 1) ID.prL = idealpow(nf,pr,ID.L);
	  ID.prL = Idealstar(nf,ID.prL, istar_flag);
	  if (do_units) ID.emb = zlog_units_noarch(nf, U, ID.prL);
	}
	for (iQ = Q,i = 1; iQ <= bound; iQ += Q,i++)
	  concat_join(&gel(z,iQ), gel(z2,i), join_z, &ID);
      }
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"Ideallist");
      z = gerepilecopy(av, z);
    }
  }
  if (do_units) for (i = 1; i < lg(z); i++)
  {
    GEN s = gel(z,i);
    long l = lg(s);
    for (j = 1; j < l; j++) {
      GEN v = gel(s,j), bid = gel(v,1);
      gel(v,2) = ZM_mul(gel(bid,5), gel(v,2));
    }
  }
  return gerepilecopy(av0, z);
}
GEN
ideallist0(GEN bnf,long bound, long flag) {
  if (flag<0 || flag>4) pari_err(flagerr,"ideallist");
  return Ideallist(bnf,bound,flag);
}
GEN
ideallistzstar(GEN nf,long bound) { return Ideallist(nf,bound,0); }
GEN
ideallistzstargen(GEN nf,long bound) { return Ideallist(nf,bound,1); }
GEN
ideallistunit(GEN nf,long bound) { return Ideallist(nf,bound,2); }
GEN
ideallistunitgen(GEN nf,long bound) { return Ideallist(nf,bound,3); }
GEN
ideallist(GEN bnf,long bound) { return Ideallist(bnf,bound,4); }

/* bid1 = for module m1 (without arch. part), arch = archimedean part.
 * Output: bid [[m1,arch],[h,[cyc],[gen]],idealfact,[liste],U] for m1.arch */
static GEN
join_bid_arch(GEN nf, GEN bid1, GEN arch)
{
  pari_sp av = avma;
  long i, lx1;
  GEN f1, G1, fa1, lists1, U;
  GEN lists, cyc, y, u1 = NULL, x, sarch, gen;

  checkbid(bid1);
  f1 = gel(bid1,1); G1 = gel(bid1,2); fa1 = gel(bid1,3);
  x = gel(f1,1);
  sarch = zarchstar(nf, x, arch);
  lists1 = gel(bid1,4); lx1 = lg(lists1);
  lists = cgetg(lx1,t_VEC);
  for (i=1; i<lx1-1; i++) lists[i] = lists1[i];
  gel(lists,i) = sarch;

  gen = (lg(G1)>3)? gen_1: NULL;
  cyc = diagonal_i(shallowconcat(gel(G1,2), gel(sarch,1)));
  cyc = smithrel(cyc, &U, gen? &u1: NULL);
  if (gen) gen = shallowconcat(gel(G1,3), gel(sarch,2));
  y = cgetg(6,t_VEC);
  gel(y,1) = mkvec2(x, arch);
  gel(y,3) = fa1;
  gel(y,4) = lists;
  gel(y,5) = U;
  add_grp(nf, u1, cyc, gen, y);
  return gerepilecopy(av,y);
}
static GEN
join_arch(ideal_data *D, GEN x) {
  return join_bid_arch(D->nf, x, D->arch);
}
static GEN
join_archunit(ideal_data *D, GEN x) {
  GEN bid = join_arch(D, gel(x,1)), U = gel(x,2);
  U = ZM_mul(gel(bid,5), vconcat(U, zlog_unitsarch(D->sgnU, bid)));
  return mkvec2(bid, U);
}

/* L from ideallist, add archimedean part */
GEN
ideallistarch(GEN bnf, GEN L, GEN arch)
{
  pari_sp av;
  long i, j, l = lg(L), lz;
  GEN v, z, V;
  ideal_data ID;
  GEN (*join_z)(ideal_data*, GEN) = &join_arch;

  if (typ(L) != t_VEC) pari_err(typeer, "ideallistarch");
  if (l == 1) return cgetg(1,t_VEC);
  z = gel(L,1);
  if (typ(z) != t_VEC) pari_err(typeer, "ideallistarch");
  z = gel(z,1); /* either a bid or [bid,U] */
  if (lg(z) == 3) { /* the latter: do units */
    if (typ(z) != t_VEC) pari_err(typeer,"ideallistarch");
    join_z = &join_archunit;
    ID.sgnU = zsignunits(bnf, NULL, 1);
  }
  ID.nf = checknf(bnf);
  arch = arch_to_perm(arch);
  av = avma; V = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    z = gel(L,i); lz = lg(z);
    gel(V,i) = v = cgetg(lz,t_VEC);
    for (j=1; j<lz; j++) gel(v,j) = join_z(&ID, gel(z,j));
  }
  return gerepilecopy(av,V);
}
