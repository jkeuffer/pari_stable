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
#include "parinf.h"
extern GEN to_famat(GEN g, GEN e);
extern GEN famat_makecoprime(GEN nf, GEN g, GEN e, GEN pr, GEN prk, GEN EX);
extern GEN famat_to_nf_modidele(GEN nf, GEN g, GEN e, GEN bid);
extern GEN vconcat(GEN A, GEN B);
extern GEN hnf_gauss(GEN A, GEN B);

/*******************************************************************/
/*                                                                 */
/*                OPERATIONS OVER NUMBER FIELD ELEMENTS.           */
/*     These are always represented as column vectors over the     */
/*     integral basis nf[7]                                        */
/*                                                                 */
/*******************************************************************/

int
isnfscalar(GEN x)
{
  long lx=lg(x),i;

  if (typ(x) != t_COL) return 0;
  for (i=2; i<lx; i++)
    if (!gcmp0((GEN)x[i])) return 0;
  return 1;
}

static GEN
scal_mul(GEN nf, GEN x, GEN y, long ty)
{
  pari_sp av=avma, tetpil;
  GEN p1;

  if (!is_extscalar_t(ty))
  {
    if (ty!=t_COL) err(typeer,"nfmul");
    y = gmul((GEN)nf[7],y);
  }
  p1 = gmul(x,y); tetpil=avma;
  return gerepile(av,tetpil,algtobasis(nf,p1));
}

static GEN
get_tab(GEN nf, long *N)
{
  GEN tab = (typ(nf) == t_MAT)? nf: (GEN)nf[9];
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
      s = gmul((GEN)x[1],(GEN)y[1]);
    else
      s = gadd(gmul((GEN)x[1],(GEN)y[k]),
               gmul((GEN)x[k],(GEN)y[1]));
    for (i=2; i<=N; i++)
    {
      GEN t, xi = (GEN)x[i];
      long base;
      if (gcmp0(xi)) continue;

      base = (i-1)*N;
      t = NULL;
      for (j=2; j<=N; j++)
      {
	GEN p1, c = gcoeff(tab,k,base+j); /* m^{i,j}_k */
	if (!signe(c)) continue;
        p1 = _mulix(c, (GEN)y[j]);
        t = t? gadd(t, p1): p1;
      }
      if (t) s = gadd(s, gmul(xi, t));
    }
    v[k] = lpileupto(av,s);
  }
  return v;
}

/* product of x and y in nf */
GEN
element_mul(GEN nf, GEN x, GEN y)
{
  long N,tx,ty;
  GEN tab;

  if (x == y) return element_sqr(nf,x);

  tx=typ(x); ty=typ(y);
  nf=checknf(nf);
  if (tx==t_POLMOD) x=checknfelt_mod(nf,x,"element_mul");
  if (ty==t_POLMOD) y=checknfelt_mod(nf,y,"element_mul");
  if (is_extscalar_t(tx)) return scal_mul(nf,x,y,ty);
  if (is_extscalar_t(ty)) return scal_mul(nf,y,x,tx);
  if (tx != t_COL || ty != t_COL) err(typeer,"element_mul");
  if (isnfscalar(x)) return gmul((GEN)x[1],y);
  if (isnfscalar(y)) return gmul((GEN)y[1],x);

  tab = get_tab(nf, &N);
  return mul_by_tabi(tab,x,y);
}

/* inverse of x in nf */
GEN
element_inv(GEN nf, GEN x)
{
  pari_sp av=avma;
  long i,N,tx=typ(x);
  GEN p1,p;

  nf=checknf(nf); N=degpol(nf[1]);
  if (is_extscalar_t(tx))
  {
    if (tx==t_POLMOD) (void)checknfelt_mod(nf,x,"element_inv");
    else if (tx==t_POL) x=gmodulcp(x,(GEN)nf[1]);
    return gerepileupto(av, algtobasis(nf, ginv(x)));
  }
  if (isnfscalar(x))
  {
    p1=cgetg(N+1,t_COL); p1[1]=linv((GEN)x[1]);
    for (i=2; i<=N; i++) p1[i]=lcopy((GEN)x[i]);
    return p1;
  }
  if (tx != t_COL) err(typeer,"element_inv");
  p = NULL;
  for (i=1; i<=N; i++)
    if (typ(x[i])==t_INTMOD)
    {
      p = gmael(x,i,1);
      x = lift(x); break;
    }
  p1 = QX_invmod(gmul((GEN)nf[7],x), (GEN)nf[1]);
  p1 = algtobasis_i(nf,p1);

  if (p) p1 = FpV(p1, p);
  return gerepileupto(av,p1);
}

/* quotient of x and y in nf */
GEN
element_div(GEN nf, GEN x, GEN y)
{
  pari_sp av=avma;
  long i,N,tx=typ(x),ty=typ(y);
  GEN p1,p;

  nf=checknf(nf); N=degpol(nf[1]);
  if (tx==t_POLMOD) (void)checknfelt_mod(nf,x,"element_div");
  else if (tx==t_POL) x=gmodulcp(x,(GEN)nf[1]);

  if (ty==t_POLMOD) (void)checknfelt_mod(nf,y,"element_div");
  else if (ty==t_POL) y=gmodulcp(y,(GEN)nf[1]);

  if (is_extscalar_t(tx))
  {
    if (is_extscalar_t(ty)) p1=gdiv(x,y);
    else
    {
      if (ty!=t_COL) err(typeer,"nfdiv");
      p1=gdiv(x,gmodulcp(gmul((GEN)nf[7],y),(GEN)nf[1]));
    }
    return gerepileupto(av, algtobasis(nf,p1));
  }
  if (is_extscalar_t(ty))
  {
    if (tx!=t_COL) err(typeer,"nfdiv");
    p1=gdiv(gmodulcp(gmul((GEN)nf[7],x),(GEN)nf[1]),y);
    return gerepileupto(av, algtobasis(nf,p1));
  }
  if (tx != t_COL || ty != t_COL) err(typeer,"element_div");

  if (isnfscalar(y)) return gdiv(x,(GEN)y[1]);
  if (isnfscalar(x))
  {
    p1=element_inv(nf,y);
    return gerepileupto(av, gmul((GEN)x[1],p1));
  }

  p = NULL;
  for (i=1; i<=N; i++)
    if (typ(x[i])==t_INTMOD)
    {
      p = gmael(x,i,1);
      x = lift(x); break;
    }
  for (i=1; i<=N; i++)
    if (typ(y[i])==t_INTMOD)
    {
      p1 = gmael(y,i,1);
      if (p && !egalii(p,p1))
        err(talker,"inconsistant prime moduli in element_inv");
      y = lift(y); break;
    }

  p1 = gmul(gmul((GEN)nf[7],x), QX_invmod(gmul((GEN)nf[7],y), (GEN)nf[1]));
  p1 = algtobasis_i(nf, gres(p1, (GEN)nf[1]));
  if (p) p1 = FpV(p1,p);
  return gerepileupto(av,p1);
}

/* product of INTEGERS (i.e vectors with integral coeffs) x and y in nf */
GEN
element_muli(GEN nf, GEN x, GEN y)
{
  long i, j, k, N;
  GEN s, v, tab = get_tab(nf, &N);

  if (typ(x) != t_COL || lg(x) != N+1
   || typ(y) != t_COL || lg(y) != N+1) err(typeer,"element_muli");
  v = cgetg(N+1,t_COL);
  for (k=1; k<=N; k++)
  {
    pari_sp av = avma;
    if (k == 1)
      s = mulii((GEN)x[1],(GEN)y[1]);
    else
      s = addii(mulii((GEN)x[1],(GEN)y[k]),
                mulii((GEN)x[k],(GEN)y[1]));
    for (i=2; i<=N; i++)
    {
      GEN t, xi = (GEN)x[i];
      long base;
      if (!signe(xi)) continue;

      base = (i-1)*N;
      t = NULL;
      for (j=2; j<=N; j++)
      {
	GEN p1, c = gcoeff(tab,k,base+j); /* m^{i,j}_k */
	if (!signe(c)) continue;
        p1 = _mulii(c, (GEN)y[j]);
        t = t? addii(t, p1): p1;
      }
      if (t) s = addii(s, mulii(xi, t));
    }
    v[k] = lpileuptoint(av,s);
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
      s = sqri((GEN)x[1]);
    else
      s = shifti(mulii((GEN)x[1],(GEN)x[k]), 1);
    for (i=2; i<=N; i++)
    {
      GEN p1, c, t, xi = (GEN)x[i];
      long base;
      if (!signe(xi)) continue;

      base = (i-1)*N;
      c = gcoeff(tab,k,base+i);
      t = signe(c)? _mulii(c,xi): NULL;
      for (j=i+1; j<=N; j++)
      {
	c = gcoeff(tab,k,base+j);
	if (!signe(c)) continue;
        p1 = _mulii(shifti(c,1), (GEN)x[j]);
        t = t? addii(t, p1): p1;
      }
      if (t) s = addii(s, mulii(xi, t));
    }
    v[k] = lpileuptoint(av,s);
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
      s = gsqr((GEN)x[1]);
    else
      s = gmul2n(gmul((GEN)x[1],(GEN)x[k]), 1);
    for (i=2; i<=N; i++)
    {
      GEN p1, c, t, xi = (GEN)x[i];
      long base;
      if (gcmp0(xi)) continue;

      base = (i-1)*N;
      c = gcoeff(tab,k,base+i);
      t = signe(c)? _mulix(c,xi): NULL;
      for (j=i+1; j<=N; j++)
      {
	c = gcoeff(tab,k,(i-1)*N+j);
	if (!signe(c)) continue;
        p1 = gmul(shifti(c,1), (GEN)x[j]);
        t = t? gadd(t, p1): p1;
      }
      if (t) s = gadd(s, gmul(xi, t));
    }
    v[k] = (long)gerepileupto(av,s);
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
      s = gsqr((GEN)x[1]);
    else
      s = gmul2n(gmul((GEN)x[1],(GEN)x[k]), 1);
    for (i=2; i<=N; i++)
    {
      GEN p1, c, t, xi = (GEN)x[i];
      long base;
      if (gcmp0(xi)) continue;

      base = (i-1)*N;
      c = gcoeff(tab,k,base+i);
      t = !gcmp0(c)? gmul(c,xi): NULL;
      for (j=i+1; j<=N; j++)
      {
	c = gcoeff(tab,k,(i-1)*N+j);
	if (gcmp0(c)) continue;
        p1 = gmul(gmul2n(c,1), (GEN)x[j]);
        t = t? gadd(t, p1): p1;
      }
      if (t) s = gadd(s, gmul(xi, t));
    }
    v[k] = (long)gerepileupto(av,s);
  }
  return v;
}

/* square of x in nf */
GEN
element_sqr(GEN nf, GEN x)
{
  long N, tx = typ(x);
  GEN tab;

  nf = checknf(nf);
  if (tx==t_POLMOD) x=checknfelt_mod(nf,x,"element_sqr");
  if (is_extscalar_t(tx))
  {
    pari_sp av = avma;
    return gerepileupto(av, algtobasis(nf, gsqr(x)));
  }
  if (tx != t_COL) err(typeer,"element_sqr");

  tab = get_tab(nf, &N);
  return sqr_by_tabi(tab,x);
}

static GEN
_mul(void *data, GEN x, GEN y) { return element_mul((GEN)data,x,y); }
static GEN
_sqr(void *data, GEN x) { return element_sqr((GEN)data,x); }

/* Compute x^n in nf, left-shift binary powering */
GEN
element_pow(GEN nf, GEN x, GEN n)
{
  pari_sp av = avma;
  long s,N;
  GEN y, cx;

  if (typ(n)!=t_INT) err(talker,"not an integer exponent in nfpow");
  nf=checknf(nf); N=degpol(nf[1]);
  s=signe(n); if (!s) return gscalcol_i(gun,N);
  if (typ(x) != t_COL)
  {
    x = algtobasis(nf,x);
    if (typ(x) != t_COL) err(typeer,"element_pow");
  }

  if (isnfscalar(x))
  {
    y = gscalcol_i(gun,N);
    y[1] = (long)powgi((GEN)x[1],n); return y;
  }
  x = primitive_part(x, &cx);
  y = leftright_pow(x, n, (void*)nf, _sqr, _mul);
  if (s<0) y = element_inv(nf, y);
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
  return FpV_red(element_mulid(D->nf, x, D->I), D->p);
}
static GEN
_sqrmod(void *data, GEN x)
{
  eltmod_muldata *D = (eltmod_muldata*)data;
  return FpV_red(element_sqri(D->nf, x), D->p);
}

/* x = I-th vector of the Z-basis of Z_K, in Z^n, compute lift(x^n mod p) */
GEN
element_powid_mod_p(GEN nf, long I, GEN n, GEN p)
{
  pari_sp av = avma;
  eltmod_muldata D;
  long s,N;
  GEN y;

  if (typ(n)!=t_INT) err(talker,"not an integer exponent in nfpow");
  nf=checknf(nf); N=degpol(nf[1]);
  s=signe(n);
  if (!s || I == 1) return gscalcol_i(gun,N);
  y = zerocol(N); y[I] = un;
  D.nf = nf;
  D.p = p;
  D.I = I;
  y = leftright_pow(y,n, (void*)&D, &_sqrmod, &_mulidmod);
  if (s < 0) y = FpV_red(element_inv(nf,y), p);
  return av==avma? gcopy(y): gerepileupto(av,y);
}

GEN
element_mulidid(GEN nf, long i, long j)
{
  long N;
  GEN tab = get_tab(nf, &N);
  tab += (i-1)*N; return (GEN)tab[j];
}

/* Outputs x.w_i, where w_i is the i-th elt of the integral basis */
GEN
element_mulid(GEN nf, GEN x, long i)
{
  long j, k, N;
  GEN v, tab;

  if (i==1) return gcopy(x);
  tab = get_tab(nf, &N);
  if (typ(x) != t_COL || lg(x) != N+1) err(typeer,"element_mulid");
  tab += (i-1)*N;
  v = cgetg(N+1,t_COL);
  for (k=1; k<=N; k++)
  {
    pari_sp av = avma;
    GEN s = gzero;
    for (j=1; j<=N; j++)
    {
      GEN c = gcoeff(tab,k,j);
      if (signe(c)) s = gadd(s, _mulix(c, (GEN)x[j]));
    }
    v[k] = lpileupto(av,s);
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

/* table of multiplication by x in ZK = Z[w1,..., wN] */
GEN
eltmul_get_table(GEN nf, GEN x)
{
  long i, N = degpol(nf[1]);
  GEN mul = cgetg(N+1,t_MAT);
  x = _algtobasis(nf, x);
  mul[1] = (long)x; /* assume w_1 = 1 */
  for (i=2; i<=N; i++) mul[i] = (long)element_mulid(nf,x,i);
  return mul;
}

/* valuation of integer x, with resp. to prime ideal P above p.
 * p.P^(-1) = b Z_K, v >= val_p(norm(x)), and N = deg(nf)
 * [b may be given as the 'multiplication by b' matrix]
 */
long
int_elt_val(GEN nf, GEN x, GEN p, GEN b, GEN *newx)
{
  long i,k,w, N = degpol(nf[1]);
  GEN r,a,y,mul;
  
  mul = (typ(b) == t_MAT)? b: eltmul_get_table(nf, b);
  y = cgetg(N+1, t_COL); /* will hold the new x */
  x = dummycopy(x);
  for(w=0;; w++)
  {
    for (i=1; i<=N; i++)
    { /* compute (x.b)_i */
      a = mulii((GEN)x[1], gcoeff(mul,i,1));
      for (k=2; k<=N; k++) a = addii(a, mulii((GEN)x[k], gcoeff(mul,i,k)));
      /* is it divisible by p ? */
      y[i] = ldvmdii(a,p,&r);
      if (signe(r))
      {
        if (newx) *newx = x;
        return w;
      }
    }
    r=x; x=y; y=r;
  }
}

long
element_val(GEN nf, GEN x, GEN vp)
{
  pari_sp av = avma;
  long N,w,vcx,e;
  GEN cx,p;

  if (gcmp0(x)) return VERYBIGINT;
  nf = checknf(nf); N = degpol(nf[1]);
  checkprimeid(vp);
  p = (GEN)vp[1];
  e = itos((GEN)vp[3]);
  switch(typ(x))
  {
    case t_INT: case t_FRAC: case t_FRACN:
      return ggval(x,p)*e;
    case t_POLMOD: x = (GEN)x[2]; /* fall through */
    case t_POL:
      x = algtobasis_i(nf,x); break;
    case t_COL:
      if (lg(x)==N+1) break;
    default: err(typeer,"element_val");
  }
  if (isnfscalar(x)) return ggval((GEN)x[1],p)*e;

  cx = content(x);
  if (gcmp1(cx)) vcx=0; else { x = gdiv(x,cx); vcx = ggval(cx,p); }
  w = int_elt_val(nf,x,p,(GEN)vp[5],NULL);
  avma = av; return w + vcx*e;
}

/* polegal without comparing variables */
long
polegal_spec(GEN x, GEN y)
{
  long i = lg(x);

  if (i != lg(y)) return 0;
  for (i--; i > 1; i--)
    if (!gegal((GEN)x[i],(GEN)y[i])) return 0;
  return 1;
}

GEN
basistoalg(GEN nf, GEN x)
{
  long tx=typ(x),lx=lg(x),i,j,l;
  GEN z;

  nf=checknf(nf);
  switch(tx)
  {
    case t_COL:
      for (i=1; i<lx; i++)
      {
        long t = typ(x[i]);
	if (is_matvec_t(t)) break;
      }
      if (i==lx)
      {
        z = cgetg(3,t_POLMOD);
        z[1] = lcopy((GEN)nf[1]);
	z[2] = lmul((GEN)nf[7],x); return z;
      }
      /* fall through */

    case t_VEC: z=cgetg(lx,tx);
      for (i=1; i<lx; i++) z[i]=(long)basistoalg(nf,(GEN)x[i]);
      return z;
    case t_MAT: z=cgetg(lx,t_MAT);
      if (lx == 1) return z;
      l = lg(x[1]);
      for (j=1; j<lx; j++)
      {
        z[j] = lgetg(l,t_COL);
        for (i=1; i<l; i++) coeff(z,i,j) = (long)basistoalg(nf,gcoeff(x,i,j));
      }
      return z;

    case t_POLMOD:
      if (!polegal_spec((GEN)nf[1],(GEN)x[1]))
	err(talker,"not the same number field in basistoalg");
      return gcopy(x);
    default: z=cgetg(3,t_POLMOD);
      z[1]=lcopy((GEN)nf[1]);
      z[2]=lmul(x,polun[varn(nf[1])]); return z;
  }
}

GEN
_basistoalg(GEN nf, GEN x)
{ return typ(x) == t_COL? basistoalg(nf, x): x; }
GEN
_algtobasis(GEN nf, GEN x)
{ 
  switch(typ(x))
  {
    case t_INT:
    case t_FRAC:
    case t_FRACN: return gscalcol_i(x, degpol( checknf(nf)[1] ));
    case t_POLMOD:
    case t_POL:   return algtobasis(nf,x);
    case t_COL:   break;
    default: err(typeer,"_algtobasis");
  }
  return x;
}
GEN
_algtobasis_cp(GEN nf, GEN x)
{ return typ(x) == t_COL? gcopy(x): algtobasis(nf, x); }

/* gmul(A, pol_to_vec(x)), A t_MAT (or t_VEC) of compatible dimensions */
GEN
mulmat_pol(GEN A, GEN x)
{
  long i,l;
  GEN z;
  if (typ(x) != t_POL) return gmul(x,(GEN)A[1]); /* scalar */
  l=lg(x)-1; if (l == 1) return typ(A)==t_VEC? gzero: zerocol(lg(A[1])-1);
  x++; z = gmul((GEN)x[1], (GEN)A[1]);
  for (i=2; i<l ; i++) 
    if (!gcmp0((GEN)x[i])) z = gadd(z, gmul((GEN)x[i], (GEN)A[i]));
  return z;
}

/* valid for scalars and polynomial, degree less than N.
 * No garbage collecting. No check.  */
GEN
algtobasis_i(GEN nf, GEN x)
{
  GEN P = (GEN)nf[1];
  long tx = typ(x), N = degpol(P);

  if (tx==t_POLMOD) { x=(GEN)x[2]; tx=typ(x); }
  if (tx==t_POL)
  {
    if (varn(x) != varn(P))
      err(talker,"incompatible variables in algtobasis");
    if (degpol(x) >= N) x = gres(x,P);
    return mulmat_pol((GEN)nf[8], x);
  }
  return gscalcol(x,N);
}

GEN
algtobasis(GEN nf, GEN x)
{
  long tx=typ(x),lx=lg(x),i,N;
  pari_sp av=avma;
  GEN z;

  nf=checknf(nf);
  switch(tx)
  {
    case t_VEC: case t_COL: case t_MAT:
      z=cgetg(lx,tx);
      for (i=1; i<lx; i++) z[i]=(long)algtobasis(nf,(GEN)x[i]);
      return z;
    case t_POLMOD:
      if (!polegal_spec((GEN)nf[1],(GEN)x[1]))
	err(talker,"not the same number field in algtobasis");
      x = (GEN)x[2]; /* fall through */
    case t_POL:
      return gerepileupto(av,algtobasis_i(nf,x));

    default: N=degpol(nf[1]); return gscalcol(x,N);
  }
}

/* Given a and b in nf, gives an algebraic integer y in nf such that a-b.y
 * is "small"
 */
GEN
nfdiveuc(GEN nf, GEN a, GEN b)
{
  pari_sp av=avma, tetpil;
  a = element_div(nf,a,b); tetpil=avma;
  return gerepile(av,tetpil,ground(a));
}

/* Given a and b in nf, gives a "small" algebraic integer r in nf
 * of the form a-b.y
 */
GEN
nfmod(GEN nf, GEN a, GEN b)
{
  pari_sp av=avma,tetpil;
  GEN p1=gneg_i(element_mul(nf,b,ground(element_div(nf,a,b))));
  tetpil=avma; return gerepile(av,tetpil,gadd(a,p1));
}

/* Given a and b in nf, gives a two-component vector [y,r] in nf such
 * that r=a-b.y is "small".
 */
GEN
nfdivres(GEN nf, GEN a, GEN b)
{
  pari_sp av=avma,tetpil;
  GEN p1,z, y = ground(element_div(nf,a,b));

  p1=gneg_i(element_mul(nf,b,y)); tetpil=avma;
  z=cgetg(3,t_VEC); z[1]=lcopy(y); z[2]=ladd(a,p1);
  return gerepile(av,tetpil,z);
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
  GEN z = mpmul(gcoeff(M,k,1), (GEN)x[1]);
  for (i = 2; i < l; i++)
    z = mpadd(z, mpmul(gcoeff(M,k,i), (GEN)x[i]));
  if (lg(z) < DEFAULTPREC) err(precer,"zsigne");
  return signe(z);
}

GEN
vecconst(GEN v, GEN x)
{
  long i, l = lg(v);
  for (i = 1; i < l; i++) v[i] = (long)x;
  return v;
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
   default: err(typeer,"arch_to_perm");
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
  for (i = 1; i < l; i++) v[ archp[i] ] = un;
  return v;
}

/* reduce mod 2 in place */
GEN
F2V_red_ip(GEN v)
{
  long i, l = lg(v);
  for (i = 1; i < l; i++) v[i] = mpodd((GEN)v[i])? un: zero;
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
  switch(typ(x))
  {
    case t_MAT: /* factorisation */
    {
      GEN g = (GEN)x[1], e = (GEN)x[2], z = vecconst(V, gzero);
      for (i=1; i<lg(g); i++)
        if (mpodd((GEN)e[i])) z = gadd(z, zsigne(nf,(GEN)g[i],archp));
      for (i=1; i<l; i++) V[i] = mpodd((GEN)z[i])? un: zero;
      avma = av; return V;
    }
    case t_POLMOD: x = (GEN)x[2];      /* fall through */
    case t_POL: x = algtobasis(nf, x); /* fall through */
    case t_COL: if (!isnfscalar(x)) break;
                x = (GEN)x[1];         /* fall through */
    case t_INT: case t_FRAC:
      s = gsigne(x); if (!s) err(talker,"zero element in zsigne");
      return vecconst(V, (s < 0)? gun: gzero);
  }
  x = Q_primpart(x); M = gmael(nf,5,1);
  for (i = 1; i < l; i++) V[i] = (eval_sign(M, x, archp[i]) > 0)? zero: un;
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
  for (i=1; i<l; i++) S[i] = (long)zsigne(nf, (GEN)x[i], arch);
  return S;
}

/* For internal use. Reduce x modulo (invertible) y */
GEN
close_modinvertible(GEN x, GEN y)
{
  return gmul(y, ground(gauss(y,x)));
}
GEN
reducemodinvertible(GEN x, GEN y)
{
  return gadd(x, gneg(close_modinvertible(x,y)));
}
GEN
lllreducemodmatrix(GEN x,GEN y)
{
  return reducemodinvertible(x, lllint_ip(y,4));
}

/* Reduce column x modulo y in HNF */
GEN
colreducemodHNF(GEN x, GEN y, GEN *Q)
{
  long i, l = lg(x);
  GEN q;

  if (Q) *Q = cgetg(l,t_COL);
  if (l == 1) return cgetg(1,t_COL);
  for (i = l-1; i>0; i--)
  {
    q = negi(diviiround((GEN)x[i], gcoeff(y,i,i)));
    if (Q) (*Q)[i] = (long)q;
    if (signe(q)) x = gadd(x, gmul(q, (GEN)y[i]));
  }
  return x;
}

/* for internal use...Reduce matrix x modulo matrix y */
GEN
reducemodmatrix(GEN x, GEN y)
{
  return reducemodHNF(x, hnfmod(y,detint(y)), NULL);
}

/* x = y Q + R */
GEN
reducemodHNF(GEN x, GEN y, GEN *Q)
{
  long lx = lg(x), i;
  GEN R = cgetg(lx, t_MAT);
  if (Q)
  {
    GEN q = cgetg(lx, t_MAT); *Q = q;
    for (i=1; i<lx; i++) R[i] = (long)colreducemodHNF((GEN)x[i],y,(GEN*)(q+i));
  }
  else
    for (i=1; i<lx; i++)
    {
      pari_sp av = avma;
      R[i] = lpileupto(av, colreducemodHNF((GEN)x[i],y,NULL));
    }
  return R;
}

/* For internal use. Reduce x modulo ideal (assumed non-zero, in HNF). We
 * want a non-zero result */
GEN
nfreducemodideal_i(GEN x0,GEN ideal)
{
  GEN x = colreducemodHNF(x0, ideal, NULL);
  if (gcmp0(x)) return (GEN)ideal[1];
  return x == x0? gcopy(x) : x;
}
GEN
nfreducemodideal(GEN nf,GEN x0,GEN ideal)
{
  return nfreducemodideal_i(x0, idealhermite(nf,ideal));
}

/* multiply y by t = 1 mod^* f such that sign(x) = sign(y) at arch = idele[2].
 * If x == NULL, make y >> 0 at sarch */
GEN
set_sign_mod_idele(GEN nf, GEN x, GEN y, GEN idele, GEN sarch)
{
  GEN s,arch,gen;
  long nba,i;
  if (!sarch) return y;
  gen = (GEN)sarch[2]; nba = lg(gen);
  if (nba == 1) return y;

  arch = (GEN)idele[2];
  s = zsigne(nf, y, arch);
  if (x) s = gadd(s, zsigne(nf, x, arch));
  s = gmul((GEN)sarch[3], s);
  for (i=1; i<nba; i++)
    if (mpodd((GEN)s[i])) y = element_mul(nf,y,(GEN)gen[i]);
  return y;
}

/* compute elt = x mod idele, with sign(elt) = sign(x) at arch */
GEN
nfreducemodidele(GEN nf,GEN x,GEN idele,GEN sarch)
{
  GEN y;

  if (gcmp0(x)) return gcopy(x);
  if (!sarch || typ(idele)!=t_VEC || lg(idele)!=3)
    return nfreducemodideal(nf,x,idele);

  y = nfreducemodideal(nf,x,(GEN)idele[1]);
  y = set_sign_mod_idele(nf, x, y, idele, sarch);
  return (gexpo(y) > gexpo(x))? x: y;
}

/* assume k >= 0 */
GEN
element_powmodideal(GEN nf,GEN x,GEN k,GEN ideal)
{
  GEN y = gscalcol_i(gun,degpol(nf[1]));
  for(;;)
  {
    if (mpodd(k)) y = element_mulmodideal(nf,x,y,ideal);
    k = shifti(k,-1); if (!signe(k)) return y;
    x = element_sqrmodideal(nf,x,ideal);
  }
}

/* assume k >= 0 */
GEN
element_powmodidele(GEN nf,GEN x,GEN k,GEN idele,GEN sarch)
{
  GEN y = element_powmodideal(nf,x,k,idele);
  if (mpodd(k))
  { if (!gcmp1(k)) y = set_sign_mod_idele(nf, x, y, idele, sarch); }
  else
  { if (!gcmp0(k)) y = set_sign_mod_idele(nf, NULL, y, idele, sarch); }
  return y;
}

/* H relation matrix among row of generators g.  Let URV = D its SNF, newU R
 * newV = newD its clean SNF (no 1 in Dnew). Return the diagonal of newD,
 * newU and newUi such that  1/U = (newUi, ?).
 * Rationale: let (G,0) = g Ui be the new generators then
 * 0 = G U R --> G D = 0,  g = G newU  and  G = g newUi */
GEN
smithrel(GEN H, GEN *newU, GEN *newUi)
{ 
  GEN U, Ui, D = smithall(H, &U, NULL);
  long c, l = lg(D);

  for (c=1; c<l; c++)
  {
    GEN t = gcoeff(D,c,c);
    if (is_pm1(t)) break;
  }
  if (newU) *newU = rowextract_i(U, 1, c-1);
  if (newUi) {
    Ui = ZM_inv(U, gun); setlg(Ui, c);
    *newUi = reducemodHNF(Ui, H, NULL);
  }
  setlg(D, c); return mattodiagonal_i(D);
}

/* given 2 integral ideals x, y in HNF s.t x | y | x^2, compute the quotient
   (1+x)/(1+y) in the form [[cyc],[gen]], if U != NULL, set *U := ux^-1 */
static GEN
zidealij(GEN x, GEN y, GEN *U)
{
  GEN G, p1, cyc, z;
  long j, N;

  /* x^(-1) y = relations between the 1 + x_i (HNF) */
  cyc = smithrel(hnf_gauss(x, y), U, &G);
  N = lg(cyc); G = gmul(x,G); settyp(G, t_VEC); /* new generators */
  for (j=1; j<N; j++)
  {
    p1 = (GEN)G[j];
    p1[1] = laddsi(1, (GEN)p1[1]); /* 1 + g_j */
  }
  z = cgetg(3,t_VEC);
  z[1] = (long)cyc;
  z[2] = (long)G;
  if (U) *U = gmul(*U, ginv(x));
  return z;
}

/* smallest integer n such that g0^n=x modulo p prime. Assume g0 has order q
 * (p-1 if q = NULL) */
GEN
Fp_shanks(GEN x,GEN g0,GEN p, GEN q)
{
  pari_sp av=avma,av1,lim;
  long lbaby,i,k,c;
  GEN p1,smalltable,giant,perm,v,g0inv;

  x = modii(x,p);
  if (is_pm1(x) || egalii(p,gdeux)) { avma = av; return gzero; }
  p1 = addsi(-1, p); if (!q) q = p1;
  if (egalii(p1,x)) { avma = av; return shifti(q,-1); }
  p1 = racine(q);
  if (cmpis(p1,LGBITS) >= 0) err(talker,"module too large in Fp_shanks");
  lbaby=itos(p1)+1; smalltable=cgetg(lbaby+1,t_VEC);
  g0inv = mpinvmod(g0, p); p1 = x;

  c = 3 * lgefint(p);
  for (i=1;;i++)
  {
    av1 = avma;
    if (is_pm1(p1)) { avma=av; return stoi(i-1); }
    smalltable[i]=(long)p1; if (i==lbaby) break;
    (void)new_chunk(c); p1 = mulii(p1,g0inv); /* HACK */
    avma = av1; p1 = resii(p1, p);
  }
  giant = resii(mulii(x, mpinvmod(p1,p)), p);
  p1=cgetg(lbaby+1,t_VEC);
  perm = gen_sort(smalltable, cmp_IND | cmp_C, cmpii);
  for (i=1; i<=lbaby; i++) p1[i]=smalltable[perm[i]];
  smalltable=p1; p1=giant;

  av1 = avma; lim=stack_lim(av1,2);
  for (k=1;;k++)
  {
    i=tablesearch(smalltable,p1,cmpii);
    if (i)
    {
      v=addis(mulss(lbaby-1,k),perm[i]);
      return gerepileuptoint(av,addsi(-1,v));
    }
    p1 = resii(mulii(p1,giant), p);

    if (low_stack(lim, stack_lim(av1,2)))
    {
      if(DEBUGMEM>1) err(warnmem,"Fp_shanks, k = %ld", k);
      p1 = gerepileuptoint(av1, p1);
    }
  }
}

/* Pohlig-Hellman */
GEN
Fp_PHlog(GEN a, GEN g, GEN p, GEN ord)
{
  pari_sp av = avma;
  GEN v,t0,a0,b,q,g_q,n_q,ginv0,qj,ginv;
  GEN fa, ex;
  long e,i,j,l;

  if (!ord) ord = subis(p,1);
  if (typ(ord) == t_MAT)
  {
    fa = ord;
    ord= factorback(fa,NULL);
  }
  else
    fa = decomp(ord);
  if (typ(g) == t_INTMOD) g = lift_intern(g);
  ex = (GEN)fa[2];
  fa = (GEN)fa[1];
  l = lg(fa);
  ginv = mpinvmod(g,p);
  v = cgetg(l, t_VEC);
  for (i=1; i<l; i++)
  {
    q = (GEN)fa[i];
    e = itos((GEN)ex[i]);
    if (DEBUGLEVEL>5) 
      fprintferr("Pohlig-Hellman: DL mod %Z^%ld\n",q,e);
    qj = new_chunk(e+1); qj[0] = un;
    for (j=1; j<=e; j++) qj[j] = lmulii((GEN)qj[j-1], q);
    t0 = divii(ord, (GEN)qj[e]);
    a0 = powmodulo(a, t0, p); 
    ginv0 = powmodulo(ginv, t0, p); /* order q^e */
    g_q = powmodulo(g, divii(ord,q), p); /* order q */
    n_q = gzero;
    for (j=0; j<e; j++)
    {
      b = modii(mulii(a0, powmodulo(ginv0, n_q, p)), p);
      b = powmodulo(b, (GEN)qj[e-1-j], p);
      b = Fp_shanks(b, g_q, p, q);
      n_q = addii(n_q, mulii(b, (GEN)qj[j]));
    }
    v[i] = lmodulcp(n_q, (GEN)qj[e]);
  }
  return gerepileuptoint(av, lift(chinese(v,NULL)));
}

/* discrete log in Fq for a in Fp^*, g primitive root in Fq^* */
static GEN
ff_PHlog_Fp(GEN a, GEN g, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN q,n_q,ord,ordp;

  if (gcmp1(a)) { avma = av; return gzero; }
  if (egalii(p, gdeux)) {
    if (!signe(a)) err(talker,"a not invertible in ff_PHlog_Fp");
    avma = av; return gzero;
  }
  ordp = subis(p, 1);
  ord = T? subis(gpowgs(p,degpol(T)), 1): p;
  if (egalii(a, ordp)) /* -1 */
    return gerepileuptoint(av, shifti(ord,-1));

  if (!T) q = NULL;
  else 
  { /* we want < g > = Fp^* */
    q = divii(ord,ordp);
    g = FpXQ_pow(g,q,T,p);
    if (typ(g) == t_POL) g = constant_term(g);
  }
  n_q = Fp_PHlog(a,g,p,NULL);
  if (q) n_q = mulii(q, n_q);
  return gerepileuptoint(av, n_q);
}

/* smallest n >= 0 such that g0^n=x modulo pr, assume g0 reduced
 * q = order of g0 is prime (and != p) */
static GEN
ffshanks(GEN x, GEN g0, GEN q, GEN T, GEN p)
{
  pari_sp av = avma, av1, lim;
  long lbaby,i,k;
  GEN p1,smalltable,giant,perm,v,g0inv;

  if (!degpol(x)) x = constant_term(x);
  if (typ(x) == t_INT)
  {
    if (!gcmp1(modii(p,q))) return gzero;
    /* g0 in Fp^*, order q | (p-1) */
    if (typ(g0) == t_POL) g0 = constant_term(g0);
    return Fp_PHlog(x,g0,p,q);
  }

  p1 = racine(q);
  if (cmpis(p1,LGBITS) >= 0) err(talker,"module too large in ffshanks");
  lbaby = itos(p1)+1; smalltable = cgetg(lbaby+1,t_VEC);
  g0inv = FpXQ_inv(g0,T,p);
  p1 = x;

  for (i=1;;i++)
  {
    if (gcmp1(p1)) { avma = av; return stoi(i-1); }

    smalltable[i]=(long)p1; if (i==lbaby) break;
    p1 = FpXQ_mul(p1,g0inv, T,p);
  }
  giant = FpXQ_div(x,p1,T,p);
  perm = gen_sort(smalltable, cmp_IND | cmp_C, cmp_pol);
  smalltable = vecextract_p(smalltable, perm);
  p1 = giant;

  av1 = avma; lim=stack_lim(av1,2);
  for (k=1;;k++)
  {
    i = tablesearch(smalltable,p1,cmp_pol);
    if (i)
    {
      v = addis(mulss(lbaby-1,k), perm[i]);
      return gerepileuptoint(av, addsi(-1,v));
    }
    p1 = FpXQ_mul(p1, giant, T,p);

    if (low_stack(lim, stack_lim(av1,2)))
    {
      if(DEBUGMEM>1) err(warnmem,"ffshanks");
      p1 = gerepileupto(av1, p1);
    }
  }
}

/* same in Fp[X]/T */
GEN
ff_PHlog(GEN a, GEN g, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN v,t0,a0,b,q,g_q,n_q,ginv0,qj,ginv,ord,fa,ex;
  long e,i,j,l;

  if (typ(a) == t_INT)
    return gerepileuptoint(av, ff_PHlog_Fp(a,g,T,p));
  /* f > 1 ==> T != NULL */
  ord = subis(gpowgs(p, degpol(T)), 1);
  fa = factor(ord);
  ex = (GEN)fa[2];
  fa = (GEN)fa[1];
  l = lg(fa);
  ginv = FpXQ_inv(g,T,p);
  v = cgetg(l, t_VEC);
  for (i=1; i<l; i++)
  {
    q = (GEN)fa[i];
    e = itos((GEN)ex[i]);
    if (DEBUGLEVEL>5) fprintferr("nf_Pohlig-Hellman: DL mod %Z^%ld\n",q,e);
    qj = new_chunk(e+1); qj[0] = un;
    for (j=1; j<=e; j++) qj[j] = lmulii((GEN)qj[j-1], q);
    t0 = divii(ord, (GEN)qj[e]);
    a0 = FpXQ_pow(a, t0, T,p); 
    ginv0 = FpXQ_pow(ginv, t0, T,p); /* order q^e */
    g_q = FpXQ_pow(g, divii(ord,q), T,p); /* order q */

    n_q = gzero;
    for (j=0; j<e; j++)
    {
      b = FpXQ_mul(a0, FpXQ_pow(ginv0, n_q, T,p), T,p);
      b = FpXQ_pow(b, (GEN)qj[e-1-j], T,p);
      b = ffshanks(b, g_q, q, T,p);
      n_q = addii(n_q, mulii(b, (GEN)qj[j]));
    }
    v[i] = lmodulcp(n_q, (GEN)qj[e]);
  }
  return gerepileuptoint(av, lift(chinese(v,NULL)));
}

/* same in nf.zk / pr */
GEN
nf_PHlog(GEN nf, GEN a, GEN g, GEN pr)
{
  pari_sp av = avma;
  GEN T,p, modpr = nf_to_ff_init(nf, &pr, &T, &p);
  GEN A = nf_to_ff(nf,a,modpr);
  GEN G = nf_to_ff(nf,g,modpr);
  return gerepileuptoint(av, ff_PHlog(A,G,T,p));
}

GEN
znlog(GEN x, GEN g0)
{
  pari_sp av=avma;
  GEN p = (GEN)g0[1];
  if (typ(g0) != t_INTMOD)
    err(talker,"not an element of (Z/pZ)* in znlog");
  switch(typ(x))
  {
    case t_INT: break;
    default: x = gmul(x, gmodulsg(1,p));
    if (typ(x) != t_INTMOD)
      err(talker,"not an element of (Z/pZ)* in znlog");
    case t_INTMOD: x = (GEN)x[2]; break;
  }
  return gerepileuptoint(av, Fp_PHlog(x,(GEN)g0[2],p,NULL));
}

GEN
dethnf(GEN mat)
{
  long i,l = lg(mat);
  pari_sp av;
  GEN s;

  if (l<3) return l<2? gun: icopy(gcoeff(mat,1,1));
  av = avma; s = gcoeff(mat,1,1);
  for (i=2; i<l; i++) s = gmul(s,gcoeff(mat,i,i));
  return av==avma? gcopy(s): gerepileupto(av,s);
}

GEN
dethnf_i(GEN mat)
{
  pari_sp av;
  long i,l = lg(mat);
  GEN s;

  if (l<3) return l<2? gun: icopy(gcoeff(mat,1,1));
  av = avma; s = gcoeff(mat,1,1);
  for (i=2; i<l; i++) s = mulii(s,gcoeff(mat,i,i));
  return gerepileuptoint(av,s);
}

/* as above with cyc = diagonal(mat) */
GEN
detcyc(GEN cyc)
{
  pari_sp av;
  long i,l = lg(cyc);
  GEN s;

  if (l<3) return l<2? gun: icopy((GEN)cyc[1]);
  av = avma; s = (GEN)cyc[1];
  for (i=2; i<l; i++) s = mulii(s,(GEN)cyc[i]);
  return gerepileuptoint(av,s);
}

/* (U,V) = 1. Return y = x mod U, = 1 mod V (uv: u + v = 1, u in U, v in V) */
GEN
makeprimetoideal(GEN nf,GEN UV,GEN uv,GEN x)
{
  GEN y = gadd((GEN)uv[1], element_mul(nf,x,(GEN)uv[2]));
  return nfreducemodideal_i(y,UV);
}

static GEN
makeprimetoidealvec(GEN nf,GEN UV,GEN uv,GEN gen)
{
  long i, lx = lg(gen);
  GEN y = cgetg(lx,t_VEC);
  for (i=1; i<lx; i++)
    y[i] = (long)makeprimetoideal(nf,UV,uv,(GEN)gen[i]);
  return y;
}

GEN
FpXQ_gener(GEN T, GEN p)
{
  long i,j, k, vT = varn(T), f = degpol(T);
  GEN g, list, pf_1 = subis(gpowgs(p, f), 1);
  pari_sp av0 = avma, av;

  list = (GEN)factor(pf_1)[1];
  k = lg(list)-1;

  for (i=1; i<=k; i++) list[i] = (long)diviiexact(pf_1, (GEN)list[i]);
  for (av = avma;; avma = av)
  {
    g = FpX_rand(f, vT, p);
    if (degpol(g) < 1) continue;
    for (j=1; j<=k; j++)
      if (gcmp1(FpXQ_pow(g, (GEN)list[j], T, p))) break;
    if (j > k) return gerepilecopy(av0, g);
  }
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
  long f, e, a, b;
  GEN p, list, v, y, uv, g0, prh, prb, pre;

  if(DEBUGLEVEL>3) { fprintferr("treating pr = %Z ^ %Z\n",pr,ep); flusherr(); }
  f = itos((GEN)pr[4]);
  p = (GEN)pr[1];
  if (f == 1)
    v = gscalcol_i((GEN)gener(p)[2], degpol(nf[1]));
  else
  {
    GEN T, modpr = zk_to_ff_init(nf, &pr, &T, &p);
    v = ff_to_nf(FpXQ_gener(T,p), modpr);
    v = algtobasis(nf, v);
  }
  /* v generates  (Z_K / pr)^* */
  if(DEBUGLEVEL>3) fprintferr("v computed\n");
  prh = prime_to_ideal(nf,pr);
  e = itos(ep); pre = (e==1)? prh: idealpow(nf,pr,ep);
  if(DEBUGLEVEL>3) fprintferr("pre computed\n");
  g0 = v;
  uv = NULL; /* gcc -Wall */
  if (x)
  {
    uv = idealaddtoone(nf,pre, idealdivpowprime(nf,x,pr,ep));
    g0 = makeprimetoideal(nf,x,uv,v);
    if(DEBUGLEVEL>3) fprintferr("g0 computed\n");
  }

  list = cget1(e+1, t_VEC);
  y = cgetg(6,t_VEC); appendL(list, y);
  y[1] = (long)_vec(addis(gpowgs(p,f), -1));
  y[2] = (long)_vec(v);
  y[3] = (long)_vec(g0);
  y[4] = (long)_vec(zsigne(nf,g0,arch));
  y[5] = un;
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
    gen = dummycopy((GEN)z[2]);
    l = lg(gen); s = cgetg(l, t_VEC);
    if(DEBUGLEVEL>3) fprintferr("zidealij done\n");
    for (i = 1; i < l; i++)
    {
      if (x) gen[i] = (long)makeprimetoideal(nf,x,uv,(GEN)gen[i]);
      s[i] = (long)zsigne(nf,(GEN)gen[i],arch);
    }
    y = cgetg(6,t_VEC); appendL(list, y);
    y[1] = z[1];
    y[2] = z[2];
    y[3] = (long)gen;
    y[4] = (long)s;
    y[5] = (long)U;
  }
  return gerepilecopy(av, list);
}

/* x integral ideal, compute elements in 1+x whose sign matrix is invertible */
GEN
zarchstar(GEN nf, GEN x, GEN archp)
{
  long limr, N, i, k, r, rr, zk, lgmat, nba;
  pari_sp av;
  GEN p1, y, bas, genarch, mat, lambda, nfun, vun;

  archp = arch_to_perm(archp);
  nba = lg(archp) - 1;
  y = cgetg(4,t_VEC);
  if (!nba)
  {
    y[1] = lgetg(1,t_VEC);
    y[2] = lgetg(1,t_VEC);
    y[3] = lgetg(1,t_MAT); return y;
  }
  N = degpol(nf[1]);
  p1 = cgetg(nba+1,t_VEC); for (i=1; i<=nba; i++) p1[i] = deux;
  y[1] = (long)p1; av = avma;
  if (N == 1)
  {
    p1 = gerepileuptoint(av, subsi(1, shifti(gcoeff(x,1,1),1)));
    y[2] = (long)_vec(_col(p1));
    y[3] = (long)gscalmat(gun,1); return y;
  }
  genarch = cgetg(nba+1,t_VEC);
  mat = cgetg(nba+1,t_MAT); setlg(mat,2);
  for (i=1; i<=nba; i++) mat[i] = lgetg(nba+1, t_VECSMALL);
  lambda = cgetg(N+1, t_VECSMALL);

  bas = gmael(nf,5,1);
  bas = rowextract_p(bas, archp);
  zk = gcmp1(gcoeff(x,1,1));
  if (!zk)
  {
    x = lllint_ip(x,4);
    bas = gmul(bas, x);
  }

  vun = cgetg(nba+1, t_COL);
  for (i=1; i<=nba; i++) vun[i] = un;
  nfun = gscalcol(gun, N); lgmat = 1;
  for (r=1, rr=3; ; r<<=1, rr=(r<<1)+1)
  {
    if (DEBUGLEVEL>5) fprintferr("zarchstar: r = %ld\n",r);
    p1 = gpowgs(stoi(rr),N);
    limr = (cmpis(p1,BIGINT) >= 0)? BIGINT: p1[2];
    limr = (limr-1)>>1;
    k = zk? rr: 1; /* to avoid 0 */
    for ( ; k<=limr; k++)
    {
      pari_sp av1=avma;
      long kk = k;
      GEN alpha = vun, c;
      for (i=1; i<=N; i++)
      {
        lambda[i] = (kk+r)%rr - r; kk/=rr;
        if (lambda[i])
          alpha = gadd(alpha, gmulsg(lambda[i],(GEN)bas[i]));
      }
      c = (GEN)mat[lgmat];
      for (i=1; i<=nba; i++)
        c[i] = (gsigne((GEN)alpha[i]) < 0)? 1: 0;
      if (Flm_deplin(mat, 2)) { avma = av1; continue; }

      /* new vector indep. of previous ones */
      avma = av1; alpha = nfun;
      for (i=1; i<=N; i++)
        if (lambda[i])
          alpha = gadd(alpha, gmulsg(lambda[i],(GEN)x[i]));
      genarch[lgmat++] = (long)alpha;
      if (lgmat > nba)
      {
        mat = matsmall_mat( Flm_inv(mat, 2) );
        gerepileall(av,2,&genarch,&mat);
        y[2] = (long)genarch;
        y[3] = (long)mat; return y;
      }
      setlg(mat,lgmat+1);
    }
  }
}

/* a * g^n mod id */
static GEN
elt_mulpow_modideal(GEN nf, GEN a, GEN g, GEN n, GEN id)
{
  return element_mulmodideal(nf, a, element_powmodideal(nf,g,n,id), id);
}

static GEN
zlog_pk(GEN nf, GEN a0, GEN y, GEN pr, GEN prk, GEN list, GEN *psigne)
{
  GEN a = a0, L, e, cyc, gen, s, U;
  long i,j, llist = lg(list)-1;
  
  for (j = 1; j <= llist; j++)
  {
    L = (GEN)list[j];
    cyc = (GEN)L[1];
    gen = (GEN)L[2];
    s   = (GEN)L[4];
    U   = (GEN)L[5];
    if (j == 1)
      e = _col( nf_PHlog(nf, a, (GEN)gen[1], pr) );
    else if (typ(a) == t_INT)
      e = gmul(subis(a, 1), (GEN)U[1]);
    else
    { /* t_COL */
      GEN t = (GEN)a[1];
      a[1] = laddsi(-1, (GEN)a[1]); /* a -= 1 */
      e = gmul(U, a);
      a[1] = (long)t; /* restore */
    }
    /* here lg(e) == lg(cyc) */
    for (i = 1; i < lg(cyc); i++)
    {
      GEN t = modii(negi((GEN)e[i]), (GEN)cyc[i]);
      *++y = lnegi(t); if (!signe(t)) continue;

      if (mod2(t)) *psigne = *psigne? gadd(*psigne, (GEN)s[i]): (GEN)s[i];
      if (j != llist) a = elt_mulpow_modideal(nf, a, (GEN)gen[i], t, prk);
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
  s = gmul(gmael(lists, lg(lists)-1, 3), lift_intern(sgn));
  for (i = lg(s)-1; i > 0; i--) *--y = mpodd((GEN)s[i])? un: zero;
}

static GEN
famat_zlog(GEN nf, GEN g, GEN e, GEN bid)
{
  GEN vp = gmael(bid, 3,1), ep = gmael(bid, 3,2), arch = gmael(bid,1,2);
  GEN cyc = gmael(bid,2,2), lists = (GEN)bid[4], U = (GEN)bid[5];
  GEN y0, x, y, psigne, EX = (GEN)cyc[1];
  long i, l;

  y0 = y = cgetg(lg(U), t_COL);
  psigne = zsigne(nf, to_famat(g,e), arch);
  l = lg(vp);
  for (i=1; i < l; i++)
  {
    GEN pr = (GEN)vp[i], prk;
    prk = (l==2)? gmael(bid,1,1): idealpow(nf, pr, (GEN)ep[i]);
    /* FIXME: FIX group exponent (should be mod prk, not f !) */
    x = famat_makecoprime(nf, g, e, pr, prk, EX);
    y = zlog_pk(nf, x, y, pr, prk, (GEN)lists[i], &psigne);
  }
  zlog_add_sign(y0, psigne, lists);
  return y0;
}

static GEN
get_index(GEN lists)
{
  long t = 0, j, k, l = lg(lists)-1;
  GEN L, ind = cgetg(l+1, t_VECSMALL);

  for (k = 1; k < l; k++)
  {
    L = (GEN)lists[k];
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
  GEN ideal = (GEN)bid[1], fa = (GEN)bid[3], fa2 = (GEN)bid[4], U = (GEN)bid[5];
  GEN arch = (typ(ideal)==t_VEC && lg(ideal)==3)? (GEN)ideal[2]: NULL;
  init_zlog(S, lg(U)-1, (GEN)fa[1], (GEN)fa[2], arch, fa2, U);
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

  if (typ(a) != t_INT) a = _algtobasis(nf,a);
  if (DEBUGLEVEL>3)
  {
    fprintferr("entering zlog, "); flusherr();
    if (DEBUGLEVEL>5) fprintferr("with a = %Z\n",a);
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
    list= (GEN)S->lists[k];
    pr  = (GEN)S->P[k];
    prk = idealpow(nf, pr, (GEN)S->e[k]);
    y = zlog_pk(nf, a, y, pr, prk, list, &sgn);
  }
  zlog_add_sign(y0, sgn, S->lists);
  if (DEBUGLEVEL>3) { fprintferr("leaving\n"); flusherr(); }
  avma = av;
  for (i=1; i <= S->n; i++) y0[i] = licopy((GEN)y0[i]);
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
  GEN y, A, L, L2 = (GEN)S->lists[index];

  if (e == 1)
  {
    L = (GEN)L2[1];
    y = zerocol(S->n); y[yind + 1] = un;
    zlog_add_sign(y, gmael(L,4,1), S->lists);
    A = cgetg(2, t_MAT); A[1] = (long)y;
  }
  else
  {
    GEN pr = (GEN)S->P[index], prk, g;
    
    if (e == 2)
      L = (GEN)L2[2];
    else
      L = zidealij(idealpows(nf,pr,e-1), idealpows(nf,pr,e), NULL);
    g = (GEN)L[2];
    l = lg(g);
    A = cgetg(l, t_MAT);
    prk = idealpow(nf, pr, (GEN)S->e[index]);
    for (i = 1; i < l; i++)
    {
      GEN G = (GEN)g[i], sgn = NULL; /* positive at f_oo */
      y = zerocol(S->n);
      (void)zlog_pk(nf, G, y + yind, pr, prk, L2, &sgn);
      zlog_add_sign(y, sgn, S->lists);
      A[i] = (long)y;
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
  zlog_add_sign(y, vec_ei(lg(S->archp)-1, index), S->lists);
  return gmul(S->U, y);
}

static GEN
compute_gen(GEN nf, GEN u1, GEN gen, GEN bid)
{
  long i, c = lg(u1);
  GEN basecl = cgetg(c,t_VEC);

  for (i=1; i<c; i++)
    basecl[i] = (long)famat_to_nf_modidele(nf, gen, (GEN)u1[i], bid);
  return basecl;
}

/* Compute [[ideal,arch], [h,[cyc],[gen]], idealfact, [liste], U]
   gen not computed unless add_gen != 0 */
GEN
zidealstarinitall(GEN nf, GEN ideal,long add_gen)
{
  pari_sp av = avma;
  long i, j, k, nbp, R1, nbgen, cp;
  GEN p1, y, h, cyc, U, u1, fa, lists, e, x, arch, archp, P, sarch, gen;
  zlog_S S;

  nf = checknf(nf);
  R1 = nf_get_r1(nf);
  if (typ(ideal) == t_VEC && lg(ideal) == 3)
  {
    arch = (GEN)ideal[2]; ideal = (GEN)ideal[1];
    i = typ(arch);
    if (!is_vec_t(i) || lg(arch) != R1+1)
      err(talker,"incorrect archimedean component in zidealstarinit");
    archp = arch_to_perm(arch);
  }
  else
  {
    arch = zerovec(R1);
    archp = cgetg(1, t_VECSMALL);
  }
  x = idealhermite(nf, ideal);
  if (lg(x) == 1 || !gcmp1(denom(gcoeff(x,1,1))))
    err(talker,"zidealstarinit needs an integral non-zero ideal: %Z",x);
  ideal = cgetg(3,t_VEC);
  ideal[1] = (long)x;
  ideal[2] = (long)arch;

  fa = idealfactor(nf,x);
  P = (GEN)fa[1];
  e = (GEN)fa[2]; nbp = lg(P)-1;
  lists = cgetg(nbp+2,t_VEC);

  gen = cgetg(1,t_VEC);
  p1 = (nbp==1)? (GEN)NULL: x;
  for (i=1; i<=nbp; i++)
  {
    GEN L = zprimestar(nf,(GEN)P[i],(GEN)e[i],p1,archp);
    lists[i] = (long)L;
    for (j=1; j<lg(L); j++) gen = concatsp(gen,gmael(L,j,3));
  }
  sarch = zarchstar(nf, x, archp);
  lists[i] = (long)sarch;
  gen = concatsp(gen, (GEN)sarch[2]);

  nbgen = lg(gen)-1;
  h = cgetg(nbgen+1,t_MAT); cp = 0;
  init_zlog(&S, nbgen, P, e, archp, lists, NULL);
  for (i=1; i<=nbp; i++)
  {
    GEN L2 = (GEN)lists[i];
    for (j=1; j < lg(L2); j++)
    {
      GEN a, L = (GEN)L2[j], f = (GEN)L[1], g = (GEN)L[3];
      for (k=1; k<lg(g); k++)
      {
	a = element_powmodidele(nf, (GEN)g[k], (GEN)f[k], ideal, sarch);
	h[++cp] = lneg(zlog_ind(nf, a, &S, NULL, i));
	coeff(h,cp,cp) = f[k];
      }
    }
  }
  for (j=1; j<lg(archp); j++)
  {
    h[++cp] = (long)zerocol(nbgen);
    coeff(h,cp,cp) = deux;
  }
  if (cp != nbgen) err(bugparier, "zidealstarinit");
  h = hnfall_i(h,NULL,0);
  cyc = smithrel(h, &U, add_gen? &u1: NULL);
  p1 = cgetg(add_gen? 4: 3, t_VEC);
  p1[1] = (long)detcyc(cyc);
  p1[2] = (long)cyc;

  y = cgetg(6,t_VEC);
  y[1] = (long)ideal;
  y[2] = (long)p1;
  y[3] = (long)fa;
  y[4] = (long)lists;
  y[5] = (long)U;
  if (add_gen) p1[3] = (long)compute_gen(nf,u1,gen, y);
  return gerepilecopy(av, y);
}

GEN
zidealstarinitgen(GEN nf, GEN ideal)
{
  return zidealstarinitall(nf,ideal,1);
}

GEN
zidealstarinit(GEN nf, GEN ideal)
{
  return zidealstarinitall(nf,ideal,0);
}

GEN
zidealstar(GEN nf, GEN ideal)
{
  pari_sp av = avma;
  GEN y = zidealstarinitall(nf,ideal,1);
  return gerepilecopy(av,(GEN)y[2]);
}

GEN
idealstar0(GEN nf, GEN ideal,long flag)
{
  switch(flag)
  {
    case 0: return zidealstar(nf,ideal);
    case 1: return zidealstarinit(nf,ideal);
    case 2: return zidealstarinitgen(nf,ideal);
    default: err(flagerr,"idealstar");
  }
  return NULL; /* not reached */
}

void
check_nfelt(GEN x, GEN *den)
{
  long l = lg(x), i;
  GEN t, d = NULL;
  if (typ(x) != t_COL) err(talker,"%Z not a nfelt", x);
  for (i=1; i<l; i++)
  {
    t = (GEN)x[i];
    switch (typ(t))
    {
      case t_INT: case t_INTMOD: break;
      case t_FRACN: case t_FRAC:
        if (!d) d = (GEN)t[2]; else d = mpppcm(d, (GEN)t[2]);
        break;
      default: err(talker,"%Z not a nfelt", x);
    }
  }
  *den = d;
}

GEN
vecmodii(GEN a, GEN b)
{
  long i, l = lg(a);
  GEN c = cgetg(l, typ(a));
  for (i = 1; i < l; i++) c[i] = lmodii((GEN)a[i], (GEN)b[i]);
  return c;
}

/* Given x (not necessarily integral), and bid as output by zidealstarinit,
 * compute the vector of components on the generators bid[2].
 * Assume (x,bid) = 1 */
GEN
zideallog(GEN nf, GEN x, GEN bid)
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
    case t_INT: case t_FRAC: case t_FRACN:
      ok = 1; den = denom(x);
      break;
    case t_POLMOD: case t_POL:
      x = algtobasis(nf,x); break;
    case t_COL: break;
    case t_MAT:
      if (lg(x) == 1) return zerocol(lcyc-1);
      y = famat_zlog(nf, (GEN)x[1], (GEN)x[2], bid);
      goto END;

    default: err(talker,"not an element in zideallog");
  }
  if (!ok)
  {
    if (lg(x) != N+1) err(talker,"not an element in zideallog");
    check_nfelt(x, &den);
  }
  if (den)
  {
    GEN g = cgetg(3, t_COL);
    GEN e = cgetg(3, t_COL);
    g[1] = (long)Q_muli_to_int(x,den); e[1] = un;
    g[2] = (long)den;                  e[2] = lstoi(-1);
    y = famat_zlog(nf, g, e, bid);
  }
  else
  {
    zlog_S S; init_zlog_bid(&S, bid);
    y = zlog(nf, x, NULL, &S);
  }
END:
  y = gmul((GEN)bid[5], y);
  return gerepileupto(av, vecmodii(y, cyc));
}

/* bid1, bid2: output from 'zidealstarinit' for coprime modules m1 and m2
 * (without arch. part).
 * Output: zidealstarinit [[ideal,arch],[h,[cyc],[gen]],idealfact,[liste],U]
 * associated to m1 m2 */
GEN
zidealstarinitjoin(GEN nf, GEN bid1, GEN bid2, long add_gen)
{
  pari_sp av=avma;
  long i,nbp,nbgen,lx1,lx2,l1,l2,lx;
  GEN module1,module2,struct1,struct2,fact1,fact2,liste1,liste2;
  GEN module,liste,fact,U,U1,U2,cyc,cyc1,cyc2,uv;
  GEN p1,p2,y,u1,x,fa1,fa2, gen = add_gen? gun: NULL;

  nf = checknf(nf); checkbid(bid1); checkbid(bid2);
  module1 = (GEN)bid1[1]; struct1 = (GEN)bid1[2]; fact1 = (GEN)bid1[3];
  module2 = (GEN)bid2[1]; struct2 = (GEN)bid2[2]; fact2 = (GEN)bid2[3];
  x = idealmul(nf,(GEN)module1[1],(GEN)module2[1]);
  module = cgetg(3,t_VEC);
  module[1] = (long)x;
  module[2] = module1[2];
  if (!gcmp0((GEN)module1[2]) || !gcmp0((GEN)module2[2]))
    err(talker,"non-0 Archimedian components in zidealstarinitjoin");

  fa1 = (GEN)fact1[1]; lx1 = lg(fa1);
  fa2 = (GEN)fact2[1]; lx2 = lg(fa2);
  fact = cgetg(3,t_MAT);
  fact[1] = (long)concatsp(fa1,fa2);
  fact[2] = (long)concatsp((GEN)fact1[2],(GEN)fact2[2]);
  for (i=1; i<lx1; i++)
    if (isinvector(fa2,(GEN)fa1[i],lx2-1))
      err(talker,"noncoprime ideals in zidealstarinitjoin");

  liste1 = (GEN)bid1[4]; lx1 = lg(liste1);
  liste2 = (GEN)bid2[4]; lx2 = lg(liste2);
  /* concat (liste1 - last elt [zarchstar]) + liste2 */
  lx = lx1+lx2-2; liste = cgetg(lx,t_VEC);
  for (i=1; i<lx1-1; i++) liste[i] = liste1[i];
  for (   ; i<lx; i++)    liste[i] = liste2[i-lx1+2];

  U1 = (GEN)bid1[5]; cyc1 = (GEN)struct1[2]; l1 = lg(cyc1);
  U2 = (GEN)bid2[5]; cyc2 = (GEN)struct2[2]; l2 = lg(cyc2);
  nbgen = l1+l2-2;
  cyc = diagonal(concatsp(cyc1,cyc2));
  cyc = smithrel(cyc, &U, gen? &u1: NULL);

  if (nbgen)
    U = concatsp(
      gmul(vecextract_i(U, 1,   l1-1), U1) ,
      gmul(vecextract_i(U, l1, nbgen), U2)
    );

  if (gen)
  {
    if (lg(struct1)<=3 || lg(struct2)<=3)
      err(talker,"please apply idealstar(,,2) and not idealstar(,,1)");

    uv = idealaddtoone(nf,(GEN)module1[1],(GEN)module2[1]);
    p1 = makeprimetoidealvec(nf,x,uv,(GEN)struct1[3]);
    p2 = (GEN)uv[1]; uv[1] = uv[2]; uv[2] = (long)p2;
    p2 = makeprimetoidealvec(nf,x,uv,(GEN)struct2[3]);
    gen = concatsp(p1,p2);
    nbp = lg((GEN)fact[1])-1;
  }
  p1 = cgetg(gen? 4: 3,t_VEC);
  p1[1] = (long)detcyc(cyc);
  p1[2] = (long)cyc;

  y = cgetg(6,t_VEC);
  y[1] = (long)module;
  y[2] = (long)p1;
  y[3] = (long)fact;
  y[4] = (long)liste;
  y[5] = (long)U;
  if (gen) p1[3] = (long)compute_gen(nf,u1,gen, y);
  return gerepilecopy(av,y);
}

/* bid1: output from 'zidealstarinit' for module m1 (without arch. part)
 * arch: archimedean part.
 * Output: zidealstarinit [[ideal,arch],[h,[cyc],[gen]],idealfact,[liste],U]
 * associated to m1.arch */
GEN
zidealstarinitjoinarch(GEN nf, GEN bid1, GEN arch, long add_gen)
{
  pari_sp av=avma;
  long i, lx1;
  GEN module1,struct1,fact1,liste1,U1,U;
  GEN module,liste,cyc,p1,y,u1,x,sarch, gen = add_gen? gun: NULL;

  nf = checknf(nf); checkbid(bid1);
  module1 = (GEN)bid1[1]; struct1 = (GEN)bid1[2]; fact1 = (GEN)bid1[3];
  x = (GEN)module1[1];
  module = cgetg(3,t_VEC);
  module[1] = (long)x;
  module[2] = (long)arch;
  if (!gcmp0((GEN)module1[2]))
    err(talker,"non-0 Archimedian components in zidealstarinitjoinarch");

  sarch = zarchstar(nf, x, arch);
  liste1 = (GEN)bid1[4]; lx1 = lg(liste1);
  liste = cgetg(lx1,t_VEC);
  for (i=1; i<lx1-1; i++) liste[i]=liste1[i];
  liste[i] = (long)sarch;

  U1 = (GEN)bid1[5]; lx1 = lg(U1);
  cyc = diagonal(concatsp((GEN)struct1[2],(GEN)sarch[1]));
  cyc = smithrel(cyc, &U, gen? &u1: NULL);

  if (gen)
  {
    if (lg(struct1)<=3)
      err(talker,"please apply idealstar(,,2) and not idealstar(,,1)");
    gen = concatsp((GEN)struct1[3],(GEN)sarch[2]);
  }
  p1 = cgetg(gen? 4: 3, t_VEC);
  p1[1] = (long)detcyc(cyc);
  p1[2] = (long)cyc;

  y = cgetg(6,t_VEC);
  y[1] = (long)module;
  y[2] = (long)p1;
  y[3] = (long)fact1;
  y[4] = (long)liste;
  y[5] = (long)U;
  if (gen) p1[3] = (long)compute_gen(nf,u1,gen, y);
  return gerepilecopy(av,y);
}

/* compute matrix of zlogs of units */
GEN
logunitmatrix(GEN nf, GEN U, GEN sgnU, GEN bid)
{
  long j, l = lg(U);
  GEN m = cgetg(l, t_MAT);
  zlog_S S; init_zlog_bid(&S, bid);
  for (j = 1; j < l; j++)
    m[j] = (long)zlog(nf, (GEN)U[j], vecextract_p((GEN)sgnU[j], S.archp), &S);
  return m;
}

/* calcule la matrice des zlog des unites */
static GEN
logunitmatrixarch(GEN sgnU, GEN bid)
{
  GEN liste = (GEN)bid[4], structarch, arch = gmael(bid,1,2);
  structarch = (GEN)liste[lg(liste)-1];
  return F2V_red_ip(gmul((GEN)structarch[3],
                    rowextract_p(sgnU, arch_to_perm(arch))));
}

GEN
init_units(GEN BNF)
{
  GEN bnf = checkbnf(BNF), x = (GEN)bnf[8], v, funits;
  long i, l;
  if (lg(x) == 5) funits = (GEN)buchfu(bnf)[1];
  else
  {
    if (lg(x) != 6) err(talker,"incorrect big number field");
    funits = (GEN)x[5];
  }
  l = lg(funits) + 1;
  v = cgetg(l, t_VEC); v[1] = mael(x, 4, 2);
  for (i = 2; i < l; i++) v[i] = funits[i - 1];
  return v;
}

/*  flag &1 : generateurs, sinon non
 *  flag &2 : unites, sinon pas.
 *  flag &4 : ideaux, sinon zidealstar.
 */
static GEN
ideallistzstarall(GEN bnf,long bound,long flag)
{
  byteptr ptdif = diffptr;
  pari_sp lim, av, av0 = avma;
  long i, j, k, l, q2, lp1, q;
  long do_gen = flag & 1, do_units = flag & 2, big_id = !(flag & 4);
  GEN y,nf,p,z,z2,p1,p2,fa,pr,ideal,lu,lu2, U, sgnU, embunit;

  nf = checknf(bnf);
  if (bound <= 0) return cgetg(1,t_VEC);
  z = cgetg(bound+1,t_VEC);
  for (i=2; i<=bound; i++) z[i] = lgetg(1,t_VEC);

  ideal = idmat(degpol(nf[1]));
  if (big_id) ideal = zidealstarinitall(nf,ideal,do_gen);
  z[1] = (long)_vec(ideal);
  lu = U = sgnU = NULL; /* -Wall */
  if (do_units)
  {
    U = init_units(bnf);
    sgnU = zsignunits(bnf, NULL, 1);
    lu = cgetg(bound+1,t_VEC);
    lu[1] = (long)_vec(logunitmatrix(nf, U, sgnU, ideal));
    for (i=2; i<=bound; i++) lu[i] = lgetg(1,t_VEC);
  }

  p = cgeti(3); p[1] = evalsigne(1) | evallgefint(3);
  av = avma; lim = stack_lim(av,1);
  lu2 = embunit = NULL; /* gcc -Wall */
  maxprime_check((ulong)bound);
  for (p[2] = 0; p[2] <= bound; )
  {
    NEXT_PRIME_VIADIFF(p[2], ptdif);
    if (DEBUGLEVEL>1) { fprintferr("%ld ",p[2]); flusherr(); }
    fa = primedec(nf,p);
    for (j=1; j<lg(fa); j++)
    {
      pr = (GEN)fa[j]; p1 = powgi(p,(GEN)pr[4]);
      if (is_bigint(p1) || (q = itos(p1)) > bound) continue;

      q2 = q; ideal = pr; z2 = dummycopy(z);
      if (do_units) lu2 = dummycopy(lu);
      for (l=2; ;l++)
      {
        if (big_id) ideal = zidealstarinitall(nf,ideal,do_gen);
        if (do_units) embunit = logunitmatrix(nf, U, sgnU, ideal);
        for (i = q; i <= bound; i += q)
        {
          p1 = (GEN)z[i/q]; lp1 = lg(p1);
          if (lp1 == 1) continue;

          p2 = cgetg(lp1,t_VEC);
          for (k = 1; k < lp1; k++)
            if (big_id)
              p2[k] = (long)zidealstarinitjoin(nf,(GEN)p1[k],ideal,do_gen);
            else
              p2[k] = (long)idealmul(nf,(GEN)p1[k],ideal);
          z2[i] = (long)concatsp((GEN)z2[i],p2);
          if (do_units)
          {
            p1 = (GEN)lu[i/q];
            p2 = cgetg(lp1,t_VEC);
            for (k = 1; k < lp1; k++) p2[k] = (long)vconcat((GEN)p1[k],embunit);
            lu2[i] = (long)concatsp((GEN)lu2[i],p2);
          }
        }
        q *= q2; if ((ulong)q > (ulong)bound) break;
        ideal = idealpows(nf,pr,l);
      }
      z = z2; if (do_units) lu = lu2;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"ideallistzstarall");
      gerepileall(av, do_units?2:1, &z, &lu);
    }
  }
  if (!do_units) return gerepilecopy(av0, z);
  y = cgetg(3,t_VEC);
  y[1] = (long)z;
  for (i = 1; i < lg(z); i++)
  {
    GEN p1 = (GEN)z[i], p2 = (GEN)lu[i];
    long l = lg(p2);
    for (j = 1; j < l; j++) p2[j] = lmul(gmael(p1,j,5), (GEN)p2[j]);
  }
  y[2] = (long)lu; return gerepilecopy(av0, y);
}

GEN
ideallist0(GEN bnf,long bound, long flag)
{
  if (flag<0 || flag>4) err(flagerr,"ideallist");
  return ideallistzstarall(bnf,bound,flag);
}

GEN
ideallistzstar(GEN nf,long bound)
{
  return ideallistzstarall(nf,bound,0);
}

GEN
ideallistzstargen(GEN nf,long bound)
{
  return ideallistzstarall(nf,bound,1);
}

GEN
ideallistunit(GEN nf,long bound)
{
  return ideallistzstarall(nf,bound,2);
}

GEN
ideallistunitgen(GEN nf,long bound)
{
  return ideallistzstarall(nf,bound,3);
}

GEN
ideallist(GEN bnf,long bound)
{
  return ideallistzstarall(bnf,bound,4);
}

static GEN
ideallist_arch(GEN nf,GEN list,GEN archp,long flun)
{
  long i, j, lx, ly;
  GEN p1, z, p2;

  archp = arch_to_perm(archp);
  lx=lg(list); z=cgetg(lx,t_VEC);
  for (i=1; i<lx; i++)
  {
    p2 = (GEN)list[i]; checkbid(p2); ly = lg(p2);
    p1 = cgetg(ly,t_VEC); z[i] = (long)p1;
    for (j=1; j<ly; j++)
      p1[j] = (long)zidealstarinitjoinarch(nf, (GEN)p2[j], archp, flun);
  }
  return z;
}

static GEN
ideallistarchall(GEN bnf,GEN list,GEN arch,long flag)
{
  pari_sp av;
  long i,j,lp1, do_units = flag & 2;
  GEN nf = checknf(bnf), p1, p2, p3, lu2, lu, z, y, sgnU;

  if (typ(list) != t_VEC || (do_units && lg(list) != 3))
    err(typeer, "ideallistarch");
  if (lg(list) == 1) return cgetg(1,t_VEC);
  if (do_units)
  {
    y = cgetg(3,t_VEC);
    z = (GEN)list[1];
    lu= (GEN)list[2]; if (typ(lu) != t_VEC) err(typeer, "ideallistarch");
  }
  else
  {
    z = list;
    y = lu = NULL; /* gcc -Wall */
  }
  if (typ(z) != t_VEC) err(typeer, "ideallistarch");
  z = ideallist_arch(nf,z,arch, flag & 1);
  if (!do_units) return z;

  y[1] = (long)z; av = avma;
  sgnU = zsignunits(bnf, NULL, 1);
  lu2 = cgetg(lg(z), t_VEC);
  for (i = 1; i < lg(z); i++)
  {
    p1 = (GEN)z[i]; p2 = (GEN)lu[i]; lp1 = lg(p1);
    p3 = cgetg(lp1,t_VEC); lu2[i] = (long)p3;
    for (j = 1; j<lp1; j++)
    {
      GEN bid = (GEN)p1[j], emb = logunitmatrixarch(sgnU, bid);
      p3[j] = lmul((GEN)bid[5], vconcat((GEN)p2[j], emb));
    }
  }
  y[2] = lpilecopy(av,lu2); return y;
}

GEN
ideallistarch(GEN nf, GEN list, GEN arch)
{
  return ideallistarchall(nf,list,arch,0);
}

GEN
ideallistarchgen(GEN nf, GEN list, GEN arch)
{
  return ideallistarchall(nf,list,arch,1);
}

GEN
ideallistunitarch(GEN bnf,GEN list,GEN arch)
{
  return ideallistarchall(bnf,list,arch,2);
}

GEN
ideallistunitarchgen(GEN bnf,GEN list,GEN arch)
{
  return ideallistarchall(bnf,list,arch,3);
}

GEN
ideallistarch0(GEN nf, GEN list, GEN arch,long flag)
{
  if (!arch) arch=cgetg(1,t_VEC);
  if (flag<0 || flag>3) err(flagerr,"ideallistarch");
  return ideallistarchall(nf,list,arch,flag);
}
