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
extern GEN u_FpM_deplin(GEN x, ulong p);
extern GEN u_FpM_inv(GEN a, ulong p);
extern long ideal_is_zk(GEN ideal,long N);
extern GEN famat_ideallog(GEN nf, GEN g, GEN e, GEN bid);
extern GEN famat_to_nf_modidele(GEN nf, GEN g, GEN e, GEN bid);
extern GEN hnfall_i(GEN A, GEN *ptB, long remove);
extern GEN vconcat(GEN A, GEN B);

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
  gpmem_t av=avma, tetpil;
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

GEN
mul_by_tab(GEN tab, GEN x, GEN y)
{
  gpmem_t av;
  long i,j,k,N;
  GEN s,v,c,p1;

  N = lg(x)-1;
  v=cgetg(N+1,t_COL); av=avma;
  for (k=1; k<=N; k++)
  {
    if (k == 1)
      s = gmul((GEN)x[1],(GEN)y[1]);
    else
      s = gadd(gmul((GEN)x[1],(GEN)y[k]),
               gmul((GEN)x[k],(GEN)y[1]));
    for (i=2; i<=N; i++)
    {
      c=gcoeff(tab,k,(i-1)*N+i);
      if (signe(c))
      {
        p1 = gmul((GEN)x[i],(GEN)y[i]);
	if (!gcmp1(c)) p1 = gmul(p1,c);
	s = gadd(s, p1);
      }
      for (j=i+1; j<=N; j++)
      {
	c=gcoeff(tab,k,(i-1)*N+j);
	if (signe(c))
	{
          p1 = gadd(gmul((GEN)x[i],(GEN)y[j]),
                    gmul((GEN)x[j],(GEN)y[i]));
	  if (!gcmp1(c)) p1 = gmul(p1,c);
          s = gadd(s, p1);
	}
      }
    }
    v[k]=(long)gerepileupto(av,s); av=avma;
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
  return mul_by_tab(tab,x,y);
}

/* inverse of x in nf */
GEN
element_inv(GEN nf, GEN x)
{
  gpmem_t av=avma;
  long i,N,tx=typ(x);
  GEN p1,p;

  nf=checknf(nf); N=degpol(nf[1]);
  if (is_extscalar_t(tx))
  {
    if (tx==t_POLMOD) checknfelt_mod(nf,x,"element_inv");
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
  gpmem_t av=avma;
  long i,N,tx=typ(x),ty=typ(y);
  GEN p1,p;

  nf=checknf(nf); N=degpol(nf[1]);
  if (tx==t_POLMOD) checknfelt_mod(nf,x,"element_div");
  else if (tx==t_POL) x=gmodulcp(x,(GEN)nf[1]);

  if (ty==t_POLMOD) checknfelt_mod(nf,y,"element_div");
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
  gpmem_t av;
  long i,j,k,N;
  GEN p1,s,v,c,tab;

  tab = get_tab(nf, &N);
  v=cgetg(N+1,t_COL); av=avma;
  for (k=1; k<=N; k++)
  {
    if (k == 1)
      s = mulii((GEN)x[1],(GEN)y[1]);
    else
      s = addii(mulii((GEN)x[1],(GEN)y[k]),
                mulii((GEN)x[k],(GEN)y[1]));
    for (i=2; i<=N; i++)
    {
      c=gcoeff(tab,k,(i-1)*N+i);
      if (signe(c))
      {
        p1 = mulii((GEN)x[i],(GEN)y[i]);
        if (!gcmp1(c)) p1 = mulii(p1,c);
	s = addii(s,p1);
      }
      for (j=i+1; j<=N; j++)
      {
	c=gcoeff(tab,k,(i-1)*N+j);
	if (signe(c))
	{
          p1 = addii(mulii((GEN)x[i],(GEN)y[j]),
                     mulii((GEN)x[j],(GEN)y[i]));
          if (!gcmp1(c)) p1 = mulii(p1,c);
	  s = addii(s,p1);
	}
      }
    }
    v[k]=(long) gerepileuptoint(av,s); av=avma;
  }
  return v;
}

/* product of INTEGERS (i.e vectors with integral coeffs) x and y in nf */
GEN
element_sqri(GEN nf, GEN x)
{
  GEN p1,s,v,c,tab;
  gpmem_t av;
  long i,j,k,N;

  tab = get_tab(nf, &N);

  v=cgetg(N+1,t_COL); av=avma;
  for (k=1; k<=N; k++)
  {
    if (k == 1)
      s = sqri((GEN)x[1]);
    else
      s = shifti(mulii((GEN)x[1],(GEN)x[k]), 1);
    for (i=2; i<=N; i++)
    {
      c=gcoeff(tab,k,(i-1)*N+i);
      if (signe(c))
      {
        p1 = sqri((GEN)x[i]);
        if (!gcmp1(c)) p1 = mulii(p1,c);
	s = addii(s,p1);
      }
      for (j=i+1; j<=N; j++)
      {
	c=gcoeff(tab,k,(i-1)*N+j);
	if (signe(c))
	{
          p1 = shifti(mulii((GEN)x[i],(GEN)x[j]),1);
          if (!gcmp1(c)) p1 = mulii(p1,c);
	  s = addii(s,p1);
	}
      }
    }
    v[k]=(long) gerepileuptoint(av,s); av=avma;
  }
  return v;
}

GEN
sqr_by_tab(GEN tab, GEN x)
{
  gpmem_t av = avma;
  long i,j,k,N;
  GEN p1,s,v,c;

  N = lg(x)-1;
  if (isnfscalar(x))
  {
    s=cgetg(N+1,t_COL); s[1]=lsqr((GEN)x[1]);
    for (i=2; i<=N; i++) s[i]=lcopy((GEN)x[i]);
    return s;
  }
  v=cgetg(N+1,t_COL); av = avma;
  for (k=1; k<=N; k++)
  {
    if (k == 1)
      s = gsqr((GEN)x[1]);
    else
      s = gmul2n(gmul((GEN)x[1],(GEN)x[k]), 1);
    for (i=2; i<=N; i++)
    {
      c=gcoeff(tab,k,(i-1)*N+i);
      if (signe(c))
      {
        p1 = gsqr((GEN)x[i]);
	if (!gcmp1(c)) p1 = gmul(p1,c);
        s = gadd(s,p1);
      }
      for (j=i+1; j<=N; j++)
      {
	c=gcoeff(tab,k,(i-1)*N+j);
	if (signe(c))
	{
          p1 = gmul((GEN)x[i],(GEN)x[j]);
	  p1 = gcmp1(c)? gmul2n(p1,1): gmul(p1,shifti(c,1));
	  s = gadd(s,p1);
	}
      }
    }
    v[k]=(long)gerepileupto(av,s); av=avma;
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
    gpmem_t av = avma;
    return gerepileupto(av, algtobasis(nf, gsqr(x)));
  }
  if (tx != t_COL) err(typeer,"element_sqr");

  tab = get_tab(nf, &N);
  return sqr_by_tab(tab,x);
}

static GEN
_mul(void *data, GEN x, GEN y) { return element_mul((GEN)data,x,y); }
static GEN
_sqr(void *data, GEN x) { return element_sqr((GEN)data,x); }

/* Compute x^n in nf, left-shift binary powering */
GEN
element_pow(GEN nf, GEN x, GEN n)
{
  gpmem_t av = avma;
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
  gpmem_t av = avma;
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
  gpmem_t av;
  long j,k,N;
  GEN s,v,c,p1, tab;

  if (i==1) return gcopy(x);
  tab = get_tab(nf, &N);
  if (typ(x) != t_COL || lg(x) != N+1) err(typeer,"element_mulid");
  tab += (i-1)*N;
  v=cgetg(N+1,t_COL); av=avma;
  for (k=1; k<=N; k++)
  {
    s = gzero;
    for (j=1; j<=N; j++)
      if (signe(c = gcoeff(tab,k,j)) && !gcmp0(p1 = (GEN)x[j]))
      {
        if (!gcmp1(c)) p1 = gmul(p1,c);
	s = gadd(s,p1);
      }
    v[k]=lpileupto(av,s); av=avma;
  }
  return v;
}

/* table of multiplication by wi in ZK = Z[w1,..., wN] */
GEN
eltmulid_get_table(GEN nf, long i)
{
  long k,N;
  GEN m, tab;

  tab = get_tab(nf, &N);
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
  gpmem_t av = avma;
  long N,w,vcx,e;
  GEN cx,p;

  if (gcmp0(x)) return VERYBIGINT;
  nf=checknf(nf); N=degpol(nf[1]);
  checkprimeid(vp); p=(GEN)vp[1]; e=itos((GEN)vp[3]);
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
  avma=av; return w + vcx*e;
}

/* d = a multiple of norm(x), x integral */
long
element_val2(GEN nf, GEN x, GEN d, GEN vp)
{
  GEN p = (GEN)vp[1];
  gpmem_t av;
  long v = ggval(d,p);

  if (!v) return 0;
  av=avma;
  v = int_elt_val(nf,x,p,(GEN)vp[5],NULL);
  avma=av; return v;
}

/* polegal without comparing variables */
long
polegal_spec(GEN x, GEN y)
{
  long i = lgef(x);

  if (i != lgef(y)) return 0;
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
      if (!lx) return z;
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

/* return the (N-dimensional) vector of coeffs of p */
GEN
pol_to_vec(GEN x, long N)
{
  long i, l;
  GEN z = cgetg(N+1,t_COL);
  if (typ(x) != t_POL)
  {
    z[1] = (long)x;
    for (i=2; i<=N; i++) z[i]=zero;
    return z;
  }
  l = lgef(x)-1; x++;
  for (i=1; i<l ; i++) z[i]=x[i];
  for (   ; i<=N; i++) z[i]=zero;
  return z;
}

/* gmul(A, pol_to_vec(x)), A t_MAT (or t_VEC) of compatible dimensions */
GEN
mulmat_pol(GEN A, GEN x)
{
  long i,l;
  GEN z;
  if (typ(x) != t_POL) return gmul(x,(GEN)A[1]); /* scalar */
  l=lgef(x)-1; if (l == 1) return typ(A)==t_VEC? gzero: zerocol(lg(A[1])-1);
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
  gpmem_t av=avma;
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
  gpmem_t av=avma, tetpil;
  a = element_div(nf,a,b); tetpil=avma;
  return gerepile(av,tetpil,ground(a));
}

/* Given a and b in nf, gives a "small" algebraic integer r in nf
 * of the form a-b.y
 */
GEN
nfmod(GEN nf, GEN a, GEN b)
{
  gpmem_t av=avma,tetpil;
  GEN p1=gneg_i(element_mul(nf,b,ground(element_div(nf,a,b))));
  tetpil=avma; return gerepile(av,tetpil,gadd(a,p1));
}

/* Given a and b in nf, gives a two-component vector [y,r] in nf such
 * that r=a-b.y is "small".
 */
GEN
nfdivres(GEN nf, GEN a, GEN b)
{
  gpmem_t av=avma,tetpil;
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

/* return (column) vector of R1 signatures of x (coeff modulo 2)
 * if arch = NULL, assume arch = [0,..0]
 */
GEN
zsigne(GEN nf,GEN x,GEN arch)
{
  GEN _0,_1, vecsign, rac = (GEN)nf[6];
  long i,j,l,e,B;
  gpmem_t av0, av;

  if (!arch) return cgetg(1,t_COL);
  av0 = avma;
  l = lg(arch); vecsign = cgetg(l,t_COL);
  _0 = gmodulss(0,2);
  _1 = gmodulss(1,2); av = avma;
  switch(typ(x))
  {
    case t_MAT: /* factorisation */
    {
      GEN t = (GEN)x[1], e = (GEN)x[2];
      for (j=i=1; i<l; i++)
        if (signe(arch[i])) vecsign[j++] = (long)_0;
      setlg(vecsign,j);
      if (j==1) { avma = av0; return cgetg(1, t_COL); }
      for (i=1; i<lg(t); i++)
      {
        GEN p1 = (GEN)e[i];
        if (mpodd(p1))
          vecsign = gadd(vecsign, zsigne(nf,(GEN)t[i],arch));
      }
      return gerepileupto(av0, vecsign);
    }
    case t_COL: x = gmul((GEN)nf[7],x); break;
    case t_POLMOD: x = (GEN)x[2];
  }
  if (gcmp0(x)) err(talker,"zero element in zsigne");

  B = bit_accuracy(precision((GEN)rac[1]));
  e = gexpo(x);
  for (j=i=1; i<l; i++)
    if (signe(arch[i]))
    {
      GEN y = poleval(x,(GEN)rac[i]);
      if (lg(y) == 3 && typ(y) == t_REAL)
        err(warner,"dubious value in zsigne. Increase nf precision?");
      if (e + gexpo((GEN)rac[i]) - gexpo(y) > B)
        err(precer, "zsigne");
      vecsign[j++] = (gsigne(y) > 0)? (long)_0: (long)_1;
    }
  avma = av; setlg(vecsign,j); return vecsign;
}

GEN
lllreducemodmatrix(GEN x,GEN y)
{
  gpmem_t av = avma;
  GEN z = gmul(y,lllint(y));
  return gerepileupto(av, reducemodinvertible(x, z));
}

/* for internal use...reduce x modulo (invertible) y */
GEN
reducemodinvertible(GEN x, GEN y)
{
  return gadd(x, gneg(gmul(y, ground(gauss(y,x)))));
}

/* Reduce column x modulo y in HNF */
GEN
colreducemodmat(GEN x, GEN y, GEN *Q)
{
  long i, l = lg(x);
  GEN q;

  if (Q) *Q = cgetg(l,t_COL);
  if (l == 1) return cgetg(1,t_COL);
  for (i = l-1; i>0; i--)
  {
    q = negi(gdivround((GEN)x[i], gcoeff(y,i,i)));
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
    for (i=1; i<lx; i++) R[i] = (long)colreducemodmat((GEN)x[i],y,(GEN*)(q+i));
  }
  else
    for (i=1; i<lx; i++)
    {
      gpmem_t av = avma;
      R[i] = lpileupto(av, colreducemodmat((GEN)x[i],y,NULL));
    }
  return R;
}

/* For internal use. Reduce x modulo ideal. We want a non-zero result */
GEN
nfreducemodideal(GEN nf,GEN x0,GEN ideal)
{
  GEN y = idealhermite(nf,ideal);
  GEN x = colreducemodmat(x0, y, NULL);
  if (gcmp0(x)) return (GEN)y[1];
  return x == x0? gcopy(x) : x;
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
  s = zsigne(nf,y,arch);
  if (x) s = gadd(s, zsigne(nf,x,arch));
  s = lift_intern(gmul((GEN)sarch[3],s));
  for (i=1; i<nba; i++)
    if (signe(s[i])) y = element_mul(nf,y,(GEN)gen[i]);
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

GEN
element_powmodideal(GEN nf,GEN x,GEN k,GEN ideal)
{
  GEN y = gscalcol_i(gun,degpol(nf[1]));
  for(;;)
  {
    if (mpodd(k)) y=element_mulmodideal(nf,x,y,ideal);
    k=shifti(k,-1); if (!signe(k)) return y;
    x = element_sqrmodideal(nf,x,ideal);
  }
}

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
  GEN U,Ui,D,p1;
  long l,c;

  D = smithall(H, &U, NULL);
  l = lg(D);
  for (c=1; c<l; c++)
  {
    p1 = gcoeff(D,c,c);
    if (is_pm1(p1)) break;
  }
  if (newU) *newU = rowextract_i(U, 1, c-1);
  if (newUi) {
    Ui = ginv(U); setlg(Ui, c);
    *newUi = reducemodHNF(Ui, H, NULL);
  }
  setlg(D, c); return mattodiagonal_i(D);
}

/* given 2 integral ideals x, y in HNF s.t x | y | x^2, compute the quotient
   (1+x)/(1+y) in the form [[cyc],[gen],ux^-1]. */
static GEN
zidealij(GEN x, GEN y)
{
  GEN U,R,G,p1,cyc,z,xi;
  long j,N;

  xi = ginv(x); R = gmul(xi, y); /* relations between the 1 + x_i (HNF) */
  cyc = smithrel(R, &U, &G);
  N = lg(cyc); G = gmul(x,G); settyp(G, t_VEC); /* new generators */
  for (j=1; j<N; j++)
  {
    p1 = (GEN)G[j];
    p1[1] = laddsi(1, (GEN)p1[1]); /* 1 + g_j */
  }
  z = cgetg(4,t_VEC);
  z[1] = (long)cyc;
  z[2] = (long)G;
  z[3] = lmul(U,xi); return z;
}

/* smallest integer n such that g0^n=x modulo p prime. Assume g0 has order q
 * (p-1 if q = NULL) */
GEN
Fp_shanks(GEN x,GEN g0,GEN p, GEN q)
{
  gpmem_t av=avma,av1,lim;
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
    new_chunk(c); p1 = mulii(p1,g0inv);
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
  gpmem_t av = avma;
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

/* discrete log in Fq for a in Fp^* */
static GEN
ff_PHlog_Fp(GEN a, GEN g, GEN T, GEN p)
{
  gpmem_t av = avma;
  GEN q,n_q,ord,ordp;

  if (gcmp1(a) || egalii(p, gdeux)) { avma = av; return gzero; }

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
 * q = order of g0  (Npr - 1 if q = NULL) */
static GEN
ffshanks(GEN x, GEN g0, GEN q, GEN T, GEN p)
{
  gpmem_t av = avma, av1, lim;
  long lbaby,i,k;
  GEN p1,smalltable,giant,perm,v,g0inv;

  if (typ(x) == t_INT) return ff_PHlog_Fp(x,g0,T,p);

  /* here f > 1 ==> T != NULL */
  p1 = q? q: addsi(-1, gpowgs(p,degpol(T)));
  p1 = racine(p1);
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
  gpmem_t av = avma;
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
  gpmem_t av = avma;
  GEN T,p, modpr = nf_to_ff_init(nf, &pr, &T, &p);
  GEN A = nf_to_ff(nf,a,modpr);
  GEN G = nf_to_ff(nf,g,modpr);
  return gerepileuptoint(av, ff_PHlog(A,G,T,p));
}

GEN
znlog(GEN x, GEN g0)
{
  gpmem_t av=avma;
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
  gpmem_t av;
  GEN s;

  if (l<3) return l<2? gun: icopy(gcoeff(mat,1,1));
  av = avma; s = gcoeff(mat,1,1);
  for (i=2; i<l; i++) s = gmul(s,gcoeff(mat,i,i));
  return av==avma? gcopy(s): gerepileupto(av,s);
}

GEN
dethnf_i(GEN mat)
{
  gpmem_t av;
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
  gpmem_t av;
  long i,l = lg(cyc);
  GEN s;

  if (l<3) return l<2? gun: icopy((GEN)cyc[1]);
  av = avma; s = (GEN)cyc[1];
  for (i=2; i<l; i++) s = mulii(s,(GEN)cyc[i]);
  return gerepileuptoint(av,s);
}

/* (U,V) = 1. Return y = x mod U, = 1 mod V (uv: u + v = 1, u in U, v in V) */
static GEN
makeprimetoideal(GEN nf,GEN UV,GEN uv,GEN x)
{
  GEN y = gadd((GEN)uv[1], element_mul(nf,x,(GEN)uv[2]));
  return nfreducemodideal(nf,y,UV);
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

/* Given an ideal pr^ep, and an integral ideal x (in HNF form) compute a list
 * of vectors, each with 5 components as follows :
 * [[clh],[gen1],[gen2],[signat2],U.X^-1]. Each component corresponds to
 * d_i,g_i,g'_i,s_i.  Generators g_i are not necessarily prime to x, the
 * generators g'_i are. signat2 is the (horizontal) vector made of the
 * signatures (column vectors) of the g'_i. If x = NULL, the original ideal
 * was a prime power
 */
static GEN
zprimestar(GEN nf,GEN pr,GEN ep,GEN x,GEN arch)
{
  gpmem_t av = avma, av1, tetpil;
  long N, f, j, i, e, a, b;
  GEN prh,p,pf_1,list,v,p1,p3,p4,prk,uv,g0,newgen,pra,prb;
  GEN *gptr[2];

  if(DEBUGLEVEL>3) { fprintferr("treating pr = %Z ^ %Z\n",pr,ep); flusherr(); }
  prh = prime_to_ideal(nf,pr); N = degpol(nf[1]);
  f = itos((GEN)pr[4]);
  p = (GEN)pr[1];

  pf_1 = addis(gpowgs(p,f), -1);
  if (f==1)
  {
    v = zerocol(N);
    v[1] = gener(p)[2];
  }
  else
  {
    GEN T, modpr = nf_to_ff_init(nf, &pr, &T, &p);
    long k, vT = varn(T);

    list = (GEN)factor(pf_1)[1];
    k = lg(list)-1;
    for (i=1; i<=k; i++) list[i] = (long)diviiexact(pf_1, (GEN)list[i]);
    for (av1 = avma;; avma = av1)
    {
      p1 = FpX_rand(f, vT, p);
      if (degpol(p1) < 1) continue;
      for (j=1; j<=k; j++)
	if (gcmp1(FpXQ_pow(p1, (GEN)list[j], T, p))) break;
      if (j > k) break;
    }
    v = ff_to_nf(p1, modpr);
    v = algtobasis(nf, v);
  }
  /* v generates  (Z_K / pr)^* */
  if(DEBUGLEVEL>3) fprintferr("v computed\n");
  e = itos(ep); prk=(e==1)? pr: idealpow(nf,pr,ep);
  if(DEBUGLEVEL>3) fprintferr("prk computed\n");
  g0 = v;
  uv = NULL; /* gcc -Wall */
  if (x)
  {
    uv = idealaddtoone(nf,prk, idealdivexact(nf,x,prk));
    g0 = makeprimetoideal(nf,x,uv,v);
    if(DEBUGLEVEL>3) fprintferr("g0 computed\n");
  }

  p1 = cgetg(6,t_VEC); list = _vec(p1);
  p1[1] = (long)_vec(pf_1);
  p1[2] = (long)_vec(v);
  p1[3] = (long)_vec(g0);
  p1[4] = (long)_vec(zsigne(nf,g0,arch));
  p1[5] = un;
  if (e==1) return gerepilecopy(av, list);

  a=1; b=2; av1=avma;
  pra = prh; prb = (e==2)? prk: idealpow(nf,pr,gdeux);
  for(;;)
  {
    if(DEBUGLEVEL>3) fprintferr("  treating a = %ld, b = %ld\n",a,b);
    p1 = zidealij(pra,prb);
    newgen = dummycopy((GEN)p1[2]);
    p3 = cgetg(lg(newgen),t_VEC);
    if(DEBUGLEVEL>3) fprintferr("zidealij done\n");
    for (i=1; i<lg(newgen); i++)
    {
      if (x) newgen[i]=(long)makeprimetoideal(nf,x,uv,(GEN)newgen[i]);
      p3[i]=(long)zsigne(nf,(GEN)newgen[i],arch);
    }
    p4 = cgetg(6,t_VEC);
    p4[1] = p1[1];
    p4[2] = p1[2];
    p4[3] = (long)newgen;
    p4[4] = (long)p3;
    p4[5] = p1[3]; p4 = _vec(p4);

    a=b; b=min(e,b<<1); tetpil = avma;
    list = concat(list, p4);
    if (a==b) return gerepile(av,tetpil,list);

    pra = gcopy(prb);
    gptr[0]=&pra; gptr[1]=&list;
    gerepilemanysp(av1,tetpil,gptr,2);
    prb = (b==(a<<1))? idealpows(nf,pr,b): prk;
  }
}

/* x ideal, compute elements in 1+x whose sign matrix is invertible */
GEN
zarchstar(GEN nf,GEN x,GEN arch,long nba)
{
  long limr, N, i, j, k, r, rr, zk, lgmat;
  gpmem_t av;
  GEN p1,y,bas,genarch,mat,lambda,nfun,vun;

  if (nba < 0)
  {
    nba = 0;
    for (i=1; i<lg(arch); i++)
      if (signe(arch[i])) nba++;
  }
  y = cgetg(4,t_VEC);
  if (!nba)
  {
    y[1]=lgetg(1,t_VEC);
    y[2]=lgetg(1,t_VEC);
    y[3]=lgetg(1,t_MAT); return y;
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
  zk = ideal_is_zk(x,N);
  genarch = cgetg(nba+1,t_VEC);
  mat = cgetg(nba+1,t_MAT); setlg(mat,2);
  for (i=1; i<=nba; i++) mat[i] = lgetg(nba+1, t_VECSMALL);
  lambda = cgetg(N+1, t_VECSMALL);

  bas = dummycopy(gmael(nf,5,1)); r = lg(arch);
  for (k=1,i=1; i<r; i++)
    if (signe(arch[i]))
    {
      if (k < i)
        for (j=1; j<=N; j++) coeff(bas,k,j) = coeff(bas,i,j);
      k++;
    }
  r = nba+1; for (i=1; i<=N; i++) setlg(bas[i], r);
  if (!zk)
  {
    x = gmul(x,lllintpartial(x));
    bas = gmul(bas, x);
  }

  vun = cgetg(nba+1, t_COL);
  for (i=1; i<=nba; i++) vun[i] = un;
  nfun = gscalcol(gun, N); lgmat = 1;
  for (r=1, rr=3; ; r<<=1, rr=(r<<1)+1)
  {
    if (DEBUGLEVEL>5) fprintferr("zarchstar: r = %ld\n",r);
    p1 = gpowgs(stoi(rr),N);
    limr = is_bigint(p1)? BIGINT: p1[2];
    limr = (limr-1)>>1;
    k = zk? rr: 1; /* to avoid 0 */
    for ( ; k<=limr; k++)
    {
      gpmem_t av1=avma;
      long kk = k;
      GEN alpha = vun;
      for (i=1; i<=N; i++)
      {
        lambda[i] = (kk+r)%rr - r; kk/=rr;
        if (lambda[i])
          alpha = gadd(alpha, gmulsg(lambda[i],(GEN)bas[i]));
      }
      p1 = (GEN)mat[lgmat];
      for (i=1; i<=nba; i++)
        p1[i] = (gsigne((GEN)alpha[i]) < 0)? 1: 0;

      if (u_FpM_deplin(mat, 2)) avma = av1;
      else
      { /* new vector indep. of previous ones */
        avma = av1; alpha = nfun;
        for (i=1; i<=N; i++)
          if (lambda[i])
            alpha = gadd(alpha, gmulsg(lambda[i],(GEN)x[i]));
	genarch[lgmat++] = (long)alpha;
	if (lgmat > nba)
	{
          GEN *gptr[2];
          mat = small_to_mat( u_FpM_inv(mat, 2) );
          gptr[0]=&genarch; gptr[1]=&mat;
          gerepilemany(av,gptr,2);
	  y[2]=(long)genarch;
          y[3]=(long)mat; return y;
	}
        setlg(mat,lgmat+1);
      }
    }
  }
}

GEN
zinternallog_pk(GEN nf, GEN a0, GEN y, GEN pr, GEN prk, GEN list, GEN *psigne)
{
  GEN a = a0, L,e,p1,cyc,gen;
  long i,j, llist = lg(list)-1;
  
  e = gzero; /* gcc -Wall */
  for (j=1; j<=llist; j++)
  {
    L = (GEN)list[j]; cyc=(GEN)L[1]; gen=(GEN)L[2];
    if (j==1)
      p1 = nf_PHlog(nf,a,(GEN)gen[1],pr);
    else
    {
      p1 = (GEN)a[1]; a[1] = laddsi(-1,(GEN)a[1]);
      e = gmul((GEN)L[5],a); a[1] = (long)p1;
      /* here lg(e) == lg(cyc) */
      p1 = (GEN)e[1];
    }
    for (i=1; i<lg(cyc); i++, p1 = (GEN)e[i])
    {
      p1 = modii(negi(p1), (GEN)cyc[i]);
      *++y = lnegi(p1);
      if (!signe(p1)) continue;

      if (psigne && mpodd(p1)) *psigne = gadd(*psigne,gmael(L,4,i));
      if (j == llist) continue;

      if (DEBUGLEVEL>5) fprintferr("do element_powmodideal\n");
      p1 = element_powmodideal(nf,(GEN)gen[i],p1,prk);
      a = element_mulmodideal(nf,a,p1,prk);
    }
  }
  return y;
}

/* Retourne la decomposition de a sur les nbgen generateurs successifs
 * contenus dans list_set et si index !=0 on ne fait ce calcul que pour
 * l'ideal premier correspondant a cet index en mettant a 0 les autres
 * composantes
 */
static GEN
zinternallog(GEN nf,GEN a,GEN list_set,long nbgen,GEN arch,GEN fa,long index)
{
  GEN prlist,ep,y0,y,ainit,list,pr,prk,cyc,psigne,p1,p2;
  gpmem_t av;
  long nbp,i,j,k;

  y0 = y = cgetg(nbgen+1,t_COL); av=avma;
  prlist=(GEN)fa[1]; ep=(GEN)fa[2]; nbp=lg(ep)-1;
  i=typ(a); if (is_extscalar_t(i)) a = algtobasis(nf,a);
  if (DEBUGLEVEL>3)
  {
    fprintferr("entering zinternallog, "); flusherr();
    if (DEBUGLEVEL>5) fprintferr("with a = %Z\n",a);
  }
  ainit = a; psigne = zsigne(nf,ainit,arch);
  p2 = NULL; /* gcc -Wall */
  for (k=1; k<=nbp; k++)
  {
    list = (GEN)list_set[k];
    if (index && index!=k)
    {
      for (j=1; j<lg(list); j++)
      {
        cyc = gmael(list,j,1);
        for (i=1; i<lg(cyc); i++) *++y = zero;
      }
      continue;
    }
    pr = (GEN)prlist[k]; prk = idealpow(nf,pr,(GEN)ep[k]);
    y = zinternallog_pk(nf, ainit, y, pr, prk, list, &psigne);
  }
  p1 = lift_intern(gmul(gmael(list_set,k,3), psigne));
  avma=av; for (i=1; i<lg(p1); i++) *++y = p1[i];
  if (DEBUGLEVEL>3) { fprintferr("leaving\n"); flusherr(); }
  for (i=1; i<=nbgen; i++) y0[i] = licopy((GEN)y0[i]);
  return y0;
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
  gpmem_t av = avma;
  long i,j,k,nba,nbp,R1,nbgen,cp;
  GEN p1,y,h,cyc,U,u1,fa,fa2,ep,x,arch,list,sarch,gen;

  nf = checknf(nf); R1=itos(gmael(nf,2,1));
  if (typ(ideal)==t_VEC && lg(ideal)==3)
  {
    arch=(GEN)ideal[2]; ideal = (GEN)ideal[1];
    i = typ(arch);
    if (!is_vec_t(i) || lg(arch) != R1+1)
      err(talker,"incorrect archimedean component in zidealstarinit");
    for (nba=0,i=1; i<=R1; i++)
      if (signe(arch[i])) nba++;
  }
  else
  {
    arch=cgetg(R1+1,t_VEC);
    for (nba=0,i=1; i<=R1; i++) arch[i]=zero;
  }
  x = idealhermite(nf,ideal);
  if (!gcmp1(denom(x)))
    err(talker,"zidealstarinit needs an integral ideal: %Z",x);
  p1=cgetg(3,t_VEC); ideal=p1;
  p1[1]=(long)x;
  p1[2]=(long)arch;

  fa=idealfactor(nf,x); list=(GEN)fa[1]; ep=(GEN)fa[2];
  nbp=lg(list)-1; fa2=cgetg(nbp+2,t_VEC);

  gen = cgetg(1,t_VEC);
  p1 = (nbp==1)? (GEN)NULL: x;
  for (i=1; i<=nbp; i++)
  {
    GEN L = zprimestar(nf,(GEN)list[i],(GEN)ep[i],p1,arch);
    fa2[i] = (long)L;
    for (j=1; j<lg(L); j++) gen = concatsp(gen,gmael(L,j,3));
  }
  sarch = zarchstar(nf,x,arch,nba);
  fa2[i]=(long)sarch;
  gen = concatsp(gen,(GEN)sarch[2]);

  nbgen = lg(gen)-1;
  h=cgetg(nbgen+1,t_MAT); cp=0;
  for (i=1; i<=nbp; i++)
  {
    list = (GEN)fa2[i];
    for (j=1; j<lg(list); j++)
    {
      GEN a, L = (GEN)list[j], e = (GEN)L[1], g = (GEN)L[3];
      for (k=1; k<lg(g); k++)
      {
	a = element_powmodidele(nf,(GEN)g[k],(GEN)e[k],ideal,sarch);
	h[++cp] = lneg(zinternallog(nf,a,fa2,nbgen,arch,fa,i));
	coeff(h,cp,cp) = e[k];
      }
    }
  }
  for (j=1; j<=nba; j++) { h[++cp]=(long)zerocol(nbgen); coeff(h,cp,cp)=deux; }
  if (cp!=nbgen) err(talker,"bug in zidealstarinit");
  h = hnfall_i(h,NULL,0);
  cyc = smithrel(h, &U, add_gen? &u1: NULL);
  p1 = cgetg(add_gen? 4: 3, t_VEC);
  p1[1] = (long)detcyc(cyc);
  p1[2] = (long)cyc;

  y = cgetg(6,t_VEC);
  y[1] = (long)ideal;
  y[2] = (long)p1;
  y[3] = (long)fa;
  y[4] = (long)fa2;
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
  gpmem_t av = avma;
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

/* Given x (not necessarily integral), and bid as output by zidealstarinit,
 * compute the vector of components on the generators bid[2].
 * Assume (x,bid) = 1 */
GEN
zideallog(GEN nf, GEN x, GEN bid)
{
  gpmem_t av;
  long l,i,N,c;
  GEN fa,fa2,ideal,arch,den,p1,cyc,y;

  nf=checknf(nf); checkbid(bid);
  cyc=gmael(bid,2,2); c=lg(cyc);
  y=cgetg(c,t_COL); av=avma;
  N = degpol(nf[1]); ideal = (GEN) bid[1];
  if (typ(ideal)==t_VEC && lg(ideal)==3)
    arch = (GEN)ideal[2];
  else
    arch = NULL;
  switch(typ(x))
  {
    case t_INT: case t_FRAC: case t_FRACN:
      x = gscalcol_i(x,N); break;
    case t_POLMOD: case t_POL:
      x = algtobasis(nf,x); break;
    case t_MAT:
      return famat_ideallog(nf,(GEN)x[1],(GEN)x[2],bid);
    case t_COL: break;
    default: err(talker,"not an element in zideallog");
  }
  if (lg(x) != N+1) err(talker,"not an element in zideallog");
  check_nfelt(x, &den);
  if (den)
  {
    GEN g = cgetg(3, t_COL);
    GEN e = cgetg(3, t_COL);
    g[1] = lmul(x,den); e[1] = un;
    g[2] = (long)den;   e[2] = lstoi(-1);
    p1 = famat_ideallog(nf, g, e, bid);
  }
  else
  {
    l=lg(bid[5])-1; fa=(GEN)bid[3]; fa2=(GEN)bid[4];
    p1 = zinternallog(nf,x,fa2,l,arch,fa,0);
    p1 = gmul((GEN)bid[5],p1); /* apply smith */
  }
  if (lg(p1)!=c) err(bugparier,"zideallog");
  for (i=1; i<c; i++)
    y[i] = lmodii((GEN)p1[i],(GEN)cyc[i]);
  avma=av; /* following line does a gerepile ! */
  for (i=1; i<c; i++)
    y[i] = (long)icopy((GEN)y[i]);
  return y;
}

/* bid1, bid2: output from 'zidealstarinit' for coprime modules m1 and m2
 * (without arch. part).
 * Output: zidealstarinit [[ideal,arch],[h,[cyc],[gen]],idealfact,[liste],U]
 * associated to m1 m2 */
GEN
zidealstarinitjoin(GEN nf, GEN bid1, GEN bid2, long add_gen)
{
  gpmem_t av=avma;
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
zidealstarinitjoinarch(GEN nf, GEN bid1, GEN arch, long nba, long add_gen)
{
  gpmem_t av=avma;
  long i,nbp,lx1;
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

  sarch = zarchstar(nf,x,arch,nba);
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
    nbp = lg((GEN)fact1[1])-1;
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

/* calcule la matrice des zinternallog des unites */
GEN
logunitmatrix(GEN nf,GEN funits,GEN racunit,GEN bid)
{
  long R,j,sizeh;
  GEN m,fa2,fa,arch;

  R=lg(funits)-1; m=cgetg(R+2,t_MAT);
  fa2=(GEN)bid[4]; sizeh=lg(bid[5])-1; arch=gmael(bid,1,2);
  fa=(GEN)bid[3];
  m[1]=(long)zinternallog(nf,racunit,fa2,sizeh,arch,fa,0);
  for (j=2; j<=R+1; j++)
    m[j]=(long)zinternallog(nf,(GEN)funits[j-1],fa2,sizeh,arch,fa,0);
  return m;
}

/* calcule la matrice des zinternallog des unites */
static GEN
logunitmatrixarch(GEN nf,GEN funits,GEN racunit,GEN bid)
{
  long R,j;
  GEN m,liste,structarch,arch;

  R=lg(funits)-1; m=cgetg(R+2,t_MAT); arch=gmael(bid,1,2);
  liste=(GEN)bid[4]; structarch=(GEN)liste[lg(liste)-1];
  m[1]=(long)zsigne(nf,racunit,arch);
  for (j=2; j<=R+1; j++)
    m[j]=(long)zsigne(nf,(GEN)funits[j-1],arch);
  return lift_intern(gmul((GEN)structarch[3],m));
}

static void
init_units(GEN bnf, GEN *funits, GEN *racunit)
{
  GEN p1;
  bnf = checkbnf(bnf); p1=(GEN)bnf[8];
  if (lg(p1)==5) *funits=(GEN)buchfu(bnf)[1];
  else
  {
    if (lg(p1)!=7) err(talker,"incorrect big number field");
    *funits=(GEN)p1[5];
  }
  *racunit=gmael(p1,4,2);
}

/*  flag &1 : generateurs, sinon non
 *  flag &2 : unites, sinon pas.
 *  flag &4 : ideaux, sinon zidealstar.
 */
static GEN
ideallistzstarall(GEN bnf,long bound,long flag)
{
  byteptr ptdif=diffptr;
  gpmem_t lim,av0=avma,av;
  long i,j,k,l,q2,lp1,q;
  long do_gen = flag & 1, do_units = flag & 2, big_id = !(flag & 4);
  GEN y,nf,p,z,z2,p1,p2,p3,fa,pr,ideal,lu,lu2,funits,racunit,embunit;

  nf = checknf(bnf);
  if (bound <= 0) return cgetg(1,t_VEC);
  z = cgetg(bound+1,t_VEC);
  for (i=2; i<=bound; i++) z[i] = lgetg(1,t_VEC);

  ideal = idmat(degpol(nf[1]));
  if (big_id) ideal = zidealstarinitall(nf,ideal,do_gen);
  z[1] = (long)_vec(ideal);
  if (do_units)
  {
    init_units(bnf,&funits,&racunit);
    lu = cgetg(bound+1,t_VEC);
    for (i=2; i<=bound; i++) lu[i]=lgetg(1,t_VEC);
    lu[1] = (long)_vec(logunitmatrix(nf,funits,racunit,ideal));
  }

  p=cgeti(3); p[1]=evalsigne(1) | evallgefint(3);
  av=avma; lim=stack_lim(av,1);
  lu2 = embunit = NULL; /* gcc -Wall */
  if (bound > (long)maxprime()) err(primer1);
  for (p[2]=0; p[2]<=bound; )
  {
    p[2] += *ptdif++;
    if (DEBUGLEVEL>1) { fprintferr("%ld ",p[2]); flusherr(); }
    fa = primedec(nf,p);
    for (j=1; j<lg(fa); j++)
    {
      pr = (GEN)fa[j]; p1 = powgi(p,(GEN)pr[4]);
      if (is_bigint(p1) || (q = itos(p1)) > bound) continue;

      q2=q; ideal=pr; z2=dummycopy(z);
      if (do_units) lu2=dummycopy(lu);
      for (l=2; ;l++)
      {
        if (big_id) ideal = zidealstarinitall(nf,ideal,do_gen);
        if (do_units) embunit = logunitmatrix(nf,funits,racunit,ideal);
        for (i=q; i<=bound; i+=q)
        {
          p1 = (GEN)z[i/q]; lp1 = lg(p1);
          if (lp1 == 1) continue;

          p2 = cgetg(lp1,t_VEC);
          for (k=1; k<lp1; k++)
            if (big_id)
              p2[k] = (long)zidealstarinitjoin(nf,(GEN)p1[k],ideal,do_gen);
            else
              p2[k] = (long)idealmul(nf,(GEN)p1[k],ideal);
          z2[i] = (long)concatsp((GEN)z2[i],p2);
          if (do_units)
          {
            p1 = (GEN)lu[i/q];
            p2 = cgetg(lp1,t_VEC);
            for (k=1; k<lp1; k++)
              p2[k] = (long)vconcat((GEN)p1[k],embunit);
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
      GEN *gptr[2]; gptr[0]=&z; gptr[1]=&lu;
      if(DEBUGMEM>1) err(warnmem,"ideallistzstarall");
      gerepilemany(av,gptr,do_units?2:1);
    }
  }
  if (!do_units) return gerepilecopy(av0, z);
  y = cgetg(3,t_VEC);
  y[1] = lcopy(z);
  lu2 = cgetg(lg(z),t_VEC);
  for (i=1; i<lg(z); i++)
  {
    p1=(GEN)z[i]; p2=(GEN)lu[i]; lp1=lg(p1);
    p3=cgetg(lp1,t_VEC); lu2[i]=(long)p3;
    for (j=1; j<lp1; j++) p3[j] = lmul(gmael(p1,j,5),(GEN)p2[j]);
  }
  y[2]=(long)lu2; return gerepileupto(av0, y);
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
ideallist_arch(GEN nf,GEN list,GEN arch,long flun)
{
  long nba,i,j,lx,ly;
  GEN p1,z,p2;

  nba=0; for (i=1; i<lg(arch); i++) if (signe(arch[i])) nba++;
  lx=lg(list); z=cgetg(lx,t_VEC);
  for (i=1; i<lx; i++)
  {
    p2=(GEN)list[i]; checkbid(p2); ly=lg(p2);
    p1=cgetg(ly,t_VEC); z[i]=(long)p1;
    for (j=1; j<ly; j++)
      p1[j]=(long)zidealstarinitjoinarch(nf,(GEN)p2[j],arch,nba,flun);
  }
  return z;
}

static GEN
ideallistarchall(GEN bnf,GEN list,GEN arch,long flag)
{
  gpmem_t av;
  long i,j,lp1, do_units = flag & 2;
  GEN nf = checknf(bnf), p1,p2,p3,racunit,funits,lu2,lu,embunit,z,y;

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

  y[1]=(long)z; av=avma;
  init_units(bnf,&funits,&racunit);
  lu2=cgetg(lg(z),t_VEC);
  for (i=1; i<lg(z); i++)
  {
    p1=(GEN)z[i]; p2=(GEN)lu[i]; lp1=lg(p1);
    p3=cgetg(lp1,t_VEC); lu2[i]=(long)p3;
    for (j=1; j<lp1; j++)
    {
      embunit = logunitmatrixarch(nf,funits,racunit,(GEN)p1[j]);
      p3[j] = lmul(gmael(p1,j,5), vconcat((GEN)p2[j],embunit));
    }
  }
  y[2]=lpilecopy(av,lu2); return y;
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
