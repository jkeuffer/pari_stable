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
extern int ker_trivial_mod_p(GEN x, GEN p);
long ideal_is_zk(GEN ideal,long N);
GEN idealaddtoone_i(GEN nf, GEN x, GEN y);

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

  for (i=2; i<lx; i++)
    if (!gcmp0((GEN)x[i])) return 0;
  return 1;
}

static GEN
checknfelt_mod(GEN nf, GEN x)
{
  if (gegal((GEN)x[1],(GEN)nf[1])) return (GEN) x[2];
  err(talker,"not the same polynomial in number field operation");
  return NULL; /* not reached */
}

static GEN
scal_mul(GEN nf, GEN x, GEN y, long ty)
{
  long av=avma, tetpil;
  GEN p1;

  if (!is_extscalar_t(ty))
  {
    if (ty!=t_COL) err(typeer,"nfmul");
    y = gmul((GEN)nf[7],y);
  }
  p1 = gmul(x,y); tetpil=avma;
  return gerepile(av,tetpil,algtobasis(nf,p1));
}

/* product of x and y in nf */
GEN
element_mul(GEN nf, GEN x, GEN y)
{
  long av,i,j,k,N,tx,ty;
  GEN s,v,c,p1,tab;

  if (x == y) return element_sqr(nf,x);

  tx=typ(x); ty=typ(y);
  nf=checknf(nf); tab = (GEN)nf[9]; N=lgef(nf[1])-3;
  if (tx==t_POLMOD) x=checknfelt_mod(nf,x);
  if (ty==t_POLMOD) y=checknfelt_mod(nf,y);
  if (is_extscalar_t(tx)) return scal_mul(nf,x,y,ty);
  if (is_extscalar_t(ty)) return scal_mul(nf,y,x,tx);
  if (isnfscalar(x)) return gmul((GEN)x[1],y);
  if (isnfscalar(y)) return gmul((GEN)y[1],x);

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

/* inverse of x in nf */
GEN
element_inv(GEN nf, GEN x)
{
  long av=avma,i,N,tx=typ(x);
  GEN p1,p;

  nf=checknf(nf); N=lgef(nf[1])-3;
  if (is_extscalar_t(tx))
  {
    if (tx==t_POLMOD) checknfelt_mod(nf,x);
    else if (tx==t_POL) x=gmodulcp(x,(GEN)nf[1]);
    return gerepileupto(av, algtobasis(nf, ginv(x)));
  }
  if (isnfscalar(x))
  {
    p1=cgetg(N+1,t_COL); p1[1]=linv((GEN)x[1]);
    for (i=2; i<=N; i++) p1[i]=lcopy((GEN)x[i]);
    return p1;
  }
  p = NULL;
  for (i=1; i<=N; i++)
    if (typ(x[i])==t_INTMOD)
    {
      p = gmael(x,i,1);
      x = lift(x); break;
    }
  p1 = ginvmod(gmul((GEN)nf[7],x), (GEN)nf[1]);
  p1 = algtobasis_intern(nf,p1);

  if (p) p1 = FpV(p1, p);
  return gerepileupto(av,p1);
}

/* quotient of x and y in nf */
GEN
element_div(GEN nf, GEN x, GEN y)
{
  long av=avma,i,N,tx=typ(x),ty=typ(y);
  GEN p1,p;

  nf=checknf(nf); N=lgef(nf[1])-3;
  if (tx==t_POLMOD) checknfelt_mod(nf,x);
  else if (tx==t_POL) x=gmodulcp(x,(GEN)nf[1]);

  if (ty==t_POLMOD) checknfelt_mod(nf,y);
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

  p1 = gmul(gmul((GEN)nf[7],x), ginvmod(gmul((GEN)nf[7],y), (GEN)nf[1]));
  p1 = algtobasis_intern(nf, gres(p1, (GEN)nf[1]));
  if (p) p1 = FpV(p1,p);
  return gerepileupto(av,p1);
}

/* product of INTEGERS (i.e vectors with integral coeffs) x and y in nf */
GEN
element_muli(GEN nf, GEN x, GEN y)
{
  long av,i,j,k,N=lgef(nf[1])-3;
  GEN p1,s,v,c,tab = (GEN)nf[9];

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
  long av,i,j,k,N=lgef(nf[1])-3;
  GEN p1,s,v,c,tab = (GEN)nf[9];

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

/* square of x in nf */
GEN
element_sqr(GEN nf, GEN x)
{
  long av = avma,i,j,k,N=lgef(nf[1])-3, tx = typ(x);
  GEN p1,s,v,c, tab = (GEN)nf[9];

  if (tx==t_POLMOD) x=checknfelt_mod(nf,x);
  if (is_extscalar_t(tx))
    return gerepileupto(av, algtobasis(nf, gsqr(x)));
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

/* Compute x^n in nf, left-shift binary powering */
GEN
element_pow(GEN nf, GEN x, GEN n)
{
  long s,av=avma,N,i,j,m;
  GEN y,p1;

  if (typ(n)!=t_INT) err(talker,"not an integer exponent in nfpow");
  nf=checknf(nf); N=lgef(nf[1])-3;
  s=signe(n); if (!s) return gscalcol_i(gun,N);
  if (typ(x)!=t_COL) x=algtobasis(nf,x);

  if (isnfscalar(x))
  {
    y = gscalcol_i(gun,N);
    y[1] = (long)powgi((GEN)x[1],n); return y;
  }
  p1 = n+2; m = *p1;
  y=x; j=1+bfffo(m); m<<=j; j = BITS_IN_LONG-j;
  for (i=lgefint(n)-2;;)
  {
    for (; j; m<<=1,j--)
    {
      y = element_sqr(nf, y);
      if (m<0) y=element_mul(nf, y, x);
    }
    if (--i == 0) break;
    m = *++p1, j = BITS_IN_LONG;
  }
  if (s<0) y = element_inv(nf, y);
  return av==avma? gcopy(y): gerepileupto(av,y);
}

/* x in Z^n, compute lift(x^n mod p) */
GEN
element_pow_mod_p(GEN nf, GEN x, GEN n, GEN p)
{
  long s,av=avma,N,i,j,m;
  GEN y,p1;

  if (typ(n)!=t_INT) err(talker,"not an integer exponent in nfpow");
  nf=checknf(nf); N=lgef(nf[1])-3;
  s=signe(n); if (!s) return gscalcol_i(gun,N);
  if (typ(x)!=t_COL) x=algtobasis(nf,x);

  if (isnfscalar(x))
  {
    y = gscalcol_i(gun,N);
    y[1] = (long)powmodulo((GEN)x[1],n,p); return y;
  }
  p1 = n+2; m = *p1;
  y=x; j=1+bfffo(m); m<<=j; j = BITS_IN_LONG-j;
  for (i=lgefint(n)-2;;)
  {
    for (; j; m<<=1,j--)
    {
      y = element_sqri(nf, y);
      if (m<0) y=element_muli(nf, y, x);
      y = FpV_red(y, p);
    }
    if (--i == 0) break;
    m = *++p1, j = BITS_IN_LONG;
  }
  if (s<0)  y = FpV_red(element_inv(nf,y), p);
  return av==avma? gcopy(y): gerepileupto(av,y);
}

/* x = I-th vector of the Z-basis of Z_K, in Z^n, compute lift(x^n mod p) */
GEN
element_powid_mod_p(GEN nf, long I, GEN n, GEN p)
{
  long s,av=avma,N,i,j,m;
  GEN y,p1;

  if (typ(n)!=t_INT) err(talker,"not an integer exponent in nfpow");
  nf=checknf(nf); N=lgef(nf[1])-3;
  s=signe(n);
  if (!s || I == 1) return gscalcol_i(gun,N);
  p1 = n+2; m = *p1;
  y = zerocol(N); y[I] = un;
  j=1+bfffo(m); m<<=j; j = BITS_IN_LONG-j;
  for (i=lgefint(n)-2;;)
  {
    for (; j; m<<=1,j--)
    {
      y = element_sqri(nf, y);
      if (m<0) y=element_mulid(nf, y, I);
      y = FpV_red(y, p);
    }
    if (--i == 0) break;
    m = *++p1, j = BITS_IN_LONG;
  }
  if (s<0)  y = FpV_red(element_inv(nf,y), p);
  return av==avma? gcopy(y): gerepileupto(av,y);
}

/* Outputs x.w_i, where w_i is the i-th elt of the integral basis */
GEN
element_mulid(GEN nf, GEN x, long i)
{
  long av,j,k,N;
  GEN s,v,c,p1, tab;

  if (i==1) return gcopy(x);
  N = lgef(nf[1])-3;
  if (typ(x) != t_COL || lg(x) != N+1) err(typeer,"element_mulid");
  tab = (GEN)nf[9]; tab += (i-1)*N;
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

/* valuation of integer x, with resp. to prime ideal P above p.
 * p.P^(-1) = b Z_K, v <= val_p(norm(x)), and N = deg(nf)
 */
long
int_elt_val(GEN nf, GEN x, GEN p, GEN b, long v)
{
  long i,k,w, N = lgef(nf[1])-3;
  GEN r,a,y, mul = cgetg(N+1,t_MAT);

  for (i=1; i<=N; i++) mul[i] = (long)element_mulid(nf,b,i);
  y = cgetg(N+1, t_COL); /* will hold the new x */
  x = dummycopy(x);
  for(w=0; w<=v; w++)
  {
    for (i=1; i<=N; i++)
    { /* compute (x.b)_i */
      a = mulii((GEN)x[1], gcoeff(mul,i,1));
      for (k=2; k<=N; k++) a = addii(a, mulii((GEN)x[k], gcoeff(mul,i,k)));
      /* is it divisible by p ? */
      y[i] = ldvmdii(a,p,&r);
      if (signe(r)) return w;
    }
    r=x; x=y; y=r;
  }
  return w;
}

long
element_val(GEN nf, GEN x, GEN vp)
{
  long av = avma,N,w,vcx,e;
  GEN cx,p;

  if (gcmp0(x)) return VERYBIGINT;
  nf=checknf(nf); N=lgef(nf[1])-3;
  checkprimeid(vp); p=(GEN)vp[1]; e=itos((GEN)vp[3]);
  switch(typ(x))
  {
    case t_INT: case t_FRAC: case t_FRACN:
      return ggval(x,p)*e;
    case t_POLMOD: x = (GEN)x[2]; /* fall through */
    case t_POL:
      x = algtobasis_intern(nf,x); break;
    case t_COL:
      if (lg(x)==N+1) break;
    default: err(typeer,"element_val");
  }
  if (isnfscalar(x)) return ggval((GEN)x[1],p)*e;

  cx = content(x);
  if (gcmp1(cx)) vcx=0; else { x = gdiv(x,cx); vcx = ggval(cx,p); }
  w = int_elt_val(nf,x,p,(GEN)vp[5],VERYBIGINT);
  avma=av; return w + vcx*e;
}

/* d = a multiple of norm(x), x integral */
long
element_val2(GEN nf, GEN x, GEN d, GEN vp)
{
  GEN p = (GEN)vp[1];
  long av, v = ggval(d,p);

  if (!v) return 0;
  av=avma;
  v = int_elt_val(nf,x,p,(GEN)vp[5],v);
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
  long tx=typ(x),lx=lg(x),i;
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

    case t_VEC: case t_MAT: z=cgetg(lx,tx);
      for (i=1; i<lx; i++) z[i]=(long)basistoalg(nf,(GEN)x[i]);
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
  long i,l=lgef(x)-1;
  GEN z = cgetg(N+1,t_COL);
  x++;
  for (i=1; i<l ; i++) z[i]=x[i];
  for (   ; i<=N; i++) z[i]=zero;
  return z;
}

/* gmul(A, pol_to_vec(x)), A matrix of compatible dimensions */
GEN
mulmat_pol(GEN A, GEN x)
{
  long i,l;
  GEN z;
  if (typ(x) != t_POL) return gscalcol(x, lg(A[1])-1);
  l=lgef(x)-1; if (l == 1) return zerocol(lg(A[1])-1);
  x++; z = gmul((GEN)x[1], (GEN)A[1]);
  for (i=2; i<l ; i++) 
    if (!gcmp0((GEN)x[i]))z = gadd(z, gmul((GEN)x[i], (GEN)A[i]));
  return z;
}

/* valid for scalars and polynomial, degree less than N.
 * No garbage collecting. No check (SEGV for vectors).
 */
GEN
algtobasis_intern(GEN nf,GEN x)
{
  GEN z, P = (GEN)nf[1];
  long i, tx = typ(x), N = lgef(P)-3;

  if (tx==t_POLMOD) { x=(GEN)x[2]; tx=typ(x); }
  if (tx==t_POL)
  {
    if (varn(x) != varn(P))
      err(talker,"incompatible variables in algtobasis");
    if (lgef(x)-3 >= N) x=gres(x,P);
    return mulmat_pol((GEN)nf[8], x);
  }
  z = cgetg(N+1,t_COL);
  z[1]=lcopy(x); for (i=2; i<=N; i++) z[i]=zero;
  return z;
}

GEN
algtobasis(GEN nf, GEN x)
{
  long tx=typ(x),lx=lg(x),av=avma,i,N;
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
      return gerepileupto(av,algtobasis_intern(nf,x));

    default: N=lgef(nf[1])-3; return gscalcol(x,N);
  }
}

/* Given a and b in nf, gives an algebraic integer y in nf such that a-b.y
 * is "small"
 */
GEN
nfdiveuc(GEN nf, GEN a, GEN b)
{
  long av=avma, tetpil;
  a = element_div(nf,a,b); tetpil=avma;
  return gerepile(av,tetpil,ground(a));
}

/* Given a and b in nf, gives a "small" algebraic integer r in nf
 * of the form a-b.y
 */
GEN
nfmod(GEN nf, GEN a, GEN b)
{
  long av=avma,tetpil;
  GEN p1=gneg_i(element_mul(nf,b,ground(element_div(nf,a,b))));
  tetpil=avma; return gerepile(av,tetpil,gadd(a,p1));
}

/* Given a and b in nf, gives a two-component vector [y,r] in nf such
 * that r=a-b.y is "small".
 */
GEN
nfdivres(GEN nf, GEN a, GEN b)
{
  long av=avma,tetpil;
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
  long av, i,j,l,e,B;

  if (!arch) return cgetg(1,t_COL);
  switch(typ(x))
  {
    case t_COL: x = gmul((GEN)nf[7],x); break;
    case t_POLMOD: x = (GEN)x[2];
  }
  if (gcmp0(x)) err(talker,"zero element in zsigne");

  l = lg(arch); vecsign = cgetg(l,t_COL);
  _0 = gmodulss(0,2);
  _1 = gmodulss(1,2); av = avma;
  B = bit_accuracy(precision((GEN)rac[1]));
  e = gexpo(x);
  for (j=1,i=1; i<l; i++)
    if (signe(arch[i]))
    {
      GEN y = poleval(x,(GEN)rac[i]);
      if (e + gexpo((GEN)rac[i]) - gexpo(y) > B)
        err(talker, "precision too low in zsigne");
      vecsign[j++] = (gsigne(y) > 0)? (long)_0: (long)_1;
    }
  avma = av; setlg(vecsign,j); return vecsign;
}

/* For internal use. Reduce x modulo ideal. We want a non-zero result */
GEN
nfreducemodideal(GEN nf,GEN x,GEN ideal)
{
  long N = lg(x)-1, do_copy = 1, i;
  GEN p1,q;

  ideal=idealhermite(nf,ideal);
  for (i=N; i>=1; i--)
  {
    p1=gcoeff(ideal,i,i); q=gdivround((GEN)x[i],p1);
    if (signe(q)) { x=gsub(x,gmul(q,(GEN)ideal[i])); do_copy=0; }
  }
  if (gcmp0(x)) return (GEN) ideal[1];
  return do_copy? gcopy(x) : x;
}

/* a usage interne...Reduction de la colonne x modulo la matrice y inversible
   utilisant LLL */
GEN
lllreducemodmatrix(GEN x,GEN y)
{
  long av = avma,tetpil;
  GEN z = gmul(y,lllint(y));

  z = gneg(gmul(z, ground(gauss(z,x))));
  tetpil=avma; return gerepile(av,tetpil,gadd(x,z));
}

/* Reduce column x modulo y in HNF */
static GEN
colreducemodmat(GEN x, GEN y, GEN *Q)
{
  long i, l = lg(x), av = avma;
  GEN q;

  if (Q) *Q = cgetg(l,t_COL);
  if (l == 1) return cgetg(1,t_COL);
  for (i = l-1; i>0; i--)
  {
    q = negi(gdivround((GEN)x[i], gcoeff(y,i,i)));
    if (Q) (*Q)[i] = (long)q;
    if (signe(q)) x = gadd(x, gmul(q, (GEN)y[i]));
  }
  return Q? x: gerepileupto(av,x);
}

/* for internal use...Reduce matrix x modulo matrix y */
GEN
reducemodmatrix(GEN x, GEN y)
{
  if (DEBUGLEVEL>=8)
  {
    fprintferr("entering reducemodmatrix; avma-bot = %ld\n",avma-bot);
    flusherr();
  }
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
    for (i=1; i<lx; i++) R[i] = (long)colreducemodmat((GEN)x[i],y,NULL);
  return R;
}

/* compute elt = x mod idele, with sign(elt) = sign(x) at arch */
GEN
nfreducemodidele(GEN nf,GEN x,GEN idele,GEN sarch)
{
  GEN p1,p2,arch,gen;
  long nba,i;

  if (gcmp0(x)) return gcopy(x);
  if (!sarch || typ(idele)!=t_VEC || lg(idele)!=3)
    return nfreducemodideal(nf,x,idele);

  arch =(GEN)idele[2];
  nba = lg(sarch[1]);
  gen =(GEN)sarch[2];
  p1 = nfreducemodideal(nf,x,(GEN)idele[1]);
  p2 = gadd(zsigne(nf,p1,arch), zsigne(nf,x,arch));
  p2 = lift_intern(gmul((GEN)sarch[3],p2));
  for (i=1; i<nba; i++)
    if (signe(p2[i])) p1 = element_mul(nf,p1,(GEN)gen[i]);
  return (gcmp(gnorml2(p1),gnorml2(x)) > 0)? x: p1;
}

GEN
element_powmodideal(GEN nf,GEN x,GEN k,GEN ideal)
{
  GEN y = gscalcol_i(gun,lgef(nf[1])-3);
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
  GEN y = gscalcol_i(gun,lgef(nf[1])-3);
  for(;;)
  {
    if (mpodd(k)) y=element_mulmodidele(nf,x,y,idele,sarch);
    k=shifti(k,-1); if (!signe(k)) return y;
    x = element_sqrmodidele(nf,x,idele,sarch);
  }
}

/* given 2 integral ideals x, y in HNF s.t x|y|x^2, compute the quotient
   (1+x)/(1+y) in the form [[cyc],[gen],ux^-1]. */
static GEN
zidealij(GEN x, GEN y)
{
  GEN p1,p2,p3,p4,d,z,x1;
  long j,N,c;

  if(DEBUGLEVEL>5)
    {fprintferr("entering zidealij; avma = %ld\n",avma); flusherr();}
  x1 = ginv(x);
  p1 = gmul(x1,y);
  p2 = smith2(p1);
  p3 = ginv((GEN)p2[1]);
  p3 = reducemodmatrix(p3,p1);
  p3 = gmul(x,p3); N=lg(p3)-1;
  for (j=1; j<=N; j++) coeff(p3,1,j)=laddsi(1,gcoeff(p3,1,j));
  p4 = smithclean(p2); d=(GEN)p4[3];
  if(DEBUGLEVEL>5) {fprintferr("done; avma = %ld\n",avma); flusherr();}

  z=cgetg(4,t_VEC); c=lg(d); p1=cgetg(c,t_VEC);
  /* transform p3 into a vector */
  p3[0] = evaltyp(t_VEC) | evallg(c);
  for (j=1; j<c; j++) p1[j] = coeff(d,j,j);
  z[1]=(long)p1;
  z[2]=(long)p3;
  z[3] = lmul((GEN)p4[1],x1); return z;
}

#if 0
/* un element g generateur d'un p^k divisant x etant donne, calcule
   un element congru a g modulo p^k et a 1 modulo x/p^k et de plus
   positif aux places de arch */
GEN
zconvert(GEN nf,GEN uv,GEN x,GEN arch,GEN structarch,GEN g)
{
  long i,nba;
  GEN p1,p2,generator;

  p1=nfreducemodideal(nf,gadd((GEN)uv[1],element_mul(nf,g,(GEN)uv[2])),x);
  nba=lg(structarch[1])-1; generator=(GEN)structarch[2];
  p2 = zsigne(nf,p1,arch);
  for (i=1; i<=nba; i++)
    if (signe(p2[i])) p1 = element_mul(nf,p1,(GEN)generator[i]);
  return p1;
}
#endif

static GEN
get_multab(GEN nf, GEN x)
{
  long lx = lg(x), i;
  GEN multab = cgetg(lx, t_MAT);
  for (i=1; i<lx; i++)
    multab[i]=(long)element_mulid(nf,x,i);
  return multab;
}

/* return mat * y mod prh */
static GEN
mul_matvec_mod_pr(GEN mat, GEN y, GEN prh)
{
  long av,i,j, lx = lg(mat);
  GEN v, res = cgetg(lx,t_COL), p = gcoeff(prh,1,1);

  av = avma; (void)new_chunk((lx-1) * lgefint(p));
  v = zerocol(lx-1);
  for (i=lx-1; i; i--)
  {
    GEN p1 = (GEN)v[i], t = (GEN)prh[i];
    for (j=1; j<lx; j++)
      p1 = addii(p1, mulii(gcoeff(mat,i,j), (GEN)y[j]));
    p1 = modii(p1, p);
    if (p1 != gzero && is_pm1(t[i]))
    {
      for (j=1; j<i; j++)
        v[j] = lsubii((GEN)v[j], mulii(p1, (GEN)t[j]));
      p1 = gzero;
    }
    if (p1 == gzero) /* intended */
      res[i] = zero;
    else
      av = res[i] = (long)icopy_av(p1, (GEN)av);
  }
  avma = av; return res;
}

/* smallest integer n such that g0^n=x modulo p prime */
static GEN
Fp_shanks(GEN x,GEN g0,GEN p)
{
  long av=avma,av1,lim,lbaby,i,k,c;
  GEN p1,smalltable,giant,perm,v,g0inv;

  x = modii(x,p);
  if (is_pm1(x) || egalii(p,gdeux)) { avma = av; return gzero; }
  p1 = addsi(-1, p);
  if (egalii(p1,x)) { avma = av; return shifti(p,-1); }
  p1 = racine(p1);
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

/* smallest integer n such that g0^n=x modulo pr, assume g0 reduced  */
/* TODO: should be done in F_(p^f), not in Z_k mod pr (done for f=1) */
GEN
nfshanks(GEN nf,GEN x,GEN g0,GEN pr,GEN prhall)
{
  long av=avma,av1,lim,lbaby,i,k, f = itos((GEN)pr[4]);
  GEN p1,smalltable,giant,perm,v,g0inv,prh = (GEN)prhall[1];
  GEN multab, p = (GEN)pr[1];

  x = lift_intern(nfreducemodpr(nf,x,prhall));
  if (f == 1) return gerepileuptoint(av, Fp_shanks((GEN)x[1],(GEN)g0[1],p));
  p1 = addsi(-1, gpowgs(p,f));
  if (isnfscalar(x))
  {
    x = (GEN)x[1];
    if (gcmp1(x) || egalii((GEN)pr[1], gdeux)) { avma = av; return gzero; }
    if (egalii(x, p1)) return gerepileuptoint(av,shifti(p1,-1));
    v = divii(p1, addsi(-1,p));
    g0 = lift_intern((GEN)element_powmodpr(nf,g0,v,prhall)[1]);
    return gerepileuptoint(av, mulii(v, Fp_shanks(x,g0,p)));
  }
  p1 = racine(p1);
  if (cmpis(p1,LGBITS) >= 0) err(talker,"module too large in nfshanks");
  lbaby=itos(p1)+1; smalltable=cgetg(lbaby+1,t_VEC);
  g0inv = lift_intern(element_invmodpr(nf,g0,prhall));
  p1 = x;

  multab = get_multab(nf, g0inv);
  for (i=lg(multab)-1; i; i--)
    multab[i]=(long)FpV_red((GEN)multab[i], p);

  for (i=1;;i++)
  {
    if (isnfscalar(p1) && gcmp1((GEN)p1[1])) { avma=av; return stoi(i-1); }

    smalltable[i]=(long)p1; if (i==lbaby) break;
    p1 = mul_matvec_mod_pr(multab,p1,prh);
  }
  giant=lift_intern(element_divmodpr(nf,x,p1,prhall));
  p1=cgetg(lbaby+1,t_VEC);
  perm = gen_sort(smalltable, cmp_IND | cmp_C, cmp_vecint);
  for (i=1; i<=lbaby; i++) p1[i]=smalltable[perm[i]];
  smalltable=p1; p1=giant;

  multab = get_multab(nf, giant);
  for (i=lg(multab)-1; i; i--)
    multab[i]=(long)FpV_red((GEN)multab[i], p);

  av1 = avma; lim=stack_lim(av1,2);
  for (k=1;;k++)
  {
    i=tablesearch(smalltable,p1,cmp_vecint);
    if (i)
    {
      v=addis(mulss(lbaby-1,k),perm[i]);
      return gerepileuptoint(av,addsi(-1,v));
    }
    p1 = mul_matvec_mod_pr(multab,p1,prh);

    if (low_stack(lim, stack_lim(av1,2)))
    {
      if(DEBUGMEM>1) err(warnmem,"nfshanks");
      p1 = gerepileupto(av1, p1);
    }
  }
}

GEN
znlog(GEN x, GEN g0)
{
  long av=avma;
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
  return gerepileuptoint(av, Fp_shanks(x,(GEN)g0[2],p));
}

GEN
dethnf(GEN mat)
{
  long av,i,l = lg(mat);
  GEN s;

  if (l<3) return l<2? gun: icopy(gcoeff(mat,1,1));
  av = avma; s = gcoeff(mat,1,1);
  for (i=2; i<l; i++) s = gmul(s,gcoeff(mat,i,i));
  return av==avma? gcopy(s): gerepileupto(av,s);
}

GEN
dethnf_i(GEN mat)
{
  long av,i,l = lg(mat);
  GEN s;

  if (l<3) return l<2? gun: icopy(gcoeff(mat,1,1));
  av = avma; s = gcoeff(mat,1,1);
  for (i=2; i<l; i++) s = mulii(s,gcoeff(mat,i,i));
  return gerepileuptoint(av,s);
}

static GEN
makeprimetoideal(GEN nf,GEN id,GEN uv,GEN x)
{
  GEN p1 = gadd((GEN)uv[1], element_mul(nf,x,(GEN)uv[2]));
  return nfreducemodideal(nf,p1,id);
}

static GEN
makeprimetoidealvec(GEN nf,GEN ideal,GEN uv,GEN listgen)
{
  long i, lx = lg(listgen);
  GEN y = cgetg(lx,t_VEC);

  for (i=1; i<lx; i++)
    y[i] = (long)makeprimetoideal(nf,ideal,uv,(GEN)listgen[i]);
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
  long av=avma,av1,N,f,nbp,j,n,m,tetpil,i,e,a,b;
  GEN prh,p,pf_1,list,v,p1,p2,p3,p4,prk,uv,g0,newgen,pra,prb;
  GEN *gptr[2];

  if(DEBUGLEVEL>=4)
    { fprintferr("treating pr = %Z ^ %Z\n",pr,ep); flusherr(); }
  prh=prime_to_ideal(nf,pr); N=lg(prh)-1;
  f=itos((GEN)pr[4]); p=(GEN)pr[1];

  pf_1 = addis(gpowgs(p,f), -1);
  v = zerocol(N);
  if (f==1) v[1]=gener(p)[2];
  else
  {
    GEN prhall = cgetg(3,t_VEC);
    long psim;
    if (is_bigint(p)) err(talker,"prime too big in zprimestar");
    psim = itos(p);
    list = (GEN)factor(pf_1)[1]; nbp=lg(list)-1;
    prhall[1]=(long)prh; prhall[2]=zero;
    for (n=psim; n>=0; n++)
    {
      m=n;
      for (i=1; i<=N; i++)
	if (!gcmp1(gcoeff(prh,i,i))) { v[i]=lstoi(m%psim); m/=psim; }
      for (j=1; j<=nbp; j++)
      {
        p1 = divii(pf_1,(GEN)list[j]);
	p1 = lift_intern(element_powmodpr(nf,v,p1,prhall));
        if (isnfscalar(p1) && gcmp1((GEN)p1[1])) break;
      }
      if (j>nbp) break;
    }
    if (n < 0) err(talker,"prime too big in zprimestar");
  }
  /* v generates  (Z_K / pr)^* */
  if(DEBUGLEVEL>=4) {fprintferr("v calcule\n");flusherr();}
  e = itos(ep); prk=(e==1)? pr: idealpow(nf,pr,ep);
  if(DEBUGLEVEL>=4) {fprintferr("prk calcule\n");flusherr();}
  g0 = v;
  uv = NULL; /* gcc -Wall */
  if (x)
  {
    uv = idealaddtoone(nf,prk,idealdivexact(nf,x,prk));
    g0 = makeprimetoideal(nf,x,uv,v);
  }
  if(DEBUGLEVEL>=4) {fprintferr("g0 calcule\n");flusherr();}

  list=cgetg(2,t_VEC);
  p1=cgetg(6,t_VEC); list[1]=(long)p1; p1[5]=un;
  p2=cgetg(2,t_VEC); p1[1]=(long)p2; p2[1]=(long)pf_1;
  p2=cgetg(2,t_VEC); p1[2]=(long)p2; p2[1]=(long)v;
  p2=cgetg(2,t_VEC); p1[3]=(long)p2; p2[1]=(long)g0;
  p2=cgetg(2,t_VEC); p1[4]=(long)p2; p2[1]=(long)zsigne(nf,g0,arch);
  if (e==1)
  {
    tetpil=avma; return gerepile(av,tetpil,gcopy(list));
  }

  a=1; b=2; av1=avma;
  pra = prh; prb = (e==2)? prk: idealpow(nf,pr,gdeux);
  for(;;)
  {
    if(DEBUGLEVEL>=4)
      {fprintferr("on traite a = %ld, b = %ld\n",a,b); flusherr();}
    p1 = zidealij(pra,prb);
    newgen = dummycopy((GEN)p1[2]);
    p3 = cgetg(lg(newgen),t_VEC);
    if(DEBUGLEVEL>=4) {fprintferr("zidealij fait\n"); flusherr();}
    for (i=1; i<lg(newgen); i++)
    {
      if (x) newgen[i]=(long)makeprimetoideal(nf,x,uv,(GEN)newgen[i]);
      p3[i]=(long)zsigne(nf,(GEN)newgen[i],arch);
    }
    p2=cgetg(2,t_VEC); p4=cgetg(6,t_VEC); p2[1]=(long)p4;
    p4[1] = p1[1];
    p4[2] = p1[2];
    p4[3] = (long)newgen;
    p4[4] = (long)p3;
    p4[5] = p1[3];

    a=b; b=min(e,b<<1); tetpil = avma;
    list = concat(list,p2);
    if (a==b) return gerepile(av,tetpil,list);

    pra = gcopy(prb);
    gptr[0]=&pra; gptr[1]=&list;
    gerepilemanysp(av1,tetpil,gptr,2);
    prb = (b==(a<<1))? idealpow(nf,pra,gdeux): prk;
  }
}

/* x ideal, compute elements in 1+x whose sign matrix is invertible */
GEN
zarchstar(GEN nf,GEN x,GEN arch,long nba)
{
  long av,N,i,j,k,r,rr,limr,zk,lgmat;
  GEN p1,y,bas,genarch,mat,lambda;

  if (!nba)
  {
    y=cgetg(4,t_VEC);
    y[1]=lgetg(1,t_VEC);
    y[2]=lgetg(1,t_VEC);
    y[3]=lgetg(1,t_MAT); return y;
  }
  N=lgef(nf[1])-3; y=cgetg(4,t_VEC);
  p1=cgetg(nba+1,t_VEC); for (i=1; i<=nba; i++) p1[i]=deux;
  y[1]=(long)p1; av = avma;
  if (N==1)
  {
    p1 = scalarpol(subsi(1, shifti(gcoeff(x,1,1),1)), varn(nf[1]));
    p1 = gerepileupto(av, p1);
    y[2]=lgetg(2,t_VEC); mael(y,2,1) = (long)p1;
    y[3]=(long)gscalmat(gun,1); return y;
  }
  zk = ideal_is_zk(x,N);
  x = gmul(x,lllintpartial(x));
  genarch = cgetg(nba+1,t_VEC);
  mat = cgetg(nba+1,t_MAT); setlg(mat,2);
  for (i=1; i<=nba; i++) mat[i] = lgetg(nba+1, t_MAT);
  lambda = new_chunk(N+1);

  bas = dummycopy(gmael(nf,5,1)); r = lg(arch);
  for (k=1,i=1; i<r; i++)
    if (signe(arch[i]))
    {
      if (k < i)
        for (j=1; j<=N; j++) coeff(bas,k,j) = coeff(bas,i,j);
      k++;
    }
  r = nba+1;
  for (i=1; i<=N; i++) setlg(bas[i], r);
  bas = gmul(bas, x);

  for (lgmat=1,r=1, rr=3; ; r<<=1, rr=(r<<1)+1)
  {
    if (DEBUGLEVEL>5) fprintferr("zarchstar: r = %ld\n",r);
    p1 = gpuigs(stoi(rr),N);
    limr = (cmpis(p1,BIGINT) > 0)? BIGINT: p1[2];
    limr = (limr-1)>>1;
    k = zk? rr: 1; /* to avoid 0 */
    for ( ; k<=limr; k++)
    {
      long av1=avma, kk = k;
      GEN alpha = gzero;
      for (i=1; i<=N; i++)
      {
        lambda[i] = (kk+r)%rr - r; kk/=rr;
        if (lambda[i])
          alpha = gadd(alpha, gmulsg(lambda[i],(GEN)bas[i]));
      }
      for (i=1; i<=nba; i++)
        alpha[i] = ladd((GEN)alpha[i], gun);
      p1 = (GEN)mat[lgmat];
      for (i=1; i<=nba; i++)
        p1[i] = (gsigne((GEN)alpha[i]) > 0)? zero: un;

      if (ker_trivial_mod_p(mat, gdeux)) avma = av1;
      else
      { /* new vector indep. of previous ones */
        avma = av1; alpha = gzero;
        for (i=1; i<=N; i++)
          if (lambda[i])
            alpha = gadd(alpha, gmulsg(lambda[i],(GEN)x[i]));
        alpha[1] = ladd((GEN)alpha[1], gun);
	genarch[lgmat++] = (long)alpha;
	if (lgmat > nba)
	{
          GEN *gptr[2];
          mat = ginv(mat); gptr[0]=&genarch; gptr[1]=&mat;
          gerepilemany(av,gptr,2);
	  y[2]=(long)genarch;
          y[3]=(long)mat; return y;
	}
        setlg(mat,lgmat+1);
      }
    }
  }
}

/* Retourne la decomposition de a sur les nbgen generateurs successifs
 * contenus dans list_set et si index !=0 on ne fait ce calcul que pour
 * l'ideal premier correspondant a cet index en mettant a 0 les autres
 * composantes
 */
static GEN
zinternallog(GEN nf,GEN list_set,long nbgen,GEN arch,GEN fa,GEN a,long index)
{
  GEN prlist,ep,y,ainit,list,pr,prk,cyc,gen,psigne,p1,p2,p3;
  long av,nbp,cp,i,j,k;

  y = cgetg(nbgen+1,t_COL); cp=0; av=avma;
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
    list=(GEN)list_set[k];
    if (index && index!=k)
    {
      for (j=1; j<lg(list); j++)
      {
        cyc = gmael(list,j,1);
        for (i=1; i<lg(cyc); i++) y[++cp]=zero;
      }
      continue;
    }
    pr=(GEN)prlist[k]; prk=idealpow(nf,pr,(GEN)ep[k]);
    for (j=1; j<lg(list); j++)
    {
      p1 = (GEN)list[j]; cyc=(GEN)p1[1]; gen=(GEN)p1[2];
      if (j==1)
      {
        if (DEBUGLEVEL>5) { fprintferr("do nfshanks\n"); flusherr(); }
        a=ainit; p3=nfmodprinit(nf,pr);
        p3 = nfshanks(nf,a,(GEN)gen[1],pr,p3);
      }
      else
      {
        p3 = (GEN)a[1]; a[1] = laddsi(-1,(GEN)a[1]);
        p2 = gmul((GEN)p1[5],a); a[1] = (long)p3;
        if (lg(p2)!=lg(cyc)) err(bugparier,"zinternallog");
        p3 = (GEN)p2[1];
      }
      for(i=1;;)
      {
        p3 = modii(negi(p3), (GEN)cyc[i]);
        y[++cp] = lnegi(p3);
        if (signe(p3))
        {
          if (mpodd((GEN)y[cp])) psigne = gadd(psigne,gmael(p1,4,i));
          if (DEBUGLEVEL>5) fprintferr("do element_powmodideal\n");
          p3 = element_powmodideal(nf,(GEN)gen[i],p3,prk);
          a = element_mulmodideal(nf,a,p3,prk);
        }
        i++; if (i==lg(cyc)) break;
        /* never reached if j = 1 since lg(cyc) = 2 */
        p3 = (GEN)p2[i];
      }
    }
  }
  p1=lift_intern(gmul(gmael(list_set,nbp+1,3), psigne));
  avma=av; for (i=1; i<lg(p1); i++) y[++cp] = p1[i];
  if (DEBUGLEVEL>3) { fprintferr("leaving\n"); flusherr(); }
  for (i=1; i<=nbgen; i++) y[i] = licopy((GEN)y[i]);
  return y;
}

GEN
compute_gen(GEN nf, GEN u1, GEN met, GEN gen, GEN module, long nbp, GEN sarch)
{
  long i,j,s,nba, c = lg(met), lgen = lg(gen);
  GEN basecl=cgetg(c,t_VEC), unnf = gscalcol_i(gun, lgef(nf[1])-3);
  GEN arch,x,p1,p2,p3,p4,p5,generator;

  if (sarch)
  {
    arch = (GEN)module[2];
    x = (GEN)module[1];
    generator = (GEN)sarch[2];
    nba = lg(generator)-1;
  }
  else
  {
    x = (typ(module) == t_MAT)? module: (GEN)module[1];
    nba = 0;
    arch = generator = NULL; /* gcc -Wall */
  }
  for (j=1; j<c; j++)
  {
    GEN *op, plus = unnf, minus = unnf;

    for (i=1; i<lgen; i++)
    {
      p1 = gcoeff(u1,i,j);
      if (!(s = signe(p1))) continue;

      if (s > 0) op = &plus; else { op = &minus; p1 = negi(p1); }
      p1 = element_powmodidele(nf,(GEN)gen[i],p1,module,sarch);
      *op = *op==unnf? p1: element_mulmodidele(nf,*op,p1,module,sarch);
    }
    if (nbp)
    {
      p5=idealaddtoone_i(nf,minus,x);
      p4=element_div(nf,p5,minus); /* = minus^(-1) mod x */
      p3=element_mulmodideal(nf,plus,p4,x);
    }
    else p3=unnf;

    if (nba)
    { /* correct so that sign(p3) == sign(plus/minus) */
      p4=gadd(gadd(zsigne(nf,p3,arch),
                   zsigne(nf,plus,arch)),
                   zsigne(nf,minus,arch));
      p2=lift_intern(gmul((GEN)sarch[3],p4));
      for (i=1; i<=nba; i++)
        if (signe(p2[i])) p3=element_mul(nf,p3,(GEN)generator[i]);
    }
    basecl[j]=(long)p3;
  }
  return basecl;
}

/* Compute [[ideal,arch], [h,[cyc],[gen]], idealfact, [liste], U]
   gen not computed unless add_gen != 0 */
GEN
zidealstarinitall(GEN nf, GEN ideal,long add_gen)
{
  long av=avma,tetpil,i,j,k,nba,nbp,R1,nbgen,cp;
  GEN p1,p2,p3,p4,y,h,met,u1,u1u2,u1u2clean,fa,fa2,ep,x,arch,gen,list,sarch;

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
    err(talker,"zidealstarinit needs an integral ideal. x =\n%Z",x);
  p1=cgetg(3,t_VEC); ideal=p1;
  p1[1]=(long)x;
  p1[2]=(long)arch;

  fa=idealfactor(nf,x); list=(GEN)fa[1]; ep=(GEN)fa[2];
  nbp=lg(list)-1; fa2=cgetg(nbp+2,t_VEC);

  /* compute them */
  gen = cgetg(1,t_VEC);
  p2 = (nbp==1)? (GEN)NULL: x;
  for (i=1; i<=nbp; i++)
  {
    p1 = zprimestar(nf,(GEN)list[i],(GEN)ep[i],p2,arch);
    fa2[i]=(long)p1;
    for (j=1; j<lg(p1); j++)
      gen = concatsp(gen,gmael(p1,j,3));
  }
  sarch = zarchstar(nf,x,arch,nba);
  fa2[i]=(long)sarch;
  gen = concatsp(gen,(GEN)sarch[2]);
  nbgen = lg(gen)-1;
  h=cgetg(nbgen+1,t_MAT); cp=0;
  for (i=1; i<=nbp; i++)
  {
    list=(GEN)fa2[i];
    for (j=1; j<lg(list); j++)
    {
      p1=(GEN)list[j]; p2=(GEN)p1[1]; p3=(GEN)p1[3];
      for (k=1; k<lg(p3); k++)
      {
	if (DEBUGLEVEL>=6)
          { fprintferr("entering element_powmodidele\n"); flusherr(); }
	p4 = element_powmodidele(nf,(GEN)p3[k],(GEN)p2[k],ideal,sarch);
	h[++cp] = lneg(zinternallog(nf,fa2,nbgen,arch,fa,p4,i));
	coeff(h,cp,cp) = p2[k];
      }
    }
  }
  for (j=1; j<=nba; j++)
    { h[++cp]=(long)zerocol(nbgen); coeff(h,cp,cp)=deux; }
  if (cp!=nbgen) err(talker,"bug in zidealstarinit");
  u1u2 = smith2(h); u1u2clean = smithclean(u1u2);
  met=(GEN)u1u2clean[3];
  if (add_gen)
  {
    u1 = reducemodmatrix(ginv((GEN)u1u2[1]),h);
    p1 = cgetg(4,t_VEC);
    p1[3] = (long)compute_gen(nf,u1,met,gen,ideal, nbp,sarch);
  }
  else p1 = cgetg(3,t_VEC);
  y = cgetg(6,t_VEC);
  y[1]=(long)ideal;
  y[2]=(long)p1;
    p1[1]=(long)dethnf(met);
    p1[2]=(long)mattodiagonal(met);
  y[3]=(long)fa;
  y[4]=(long)fa2;
  y[5] = u1u2clean[1];
  tetpil=avma; return gerepile(av,tetpil,gcopy(y));
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
  long av = avma,tetpil;
  GEN y = zidealstarinitall(nf,ideal,1);
  tetpil=avma; return gerepile(av,tetpil,gcopy((GEN)y[2]));
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

/* x is not integral, but check that v_p(x)=0 for all prime divisors of the
 * ideal. We need x = a/b with integral a and b, prime to ideal
 * denmat = den * id.
 */
static GEN
rat_zinternallog(GEN nf, GEN x, GEN bigideal, GEN denmat)
{
  long nbp,i,v,k, N = lgef(nf[1])-3;
  GEN den,fa,list,ep,pr,p1,p2,p3,x1,dinv,ideal;

  ideal = (GEN)bigideal[1];
  if (lg(ideal) == 3) ideal = (GEN)ideal[1];
  fa=(GEN)bigideal[3]; list=(GEN)fa[1]; ep=(GEN)fa[2];
  den=gmael(denmat,1,1); k=1; nbp=lg(list)-1;
  for (i=1; i<=nbp; i++)
  {
    pr=(GEN)list[i];
    v = (ggval(den,(GEN)pr[1])*itos((GEN)pr[3])) / itos((GEN)ep[i]) + 1;
    if (v>k) k=v;
  }
  p3=idealpow(nf,ideal,stoi(k));
  p1=idealadd(nf,denmat,p3); dinv=idealinv(nf,p1);
  p2=idealmullll(nf,denmat,dinv);
  p3=idealmullll(nf,p3,dinv);
  x1=idealaddtoone_i(nf,p2,p3);
  if (gcmp0(x1)) x1 = (GEN)denmat[1];
  /* x = a/b is suitable, with a=x1*x, b=x1 */
  p1=element_mul(nf,x1,x);
  /* x1 is prime to ideal. Check that x1 * x also */
  p2=idealadd(nf,p1,ideal);
  if (! ideal_is_zk(p2,N))
    err(talker,"element is not coprime to ideal in zideallog");
  p1=zideallog(nf,p1,bigideal);
  p2=zideallog(nf,x1,bigideal);
  return gsub(p1,p2);
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
 * compute the vector of components on the generators bid[2]
 */
GEN
zideallog(GEN nf, GEN x, GEN bid)
{
  long av,l,i,N,c;
  GEN fa,fa2,ideal,arch,den,p1,cyc,y;

  nf=checknf(nf); checkbid(bid);
  cyc=gmael(bid,2,2); c=lg(cyc);
  y=cgetg(c,t_COL); av=avma;
  N = lgef(nf[1])-3; ideal = (GEN) bid[1];
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
    case t_COL: break;
    default: err(talker,"not an element in zideallog");
  }
  if (lg(x) != N+1) err(talker,"not an element in zideallog");
  check_nfelt(x, &den);
  if (den)
    p1 = rat_zinternallog(nf,x,bid, gscalmat(den,N));
  else
  {
    l=lg(bid[5])-1; fa=(GEN)bid[3]; fa2=(GEN)bid[4];
    p1 = zinternallog(nf,fa2,l,arch,fa,x,0);
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

/* Etant donnes bid1, bid2 resultats de zidealstarinit pour deux modules m1
 * et m2 premiers entre eux sans partie archimedienne, calcule le
 * zidealstarinit [[ideal,arch],[h,[cyc],[gen]],idealfact,[liste],U] du
 * produit
 */
static GEN
zidealstarinitjoinall(GEN nf, GEN bid1, GEN bid2, long add_gen)
{
  long av=avma,i,j,nbp,nbgen,lx1,lx2,llx1,llx2,lx,llx;
  GEN module1,module2,struct1,struct2,fact1,fact2,liste1,liste2,U1,U2;
  GEN module,liste,fact,U,cyc,ex1,ex2,uv;
  GEN p1,p2,y,met,u1;
  GEN fa1,fa2,gen,u1u2,u1u2clean;

  nf=checknf(nf); checkbid(bid1); checkbid(bid2);
  module1=(GEN)bid1[1]; struct1=(GEN)bid1[2]; fact1=(GEN)bid1[3];
  module2=(GEN)bid2[1]; struct2=(GEN)bid2[2]; fact2=(GEN)bid2[3];
  module=cgetg(3,t_VEC);
  module[1]=(long)idealmul(nf,(GEN)module1[1],(GEN)module2[1]);
  module[2]=ladd((GEN)module1[2],(GEN)module2[2]);
  if (gcmpgs(vecmax((GEN)module[2]),1)>=0)
    err(talker,"nontrivial Archimedian components in zidealstarinitjoin");

  fa1=(GEN)fact1[1]; ex1=(GEN)fact1[2];
  fa2=(GEN)fact2[1]; ex2=(GEN)fact2[2];
  fact=cgetg(3,t_MAT);
  fact[1]=lconcat(fa1,fa2); lx1=lg(fa1);
  fact[2]=lconcat(ex1,ex2); lx2=lg(fa2);
  nbp=lx1+lx2-2;
  for (i=1; i<lx1; i++)
    if (isinvector(fa2,(GEN)fa1[i],lx2-1))
      err(talker,"noncoprime ideals in zidealstarinitjoin");

  liste1=(GEN)bid1[4]; lx1=lg(liste1);
  liste2=(GEN)bid2[4]; lx2=lg(liste2);
  lx=lx1+lx2-2; liste = cgetg(lx,t_VEC);
  for (i=1; i<lx1-1; i++) liste[i]=liste1[i];
  for (   ; i<lx; i++)    liste[i]=liste2[i-lx1+2];
  U1=(GEN)bid1[5]; lx1=lg(U1);
  U2=(GEN)bid2[5]; lx2=lg(U2);
  lx=lx1+lx2-1; U = cgetg(lx,t_MAT);

  llx1=lg(struct1[2]);
  llx2=lg(struct2[2]);
  llx=llx1+llx2-1; nbgen=llx-1;
  cyc = diagonal(concatsp((GEN)struct1[2],(GEN)struct2[2]));
  u1u2=smith2(cyc); u1u2clean=smithclean(u1u2);
  met=(GEN)u1u2clean[3];
  if (nbgen)
  {
    for (j=1; j<lx1; j++)
    {
      p1=cgetg(llx,t_COL); U[j]=(long)p1;
      p2=(GEN)U1[j];
      for (i=1; i<llx1; i++) p1[i]=p2[i];
      for (   ; i<llx; i++) p1[i]=zero;
    }
    for (  ; j<lx; j++)
    {
      p1=cgetg(llx,t_COL); U[j]=(long)p1;
      p2=((GEN)U2[j-(lx1-1)]) + 1-llx1;
      for (i=1; i<llx1; i++) p1[i]=zero;
      for (   ; i<llx; i++) p1[i]=p2[i];
    }
    U = gmul((GEN)u1u2clean[1],U);
  }
  else
    for (j=1; j<lx; j++) U[j]=lgetg(1,t_COL);

  if (add_gen)
  {
    if (lg(struct1)<=3 || lg(struct2)<=3)
      err(talker,"please apply idealstar(,,2) and not idealstar(,,1)");

    uv = idealaddtoone(nf,(GEN)module1[1],(GEN)module2[1]);
    p1 = makeprimetoidealvec(nf,(GEN)module[1],uv,(GEN)struct1[3]);
    p2=(GEN)uv[1]; uv[1]=uv[2]; uv[2]=(long)p2;
    p2 = makeprimetoidealvec(nf,(GEN)module[1],uv,(GEN)struct2[3]);
    gen=concatsp(p1,p2);

    u1 = reducemodmatrix(ginv((GEN)u1u2[1]),cyc);
    p1 = cgetg(4,t_VEC);
    p1[3] = (long)compute_gen(nf,u1,met,gen,module, nbp,NULL);
  }
  else p1 = cgetg(3,t_VEC);

  y=cgetg(6,t_VEC);
  y[1]=(long)module;
  y[2]=(long)p1;
    p1[1]=(long)dethnf(met);
    p1[2]=(long)mattodiagonal(met);
  y[3]=(long)fact;
  y[4]=(long)liste;
  y[5]=(long)U;
  return gerepileupto(av,gcopy(y));
}

GEN
zidealstarinitjoin(GEN nf, GEN bid1, GEN bid2)
{
  return zidealstarinitjoinall(nf,bid1,bid2,0);
}

GEN
zidealstarinitjoingen(GEN nf, GEN bid1, GEN bid2)
{
  return zidealstarinitjoinall(nf,bid1,bid2,1);
}

/* Etant donnes bid1 resultat de zidealstarinit pour un module m1 sans partie
 * archimedienne et une partie archimedienne arch, calcule le zidealstarinit
 * [[ideal,arch],[h,[cyc],[gen]],idealfact,[liste],U] du produit
 */
static GEN
zidealstarinitjoinarchall(GEN nf, GEN bid1, GEN arch, long nba, long add_gen)
{
  long av=avma,i,nbp,lx1,lx;
  GEN module1,struct1,fact1,liste1,U1;
  GEN module,liste,h,p1,y,met,u1,x,gen,sarch,u1u2,u1u2clean;

  nf=checknf(nf); checkbid(bid1);
  module1=(GEN)bid1[1]; struct1=(GEN)bid1[2]; fact1=(GEN)bid1[3];
  nbp=lg((GEN)fact1[1])-1;
  x=(GEN)module1[1];
  sarch = zarchstar(nf,x,arch,nba);
  module=cgetg(3,t_VEC);
  module[1]=(long)x;
  module[2]=(long)arch;
  if (gcmpgs(vecmax((GEN)module1[2]),1)>=0)
    err(talker,"nontrivial Archimedian components in zidealstarinitjoinarchall");
  liste1=(GEN)bid1[4]; lx=lg(liste1);
  liste=cgetg(lx,t_VEC); for (i=1; i<lx-1; i++) liste[i]=liste1[i];
  liste[lx-1]=(long)sarch;
  U1=(GEN)bid1[5]; lx1=lg(U1);
  lx=lx1+nba;
  h = diagonal(concatsp((GEN)struct1[2],(GEN)sarch[1]));
  u1u2 = smith2(h); u1u2clean = smithclean(u1u2);
  met=(GEN)u1u2clean[3];

  if (add_gen)
  {
    if (lg(struct1)<=3)
      err(talker,"please apply idealstar(,,2) and not idealstar(,,1)");
    gen=concatsp((GEN)struct1[3],(GEN)sarch[2]);

    u1 = reducemodmatrix(ginv((GEN)u1u2[1]),h);
    p1 = cgetg(4,t_VEC);
    p1[3] = (long)compute_gen(nf,u1,met,gen,module, nbp,sarch);
  }
  else p1 = cgetg(3,t_VEC);

  y=cgetg(6,t_VEC);
  y[1]=(long)module;
  y[2]=(long)p1;
    p1[1]=(long)dethnf(met);
    p1[2]=(long)mattodiagonal(met);
  y[3]=(long)fact1;
  y[4]=(long)liste;
  y[5] = u1u2clean[1];
  return gerepileupto(av,gcopy(y));
}

GEN
zidealstarinitjoinarch(GEN nf, GEN bid1, GEN arch, long nba)
{
  return zidealstarinitjoinarchall(nf,bid1,arch,nba,0);
}

GEN
zidealstarinitjoinarchgen(GEN nf, GEN bid1, GEN arch, long nba)
{
  return zidealstarinitjoinarchall(nf,bid1,arch,nba,1);
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
  m[1]=(long)zinternallog(nf,fa2,sizeh,arch,fa,racunit,0);
  for (j=2; j<=R+1; j++)
    m[j]=(long)zinternallog(nf,fa2,sizeh,arch,fa,(GEN)funits[j-1],0);
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

/* concatenation verticale de Q1 et Q2. Ne cree pas le resultat. */
GEN
vconcat(GEN Q1, GEN Q2)
{
  long lc,lr,lx1,lx2,i,j;
  GEN m,p1,p2,p3;

  lc=lg(Q1); if (lc==1) return Q1;
  lx1=lg(Q1[1]); lx2=lg(Q2[1]); lr=lx1+lx2-1;
  m=cgetg(lc,t_MAT);
  for (j=1; j<lc; j++)
  {
    p1=cgetg(lr,t_COL); m[j]=(long)p1; p2=(GEN)Q1[j]; p3=(GEN)Q2[j];
    for (i=1; i<lx1; i++) p1[i]=p2[i];
    for (   ; i<lr; i++) p1[i]=p3[i-lx1+1];
  }
  return m;
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
  long lim,av0=avma,av,i,j,k,l,q2,lp1,q;
  long do_gen = flag & 1, do_units = flag & 2, big_id = !(flag & 4);
  GEN y,nf,p,z,z2,p1,p2,p3,fa,pr,ideal,lu,lu2,funits,racunit,embunit;

  nf=checknf(bnf);
  if (bound <= 0) return cgetg(1,t_VEC);
  z = cgetg(bound+1,t_VEC);
  for (i=2; i<=bound; i++) z[i] = lgetg(1,t_VEC);
  if (do_units)
  {
    init_units(bnf,&funits,&racunit);
    lu = cgetg(bound+1,t_VEC);
    for (i=2; i<=bound; i++) lu[i]=lgetg(1,t_VEC);
  }

  ideal = idmat(lgef(nf[1])-3);
  if (big_id) ideal = zidealstarinitall(nf,ideal,do_gen);
  p2 = cgetg(2,t_VEC); z[1] = (long)p2;
  p2[1] = (long)ideal;
  if (do_units)
  {
    p2 = cgetg(2,t_VEC); lu[1] = (long)p2;
    p2[1] = (long)logunitmatrix(nf,funits,racunit,ideal);
  }

  p=cgeti(3); p[1]=evalsigne(1) | evallgefint(3);
  av=avma; lim=stack_lim(av,1);
  lu2 = embunit = NULL; /* gcc -Wall */
  for (p[2]=0; p[2]<=bound; )
  {
    if (!*ptdif) err(primer1);
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
          p1 = (GEN)z[i/q];
          if ((lp1 = lg(p1)) == 1) continue;

          p2 = cgetg(lp1,t_VEC);
          for (k=1; k<lp1; k++)
            if (big_id)
              p2[k] = (long)zidealstarinitjoinall(nf,(GEN)p1[k],ideal,do_gen);
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
  if (!do_units) return gerepileupto(av0, gcopy(z));
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
      p1[j]=(long)zidealstarinitjoinarchall(nf,(GEN)p2[j],arch,nba,flun);
  }
  return z;
}

static GEN
ideallistarchall(GEN bnf,GEN list,GEN arch,long flag)
{
  long av,tetpil,i,j,lp1;
  long do_units = flag & 2;
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
  tetpil=avma; y[2]=lpile(av,tetpil,gcopy(lu2)); return y;
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
