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
/**                  BIBLIOTHEQUE  MATHEMATIQUE                    **/
/**                     (deuxieme partie)                          **/
/**                                                                **/
/********************************************************************/
#include "pari.h"

/********************************************************************/
/**                                                                **/
/**                 DEVELOPPEMENTS  LIMITES                        **/
/**                                                                **/
/********************************************************************/

GEN
tayl(GEN x, long v, long precS)
{
  long i, vx = gvar9(x);
  pari_sp tetpil, av=avma;
  GEN p1,y;

  if (v <= vx)
  {
    long p1[] = { evaltyp(t_SER)|_evallg(2), 0 };
    p1[1] = evalvalp(precS) | evalvarn(v);
    return gadd(p1,x);
  }
  p1=cgetg(v+2,t_VEC);
  for (i=0; i<v; i++) p1[i+1]=lpolx[i];
  p1[vx+1]=lpolx[v]; p1[v+1]=lpolx[vx];
  y = tayl(changevar(x,p1), vx,precS); tetpil=avma;
  return gerepile(av,tetpil, changevar(y,p1));
}

GEN
grando0(GEN x, long n, long do_clone)
{
  long m, v, tx=typ(x);

  if (gcmp0(x)) err(talker,"zero argument in O()");
  if (tx == t_INT)
  {
    if (!gcmp1(x)) /* bug 3 + O(1). We suppose x is a truc() */
    {
      if (do_clone) x = gclone(x);
      return padiczero(x,n);
    }
    v=0; m=0; /* 1 = x^0 */
  }
  else
  {
    if (tx != t_POL && ! is_rfrac_t(tx))
      err(talker,"incorrect argument in O()");
    v = gvar(x); if ((ulong)v > MAXVARN) err(talker,"incorrect object in O()");
    m = n*gval(x,v);
  }
  return zeroser(v,m);
}

/*******************************************************************/
/**                                                               **/
/**                      SPECIAL POLYNOMIALS                      **/
/**                                                               **/
/*******************************************************************/
#ifdef LONG_IS_64BIT
# define SQRTVERYBIGINT 3037000500   /* ceil(sqrt(VERYBIGINT)) */
#else
# define SQRTVERYBIGINT 46341
#endif

/* Tchebichev polynomial: T0=1; T1=X; T(n)=2*X*T(n-1)-T(n-2)
 * T(n) = (n/2) sum_{k=0}^{n/2} a_k x^(n-2k)
 *   where a_k = (-1)^k 2^(n-2k) (n-k-1)! / k!(n-2k)! is an integer
 *   and a_0 = 2^(n-1), a_k / a_{k-1} = - (n-2k+2)(n-2k+1) / 4k(n-k) */
GEN
tchebi(long n, long v) /* Assume 4*n < VERYBIGINT */
{
  long k, l;
  pari_sp av;
  GEN q,a,r;

  if (v<0) v = 0;
  if (n < 0) n = -n;
  if (n==0) return polun[v];
  if (n==1) return polx[v];

  q = cgetg(n+3, t_POL); r = q + n+2;
  a = shifti(gun, n-1);
  *r-- = (long)a;
  *r-- = zero;
  if (n < SQRTVERYBIGINT)
    for (k=1,l=n; l>1; k++,l-=2)
    {
      av = avma;
      a = divis(mulis(a, l*(l-1)), 4*k*(n-k));
      a = gerepileuptoint(av, negi(a));
      *r-- = (long)a;
      *r-- = zero;
    }
  else
    for (k=1,l=n; l>1; k++,l-=2)
    {
      av = avma;
      a = mulis(mulis(a, l), l-1);
      a = divis(divis(a, 4*k), n-k);
      a = gerepileuptoint(av, negi(a));
      *r-- = (long)a;
      *r-- = zero;
    }
  q[1] = evalsigne(1) | evalvarn(v) | evallgef(n+3);
  return q;
}

GEN addshiftw(GEN x, GEN y, long d);
/* Legendre polynomial */
/* L0=1; L1=X; (n+1)*L(n+1)=(2*n+1)*X*L(n)-n*L(n-1) */
GEN
legendre(long n, long v)
{
  long m;
  pari_sp av, tetpil, lim;
  GEN p0,p1,p2;

  if (v<0) v = 0;
  if (n < 0) err(talker,"negative degree in legendre");
  if (n==0) return polun[v];
  if (n==1) return polx[v];

  p0=polun[v]; av=avma; lim=stack_lim(av,2);
  p1=gmul2n(polx[v],1);
  for (m=1; m<n; m++)
  {
    p2 = addshiftw(gmulsg(4*m+2,p1), gmulsg(-4*m,p0), 1);
    setvarn(p2,v);
    p0 = p1; tetpil=avma; p1 = gdivgs(p2,m+1);
    if (low_stack(lim, stack_lim(av,2)))
    {
      GEN *gptr[2];
      if(DEBUGMEM>1) err(warnmem,"legendre");
      p0=gcopy(p0); gptr[0]=&p0; gptr[1]=&p1;
      gerepilemanysp(av,tetpil,gptr,2);
    }
  }
  tetpil=avma; return gerepile(av,tetpil,gmul2n(p1,-n));
}

/* cyclotomic polynomial */
GEN
cyclo(long n, long v)
{
  long d, q, m;
  pari_sp av=avma, tetpil;
  GEN yn,yd;

  if (n<=0) err(arither2);
  if (v<0) v = 0;
  yn = yd = polun[0];
  for (d=1; d*d<=n; d++)
  {
    if (n%d) continue;
    q=n/d;
    m = mu(stoi(q));
    if (m)
    { /* y *= (x^d - 1) */
      if (m>0) yn = addshiftw(yn, gneg(yn), d);
      else     yd = addshiftw(yd, gneg(yd), d);
    }
    if (q==d) break;
    m = mu(stoi(d));
    if (m)
    { /* y *= (x^q - 1) */
      if (m>0) yn = addshiftw(yn, gneg(yn), q);
      else     yd = addshiftw(yd, gneg(yd), q);
    }
  }
  tetpil=avma; yn = gerepile(av,tetpil,gdeuc(yn,yd));
  setvarn(yn,v); return yn;
}

/* compute prod (L*x +/- a[i]) */
GEN
roots_to_pol_intern(GEN L, GEN a, long v, int plus)
{
  long i,k,lx = lg(a), code;
  GEN p1,p2;
  if (lx == 1) return polun[v];
  p1 = cgetg(lx, t_VEC);
  code = evalsigne(1)|evalvarn(v)|evallgef(5);
  for (k=1,i=1; i<lx-1; i+=2)
  {
    p2 = cgetg(5,t_POL); p1[k++] = (long)p2;
    p2[2] = lmul((GEN)a[i],(GEN)a[i+1]);
    p2[3] = ladd((GEN)a[i],(GEN)a[i+1]);
    if (plus == 0) p2[3] = lneg((GEN)p2[3]);
    p2[4] = (long)L; p2[1] = code;
  }
  if (i < lx)
  {
    p2 = cgetg(4,t_POL); p1[k++] = (long)p2;
    p2[1] = code = evalsigne(1)|evalvarn(v)|evallgef(4);
    p2[2] = plus? a[i]: lneg((GEN)a[i]);
    p2[3] = (long)L;
  }
  setlg(p1, k); return divide_conquer_prod(p1, gmul);
}

GEN
roots_to_pol(GEN a, long v)
{
  return roots_to_pol_intern(gun,a,v,0);
}

/* prod_{i=1..r1} (x - a[i]) prod_{i=1..r2} (x - a[i])(x - conj(a[i]))*/
GEN
roots_to_pol_r1r2(GEN a, long r1, long v)
{
  long i,k,lx = lg(a), code;
  GEN p1;
  if (lx == 1) return polun[v];
  p1 = cgetg(lx, t_VEC);
  code = evalsigne(1)|evalvarn(v)|evallgef(5);
  for (k=1,i=1; i<r1; i+=2)
  {
    GEN p2 = cgetg(5,t_POL); p1[k++] = (long)p2;
    p2[2] = lmul((GEN)a[i],(GEN)a[i+1]);
    p2[3] = lneg(gadd((GEN)a[i],(GEN)a[i+1]));
    p2[4] = un; p2[1] = code;
  }
  if (i < r1+1)
    p1[k++] = ladd(polx[v], gneg((GEN)a[i]));
  for (i=r1+1; i<lx; i++)
  {
    GEN p2 = cgetg(5,t_POL); p1[k++] = (long)p2;
    p2[2] = lnorm((GEN)a[i]);
    p2[3] = lneg(gtrace((GEN)a[i]));
    p2[4] = un; p2[1] = code;
  }
  setlg(p1, k); return divide_conquer_prod(p1, gmul);
}

/********************************************************************/
/**                                                                **/
/**                  HILBERT & PASCAL MATRICES                     **/
/**                                                                **/
/********************************************************************/
GEN
mathilbert(long n) /* Hilbert matrix of order n */
{
  long i,j;
  GEN a,p;

  if (n<0) n = 0;
  p = cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++)
  {
    p[j]=lgetg(n+1,t_COL);
    for (i=1+(j==1); i<=n; i++)
    {
      a=cgetg(3,t_FRAC); a[1]=un; a[2]=lstoi(i+j-1);
      coeff(p,i,j)=(long)a;
    }
  }
  if ( n ) mael(p,1,1)=un;
  return p;
}

/* q-Pascal triangle = (choose(i,j)_q) (ordinary binomial if q = NULL) */
GEN
matqpascal(long n, GEN q)
{
  long i, j, I;
  pari_sp av = avma;
  GEN m, *qpow = NULL; /* gcc -Wall */

  if (n<0) n = -1;
  n++; m = cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++) m[j] = lgetg(n+1,t_COL);
  if (q)
  {
    I = (n+1)/2;
    if (I > 1) { qpow = (GEN*)new_chunk(I+1); qpow[2]=q; }
    for (j=3; j<=I; j++) qpow[j] = gmul(q, qpow[j-1]);
  }
  for (i=1; i<=n; i++)
  {
    I = (i+1)/2; coeff(m,i,1)=un;
    if (q)
    {
      for (j=2; j<=I; j++)
        coeff(m,i,j) = ladd(gmul(qpow[j],gcoeff(m,i-1,j)), gcoeff(m,i-1,j-1));
    }
    else
    {
      for (j=2; j<=I; j++)
        coeff(m,i,j) = laddii(gcoeff(m,i-1,j), gcoeff(m,i-1,j-1));
    }
    for (   ; j<=i; j++) coeff(m,i,j) = coeff(m,i,i+1-j);
    for (   ; j<=n; j++) coeff(m,i,j) = zero;
  }
  return gerepilecopy(av, m);
}

/********************************************************************/
/**                                                                **/
/**                  LAPLACE TRANSFORM (OF A SERIES)               **/
/**                                                                **/
/********************************************************************/

GEN
laplace(GEN x)
{
  pari_sp av = avma;
  long i,l,ec;
  GEN y,p1;

  if (typ(x)!=t_SER) err(talker,"not a series in laplace");
  if (gcmp0(x)) return gcopy(x);

  ec = valp(x);
  if (ec<0) err(talker,"negative valuation in laplace");
  l=lg(x); y=cgetg(l,t_SER);
  p1=mpfact(ec); y[1]=x[1];
  for (i=2; i<l; i++)
  {
    y[i]=lmul(p1,(GEN)x[i]);
    ec++; p1=mulsi(ec,p1);
  }
  return gerepilecopy(av,y);
}

/********************************************************************/
/**                                                                **/
/**              CONVOLUTION PRODUCT (OF TWO SERIES)               **/
/**                                                                **/
/********************************************************************/

GEN
convol(GEN x, GEN y)
{
  long j, lx, ly, ex, ey, vx = varn(x);
  GEN z;

  if (typ(x) != t_SER || typ(y) != t_SER) err(talker,"not a series in convol");
  if (varn(y) != vx) err(talker,"different variables in convol");
  ex = valp(x); lx = lg(x) + ex; x -= ex;
  ey = valp(y); ly = lg(y) + ey; y -= ey;
  /* inputs shifted: x[i] and y[i] now correspond to monomials of same degree */
  if (ly < lx) lx = ly; /* min length */
  if (ex < ey) ex = ey; /* max valuation */

  z = cgetg(lx - ex, t_SER);
  z[1] = evalsigne(1) | evalvalp(ex) | evalvarn(vx);
  for (j = ex+2; j<lx; j++) z[j-ex] = lmul((GEN)x[j],(GEN)y[j]);
  return normalize(z);
}

/******************************************************************/
/**                                                              **/
/**                       PRECISION CHANGES                      **/
/**                                                              **/
/******************************************************************/

GEN
gprec(GEN x, long l)
{
  long tx=typ(x),lx=lg(x),i,pr;
  GEN y;

  if (l<=0) err(talker,"precision<=0 in gprec");
  switch(tx)
  {
    case t_REAL:
      pr = (long) (l*pariK1+3); y=cgetr(pr); affrr(x,y); break;

    case t_PADIC:
      if (!signe(x[4]))
        return padiczero((GEN)x[2], l+precp(x));
      y=cgetg(lx,tx); copyifstack(x[2], y[2]);
      y[1]=x[1]; setprecp(y,l);
      y[3]=lpuigs((GEN)x[2],l);
      y[4]=lmodii((GEN)x[4],(GEN)y[3]);
      break;

    case t_SER:
      if (gcmp0(x)) return zeroser(varn(x), l);
      y=cgetg(l+2,t_SER); y[1]=x[1]; l++; i=l;
      if (l>=lx)
	for ( ; i>=lx; i--) y[i]=zero;
      for ( ; i>=2; i--) y[i]=lcopy((GEN)x[i]);
      break;

    case t_POL:
      lx=lgef(x); y=cgetg(lx,tx); y[1]=x[1];
      for (i=2; i<lx; i++) y[i]=lprec((GEN)x[i],l);
      break;

    case t_COMPLEX: case t_POLMOD: case t_RFRAC: case t_RFRACN:
    case t_VEC: case t_COL: case t_MAT:
      y=cgetg(lx,tx);
      for (i=1; i<lx; i++) y[i]=lprec((GEN)x[i],l);
      break;
    default: y=gcopy(x);
  }
  return y;
}

/* internal: precision given in word length (including codewords) */
GEN
gprec_w(GEN x, long pr)
{
  long tx=typ(x),lx,i;
  GEN y;

  switch(tx)
  {
    case t_REAL:
      y=cgetr(pr); affrr(x,y); break;

    case t_POL:
      lx=lgef(x); y=cgetg(lx,tx); y[1]=x[1];
      for (i=2; i<lx; i++) y[i]=(long)gprec_w((GEN)x[i],pr);
      break;

    case t_COMPLEX: case t_POLMOD: case t_RFRAC: case t_RFRACN:
    case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); y=cgetg(lx,tx);
      for (i=1; i<lx; i++) y[i]=(long)gprec_w((GEN)x[i],pr);
      break;
    default: y=gprec(x,pr);
  }
  return y;
}

/*******************************************************************/
/**                                                               **/
/**                     RECIPROCAL POLYNOMIAL                     **/
/**                                                               **/
/*******************************************************************/

GEN
polrecip(GEN x)
{
  long lx=lgef(x),i,j;
  GEN y;

  if (typ(x) != t_POL) err(typeer,"polrecip");
  y=cgetg(lx,t_POL); y[1]=x[1];
  for (i=2,j=lx-1; i<lx; i++,j--) y[i]=lcopy((GEN)x[j]);
  return normalizepol_i(y,lx);
}

/* as above. Internal (don't copy or normalize) */
GEN
polrecip_i(GEN x)
{
  long lx=lgef(x),i,j;
  GEN y;

  y=cgetg(lx,t_POL); y[1]=x[1];
  for (i=2,j=lx-1; i<lx; i++,j--) y[i]=x[j];
  return y;
}

/*******************************************************************/
/**                                                               **/
/**                      BINOMIAL COEFFICIENTS                    **/
/**                                                               **/
/*******************************************************************/

GEN
binome(GEN n, long k)
{
  long i;
  pari_sp av;
  GEN y;

  if (k <= 1)
  {
    if (is_noncalc_t(typ(n))) err(typeer,"binomial");
    if (k < 0) return gzero;
    if (k == 0) return gun;
    return gcopy(n);
  }
  av = avma; y = n;
  if (typ(n) == t_INT)
  {
    if (signe(n) > 0)
    {
      GEN z = subis(n,k);
      if (cmpis(z,k) < 0) k = itos(z);
      avma = av;
      if (k <= 1)
      {
        if (k < 0) return gzero;
        if (k == 0) return gun;
        return gcopy(n);
      }
    }
    for (i=2; i<=k; i++)
      y = gdivgs(gmul(y,addis(n,i-1-k)), i);
  }
  else
  {
    for (i=2; i<=k; i++)
      y = gdivgs(gmul(y,gaddgs(n,i-1-k)), i);
  }
  return gerepileupto(av, y);
}

/* Assume n >= 1, return bin, bin[k+1] = binomial(n, k) */
GEN
vecbinome(long n)
{
  long d = (n + 1)/2, k;
  GEN bin = cgetg(n+2, t_VEC), *C;
  C = (GEN*)(bin + 1); /* C[k] = binomial(n, k) */
  C[0] = gun;
  for (k=1; k <= d; k++)
  {
    pari_sp av = avma;
    C[k] = gerepileuptoint(av, diviiexact(mulsi(n-k+1, C[k-1]), stoi(k)));
  }
  for (   ; k <= n; k++) C[k] = C[n - k];
  return bin;
}

/********************************************************************/
/**                                                                **/
/**                  POLYNOMIAL INTERPOLATION                      **/
/**                                                                **/
/********************************************************************/
/* assume n > 1 */
GEN
polint_i(GEN xa, GEN ya, GEN x, long n, GEN *ptdy)
{
  long i, m, ns=0, tx=typ(x);
  pari_sp av = avma, tetpil;
  GEN den,ho,hp,w,y,c,d,dy;

  if (!xa)
  {
    xa = cgetg(n+1, t_VEC);
    for (i=1; i<=n; i++) xa[i] = lstoi(i);
    xa++;
  }
  if (is_scalar_t(tx) && tx != t_INTMOD && tx != t_PADIC && tx != t_POLMOD)
  {
    GEN dif = NULL, dift;
    for (i=0; i<n; i++)
    {
      dift = gabs(gsub(x,(GEN)xa[i]), MEDDEFAULTPREC);
      if (!dif || gcmp(dift,dif)<0) { ns=i; dif=dift; }
    }
  }
  c=new_chunk(n);
  d=new_chunk(n); for (i=0; i<n; i++) c[i] = d[i] = ya[i];
  y=(GEN)d[ns--];
  dy = NULL; tetpil = 0; /* gcc -Wall */
  for (m=1; m<n; m++)
  {
    for (i=0; i<n-m; i++)
    {
      ho = gsub((GEN)xa[i],x);
      hp = gsub((GEN)xa[i+m],x); den = gsub(ho,hp);
      if (gcmp0(den)) err(talker,"two abcissas are equal in polint");
      w=gsub((GEN)c[i+1],(GEN)d[i]); den = gdiv(w,den);
      c[i]=lmul(ho,den);
      d[i]=lmul(hp,den);
    }
    dy = (2*(ns+1) < n-m)? (GEN)c[ns+1]: (GEN)d[ns--];
    tetpil=avma; y=gadd(y,dy);
  }
  if (!ptdy) y = gerepile(av,tetpil,y);
  else
  {
    GEN *gptr[2];
    *ptdy=gcopy(dy); gptr[0]=&y; gptr[1]=ptdy;
    gerepilemanysp(av,tetpil,gptr,2);
  }
  return y;
}

GEN
polint(GEN xa, GEN ya, GEN x, GEN *ptdy)
{
  long tx=typ(xa), ty, lx=lg(xa);

  if (ya) ty = typ(ya); else { ya = xa; ty = tx; xa = NULL; }

  if (! is_vec_t(tx) || ! is_vec_t(ty))
    err(talker,"not vectors in polinterpolate");
  if (lx != lg(ya))
    err(talker,"different lengths in polinterpolate");
  if (lx <= 2)
  {
    if (lx == 1) err(talker,"no data in polinterpolate");
    ya=gcopy((GEN)ya[1]); if (ptdy) *ptdy = ya;
    return ya;
  }
  if (!x) x = polx[0];
  return polint_i(xa? xa+1: xa,ya+1,x,lx-1,ptdy);
}

/***********************************************************************/
/*                                                                     */
/*                          SET OPERATIONS                             */
/*                                                                     */
/***********************************************************************/
GEN
gtoset(GEN x)
{
  pari_sp av;
  long i,c,tx,lx;
  GEN y;

  if (!x) return cgetg(1, t_VEC);
  tx = typ(x); lx = lg(x);
  if (!is_vec_t(tx))
  {
    if (tx != t_LIST)
      { y=cgetg(2,t_VEC); y[1]=(long)GENtoGENstr(x); return y; }
    lx = lgeflist(x)-1; x++;
  }
  if (lx==1) return cgetg(1,t_VEC);
  av=avma; y=cgetg(lx,t_VEC);
  for (i=1; i<lx; i++) y[i]=(long)GENtoGENstr((GEN)x[i]);
  y = sort(y);
  c=1;
  for (i=2; i<lx; i++)
    if (!gegal((GEN)y[i], (GEN)y[c])) y[++c] = y[i];
  setlg(y,c+1); return gerepilecopy(av,y);
}

long
setisset(GEN x)
{
  long lx,i;

  if (typ(x)!=t_VEC) return 0;
  lx=lg(x)-1; if (!lx) return 1;
  for (i=1; i<lx; i++)
    if (typ(x[i]) != t_STR || gcmp((GEN)x[i+1],(GEN)x[i])<=0) return 0;
  return typ(x[i]) == t_STR;
}

/* looks if y belongs to the set x and returns the index if yes, 0 if no */
long
gen_search(GEN x, GEN y, int flag, int (*cmp)(GEN,GEN))
{
  long lx,j,li,ri,fl, tx = typ(x);

  if (tx==t_VEC) lx = lg(x);
  else
  {
    if (tx!=t_LIST) err(talker,"not a set in setsearch");
    lx=lgeflist(x)-1; x++;
  }
  if (lx==1) return flag? 1: 0;

  li=1; ri=lx-1;
  do
  {
    j = (ri+li)>>1; fl = cmp((GEN)x[j],y);
    if (!fl) return flag? 0: j;
    if (fl<0) li=j+1; else ri=j-1;
  } while (ri>=li);
  if (!flag) return 0;
  return (fl<0)? j+1: j;
}


long
setsearch(GEN x, GEN y, long flag)
{
  pari_sp av = avma;
  long res;
  if (typ(y) != t_STR) y = GENtoGENstr(y);
  res=gen_search(x,y,flag,gcmp);
  avma=av;
  return res;
}

#if 0
GEN
gen_union(GEN x, GEN y, int (*cmp)(GEN,GEN))
{
  if (typ(x) != t_VEC || typ(y) != t_VEC) err(talker,"not a set in setunion");

}
#endif

GEN
setunion(GEN x, GEN y)
{
  pari_sp av=avma, tetpil;
  GEN z;

  if (typ(x) != t_VEC || typ(y) != t_VEC) err(talker,"not a set in setunion");
  z=concatsp(x,y); tetpil=avma; return gerepile(av,tetpil,gtoset(z));
}

GEN
setintersect(GEN x, GEN y)
{
  long i, lx, c;
  pari_sp av=avma;
  GEN z;

  if (!setisset(x) || !setisset(y)) err(talker,"not a set in setintersect");
  lx=lg(x); z=cgetg(lx,t_VEC); c=1;
  for (i=1; i<lx; i++)
    if (setsearch(y, (GEN)x[i], 0)) z[c++] = x[i];
  setlg(z,c); return gerepilecopy(av,z);
}

GEN
gen_setminus(GEN set1, GEN set2, int (*cmp)(GEN,GEN))
{
  pari_sp ltop=avma;
  long find;
  long i,j,k;
  GEN  diff=cgetg(lg(set1),t_VEC);
  for(i=1,j=1,k=1; i < lg(set1); i++)
  {
    for(find=0; j < lg(set2); j++)
    {
      int s=cmp((GEN)set1[i],(GEN)set2[j]);
      if (s<0)  break ;
      if (s>0)  continue;
      find=1;
    }
    if (!find)
      diff[k++]=set1[i];
  }
  setlg(diff,k);
  return gerepilecopy(ltop,diff);
}

GEN
setminus(GEN x, GEN y)
{
  if (!setisset(x) || !setisset(y)) err(talker,"not a set in setminus");
  return gen_setminus(x,y,gcmp);
}

/***********************************************************************/
/*                                                                     */
/*               OPERATIONS ON DIRICHLET SERIES                        */
/*                                                                     */
/***********************************************************************/

/* Addition, subtraction and scalar multiplication of Dirichlet series
   are done on the corresponding vectors */

static long
dirval(GEN x)
{
  long i=1,lx=lg(x);
  while (i<lx && gcmp0((GEN)x[i])) i++;
  return i;
}

GEN
dirmul(GEN x, GEN y)
{
  pari_sp av = avma, lim = stack_lim(av, 1);
  long lx,ly,lz,dx,dy,i,j,k;
  GEN z,p1;

  if (typ(x)!=t_VEC || typ(y)!=t_VEC) err(talker,"not a dirseries in dirmul");
  dx=dirval(x); dy=dirval(y); lx=lg(x); ly=lg(y);
  if (ly-dy<lx-dx) { z=y; y=x; x=z; lz=ly; ly=lx; lx=lz; lz=dy; dy=dx; dx=lz; }
  lz=min(lx*dy,ly*dx);
  z=cgetg(lz,t_VEC); for (i=1; i<lz; i++) z[i]=zero;
  for (j=dx; j<lx; j++)
  {
    p1=(GEN)x[j];
    if (!gcmp0(p1))
    {
      if (gcmp1(p1))
	for (k=dy,i=j*dy; i<lz; i+=j,k++) z[i]=ladd((GEN)z[i],(GEN)y[k]);
      else
      {
	if (gcmp_1(p1))
	  for (k=dy,i=j*dy; i<lz; i+=j,k++) z[i]=lsub((GEN)z[i],(GEN)y[k]);
	else
	  for (k=dy,i=j*dy; i<lz; i+=j,k++) z[i]=ladd((GEN)z[i],gmul(p1,(GEN)y[k]));
      }
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if (DEBUGLEVEL) fprintferr("doubling stack in dirmul\n");
      z = gerepilecopy(av,z);
    }
  }
  return gerepilecopy(av,z);
}

GEN
dirdiv(GEN x, GEN y)
{
  pari_sp av = avma;
  long lx,ly,lz,dx,dy,i,j;
  GEN z,p1;

  if (typ(x)!=t_VEC || typ(y)!=t_VEC) err(talker,"not a dirseries in dirmul");
  dx=dirval(x); dy=dirval(y); lx=lg(x); ly=lg(y);
  if (dy!=1) err(talker,"not an invertible dirseries in dirdiv");
  lz=min(lx,ly*dx); p1=(GEN)y[1];
  if (!gcmp1(p1)) { y=gdiv(y,p1); x=gdiv(x,p1); }
  else x=gcopy(x);
  z=cgetg(lz,t_VEC); for (i=1; i<dx; i++) z[i]=zero;
  for (j=dx; j<lz; j++)
  {
    p1=(GEN)x[j]; z[j]=(long)p1;
    if (!gcmp0(p1))
    {
      if (gcmp1(p1))
	for (i=j+j; i<lz; i+=j) x[i]=lsub((GEN)x[i],(GEN)y[i/j]);
      else
      {
	if (gcmp_1(p1))
	  for (i=j+j; i<lz; i+=j) x[i]=ladd((GEN)x[i],(GEN)y[i/j]);
	else
	  for (i=j+j; i<lz; i+=j) x[i]=lsub((GEN)x[i],gmul(p1,(GEN)y[i/j]));
      }
    }
  }
  return gerepilecopy(av,z);
}

/*************************************************************************/
/**									**/
/**			         RANDOM					**/
/**									**/
/*************************************************************************/

GEN
genrand(GEN N)
{
  if (!N) return stoi( pari_rand31() );
  if (typ(N)!=t_INT || signe(N)<=0) err(talker,"invalid bound in random");
  return randomi(N);
}

long
getstack(void) { return top-avma; }

long
gettime(void) { return timer(); }

/***********************************************************************/
/**							              **/
/**       		     PERMUTATIONS                             **/
/**								      **/
/***********************************************************************/

GEN
numtoperm(long n, GEN x)
{
  pari_sp av;
  long i,a,r;
  GEN v,w;

  if (n < 0) err(talker,"n too small (%ld) in numtoperm",n);
  if (typ(x) != t_INT) err(arither1);
  v = cgetg(n+1, t_VEC);
  v[1] = 1; av = avma;
  if (signe(x) <= 0) x = modii(x, mpfact(n));
  for (r=2; r<=n; r++)
  {
    x = dvmdis(x,r,&w); a = itos(w);
    for (i=r; i>=a+2; i--) v[i] = v[i-1];
    v[i] = r;
  }
  avma = av;
  for (i=1; i<=n; i++) v[i] = lstoi(v[i]);
  return v;
}

GEN
permtonum(GEN x)
{
  long lx=lg(x)-1, n=lx, last, ind, tx = typ(x);
  pari_sp av=avma;
  GEN ary,res;

  if (!is_vec_t(tx)) err(talker,"not a vector in permtonum");
  ary = cgetg(lx+1,t_VECSMALL);
  for (ind=1; ind<=lx; ind++)
  {
    res = (GEN)*++x;
    if (typ(res) != t_INT) err(typeer,"permtonum");
    ary[ind] = itos(res);
  }
  ary++; res = gzero;
  for (last=lx; last>0; last--)
  {
    lx--; ind = lx;
    while (ind>0 && ary[ind] != last) ind--;
    res = addis(mulis(res,last), ind);
    while (ind++<lx) ary[ind-1] = ary[ind];
  }
  if (!signe(res)) res = mpfact(n);
  return gerepileuptoint(av, res);
}

/********************************************************************/
/**                                                                **/
/**                       MODREVERSE                               **/
/**                                                                **/
/********************************************************************/
/* evaluate f(x) mod T */
GEN
RX_RXQ_compo(GEN f, GEN x, GEN T)
{
  pari_sp av = avma;
  long l;
  GEN y;

  if (typ(f) != t_POL) return gcopy(f);
  l = lgef(f)-1; y = (GEN)f[l];
  for (l--; l>=2; l--)
    y = gres(gadd(gmul(y,x), (GEN)f[l]), T);
  return gerepileupto(av, y);
}

/* return (1,...a^l) mod T. Not memory clean */
GEN
RXQ_powers(GEN a, GEN T, long l)
{
  long i;
  GEN v;

  if (typ(a) != t_POL) err(typeer,"RXQ_powers");
  l += 2;
  v = cgetg(l,t_VEC);
  v[1] = un; if (l == 2) return v;

  if (degpol(a) >= degpol(T)) a = gres(a, T);
  v[2] = (long)a;
  for (i=3; i<l; i++) v[i] = lres(gmul((GEN)v[i-1], a), T);
  return v;
}

/* return y such that Mod(y, charpoly(Mod(a,T)) = Mod(a,T) */
GEN
modreverse_i(GEN a, GEN T)
{
  pari_sp av = avma;
  long n = degpol(T);
  GEN y;

  if (n <= 0) return gcopy(a);
  if (n == 1)
    return gerepileupto(av, gneg(gdiv((GEN)T[2], (GEN)T[3])));
  if (gcmp0(a) || typ(a) != t_POL) err(talker,"reverse polmod does not exist");

  y = vecpol_to_mat(RXQ_powers(a,T,n-1), n);
  y = gauss(y, vec_ei(n, 2));
  return gerepilecopy(av, vec_to_pol(y, varn(T)));
}

GEN
polymodrecip(GEN x)
{
  long v, n;
  GEN T, a, y;

  if (typ(x)!=t_POLMOD) err(talker,"not a polmod in modreverse");
  T = (GEN)x[1];
  a = (GEN)x[2];
  n = degpol(T); if (n <= 0) return gcopy(x);
  v = varn(T);
  y = cgetg(3,t_POLMOD);
  y[1] = (n==1)? lsub(polx[v], a): (long)caract2(T, a, v);
  y[2] = (long)modreverse_i(a, T); return y;
}

/********************************************************************/
/**                                                                **/
/**                           HEAPSORT                             **/
/**                                                                **/
/********************************************************************/
static GEN vcmp_k;
static int vcmp_lk;
static int (*vcmp_cmp)(GEN,GEN);

int
pari_compare_int(int *a,int *b)
{
  return *a - *b;
}

int
pari_compare_long(long *a,long *b)
{
  return *a - *b;
}

static int
veccmp(GEN x, GEN y)
{
  int i,s;

  for (i=1; i<vcmp_lk; i++)
  {
    s = vcmp_cmp((GEN) x[vcmp_k[i]], (GEN) y[vcmp_k[i]]);
    if (s) return s;
  }
  return 0;
}

static int
longcmp(GEN x, GEN y)
{
  return ((long)x > (long)y)? 1: ((x == y)? 0: -1);
}

/* Sort x = vector of elts, using cmp to compare them.
 *  flag & cmp_IND: indirect sort: return permutation that would sort x
 *  flag & cmp_C  : as cmp_IND, but return permutation as vector of C-longs
 */
GEN
gen_sort(GEN x, int flag, int (*cmp)(GEN,GEN))
{
  long i, j, indxt, ir, l, tx = typ(x), lx = lg(x);
  GEN q, y, indx;

  if (tx == t_LIST) { lx = lgeflist(x)-1; tx = t_VEC; x++; }
  if (!is_matvec_t(tx) && tx != t_VECSMALL) err(typeer,"gen_sort");
  if      (flag & cmp_C)   tx = t_VECSMALL;
  else if (flag & cmp_IND) tx = t_VEC;
  y = cgetg(lx, tx);
  if (lx==1) return y;
  if (lx==2)
  {
    if      (flag & cmp_C)   y[1] = 1;
    else if (flag & cmp_IND) y[1] = un;
    else if (tx == t_VECSMALL) y[1] = x[1];
    else y[1] = lcopy((GEN)x[1]); 
    return y;
  }
  if (!cmp) cmp = &longcmp;
  indx = (GEN) gpmalloc(lx*sizeof(long));
  for (j=1; j<lx; j++) indx[j] = j;

  ir = lx-1; l = (ir>>1)+1;
  for(;;)
  { /* HeapSort */
    if (l > 1) indxt = indx[--l];
    else
    {
      indxt = indx[ir]; indx[ir] = indx[1];
      if (--ir == 1) break; /* DONE */
    }
    q = (GEN)x[indxt]; i = l;
    for (j=i<<1; j<=ir; j<<=1)
    {
      if (j<ir && cmp((GEN)x[indx[j]],(GEN)x[indx[j+1]]) < 0) j++;
      if (cmp(q,(GEN)x[indx[j]]) >= 0) break;

      indx[i] = indx[j]; i = j;
    }
    indx[i] = indxt;
  }
  indx[1] = indxt;

  if (flag & cmp_REV)
  { /* reverse order */
    GEN indy = (GEN) gpmalloc(lx*sizeof(long));
    for (j=1; j<lx; j++) indy[j] = indx[lx-j];
    free(indx); indx = indy;
  }
  if (flag & cmp_C)
    for (i=1; i<lx; i++) y[i] = indx[i];
  else if (flag & cmp_IND)
    for (i=1; i<lx; i++) y[i] = lstoi(indx[i]);
  else if (tx == t_VECSMALL)
    for (i=1; i<lx; i++) y[i] = x[indx[i]];
  else
    for (i=1; i<lx; i++) y[i] = lcopy((GEN)x[indx[i]]);
  free(indx); return y;
}

#define sort_fun(flag) ((flag & cmp_LEX)? &lexcmp: &gcmp)

GEN
gen_vecsort(GEN x, GEN k, long flag)
{
  long i,j,l,t, lx = lg(x), tmp[2];

  if (lx<=2) return gen_sort(x,flag,sort_fun(flag));
  t = typ(k); vcmp_cmp = sort_fun(flag);
  if (t==t_INT)
  {
    tmp[1] = (long)k; k = tmp;
    vcmp_lk = 2;
  }
  else
  {
    if (! is_vec_t(t)) err(talker,"incorrect lextype in vecsort");
    vcmp_lk = lg(k);
  }
  l = 0;
  vcmp_k = (GEN)gpmalloc(vcmp_lk * sizeof(long));
  for (i=1; i<vcmp_lk; i++)
  {
    j = itos((GEN)k[i]);
    if (j<=0) err(talker,"negative index in vecsort");
    vcmp_k[i]=j; if (j>l) l=j;
  }
  t = typ(x);
  if (! is_matvec_t(t)) err(typeer,"vecsort");
  for (j=1; j<lx; j++)
  {
    t = typ(x[j]);
    if (! is_vec_t(t)) err(typeer,"vecsort");
    if (lg((GEN)x[j]) <= l) err(talker,"index too large in vecsort");
  }
  x = gen_sort(x, flag, veccmp);
  free(vcmp_k); return x;
}

GEN
vecsort0(GEN x, GEN k, long flag)
{
  if (flag < 0 || flag >= cmp_C) err(flagerr,"vecsort");
  if (k) return gen_vecsort(x, k, flag);
  return gen_sort(x, flag, (typ(x) == t_VECSMALL)?NULL: sort_fun(flag));
}

GEN
vecsort(GEN x, GEN k)
{
  return gen_vecsort(x,k, 0);
}

GEN
sindexsort(GEN x)
{
  return gen_sort(x, cmp_IND | cmp_C, gcmp);
}

GEN
sindexlexsort(GEN x)
{
  return gen_sort(x, cmp_IND | cmp_C, lexcmp);
}

GEN
indexsort(GEN x)
{
  return gen_sort(x, cmp_IND, gcmp);
}

GEN
indexlexsort(GEN x)
{
  return gen_sort(x, cmp_IND, lexcmp);
}

GEN
sort(GEN x)
{
  return gen_sort(x, 0, gcmp);
}

GEN
lexsort(GEN x)
{
  return gen_sort(x, 0, lexcmp);
}

/* index of x in table T, 0 otherwise */
long
tablesearch(GEN T, GEN x, int (*cmp)(GEN,GEN))
{
  long l=1,u=lg(T)-1,i,s;

  while (u>=l)
  {
    i = (l+u)>>1; s = cmp(x,(GEN)T[i]);
    if (!s) return i;
    if (s<0) u=i-1; else l=i+1;
  }
  return 0;
}

/* assume lg(x) = lg(y), x,y in Z^n */
int
cmp_vecint(GEN x, GEN y)
{
  long fl,i, lx = lg(x);
  for (i=1; i<lx; i++)
    if (( fl = cmpii((GEN)x[i], (GEN)y[i]) )) return fl;
  return 0;
}

/* assume x and y come from the same primedec call (uniformizer unique) */
int
cmp_prime_over_p(GEN x, GEN y)
{
  int k = mael(x,4,2) - mael(y,4,2); /* diff. between residue degree */
  return k? ((k > 0)? 1: -1)
          : cmp_vecint((GEN)x[2], (GEN)y[2]);
}

int
cmp_prime_ideal(GEN x, GEN y)
{
  int k = cmpii((GEN)x[1], (GEN)y[1]);
  return k? k: cmp_prime_over_p(x,y);
}
