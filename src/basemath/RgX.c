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

int 
is_rational(GEN x) { long t = typ(x); return is_rational_t(t); }
int
RgX_is_rational(GEN x)
{
  long i, t = typ(x);
  if (t != t_POL) return is_rational_t(t);
  for (i=lg(x)-1; i>1; i--)
    if (!is_rational((GEN)t[i])) return 0;
  return 1;
}

/********************************************************************/
/**                                                                **/
/**                        LINEAR ALGEBRA                          **/
/**                                                                **/
/********************************************************************/

/* x non-empty t_MAT, y a compatible zc (dimension > 0). */
static GEN
RgM_zc_mul_i(GEN x, GEN y, long c, long l)
{
  long i, j;
  pari_sp av;
  GEN z = cgetg(l,t_COL), s;

  for (i=1; i<l; i++)
  {
    av = avma; s = gmulgs(gcoeff(x,i,1),y[1]);
    for (j=2; j<c; j++)
       if (y[j]) s = gadd(s, gmulgs(gcoeff(x,i,j),y[j]));
    z[i] = lpileupto(av,s);
  }
  return z;
}
GEN
RgM_zc_mul(GEN x, GEN y) { return RgM_zc_mul_i(x,y, lg(x), lg(x[1])); }

/* x t_MAT, y a compatible zm (dimension > 0). */
GEN 
RgM_zm_mul(GEN x, GEN y)
{
  long j, c, l = lg(x), ly = lg(y);
  GEN z = cgetg(ly, t_MAT);
  if (l == 1) return z;
  c = lg(x[1]);
  for (j = 1; j < ly; j++) z[j] = (long)RgM_zc_mul_i(x, (GEN)y[j], l,c);
  return z;
}
static GEN
RgV_zc_mul_i(GEN x, GEN y, long l)
{
  long i;
  GEN z = gzero;
  pari_sp av = avma;
  for (i = 1; i < l; i++) z = gadd(z, gmulgs((GEN)x[i], y[i]));
  return gerepileupto(av, z);
}
GEN
RgV_zc_mul(GEN x, GEN y) { return RgV_zc_mul_i(x, y, lg(x)); }

GEN 
RgV_zm_mul(GEN x, GEN y)
{
  long j, l = lg(x), ly = lg(y);
  GEN z = cgetg(ly, t_VEC);
  for (j = 1; j < ly; j++) z[j] = (long)RgV_zc_mul_i(x, (GEN)y[j], l);
  return z;
}

/********************************************************************/
/**                                                                **/
/**                         COMPOSITION                            **/
/**                                                                **/
/********************************************************************/

/* evaluate f(x) mod T */
GEN
RgX_RgX_compo(GEN f, GEN x, GEN T)
{
  pari_sp av = avma, limit;
  long l;
  GEN y;

  if (typ(f) != t_POL) return gcopy(f);
  l = lg(f)-1; y = (GEN)f[l];
  limit = stack_lim(av, 1);
  for (l--; l>=2; l--)
  {
    y = grem(gadd(gmul(y,x), (GEN)f[l]), T);
    if (low_stack(limit,stack_lim(av,1)))
    {
      if (DEBUGMEM > 1) err(warnmem, "RgX_RgX_compo");
      y = gerepileupto(av, y);
    }
  }
  return gerepileupto(av, y);
}

/* return (1,...a^l) mod T. Not memory clean */
GEN
RgX_powers(GEN a, GEN T, long l)
{
  long i;
  GEN v;

  if (typ(a) != t_POL) err(typeer,"RgX_powers");
  l += 2;
  v = cgetg(l,t_VEC);
  v[1] = un; if (l == 2) return v;

  if (degpol(a) >= degpol(T)) a = grem(a, T);
  v[2] = (long)a;
  for (i=3; i<l; i++) v[i] = lres(gmul((GEN)v[i-1], a), T);
  return v;
}

/********************************************************************/
/**                                                                **/
/**                          CONVERSIONS                           **/
/**                       (not memory clean)                       **/
/**                                                                **/
/********************************************************************/

GEN
RgV_to_RgX(GEN x, long v)
{
  long i, k = lg(x);
  GEN p;

  while (--k && gcmp0((GEN)x[k]));
  if (!k) return zeropol(v);
  i = k+2; p = cgetg(i,t_POL);
  p[1] = evalsigne(1) | evalvarn(v);
  x--; for (k=2; k<i; k++) p[k] = x[k];
  return p;
}

/* return the (N-dimensional) vector of coeffs of p */
GEN
RgX_to_RgV(GEN x, long N)
{
  long i, l;
  GEN z = cgetg(N+1,t_COL);
  if (typ(x) != t_POL)
  {
    z[1] = (long)x;
    for (i=2; i<=N; i++) z[i]=zero;
    return z;
  }
  l = lg(x)-1; x++;
  for (i=1; i<l ; i++) z[i]=x[i];
  for (   ; i<=N; i++) z[i]=zero;
  return z;
}

/* vector of polynomials (in v) whose coeffs are given by the columns of x */
GEN
RgM_to_RgXV(GEN x, long v)
{
  long j, lx = lg(x);
  GEN y = cgetg(lx, t_VEC);
  for (j=1; j<lx; j++) y[j] = (long)RgV_to_RgX((GEN)x[j], v);
  return y;
}

/* matrix whose entries are given by the coeffs of the polynomials in
 * vector v (considered as degree n-1 polynomials) */
GEN
RgX_to_RgM(GEN v, long n)
{
  long j, N = lg(v);
  GEN y = cgetg(N, t_MAT);
  for (j=1; j<N; j++) y[j] = (long)RgX_to_RgV((GEN)v[j], n);
  return y;
}

/* polynomial (in v) of polynomials (in w) whose coeffs are given by the columns of x */
GEN
RgM_to_RgXX(GEN x, long v,long w)
{
  long j, lx = lg(x);
  GEN y = cgetg(lx+1, t_POL);
  y[1]=evalsigne(1) | evalvarn(v);
  y++;
  for (j=1; j<lx; j++) y[j] = (long)RgV_to_RgX((GEN)x[j], w);
  return normalizepol_i(--y, lx+1);
}

/* matrix whose entries are given by the coeffs of the polynomial v in
 * two variables (considered as degree n polynomials) */
GEN
RgXX_to_RgM(GEN v, long n)
{
  long j, N = lg(v)-1;
  GEN y = cgetg(N, t_MAT);
  v++;
  for (j=1; j<N; j++) y[j] = (long)RgX_to_RgV((GEN)v[j], n);
  return y;
}

/* P(X,Y) --> P(Y,X), n is an upper bound for deg_Y(P) */
GEN
RgXY_swap(GEN x, long n, long w)
{
  long j, lx = lg(x), ly = n+3;
  long v=varn(x);
  GEN y = cgetg(ly, t_POL);
  y[1]=evalsigne(1) | evalvarn(v);
  for (j=2; j<ly; j++)
  {
    long k;
    GEN p1=cgetg(lx,t_POL);
    p1[1] = evalsigne(1) | evalvarn(w);
    for (k=2; k<lx; k++)
      if( j<lg(x[k]))
        p1[k] = mael(x,k,j);
      else
        p1[k] = zero;
    y[j] = (long)normalizepol_i(p1,lx);
  }
  return normalizepol_i(y,ly);
}

GEN
RgX_shift(GEN a, long n)
{
  long i, l = lg(a);
  GEN  b;
  if (!signe(a)) return a;
  b = cgetg(l+n, t_POL);
  b[1] = a[1];
  for (i=0; i<n; i++) b[2+i] = zero;
  for (i=2; i<l; i++) b[i+n] = a[i];
  return b;
}

GEN
RgXQX_red(GEN P, GEN T)
{
  long i, l = lg(P);
  GEN Q = cgetg(l, t_POL);
  Q[1] = P[1];
  for (i=2; i<l; i++) Q[i] = lrem((GEN)P[i], T);
  return Q;
}

GEN
RgXQV_red(GEN P, GEN T)
{
  long i, l = lg(P);
  GEN Q = cgetg(l, typ(P));
  for (i=1; i<l; i++) Q[i] = lrem((GEN)P[i], T);
  return Q;
}

/*******************************************************************/
/*                                                                 */
/*                  KARATSUBA (for polynomials)                    */
/*                                                                 */
/*******************************************************************/

#if 1 /* for tunings */
long SQR_LIMIT = 6;
long MUL_LIMIT = 10;
long u_SQR_LIMIT = 6;
long u_MUL_LIMIT = 10;

void
setsqpol(long a) { SQR_LIMIT=a; u_SQR_LIMIT=a; }
void
setmulpol(long a) { MUL_LIMIT=a; u_MUL_LIMIT=a; }

GEN
u_specpol(GEN x, long nx)
{
  GEN z = cgetg(nx+2,t_POL);
  long i;
  for (i=0; i<nx; i++) z[i+2] = lstoi(x[i]);
  z[1] = evalsigne(1); return z;
}

GEN
specpol(GEN x, long nx)
{
  GEN z = cgetg(nx+2,t_POL);
  long i;
  for (i=0; i<nx; i++) z[i+2] = x[i];
  z[1] = evalsigne(1); return z;
}
#else
#  define SQR_LIMIT 6
#  define MUL_LIMIT 10
#endif

/* generic multiplication */

static GEN
addpol(GEN x, GEN y, long lx, long ly)
{
  long i,lz;
  GEN z;

  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx+2; z = cgetg(lz,t_POL) + 2;
  for (i=0; i<ly; i++) z[i]=ladd((GEN)x[i],(GEN)y[i]);
  for (   ; i<lx; i++) z[i]=x[i];
  z -= 2; z[1]=0; return normalizepol_i(z, lz);
}

static GEN
addpolcopy(GEN x, GEN y, long lx, long ly)
{
  long i,lz;
  GEN z;

  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx+2; z = cgetg(lz,t_POL) + 2;
  for (i=0; i<ly; i++) z[i]=ladd((GEN)x[i],(GEN)y[i]);
  for (   ; i<lx; i++) z[i]=lcopy((GEN)x[i]);
  z -= 2; z[1]=0; return normalizepol_i(z, lz);
}

INLINE GEN
mulpol_limb(GEN x, GEN y, char *ynonzero, long a, long b)
{
  GEN p1 = NULL;
  long i;
  pari_sp av = avma;
  for (i=a; i<b; i++)
    if (ynonzero[i])
    {
      GEN p2 = gmul((GEN)y[i],(GEN)x[-i]);
      p1 = p1 ? gadd(p1, p2): p2;
    }
  return p1 ? gerepileupto(av, p1): gzero;
}

/* assume nx >= ny > 0 */
static GEN
mulpol(GEN x, GEN y, long nx, long ny)
{
  long i,lz,nz;
  GEN z;
  char *p1;

  lz = nx+ny+1; nz = lz-2;
  z = cgetg(lz, t_POL) + 2; /* x:y:z [i] = term of degree i */
  p1 = gpmalloc(ny);
  for (i=0; i<ny; i++)
  {
    p1[i] = !isexactzero((GEN)y[i]);
    z[i] = (long)mulpol_limb(x+i,y,p1,0,i+1);
  }
  for (  ; i<nx; i++) z[i] = (long)mulpol_limb(x+i,y,p1,0,ny);
  for (  ; i<nz; i++) z[i] = (long)mulpol_limb(x+i,y,p1,i-nx+1,ny);
  free(p1); z -= 2; z[1]=0; return normalizepol_i(z, lz);
}

/* return (x * X^d) + y. Assume d > 0, y != 0 */
GEN
addmulXn(GEN x, GEN y, long d)
{
  GEN xd, yd, zd;
  long a, lz, nx, ny;
  
  if (!signe(x)) return y;
  ny = lgpol(y);
  nx = lgpol(x);
  zd = (GEN)avma;
  x += 2; y += 2; a = ny-d;
  if (a <= 0)
  {
    lz = (a>nx)? ny+2: nx+d+2;
    (void)new_chunk(lz); xd = x+nx; yd = y+ny;
    while (xd > x) *--zd = *--xd;
    x = zd + a;
    while (zd > x) *--zd = zero;
  }
  else
  {
    xd = new_chunk(d); yd = y+d;
    x = addpol(x,yd, nx,a);
    lz = (a>nx)? ny+2: lg(x)+d;
    x += 2; while (xd > x) *--zd = *--xd;
  }
  while (yd > y) *--zd = *--yd;
  *--zd = evalsigne(1);
  *--zd = evaltyp(t_POL) | evallg(lz); return zd;
}
/* return (x * X^d). Assume d >= 0 */
GEN
gmulXn(GEN x, long d)
{
  long i, l;
  GEN z;
  
  if (!signe(x)) return x;
  l = lg(x);
  z = cgetg(l + d, t_POL);
  z[1] = x[1];
  for (i = 2; i < l; i++) z[d + i] = x[i];
  for (i = 2; i < 2+d; i++) z[i] = zero;
  return z;
}

GEN
addshiftpol(GEN x, GEN y, long d)
{
  long v = varn(x);
  x = addmulXn(x,y,d);
  setvarn(x,v); return x;
}

/* as above, producing a clean malloc */
static GEN
addmulXncopy(GEN x, GEN y, long d)
{
  GEN xd, yd, zd;
  long a, lz, nx, ny;
  
  if (!signe(x)) return gcopy(y);
  nx = lgpol(x);
  ny = lgpol(y);
  zd = (GEN)avma;
  x += 2; y += 2; a = ny-d;
  if (a <= 0)
  {
    lz = nx+d+2;
    (void)new_chunk(lz); xd = x+nx; yd = y+ny;
    while (xd > x) *--zd = lcopy((GEN)*--xd);
    x = zd + a;
    while (zd > x) *--zd = zero;
  }
  else
  {
    xd = new_chunk(d); yd = y+d;
    x = addpolcopy(x,yd, nx,a);
    lz = (a>nx)? ny+2: lg(x)+d;
    x += 2; while (xd > x) *--zd = *--xd;
  }
  while (yd > y) *--zd = lcopy((GEN)*--yd);
  *--zd = evalsigne(1);
  *--zd = evaltyp(t_POL) | evallg(lz); return zd;
}

/* shift polynomial in place. assume v free cells have been left before x */
static GEN
shiftpol_ip(GEN x, long v)
{
  long i, lx;
  GEN y;
  if (v <= 0 || !signe(x)) return x;
  lx = lg(x);
  x += 2; y = x + v;
  for (i = lx-3; i>=0; i--) y[i] = x[i];
  for (i = 0   ; i< v; i++) x[i] = zero;
  lx += v;
  *--x = evalsigne(1);
  *--x = evaltyp(t_POL) | evallg(lx); return x;
}

/* fast product (Karatsuba) of polynomials a,b. These are not real GENs, a+2,
 * b+2 were sent instead. na, nb = number of terms of a, b.
 * Only c, c0, c1, c2 are genuine GEN.
 */
GEN
RgX_mulspec(GEN a, GEN b, long na, long nb)
{
  GEN a0, c, c0;
  long n0, n0a, i, v = 0;
  pari_sp av;

  while (na && isexactzero((GEN)a[0])) { a++; na--; v++; }
  while (nb && isexactzero((GEN)b[0])) { b++; nb--; v++; }
  if (na < nb) swapspec(a,b, na,nb);
  if (!nb) return zeropol(0);

  if (v) (void)cgetg(v,t_STR); /* v gerepile-safe cells for shiftpol_ip */
  if (nb < MUL_LIMIT)
    return shiftpol_ip(mulpol(a,b,na,nb), v);
  i = (na>>1); n0 = na-i; na = i;
  av = avma; a0 = a+n0; n0a = n0;
  while (n0a && isexactzero((GEN)a[n0a-1])) n0a--;

  if (nb > n0)
  {
    GEN b0,c1,c2;
    long n0b;

    nb -= n0; b0 = b+n0; n0b = n0;
    while (n0b && isexactzero((GEN)b[n0b-1])) n0b--;
    c = RgX_mulspec(a,b,n0a,n0b);
    c0 = RgX_mulspec(a0,b0, na,nb);

    c2 = addpol(a0,a, na,n0a);
    c1 = addpol(b0,b, nb,n0b);

    c1 = RgX_mulspec(c1+2,c2+2, lgpol(c1),lgpol(c2));
    c2 = gadd(c1, gneg_i(gadd(c0,c)));
    c0 = addmulXn(c0, c2, n0);
  }
  else
  {
    c = RgX_mulspec(a,b,n0a,nb);
    c0 = RgX_mulspec(a0,b,na,nb);
  }
  c0 = addmulXncopy(c0,c,n0);
  return shiftpol_ip(gerepileupto(av,c0), v);
}

static GEN
sqrpol(GEN x, long nx)
{
  long i, j, l, lz, nz;
  pari_sp av;
  GEN p1,z;
  char *p2;

  if (!nx) return zeropol(0);
  lz = (nx << 1) + 1, nz = lz-2;
  z = cgetg(lz,t_POL) + 2;
  p2 = gpmalloc(nx);
  for (i=0; i<nx; i++)
  {
    p2[i] = !isexactzero((GEN)x[i]);
    p1=gzero; av=avma; l=(i+1)>>1;
    for (j=0; j<l; j++)
      if (p2[j] && p2[i-j])
        p1 = gadd(p1, gmul((GEN)x[j],(GEN)x[i-j]));
    p1 = gshift(p1,1);
    if ((i&1) == 0 && p2[i>>1])
      p1 = gadd(p1, gsqr((GEN)x[i>>1]));
    z[i] = lpileupto(av,p1);
  }
  for (  ; i<nz; i++)
  {
    p1=gzero; av=avma; l=(i+1)>>1;
    for (j=i-nx+1; j<l; j++)
      if (p2[j] && p2[i-j])
        p1 = gadd(p1, gmul((GEN)x[j],(GEN)x[i-j]));
    p1 = gshift(p1,1);
    if ((i&1) == 0 && p2[i>>1])
      p1 = gadd(p1, gsqr((GEN)x[i>>1]));
    z[i] = lpileupto(av,p1);
  }
  free(p2); z -= 2; z[1]=0; return normalizepol_i(z,lz);
}

GEN
RgX_sqrspec(GEN a, long na)
{
  GEN a0, c, c0, c1;
  long n0, n0a, i, v = 0;
  pari_sp av;

  while (na && isexactzero((GEN)a[0])) { a++; na--; v += 2; }
  if (v) (void)new_chunk(v);
  if (na<SQR_LIMIT) return shiftpol_ip(sqrpol(a,na), v);
  i = (na>>1); n0 = na-i; na = i;
  av = avma; a0 = a+n0; n0a = n0;
  while (n0a && isexactzero((GEN)a[n0a-1])) n0a--;

  c = RgX_sqrspec(a,n0a);
  c0 = RgX_sqrspec(a0,na);
  c1 = gmul2n(RgX_mulspec(a0,a, na,n0a), 1);
  c0 = addmulXn(c0,c1, n0);
  c0 = addmulXncopy(c0,c,n0);
  return shiftpol_ip(gerepileupto(av,c0), v);
}
GEN
RgX_mul(GEN x,GEN y)
{
  GEN z = RgX_mulspec(y+2, x+2, lgpol(y), lgpol(x));
  setvarn(z,varn(x)); return z;
}
GEN
RgX_sqr(GEN x)
{
  GEN z = RgX_sqrspec(x+2, lgpol(x));
  setvarn(z,varn(x)); return z;
}

/*******************************************************************/
/*                                                                 */
/*                               DIVISION                          */
/*                                                                 */
/*******************************************************************/

/* x and y in (R[Y]/T)[X]  (lifted), T in R[Y]. y preferably monic */
GEN
RgXQX_divrem(GEN x, GEN y, GEN T, GEN *pr)
{
  long vx, dx, dy, dz, i, j, sx, lr;
  pari_sp av0, av, tetpil;
  GEN z,p1,rem,lead;

  if (!signe(y)) err(gdiver);
  vx = varn(x);
  dx = degpol(x);
  dy = degpol(y);
  if (dx < dy)
  {
    if (pr)
    {
      av0 = avma; x = RgXQX_red(x, T);
      if (pr == ONLY_DIVIDES) { avma=av0; return signe(x)? NULL: gzero; }
      if (pr == ONLY_REM) return x;
      *pr = x;
    }
    return zeropol(vx);
  }
  lead = leading_term(y);
  if (!dy) /* y is constant */
  {
    if (pr && pr != ONLY_DIVIDES)
    {
      if (pr == ONLY_REM) return zeropol(vx);
      *pr = zeropol(vx);
    }
    if (gcmp1(lead)) return gcopy(x);
    av0 = avma; x = gmul(x, ginvmod(lead,T)); tetpil = avma;
    return gerepile(av0,tetpil,RgXQX_red(x,T));
  }
  av0 = avma; dz = dx-dy;
  lead = gcmp1(lead)? NULL: gclone(ginvmod(lead,T));
  avma = av0;
  z = cgetg(dz+3,t_POL); z[1] = x[1];
  x += 2; y += 2; z += 2;

  p1 = (GEN)x[dx]; av = avma;
  z[dz] = lead? lpileupto(av, grem(gmul(p1,lead), T)): lcopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av=avma; p1=(GEN)x[i];
    for (j=i-dy+1; j<=i && j<=dz; j++)
      p1 = gsub(p1, gmul((GEN)z[j],(GEN)y[i-j]));
    if (lead) p1 = gmul(grem(p1, T), lead);
    tetpil=avma; z[i-dy] = lpile(av,tetpil, grem(p1, T));
  }
  if (!pr) { if (lead) gunclone(lead); return z-2; }

  rem = (GEN)avma; av = (pari_sp)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = (GEN)x[i];
    for (j=0; j<=i && j<=dz; j++)
      p1 = gsub(p1, gmul((GEN)z[j],(GEN)y[i-j]));
    tetpil=avma; p1 = grem(p1, T); if (signe(p1)) { sx = 1; break; }
    if (!i) break;
    avma=av;
  }
  if (pr == ONLY_DIVIDES)
  {
    if (lead) gunclone(lead);
    if (sx) { avma=av0; return NULL; }
    avma = (pari_sp)rem; return z-2;
  }
  lr=i+3; rem -= lr;
  rem[0] = evaltyp(t_POL) | evallg(lr);
  rem[1] = z[-1];
  p1 = gerepile((pari_sp)rem,tetpil,p1);
  rem += 2; rem[i]=(long)p1;
  for (i--; i>=0; i--)
  {
    av=avma; p1 = (GEN)x[i];
    for (j=0; j<=i && j<=dz; j++)
      p1 = gsub(p1, gmul((GEN)z[j],(GEN)y[i-j]));
    tetpil=avma; rem[i]=lpile(av,tetpil, grem(p1, T));
  }
  rem -= 2;
  if (lead) gunclone(lead);
  if (!sx) (void)normalizepol_i(rem, lr);
  if (pr == ONLY_REM) return gerepileupto(av0,rem);
  *pr = rem; return z-2;
}

GEN
RgXQX_mul(GEN x, GEN y, GEN T)
{
  return RgXQX_red(RgX_mul(x,y), T);
}
GEN
RgX_Rg_mul(GEN y, GEN x) {
  long i, ly;
  GEN z;
  if (isexactzero(x)) { long vy = varn(y); return zeropol(vy); }
  ly = lg(y);
  z = cgetg(ly,t_POL); z[1] = y[1];
  if (ly == 2) return z;
  for (i = 2; i < ly; i++) z[i] = lmul(x,(GEN)y[i]);
  return normalizepol_i(z,ly);
}
GEN
RgXQX_RgXQ_mul(GEN x, GEN y, GEN T)
{
  return RgXQX_red(RgX_Rg_mul(x,y), T);
}
GEN
RgXQX_sqr(GEN x, GEN T)
{
  return RgXQX_red(RgX_sqr(x), T);
}
