/* $Id$

Copyright (C) 2012  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#include "pari.h"
#include "paripriv.h"

/* Not so fast arithmetic with polynomials over FpX */

/*******************************************************************/
/*                                                                 */
/*                             FpXX                                */
/*                                                                 */
/*******************************************************************/
/*Polynomials whose coefficients are either polynomials or integers*/
GEN
FpXX_red(GEN z, GEN p)
{
  GEN res;
  long i, l = lg(z);
  res = cgetg(l,t_POL); res[1] = z[1];
  for (i=2; i<l; i++)
  {
    GEN zi = gel(z,i), c;
    if (typ(zi)==t_INT)
      c = modii(zi,p);
    else
    {
      pari_sp av = avma;
      c = FpX_red(zi,p);
      switch(lg(c)) {
        case 2: avma = av; c = gen_0; break;
        case 3: c = gerepilecopy(av, gel(c,2)); break;
      }
    }
    gel(res,i) = c;
  }
  return FpXX_renormalize(res,lg(res));
}
GEN
FpXX_add(GEN x, GEN y, GEN p)
{
  long i,lz;
  GEN z;
  long lx=lg(x);
  long ly=lg(y);
  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx; z = cgetg(lz, t_POL); z[1]=x[1];
  for (i=2; i<ly; i++) gel(z,i) = Fq_add(gel(x,i), gel(y,i), NULL, p);
  for (   ; i<lx; i++) gel(z,i) = gcopy(gel(x,i));
  return FpXX_renormalize(z, lz);
}
GEN
FpXX_sub(GEN x, GEN y, GEN p)
{
  long i,lz;
  GEN z;
  long lx=lg(x);
  long ly=lg(y);
  if (ly <= lx)
  {
    lz = lx; z = cgetg(lz, t_POL); z[1]=x[1];
    for (i=2; i<ly; i++) gel(z,i) = Fq_sub(gel(x,i), gel(y,i), NULL, p);
    for (   ; i<lx; i++) gel(z,i) = gcopy(gel(x,i));
  }
  else
  {
    lz = ly; z = cgetg(lz, t_POL); z[1]=x[1];
    for (i=2; i<lx; i++) gel(z,i) = Fq_sub(gel(x,i), gel(y,i), NULL, p);
    for (   ; i<ly; i++) gel(z,i) = Fq_neg(gel(y,i), NULL, p);
  }
  return FpXX_renormalize(z, lz);
}

GEN
FpXX_neg(GEN x, GEN p)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx,t_POL);
  y[1] = x[1];
  for(i=2; i<lx; i++) gel(y,i) = Fq_neg(gel(x,i), NULL, p);
  return FpXX_renormalize(y, lx);
}

GEN
FpXX_Fp_mul(GEN P, GEN u, GEN p)
{
  long i, lP;
  GEN res = cgetg_copy(P, &lP); res[1] = P[1];
  for(i=2; i<lP; i++)
  {
    GEN x = gel(P,i);
    gel(res,i) = typ(x)==t_INT? Fp_mul(x,u,p): FpX_Fp_mul(x,u,p);
  }
  return FpXX_renormalize(res,lP);
}

GEN
FpXX_mulu(GEN P, ulong u, GEN p)
{
  long i, lP;
  GEN res = cgetg_copy(P, &lP); res[1] = P[1];
  for(i=2; i<lP; i++)
  {
    GEN x = gel(P,i);
    gel(res,i) = typ(x)==t_INT? Fp_mulu(x,u,p): FpX_mulu(x,u,p);
  }
  return FpXX_renormalize(res,lP);
}

/*******************************************************************/
/*                                                                 */
/*                             (Fp[X]/(Q))[Y]                      */
/*                                                                 */
/*******************************************************************/
/*Not malloc nor warn-clean.*/
GEN
Kronecker_to_FpXQX(GEN Z, GEN T, GEN p)
{
  long i,j,lx,l, N = (degpol(T)<<1) + 1;
  GEN x, t = cgetg(N,t_POL), z = FpX_red(Z, p);
  t[1] = T[1];
  l = lg(z); lx = (l-2) / (N-2);
  x = cgetg(lx+3,t_POL);
  x[1] = z[1];
  for (i=2; i<lx+2; i++)
  {
    for (j=2; j<N; j++) gel(t,j) = gel(z,j);
    z += (N-2);
    gel(x,i) = FpX_rem(FpX_renormalize(t,N), T,p);
  }
  N = (l-2) % (N-2) + 2;
  for (j=2; j<N; j++) gel(t,j) = gel(z,j);
  gel(x,i) = FpX_rem(FpX_renormalize(t,N), T,p);
  return FpXQX_renormalize(x, i+1);
}

GEN
FpXQX_red(GEN z, GEN T, GEN p)
{
  long i, l = lg(z);
  GEN res = cgetg(l,t_POL); res[1] = z[1];
  for(i=2;i<l;i++)
    if (typ(gel(z,i)) == t_INT)
      gel(res,i) = modii(gel(z,i),p);
    else
      gel(res,i) = FpXQ_red(gel(z,i),T,p);
  return FpXQX_renormalize(res,l);
}

GEN
FpXQX_mul(GEN x, GEN y, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z, kx, ky;
  kx = mod_to_Kronecker(x,T);
  ky = mod_to_Kronecker(y,T);
  z = Kronecker_to_FpXQX(ZX_mul(ky,kx), T, p);
  return gerepileupto(av, z);
}

GEN
FpXQX_sqr(GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z, kx;
  kx= mod_to_Kronecker(x,T);
  z = Kronecker_to_FpXQX(ZX_sqr(kx), T, p);
  return gerepileupto(av, z);
}

GEN
FpXQX_FpXQ_mul(GEN P, GEN U, GEN T, GEN p)
{
  long i, lP;
  GEN res;
  res = cgetg_copy(P, &lP); res[1] = P[1];
  for(i=2; i<lP; i++)
    gel(res,i) = typ(gel(P,i))==t_INT? FpX_Fp_mul(U, gel(P,i), p):
                                       FpXQ_mul(U, gel(P,i), T,p);
  return FpXQX_renormalize(res,lP);
}

/* x and y in Z[Y][X]. Assume T irreducible mod p */
GEN
FpXQX_divrem(GEN x, GEN y, GEN T, GEN p, GEN *pr)
{
  long vx, dx, dy, dz, i, j, sx, lr;
  pari_sp av0, av, tetpil;
  GEN z,p1,rem,lead;

  if (!T) return FpX_divrem(x,y,p,pr);
  if (!signe(y)) pari_err_INV("FpX_divrem",y);
  vx=varn(x); dy=degpol(y); dx=degpol(x);
  if (dx < dy)
  {
    if (pr)
    {
      av0 = avma; x = FpXQX_red(x, T, p);
      if (pr == ONLY_DIVIDES) { avma=av0; return signe(x)? NULL: pol_0(vx); }
      if (pr == ONLY_REM) return x;
      *pr = x;
    }
    return pol_0(vx);
  }
  lead = leading_term(y);
  if (!dy) /* y is constant */
  {
    if (pr && pr != ONLY_DIVIDES)
    {
      if (pr == ONLY_REM) return pol_0(vx);
      *pr = pol_0(vx);
    }
    if (gequal1(lead)) return FpXQX_red(x,T,p);
    av0 = avma; x = FqX_Fq_mul(x, Fq_inv(lead, T,p), T,p);
    return gerepileupto(av0,x);
  }
  av0 = avma; dz = dx-dy;
  if (lgefint(p) == 3)
  { /* assume ab != 0 mod p */
    {
      GEN *gptr[2];
      ulong pp = (ulong)p[2];
      long v = varn(T);
      GEN a = ZXX_to_FlxX(x, pp, v);
      GEN b = ZXX_to_FlxX(y, pp, v);
      GEN t = ZX_to_Flx(T, pp);
      z = FlxqX_divrem(a,b,t,pp,pr);
      tetpil=avma;
      z = FlxX_to_ZXX(z);
      if (pr && pr != ONLY_DIVIDES && pr != ONLY_REM)
        *pr = FlxX_to_ZXX(*pr);
      else return gerepile(av0,tetpil,z);
      gptr[0]=pr; gptr[1]=&z;
      gerepilemanysp(av0,tetpil,gptr,2);
      return z;
    }
  }
  lead = gequal1(lead)? NULL: gclone(Fq_inv(lead,T,p));
  avma = av0;
  z = cgetg(dz+3,t_POL); z[1] = x[1];
  x += 2; y += 2; z += 2;

  p1 = gel(x,dx); av = avma;
  gel(z,dz) = lead? gerepileupto(av, Fq_mul(p1,lead, T, p)): gcopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av=avma; p1=gel(x,i);
    for (j=i-dy+1; j<=i && j<=dz; j++)
      p1 = Fq_sub(p1, Fq_mul(gel(z,j),gel(y,i-j),NULL,p),NULL,p);
    if (lead) p1 = Fq_mul(p1, lead, NULL,p);
    tetpil=avma; gel(z,i-dy) = gerepile(av,tetpil,Fq_red(p1,T,p));
  }
  if (!pr) { if (lead) gunclone(lead); return z-2; }

  rem = (GEN)avma; av = (pari_sp)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++)
      p1 = Fq_sub(p1, Fq_mul(gel(z,j),gel(y,i-j),NULL,p),NULL,p);
    tetpil=avma; p1 = Fq_red(p1, T, p); if (signe(p1)) { sx = 1; break; }
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
  rem += 2; gel(rem,i) = p1;
  for (i--; i>=0; i--)
  {
    av=avma; p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++)
      p1 = Fq_sub(p1, Fq_mul(gel(z,j),gel(y,i-j), NULL,p), NULL,p);
    tetpil=avma; gel(rem,i) = gerepile(av,tetpil, Fq_red(p1, T, p));
  }
  rem -= 2;
  if (lead) gunclone(lead);
  if (!sx) (void)FpXQX_renormalize(rem, lr);
  if (pr == ONLY_REM) return gerepileupto(av0,rem);
  *pr = rem; return z-2;
}

GEN
FpXQX_gcd(GEN P, GEN Q, GEN T, GEN p)
{
  pari_sp av=avma, av0;
  GEN R;
  if (lgefint(p) == 3)
  {
    ulong pp = (ulong)p[2];
    GEN Pl, Ql, Tl, U;
    Pl = ZXX_to_FlxX(P, pp, varn(T));
    Ql = ZXX_to_FlxX(Q, pp, varn(T));
    Tl = ZX_to_Flx(T, pp);
    U  = FlxqX_gcd(Pl, Ql, Tl, pp);
    return gerepileupto(av, FlxX_to_ZXX(U));
  }
  P = FpXX_red(P, p); av0 = avma;
  Q = FpXX_red(Q, p);
  while (signe(Q))
  {
    av0 = avma; R = FpXQX_rem(P,Q,T,p); P=Q; Q=R;
  }
  avma = av0; return gerepileupto(av, P);
}

/* x and y in Z[Y][X], return lift(gcd(x mod T,p, y mod T,p)). Set u and v st
 * ux + vy = gcd (mod T,p) */
GEN
FpXQX_extgcd(GEN x, GEN y, GEN T, GEN p, GEN *ptu, GEN *ptv)
{
  GEN a, b, q, r, u, v, d, d1, v1;
  long vx = varn(x);
  pari_sp ltop=avma;
  if (lgefint(p) == 3)
  {
    ulong pp = (ulong)p[2];
    GEN Pl, Ql, Tl, Dl;
    Pl = ZXX_to_FlxX(x, pp, varn(T));
    Ql = ZXX_to_FlxX(y, pp, varn(T));
    Tl = ZX_to_Flx(T, pp);
    Dl = FlxqX_extgcd(Pl, Ql, Tl, pp, ptu, ptv);
    if (ptu) *ptu = FlxX_to_ZXX(*ptu);
    *ptv = FlxX_to_ZXX(*ptv);
    d = FlxX_to_ZXX(Dl);
  }
  else
  {
    a = FpXQX_red(x, T, p);
    b = FpXQX_red(y, T, p);
    d = a; d1 = b; v = pol_0(vx); v1 = pol_1(vx);
    while (signe(d1))
    {
      q = FqX_divrem(d,d1,T,p, &r);
      v = FqX_sub(v, FqX_mul(q,v1, T,p), T,p);
      u=v; v=v1; v1=u;
      u=r; d=d1; d1=u;
    }
    if (ptu) *ptu = FqX_div(FqX_sub(d, FqX_mul(b,v, T,p), T,p),a, T,p);
    *ptv = v;
  }
  gerepileall(ltop,ptu?3:2,&d,ptv,ptu);
  return d;
}
struct _FpXQX { GEN T,p; };
static GEN _FpXQX_mul(void *data, GEN a,GEN b)
{
  struct _FpXQX *d=(struct _FpXQX*)data;
  return FpXQX_mul(a,b,d->T,d->p);
}
GEN
FpXQXV_prod(GEN V, GEN T, GEN p)
{
  if (lgefint(p) == 3)
  {
    pari_sp av = avma;
    ulong pp = p[2];
    GEN Tl = ZX_to_Flx(T, pp);
    GEN Vl = ZXXV_to_FlxXV(V, pp, varn(T));
    Tl = FlxqXV_prod(Vl, Tl, pp);
    return gerepileupto(av, FlxX_to_ZXX(Tl));
  }
  else
  {
    struct _FpXQX d;
    d.p=p;
    d.T=T;
    return divide_conquer_assoc(V, (void*)&d, &_FpXQX_mul);
  }
}

/* Q an FpXY (t_POL with FpX coeffs), evaluate at X = x */
GEN
FpXY_evalx(GEN Q, GEN x, GEN p)
{
  long i, lb = lg(Q);
  GEN z;
  z = cgetg(lb, t_POL); z[1] = Q[1];
  for (i=2; i<lb; i++)
  {
    GEN q = gel(Q,i);
    gel(z,i) = typ(q) == t_INT? modii(q,p): FpX_eval(q, x, p);
  }
  return FpX_renormalize(z, lb);
}
/* Q an FpXY, evaluate at Y = y */
GEN
FpXY_evaly(GEN Q, GEN y, GEN p, long vx)
{
  pari_sp av = avma;
  long i, lb = lg(Q);
  GEN z;
  if (lb == 2) return pol_0(vx);
  z = gel(Q, lb-1);
  if (lb == 3 || !signe(y)) return typ(z)==t_INT? scalar_ZX(z, vx): ZX_copy(z);

  if (typ(z) == t_INT) z = scalar_ZX_shallow(z, vx);
  for (i=lb-2; i>=2; i--) z = Fq_add(gel(Q,i), FpX_Fp_mul(z, y, p), NULL, p);
  return gerepileupto(av, z);
}
/* Q an FpXY, evaluate at (X,Y) = (x,y) */
GEN
FpXY_eval(GEN Q, GEN y, GEN x, GEN p)
{
  pari_sp av = avma;
  return gerepileuptoint(av, FpX_eval(FpXY_evalx(Q, x, p), y, p));
}

/*******************************************************************/
/*                                                                 */
/*                       (Fp[X]/T(X))[Y] / S(Y)                    */
/*                                                                 */
/*******************************************************************/

/*Preliminary implementation to speed up FpX_ffisom*/
typedef struct {
  GEN S, T, p;
} FpXYQQ_muldata;

/* reduce x in Fp[X, Y] in the algebra Fp[X, Y]/ (P(X),Q(Y)) */
static GEN
FpXYQQ_redswap(GEN x, GEN S, GEN T, GEN p)
{
  pari_sp ltop=avma;
  long n=degpol(S);
  long m=degpol(T);
  long v=varn(T),w=varn(S);
  GEN V = RgXY_swap(x,n,w);
  setvarn(T,w);
  V = FpXQX_red(V,T,p);
  setvarn(T,v);
  V = RgXY_swap(V,m,w);
  return gerepilecopy(ltop,V);
}
static GEN
FpXYQQ_sqr(void *data, GEN x)
{
  FpXYQQ_muldata *D = (FpXYQQ_muldata*)data;
  return FpXYQQ_redswap(FpXQX_sqr(x, D->S, D->p),D->S,D->T,D->p);

}
static GEN
FpXYQQ_mul(void *data, GEN x, GEN y)
{
  FpXYQQ_muldata *D = (FpXYQQ_muldata*)data;
  return FpXYQQ_redswap(FpXQX_mul(x,y, D->S, D->p),D->S,D->T,D->p);
}

/* x in Z[X,Y], S in Z[X] over Fq = Z[Y]/(p,T); compute lift(x^n mod (S,T,p)) */
GEN
FpXYQQ_pow(GEN x, GEN n, GEN S, GEN T, GEN p)
{
  pari_sp av = avma;
  FpXYQQ_muldata D;
  GEN y;
  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    x = ZXX_to_FlxX(x, pp, varn(T));
    S = ZX_to_Flx(S, pp);
    T = ZX_to_Flx(T, pp);
    y = FlxX_to_ZXX( FlxYqQ_pow(x, n, S, T, pp) );
  }
  else
  {
    D.S = S;
    D.T = T;
    D.p = p;
    y = gen_pow(x, n, (void*)&D, &FpXYQQ_sqr, &FpXYQQ_mul);
  }
  return gerepileupto(av, y);
}

GEN
FpXQXQ_mul(GEN x, GEN y, GEN S, GEN T, GEN p) {
  GEN kx = mod_to_Kronecker(x, T);
  GEN ky = mod_to_Kronecker(y, T);
  GEN t = Kronecker_to_FpXQX(ZX_mul(kx, ky), T, p);
  return FpXQX_rem(t, S, T, p);
}

GEN
FpXQXQ_sqr(GEN x, GEN S, GEN T, GEN p) {
  GEN kx = mod_to_Kronecker(x, T);
  GEN t = Kronecker_to_FpXQX(ZX_sqr(kx), T, p);
  return FpXQX_rem(t, S, T, p);
}

/* Inverse of x in Z/pZ[X]/(pol) or NULL if inverse doesn't exist
 * return lift(1 / (x mod (p,pol))) */
GEN
FpXQXQ_invsafe(GEN x, GEN S, GEN T, GEN p)
{
  GEN V, z = FpXQX_extgcd(S, x, T, p, NULL, &V);
  if (degpol(z)) return NULL;
  z = gel(z,2);
  z = typ(z)==t_INT ? Fp_invsafe(z,p) : FpXQ_invsafe(z,T,p);
  if (!z) return NULL;
  return typ(z)==t_INT ? FpXX_Fp_mul(V, z, p): FpXQX_FpXQ_mul(V, z, T, p);
}

GEN
FpXQXQ_inv(GEN x, GEN S, GEN T,GEN p)
{
  pari_sp av = avma;
  GEN U = FpXQXQ_invsafe(x, S, T, p);
  if (!U) pari_err_INV("FpXQXQ_inv",x);
  return gerepileupto(av, U);
}

GEN
FpXQXQ_div(GEN x,GEN y,GEN S, GEN T,GEN p)
{
  pari_sp av = avma;
  return gerepileupto(av, FpXQXQ_mul(x, FpXQXQ_inv(y,S,T,p),S,T,p));
}

struct FpXQXQ_muldata
{
  GEN S, T, p;
};

static GEN
_FpXQXQ_mul(void *data, GEN x, GEN y) {
  struct FpXQXQ_muldata *d = (struct FpXQXQ_muldata *) data;
  return FpXQXQ_mul(x,y,d->S,d->T,d->p);
}
static GEN
_FpXQXQ_sqr(void *data, GEN x) {
  struct FpXQXQ_muldata *d = (struct FpXQXQ_muldata *) data;
  return FpXQXQ_sqr(x,d->S,d->T,d->p);
}

static GEN
_FpXQXQ_one(void *data) {
  struct FpXQXQ_muldata *d = (struct FpXQXQ_muldata *) data;
  return pol_1(varn(d->S));
}

/* x over Fq, return lift(x^n) mod S */
GEN
FpXQXQ_pow(GEN x, GEN n, GEN S, GEN T, GEN p)
{
  pari_sp ltop = avma;
  GEN y;
  struct FpXQXQ_muldata D;
  long s = signe(n);
  if (!s) return pol_1(varn(x));
  if (is_pm1(n)) /* +/- 1 */
    return (s < 0)? FpXQXQ_inv(x,S,T,p): gcopy(x);
  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    GEN z;
    long v = varn(T);
    T = ZX_to_Flx(T, pp);
    x = ZXX_to_FlxX(x, pp, v);
    S = ZXX_to_FlxX(S, pp, v);
    z = FlxqXQ_pow(x, n, S, T, pp);
    y = FlxX_to_ZXX(z);
  }
  else
  {
    D.S = S; D.T = T; D.p = p;
    if (s < 0) x = FpXQXQ_inv(x,S,T,p);
    y = gen_pow(x, n, (void*)&D,&_FpXQXQ_sqr,&_FpXQXQ_mul);
  }
  return gerepileupto(ltop, y);
}

/* generates the list of powers of x of degree 0,1,2,...,l*/
GEN
FpXQXQ_powers(GEN x, long l, GEN S, GEN T, GEN p)
{
  struct FpXQXQ_muldata D;
  int use_sqr = (degpol(x)<<1)>=degpol(T);
  D.S = S; D.T = T; D.p = p;
  return gen_powers(x, l, use_sqr, (void*)&D, &_FpXQXQ_sqr, &_FpXQXQ_mul,&_FpXQXQ_one);
}

GEN
FpXQXQ_matrix_pow(GEN y, long n, long m, GEN S, GEN T, GEN p)
{
  return RgXV_to_RgM(FpXQXQ_powers(y,m-1,S,T,p),n);
}
