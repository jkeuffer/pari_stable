/* $Id: ZX.c 9634 2008-02-12 14:48:34Z kb $

Copyright (C) 2007  The PARI group.

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

/*******************************************************************/
/*                                                                 */
/*                                ZX                               */
/*                                                                 */
/*******************************************************************/
static int
_check_ZX(GEN x)
{
  long k = lg(x)-1;
  for ( ; k>1; k--)
    if (typ(x[k])!=t_INT) return 0;
  return 1;
}

void
RgX_check_ZX(GEN x, const char *s)
{
  if (! _check_ZX(x)) pari_err(talker,"polynomial not in Z[X] in %s",s);
}
void
RgX_check_ZXY(GEN x, const char *s)
{
  long k = lg(x)-1;
  for ( ; k>1; k--) {
    GEN t = gel(x,k);
    switch(typ(t)) {
      case t_INT: break;
      case t_POL: if (_check_ZX(t)) break;
      /* fall through */
      default: pari_err(talker,"polynomial not in Z[X,Y] in %s",s);
    }
  }
}

long
ZXY_max_lg(GEN x)
{
  long i, prec = 0, lx = lg(x);
  for (i=2; i<lx; i++)
  {
    GEN p = gel(x,i);
    long l = (typ(p) == t_INT)? lgefint(p): ZX_max_lg(p);
    if (l > prec) prec = l;
  }
  return prec;
}
long
ZX_max_lg(GEN x)
{
  long i, prec = 0, lx = lg(x);

  for (i=2; i<lx; i++) { long l = lgefint(x[i]); if (l > prec) prec = l; }
  return prec;
}

/*Renormalize (in place) polynomial with t_INT or t_POL coefficients.*/
GEN
ZX_renormalize(GEN x, long lx)
{
  long i;
  for (i = lx-1; i>1; i--)
    if (signe(gel(x,i))) break;
  stackdummy((pari_sp)(x + lg(x)), (pari_sp)(x + (i+1)));
  setlg(x, i+1); setsigne(x, i!=1); return x;
}

GEN
ZX_add(GEN x, GEN y)
{
  long lx,ly,i;
  GEN z;
  lx = lg(x); ly = lg(y); if (lx < ly) swapspec(x,y, lx,ly);
  z = cgetg(lx,t_POL); z[1] = x[1];
  for (i=2; i<ly; i++) gel(z,i) = addii(gel(x,i),gel(y,i));
  for (   ; i<lx; i++) gel(z,i) = icopy(gel(x,i));
  if (lx == ly) z = ZX_renormalize(z, lx);
  if (!lgpol(z)) { avma = (pari_sp)(z + lx); return zeropol(varn(x)); }
  return z;
}

GEN
ZX_sub(GEN x,GEN y)
{
  long i, lx = lg(x), ly = lg(y);
  GEN z;
  if (lx >= ly)
  {
    z = cgetg(lx,t_POL); z[1] = x[1];
    for (i=2; i<ly; i++) gel(z,i) = subii(gel(x,i),gel(y,i));
    if (lx == ly)
    {
      z = ZX_renormalize(z, lx);
      if (!lgpol(z)) { avma = (pari_sp)(z + lx); z = zeropol(varn(x)); }
    }
    else
      for (   ; i<lx; i++) gel(z,i) = icopy(gel(x,i));
  }
  else
  {
    z = cgetg(ly,t_POL); z[1] = y[1];
    for (i=2; i<lx; i++) gel(z,i) = subii(gel(x,i),gel(y,i));
    for (   ; i<ly; i++) gel(z,i) = negi(gel(y,i));
  }
  return z;
}

GEN
ZX_neg(GEN x)
{
  long i, l = lg(x);
  GEN y = cgetg(l,t_POL);
  y[1] = x[1]; for(i=2; i<l; i++) gel(y,i) = negi(gel(x,i));
  return y;
}
GEN
ZX_copy(GEN x)
{
  long i, l = lg(x);
  GEN y = cgetg(l, t_POL);
  y[1] = x[1];
  for (i=2; i<l; i++)
  {
    GEN c = gel(x,i);
    gel(y,i) = lgefint(c) == 2? gen_0: icopy(c);
  }
  return y;
}

GEN
scalar_ZX(GEN x, long v)
{
  GEN z;
  if (!signe(x)) return zeropol(v);
  z = cgetg(3, t_POL);
  z[1] = evalsigne(1) | evalvarn(v);
  gel(z,2) = icopy(x); return z;
}

GEN
scalar_ZX_shallow(GEN x, long v)
{
  GEN z;
  if (!signe(x)) return zeropol(v);
  z = cgetg(3, t_POL);
  z[1] = evalsigne(1) | evalvarn(v);
  gel(z,2) = x; return z;
}

GEN
ZX_Z_add(GEN y, GEN x)
{
  long lz, i;
  GEN z = cgetg_copy(y, &lz);
  if (lz == 2) { avma = (pari_sp)(z + 2); return scalar_ZX(x,varn(y)); }
  z[1] = y[1];
  gel(z,2) = addii(gel(y,2),x);
  for(i=3; i<lz; i++) gel(z,i) = icopy(gel(y,i));
  if (lz==3) z = ZX_renormalize(z,lz);
  return z;
}

GEN
ZX_Z_sub(GEN y, GEN x)
{
  long lz, i;
  GEN z = cgetg_copy(y, &lz);
  if (lz == 2)
  { /* scalarpol(negi(x), v) */
    long v = varn(y);
    avma = (pari_sp)(z + 2);
    if (!signe(x)) return zeropol(v);
    z = cgetg(3,t_POL);
    z[1] = evalvarn(v) | evalsigne(1);
    gel(z,2) = negi(x); return z;
  }
  z[1] = y[1];
  gel(z,2) = subii(gel(y,2),x);
  for(i=3; i<lz; i++) gel(z,i) = icopy(gel(y,i));
  if (lz==3) z = ZX_renormalize(z,lz);
  return z;
}

GEN
Z_ZX_sub(GEN x, GEN y)
{
  long lz, i;
  GEN z = cgetg_copy(y, &lz);
  if (lz == 2) { avma = (pari_sp)(z + 2); return scalar_ZX(x,varn(y)); }
  z[1] = y[1];
  gel(z,2) = subii(x, gel(y,2));
  for(i=3; i<lz; i++) gel(z,i) = negi(gel(y,i));
  if (lz==3) z = ZX_renormalize(z,lz);
  return z;
}

GEN
ZX_Z_divexact(GEN y,GEN x)
{
  long i, l = lg(y);
  GEN z = cgetg(l,t_POL); z[1] = y[1];
  for(i=2; i<l; i++) gel(z,i) = diviiexact(gel(y,i),x);
  return z;
}

GEN
ZX_Z_mul(GEN y,GEN x)
{
  GEN z;
  long i, l;
  if (!signe(x)) return zeropol(varn(y));
  l = lg(y); z = cgetg(l,t_POL); z[1] = y[1];
  for(i=2; i<l; i++) gel(z,i) = mulii(gel(y,i),x);
  return z;
}

GEN
ZXV_Z_mul(GEN y, GEN x)
{
  long i, l;
  GEN z = cgetg_copy(y, &l);
  for(i=1; i<l; i++) gel(z,i) = ZX_Z_mul(gel(y,i), x);
  return z;
}

GEN
zx_to_ZX(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_POL);
  for (i=2; i<l; i++) gel(x,i) = stoi(z[i]);
  x[1] = evalsigne(l-2!=0)| z[1]; return x;
}

GEN
ZX_deriv(GEN x)
{
  long i,lx = lg(x)-1;
  GEN y;

  if (lx<3) return zeropol(varn(x));
  y = cgetg(lx,t_POL);
  for (i=2; i<lx ; i++) gel(y,i) = mului(i-1,gel(x,i+1));
  y[1] = x[1]; return y;
}

int
ZX_equal(GEN V, GEN W)
{
  long i, l = lg(V);
  if (lg(W) != l || V[1] != W[1]) return 0;
  for (i = 2; i < l; i++)
    if (!equalii(gel(V,i), gel(W,i))) return 0;
  return 1;
}

long
ZX_val(GEN x)
{
  long vx;
  if (!signe(x)) return LONG_MAX;
  for (vx = 0;; vx++)
    if (signe(gel(x,2+vx))) break;
  return vx;
}
long
ZX_valrem(GEN x, GEN *Z)
{
  long vx;
  if (!signe(x)) { *Z = zeropol(varn(x)); return LONG_MAX; }
  for (vx = 0;; vx++)
    if (signe(gel(x,2+vx))) break;
  *Z = RgX_shift_shallow(x, -vx);
  return vx;
}

/* Return h^degpol(P) P(x / h), not memory clean. h integer, P ZX */
GEN
ZX_rescale(GEN P, GEN h)
{
  long i, l = lg(P);
  GEN Q = cgetg(l,t_POL), hi = h;
  Q[l-1] = P[l-1];
  for (i=l-2; i>=2; i--)
  {
    gel(Q,i) = mulii(gel(P,i), hi);
    if (i == 2) break;
    hi = mulii(hi,h);
  }
  Q[1] = P[1]; return Q;
}

/*Eval x in 2^(k*BIL) in linear time; assume x non-constant */
static GEN
ZX_eval2BIL(GEN x, long k)
{
  long i,j, l = lgpol(x), lz = k*l, ki;
  GEN pz = cgetipos(2+lz);
  GEN nz = cgetipos(2+lz);
  for(i=0; i < lz; i++)
  {
    *int_W(pz,i) = 0UL;
    *int_W(nz,i) = 0UL;
  }
  for(i=0, ki=0; i<l; i++, ki+=k)
  {
    GEN c = gel(x,2+i);
    long lc = lgefint(c)-2;
    if (signe(c)==0) continue;
    if (signe(c) > 0)
      for (j=0; j<lc; j++) *int_W(pz,j+ki) = *int_W(c,j);
    else
      for (j=0; j<lc; j++) *int_W(nz,j+ki) = *int_W(c,j);
  }
  pz = int_normalize(pz,0);
  nz = int_normalize(nz,0); return subii(pz,nz);
}

#if 0
static long
ZX_expi(GEN x)
{
  long i, m = 0;
  for(i = 2; i < lg(x); i++)
  {
    long e = expi(gel(x,i));
    if (e > m) m = e;
  }
  return m;
}
#endif

/* x != 0 a ZX */
static long
ZX_valrem_expi(GEN *px, long *pe)
{
  GEN x = *px;
  const long l = lg(x);
  long vx, i, m = 0;
  for (i = 2;; i++)
    if (signe(gel(x,i))) break;
  vx = i - 2;
  for (; i < l; i++)
  {
    long e = expi(gel(x,i));
    if (e > m) m = e;
  }
  *px = RgX_shift_shallow(x, -vx);
  *pe = m; return vx;
}

/* Convert a t_INT x equal to T(2^(BIL*bs)) to a ZX T(y) * y^valx * .
 * v = variable number, d >= deg(T) */
static GEN
Z_mod2BIL_ZX(GEN x, long bs, long d, long v, long valx)
{
  long i, offset, lm = lgefint(x)-2, l = d+valx+3, sx = signe(x);
  GEN s1 = int2n(bs*BITS_IN_LONG), pol = cgetg(l, t_POL);
  int carry = 0;

  pol[1] = evalsigne(1)|evalvarn(v);
  for (i=0; i<valx; i++) gel(pol,i+2) = gen_0;
  for (offset=0; i <= d+valx; i++, offset += bs)
  {
    pari_sp av = avma;
    long lz = minss(bs, lm-offset);
    GEN z = adduispec_offset(carry, x, offset, lz);
    if (lgefint(z) == 3+bs) { carry = 1; z = gen_0;}
    else
    {
      carry = (lgefint(z) == 2+bs && (HIGHBIT & *int_W(z,bs-1)));
      if (carry) 
        z = gerepileuptoint(av, (sx==-1)? subii(s1,z): subii(z,s1));
      else if (sx==-1) togglesign(z);
    }
    gel(pol,i+2) = z;
  }
  return ZX_renormalize(pol,l);
}

/* assume x != 0 a ZX */
static GEN
ZX_sqr_sqri(GEN x)
{
  pari_sp av = avma;
  long ex, vx = ZX_valrem_expi(&x, &ex);
  long dx = degpol(x), v = vx*2;
  long e, N;
  GEN z;
  if (!dx)
  {
    RgX_shift_inplace_init(v);
    z = ZX_Z_mul(x,gel(x,2)); /* FIXE: improve ? */
    return gerepileupto(av, RgX_shift_inplace(z, v));
  }
  e = 2*ex + expu(dx) + 3;
  N = divsBIL(e)+1;
  z = sqri(ZX_eval2BIL(x,N));
  return gerepileupto(av, Z_mod2BIL_ZX(z, N, dx*2, varn(x), v));
}

/* assume x,y two non-constant ZX */
static GEN
ZX_mul_mulii(GEN x,GEN y)
{
  pari_sp av = avma;
  long ex, vx = ZX_valrem_expi(&x, &ex);
  long ey, vy = ZX_valrem_expi(&y, &ey);
  long dx = degpol(x), dy = degpol(y), v = vx+vy;
  long e, N;
  GEN z;
  if (!dx)
  {
    RgX_shift_inplace_init(v);
    z = ZX_Z_mul(y,gel(x,2));
    return gerepileupto(av, RgX_shift_inplace(z, v));
  }
  if (!dy)
  {
    RgX_shift_inplace_init(v);
    z = ZX_Z_mul(x,gel(y,2));
    return gerepileupto(av, RgX_shift_inplace(z, v));
  }
  if (ex > 2*ey || ey > 2*ex)
  {
    RgX_shift_inplace_init(v);
    z = RgX_mul(x, y);
    return gerepileupto(av, RgX_shift_inplace(z, v));
  }
  e = ex + ey + expu(dx) + 3;
  N = divsBIL(e)+1;
  z = mulii(ZX_eval2BIL(x,N), ZX_eval2BIL(y,N));
  return gerepileupto(av, Z_mod2BIL_ZX(z, N, dx+dy, varn(x), v));
}

GEN
ZX_sqr(GEN x)
{
  long dx = degpol(x);
  if (dx<=0) return dx < 0? ZX_copy(x): ZX_Z_mul(x, gel(x,2));
  return ZX_sqr_sqri(x);
}

GEN
ZX_mul(GEN x, GEN y)
{
  long dx, dy;
  dx = degpol(x); if (dx<=0) return dx < 0? ZX_copy(x): ZX_Z_mul(y, gel(x,2));
  dy = degpol(y); if (dy<=0) return dy < 0? ZX_copy(y): ZX_Z_mul(x, gel(y,2));
  return ZX_mul_mulii(x,y);
}

/* x,y two ZX in the same variable; assume y is monic */
GEN
ZX_rem(GEN x, GEN y)
{
  long vx, dx, dy, dz, i, j, sx, lr;
  pari_sp av0, av;
  GEN z,p1,rem;

  vx = varn(x);
  dy = degpol(y);
  dx = degpol(x);
  if (dx < dy) return ZX_copy(x);
  if (!dy) return zeropol(vx); /* y is constant */
  av0 = avma; dz = dx-dy;
  avma = av0;
  z=cgetg(dz+3,t_POL); z[1] = x[1];
  x += 2; y += 2; z += 2;

  p1 = gel(x,dx); av = avma;
  gel(z,dz) = icopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av=avma; p1=gel(x,i);
    for (j=i-dy+1; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii(gel(z,j),gel(y,i-j)));
    gel(z,i-dy) = avma == av? icopy(p1): gerepileuptoint(av, p1);
  }
  rem = (GEN)avma; av = (pari_sp)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii(gel(z,j),gel(y,i-j)));
    if (signe(p1)) { sx = 1; break; }
    if (!i) break;
    avma=av;
  }
  lr=i+3; rem -= lr;
  rem[0] = evaltyp(t_POL) | evallg(lr);
  rem[1] = z[-1];
  p1 = gerepileuptoint((pari_sp)rem, p1);
  rem += 2; gel(rem,i) = p1;
  for (i--; i>=0; i--)
  {
    av=avma; p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii(gel(z,j),gel(y,i-j)));
    gel(rem,i) = avma == av? icopy(p1): gerepileuptoint(av, p1);
  }
  rem -= 2;
  if (!sx) (void)ZX_renormalize(rem, lr);
  return gerepileupto(av0,rem);
}
