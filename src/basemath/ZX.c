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

/*ZX_mul and ZX_sqr are alias for RgX_mul and Rgx_sqr currently*/

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

