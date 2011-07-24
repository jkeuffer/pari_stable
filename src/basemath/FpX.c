/* $Id$

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

/* Not so fast arithmetic with polynomials over Fp */

/***********************************************************************/
/**                                                                   **/
/**                              FpX                                  **/
/**                                                                   **/
/***********************************************************************/

/* FpX are polynomials over Z/pZ represented as t_POL with
 * t_INT coefficients.
 * 1) Coefficients should belong to {0,...,p-1}, though non-reduced
 * coefficients should work but be slower.
 *
 * 2) p is not assumed to be prime, but it is assumed that impossible divisions
 *    will not happen.
 * 3) Theses functions let some garbage on the stack, but are gerepileupto
 * compatible.
 */

/* z in Z[X], return lift(z * Mod(1,p)), normalized*/
GEN
FpX_red(GEN z, GEN p)
{
  long i, l = lg(z);
  GEN x = cgetg(l, t_POL);
  for (i=2; i<l; i++) gel(x,i) = modii(gel(z,i),p);
  x[1] = z[1]; return FpX_renormalize(x,l);
}
GEN
FpXV_red(GEN z, GEN p)
{
  long i,l = lg(z);
  GEN x = cgetg(l, t_VEC);
  for (i=1; i<l; i++) gel(x,i) = FpX_red(gel(z,i), p);
  return x;
}

GEN
FpX_normalize(GEN z, GEN p)
{
  GEN p1 = leading_term(z);
  if (lg(z) == 2 || equali1(p1)) return z;
  return FpX_Fp_mul_to_monic(z, Fp_inv(p1,p), p);
}

GEN
FpX_center(GEN T, GEN p, GEN pov2)
{
  long i, l = lg(T);
  GEN P = cgetg(l,t_POL);
  for(i=2; i<l; i++) gel(P,i) = Fp_center(gel(T,i), p, pov2);
  P[1] = T[1]; return P;
}

GEN
FpX_add(GEN x,GEN y,GEN p)
{
  long lx = lg(x), ly = lg(y), i;
  GEN z;
  if (lx < ly) swapspec(x,y, lx,ly);
  z = cgetg(lx,t_POL); z[1] = x[1];
  for (i=2; i<ly; i++) gel(z,i) = Fp_add(gel(x,i),gel(y,i), p);
  for (   ; i<lx; i++) gel(z,i) = modii(gel(x,i), p);
  z = ZX_renormalize(z, lx);
  if (!lgpol(z)) { avma = (pari_sp)(z + lx); return pol_0(varn(x)); }
  return z;
}

static GEN
Fp_red_FpX(GEN x, GEN p, long v)
{
  GEN z;
  if (!signe(x)) return pol_0(v);
  z = cgetg(3, t_POL);
  z[1] = evalsigne(1) | evalvarn(v);
  gel(z,2) = Fp_red(x,p); return z;
}

static GEN
Fp_neg_FpX(GEN x, GEN p, long v)
{
  GEN z;
  if (!signe(x)) return pol_0(v);
  z = cgetg(3, t_POL);
  z[1] = evalsigne(1) | evalvarn(v);
  gel(z,2) = Fp_neg(x,p); return z;
}

GEN
FpX_Fp_add(GEN y,GEN x,GEN p)
{
  long i, lz = lg(y);
  GEN z;
  if (lz == 2) return Fp_red_FpX(x,p,varn(y));
  z = cgetg(lz,t_POL); z[1] = y[1];
  gel(z,2) = Fp_add(gel(y,2),x, p);
  if (lz == 3) z = FpX_renormalize(z,lz);
  else
    for(i=3;i<lz;i++) gel(z,i) = icopy(gel(y,i));
  return z;
}
GEN
FpX_Fp_add_shallow(GEN y,GEN x,GEN p)
{
  long i, lz = lg(y);
  GEN z;
  if (lz == 2) return scalar_ZX_shallow(x,varn(y));
  z = cgetg(lz,t_POL); z[1] = y[1];
  gel(z,2) = Fp_add(gel(y,2),x, p);
  if (lz == 3) z = FpX_renormalize(z,lz);
  else
    for(i=3;i<lz;i++) gel(z,i) = gel(y,i);
  return z;
}
GEN
FpX_Fp_sub(GEN y,GEN x,GEN p)
{
  long i, lz = lg(y);
  GEN z;
  if (lz == 2) return Fp_neg_FpX(x,p,varn(y));
  z = cgetg(lz,t_POL); z[1] = y[1];
  gel(z,2) = Fp_sub(gel(y,2),x, p);
  if (lz == 3) z = FpX_renormalize(z,lz);
  else
    for(i=3;i<lz;i++) gel(z,i) = icopy(gel(y,i));
  return z;
}
GEN
FpX_Fp_sub_shallow(GEN y,GEN x,GEN p)
{
  long i, lz = lg(y);
  GEN z;
  if (lz == 2) return Fp_neg_FpX(x,p,varn(y));
  z = cgetg(lz,t_POL); z[1] = y[1];
  gel(z,2) = Fp_sub(gel(y,2),x, p);
  if (lz == 3) z = FpX_renormalize(z,lz);
  else
    for(i=3;i<lz;i++) gel(z,i) = gel(y,i);
  return z;
}

GEN
FpX_neg(GEN x,GEN p)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx,t_POL);
  y[1] = x[1];
  for(i=2; i<lx; i++) gel(y,i) = Fp_neg(gel(x,i), p);
  return ZX_renormalize(y, lx);
}

static GEN
FpX_subspec(GEN x,GEN y,GEN p, long nx, long ny)
{
  long i, lz;
  GEN z;
  if (nx >= ny)
  {
    lz = nx+2;
    z = cgetg(lz,t_POL); z[1] = 0; z += 2;
    for (i=0; i<ny; i++) gel(z,i) = Fp_sub(gel(x,i),gel(y,i), p);
    for (   ; i<nx; i++) gel(z,i) = modii(gel(x,i), p);
  }
  else
  {
    lz = ny+2;
    z = cgetg(lz,t_POL); z[1] = 0; z += 2;
    for (i=0; i<nx; i++) gel(z,i) = Fp_sub(gel(x,i),gel(y,i), p);
    for (   ; i<ny; i++) gel(z,i) = Fp_neg(gel(y,i), p);
  }
  z = FpX_renormalize(z-2, lz);
  if (!lgpol(z)) { avma = (pari_sp)(z + lz); return pol_0(0); }
  return z;
}

GEN
FpX_sub(GEN x,GEN y,GEN p)
{
  GEN z = FpX_subspec(x+2,y+2,p,lgpol(x),lgpol(y));
  setvarn(z, varn(x));
  return z;
}

GEN
Fp_FpX_sub(GEN x, GEN y, GEN p)
{
  long ly = lg(y), i;
  GEN z;
  if (ly <= 3) {
    z = cgetg(3, t_POL);
    x = (ly == 3)? Fp_sub(x, gel(y,2), p): modii(x, p);
    if (!signe(x)) { avma = (pari_sp)(z + 3); return pol_0(varn(y)); }
    z[1] = y[1]; gel(z,2) = x; return z;
  }
  z = cgetg(ly,t_POL);
  gel(z,2) = Fp_sub(x, gel(y,2), p);
  for (i = 3; i < ly; i++) gel(z,i) = Fp_neg(gel(y,i), p);
  z = ZX_renormalize(z, ly);
  if (!lgpol(z)) { avma = (pari_sp)(z + ly); return pol_0(varn(x)); }
  z[1] = y[1]; return z;
}

GEN
FpX_mul(GEN x,GEN y,GEN p) { return FpX_red(ZX_mul(x, y), p); }

GEN
FpX_sqr(GEN x,GEN p) { return FpX_red(ZX_sqr(x), p); }

GEN
FpX_Fp_mul(GEN y,GEN x,GEN p)
{
  GEN z;
  long i, l;
  if (!signe(x)) return pol_0(varn(y));
  z = cgetg_copy(y, &l); z[1] = y[1];
  for(i=2; i<l; i++) gel(z,i) = Fp_mul(gel(y,i), x, p);
  return ZX_renormalize(z, l);
}
GEN
FpX_Fp_mul_to_monic(GEN y,GEN x,GEN p)
{
  GEN z;
  long i, l;
  z = cgetg_copy(y, &l); z[1] = y[1];
  for(i=2; i<l-1; i++) gel(z,i) = Fp_mul(gel(y,i), x, p);
  gel(z,l-1) = gen_1; return z;
}

GEN
FpX_divrem(GEN x, GEN y, GEN p, GEN *pr)
{
  long vx, dx, dy, dz, i, j, sx, lr;
  pari_sp av0, av;
  GEN z,p1,rem,lead;

  if (!signe(y)) pari_err(gdiver);
  vx = varn(x);
  dy = degpol(y);
  dx = degpol(x);
  if (dx < dy)
  {
    if (pr)
    {
      av0 = avma; x = FpX_red(x, p);
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
    av0 = avma;
    if (equali1(lead)) return FpX_red(x, p);
    else return gerepileupto(av0, FpX_Fp_mul(x, Fp_inv(lead,p), p));
  }
  av0 = avma; dz = dx-dy;
  if (lgefint(p) == 3)
  { /* assume ab != 0 mod p */
    ulong pp = (ulong)p[2];
    GEN a = ZX_to_Flx(x, pp);
    GEN b = ZX_to_Flx(y, pp);
    z = Flx_divrem(a,b,pp, pr);
    avma = av0; /* HACK: assume pr last on stack, then z */
    if (!z) return NULL;
    z = leafcopy(z);
    if (pr && pr != ONLY_DIVIDES && pr != ONLY_REM)
    {
      *pr = leafcopy(*pr);
      *pr = Flx_to_ZX_inplace(*pr);
    }
    return Flx_to_ZX_inplace(z);
  }
  lead = equali1(lead)? NULL: gclone(Fp_inv(lead,p));
  avma = av0;
  z=cgetg(dz+3,t_POL); z[1] = x[1];
  x += 2; y += 2; z += 2;

  p1 = gel(x,dx); av = avma;
  gel(z,dz) = lead? gerepileuptoint(av, Fp_mul(p1,lead, p)): icopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av=avma; p1=gel(x,i);
    for (j=i-dy+1; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii(gel(z,j),gel(y,i-j)));
    if (lead) p1 = mulii(p1,lead);
    gel(z,i-dy) = gerepileuptoint(av,modii(p1, p));
  }
  if (!pr) { if (lead) gunclone(lead); return z-2; }

  rem = (GEN)avma; av = (pari_sp)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii(gel(z,j),gel(y,i-j)));
    p1 = modii(p1,p); if (signe(p1)) { sx = 1; break; }
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
  p1 = gerepileuptoint((pari_sp)rem, p1);
  rem += 2; gel(rem,i) = p1;
  for (i--; i>=0; i--)
  {
    av=avma; p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii(gel(z,j),gel(y,i-j)));
    gel(rem,i) = gerepileuptoint(av, modii(p1,p));
  }
  rem -= 2;
  if (lead) gunclone(lead);
  if (!sx) (void)FpX_renormalize(rem, lr);
  if (pr == ONLY_REM) return gerepileupto(av0,rem);
  *pr = rem; return z-2;
}

GEN
FpX_div_by_X_x(GEN a, GEN x, GEN p, GEN *r)
{
  long l = lg(a)-1, i;
  GEN z = cgetg(l, t_POL);
  z[1] = evalsigne(1) | evalvarn(0);
  gel(z, l-1) = gel(a,l);
  for (i=l-2; i>1; i--) /* z[i] = a[i+1] + x*z[i+1] */
    gel(z, i) = Fp_addmul(gel(a,i+1), x, gel(z,i+1), p);
  if (r) *r = Fp_addmul(gel(a,2), x, gel(z,2), p);
  return z;
}

long
FpX_valrem(GEN x, GEN t, GEN p, GEN *py)
{
  pari_sp av=avma;
  long k;
  GEN r, y;

  for (k=0; ; k++)
  {
    y = FpX_divrem(x, t, p, &r);
    if (signe(r)) break;
    x = y;
  }
  *py = gerepilecopy(av,x);
  return k;
}

static GEN
FpX_halfgcd_basecase(GEN a, GEN b, GEN p)
{
  pari_sp av=avma, lim = stack_lim(av,2);
  GEN u,u1,v,v1;
  long vx = varn(a);
  long n = lgpol(a)>>1;
  u1 = v = pol_0(vx);
  u = v1 = pol_1(vx);
  while (lgpol(b)>n)
  {
    GEN r, q = FpX_divrem(a,b,p, &r);
    a = b; b = r; swap(u,u1); swap(v,v1);
    u1 = FpX_sub(u1, FpX_mul(u, q, p), p);
    v1 = FpX_sub(v1, FpX_mul(v, q ,p), p);
    if (low_stack(lim,stack_lim(av,2)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FpX_halfgcd (d = %ld)",degpol(b));
      gerepileall(av,6, &a,&b,&u1,&v1,&u,&v);
    }
  }
  return gerepilecopy(av, mkmat2(mkcol2(u,u1), mkcol2(v,v1)));
}
static GEN
FpX_addmulmul(GEN u, GEN v, GEN x, GEN y, GEN p)
{
  return FpX_add(FpX_mul(u, x, p),FpX_mul(v, y, p), p);
}

static GEN
FpXM_FpX_mul2(GEN M, GEN x, GEN y, GEN p)
{
  GEN res = cgetg(3, t_COL);
  gel(res, 1) = FpX_addmulmul(gcoeff(M,1,1), gcoeff(M,1,2), x, y, p);
  gel(res, 2) = FpX_addmulmul(gcoeff(M,2,1), gcoeff(M,2,2), x, y, p);
  return res;
}

/*TODO: implement Strassen 7 multiplications formula (p is large) */
static GEN
FpXM_mul2(GEN M, GEN N, GEN p)
{
  GEN res = cgetg(3, t_MAT);
  gel(res, 1) = FpXM_FpX_mul2(M,gcoeff(N,1,1),gcoeff(N,2,1),p);
  gel(res, 2) = FpXM_FpX_mul2(M,gcoeff(N,1,2),gcoeff(N,2,2),p);
  return res;
}

/* Return [0,1;1,-q]*M */
static GEN
FpX_FpXM_qmul(GEN q, GEN M, GEN p)
{
  GEN u, v, res = cgetg(3, t_MAT);
  u = FpX_sub(gcoeff(M,1,1), FpX_mul(gcoeff(M,2,1), q, p), p);
  gel(res,1) = mkcol2(gcoeff(M,2,1), u);
  v = FpX_sub(gcoeff(M,1,2), FpX_mul(gcoeff(M,2,2), q, p), p);
  gel(res,2) = mkcol2(gcoeff(M,2,2), v);
  return res;
}

static GEN
matid2_FpXM(long v)
{
  GEN m = cgetg(3, t_MAT);
  gel(m,1) = mkcol2(pol_1(v),pol_0(v));
  gel(m,2) = mkcol2(pol_0(v),pol_1(v));
  return m;
}

static GEN
FpX_halfgcd_split(GEN x, GEN y, GEN p)
{
  pari_sp av=avma;
  GEN R, S, V;
  GEN y1, r, q;
  long l = lgpol(x), n = l>>1, k;
  if (lgpol(y)<=n) return matid2_FpXM(varn(x));
  R = FpX_halfgcd(RgX_shift(x,-n),RgX_shift(y,-n),p);
  V = FpXM_FpX_mul2(R,x,y,p); y1 = gel(V,2);
  if (lgpol(y1)<=n) return gerepilecopy(av, R);
  q = FpX_divrem(gel(V,1), y1, p, &r);
  k = 2*n-degpol(y1);
  S = FpX_halfgcd(RgX_shift(y1,-k), RgX_shift(r,-k),p);
  return gerepileupto(av, FpXM_mul2(S,FpX_FpXM_qmul(q,R,p),p));
}

/* Return M in GL_2(Fp[X]) such that:
if [a',b']~=M*[a,b]~ then degpol(a')>= (lgpol(a)>>1) >degpol(b')
*/

static GEN
FpX_halfgcd_i(GEN x, GEN y, GEN p)
{
  if (lg(x)<=FpX_HALFGCD_LIMIT) return FpX_halfgcd_basecase(x,y,p);
  return FpX_halfgcd_split(x,y,p);
}

GEN
FpX_halfgcd(GEN x, GEN y, GEN p)
{
  pari_sp av = avma;
  GEN M,q,r;
  if (lgefint(p)==3)
  {
    ulong pp=p[2];
    M = FlxM_to_ZXM(Flx_halfgcd(ZX_to_Flx(x, pp),ZX_to_Flx(y, pp), pp));
  }
  else
  {
    if (degpol(y)<degpol(x)) return FpX_halfgcd_i(x,y,p);
    q = FpX_divrem(y,x,p,&r);
    M = FpX_halfgcd_i(x,r,p);
    gcoeff(M,1,1) = FpX_sub(gcoeff(M,1,1), FpX_mul(q, gcoeff(M,1,2), p), p);
    gcoeff(M,2,1) = FpX_sub(gcoeff(M,2,1), FpX_mul(q, gcoeff(M,2,2), p), p);
  }
  return gerepilecopy(av, M);
}

static GEN
FpX_gcd_basecase(GEN a, GEN b, GEN p)
{
  pari_sp av = avma, av0=avma, lim = stack_lim(av0,2);
  while (signe(b))
  {
    GEN c;
    if (low_stack(lim,stack_lim(av0,2)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FpX_gcd (d = %ld)",degpol(b));
      gerepileall(av0,2, &a,&b);
    }
    av = avma; c = FpX_rem(a,b,p); a=b; b=c;
  }
  avma = av; return a;
}

GEN
FpX_gcd(GEN x, GEN y, GEN p)
{
  pari_sp av = avma, av0;
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    (void)new_chunk((lg(x) + lg(y)) << 2); /* scratch space */
    x = ZX_to_Flx(x, pp);
    y = ZX_to_Flx(y, pp);
    x = Flx_gcd(x,y, pp);
    avma = av; return Flx_to_ZX(x);
  }
  x = FpX_red(x, p); av0 = avma;
  y = FpX_red(y, p);
  if (!signe(y)) { avma = av0; return x; }
  while (lg(y)>FpX_GCD_LIMIT)
  {
    GEN c;
    if (lgpol(y)<=(lgpol(x)>>1))
    {
      GEN r = FpX_rem(x, y, p);
      x = y; y = r;
    }
    c = FpXM_FpX_mul2(FpX_halfgcd(x,y, p), x, y, p);
    x = gel(c,1); y = gel(c,2);
    gerepileall(av,2,&x,&y);
  }
  return gerepileupto(av, FpX_gcd_basecase(x,y,p));
}

/*Return 1 if gcd can be computed
 * else return a factor of p*/

GEN
FpX_gcd_check(GEN x, GEN y, GEN p)
{
  GEN a,b,c;
  pari_sp av=avma;

  a = FpX_red(x, p);
  b = FpX_red(y, p);
  while (signe(b))
  {
    GEN lead = leading_term(b);
    GEN g = gcdii(lead,p);
    if (!equali1(g)) return gerepileuptoint(av,g);
    c = FpX_rem(a,b,p); a=b; b=c;
  }
  avma = av; return gen_1;
}

static GEN
FpX_extgcd_basecase(GEN a, GEN b, GEN p, GEN *ptu, GEN *ptv)
{
  pari_sp av=avma, lim = stack_lim(av,2);
  GEN u,v,d,d1,v1;
  long vx = varn(a);
  d = a; d1 = b;
  v = pol_0(vx); v1 = pol_1(vx);
  while (signe(d1))
  {
    GEN r, q = FpX_divrem(d,d1,p, &r);
    v = FpX_sub(v,FpX_mul(q,v1,p),p);
    u=v; v=v1; v1=u;
    u=r; d=d1; d1=u;
    if (low_stack(lim,stack_lim(av,2)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FpX_extgcd (d = %ld)",degpol(d));
      gerepileall(av,5, &d,&d1,&u,&v,&v1);
    }
  }
  if (ptu) *ptu = FpX_div(FpX_sub(d,FpX_mul(b,v,p),p),a,p);
  *ptv = v; return d;
}

static GEN
FpX_extgcd_halfgcd(GEN x, GEN y, GEN p, GEN *ptu, GEN *ptv)
{
  pari_sp av=avma;
  GEN u,v,R = matid2_FpXM(varn(x));
  while (lg(y)>FpX_EXTGCD_LIMIT)
  {
    GEN M, c;
    if (lgpol(y)<=(lgpol(x)>>1))
    {
      GEN r, q = FpX_divrem(x, y, p, &r);
      x = y; y = r;
      R = FpX_FpXM_qmul(q, R, p);
    }
    M = FpX_halfgcd(x,y, p);
    c = FpXM_FpX_mul2(M, x,y, p);
    R = FpXM_mul2(M, R, p);
    x = gel(c,1); y = gel(c,2);
    gerepileall(av,3,&x,&y,&R);
  }
  y = FpX_extgcd_basecase(x,y,p,&u,&v);
  if (ptu) *ptu = FpX_addmulmul(u,v,gcoeff(R,1,1),gcoeff(R,2,1),p);
  *ptv = FpX_addmulmul(u,v,gcoeff(R,1,2),gcoeff(R,2,2),p);
  return y;
}

/* x and y in Z[X], return lift(gcd(x mod p, y mod p)). Set u and v st
 * ux + vy = gcd (mod p) */
GEN
FpX_extgcd(GEN x, GEN y, GEN p, GEN *ptu, GEN *ptv)
{
  GEN d;
  pari_sp ltop=avma;
  if (lgefint(p)==3)
  {
    ulong pp=p[2];
    x = ZX_to_Flx(x, pp);
    y = ZX_to_Flx(y, pp);
    d = Flx_extgcd(x,y, pp, ptu,ptv);
    d = Flx_to_ZX(d);
    if (ptu) *ptu=Flx_to_ZX(*ptu);
    *ptv=Flx_to_ZX(*ptv);
  }
  else
  {
    x = FpX_red(x, p);
    y = FpX_red(y, p);
    if (lg(y)>FpX_EXTGCD_LIMIT)
      d = FpX_extgcd_halfgcd(x, y, p, ptu, ptv);
    else
      d = FpX_extgcd_basecase(x, y, p, ptu, ptv);
  }
  gerepileall(ltop,ptu?3:2,&d,ptv,ptu);
  return d;
}

GEN
FpX_rescale(GEN P, GEN h, GEN p)
{
  long i, l = lg(P);
  GEN Q = cgetg(l,t_POL), hi = h;
  Q[l-1] = P[l-1];
  for (i=l-2; i>=2; i--)
  {
    gel(Q,i) = Fp_mul(gel(P,i), hi, p);
    if (i == 2) break;
    hi = Fp_mul(hi,h, p);
  }
  Q[1] = P[1]; return Q;
}

GEN
FpX_deriv(GEN x, GEN p) { return FpX_red(ZX_deriv(x), p); }

int
FpX_is_squarefree(GEN f, GEN p)
{
  pari_sp av = avma;
  GEN z = FpX_gcd(f,FpX_deriv(f,p),p);
  avma = av;
  return degpol(z)==0;
}

GEN
random_FpX(long d1, long v, GEN p)
{
  long i, d = d1+2;
  GEN y = cgetg(d,t_POL); y[1] = evalsigne(1) | evalvarn(v);
  for (i=2; i<d; i++) gel(y,i) = randomi(p);
  return FpX_renormalize(y,d);
}

/* Evaluation in Fp
 * x a ZX and y an Fp, return x(y) mod p
 *
 * If p is very large (several longs) and x has small coefficients(<<p),
 * then Brent & Kung algorithm is faster. */
GEN
FpX_eval(GEN x,GEN y,GEN p)
{
  pari_sp av;
  GEN p1,r,res;
  long j, i=lg(x)-1;
  if (i<=2)
    return (i==2)? modii(gel(x,2),p): gen_0;
  res=cgeti(lgefint(p));
  av=avma; p1=gel(x,i);
  /* specific attention to sparse polynomials (see poleval)*/
  /*You've guessed it! It's a copy-paste(tm)*/
  for (i--; i>=2; i=j-1)
  {
    for (j=i; !signe(gel(x,j)); j--)
      if (j==2)
      {
        if (i!=j) y = Fp_powu(y,i-j+1,p);
        p1=mulii(p1,y);
        goto fppoleval;/*sorry break(2) no implemented*/
      }
    r = (i==j)? y: Fp_powu(y,i-j+1,p);
    p1 = Fp_addmul(gel(x,j), p1, r, p);
    if ((i & 7) == 0) { affii(p1, res); p1 = res; avma = av; }
  }
 fppoleval:
  modiiz(p1,p,res);
  avma = av; return res;
}

/* Tz=Tx*Ty where Tx and Ty coprime
 * return lift(chinese(Mod(x*Mod(1,p),Tx*Mod(1,p)),Mod(y*Mod(1,p),Ty*Mod(1,p))))
 * if Tz is NULL it is computed
 * As we do not return it, and the caller will frequently need it,
 * it must compute it and pass it.
 */
GEN
FpX_chinese_coprime(GEN x,GEN y,GEN Tx,GEN Ty,GEN Tz,GEN p)
{
  pari_sp av = avma;
  GEN ax,p1;
  ax = FpX_mul(FpXQ_inv(Tx,Ty,p), Tx,p);
  p1 = FpX_mul(ax, FpX_sub(y,x,p),p);
  p1 = FpX_add(x,p1,p);
  if (!Tz) Tz=FpX_mul(Tx,Ty,p);
  p1 = FpX_rem(p1,Tz,p);
  return gerepileupto(av,p1);
}

/* Res(A,B) = Res(B,R) * lc(B)^(a-r) * (-1)^(ab), with R=A%B, a=deg(A) ...*/
GEN
FpX_resultant(GEN a, GEN b, GEN p)
{
  long da,db,dc;
  pari_sp av, lim;
  GEN c,lb, res = gen_1;

  if (!signe(a) || !signe(b)) return gen_0;
  da = degpol(a);
  db = degpol(b);
  if (db > da)
  {
    swapspec(a,b, da,db);
    if (both_odd(da,db)) res = subii(p, res);
  }
  if (!da) return gen_1; /* = res * a[2] ^ db, since 0 <= db <= da = 0 */
  av = avma; lim = stack_lim(av,2);
  while (db)
  {
    lb = gel(b,db+2);
    c = FpX_rem(a,b, p);
    a = b; b = c; dc = degpol(c);
    if (dc < 0) { avma = av; return NULL; }

    if (both_odd(da,db)) res = subii(p, res);
    if (!equali1(lb)) res = Fp_mul(res, Fp_powu(lb, da - dc, p), p);
    if (low_stack(lim,stack_lim(av,2)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FpX_resultant (da = %ld)",da);
      gerepileall(av,3, &a,&b,&res);
    }
    da = db; /* = degpol(a) */
    db = dc; /* = degpol(b) */
  }
  res = Fp_mul(res, Fp_powu(gel(b,2), da, p), p);
  return gerepileuptoint(av, res);
}

static GEN _FpX_mul(void *p,GEN a,GEN b){return FpX_mul(a,b,(GEN)p);}
GEN
FpXV_prod(GEN V, GEN p)
{
  return divide_conquer_assoc(V, (void *)p, &_FpX_mul);
}

GEN
FpV_roots_to_pol(GEN V, GEN p, long v)
{
  pari_sp ltop=avma;
  long i;
  GEN g=cgetg(lg(V),t_VEC);
  for(i=1;i<lg(V);i++)
    gel(g,i) = deg1pol_shallow(gen_1,modii(negi(gel(V,i)),p),v);
  return gerepileupto(ltop,FpXV_prod(g,p));
}

/* invert all elements of x mod p using Montgomery's trick. Not stack-clean. */
GEN
FpV_inv(GEN x, GEN p)
{
  long i, lx = lg(x);
  GEN u, y = cgetg(lx, t_VEC);

  gel(y,1) = gel(x,1);
  for (i=2; i<lx; i++) gel(y,i) = Fp_mul(gel(y,i-1), gel(x,i), p);

  u = Fp_inv(gel(y,--i), p);
  for ( ; i > 1; i--)
  {
    gel(y,i) = Fp_mul(u, gel(y,i-1), p);
    u = Fp_mul(u, gel(x,i), p); /* u = 1 / (x[1] ... x[i-1]) */
  }
  gel(y,1) = u; return y;
}
GEN
FqV_inv(GEN x, GEN T, GEN p)
{
  long i, lx = lg(x);
  GEN u, y = cgetg(lx, t_VEC);

  gel(y,1) = gel(x,1);
  for (i=2; i<lx; i++) gel(y,i) = Fq_mul(gel(y,i-1), gel(x,i), T,p);

  u = Fq_inv(gel(y,--i), T,p);
  for ( ; i > 1; i--)
  {
    gel(y,i) = Fq_mul(u, gel(y,i-1), T,p);
    u = Fq_mul(u, gel(x,i), T,p); /* u = 1 / (x[1] ... x[i-1]) */
  }
  gel(y,1) = u; return y;
}

/***********************************************************************/
/**                                                                   **/
/**                  Montgomery reduction                            **/
/**                                                                   **/
/***********************************************************************/

static GEN
FpX_invMontgomery_basecase(GEN T, GEN p)
{
  long i, l=lg(T)-1, lr = l-1, k;
  GEN r=cgetg(lr, t_POL); r[1]=T[1];
  gel(r,2) = gen_1;
  for (i=3; i<lr; i++)
  {
    pari_sp av = avma;
    GEN u = gel(T,l-i+2);
    for (k=3; k<i; k++)
      u = addii(u, mulii(gel(T,l-i+k), gel(r,k)));
    gel(r,i) = gerepileupto(av, modii(negi(u), p));
  }
  return FpX_renormalize(r,lr);
}

/* Return new lgpol */
static long
ZX_lgrenormalizespec(GEN x, long lx)
{
  long i;
  for (i = lx-1; i>=0; i--)
    if (signe(gel(x,i))) break;
  return i+1;
}

INLINE GEN
FpX_recipspec(GEN x, long l, long n)
{
  return RgX_recipspec_shallow(x, l, n);
}

static GEN
FpX_mulspec(GEN a, GEN b, GEN p, long na, long nb)
{
  return FpX_red(ZX_mulspec(a, b, na, nb), p);
}

static GEN
FpX_invMontgomery_Newton(GEN T, GEN p)
{
  pari_sp av = avma;
  long nold, lx, lz, lq, l = degpol(T), i, lQ;
  GEN q, y, z, x = cgetg(l+2, t_POL) + 2;
  ulong mask = quadratic_prec_mask(l-2); /* assume l > 2 */
  for (i=0;i<l;i++) gel(x,i) = gen_0;
  q = FpX_recipspec(T+2,l+1,l+1); lQ = lgpol(q); q+=2;
  /* We work on _spec_ FpX's, all the l[xzq] below are lgpol's */

  /* initialize */
  gel(x,0) = Fp_inv(gel(q,0), p);
  if (lQ>1 && signe(gel(q,1)))
  {
    GEN u = gel(q, 1);
    if (!equali1(gel(x,0))) u = Fp_mul(u, Fp_sqr(gel(x,0), p), p);
    gel(x,1) = Fp_neg(u, p); lx = 2;
  }
  else
    lx = 1;
  nold = 1;
  for (; mask > 1; )
  { /* set x -= x(x*q - 1) + O(t^(nnew + 1)), knowing x*q = 1 + O(t^(nold+1)) */
    long i, lnew, nnew = nold << 1;

    if (mask & 1) nnew--;
    mask >>= 1;

    lnew = nnew + 1;
    lq = ZX_lgrenormalizespec(q, minss(lQ,lnew));
    z = FpX_mulspec(x, q, p, lx, lq); /* FIXME: high product */
    lz = lgpol(z); if (lz > lnew) lz = lnew;
    z += 2;
    /* subtract 1 [=>first nold words are 0]: renormalize so that z(0) != 0 */
    for (i = nold; i < lz; i++) if (signe(gel(z,i))) break;
    nold = nnew;
    if (i >= lz) continue; /* z-1 = 0(t^(nnew + 1)) */

    /* z + i represents (x*q - 1) / t^i */
    lz = ZX_lgrenormalizespec (z+i, lz-i);
    z = FpX_mulspec(x, z+i, p, lx, lz); /* FIXME: low product */
    lz = lgpol(z); z += 2;
    if (lz > lnew-i) lz = ZX_lgrenormalizespec(z, lnew-i);

    lx = lz+ i;
    y  = x + i; /* x -= z * t^i, in place */
    for (i = 0; i < lz; i++) gel(y,i) = Fp_neg(gel(z,i), p);
  }
  x -= 2; setlg(x, lx + 2); x[1] = T[1];
  return gerepilecopy(av, x);
}

/* 1/polrecip(T)+O(x^(deg(T)-1)) */
GEN
FpX_invMontgomery(GEN T, GEN p)
{
  pari_sp ltop = avma;
  long l = lg(T);
  GEN r;
  if (l<5) return pol_0(T[1]);
  if (l<=FpX_INVMONTGOMERY_LIMIT)
  {
    GEN c = gel(T,l-1), ci=gen_1;
    if (!equali1(c))
    {
      ci = Fp_inv(c, p);
      T = FpX_Fp_mul(T, ci, p);
      r = FpX_invMontgomery_basecase(T, p);
      r = FpX_Fp_mul(r, ci, p);
    } else
      r = FpX_invMontgomery_basecase(T, p);
  }
  else
    r = FpX_invMontgomery_Newton(T, p);
  return gerepileupto(ltop, r);
}

/* Compute x mod T where degpol(x)<=2*(degpol(T)-1) i.e. lgpol(x)<2*lgpol(T)-2
 * and mg is the Montgomery inverse of T. */
static GEN
FpX_rem_Montgomery_noGC(GEN x, GEN mg, GEN T, GEN p)
{
  GEN z;
  long l  = lgpol(x);
  long lt = degpol(T); /*We discard the leading term*/
  long ld, lm, lT, lmg;
  if (l<=lt) return ZX_copy(x);
  ld = l-lt;
  lm = minss(ld, lgpol(mg));
  lT  = ZX_lgrenormalizespec(T+2,lt);
  lmg = ZX_lgrenormalizespec(mg+2,lm);
  z = FpX_recipspec(x+2+lt,ld,ld);              /* z = rec(x)     lz<=ld*/
  z = FpX_mulspec(z+2,mg+2,p,lgpol(z),lmg);    /* z = rec(x) * mg lz<=ld+lm*/
  z = FpX_recipspec(z+2,minss(ld,lgpol(z)),ld);/* z = rec (rec(x) * mg) lz<=ld*/
  z = FpX_mulspec(z+2,T+2,p,lgpol(z),lT);      /* z *= pol        lz<=ld+lt*/
  z = FpX_subspec(x+2,z+2,p,lt,minss(lt,lgpol(z)));/* z = x - z   lz<=lt */
  z[1] = x[1]; return z;
}
GEN
FpX_rem_Montgomery(GEN x, GEN mg, GEN T, GEN p)
{
  pari_sp av = avma;
  return gerepileupto(av, FpX_rem_Montgomery_noGC(x,mg,T,p));
}

GEN
FpX_rem(GEN x, GEN y, GEN p)
{
  long dy = degpol(y), dx = degpol(x), d = dx-dy;
  if (d < 0) return FpX_red(x,p);
  if (d+3 < FpX_REM_MONTGOMERY_LIMIT || d>dy-2)
    return FpX_divrem(x,y,p,ONLY_REM);
  else
  {
    pari_sp av=avma;
    GEN mg = FpX_invMontgomery(y, p);
    return gerepileupto(av, FpX_rem_Montgomery_noGC(x, mg, y, p));
  }
}

/***********************************************************************/
/**                                                                   **/
/**                              FpXQ                                 **/
/**                                                                   **/
/***********************************************************************/

/* FpXQ are elements of Fp[X]/(T), represented by FpX*/

GEN
FpXQ_red(GEN x, GEN T, GEN p)
{
  GEN z = FpX_red(x,p);
  return FpX_rem(z, T,p);
}

GEN
FpXQ_mul(GEN x,GEN y,GEN T,GEN p)
{
  GEN z = FpX_mul(x,y,p);
  return FpX_rem(z, T, p);
}

GEN
FpXQ_sqr(GEN x, GEN T, GEN p)
{
  GEN z = FpX_sqr(x,p);
  return FpX_rem(z, T, p);
}

/* Inverse of x in Z/pZ[X]/(pol) or NULL if inverse doesn't exist
 * return lift(1 / (x mod (p,pol))) */
GEN
FpXQ_invsafe(GEN x, GEN T, GEN p)
{
  GEN V, z = FpX_extgcd(T, x, p, NULL, &V);
  if (degpol(z)) return NULL;
  z = Fp_invsafe(gel(z,2), p);
  if (!z) return NULL;
  return FpX_Fp_mul(V, z, p);
}

GEN
FpXQ_inv(GEN x,GEN T,GEN p)
{
  pari_sp av = avma;
  GEN U = FpXQ_invsafe(x, T, p);
  if (!U) pari_err(gdiver);
  return gerepileupto(av, U);
}

GEN
FpXQ_div(GEN x,GEN y,GEN T,GEN p)
{
  pari_sp av = avma;
  return gerepileupto(av, FpXQ_mul(x,FpXQ_inv(y,T,p),T,p));
}

static GEN
FpXQ_mul_mg(GEN x,GEN y,GEN mg,GEN T,GEN p)
{
  pari_sp av = avma;
  GEN z = FpX_mul(x,y,p);
  if (lg(T) > lg(z)) return z;
  return gerepileupto(av, FpX_rem_Montgomery_noGC(z, mg, T, p));
}

/* Square of y in Z/pZ[X]/(T), as t_VECSMALL. */
static GEN
FpXQ_sqr_mg(GEN y,GEN mg,GEN T,GEN p)
{
  pari_sp av = avma;
  GEN z = FpX_sqr(y,p);
  if (lg(T) > lg(z)) return z;
  return gerepileupto(av, FpX_rem_Montgomery_noGC(z, mg, T, p));
}

typedef struct {
  GEN T, p, mg;
} FpX_muldata;

static GEN
_sqr_montgomery(void *data, GEN x)
{
  FpX_muldata *D = (FpX_muldata*)data;
  return FpXQ_sqr_mg(x,D->mg, D->T, D->p);
}
static GEN
_mul_montgomery(void *data, GEN x, GEN y)
{
  FpX_muldata *D = (FpX_muldata*)data;
  return FpXQ_mul_mg(x,y,D->mg, D->T, D->p);
}

static GEN
_FpXQ_sqr(void *data, GEN x)
{
  FpX_muldata *D = (FpX_muldata*)data;
  return FpXQ_sqr(x, D->T, D->p);
}
static GEN
_FpXQ_mul(void *data, GEN x, GEN y)
{
  FpX_muldata *D = (FpX_muldata*)data;
  return FpXQ_mul(x,y, D->T, D->p);
}

/* x,pol in Z[X], p in Z, n in Z, compute lift(x^n mod (p, pol)) */
GEN
FpXQ_pow(GEN x, GEN n, GEN T, GEN p)
{
  FpX_muldata D;
  pari_sp av;
  long s = signe(n);
  GEN y;
  if (!s) return pol_1(varn(x));
  if (is_pm1(n)) /* +/- 1 */
    return (s < 0)? FpXQ_inv(x,T,p): FpXQ_red(x,T,p);
  av = avma;
  if (!is_bigint(p))
  {
    ulong pp = p[2];
    T = ZX_to_Flx(T, pp);
    x = ZX_to_Flx(x, pp);
    y = Flx_to_ZX( Flxq_pow(x, n, T, pp) );
  }
  else
  {
    long lx = lgpol(x), lT = lgpol(T);
    D.T = T;
    D.p = p;
    if (s < 0) x = FpXQ_inv(x,T,p);
    if (lT+2>FpX_POW_MONTGOMERY_LIMIT)
    {
      D.mg  = FpX_invMontgomery(T,p);
      if (lx>=lT)
      {
        if (lx<2*lT-2) x = FpX_rem_Montgomery(x,D.mg,T,p);
        else x = FpX_rem(x,T,p);
      }
      y = gen_pow(x, n, (void*)&D, &_sqr_montgomery, &_mul_montgomery);
    }
    else
    {
      if (lx>=lT) x = FpX_rem(x,T,p);
      y = gen_pow(x, n, (void*)&D, &_FpXQ_sqr, &_FpXQ_mul);
    }
  }
  return gerepileupto(av, y);
}

/* generates the list of powers of x of degree 0,1,2,...,l*/
GEN
FpXQ_powers(GEN x, long l, GEN T, GEN p)
{
  GEN V=cgetg(l+2,t_VEC);
  long i;
  gel(V,1) = pol_1(varn(T)); if (l==0) return V;
  gel(V,2) = ZX_copy(x);       if (l==1) return V;
  if (lgefint(p) == 3) {
    long pp = p[2];
    return FlxC_to_ZXC(Flxq_powers(ZX_to_Flx(x, pp), l, ZX_to_Flx(T,pp), pp));
  }
  if (lg(T)>FpX_POW_MONTGOMERY_LIMIT)
  {
    GEN mg = FpX_invMontgomery(T,p);
    gel(V,3) = FpXQ_sqr_mg(x,mg,T,p);
    if ((degpol(x)<<1) < degpol(T)) {
      for(i = 4; i < l+2; i++)
        gel(V,i) = FpXQ_mul_mg(gel(V,i-1),x,mg,T,p);
    } else { /* use squarings if degree(x) is large */
      for(i = 4; i < l+2; i++)
        gel(V,i) = odd(i)? FpXQ_sqr_mg(gel(V, (i+1)>>1),mg,T,p)
                         : FpXQ_mul_mg(gel(V, i-1),x,mg,T,p);
    }
  } else {
    gel(V,3) = FpXQ_sqr(x,T,p);
    if ((degpol(x)<<1) < degpol(T)) {
      for(i = 4; i < l+2; i++)
        gel(V,i) = FpXQ_mul(gel(V,i-1),x,T,p);
    } else { /* use squarings if degree(x) is large */
      for(i = 4; i < l+2; i++)
        gel(V,i) = odd(i)? FpXQ_sqr(gel(V, (i+1)>>1),T,p)
                         : FpXQ_mul(gel(V, i-1),x,T,p);
    }
  }
  return V;
}

/* assume T irreducible mod p */
int
FpXQ_issquare(GEN x, GEN T, GEN p)
{
  pari_sp av;
  GEN m, z;
  long res;
  if (lg(x) == 2 || equalui(2, p)) return 1;
  if (lg(x) == 3) return Fq_issquare(gel(x,2), T, p);
  av = avma;
  m = diviiexact(subis(powiu(p, degpol(T)), 1), subis(p,1));
  z = constant_term( FpXQ_pow(x, m, T, p) );
  res = kronecker(z, p) == 1;
  avma = av; return res;
}
int
Fp_issquare(GEN x, GEN p)
{
  if (equalui(2, p)) return 1;
  return kronecker(x, p) == 1;
}
/* assume T irreducible mod p */
int
Fq_issquare(GEN x, GEN T, GEN p)
{
  if (typ(x) != t_INT) return FpXQ_issquare(x, T, p);
  return (! odd(degpol(T)) || Fp_issquare(x, p));
}

GEN
FpXQ_matrix_pow(GEN y, long n, long m, GEN P, GEN l)
{
  return RgXV_to_RgM(FpXQ_powers(y,m-1,P,l),n);
}

static GEN
famat_Z_gcd(GEN M, GEN n)
{
  pari_sp av=avma;
  long i, j, l=lg(M[1]);
  GEN F=cgetg(3,t_MAT);
  gel(F,1)=cgetg(l,t_COL);
  gel(F,2)=cgetg(l,t_COL);
  for (i=1, j=1; i<l; i++)
  {
    GEN p = gcoeff(M,i,1);
    GEN e = gminsg(Z_pval(n,p),gcoeff(M,i,2));
    if (signe(e))
    {
      gcoeff(F,j,1)=p;
      gcoeff(F,j,2)=e;
      j++;
    }
  }
  setlg(gel(F,1),j); setlg(gel(F,2),j);
  return gerepilecopy(av,F);
}

/* discrete log in FpXQ for a in Fp^*, g in FpXQ^* of order ord */
GEN
Fp_FpXQ_log(GEN a, GEN g, GEN o, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN q,n_q,ord,ordp, op;

  if (equali1(a)) return gen_0;
  /* p > 2 */

  ordp = subis(p, 1); /* even */
  ord  = dlog_get_ord(o);
  if (!ord) ord = T? subis(powiu(p, degpol(T)), 1): ordp;
  if (equalii(a, ordp)) /* -1 */
    return gerepileuptoint(av, shifti(ord,-1));
  ordp = gcdii(ordp,ord);
  op = typ(o)==t_MAT ? famat_Z_gcd(o,ordp) : ordp;

  q = NULL;
  if (T)
  { /* we want < g > = Fp^* */
    if (!equalii(ord,ordp)) {
      q = diviiexact(ord,ordp);
      g = FpXQ_pow(g,q,T,p);
    }
    g = constant_term(g);
  }
  n_q = Fp_log(a,g,op,p);
  if (q) n_q = mulii(q, n_q);
  return gerepileuptoint(av, n_q);
}

static GEN
_FpXQ_pow(void *data, GEN x, GEN y)
{
  FpX_muldata *D = (FpX_muldata*)data;
  return FpXQ_pow(x,y, D->T, D->p);
}

static ulong
_FpXQ_hash(GEN x)
{
  ulong h=0;
  long i, l=lg(x);
  for (i=2; i<l; i++)
    if (signe(gel(x,i))) h ^= mod2BIL(gel(x,i));
  return h;
}

static GEN
_FpXQ_rand(void *data)
{
  pari_sp av=avma;
  FpX_muldata *D = (FpX_muldata*)data;
  GEN z;
  do
  {
    avma=av;
    z=random_FpX(degpol(D->T),varn(D->T),D->p);
  } while (!signe(z));
  return z;
}

static const struct bb_group FpXQ_star={_FpXQ_mul,_FpXQ_pow,_FpXQ_rand,_FpXQ_hash,cmp_RgX,gequal1};

GEN
FpXQ_order(GEN a, GEN ord, GEN T, GEN p)
{
  if (lgefint(p)==3)
  {
    pari_sp av=avma;
    ulong pp=p[2];
    GEN z = Flxq_order(ZX_to_Flx(a,pp),ord,ZX_to_Flx(T,pp),pp);
    return gerepileuptoint(av,z);
  }
  else
  {
    FpX_muldata s;
    s.T=T; s.p=p;
    return gen_eltorder(a,ord, (void*)&s,&FpXQ_star);
  }
}

static GEN
_FpXQ_easylog(void *E, GEN a, GEN g, GEN ord)
{
  FpX_muldata *s=(FpX_muldata*) E;
  if (degpol(a)) return NULL;
  return Fp_FpXQ_log(constant_term(a),g,ord,s->T,s->p);
}

GEN
FpXQ_log(GEN a, GEN g, GEN ord, GEN T, GEN p)
{
  if (lgefint(p)==3)
  {
    pari_sp av=avma;
    ulong pp=p[2];
    GEN z = Flxq_log(ZX_to_Flx(a,pp),ZX_to_Flx(g,pp),ord,ZX_to_Flx(T,pp),pp);
    return gerepileuptoint(av,z);
  }
  else
  {
    FpX_muldata s;
    GEN z;
    s.T=T; s.p=p;
    z = gen_PH_log(a,g,ord, (void*)&s,&FpXQ_star,_FpXQ_easylog);
    return z? z: cgetg(1,t_VEC);
  }
}

GEN
FpXQ_sqrtn(GEN a, GEN n, GEN T, GEN p, GEN *zeta)
{
  if (!signe(a))
  {
    long v=varn(T);
    if (zeta)
      *zeta=pol_1(v);
    return pol_0(v);
  }
  if (lgefint(p)==3)
  {
    pari_sp av=avma;
    ulong pp=p[2];
    GEN z = Flxq_sqrtn(ZX_to_Flx(a,pp),n,ZX_to_Flx(T,pp),pp,zeta);
    z = Flx_to_ZX(z);
    if (zeta)
    {
      *zeta=Flx_to_ZX(*zeta);
      gerepileall(av,2,&z,zeta);
      return z;
    }
    else return gerepileupto(av, z);
  }
  else
  {
    FpX_muldata s;
    s.T=T; s.p=p;
    return gen_Shanks_sqrtn(a,n,addis(powiu(p,degpol(T)),-1),zeta,
                            (void*)&s,&FpXQ_star);
  }
}

GEN
FpXQ_norm(GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN y = FpX_resultant(T, x, p);
  GEN L = leading_term(T);
  if (gequal1(L) || signe(x)==0) return y;
  return gerepileupto(av, Fp_div(y, Fp_pows(L, degpol(x), p), p));
}

GEN
FpXQ_trace(GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z = FpX_mul(x, FpX_deriv(T, p), p);
  z = FpX_div(RgX_shift_shallow(z, 1), T, p);
  return gerepileuptoint(av, constant_term(z));
}

GEN
FpXQ_charpoly(GEN x, GEN T, GEN p)
{
  pari_sp ltop=avma;
  long v=varn(T);
  GEN R;
  T = leafcopy(T); setvarn(T, MAXVARN);
  x = leafcopy(x); setvarn(x, MAXVARN);
  R = FpX_FpXY_resultant(T, deg1pol_shallow(gen_1,FpX_neg(x,p),v),p);
  return gerepileupto(ltop,R);
}

GEN
FpXQ_minpoly(GEN x, GEN T, GEN p)
{
  pari_sp ltop=avma;
  GEN G,R=FpXQ_charpoly(x, T, p);
  GEN dR=FpX_deriv(R,p);
  while (signe(dR)==0)
  {
    R  = RgX_deflate(R,itos(p));
    dR = FpX_deriv(R,p);
  }
  G=FpX_gcd(R,dR,p);
  G=FpX_normalize(G,p);
  G=FpX_div(R,G,p);
  return gerepileupto(ltop,G);
}

GEN
FpXQ_conjvec(GEN x, GEN T, GEN p)
{
  pari_sp av=avma;
  long i;
  long n = degpol(T), v = varn(T);
  GEN M = FpXQ_matrix_pow(FpXQ_pow(pol_x(v),p,T,p),n,n,T,p);
  GEN z = cgetg(n+1,t_COL);
  gel(z,1) = RgX_to_RgV(x,n);
  for (i=2; i<=n; i++) gel(z,i) = FpM_FpC_mul(M,gel(z,i-1),p);
  gel(z,1) = x;
  for (i=2; i<=n; i++) gel(z,i) = RgV_to_RgX(gel(z,i),v);
  return gerepilecopy(av,z);
}

GEN
gener_FpXQ(GEN T, GEN p, GEN *po)
{
  long i, j, vT = varn(T), f = degpol(T);
  GEN g, L, L2, p_1, q, o;
  pari_sp av0 = avma, av;

  if (f == 1) {
    GEN L, fa;
    o = subis(p, 1);
    fa = Z_factor(o);
    L = gel(fa,1);
    L = vecslice(L, 2, lg(L)-1); /* remove 2 for efficiency */

    g = cgetg(3, t_POL);
    g[1] = evalsigne(1) | evalvarn(vT);
    gel(g,2) = pgener_Fp_local(p, L);
    if (po) *po = mkvec2(o, fa);
    return g;
  }
  if (lgefint(p) == 3)
  {
    ulong pp = (ulong)p[2];
    g = gener_Flxq(ZX_to_Flx(T, pp), pp, po);
    g = Flx_to_ZX(g);
    if (!po) g = gerepileupto(av0, g);
    else
    {
      gel(*po,2) = Flx_to_ZX(gel(*po,2));
      gerepileall(av0, 2, &g, po);
    }
    return g;
  }
  p_1 = subis(p,1);
  q = diviiexact(subis(powiu(p,f), 1), p_1);

  L = NULL;
  (void)Z_lvalrem(p_1, 2, &L);
  L = gel(Z_factor(L),1);
  for (i=lg(L)-1; i; i--) gel(L,i) = diviiexact(p_1, gel(L,i));
  o = factor_pn_1(p,f);
  L2 = leafcopy( gel(o, 1) );
  for (i = j = 1; i < lg(L2); i++)
  {
    if (remii(p_1, gel(L2,i)) == gen_0) continue;
    gel(L2,j++) = diviiexact(q, gel(L2,i));
  }
  setlg(L2, j);
  for (av = avma;; avma = av)
  {
    GEN t;
    g = random_FpX(f, vT, p);
    if (degpol(g) < 1) continue;
    t = FpX_resultant(T, g, p); /* Ng = g^q, assuming T is monic */
    if (equali1(t) || !is_gener_Fp(t, p, p_1, L)) continue;
    t = FpXQ_pow(g, shifti(p_1,-1), T, p);
    for (i = 1; i < j; i++)
    {
      GEN a = FpXQ_pow(t, gel(L2,i), T, p);
      if (!degpol(a) && equalii(gel(a,2), p_1)) break;
    }
    if (i == j) break;
  }
  if (!po) g = gerepilecopy(av0, g);
  else {
    *po = mkvec2(subis(powiu(p,f), 1), o);
    gerepileall(av0, 2, &g, po);
  }
  return g;
}
