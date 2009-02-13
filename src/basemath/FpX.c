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
  if (!lgpol(z)) { avma = (pari_sp)(z + lx); return zeropol(varn(x)); }
  return z;
}

GEN
FpX_Fp_add(GEN y,GEN x,GEN p)
{
  long i, lz = lg(y);
  GEN z;
  if (lz == 2) return scalar_ZX(x,varn(y));
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
FpX_neg(GEN x,GEN p)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx,t_POL);
  y[1] = x[1];
  for(i=2; i<lx; i++) gel(y,i) = Fp_neg(gel(x,i), p);
  return ZX_renormalize(y, lx);
}

GEN
FpX_sub(GEN x,GEN y,GEN p)
{
  long lx = lg(x), ly = lg(y), i;
  GEN z;
  if (lx >= ly)
  {
    z = cgetg(lx,t_POL); z[1] = x[1];
    for (i=2; i<ly; i++) gel(z,i) = Fp_sub(gel(x,i),gel(y,i), p);
    for (   ; i<lx; i++) gel(z,i) = modii(gel(x,i), p);
    z = ZX_renormalize(z, lx);
    if (!lgpol(z)) { avma = (pari_sp)(z + lx); return zeropol(varn(x)); }
  }
  else
  {
    z = cgetg(ly,t_POL); z[1] = y[1];
    for (i=2; i<lx; i++) gel(z,i) = Fp_sub(gel(x,i),gel(y,i), p);
    for (   ; i<ly; i++) gel(z,i) = Fp_neg(gel(y,i), p);
    z = ZX_renormalize(z, ly);
    if (!lgpol(z)) { avma = (pari_sp)(z + ly); return zeropol(varn(x)); }
  }
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
    if (!signe(x)) { avma = (pari_sp)(z + 3); return zeropol(varn(y)); }
    z[1] = y[1]; gel(z,2) = x; return z;
  }
  z = cgetg(ly,t_POL);
  gel(z,2) = Fp_sub(x, gel(y,2), p);
  for (i = 3; i < ly; i++) gel(z,i) = Fp_neg(gel(y,i), p);
  z = ZX_renormalize(z, ly);
  if (!lgpol(z)) { avma = (pari_sp)(z + ly); return zeropol(varn(x)); }
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
  if (!signe(x)) return zeropol(varn(y));
  z = cgetg_copy(y, &l); z[1] = y[1];
  for(i=2; i<l; i++) gel(z,i) = Fp_mul(gel(y,i), x, p);
  return z;
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
      if (pr == ONLY_DIVIDES) { avma=av0; return signe(x)? NULL: zeropol(vx); }
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
    av0 = avma; z = FpX_normalize(x, p);
    if (z==x) return ZX_copy(z);
    else return gerepileupto(av0, z);
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
  long l = lg(a), i;
  GEN z = cgetg(l-1, t_POL), a0, z0;
  z[1] = evalsigne(1) | evalvarn(0);
  a0 = a + l-1;
  z0 = z + l-2; *z0 = *a0--;
  for (i=l-3; i>1; i--) /* z[i] = (a[i+1] + x*z[i+1]) % p */
  {
    GEN t = addii(gel(a0--,0), Fp_mul(x, gel(z0--,0), p));
    *z0 = (long)t;
  }
  if (r) *r = addii(gel(a0,0), Fp_mul(x, gel(z0,0), p));
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

/* x and y in Z[X], return lift(gcd(x mod p, y mod p)) */
GEN
FpX_gcd(GEN x, GEN y, GEN p)
{
  GEN a,b,c;
  pari_sp av0, av;

  if (lgefint(p)==3)
  {
    ulong pp=p[2];
    av = avma;
    (void)new_chunk((lg(x) + lg(y)) << 2); /* scratch space */
    a = ZX_to_Flx(x, pp);
    b = ZX_to_Flx(y, pp);
    a = Flx_gcd_i(a,b, pp);
    avma = av; return Flx_to_ZX(a);
  }
  av0=avma;
  a = FpX_red(x, p); av = avma;
  b = FpX_red(y, p);
  while (signe(b))
  {
    av = avma; c = FpX_rem(a,b,p); a=b; b=c;
  }
  avma = av; return gerepileupto(av0, a);
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
    if (!equali1(g)) return gerepileupto(av,g);
    c = FpX_rem(a,b,p); a=b; b=c;
  }
  avma = av; return gen_1;
}

/* x and y in Z[X], return lift(gcd(x mod p, y mod p)). Set u and v st
 * ux + vy = gcd (mod p) */
GEN
FpX_extgcd(GEN x, GEN y, GEN p, GEN *ptu, GEN *ptv)
{
  GEN a,b,q,r,u,v,d,d1,v1;
  pari_sp ltop=avma;
  if (lgefint(p)==3)
  {
    ulong pp=p[2];
    a = ZX_to_Flx(x, pp);
    b = ZX_to_Flx(y, pp);
    d = Flx_extgcd(a,b, pp, &u,&v);
    d=Flx_to_ZX(d);
    u=Flx_to_ZX(u);
    v=Flx_to_ZX(v);
  }
  else
  {
    long vx = varn(x);
    a = FpX_red(x, p);
    b = FpX_red(y, p);
    d = a; d1 = b;
    v = zeropol(vx); v1 = scalar_ZX_shallow(gen_1,vx);
    while (signe(d1))
    {
      q = FpX_divrem(d,d1,p, &r);
      v = FpX_sub(v,FpX_mul(q,v1,p),p);
      u=v; v=v1; v1=u;
      u=r; d=d1; d1=u;
    }
    u = FpX_sub(d,FpX_mul(b,v,p),p);
    u = FpX_div(u,a,p);
  }
  gerepileall(ltop,3,&d,&u,&v);
  *ptu = u; *ptv = v; return d;
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
    p1 = modii(addii(mulii(p1,r), gel(x,j)),p);
  }
 fppoleval:
  modiiz(p1,p,res);
  avma=av;
  return res;
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
    if (dc < 0) { avma = av; return 0; }

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
/**                              FpXQ                                 **/
/**                                                                   **/
/***********************************************************************/

/* FpXQ are elements of Fp[X]/(T), represented by FpX*/

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
  GEN z, U, V;

  z = FpX_extgcd(x, T, p, &U, &V);
  if (degpol(z)) return NULL;
  z = Fp_invsafe(gel(z,2), p);
  if (!z) return NULL;
  return FpX_Fp_mul(U, z, p);
}

GEN
FpXQ_inv(GEN x,GEN T,GEN p)
{
  pari_sp av = avma;
  GEN U = FpXQ_invsafe(x, T, p);
  if (!U) pari_err(talker,"non invertible polynomial in FpXQ_inv");
  return gerepileupto(av, U);
}

GEN
FpXQ_div(GEN x,GEN y,GEN T,GEN p)
{
  pari_sp av = avma;
  return gerepileupto(av, FpXQ_mul(x,FpXQ_inv(y,T,p),T,p));
}

typedef struct {
  GEN pol, p;
} FpX_muldata;

static GEN
_FpXQ_sqr(void *data, GEN x)
{
  FpX_muldata *D = (FpX_muldata*)data;
  return FpXQ_sqr(x, D->pol, D->p);
}
static GEN
_FpXQ_mul(void *data, GEN x, GEN y)
{
  FpX_muldata *D = (FpX_muldata*)data;
  return FpXQ_mul(x,y, D->pol, D->p);
}

/* x,pol in Z[X], p in Z, n in Z, compute lift(x^n mod (p, pol)) */
GEN
FpXQ_pow(GEN x, GEN n, GEN pol, GEN p)
{
  FpX_muldata D;
  pari_sp av;
  long s = signe(n);
  GEN y;

  if (!s) return pol_1(varn(x));
  if (is_pm1(n)) /* +/- 1 */
    return (s < 0)? FpXQ_inv(x,pol,p): ZX_copy(x);
  av = avma;
  if (!is_bigint(p))
  {
    ulong pp = p[2];
    pol = ZX_to_Flx(pol, pp);
    x   = ZX_to_Flx(x,   pp);
    y = Flx_to_ZX( Flxq_pow(x, n, pol, pp) );
  }
  else
  {
    D.pol = pol;
    D.p   = p;
    if (s < 0) x = FpXQ_inv(x,pol,p);
    y = leftright_pow(x, n, (void*)&D, &_FpXQ_sqr, &_FpXQ_mul);
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
  gel(V,3) = FpXQ_sqr(x,T,p);
  if ((degpol(x)<<1) < degpol(T)) {
    for(i = 4; i < l+2; i++)
      gel(V,i) = FpXQ_mul(gel(V,i-1),x,T,p);
  } else { /* use squarings if degree(x) is large */
    for(i = 4; i < l+2; i++)
      gel(V,i) = odd(i)? FpXQ_sqr(gel(V, (i+1)>>1),T,p)
		       : FpXQ_mul(gel(V, i-1),x,T,p);
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
  av = avma;
  m = diviiexact(subis(powiu(p, degpol(T)), 1), subis(p,1));
  z = constant_term( FpXQ_pow(x, m, T, p) );
  res = kronecker(z, p) == 1;
  avma = av; return res;
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
  return FpXQ_pow(x,y, D->pol, D->p);
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
    z=random_FpX(degpol(D->pol),varn(D->pol),D->p);
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
    s.pol=T; s.p=p;
    return gen_eltorder(a,ord, (void*)&s,&FpXQ_star);
  }
}

static GEN
_FpXQ_easylog(void *E, GEN a, GEN g, GEN ord)
{
  FpX_muldata *s=(FpX_muldata*) E;
  if (degpol(a)) return NULL;
  return Fp_FpXQ_log(constant_term(a),g,ord,s->pol,s->p);
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
    s.pol=T; s.p=p;
    return gen_PH_log(a,g,ord, (void*)&s,&FpXQ_star,_FpXQ_easylog);
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
    return zeropol(v);
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
    s.pol=T; s.p=p;
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
