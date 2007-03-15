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
FpX_normalize(GEN z, GEN p)
{
  GEN p1 = leading_term(z);
  if (lg(z) == 2 || gcmp1(p1)) return z;
  return FpX_Fp_mul(z, Fp_inv(p1,p), p);
}

GEN
FpX_center(GEN T,GEN mod)
{
  long i, l=lg(T);
  GEN mod2=shifti(mod,-1);
  GEN P=cgetg(l,t_POL);
  P[1]=T[1];
  for(i=2;i<l;i++)
    gel(P,i) = cmpii(gel(T,i),mod2)<=0? icopy(gel(T,i)): subii(gel(T,i),mod);
  return P;
}

GEN
FpX_add(GEN x,GEN y,GEN p)
{
  GEN z = ZX_add(x,y);
  return FpX_red(z, p);
}

GEN
FpX_Fp_add(GEN y,GEN x,GEN p)
{
  GEN z;
  long lz, i;
  if (!signe(y))
    return scalarpol(x,varn(y));
  lz=lg(y);
  z=cgetg(lz,t_POL);
  z[1]=y[1];
  gel(z,2) = modii(addii(gel(y,2),x),p);
  for(i=3;i<lz;i++)
    gel(z,i) = icopy(gel(y,i));
  if (lz==3) z = FpX_renormalize(z,lz);
  return z;
}

GEN
FpX_neg(GEN x,GEN p)
{
  long i,d=lg(x);
  GEN y;
  y=cgetg(d,t_POL); y[1]=x[1];
  for(i=2;i<d;i++)
    if (signe(x[i])) gel(y,i) = subii(p,gel(x,i));
    else gel(y,i) = gen_0;
  return y;
}

GEN
FpX_sub(GEN x,GEN y,GEN p)
{
  GEN z = ZX_sub(x,y);
  return FpX_red(z, p);
}

GEN
FpX_mul(GEN x,GEN y,GEN p)
{
  GEN z = ZX_mul(x, y);
  return FpX_red(z, p);
}

GEN
FpX_sqr(GEN x,GEN p)
{
  GEN z = ZX_sqr(x);
  return FpX_red(z, p);
}

GEN
FpX_Fp_mul(GEN x,GEN y,GEN p)
{
  GEN z = ZX_Z_mul(x,y);
  return FpX_red(z, p);
}

GEN
FpX_divrem(GEN x, GEN y, GEN p, GEN *pr)
{
  long vx, dx, dy, dz, i, j, sx, lr;
  pari_sp av0, av, tetpil;
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
    if (z==x) return gcopy(z);
    else return gerepileupto(av0, z);
  }
  av0 = avma; dz = dx-dy;
  if (OK_ULONG(p))
  { /* assume ab != 0 mod p */
    ulong pp = (ulong)p[2];
    GEN a = ZX_to_Flx(x, pp);
    GEN b = ZX_to_Flx(y, pp);
    z = Flx_divrem(a,b,pp, pr);
    avma = av0; /* HACK: assume pr last on stack, then z */
    z = shallowcopy(z);
    if (pr && pr != ONLY_DIVIDES && pr != ONLY_REM)
    {
      *pr = shallowcopy(*pr);
      *pr = Flx_to_ZX_inplace(*pr);
    }
    return Flx_to_ZX_inplace(z);
  }
  lead = gcmp1(lead)? NULL: gclone(Fp_inv(lead,p));
  avma = av0;
  z=cgetg(dz+3,t_POL); z[1] = x[1];
  x += 2; y += 2; z += 2;

  p1 = gel(x,dx); av = avma;
  gel(z,dz) = lead? gerepileupto(av, modii(mulii(p1,lead), p)): icopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av=avma; p1=gel(x,i);
    for (j=i-dy+1; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii(gel(z,j),gel(y,i-j)));
    if (lead) p1 = mulii(p1,lead);
    tetpil=avma; gel(z,i-dy) = gerepile(av,tetpil,modii(p1, p));
  }
  if (!pr) { if (lead) gunclone(lead); return z-2; }

  rem = (GEN)avma; av = (pari_sp)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii(gel(z,j),gel(y,i-j)));
    tetpil=avma; p1 = modii(p1,p); if (signe(p1)) { sx = 1; break; }
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
      p1 = subii(p1, mulii(gel(z,j),gel(y,i-j)));
    tetpil=avma; gel(rem,i) = gerepile(av,tetpil, modii(p1,p));
  }
  rem -= 2;
  if (lead) gunclone(lead);
  if (!sx) (void)FpX_renormalize(rem, lr);
  if (pr == ONLY_REM) return gerepileupto(av0,rem);
  *pr = rem; return z-2;
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
    if (!is_pm1(g)) return gerepileupto(av,g);
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
    a = FpX_red(x, p);
    b = FpX_red(y, p);
    d = a; d1 = b; v = gen_0; v1 = gen_1;
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
FpX_deriv(GEN x, GEN p) 
{ 
   GEN z = ZX_deriv(x);
   return FpX_red(z, p);
}

GEN
FpX_rand(long d1, long v, GEN p)
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
    if (!gcmp1(lb)) res = Fp_mul(res, Fp_powu(lb, da - dc, p), p);
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
  return divide_conquer_assoc(V, &_FpX_mul,(void *)p);
}

GEN
FpV_roots_to_pol(GEN V, GEN p, long v)
{
  pari_sp ltop=avma;
  long i;
  GEN g=cgetg(lg(V),t_VEC);
  for(i=1;i<lg(V);i++)
    gel(g,i) = deg1pol_i(gen_1,modii(negi(gel(V,i)),p),v);
  return gerepileupto(ltop,FpXV_prod(g,p));
}

