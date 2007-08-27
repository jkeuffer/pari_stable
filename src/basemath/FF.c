/* $Id$

Copyright (C) 2000-2003  The PARI group.

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

/*************************************************************************/
/**                                                                     **/
/**                   Routines for handling FFELT                       **/
/**                                                                     **/
/*************************************************************************/

INLINE void
_getFF(GEN x, GEN *T, GEN *p, ulong *pp)
{
  *T=gel(x,3);
  *p=gel(x,4);
  *pp=mael(x,4,2);
}


INLINE GEN
_initFF(GEN x, GEN *T, GEN *p, ulong *pp)
{
  _getFF(x,T,p,pp);
  return cgetg(5,t_FFELT);
}

INLINE void
_checkFF(GEN x, GEN y, const char *s)
{
  if (x[1]!=y[1] || !equalii(gel(x,4),gel(y,4)) || !gequal(gel(x,3),gel(y,3)))
    pari_err(operi,s,x,y);
}


INLINE GEN
_mkFF(GEN x, GEN z, GEN r)
{
  z[1]=x[1];
  gel(z,2)=r;
  gel(z,3)=gcopy(gel(x,3));
  gel(z,4)=icopy(gel(x,4));
  return z;
}

INLINE GEN
_mkFF_i(GEN x, GEN z, GEN r)
{
  z[1]=x[1];
  gel(z,2)=r;
  gel(z,3)=gel(x,3);
  gel(z,4)=gel(x,4);
  return z;
}


/* Return true if x and y are defined in the same field */

int
FF_samefield(GEN x, GEN y)
{
  return x[1] == y[1] && equalii(gel(x,4),gel(y,4))
                      && gequal(gel(x,3),gel(y,3));
}

int
FF_equal(GEN x, GEN y)
{
  return x[1] == y[1] && equalii(gel(x,4),gel(y,4)) 
                      && gequal(gel(x,3),gel(y,3)) 
                      && gequal(gel(x,2),gel(y,2));
}

int
FF_cmp0(GEN x)
{
  return lgpol(gel(x,2))==0;
}

int
FF_cmp1(GEN x)
{
  switch(x[1])
  {
  case t_FF_FpXQ:
    return gcmp1(gel(x,2));
  default:
    return degpol(gel(x,2))==0 && mael(x,2,2)==1;
  }
}

int
FF_cmp_1(GEN x)
{
  ulong pp;
  GEN T, p;
  int b;
  _getFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    {
      pari_sp ltop=avma;
      b=gequal(gel(x,2),addis(p,-1));
      avma=ltop;
      break;
    }
  default:
    b=(degpol(gel(x,2))==0 && (ulong)mael(x,2,2)==pp-1);
  }
  return b;
}

GEN
FF_zero(GEN x)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    r=zeropol(varn(T));
    break;
  default:
    r=zero_Flx(T[1]);
  }
  return _mkFF(x,z,r);
}

GEN
FF_1(GEN x)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    r=pol_1(varn(T));
    break;
  default:
    r=Fl_to_Flx(1UL,T[1]);
  }
  return _mkFF(x,z,r);
}

GEN
FF_p(GEN x)
{
  return gel(x,4);
}

GEN
FF_to_FpXQ(GEN x)
{
  switch(x[1])
  {
  case t_FF_FpXQ:
    return gel(x,2);
  default:
    return Flx_to_ZX(gel(x,2));
  }
}

GEN
FF_add(GEN x, GEN y)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  _checkFF(x,y,"+");
  switch(x[1])
  {
  case t_FF_FpXQ:
    {
      pari_sp av=avma;
      r=gerepileupto(av,FpX_add(gel(x,2),gel(y,2),p));
      break;
    }
  default:
    r=Flx_add(gel(x,2),gel(y,2),pp);
  }
  return _mkFF(x,z,r);
}

GEN
FF_Z_add(GEN x, GEN y)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    {
      pari_sp av=avma;
      r=gerepileupto(av,FpX_Fp_add(gel(x,2),modii(y,p),p));
      break;
    }
  default:
    r=Flx_Fl_add(gel(x,2),umodiu(y,pp),pp);
  }
  return _mkFF(x,z,r);
}

GEN
FF_neg(GEN x)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    r=FpX_neg(gel(x,2),p);
    break;
  default:
    r=Flx_neg(gel(x,2),pp);
  }
  return _mkFF(x,z,r);
}

GEN
FF_neg_i(GEN x)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    r=FpX_neg(gel(x,2),p);
    break;
  default:
    r=Flx_neg(gel(x,2),pp);
  }
  return _mkFF_i(x,z,r);
}

GEN
FF_mul(GEN x, GEN y)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  _checkFF(x,y,"*"); 
  switch(x[1])
  {
  case t_FF_FpXQ:
    {
      pari_sp av=avma;
      r=gerepileupto(av,FpXQ_mul(gel(x,2),gel(y,2),T,p));
      break;
    }
  default:
    r=Flxq_mul(gel(x,2),gel(y,2),T,pp);
  }
  return _mkFF(x,z,r);
}

GEN
FF_Z_mul(GEN x, GEN y)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    {
      pari_sp av=avma;
      r=gerepileupto(av,FpX_Fp_mul(gel(x,2),modii(y,p),p));
      break;
    }
  default:
    r=Flx_Fl_mul(gel(x,2),umodiu(y,pp),pp);
  }
  return _mkFF(x,z,r);
}

GEN
FF_Z_Z_muldiv(GEN x, GEN a, GEN b)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  pari_sp av=avma;
  switch(x[1])
  {
  case t_FF_FpXQ:
    r=gerepileupto(av,FpX_Fp_mul(gel(x,2),Fp_div(a,b,p),p));
    break;
  default:
    r=gerepileupto(av,Flx_Fl_mul(gel(x,2),Fl_div(umodiu(a,pp),umodiu(b,pp),pp),pp));
  }
  return _mkFF(x,z,r);
}

GEN
FF_sqr(GEN x)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    {
      pari_sp av=avma;
      r=gerepileupto(av,FpXQ_sqr(gel(x,2),T,p));
      break;
    }
  default:
    r=Flxq_sqr(gel(x,2),T,pp);
  }
  return _mkFF(x,z,r);
}

GEN
FF_mul2n(GEN x, long n)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  pari_sp av=avma;
  switch(x[1])
  {
  case t_FF_FpXQ:
    {
      GEN p1;
      if (n>0) p1=remii(int2n(n),p);
      else p1=Fp_inv(remii(int2n(-n),p),p);
      r=gerepileupto(av,FpX_Fp_mul(gel(x,2),p1,p));
    }
    break;
  default:
    {
      ulong l1;
      if (n>0) l1=umodiu(int2n(n),pp);
      else l1=Fl_inv(umodiu(int2n(-n),pp),pp);
      r=gerepileupto(av,Flx_Fl_mul(gel(x,2),l1,pp));
    }
  }
  return _mkFF(x,z,r);
}

GEN
FF_inv(GEN x)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  pari_sp av=avma;
  switch(x[1])
  {
  case t_FF_FpXQ:
    r=gerepileupto(av,FpXQ_inv(gel(x,2),T,p));
    break;
  default:
    r=Flxq_inv(gel(x,2),T,pp);
  }
  return _mkFF(x,z,r);
}

GEN
FF_div(GEN x, GEN y)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  pari_sp av=avma;
  _checkFF(x,y,"/");
  switch(x[1])
  {
  case t_FF_FpXQ:
    r=gerepileupto(av,FpXQ_div(gel(x,2),gel(y,2),T,p));
    break;
  default:
    r=gerepileupto(av,Flxq_div(gel(x,2),gel(y,2),T,pp));
  }
  return _mkFF(x,z,r);
}

GEN
Z_FF_div(GEN n, GEN x)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  pari_sp av=avma;
  switch(x[1])
  {
  case t_FF_FpXQ:
    r=gerepileupto(av,FpX_Fp_mul(FpXQ_inv(gel(x,2),T,p),modii(n,p),p));
    break;
  default:
    r=gerepileupto(av,Flx_Fl_mul(Flxq_inv(gel(x,2),T,pp),umodiu(n,pp),pp));
  }
  return _mkFF(x,z,r);
}

GEN
FF_sqrtn(GEN x, GEN n, GEN *zetan)
{
  ulong pp;
  GEN r, T, p, y=_initFF(x,&T,&p,&pp);
  switch (x[1])
  {
  case t_FF_FpXQ: 
    r=FpXQ_sqrtn(gel(x,2),n,T,p,zetan);
    break;
  default:
    r=Flxq_sqrtn(gel(x,2),n,T,pp,zetan);
  }
  if (!r) 
    pari_err(talker,"nth-root does not exist in FF_sqrtn");
  (void)_mkFF(x, y, r);
  if (zetan)
  { 
    GEN z = cgetg(lg(y),t_FFELT);
    *zetan=_mkFF(x, z, *zetan);
  }
  return y;
}

GEN
FF_sqrt(GEN x)
{
  return FF_sqrtn(x,gen_2,NULL);
}

GEN
FF_pow(GEN x, GEN n)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  switch(x[1])
   {
   case t_FF_FpXQ:
     r = FpXQ_pow(gel(x,2), n, T, p);
     break;
   default:
     r = Flxq_pow(gel(x,2), n, T, pp);
   }
  return _mkFF(x,z,r);
}

GEN
FF_norm(GEN x) 
{
  ulong pp;
  GEN T,p;
  _getFF(x,&T,&p,&pp);
  switch (x[1])
  {
  case t_FF_FpXQ:
    return FpXQ_norm(gel(x,2),T,p);
  default:
    return utoi(Flxq_norm(gel(x,2),T,pp));
  }
}

GEN
FF_trace(GEN x)
{
  ulong pp;
  GEN r,T,p;
  pari_sp av;
  _getFF(x,&T,&p,&pp);
  av = avma;
  switch(x[1])
  {
  case t_FF_FpXQ:
    r = quicktrace(gel(x,2), polsym(T, degpol(T)-1));
    break;
  default:
    r = quicktrace(Flx_to_ZX(gel(x,2)), polsym(Flx_to_ZX(T), degpol(T)-1));
  }
  return gerepileupto(av, modii(r,p));
}

GEN
FF_charpoly(GEN x) 
{
  ulong pp;
  GEN T,p;
  pari_sp av=avma;
  _getFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    return gerepileupto(av,FpXQ_charpoly(gel(x,2), T, p));
  default:
    return gerepileupto(av,Flx_to_ZX(Flxq_charpoly(gel(x,2), T, pp)));
  }
}

GEN
FF_minpoly(GEN x) 
{
  ulong pp;
  GEN T,p;
  pari_sp av=avma;
  _getFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    return gerepileupto(av,FpXQ_minpoly(gel(x,2), T, p));
  default:
    return gerepileupto(av,Flx_to_ZX(Flxq_minpoly(gel(x,2), T, pp)));
  }
}

int
is_Z_factor(GEN f)
{
  long i, l;
  GEN P, E;
  if (typ(f) != t_MAT || lg(f) != 3) return 0;
  P = gel(f,1);
  E = gel(f,2); l = lg(P);
  for (i = 1; i < l; i++)
  {
    GEN p = gel(P,i), e = gel(E,i);
    if (typ(p) != t_INT || signe(p) <= 0 || typ(e) != t_INT || signe(e) <= 0)
      return 0;
  }
  return 1;
}

GEN
FF_log(GEN x, GEN g, GEN ord)
{
  pari_sp av=avma;
  ulong pp;
  GEN r, T, p;
  _getFF(x,&T,&p,&pp);
  _checkFF(x,g,"log");
  if (!ord) ord = factor_pn_1(p,degpol(T));
  else
    if (!is_Z_factor(ord)) err(typeer, "FF_log");
  switch(x[1])
  {
  case t_FF_FpXQ:
    r = FpXQ_log(gel(x,2), gel(g,2), ord, T, p);
    break;
  default:
    r = Flxq_log(gel(x,2), gel(g,2), ord, T, pp);
  }
  return gerepileuptoint(av, r);
}

GEN
FF_order(GEN x, GEN o)
{
  pari_sp av=avma;
  ulong pp;
  GEN r, T,p;
  _getFF(x,&T,&p,&pp);
  if (!o) o = factor_pn_1(p,degpol(T));
  switch(x[1])
  {
  case t_FF_FpXQ:
    r = FpXQ_order(gel(x,2), o, T, p);
    break;
  default:
    r = Flxq_order(gel(x,2), o, T, pp);
  }
  if (!o) r = gerepileuptoint(av,r);
  return r;
}

GEN
FF_primroot(GEN x, GEN *o)
{
  ulong pp;
  GEN r,T,p,z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    r = gener_FpXQ(T, p, o);
    break;
  default:
    r = gener_Flxq(T, pp, o);
  }
  return _mkFF(x,z,r);
}

static GEN
to_FF(GEN x, GEN ff)
{
  if (typ(x) == t_INT) return x;
  else
  {
    ulong pp;
    GEN r, T, p, z=_initFF(ff,&T,&p,&pp);
    switch(ff[1])
    {
    case t_FF_FpXQ:
      r=x;
      break;
    default:
      r=ZX_to_Flx(x,pp);
    }
    return _mkFF_i(ff,z,r);
  }
}

static GEN
to_FF_pol(GEN x, GEN ff)
{
  long i, lx, tx = typ(x);
  if (tx != t_POL) pari_err(typeer,"to_FF_pol");
  lx = lg(x);
  for (i=2; i<lx; i++) gel(x,i) = to_FF(gel(x,i), ff);
  return x;
}

static GEN
to_FF_fact(GEN P, GEN E, GEN ff, pari_sp av)
{
  GEN y = cgetg(3,t_MAT), u, v, zf;
  long j, l = lg(P), nbf = lg(P);

  u = cgetg(nbf,t_COL); gel(y,1) = u;
  v = cgetg(nbf,t_COL); gel(y,2) = v;
  for (j=1; j<l; j++)
  {
    gel(u,j) = simplify_i(gel(P,j)); /* may contain pols of degree 0 */
    gel(v,j) = utoi((ulong)E[j]);
  }
  y = gerepilecopy(av, y); u = gel(y,1);
  zf = FF_zero(ff);
  for (j=1; j<nbf; j++) gel(u,j) = to_FF_pol(gel(u,j), zf);
  return y;
}

/*Warning: FFX are polynomials whose coefficients are compatible with FF:
 * t_INT t_INTMOD, t_FFELT*/

static GEN
FFX_to_FqX(GEN x, GEN T, GEN p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_POL); z[1] = x[1];
  for (i = 2; i < l; i++) 
    if (typ(gel(x,i))==t_FFELT)
      gel(z,i) = simplify_i(FF_to_FpXQ(gel(x,i)));
    else
      gel(z,i) = simplify_i(Rg_to_FpXQ(gel(x,i), T,p));
  return normalizepol_i(z, l);
}

/* Factor P over the field of definition of x */
GEN
FFX_factor(GEN P, GEN x)
{
  ulong pp;
  GEN r, T, p;
  pari_sp av=avma;
  _getFF(x,&T,&p,&pp);
  if (x[1]) T=Flx_to_ZX(T);
  r = FqX_factor(FFX_to_FqX(P, T,p), T,p);
  return to_FF_fact(gel(r,1),gel(r,2), x,av);
}
