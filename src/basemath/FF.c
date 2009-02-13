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
  *pp=(*p)[2];
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

INLINE GEN
mkFF_i(GEN x, GEN r)
{
  GEN z = cgetg(5,t_FFELT);
  return _mkFF_i(x,z,r);
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
  GEN A = gel(x,2);
  switch(x[1])
  {
  case t_FF_FpXQ:
    return degpol(A)==0 && gequal1(gel(A,2));
  default:
    return degpol(A)==0 && A[2]==1;
  }
}

static int
Fp_cmp_1(GEN x, GEN p)
{
  pari_sp av = avma;
  int b = equalii(x, addis(p,-1));
  avma = av; return b;
}

int
FF_cmp_1(GEN x)
{
  ulong pp;
  GEN T, p, y = gel(x,2);
  _getFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    return (degpol(y) == 0 && Fp_cmp_1(gel(y,2), p));
  default:
    return (degpol(y) == 0 && (ulong)y[2] == pp-1);
  }
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
  case t_FF_F2xq:
    r=zero_F2x(T[1]);
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
  case t_FF_F2xq:
    r=pol1_F2x(T[1]);
    break;
  default:
    r=pol1_Flx(T[1]);
  }
  return _mkFF(x,z,r);
}

GEN
FF_p(GEN x)
{
  return icopy(gel(x,4));
}

GEN
FF_p_i(GEN x)
{
  return gel(x,4);
}

GEN
FF_mod(GEN x)
{
  switch(x[1])
  {
  case t_FF_FpXQ:
    return ZX_copy(gel(x,3));
  case t_FF_F2xq:
    return F2x_to_ZX(gel(x,3));
  default:
    return Flx_to_ZX(gel(x,3));
  }
}

GEN
FF_to_FpXQ(GEN x)
{
  switch(x[1])
  {
  case t_FF_FpXQ:
    return ZX_copy(gel(x,2));
  case t_FF_F2xq:
    return F2x_to_ZX(gel(x,2));
  default:
    return Flx_to_ZX(gel(x,2));
  }
}

GEN
FF_to_FpXQ_i(GEN x)
{
  switch(x[1])
  {
  case t_FF_FpXQ:
    return gel(x,2);
  case t_FF_F2xq:
    return F2x_to_ZX(gel(x,2));
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
    r=FpX_add(gel(x,2),gel(y,2),p);
    break;
  case t_FF_F2xq:
    r=F2x_add(gel(x,2),gel(y,2));
    break;
  default:
    r=Flx_add(gel(x,2),gel(y,2),pp);
  }
  return _mkFF(x,z,r);
}
GEN
FF_sub(GEN x, GEN y)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  _checkFF(x,y,"+");
  switch(x[1])
  {
  case t_FF_FpXQ:
    r=FpX_sub(gel(x,2),gel(y,2),p);
    break;
  case t_FF_F2xq:
    r=F2x_add(gel(x,2),gel(y,2));
    break;
  default:
    r=Flx_sub(gel(x,2),gel(y,2),pp);
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
  case t_FF_F2xq:
    r=mpodd(y)?F2x_1_add(gel(x,2)):vecsmall_copy(gel(x,2));
    break;
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
  case t_FF_F2xq:
    r=vecsmall_copy(gel(x,2));
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
  case t_FF_F2xq:
    r=gel(x,2);
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
  case t_FF_F2xq:
    r=F2xq_mul(gel(x,2),gel(y,2),T);
    break;
  default:
    r=Flxq_mul(gel(x,2),gel(y,2),T,pp);
  }
  return _mkFF(x,z,r);
}

GEN
FF_Z_mul(GEN x, GEN y)
{
  ulong pp;
  GEN r, T, p, A = gel(x,2), z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ: /* modii(y,p) left on stack for efficiency */
    r = FpX_Fp_mul(A, modii(y,p),p);
    break;
  case t_FF_F2xq:
    r = mpodd(y)? vecsmall_copy(A): zero_Flx(A[1]);
    break;
  default:
    r = Flx_Fl_mul(A, umodiu(y,pp), pp);
  }
  return _mkFF(x,z,r);
}

GEN
FF_Z_Z_muldiv(GEN x, GEN a, GEN b)
{
  ulong pp;
  GEN r, T, p, A = gel(x,2), z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ: /* Fp_div(a,b,p) left on stack for efficiency */
    r = FpX_Fp_mul(A, Fp_div(a,b,p), p);
    break;
  case t_FF_F2xq:
    if (!mpodd(b)) pari_err(gdiver);
    r = mpodd(a)? vecsmall_copy(A): zero_Flx(A[1]);
    break;
  default:
    r = Flx_Fl_mul(A, Fl_div(umodiu(a,pp),umodiu(b,pp),pp),pp);
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
  case t_FF_F2xq:
    r=F2xq_sqr(gel(x,2),T);
    break;
  default:
    r=Flxq_sqr(gel(x,2),T,pp);
  }
  return _mkFF(x,z,r);
}

GEN
FF_mul2n(GEN x, long n)
{
  ulong pp;
  GEN r, T, p, A = gel(x,2), z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    {
      GEN p1; /* left on stack for efficiency */
      if (n>0) p1=remii(int2n(n),p);
      else p1=Fp_inv(remii(int2n(-n),p),p);
      r = FpX_Fp_mul(A, p1, p);
    }
    break;
  case t_FF_F2xq:
    if (n<0) pari_err(gdiver);
    r = n==0? vecsmall_copy(A): zero_Flx(A[1]);
    break;
  default:
    {
      ulong l1;
      if (n>0) l1 = umodiu(int2n(n),pp);
      else l1 = Fl_inv(umodiu(int2n(-n),pp),pp);
      r = Flx_Fl_mul(A,l1,pp);
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
  case t_FF_F2xq:
    r=F2xq_inv(gel(x,2),T);
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
  case t_FF_F2xq:
    r=gerepileupto(av,F2xq_div(gel(x,2),gel(y,2),T));
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
  GEN r, T, p, A = gel(x,2), z=_initFF(x,&T,&p,&pp);
  pari_sp av=avma;
  switch(x[1])
  {
  case t_FF_FpXQ:
    r = gerepileupto(av,FpX_Fp_mul(FpXQ_inv(A,T,p),modii(n,p),p));
    break;
  case t_FF_F2xq:
    r = F2xq_inv(A,T); /*Check for division by 0*/
    if(!mpodd(n)) { avma = av; r = zero_Flx(A[1]); }
    break;
  default:
    r = gerepileupto(av, Flx_Fl_mul(Flxq_inv(A,T,pp),umodiu(n,pp),pp));
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
  case t_FF_F2xq:
    r=F2xq_sqrtn(gel(x,2),n,T,zetan);
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

long
FF_issquare(GEN x)
{
  GEN T, p;
  ulong pp;
  _getFF(x, &T, &p, &pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    return FpXQ_issquare(gel(x,2), T, p);

  case t_FF_F2xq:
    return 1;

  default: /* case t_FF_Flxq: */
    return Flxq_issquare(gel(x,2), T, pp);
  }
}

long
FF_issquareall(GEN x, GEN *pt)
{
  if (!pt) return FF_issquare(x);
  return FF_ispower(x, gen_2, pt);
}

long
FF_ispower(GEN x, GEN K, GEN *pt)
{
  ulong pp;
  GEN r, T, p;
  pari_sp av = avma;
  if (!K) pari_err(talker,"missing exponent in FF_ispower");

  if (FF_cmp0(x)) { if (pt) *pt = gcopy(x); return 1; }
  _getFF(x, &T, &p, &pp);
  if (pt) *pt = cgetg(5,t_FFELT);
  switch(x[1])
  {
   case t_FF_FpXQ:
     r = FpXQ_sqrtn(gel(x,2),K,T,p,NULL);
     if (!r) { avma = av; return 0; }
     break;

   case t_FF_F2xq:
     r = F2xq_sqrtn(gel(x,2),K,T,NULL);
     if (!r) { avma = av; return 0; }
     break;

   default: /* case t_FF_Flxq: */
     r = Flxq_sqrtn(gel(x,2),K,T,pp,NULL);
     if (!r) { avma = av; return 0; }
     break;
  }
  if (pt) { (void)_mkFF(x,*pt,r); }
  return 1;
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
   case t_FF_F2xq:
     r = F2xq_pow(gel(x,2), n, T);
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
  case t_FF_F2xq:
    return lgpol(gel(x,2))?gen_1:gen_0;
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
  case t_FF_F2xq:
    r = quicktrace(F2x_to_ZX(gel(x,2)), polsym(F2x_to_ZX(T), F2x_degree(T)-1));
    break;
  default:
    r = quicktrace(Flx_to_ZX(gel(x,2)), polsym(Flx_to_ZX(T), degpol(T)-1));
  }
  return gerepileupto(av, modii(r,p));
}

GEN
FF_conjvec(GEN x)
{
  ulong pp;
  GEN r,T,p,v;
  long i,l;
  pari_sp av;
  _getFF(x,&T,&p,&pp);
  av = avma;
  switch(x[1])
  {
  case t_FF_FpXQ:
    v = FpXQ_conjvec(gel(x,2), T, p);
    break;
  case t_FF_F2xq:
    v = F2xq_conjvec(gel(x,2), T);
    break;
  default:
    v = Flxq_conjvec(gel(x,2), T, pp);
  }
  l = lg(v); r = cgetg(l, t_COL);
  for(i=1; i<l; i++)
    gel(r,i) = mkFF_i(x, gel(v,i));
  return gerepilecopy(av, r);
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
  case t_FF_F2xq:
    return gerepileupto(av,Flx_to_ZX(Flxq_charpoly(F2x_to_Flx(gel(x,2)),
                                                   F2x_to_Flx(T), 2UL)));
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
  case t_FF_F2xq:
    return gerepileupto(av,Flx_to_ZX(Flxq_minpoly(F2x_to_Flx(gel(x,2)),
                                                  F2x_to_Flx(T), 2UL)));
  default:
    return gerepileupto(av,Flx_to_ZX(Flxq_minpoly(gel(x,2), T, pp)));
  }
}

GEN
FF_log(GEN x, GEN g, GEN ord)
{
  pari_sp av=avma;
  ulong pp;
  GEN r, T, p;
  _getFF(x,&T,&p,&pp);
  _checkFF(x,g,"log");
  switch(x[1])
  {
  case t_FF_FpXQ:
    if (!ord) ord = factor_pn_1(p,degpol(T));
    r = FpXQ_log(gel(x,2), gel(g,2), ord, T, p);
    break;
  case t_FF_F2xq:
    if (!ord) ord = factor_pn_1(gen_2,F2x_degree(T));
    r = F2xq_log(gel(x,2), gel(g,2), ord, T);
    break;
  default:
    if (!ord) ord = factor_pn_1(p,degpol(T));
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
  switch(x[1])
  {
  case t_FF_FpXQ:
    if (!o) o = factor_pn_1(p,degpol(T));
    r = FpXQ_order(gel(x,2), o, T, p);
    break;
  case t_FF_F2xq:
    if (!o) o = factor_pn_1(gen_2,F2x_degree(T));
    r = F2xq_order(gel(x,2), o, T);
    break;
  default:
    if (!o) o = factor_pn_1(p,degpol(T));
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
  case t_FF_F2xq:
    r = gener_F2xq(T, o);
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
    case t_FF_F2xq:
      r=ZX_to_F2x(x);
      break;
    default:
      r=ZX_to_Flx(x,pp);
    }
    return _mkFF_i(ff,z,r);
  }
}

/* in place */
static GEN
to_FF_pol(GEN x, GEN ff)
{
  long i, lx = lg(x);
  if (typ(x) != t_POL) pari_err(typeer,"to_FF_pol");
  for (i=2; i<lx; i++) gel(x,i) = to_FF(gel(x,i), ff);
  return x;
}
/* in place */
static GEN
to_FF_vec(GEN x, GEN ff)
{
  long i, lx = lg(x);
  for (i=1; i<lx; i++) gel(x,i) = to_FF(gel(x,i), ff);
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
    gel(u,j) = simplify_shallow(gel(P,j)); /* may contain pols of degree 0 */
    gel(v,j) = utoi((ulong)E[j]);
  }
  y = gerepilecopy(av, y); u = gel(y,1);
  zf = FF_zero(ff);
  for (j=1; j<nbf; j++) gel(u,j) = to_FF_pol(gel(u,j), zf);
  return y;
}

/*Warning: FFX are polynomials whose coefficients are compatible with FF:
 * t_INT t_INTMOD, t_FFELT */
static GEN
FFX_to_FqX(GEN x, GEN T, GEN p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_POL); z[1] = x[1];
  for (i = 2; i < l; i++)
  {
    GEN y = gel(x,i);
    y = (typ(y)==t_FFELT)? FF_to_FpXQ(y): Rg_to_FpXQ(y, T,p);
    gel(z,i) = simplify_shallow(y);
  }
  return normalizepol_lg(z, l);
}

/* Factor P over the field of definition of x */
GEN
FFX_factor(GEN P, GEN x)
{
  ulong pp;
  GEN r, T, p;
  pari_sp av=avma;
  _getFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    break;
  case t_FF_F2xq:
    T=F2x_to_ZX(T);
    break;
  default:
    T=Flx_to_ZX(T);
  }
  r = FqX_factor(FFX_to_FqX(P, T,p), T,p);
  return to_FF_fact(gel(r,1),gel(r,2), x,av);
}

/* Roots of P over the field of definition of x */
GEN
FFX_roots(GEN P, GEN x)
{
  ulong pp;
  GEN r, T, p;
  pari_sp av=avma;
  _getFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    break;
  case t_FF_F2xq:
    T=F2x_to_ZX(T);
    break;
  default:
    T=Flx_to_ZX(T);
  }
  r = FqX_roots(FFX_to_FqX(P, T,p), T,p);
  return gerepilecopy(av, to_FF_vec(r, x));
}

GEN
ffgen(GEN T, long v)
{
  GEN A, p, ff;
  long d;
  if (typ(T) != t_POL) pari_err(typeer,"ffgen");
  d = degpol(T); p = NULL;
  if (d < 1 || !is_FpX(&T, &p)) pari_err(typeer,"ffgen");
  ff = cgetg(5,t_FFELT);
  if (v < 0) v = varn(T);
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    long sv = evalvarn(v);
    if (pp==2)
    {
      ff[1] = t_FF_F2xq;
      T = ZX_to_F2x(T); T[1] = sv;
      A = polx_F2x(sv); if (d == 1) A = F2x_rem(A, T);
      p = gen_2;
    }
    else
    {
      ff[1] = t_FF_Flxq;
      T = ZX_to_Flx(T,pp); T[1] = sv;
      A = polx_Flx(sv); if (d == 1) A = Flx_rem(A, T, pp);
      p = icopy(p);
    }
  }
  else
  {
    ff[1] = t_FF_FpXQ;
    T = ZX_copy(T); setvarn(T,v);
    A = pol_x(v); if (d == 1) A = FpX_rem(A, T, p);
    p = icopy(p);
  }
  gel(ff,2) = A;
  gel(ff,3) = T;
  gel(ff,4) = p; return ff;
}

GEN
fforder(GEN x, GEN o)
{
  if (typ(x)!=t_FFELT) pari_err(typeer,"fforder");
  return FF_order(x,o);
}

GEN
ffprimroot(GEN x, GEN *o)
{
  if (typ(x)!=t_FFELT) pari_err(typeer,"ffprimroot");
  return FF_primroot(x,o);
}

GEN
fflog(GEN x, GEN g, GEN o)
{
  if (typ(x)!=t_FFELT || typ(g)!=t_FFELT) pari_err(typeer,"fflog");
  return FF_log(x,g,o);
}

GEN
ffrandom(GEN ff)
{
  ulong pp;
  GEN r, T, p, z = _initFF(ff,&T,&p,&pp);
  switch(ff[1])
  {
  case t_FF_FpXQ:
    r = random_FpX(degpol(T), varn(T), p);
    break;
  case t_FF_F2xq:
    r = random_F2x(F2x_degree(T), T[1]);
    break;
  default:
    r = random_Flx(degpol(T), T[1], pp);
  }
  return _mkFF(ff,z,r);
}
