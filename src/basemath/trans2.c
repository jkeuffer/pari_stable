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
/**                   TRANSCENDENTAL FUNCTIONS                     **/
/**                          (part 2)                              **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

extern GEN seq_umul(ulong a, ulong b);
extern int absrnz_egal1(GEN x);

/********************************************************************/
/**                                                                **/
/**                          ARCTANGENT                            **/
/**                                                                **/
/********************************************************************/

static GEN
mpatan(GEN x)
{
  long l, l1, l2, n, m, i, lp, e, s, sx = signe(x);
  pari_sp av0, av;
  double alpha, beta, delta;
  GEN y, p1, p2, p3, p4, p5, unr;
  int inv;

  if (!sx) return realzero_bit(expo(x));
  l = lp = lg(x);
  if (absrnz_egal1(x)) { /* |x| = 1 */
    y = Pi2n(-2, l+1); if (sx < 0) setsigne(y,-1);
    return y;
  }
  e = expo(x); inv = (e >= 0); /* = (|x| > 1 ) */
  if (e > 0) lp += (e>>TWOPOTBITS_IN_LONG);

  y = cgetr(lp); av0 = avma;
  p1 = cgetr(l+1); affrr(x,p1); setsigne(p1, 1); /* p1 = |x| */
  if (inv) p1 = divsr(1, p1);
  e = expo(p1);
  if (e < -100)
    alpha = 1.65149612947 - e; /* log_2(Pi) - e */
  else
    alpha = log2(PI / atan(rtodbl(p1)));
  beta = (double)(bit_accuracy(l)>>1);
  delta = 1 + beta - alpha/2;
  if (delta <= 0) { n = 1; m = 0; }
  else
  {
    double fi = alpha-2;
#if 0
    const double gama = 1.; /* optimize this */
    if (delta >= gama*fi*fi)
    {
      n = (long)(1+sqrt(gama*delta));
      m = (long)(1+sqrt(delta/gama) - fi);
    }
#else
    if (delta >= fi*fi)
    {
      double t = 1 + sqrt(delta);
      n = (long)t;
      m = (long)(t - fi);
    }
#endif
    else
    {
      n = (long)(1+beta/fi);
      m = 0;
    }
  }
  l2 = l+1+(m>>TWOPOTBITS_IN_LONG);
  p2 = cgetr(l2); affrr(p1,p2); av = avma;
  for (i=1; i<=m; i++)
  {
    p5 = addsr(1, mulrr(p2,p2)); setlg(p5,l2);
    p5 = addsr(1, sqrtr_abs(p5, 1)); setlg(p5,l2);
    affrr(divrr(p2,p5), p2); avma = av;
  }
  p3 = mulrr(p2,p2); l1 = 4;
  unr = realun(l2); setlg(unr,4);
  p4 = cgetr(l2); setlg(p4,4);
  affrr(divrs(unr,2*n+1), p4);
  s = 0; e = expo(p3); av = avma;
  for (i = n; i > 1; i--) /* n >= 1. i = 1 done outside for efficiency */
  {
    setlg(p3,l1); p5 = mulrr(p4,p3);
    s -= e; l1 += (s>>TWOPOTBITS_IN_LONG);
    s %= BITS_IN_LONG;
    if (l1 > l2) l1 = l2;
    setlg(unr,l1); p5 = subrr(divrs(unr,2*i-1), p5);
    setlg(p4,l1); affrr(p5,p4); avma = av;
  }
  setlg(p3, l2); p5 = mulrr(p4,p3); /* i = 1 */
  setlg(unr,l2); p4 = subrr(unr, p5);

  p4 = mulrr(p2,p4); setexpo(p4, expo(p4)+m);
  if (inv) p4 = subrr(Pi2n(-1, lp), p4);
  if (sx < 0) setsigne(p4,-signe(p4));
  affrr(p4,y); avma = av0; return y;
}

GEN
gatan(GEN x, long prec)
{
  pari_sp av;
  GEN a, y, p1;

  switch(typ(x))
  {
    case t_REAL:
      return mpatan(x);

    case t_COMPLEX:
      av = avma; p1 = cgetg(3,t_COMPLEX);
      p1[1] = lneg((GEN)x[2]);
      p1[2] = x[1]; 
      y = gerepileupto(av, gath(p1,prec));
      p1 = (GEN)y[1]; y[1] = y[2]; y[2] = (long)p1;
      setsigne(p1,-signe(p1)); return y;

    case t_INTMOD: case t_PADIC: err(typeer,"gatan");

    default:
      av = avma; if (!(y = _toser(x))) break;
      if (valp(y) < 0) err(negexper,"gatan");
      if (lg(y)==2) return gcopy(y);
      /* lg(y) > 2 */
      a = integ(gdiv(derivser(y), gaddsg(1,gsqr(y))), varn(y));
      if (!valp(y)) a = gadd(a, gatan((GEN)y[2],prec));
      return gerepileupto(av, a);
  }
  return transc(gatan,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                             ARCSINE                            **/
/**                                                                **/
/********************************************************************/
/* |x| < 1, x != 0 */
static GEN
mpasin(GEN x) {
  return mpatan( divrr(x, sqrtr( subsr(1, mulrr(x,x)) )) );
}

static GEN mpach(GEN x, long s);
GEN
gasin(GEN x, long prec)
{
  long sx;
  pari_sp av;
  GEN a, y, p1;

  switch(typ(x))
  {
    case t_REAL: sx = signe(x);
      if (!sx) return realzero_bit(expo(x));
      if (absrnz_egal1(x)) { /* |x| = 1 */
        if (sx > 0) return Pi2n(-1, lg(x)); /* 1 */
        y = Pi2n(-1, lg(x)); setsigne(y, -1); return y; /* -1 */
      }
      if (expo(x) < 0) {
        y = cgetr(lg(x)); av = avma;
        affrr(mpasin(x), y); avma = av; return y;
      }
      y = cgetg(3,t_COMPLEX);
      y[1] = (long)Pi2n(-1, lg(x));
      y[2] = (long)mpach(x, 1);
      if (sx < 0)
      {
        setsigne(y[1],-signe(y[1]));
        setsigne(y[2],-signe(y[2]));
      }
      return y;

    case t_COMPLEX:
      av = avma; p1 = cgetg(3,t_COMPLEX);
      p1[1] = (long)gneg_i((GEN)x[2]);
      p1[2] = x[1];
      y=gerepileupto(av, gash(p1,prec));
      p1 = (GEN)y[1]; y[1] = y[2]; y[2] = (long)p1;
      setsigne(p1, -signe(p1)); return y;

    case t_INTMOD: case t_PADIC: err(typeer,"gasin");
    default:
      av = avma; if (!(y = _toser(x))) break;
      if (gcmp0(y)) return gcopy(y);
      /* lg(y) > 2*/
      if (valp(y) < 0) err(negexper,"gasin");
      p1 = gdiv(derivser(y), gsqrt(gsubsg(1,gsqr(y)),prec));
      a = integ(p1,varn(y));
      if (!valp(y)) a = gadd(a, gasin((GEN)y[2],prec));
      return gerepileupto(av, a);
  }
  return transc(gasin,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                             ARCCOSINE                          **/
/**                                                                **/
/********************************************************************/
static GEN
acos0(long e) {
  long l = e >> TWOPOTBITS_IN_LONG; if (l >= 0) l = -1;
  return Pi2n(-1, 2-l);
}

/* |x| < 1, x != 0 */
static GEN
mpacos(GEN x)
{
  long l = lg(x);
  GEN y = cgetr(l);
  pari_sp av = avma;
  affrr( subrr(Pi2n(-1,l), mpasin(x)), y );
  avma = av; return y;
}

GEN
gacos(GEN x, long prec)
{
  long l, sx;
  pari_sp av;
  GEN a, y, p1;

  switch(typ(x))
  {
    case t_REAL: sx = signe(x);
      if (!sx) return acos0(expo(x));
      if (absrnz_egal1(x)) /* |x| = 1 */
        return sx > 0? realzero_bit( -(bit_accuracy(lg(x))>>1) ) : mppi(lg(x));
      if (expo(x) < 0) return mpacos(x);

      y = cgetg(3,t_COMPLEX); p1 = mpach(x, 1);
      if (sx < 0) y[1] = lmppi(lg(x));
      else {
	y[1] = zero;
        setsigne(p1,-signe(p1));
      }
      y[2] = (long)p1; return y;

    case t_COMPLEX: y = gach(x,prec);
      l = y[1]; y[1] = y[2]; y[2] = l;
      setsigne(y[2], -signe(y[2])); return y;

    case t_INTMOD: case t_PADIC: err(typeer,"gacos");
    case t_SER:
      av = avma; if (!(y = _toser(x))) break;
      if (valp(y) < 0) err(negexper,"gacos");
      if (lg(y) > 2)
      {
	p1 = integ(gdiv(derivser(y), gsqrt(gsubsg(1,gsqr(y)),prec)), varn(y));
	if (gcmp1((GEN)y[2]) && !valp(y)) /*y = 1+O(y^k), k>=1*/
	  return gerepileupto(av, gneg(p1));
      }
      else p1 = y;
      a = (lg(y)==2 || valp(y))? Pi2n(-1, prec): gacos((GEN)y[2],prec);
      return gerepileupto(av, gsub(a,p1));
  }
  return transc(gacos,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                            ARGUMENT                            **/
/**                                                                **/
/********************************************************************/

/* we know that x and y are not both 0 */
static GEN
mparg(GEN x, GEN y)
{
  long prec, sx = signe(x), sy = signe(y);
  GEN z;

  if (!sy)
  {
    if (sx > 0) return realzero_bit(expo(y) - expo(x));
    return mppi(lg(x));
  }
  prec = lg(y); if (prec < lg(x)) prec = lg(x);
  if (!sx)
  {
    z = Pi2n(-1, prec); if (sy < 0) setsigne(z,-1);
    return z;
  }

  if (expo(x)-expo(y) > -2)
  {
    z = mpatan(divrr(y,x)); if (sx > 0) return z;
    return addrr_sign(z, signe(z), mppi(prec), sy);
  }
  z = mpatan(divrr(x,y));
  return addrr_sign(z, -signe(z), Pi2n(-1, prec), sy);
}

static GEN
rfix(GEN x,long prec)
{
  switch(typ(x))
  {
    case t_INT: return itor(x, prec);
    case t_FRAC: return rdivii((GEN)x[1],(GEN)x[2], prec);
  }
  return x;
}

static GEN
sarg(GEN x, GEN y, long prec)
{
  pari_sp av = avma;
  x = rfix(x,prec);
  y = rfix(y,prec); return gerepileuptoleaf(av, mparg(x,y));
}

GEN
garg(GEN x, long prec)
{
  long tx = typ(x);
  pari_sp av;

  if (gcmp0(x)) err(talker,"zero argument in garg");
  switch(tx)
  {
    case t_REAL: prec = lg(x); /* fall through */
    case t_INT: case t_FRAC:
      return (gsigne(x)>0)? realzero(prec): mppi(prec);

    case t_QUAD:
      av = avma;
      return gerepileuptoleaf(av, garg(quadtoc(x, prec), prec));

    case t_COMPLEX:
      return sarg((GEN)x[1],(GEN)x[2],prec);

    case t_VEC: case t_COL: case t_MAT:
      return transc(garg,x,prec);
  }
  err(typeer,"garg");
  return NULL; /* not reached */
}

/********************************************************************/
/**                                                                **/
/**                      HYPERBOLIC COSINE                         **/
/**                                                                **/
/********************************************************************/

static GEN
mpch(GEN x)
{
  pari_sp av;
  GEN y, z;

  if (gcmp0(x)) { /* 1 + x */
    long e = expo(x);
    if (e > 0) return realzero_bit(e);
    return realun(3 + ((-e)>>TWOPOTBITS_IN_LONG));
  }
  y = cgetr(lg(x)); av = avma;
  z = mpexp(x); z = addrr(z, ginv(z));
  setexpo(z, expo(z)-1);
  affrr(z, y); avma = av; return y;
}

GEN
gch(GEN x, long prec)
{
  pari_sp av;
  GEN y, p1;

  switch(typ(x))
  {
    case t_REAL: return mpch(x);
    case t_COMPLEX:
      av = avma; p1 = gexp(x,prec); p1 = gadd(p1, ginv(p1));
      return gerepileupto(av, gmul2n(p1,-1));
    case t_INTMOD: case t_PADIC: err(typeer,"gch");
    default:
      av = avma; if (!(y = _toser(x))) break;
      if (gcmp0(y) && valp(y) == 0) return gcopy(y);
      p1 = gexp(y,prec); p1 = gadd(p1, ginv(p1));
      return gerepileupto(av, gmul2n(p1,-1));
  }
  return transc(gch,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                       HYPERBOLIC SINE                          **/
/**                                                                **/
/********************************************************************/

static GEN
mpsh(GEN x)
{
  pari_sp av;
  GEN y,p1;

  if (!signe(x)) return realzero_bit(expo(x));
  y = cgetr(lg(x)); av = avma;
  p1 = mpexp(x); p1 = addrr(p1, divsr(-1,p1));
  setexpo(p1, expo(p1)-1);
  affrr(p1, y); avma = av; return y;
}

GEN
gsh(GEN x, long prec)
{
  pari_sp av;
  GEN y, p1;

  switch(typ(x))
  {
    case t_REAL: return mpsh(x);
    case t_COMPLEX:
      av = avma; p1 = gexp(x,prec); p1 = gsub(p1, ginv(p1));
      return gerepileupto(av, gmul2n(p1,-1));
    case t_INTMOD: case t_PADIC: err(typeer,"gsh");
    default:
      av = avma; if (!(y = _toser(x))) break;
      if (gcmp0(y) && valp(y) == 0) return gcopy(y);
      p1 = gexp(y, prec); p1 = gsub(p1, ginv(p1));
      return gerepileupto(av, gmul2n(p1,-1));
  }
  return transc(gsh,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                      HYPERBOLIC TANGENT                        **/
/**                                                                **/
/********************************************************************/

static GEN
mpth(GEN x)
{
  long l;
  pari_sp av;
  GEN y, p1;

  if (!signe(x)) return realzero_bit(expo(x));
  l = lg(x); y = cgetr(l); av = avma;
  p1 = mpexp1(gmul2n(x,1)); /* exp(2x) - 1 */
  affrr(divrr(p1,addsr(2,p1)), y); avma = av; return y;
}

GEN
gth(GEN x, long prec)
{
  pari_sp av, tetpil;
  GEN y, p1;

  switch(typ(x))
  {
    case t_REAL: return mpth(x);
    case t_COMPLEX:
      av=avma; p1=gexp(gmul2n(x,1),prec);
      p1=gdivsg(-2,gaddgs(p1,1)); tetpil=avma;
      return gerepile(av,tetpil,gaddsg(1,p1));
    case t_INTMOD: case t_PADIC: err(typeer,"gth");
    default:
      av = avma; if (!(y = _toser(x))) break;
      if (gcmp0(y)) return gcopy(y);
      p1 = gexp(gmul2n(y, 1),prec);
      return gerepileupto(av, gdiv(gsubgs(p1,1), gaddgs(p1,1)));
  }
  return transc(gth,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                     ARG-HYPERBOLIC SINE                        **/
/**                                                                **/
/********************************************************************/

/* x is non-zero */
static GEN
mpash(GEN x)
{
  long s = signe(x);
  GEN z, y = cgetr(lg(x));
  pari_sp av = avma;

  z = (s<0)? negr(x): x;
  z = mplog( addrr(z, sqrtr( addrs(mulrr(z,z), 1) )) );
  if (s<0) setsigne(z, -signe(z));
  affrr(z,y); avma = av; return y;
}

GEN
gash(GEN x, long prec)
{
  long sx, sy, sz;
  pari_sp av;
  GEN a, y, p1;

  if (gcmp0(x)) return gcopy(x);
  switch(typ(x))
  {
    case t_REAL:
      return mpash(x);

    case t_COMPLEX: av = avma; 
      p1 = gadd(x, gsqrt(gaddsg(1,gsqr(x)), prec));
      y = glog(p1,prec);
      sz = gsigne((GEN)y[1]);
      sx = gsigne((GEN)p1[1]);
      sy = gsigne((GEN)p1[2]);
      if (sx > 0 || (!sx && sy*sz<=0)) return gerepileupto(av, y);

      p1 = mppi(prec); if (sy<0) setsigne(p1,-1);
      return gerepileupto(av, gadd(gneg_i(y), pureimag(p1)));
    case t_INTMOD: case t_PADIC: err(typeer,"gash");
    default:
      av = avma; if (!(y = _toser(x))) break;
      if (gcmp0(y)) return gcopy(y);
      if (valp(y) < 0) err(negexper,"gash");

      p1 = gdiv(derivser(y), gsqrt(gaddsg(1,gsqr(y)),prec));
      a = integ(p1,varn(y));
      if (!valp(y)) a = gadd(a, gash((GEN)y[2],prec));
      return gerepileupto(av, a);
  }
  return transc(gash,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                     ARG-HYPERBOLIC COSINE                      **/
/**                                                                **/
/********************************************************************/

/* s = +/- 1, return ach(s * x) */
static GEN
mpach(GEN x, long s)
{
  long l = lg(x);
  GEN z, y = cgetr(l);
  pari_sp av = avma;

  if (s != signe(x)) { x = rcopy(x); setsigne(x, s); }
  z = mplog( addrr(x, sqrtr( subrs(mulrr(x,x), 1) )) );
  affrr(z,y); avma = av; return y;
}

GEN
gach(GEN x, long prec)
{
  pari_sp av;
  GEN a, y, p1;
  long v;

  switch(typ(x))
  {
    case t_REAL:
      if (signe(x) == 0) { y=cgetimag(); y[2]=(long)acos0(expo(x)); return y; }
      if (signe(x) > 0 && expo(x) >= 0) return mpach(x, 1); /* x >= 1 */
      /* -1 < x < 1 */
      if (expo(x) < 0) { y = cgetimag(); y[2] = (long)mpacos(x); return y; }
      /* x <= -1 */
      if (absrnz_egal1(x)) { y = cgetimag(); y[2] = lmppi(lg(x)); return y; }
      y = cgetg(3,t_COMPLEX);
      av = avma; p1 = mpach(x, -signe(x));
      setsigne(p1, -signe(p1));
      y[1] = (long)p1;
      y[2] = lmppi(lg(x)); return y;

    case t_COMPLEX:
      av = avma; 
      p1 = gadd(x, gsqrt(gaddsg(-1,gsqr(x)), prec)); /* x + sqrt(x^2-1) */
      y = glog(p1,prec); if (signe(y[2]) < 0) y = gneg(y);
      return gerepileupto(av, y);

    case t_INTMOD: case t_PADIC: err(typeer,"gach");

    default:
      av = avma; if (!(y = _toser(x))) break;
      v = valp(y);
      if (v < 0) err(negexper,"gach");
      if (gcmp0(y))
      {
        if (!v) return gcopy(y);
        return gerepileupto(av, gadd(y, PiI2n(-1, prec)));
      }
      p1 = gdiv(derivser(y), gsqrt(gsubgs(gsqr(y),1),prec));
      a = integ(p1, varn(y));
      if (v)
        p1 = PiI2n(-1, prec); /* I Pi/2 */
      else
      {
        p1 = (GEN)y[2]; if (gcmp1(p1)) return gerepileupto(av,a);
        p1 = gach(p1, prec);
      }
      return gerepileupto(av, gadd(p1,a));
  }
  return transc(gach,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                     ARG-HYPERBOLIC TANGENT                     **/
/**                                                                **/
/********************************************************************/

/* |x| < 1, x != 0 */
static GEN
mpath(GEN x)
{
  GEN z, y = cgetr(lg(x));
  pari_sp av = avma;

  z = mplog( addrs(divsr(2,subsr(1,x)), -1) ); setexpo(z, expo(z)-1);
  affrr(z, y); avma = av; return y;
}

GEN
gath(GEN x, long prec)
{
  pari_sp av;
  GEN a, y, p1;

  switch(typ(x))
  {
    case t_REAL:
      if (!signe(x)) return realzero_bit(expo(x));
      if (expo(x) < 0) return mpath(x);

      y = cgetg(3,t_COMPLEX);
      av = avma; 
      p1 = mplog( addrs(divsr(2,addsr(-1,x)),1) );
      setexpo(p1, expo(p1)-1);
      y[1]=(long)gerepileuptoleaf(av, p1);
      y[2]=(long)Pi2n(-1, lg(x)); return y;

    case t_COMPLEX:
      av = avma; p1 = glog( gaddgs(gdivsg(2,gsubsg(1,x)),-1), prec );
      return gerepileupto(av, gmul2n(p1,-1));

    case t_INTMOD: case t_PADIC: err(typeer,"gath");
    default:
      av = avma; if (!(y = _toser(x))) break;
      if (valp(y) < 0) err(negexper,"gath");
      p1 = gdiv(derivser(y), gsubsg(1,gsqr(y)));
      a = integ(p1, varn(y));
      if (!valp(y)) a = gadd(a, gath((GEN)y[2],prec));
      return gerepileupto(av, a);
  }
  return transc(gath,x,prec);
}
/********************************************************************/
/**                                                                **/
/**               CACHE BERNOULLI NUMBERS B_2k                     **/
/**                                                                **/
/********************************************************************/
/* is B_{2k} precomputed at precision >= prec ? */
int
OK_bern(long k, long prec)
{
  return (bernzone && bernzone[1] >= k && bernzone[2] >= prec);
}

#define BERN(i)       (B + 3 + (i)*B[2])
#define set_bern(c0, i, B) STMT_START { \
  *(BERN(i)) = c0; affrr(B, BERN(i)); } STMT_END
/* compute B_0,B_2,...,B_2*nb */
void
mpbern(long nb, long prec)
{
  long i, l, c0;
  pari_sp av;
  GEN B;
  pari_timer T;

  prec++; /* compute one more word of accuracy than required */
  if (OK_bern(nb, prec)) return;
  if (nb < 0) nb = 0;
  l = 3 + prec*(nb+1);
  B = newbloc(l);
  B[0] = evallg(l);
  B[1] = nb;
  B[2] = prec;
  av = avma;

  c0 = evaltyp(t_REAL) | evallg(prec);
  *(BERN(0)) = c0; affsr(1, BERN(0));
  if (bernzone && bernzone[2] >= prec)
  { /* don't recompute known Bernoulli */
    for (i = 1; i <= bernzone[1]; i++) set_bern(c0, i, bern(i));
  }
  else i = 1;
  if (DEBUGLEVEL) {
    fprintferr("caching Bernoulli numbers 2*%ld to 2*%ld, prec = %ld\n",
               i,nb,prec);
    TIMERstart(&T);
  }

  if (i == 1 && nb > 0)
  {
    set_bern(c0, 1, divrs(realun(prec), 6)); /* B2 = 1/6 */
    i = 2;
  }
  for (   ; i <= nb; i++, avma = av)
  { /* i > 1 */
    long n = 8, m = 5, d1 = i-1, d2 = 2*i-3;
    GEN S = BERN(d1);

    for (;;)
    {
      S = divrs(mulrs(S, n*m), d1*d2);
      if (d1 == 1) break;
      n += 4; m += 2; d1--; d2 -= 2;
      S = addrr(BERN(d1), S);
      if ((d1 & 127) == 0) { set_bern(c0, i, S); S = BERN(i); avma = av; }
    }
    S = divrs(subsr(2*i, S), 2*i+1);
    setexpo(S, expo(S) - 2*i);
    set_bern(c0, i, S); /* S = B_2i */
  }
  if (DEBUGLEVEL) msgTIMER(&T, "Bernoulli");
  if (bernzone) gunclone(bernzone);
  avma = av; bernzone = B;
}
#undef BERN

GEN
bernreal(long n, long prec)
{
  GEN B;

  if (n==1) { B = stor(-1, prec); setexpo(B,-1); return B; }
  if (n<0 || n&1) return gzero;
  n >>= 1; mpbern(n+1,prec); B=cgetr(prec);
  affrr(bern(n),B); return B;
}

#if 0
/* k > 0 */
static GEN
bernfracspec(long k)
{
  ulong n, K = k+1;
  pari_sp av, lim;
  GEN s, c, N, b;

  c = N = utoi(K); s = gun; b = gzero;
  av = avma; lim = stack_lim(av,2);
  for (n=2; ; n++) /* n <= k+1 */
  {
    c = diviiexact(muliu(c,k+2-n), utoi(n));
    if (n & 1) setsigne(c, 1); else setsigne(c, -1);
    /* c = (-1)^(n-1) binomial(k+1, n),  s = 1^k + ... + (n-1)^k */

    b = gadd(b, gdivgs(mulii(c,s), n));
    if (n == K) return gerepileupto(av, b);

    N[2] = (long)n; s = addii(s, gpowgs(N,k));
    if (low_stack(lim, stack_lim(av,2)))
    {
      if (DEBUGMEM>1) err(warnmem,"bernfrac");
      gerepileall(av,3, &c,&b,&s);
    }
  }
}
#endif
extern GEN bernfrac_using_zeta(long n);

static GEN
B2(void){ GEN z = cgetg(3, t_FRAC);
  z[1] = un; z[2] = lutoi(6UL);
  return z;
}
static GEN
B4(void) { GEN z = cgetg(3, t_FRAC);
  z[1] = lstoi(-1); z[2] = lutoi(30UL);
  return z;
}

GEN
bernfrac(long k)
{
  if (!k) return gun;
  if (k == 1) return gneg(ghalf);
  if (k < 0 || k & 1) return gzero;
  if (k == 2) return B2();
  if (k == 4) return B4();
  return bernfrac_using_zeta(k);
}

/* mpbern as exact fractions */
static GEN
bernvec_old(long nb)
{
  long n, i;
  GEN y;

  if (nb < 0) return cgetg(1, t_VEC);
  if (nb > 46340 && BITS_IN_LONG == 32) err(impl, "bernvec for n > 46340");

  y = cgetg(nb+2, t_VEC); y[1] = un;
  for (n = 1; n <= nb; n++)
  { /* compute y[n+1] = B_{2n} */
    pari_sp av = avma;
    GEN b = gmul2n(stoi(1-2*n), -1); /* 1 + (2n+1)B_1 = (1-2n) /2 */
    GEN c = gun;
    ulong u1 = 2*n + 1, u2 = n, d1 = 1, d2 = 1;

    for (i = 1; i < n; i++)
    {
      c = diviiexact(muliu(c, u1*u2), utoi(d1*d2)); /* = binomial(2n+1, 2*i) */
      b = gadd(b, gmul(c, (GEN)y[i+1]));
      u1 -= 2; u2--; d1++; d2 += 2;
    }
    y[n+1] = lpileupto(av, gdivgs(b, -(1+2*n)));
  }
  return y;
}
GEN
bernvec(long nb)
{
  GEN y = cgetg(nb+2, t_VEC), z = y + 1;
  long i;
  if (nb < 20) return bernvec_old(nb);
  for (i = nb; i > 2; i--) z[i] = (long)bernfrac_using_zeta(i << 1);
  y[3] = (long)B4();
  y[2] = (long)B2();
  y[1] = un; return y;
}

/********************************************************************/
/**                                                                **/
/**                         EULER'S GAMMA                          **/
/**                                                                **/
/********************************************************************/

/* x / (i*(i+1)) */
GEN
divrsns(GEN x, long i)
{
#ifdef LONG_IS_64BIT
  if (i < 3037000500) /* i(i+1) < 2^63 */
#else
  if (i < 46341) /* i(i+1) < 2^31 */
#endif
    return divrs(x, i*(i+1));
  else
    return divrs(divrs(x, i), i+1);
}
/* x / (i*(i+1)) */
GEN
divgsns(GEN x, long i)
{
#ifdef LONG_IS_64BIT
  if (i < 3037000500) /* i(i+1) < 2^63 */
#else
  if (i < 46341) /* i(i+1) < 2^31 */
#endif
    return gdivgs(x, i*(i+1));
  else
    return gdivgs(gdivgs(x, i), i+1);
}

/* arg(s+it) */
double
darg(double s, double t)
{
  double x;
  if (!t) return (s>0)? 0.: PI;
  if (!s) return (t>0)? PI/2: -PI/2;
  x = atan(t/s);
  return (s>0)? x
              : ((t>0)? x+PI : x-PI);
}

void
dcxlog(double s, double t, double *a, double *b)
{
  *a = log(s*s + t*t) / 2; /* log |s| = Re(log(s)) */
  *b = darg(s,t);          /* Im(log(s)) */
}

double
dabs(double s, double t) { return sqrt( s*s + t*t ); }
double
dnorm(double s, double t) { return s*s + t*t; }

GEN
trans_fix_arg(long *prec, GEN *s0, GEN *sig, pari_sp *av, GEN *res)
{
  GEN s, p1;
  long l;
  if (typ(*s0)==t_COMPLEX && gcmp0((GEN)(*s0)[2])) *s0 = (GEN)(*s0)[1];
  s = *s0;
  l = precision(s); if (!l) l = *prec;

  if (typ(s) == t_COMPLEX)
  { /* s = sig + i t */
    *res = cgetc(l); *av = avma;
    p1 = cgetc(l+1); gaffect(s,p1);
    s = p1; *sig = (GEN)s[1];
  }
  else /* real number */
  {
    *res = cgetr(l); *av = avma;
    p1 = cgetr(l+1); gaffect(s,p1);
    *sig = s = p1;
  }
  if (typ(s)==t_REAL)
  {
    p1 = floorr(s);
    if (gcmp0(subri(s,p1))) *s0 = p1;
  }
  *prec = l; return s;
}

#if 0
/* x, z t_REAL. Compute unique x in ]-z,z] congruent to x mod 2z */
static GEN
red_mod_2z(GEN x, GEN z)
{
  GEN Z = gmul2n(z, 1), d = subrr(z, x);
  /* require little accuracy */
  if (!signe(d)) return x;
  setlg(d, 3 + ((expo(d) - expo(Z)) >> TWOPOTBITS_IN_LONG));
  return addrr(mulir(floorr(divrr(d, Z)), Z), x);
}
#endif

/* update lg(z) before affrr(y, z)  [ to cater for precision loss ]*/
void
rfixlg(GEN z, GEN y) {
  long ly = lg(y), lz = lg(z);
  if (ly < lz)
  {
    setlg(z, ly);
    stackdummy(z + ly, lz - ly - 1);
  }
}

static GEN
cxgamma(GEN s0, int dolog, long prec)
{
  GEN s, u, a, y, res, tes, sig, invn2, p1, nnx, pi, pi2, sqrtpi2;
  long i, lim, nn;
  pari_sp av, av2, avlim;
  int funeq = 0;

  if (DEBUGLEVEL) (void)timer2();
  s = trans_fix_arg(&prec,&s0,&sig,&av,&res);

  if (signe(sig) <= 0 || expo(sig) < -1)
  {
    if (typ(s) == t_COMPLEX && gexpo((GEN)s[2]) <= 16) funeq = 1;
  }
  /* s <--> 1-s */
  if (funeq) { s = gsub(gun, s); sig = real_i(s); }

  { /* find "optimal" parameters [lim, nn] */
    double ssig = rtodbl(sig);
    double st = rtodbl(imag_i(s));
    double la, l,l2,u,v, rlogs, ilogs;

    dcxlog(ssig,st, &rlogs,&ilogs);
    /* Re (s - 1/2) log(s) */
    u = (ssig - 0.5)*rlogs - st * ilogs;
    /* Im (s - 1/2) log(s) */
    v = (ssig - 0.5)*ilogs + st * rlogs;
    /* l2 = | (s - 1/2) log(s) - s + log(2Pi)/2 |^2 ~ |lngamma(s))|^2 */
    u = u - ssig + log(2.*PI)/2;
    v = v - st;
    l2 = u*u + v*v;
    if (l2 < 0.000001) l2 = 0.000001;
    l = (pariC2*(prec-2) - log(l2)/2) / 2.;
    if (l < 0) l = 0.;

    la = 3.; /* FIXME: heuristic... */
    if (st > 1 && l > 0)
    {
      double t = st * PI / l;
      la = t * log(t);
      if (la < 3) la = 3.;
      if (la > 150) la = t;
    }
    lim = (long)ceil(l / (1.+ log(la)));
    if (lim == 0) lim = 1;

    u = (lim-0.5) * la / PI;
    l2 = u*u - st*st;
    if (l2 > 0)
    {
      nn = (long)ceil(sqrt(l2) - ssig);
      if (nn < 1) nn = 1;
    }
    else
      nn = 1;
#if 0
    {/* same: old method */
      long e = gexpo(s);
      double beta;
      if (e > 1000)
      {
        nn = 0;
        beta = log(pariK4 / (prec-2)) / LOG2 + e;
        if (beta > 1.) beta += log(beta)/LOG2;
        lim = (long)((bit_accuracy(prec)>>1)/beta + 1);
      }
      else
      {
        double alpha = sqrt( dnorm(ssig, st) );
        beta = ((bit_accuracy(prec)>>1) * LOG2 / PI) - alpha;
        if (beta >= 0) nn = (long)(1+pariK2*beta); else nn = 0;
        if (nn)
          lim = (long)(1+PI*(alpha+nn));
        else
        {
          beta = log( pariK4 * alpha / (prec-2) ) / LOG2;
          if (beta > 1.) beta += log(beta)/LOG2;
          lim = (long)((bit_accuracy(prec)>>1)/beta + 1);
        }
      }
      nn++;
    }
#endif
    if (DEBUGLEVEL) fprintferr("lim, nn: [%ld, %ld], la = %lf\n",lim,nn,la);
  }
  prec++;

  av2 = avma; avlim = stack_lim(av2,3);
  y = s;
  if (typ(s0) == t_INT)
  {
    if (is_bigint(s0))
    {
      for (i=1; i < nn; i++)
      {
        y = mulri(y, addis(s0, i));
        if (low_stack(avlim,stack_lim(av2,3)))
        {
          if(DEBUGMEM>1) err(warnmem,"gamma");
          y = gerepileuptoleaf(av2, y);
        }
      }
    }
    else
    {
      long ss = itos(s0);
      for (i=1; i < nn; i++)
      {
        y = mulrs(y, ss + i);
        if (low_stack(avlim,stack_lim(av2,3)))
        {
          if(DEBUGMEM>1) err(warnmem,"gamma");
          y = gerepileuptoleaf(av2, y);
        }
      }
    }
    if (dolog) y = mplog(y);
  }
  else
    if (!dolog) /* Compute lngamma mod 2 I Pi */
    {
      for (i=1; i < nn; i++)
      {
        y = gmul(y, gaddgs(s,i));
        if (low_stack(avlim,stack_lim(av2,3)))
        {
          if(DEBUGMEM>1) err(warnmem,"gamma");
          y = gerepileupto(av2, y);
        }
      }
    }
    else /* Be careful with the imaginary part */
    {
      y = glog(y, prec);
      for (i=1; i < nn; i++)
      {
        y = gadd(y, glog(gaddgs(s,i), prec));
        if (low_stack(avlim,stack_lim(av2,3)))
        {
          if(DEBUGMEM>1) err(warnmem,"gamma");
          y = gerepileupto(av2, y);
        }
      }
    }

  nnx = gaddgs(s, nn);
  if (DEBUGLEVEL) msgtimer("product from 0 to N-1");

  a = ginv(nnx); invn2 = gsqr(a);
  tes = divrsns(bernreal(2*lim,prec), 2*lim-1); /* B2l / (2l-1) 2l*/
  if (DEBUGLEVEL) msgtimer("Bernoullis");
  for (i = 2*lim-2; i > 1; i -= 2)
  {
    u = divrsns(bernreal(i,prec), i-1); /* Bi / i(i-1) */
    tes = gadd(u, gmul(invn2,tes));
  }
  if (DEBUGLEVEL) msgtimer("Bernoulli sum");

  p1 = gsub(gmul(gsub(nnx, ghalf), glog(nnx,prec)), nnx);
  p1 = gadd(p1, gmul(tes, a));

  pi = mppi(prec); pi2 = gmul2n(pi, 1); sqrtpi2 = sqrtr(pi2);

  if (!dolog)
    {
      if (funeq)
      { /* y --> y Pi/(sin(Pi s) * sqrt(2Pi)) */
        y = gmul2n(gdiv(gmul(sqrtpi2,y), gsin(gmul(s,pi), prec)), -1);
        p1 = gneg(p1);
      }
      else /* y --> sqrt(2Pi) / y */
	y = gdiv(sqrtpi2, y);
    }
  else
    {
      if (funeq)
      { /* 2 Pi ceil( (2Re(s) - 3)/4 ) */
        GEN p2 = mulri(pi2, gceil(gmul2n(subrs(gmul2n(sig,1), 3), -2)));
        /* y --> y + log Pi - log sqrt(2Pi) - log sin(Pi s) */
        y = gsub(gadd(y, gmul2n(mplog(Pi2n(-1,prec)), -1)),
                 glog(gsin(gmul(s,pi), prec), prec));
        if (gsigne(imag_i(s)) < 0) setsigne(p2, -signe(p2));
        y[2] = (long)addrr((GEN)y[2], p2);
        p1 = gneg(p1);
      }
      else /* y --> sqrt(2Pi) / y */
	y = gsub(glog(sqrtpi2, prec), y);
    }

  if (dolog)
  {
    y = gadd(p1, y);
    if (typ(y) == t_COMPLEX)
    {
      if (typ(res) == t_REAL) return gerepilecopy(av, y);
      rfixlg((GEN)res[2], (GEN)y[2]);
    }
    else rfixlg(res, y);
  }
  else
    y = gmul(gexp(p1, prec), y);
  gaffect(y, res); avma = av; return res;
}

/* Gamma((m+1) / 2) */
static GEN
gammahs(long m, long prec)
{
  GEN y = cgetr(prec), z;
  pari_sp av = avma;
  long ma = labs(m);

  if (ma > 962353) err(talker, "argument too large in ggamma");
  if (ma > 200 + 50*(prec-2)) /* heuristic */
  {
    z = stor(m + 1, prec); setexpo(z, expo(z)-1);
    affrr(cxgamma(z,0,prec), y);
    avma = av; return y;
  }
  z = sqrtr( mppi(prec) );
  if (m)
  {
    GEN p1 = seq_umul(ma/2 + 1, ma);
    long v = vali(p1);
    p1 = shifti(p1, -v); v -= ma;
    if (m >= 0) z = mulri(z,p1);
    else
    {
      z = divri(z,p1); v = -v;
      if ((m&3) == 2) setsigne(z,-1);
    }
    setexpo(z, expo(z) + v);
  }
  affrr(z, y); avma = av; return y;
}

GEN
ggamma(GEN x, long prec)
{
  pari_sp av;
  long m;
  GEN y, z;

  switch(typ(x))
  {
    case t_INT:
      if (signe(x) <= 0) err(talker,"non-positive integer argument in ggamma");
      if (cmpis(x,481177) > 0) err(talker,"argument too large in ggamma");
      return mpfactr(itos(x) - 1, prec);

    case t_REAL: case t_COMPLEX:
      return cxgamma(x, 0, prec);

    case t_FRAC:
      if (!egalii((GEN)x[2], gdeux)) break;
      z = (GEN)x[1]; /* true argument is z/2 */
      if (is_bigint(z) || labs(m = itos(z)) > 962354)
      {
        err(talker, "argument too large in ggamma");
        return NULL; /* not reached */
      }
      return gammahs(m-1, prec);

    case t_PADIC: err(impl,"p-adic gamma function");
    case t_INTMOD: err(typeer,"ggamma");
    default:
      av = avma; if (!(y = _toser(x))) break;
      return gerepileupto(av, gexp(glngamma(y,prec),prec));
  }
  return transc(ggamma,x,prec);
}

GEN
mpfactr(long n, long prec)
{
  GEN f = cgetr(prec);
  pari_sp av = avma;

  if (n+1 > 350 + 70*(prec-2)) /* heuristic */
    affrr(cxgamma(stor(n+1, prec), 0, prec), f);
  else
    affir(mpfact(n), f);
  avma = av; return f;
}

GEN
glngamma(GEN x, long prec)
{
  long i, n;
  pari_sp av;
  GEN a, y, p1;

  switch(typ(x))
  {
    case t_INT:
      if (signe(x) <= 0) err(talker,"non-positive integer argument in glngamma");
      if (cmpis(x,200 + 50*(prec-2)) > 0) /* heuristic */
	return cxgamma(x, 1, prec);
      y = cgetr(prec); av = avma;
      p1 = mplog(itor(mpfact(itos(x) - 1), prec) );
      affrr(p1, y); avma = av; return y;

    case t_REAL: case t_COMPLEX:
      return cxgamma(x, 1, prec);

    default:
      av = avma; if (!(y = _toser(x))) break;
      if (valp(y)) err(negexper,"glngamma");
      p1 = gsubsg(1,y);
      if (!valp(p1)) err(impl,"lngamma around a!=1");
      n = (lg(y)-3) / valp(p1);
      a = zeroser(varn(y), lg(y)-2);
      for (i=n; i>=2; i--) a = gmul(p1, gadd(a, gdivgs(szeta(i, prec),i)));
      a = gadd(a, mpeuler(prec));
      return gerepileupto(av, gmul(a, p1));

    case t_PADIC:  err(impl,"p-adic lngamma function");
    case t_INTMOD: err(typeer,"glngamma");
  }
  return transc(glngamma,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                       GAMMA AT HALF INTEGERS                   **/
/**                                                                **/
/********************************************************************/

static GEN
mpgamd(long x, long prec)
{
  if (labs(x) > 962353) x = 962353; /* too large. Raise error in gammahs */
  return gammahs(x<<1, prec);
}

GEN
ggamd(GEN x, long prec)
{
  pari_sp av, tetpil;

  switch(typ(x))
  {
    case t_INT:
      return mpgamd(itos(x),prec);

    case t_REAL: case t_FRAC: case t_COMPLEX: case t_QUAD:
      av=avma; x = gadd(x,ghalf); tetpil=avma;
      return gerepile(av,tetpil,ggamma(x,prec));

    case t_INTMOD: case t_PADIC: err(typeer,"ggamd");
    case t_SER: err(impl,"gamd of a power series");
  }
  return transc(ggamd,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                               PSI                              **/
/**                                                                **/
/********************************************************************/

GEN
cxpsi(GEN s0, long prec)
{
  pari_sp av, av2;
  GEN sum,z,a,res,tes,in2,sig,s,unr;
  long lim,nn,k;
  const long la = 3;

  if (DEBUGLEVEL>2) (void)timer2();
  s = trans_fix_arg(&prec,&s0,&sig,&av,&res);
  if (signe(sig) <= 0)
  {
    GEN pi = mppi(prec);
    z = gsub(cxpsi(gsub(gun,s), prec), gmul(pi, gcotan(gmul(pi,s), prec)));
    gaffect(z, res); avma = av; return res;
  }

  {
    double ssig = rtodbl(sig);
    double st = rtodbl(imag_i(s));
    double l;
    {
      double rlog, ilog; /* log (s - Euler) */
      dcxlog(ssig - 0.57721566, st, &rlog,&ilog);
      l = dnorm(rlog,ilog);
    }
    if (l < 0.000001) l = 0.000001;
    l = log(l) / 2.;
    lim = 2 + (long)ceil((pariC2*(prec-2) - l) / (2*(1+log((double)la))));
    if (lim < 2) lim = 2;

    l = (2*lim-1)*la / (2.*PI);
    l = l*l - st*st;
    if (l < 0.) l = 0.;
    nn = (long)ceil( sqrt(l) - ssig );
    if (nn < 1) nn = 1;
    if (DEBUGLEVEL>2) fprintferr("lim, nn: [%ld, %ld]\n",lim,nn);
  }
  prec++; unr = realun(prec); /* one extra word of precision */

  a = gdiv(unr, gaddgs(s, nn)); /* 1 / (s+n) */
  av2 = avma; sum = gmul2n(a,-1);
  for (k = 0; k < nn; k++)
  {
    sum = gadd(sum, gdiv(unr, gaddgs(s, k)));
    if ((k & 127) == 0) sum = gerepileupto(av2, sum);
  }
  z = gsub(glog(gaddgs(s, nn), prec), sum);
  if (DEBUGLEVEL>2) msgtimer("sum from 0 to N-1");

  in2 = gsqr(a);
  av2 = avma; tes = divrs(bernreal(2*lim, prec), 2*lim);
  for (k=2*lim-2; k>=2; k-=2)
  {
    tes = gadd(gmul(in2,tes), divrs(bernreal(k, prec), k));
    if ((k & 255) == 0) tes = gerepileupto(av2, tes);
  }
  if (DEBUGLEVEL>2) msgtimer("Bernoulli sum");
  z = gsub(z, gmul(in2,tes));
  gaffect(z, res); avma = av; return res;
}

GEN
gpsi(GEN x, long prec)
{
  switch(typ(x))
  {
    case t_REAL: case t_COMPLEX: return cxpsi(x,prec);
    case t_INTMOD: case t_PADIC: err(typeer,"gpsi");
    case t_SER: err(impl,"psi of power series");
  }
  return transc(gpsi,x,prec);
}
