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

extern GEN seq_umul(ulong a, ulong b);
extern GEN mpsin(GEN x);
static GEN mpach(GEN x);

/********************************************************************/
/**                                                                **/
/**                       FONCTION ARCTG                           **/
/**                                                                **/
/********************************************************************/

static GEN
mpatan(GEN x)
{
  long l, l1, l2, n, m, u, i, lp, e, sx, s;
  pari_sp av0, av;
  double alpha,beta,gama=1.0,delta,fi;
  GEN y,p1,p2,p3,p4,p5,unr;

  sx=signe(x);
  if (!sx) return realzero_bit(expo(x));
  l = lp = lg(x);
  if (sx<0) setsigne(x,1);
  u = cmprs(x,1);
  if (!u)
  {
    y = Pi2n(-2, l+1);
    if (sx < 0)
    {
      setsigne(x,-1);
      setsigne(y,-1);
    }
    return y;
  }

  e = expo(x);
  if (e>0) lp += (e>>TWOPOTBITS_IN_LONG);

  y=cgetr(lp); av0=avma;
  p1=cgetr(l+1); affrr(x,p1); setsigne(x,sx);
  if (u==1) divsrz(1,p1,p1);
  e = expo(p1);
  if (e<-100)
    alpha = log(PI)-e*LOG2;
  else
  {
    alpha = rtodbl(p1);
    alpha = log(PI/atan(alpha));
  }
  beta = (double)(bit_accuracy(l)>>1) * LOG2;
  delta=LOG2+beta-alpha/2;
  if (delta<=0) { n=1; m=0; }
  else
  {
    fi=alpha-2*LOG2;
    if (delta>=gama*fi*fi/LOG2)
    {
      n=(long)(1+sqrt(gama*delta/LOG2));
      m=(long)(1+sqrt(delta/(gama*LOG2))-fi/LOG2);
    }
    else
    {
      n=(long)(1+beta/fi); m=0;
    }
  }
  l2=l+1+(m>>TWOPOTBITS_IN_LONG);
  p2=cgetr(l2); p3=cgetr(l2);
  affrr(p1,p2); av=avma;
  for (i=1; i<=m; i++)
  {
    p5 = mulrr(p2,p2); setlg(p5,l2);
    p5 = addsr(1,p5); setlg(p5,l2);
    p5 = mpsqrt(p5);
    p5 = addsr(1,p5); setlg(p5,l2);
    divrrz(p2,p5,p2); avma=av;
  }
  mulrrz(p2,p2,p3); l1=4;
  unr=realun(l2); setlg(unr,4);
  p4=cgetr(l2); setlg(p4,4);
  divrsz(unr,2*n+1,p4);

  s=0; e=expo(p3); av=avma;
  for (i=n; i>=1; i--)
  {
    setlg(p3,l1); p5 = mulrr(p4,p3);
    s -= e; l1 += (s>>TWOPOTBITS_IN_LONG);
    if (l1>l2) l1=l2;
    s %= BITS_IN_LONG;
    setlg(unr,l1); p5 = subrr(divrs(unr,2*i-1), p5);
    setlg(p4,l1); affrr(p5,p4); avma=av;
  }
  setlg(p4,l2); p4 = mulrr(p2,p4);
  setexpo(p4, expo(p4)+m);
  if (u==1) p4 = subrr(Pi2n(-1, lp+1), p4);
  if (sx == -1) setsigne(p4,-signe(p4));
  affrr(p4,y); avma=av0; return y;
}

GEN
gatan(GEN x, long prec)
{
  pari_sp av, tetpil;
  GEN a, y, p1;

  switch(typ(x))
  {
    case t_REAL:
      return mpatan(x);

    case t_COMPLEX:
      av=avma; p1=cgetg(3,t_COMPLEX);
      p1[1]=lneg((GEN)x[2]);
      p1[2]=x[1]; tetpil=avma;
      y=gerepile(av,tetpil,gath(p1,prec));
      p1=(GEN)y[1]; y[1]=y[2]; y[2]=(long)p1;
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

void
gatanz(GEN x, GEN y)
{
  long prec = precision(y);
  pari_sp av=avma;

  if (!prec) err(infprecer,"gatanz");
  gaffect(gatan(x,prec),y); avma=av;
}

/********************************************************************/
/**                                                                **/
/**                      FONCTION ARCSINUS                         **/
/**                                                                **/
/********************************************************************/

/* x is non zero |x| <= 1 */
static GEN
mpasin(GEN x)
{
  long l;
  pari_sp av;
  GEN y,p1;

  if (!cmprs(x,1) || !cmpsr(-1,x))
    y = Pi2n(-1, lg(x));
  else
  {
    l = lg(x); y = cgetr(l); av = avma;
    p1 = mpsqrt( subsr(1, mulrr(x,x)) );
    affrr(mpatan(divrr(x,p1)), y); avma = av;
  }
  if (signe(x) < 0) setsigne(y,-1);
  return y;
}

GEN
gasin(GEN x, long prec)
{
  long l, sx;
  pari_sp av, tetpil;
  GEN a, y, p1;

  switch(typ(x))
  {
    case t_REAL: sx = signe(x);
      if (!sx) return realzero_bit(expo(x));
      if (sx < 0) setsigne(x,1);
      if (cmpsr(1,x)>=0) { setsigne(x,sx); return mpasin(x); }

      y = cgetg(3,t_COMPLEX);
      y[1] = (long)Pi2n(-1, lg(x));
      y[2] = lmpach(x);
      if (sx < 0)
      {
        setsigne(y[1],-signe(y[1]));
        setsigne(y[2],-signe(y[2]));
        setsigne(x, sx);
      }
      return y;

    case t_COMPLEX:
      av=avma; p1=cgetg(3,t_COMPLEX);
      p1[1]=lneg((GEN)x[2]);
      p1[2]=x[1]; tetpil=avma;
      y=gerepile(av,tetpil,gash(p1,prec));
      l=y[1]; y[1]=y[2];
      y[2]=l; gnegz((GEN)l,(GEN)l);
      return y;

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

void
gasinz(GEN x, GEN y)
{
  long prec = precision(y);
  pari_sp av=avma;

  if (!prec) err(infprecer,"gasinz");
  gaffect(gasin(x,prec),y); avma=av;
}

/********************************************************************/
/**                                                                **/
/**                      FONCTION ARCCOSINUS                       **/
/**                                                                **/
/********************************************************************/

/* |x|<=1 */
static GEN
mpacos(GEN x)
{
  long l, sx;
  pari_sp av;
  GEN y, p1;

  sx = signe(x);
  if (!sx)
  {
    l = expo(x)>>TWOPOTBITS_IN_LONG; if (l>=0) l = -1;
    return Pi2n(-1, 2-l);
  }
  l = lg(x);
  if (!cmprs(x,1)) return realzero_bit( -(bit_accuracy(l)>>1) );
  if (!cmpsr(-1,x)) return mppi(l);

  y = cgetr(l); av = avma;
  if (expo(x) < 0)
  {
    p1 = mpsqrt( subsr(1, mulrr(x,x)) );
    p1 = mpatan( divrr(x,p1) );
    p1 = subrr(Pi2n(-1,l), p1);
  }
  else
  {
    p1 = sx>0? addsr(1,x): subsr(1,x);
    p1 = mpsqrt( mulrr(p1,subsr(2,p1)) );
    p1 = mpatan( divrr(p1,x) );
    if (sx < 0) p1 = addrr(p1, mppi(l));
  }
  affrr(p1,y); avma = av; return y;
}

GEN
gacos(GEN x, long prec)
{
  long l, sx;
  pari_sp av;
  GEN a, y, p1;

  switch(typ(x))
  {
    case t_REAL: sx=signe(x);
      if (sx<0) setsigne(x,1);
      if (cmprs(x,1)<=0) { setsigne(x,sx); return mpacos(x); }

      y=cgetg(3,t_COMPLEX); y[2]=lmpach(x);
      if (sx<0) y[1]=lmppi(lg(x));
      else
      {
	y[1]=zero; setsigne(y[2],-signe(y[2]));
      }
      setsigne(x,sx); return y;

    case t_COMPLEX:
      y=gach(x,prec);
      l=y[1]; y[1]=y[2]; y[2]=l;
      setsigne(y[2],-signe(y[2])); return y;

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

void
gacosz(GEN x, GEN y)
{
  long prec = precision(y);
  pari_sp av=avma;

  if (!prec) err(infprecer,"gacosz");
  gaffect(gacos(x,prec),y); avma=av;
}

/********************************************************************/
/**                                                                **/
/**                      FONCTION ARGUMENT                         **/
/**                                                                **/
/********************************************************************/

/* we know that x and y are not both 0 */
static GEN
mparg(GEN x, GEN y)
{
  long prec,sx,sy;
  GEN theta,pitemp;

  sx=signe(x); sy=signe(y);
  if (!sy)
  {
    if (sx>0) return realzero_bit(expo(y) - expo(x));
    return mppi(lg(x));
  }
  prec = lg(y); if (prec<lg(x)) prec = lg(x);
  if (!sx)
  {
    theta = Pi2n(-1, prec);
    if (sy<0) setsigne(theta,-1);
    return theta;
  }

  if (expo(x)-expo(y) > -2)
  {
    theta = mpatan(divrr(y,x));
    if (sx>0) return theta;
    pitemp = mppi(prec);
    if (sy>0) return addrr(pitemp,theta);
    return subrr(theta,pitemp);
  }
  theta = mpatan(divrr(x,y));
  pitemp = Pi2n(-1, prec);
  if (sy>0) return subrr(pitemp,theta);
  theta = addrr(pitemp,theta);
  setsigne(theta,-signe(theta)); return theta;
}

static GEN
rfix(GEN x,long prec)
{
  GEN p1;
  switch(typ(x))
  {
    case t_INT: case t_FRAC: case t_FRACN:
      p1=cgetr(prec); gaffect(x,p1); return p1;
  }
  return x;
}

static GEN
sarg(GEN x, GEN y, long prec)
{
  pari_sp av=avma;
  x = rfix(x,prec); y = rfix(y,prec);
  return gerepileupto(av,mparg(x,y));
}

GEN
garg(GEN x, long prec)
{
  GEN p1;
  long tx=typ(x);
  pari_sp av, tetpil;

  if (gcmp0(x)) err(talker,"zero argument in garg");
  switch(tx)
  {
    case t_REAL:
      prec=lg(x); /* fall through */
    case t_INT: case t_FRAC: case t_FRACN:
      return (gsigne(x)>0)? realzero(prec): mppi(prec);

    case t_QUAD:
      av=avma; gaffsg(1,p1=cgetr(prec)); p1=gmul(p1,x);
      tetpil=avma; return gerepile(av,tetpil,garg(p1,prec));

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
  GEN y,p1;

  if (gcmp0(x)) return gaddsg(1,x);

  y = cgetr(lg(x)); av = avma;
  p1 = mpexp(x); p1 = addrr(p1, ginv(p1));
  setexpo(p1, expo(p1)-1);
  affrr(p1, y); avma = av; return y;
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

void
gchz(GEN x, GEN y)
{
  long prec = precision(y);
  pari_sp av=avma;

  if (!prec) err(infprecer,"gchz");
  gaffect(gch(x,prec),y); avma=av;
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
      if (gcmp0(x) && valp(x) == 0) return gcopy(x);
      p1 = gexp(x,prec); p1 = gsub(p1, ginv(p1));
      return gerepileupto(av, gmul2n(p1,-1));
  }
  return transc(gsh,x,prec);
}

void
gshz(GEN x, GEN y)
{
  long prec = precision(y);
  pari_sp av=avma;

  if (!prec) err(infprecer,"gshz");
  gaffect(gsh(x,prec),y); avma=av;
}

/********************************************************************/
/**                                                                **/
/**                 FONCTION TANGENTE HYPERBOLIQUE                 **/
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
  p1 = mpexp1(gmul2n(x,1));
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

void
gthz(GEN x, GEN y)
{
  long prec = precision(y);
  pari_sp av=avma;

  if (!prec) err(infprecer,"gthz");
  gaffect(gth(x,prec),y); avma=av;
}

/********************************************************************/
/**                                                                **/
/**             FONCTION ARGUMENT SINUS HYPERBOLIQUE               **/
/**                                                                **/
/********************************************************************/

/* x is non-zero */
static GEN
mpash(GEN x)
{
  long s=signe(x);
  pari_sp av;
  GEN y,p1;

  y=cgetr(lg(x)); av=avma;
  p1 = (s<0)? negr(x): x;
  p1 = addrr(p1,mpsqrt(addsr(1,mulrr(p1,p1))));
  p1 = mplog(p1); if (s<0) setsigne(p1,-signe(p1));
  affrr(p1,y); avma=av; return y;
}

GEN
gash(GEN x, long prec)
{
  long sx, sy, sz;
  pari_sp av, tetpil;
  GEN a, y, p1;

  if (gcmp0(x)) return gcopy(x);
  switch(typ(x))
  {
    case t_REAL:
      return mpash(x);

    case t_COMPLEX:
      av=avma; p1=gaddsg(1,gsqr(x));
      p1=gadd(x,gsqrt(p1,prec));
      tetpil=avma; y=glog(p1,prec);
      sz=gsigne((GEN)y[1]);
      sx=gsigne((GEN)p1[1]);
      sy=gsigne((GEN)p1[2]);
      if (sx>0 || (!sx && sy*sz<=0)) return gerepile(av,tetpil,y);

      y=gneg_i(y); p1=cgetg(3,t_COMPLEX); p1[1]=zero;
      p1[2]=lmppi(prec); if (sy<0) setsigne(p1[2],-1);
      tetpil=avma;
      return gerepile(av,tetpil,gadd(y,p1));
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

void
gashz(GEN x, GEN y)
{
  long prec = precision(y);
  pari_sp av=avma;

  if (!prec) err(infprecer,"gashz");
  gaffect(gash(x,prec),y); avma=av;
}

/********************************************************************/
/**                                                                **/
/**            FONCTION ARGUMENT COSINUS HYPERBOLIQUE              **/
/**                                                                **/
/********************************************************************/

static GEN
mpach(GEN x)
{
  long l;
  pari_sp av;
  GEN y,p1;

  l=lg(x); y=cgetr(l); av=avma;

  p1=cgetr(l+1); affrr(x,p1);
  p1 = mulrr(p1,p1);
  subrsz(p1,1,p1);
  p1 = mpsqrt(p1);
  p1 = mplog(addrr(x,p1));
  affrr(p1,y); avma=av; return y;
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
      if (gcmpgs(x,1) >= 0) return mpach(x);

      y = cgetg(3,t_COMPLEX);
      if (gcmpgs(x,-1) >= 0)
      {
        y[1] = zero;
	y[2] = lmpacos(x); return y;
      }
      av = avma;
      y[1] = lpileupto(av, gneg(mpach(gneg_i(x))));
      y[2] = lmppi(lg(x)); return y;

    case t_COMPLEX:
      av = avma; p1 = gaddsg(-1,gsqr(x));
      p1 = gadd(x, gsqrt(p1,prec)); /* x + sqrt(x^2-1) */
      y = glog(p1,prec);
      if (signe(y[2]) < 0) y = gneg(y);
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
        p1 = (GEN)y[2];
        if (gcmp1(p1)) return gerepileupto(av,a);
        p1 = gach(p1, prec);
      }
      return gerepileupto(av, gadd(p1,a));
  }
  return transc(gach,x,prec);
}

void
gachz(GEN x, GEN y)
{
  long prec = precision(y);
  pari_sp av=avma;

  if (!prec) err(infprecer,"gachz");
  gaffect(gach(x,prec),y); avma=av;
}

/********************************************************************/
/**                                                                **/
/**           FONCTION ARGUMENT TANGENTE HYPERBOLIQUE              **/
/**                                                                **/
/********************************************************************/

/* |x| < 1 */
static GEN
mpath(GEN x)
{
  pari_sp av;
  GEN y,p1;

  if (!signe(x)) return realzero_bit(expo(x));
  y = cgetr(lg(x)); av = avma;
  p1 = addrs(divsr(2,subsr(1,x)), -1);
  affrr(mplog(p1), y); avma=av;
  setexpo(y, expo(y)-1); return y;
}

GEN
gath(GEN x, long prec)
{
  pari_sp av, tetpil;
  GEN a, y, p1;

  switch(typ(x))
  {
    case t_REAL:
      if (expo(x)<0) return mpath(x);

      av=avma; p1=addrs(divsr(2,addsr(-1,x)),1);
      tetpil=avma; y=cgetg(3,t_COMPLEX);
      p1=mplog(p1); setexpo(p1,expo(p1)-1);
      y[1]=(long)p1;
      y[2]=(long)Pi2n(-1, lg(x));
      return gerepile(av,tetpil,y);

    case t_COMPLEX:
      av=avma;
      p1=gaddgs(gdivsg(2,gsubsg(1,x)),-1);
      p1=glog(p1,prec); tetpil=avma;
      return gerepile(av,tetpil,gmul2n(p1,-1));

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

void
gathz(GEN x, GEN y)
{
  long prec = precision(y);
  pari_sp av=avma;

  if (!prec) err(infprecer,"gathz");
  gaffect(gath(x,prec),y); avma=av;
}

/********************************************************************/
/**                                                                **/
/**               CACHE BERNOULLI NUMBERS B_2k                     **/
/**                                                                **/
/********************************************************************/
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
  if (bernzone && bernzone[1] >= nb && bernzone[2] >= prec) return;
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
/**                      FONCTION GAMMA                            **/
/**                                                                **/
/********************************************************************/

#if 0
static GEN
mpgamma(GEN x)
{
  GEN y,p1,p2,p3,p4,p5,p6,p7,p71,pitemp;
  long l, l1, l2, flag, i, k, e, s, sx, n, p;
  pari_sp av, av1;
  double alpha,beta,dk;

  sx=signe(x); if (!sx) err(gamer2);
  l=lg(x); y=cgetr(l); av=avma;

  l2=l+1; p1=cgetr(l2);
  flag = (expo(x)<-1 || sx<0);
  if (!flag) p2 = x;
  else
  {
    p2=gfrac(x); if (gcmp0(p2)) err(gamer2);
    p2 = subsr(1,x);
  }
  affrr(p2,p1);
  alpha=rtodbl(p1); beta=((bit_accuracy(l)>>1)*LOG2/PI) - alpha;
  if (beta>=0) n=(long)(1 + pariK2*beta); else n=0;
  if (n)
  {
    p = (long)(1 + PI*(alpha+n));
    l2 += n>>TWOPOTBITS_IN_LONG;
    p2 = cgetr(l2); addsrz(n,p1,p2);
  }
  else
  {
    dk = pariK4*alpha/(l-2); beta = log(dk)/LOG2;
    if (beta>1.) beta += log(beta)/LOG2;
    p = (long)((bit_accuracy(l)>>1)/beta + 1);
    p2 = p1;
  }
  mpbern(p,l2); p3=mplog(p2);

  p4 = real2n(-1, l2);
  p6 = subrr(p2,p4); p6 = mulrr(p6,p3);
  p6 = subrr(p6,p2);
  pitemp = mppi(l2); setexpo(pitemp,2);
  p7 = mplog(pitemp); setexpo(pitemp,1);
  setexpo(p7,-1); addrrz(p6,p7,p4);

  affrr(ginv(gsqr(p2)), p3); e=expo(p3);

  p5=cgetr(l2); setlg(p5,4);
  p71=cgetr(l2); p7 = bern(p);
  if (bernzone[2]>4) { setlg(p71,4); affrr(p7,p71); p7=p71; }
  p7 = divrs(p7, 2*p*(2*p-1)); affrr(p7,p5);

  s=0; l1=4; av1=avma;
  for (k=p-1; k>0; k--)
  {
    setlg(p3,l1); p6 = mulrr(p3,p5); p7 = bern(k);
    if (bernzone[2]>l1) { setlg(p71,l1); affrr(p7,p71); p7=p71; }
    p7 = divrs(p7, (2*k)*(2*k-1));
    s -= e; l1 += (s>>TWOPOTBITS_IN_LONG); if (l1>l2) l1=l2;
    s &= (BITS_IN_LONG-1); p7 = addrr(p7,p6);
    setlg(p5,l1); affrr(p7,p5); avma=av1;
  }
  setlg(p5,l2); p6 = divrr(p5,p2);
  p4 = addrr(p4,p6); setlg(p4,l2); p4 = mpexp(p4);
  for (i=1; i<=n; i++)
  {
    addsrz(-1,p2,p2); p4 = divrr(p4,p2);
  }
  if (flag)
  {
    setlg(pitemp,l+1); p1 = mulrr(pitemp,x);
    p4 = mulrr(mpsin(p1), p4); p4 = divrr(pitemp,p4);
  }
  affrr(p4,y); avma=av; return y;
}

static GEN
cxgamma(GEN x, long prec)
{
  GEN y,p1,p2,p3,p4,p5,p6,p7,p71,pitemp;
  long l, l1, l2, flag, i, k, e, s, n, p;
  pari_sp av, av1;
  double alpha,beta,dk;

  if (gcmp0((GEN)x[2])) return ggamma((GEN)x[1],prec);
  l = precision(x); if (!l) l = prec;
  l2 = l+1; y = cgetc(l); av = avma;

  p1 = cgetc(l2);
  flag = (gsigne((GEN)x[1])<=0 || gexpo((GEN)x[1]) < -1);
  p2 = flag? gsub(gun,x): x;
  gaffect(p2,p1);

  alpha = rtodbl(gabs(p1,DEFAULTPREC));
  beta = (bit_accuracy(l)>>1) * LOG2 / PI - alpha;
  if (beta>=0) n=(long)(1 + pariK2*beta); else n=0;
  if (n)
  {
    p = (long)(1+PI*(alpha+n));
    l2 += n>>TWOPOTBITS_IN_LONG;
    p2 = cgetc(l2);
    addsrz(n,(GEN)p1[1],(GEN)p2[1]);
    affrr((GEN)p1[2],   (GEN)p2[2]);
  }
  else
  {
    dk = pariK4*alpha/(l-2); beta = log(dk)/LOG2;
    if (beta>1.) beta += log(beta)/LOG2;
    p = (long)((bit_accuracy(l)>>1)/beta + 1);
    p2 = p1;
  }
  mpbern(p,l2); p3 = glog(p2,l2);

  p4 = cgetg(3,t_COMPLEX);
  p4[1] = (long)subrr((GEN)p2[1], real2n(-1, l2));
  p4[2] = (long)rcopy((GEN)p2[2]);
  gsubz(gmul(p4, p3), p2, p4);

  pitemp = mppi(l2); setexpo(pitemp,2);
  p7 = mplog(pitemp); setexpo(p7,-1);
  setexpo(pitemp,1);
  addrrz((GEN)p4[1],p7, (GEN)p4[1]);

  p5 = cgetc(l2);
  setlg(p5[1], 4);
  setlg(p5[2], 4);
  p71 = cgetr(l2); p7 = bern(p);
  if (bernzone[2]>4) { setlg(p71,4); affrr(p7,p71); p7=p71; }
  p7 = divrs(p7, 2*p*(2*p-1)); gaffect(p7,p5);
  p3 = ginv(gsqr(p2)); e = gexpo(p3);

  s=0; l1=4; av1=avma;
  for (k=p-1; k>0; k--)
  {
    setlg(p3[1], l1);
    setlg(p3[2], l1);
    p6 = gmul(p3,p5); p7 = bern(k);
    if (bernzone[2]>l1) { setlg(p71,l1); affrr(p7,p71); p7=p71; }
    p7 = divrs(p7, (2*k)*(2*k-1));
    s -= e; l1 += (s>>TWOPOTBITS_IN_LONG); if (l1>l2) l1=l2;
    s &= (BITS_IN_LONG-1); p7 = addrr(p7, (GEN)p6[1]);
    setlg(p5[1],l1); affrr(p7, (GEN)p5[1]); p7 = (GEN)p6[2];
    setlg(p5[2],l1); affrr(p7, (GEN)p5[2]); avma=av1;
  }
  setlg(p5[1],l2);
  setlg(p5[2],l2);
  p6 = gdiv(p5,p2); setlg(p6[1],l2); setlg(p6[2],l2);
  p4 = gadd(p4,p6); setlg(p4[1],l2); setlg(p4[2],l2);

  p4 = gexp(p4,l2);
  for (i=1; i<=n; i++)
  {
    addsrz(-1,(GEN)p2[1],(GEN)p2[1]); p4 = gdiv(p4,p2);
  }
  if (flag)
  {
    setlg(pitemp,l+1); p1 = gmul(pitemp,x);
    p4 = gmul(gsin(p1,l+1), p4);
    p4 = gdiv(pitemp,p4);
  }
  gaffect(p4,y); avma=av; return y;
}
#endif

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
    p1 = mpent(s);
    if (gcmp0(subri(s,p1))) *s0 = p1;
  }
  *prec = l; return s;
}

/* x, z t_REAL. Compute unique x in ]-z,z] congruent to x mod 2z */
static GEN
red_mod_2z(GEN x, GEN z)
{
  GEN Z = gmul2n(z, 1), d = subrr(z, x); 
  /* require little accuracy */
  setlg(d, 3 + ((expo(d) - expo(Z)) >> TWOPOTBITS_IN_LONG));
  return addrr(mulir(mpent(divrr(d, Z)), Z), x);
}

static GEN
cxgamma(GEN s0, int dolog, long prec)
{
  GEN s, u, a, y, res, tes, sig, invn2, p1, nnx, pi, sqrtpi2;
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
  if (funeq) { s = gsub(gun, s); sig = greal(s); }

  { /* find "optimal" parameters [lim, nn] */
    double ssig = rtodbl(sig);
    double st = rtodbl(gimag(s));
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
    if (DEBUGLEVEL) fprintferr("lim, nn: [%ld, %ld], la = %lf\n",lim,nn,la);

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
    if (DEBUGLEVEL) fprintferr("lim, nn: [%ld, %ld]\n",lim,nn);
#endif
  }
  prec++;

  av2 = avma; avlim = stack_lim(av2,3);
  y = s;
  if (typ(s0) == t_INT)
  {
    long ss;
    if (expi(s0) > 20) err(talker, "exponent too large in gamma");
    ss = itos(s0);
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
  else
    for (i=1; i < nn; i++)
    {
      y = gmul(y, gaddgs(s,i));
      if (low_stack(avlim,stack_lim(av2,3)))
      {
        if(DEBUGMEM>1) err(warnmem,"gamma");
        y = gerepileupto(av2, y);
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

  pi = mppi(prec); sqrtpi2 = mpsqrt( gmul2n(pi, 1) );
  if (funeq)
  { /* y --> y Pi/(sin(Pi s) * sqrt(2Pi)) */
    y = gdiv(gmul(pi,y), gmul(sqrtpi2, gsin(gmul(s,pi), prec)));
    p1 = gneg(p1);
  }
  else /* y --> sqrt(2Pi) / y */
    y = gdiv(sqrtpi2, y);
  if (dolog)
  {
    y = gadd(p1, glog(y, prec));
    if (typ(y) == t_COMPLEX) y[2] = (long)red_mod_2z((GEN)y[2], pi);
  }
  else
    y = gmul(gexp(p1, prec), y);
  gaffect(y, res); avma = av; return res;
}

GEN
ggamma(GEN x, long prec)
{
  pari_sp av = avma;
  long m;
  GEN y, p1;
  
  switch(typ(x))
  {
    case t_INT:
      if (signe(x)<=0) err(gamer2);
      if (cmpis(x,481177) > 0) err(talker,"argument too large in ggamma");
/* heuristic */
      if (cmpis(x, 350 + 70*(prec-2)) > 0) break;
      y = cgetr(prec); av = avma;
      affir(mpfact(itos(x) - 1), y);
      avma = av; return y;

    case t_REAL: case t_COMPLEX:
      return cxgamma(x, 0, prec);

    case t_FRAC:
      if (!egalii((GEN)x[2], gdeux)) break;
      x = (GEN)x[1]; /* true argument is x/2 */
/* heuristic */
      if (cmpis(x, 200 + 50*(prec-2)) > 0) break;

      y = cgetr(prec); av = avma;
      if (cmpis(mpabs(x), 962354) > 0)
        err(talker, "argument too large in ggamma");
      p1 = mpsqrt( mppi(prec) );
      m = itos(x) - 1;
      if (m)
      {
        long ma = labs(m);
        GEN p2 = gmul2n(seq_umul(ma/2 + 1, ma), -ma);
        if (m >= 0) p1 = gmul(p1,p2);
        else
        {
          p1 = gdiv(p1,p2);
          if ((m&3) == 2) setsigne(p1,-1);
        }
      }
      affrr(p1, y); avma = av; return y;

    case t_FRACN:
      return gerepileupto(av, ggamma(gred(x), prec));
      
    case t_PADIC: err(impl,"p-adic gamma function");
    case t_INTMOD: err(typeer,"ggamma");
    default:
      av = avma; if (!(y = _toser(x))) break;
      return gerepileupto(av, gexp(glngamma(y,prec),prec));
  }
  return transc(ggamma,x,prec);
}

void
ggammaz(GEN x, GEN y)
{
  long prec = precision(y);
  pari_sp av=avma;

  if (!prec) err(infprecer,"ggammaz");
  gaffect(ggamma(x,prec),y); avma=av;
}

#if 0
static GEN
mplngamma(GEN x)
{
  GEN z,y,p1,p2,p3,p4,p5,p6,p7,p71,pitemp;
  long l, l1, l2, u, i, k, e, f, s, sx, n, p;
  pari_sp av, av1;
  double alpha,beta,dk;

  sx=signe(x); if (!sx) err(talker,"zero argument in mplngamma");
  z = cgetg(3, t_COMPLEX); l=lg(x); y=cgetr(l); av=avma;

  l2=l+1; p1=cgetr(l2);
  u = (expo(x)<-1 || sx<0);
  if (!u) p2 = x;
  else
  {
    p2=gfrac(x); if (gcmp0(p2)) err(gamer2);
    p2 = subsr(1,x);
  }
  affrr(p2,p1);
  if (expo(p1)>1000)
  {
    n=0; beta = log(pariK4/(l-2))/LOG2+expo(p1);
    beta += log(beta)/LOG2;
    p = (long)((bit_accuracy(l)>>1)/beta + 1);
    p2 = p1;
  }
  else
  {
    alpha=rtodbl(p1); beta = ((bit_accuracy(l)>>1) * LOG2 / PI) - alpha;
    if (beta>=0) n=(long)(1 + pariK2*beta); else n=0;
    if (n)
    {
      p=(long)(1+PI*(alpha+n));
      l2 += n>>TWOPOTBITS_IN_LONG;
      p2 = cgetr(l2); addsrz(n,p1,p2);
    }
    else
    {
      dk = pariK4*alpha/(l-2); beta = log(dk)/LOG2;
      if (beta>1.) beta += (log(beta)/LOG2);
      p = (long)((bit_accuracy(l)>>1)/beta + 1);
      p2 = p1;
    }
  }
  mpbern(p,l2); p3=mplog(p2);

  p4 = real2n(-1, l2);
  p6 = subrr(p2,p4); p6 = mulrr(p6,p3);
  p6 = subrr(p6,p2);
  pitemp = mppi(l2); setexpo(pitemp,2);
  p7 = mplog(pitemp); setexpo(pitemp,1);
  setexpo(p7,-1); addrrz(p6,p7,p4);

  affrr(ginv(gsqr(p2)), p3); e=expo(p3);

  p5=cgetr(l2); setlg(p5,4);
  p71=cgetr(l2); p7 = bern(p);
  if (bernzone[2]>4) { setlg(p71,4); affrr(p7,p71); p7=p71; }
  p7 = divrs(p7, 2*p*(2*p-1)); affrr(p7,p5);

  s=0; l1=4; av1=avma;
  for (k=p-1; k>0; k--)
  {
    setlg(p3,l1); p6 = mulrr(p3,p5); p7 = bern(k);
    if (bernzone[2]>l1) { setlg(p71,l1); affrr(p7,p71); p7=p71; }
    p7 = divrs(p7, (2*k)*(2*k-1));
    s -= e; l1 += (s>>TWOPOTBITS_IN_LONG); if (l1>l2) l1=l2;
    s &= (BITS_IN_LONG-1); p7 = addrr(p7,p6);
    setlg(p5,l1); affrr(p7,p5); avma=av1;
  }
  setlg(p5,l2); p6 = divrr(p5,p2);
  p4 = addrr(p4,p6); setlg(p4,l2);
  if (n)
  {
    for (i=1; i<=n; i++)
    {
      addsrz(-1,p2,p2); p7 = (i==1)? rcopy(p2): mulrr(p7,p2);
    }
    f=signe(p7); if (f<0) setsigne(p7,1);
    subrrz(p4,mplog(p7),p4);
  }
  else f=1;
  if (u)
  {
    setlg(pitemp,l+1); p1 = mulrr(pitemp,x);
    p1 = divrr(pitemp,mpsin(p1));
    if (signe(p1) < 0) { setsigne(p1,1); f = -f; }
    p4 = subrr(mplog(p1),p4);
  }
  if (f<0) /* t_COMPLEX result */
  {
    z[1] = (long)y; affrr(p4,y); avma = av;
    z[2] = (long)mppi(l); return z;
  }
  /* t_REAL result */
  y[3] = y[0]; y += 3;
  affrr(p4,y); avma = (pari_sp)y; return y;
}

static GEN
cxlngamma(GEN x, long prec)
{
  GEN y,p1,p2,p3,p4,p5,p6,p7,p71,pitemp;
  long l, l1, l2, flag, i, k, e, s, n, p;
  pari_sp av, av1;
  double alpha,beta,dk;

  if (gcmp0((GEN)x[2])) return glngamma((GEN)x[1],prec);
  l = precision(x); if (!l) l = prec;
  l2 = l+1; y = cgetc(l); av = avma;

  p1 = cgetc(l2);
  flag = (gsigne((GEN)x[1]) <= 0 || gexpo((GEN)x[1]) < -1);
  if (flag && (gcmp0((GEN)x[2]) || gexpo((GEN)x[2]) > 16)) flag = 0;
  p2 = flag? gsub(gun,x): x;
  gaffect(p2,p1);

  p2 = gabs(p1,DEFAULTPREC);
  if (expo(p2)>1000)
  {
    n=0; beta = log(pariK4/(l-2)) / LOG2 + expo(p1);
    beta += log(beta)/LOG2;
    p = (long)((bit_accuracy(l)>>1)/beta + 1);
    p2 = p1;
  }
  else
  {
    alpha = rtodbl(p2);
    beta = ((bit_accuracy(l)>>1) * LOG2 / PI) - alpha;
    if (beta>=0) n=(long)(1+pariK2*beta); else n=0;
    if (n)
    {
      p = (long)(1+PI*(alpha+n));
      l2 += n>>TWOPOTBITS_IN_LONG;
      p2 = cgetc(l2);
      addsrz(n,(GEN)p1[1],(GEN)p2[1]);
      affrr((GEN)p1[2],   (GEN)p2[2]);
    }
    else
    {
      dk = pariK4*alpha/(l-2); beta = log(dk)/LOG2;
      if (beta>1.) beta += log(beta)/LOG2;
      p = (long)((bit_accuracy(l)>>1)/beta + 1);
      p2 = p1;
    }
  }
  mpbern(p,l2); p3 = glog(p2,l2);

  p4 = cgetg(3,t_COMPLEX);
  p4[1] = (long)subrr((GEN)p2[1], real2n(-1, l2));
  p4[2] = (long)rcopy((GEN)p2[2]);
  gsubz(gmul(p4, p3), p2, p4);

  pitemp = mppi(l2); setexpo(pitemp,2);
  p7 = mplog(pitemp); setexpo(p7,-1); /* log(2Pi) / 2 */
  setexpo(pitemp,1);/* now pitemp = Pi */
  addrrz((GEN)p4[1],p7, (GEN)p4[1]);

  p5 = cgetc(l2);
  setlg(p5[1], 4);
  setlg(p5[2], 4);
  p71 = cgetr(l2); p7 = bern(p);
  if (bernzone[2]>4) { setlg(p71,4); affrr(p7,p71); p7=p71; }
  p7 = divrs(p7, 2*p*(2*p-1)); gaffect(p7,p5);
  p3 = ginv(gsqr(p2)); e = gexpo(p3);

  s=0; l1=4; av1=avma;
  for (k=p-1; k>0; k--)
  {
    setlg(p3[1], l1);
    setlg(p3[2], l1);
    p6 = gmul(p3,p5); p7 = bern(k);
    if (bernzone[2]>l1) { setlg(p71,l1); affrr(p7,p71); p7=p71; }
    p7 = divrs(p7, (2*k)*(2*k-1));
    s -= e; l1 += (s>>TWOPOTBITS_IN_LONG); if (l1>l2) l1=l2;
    s &= (BITS_IN_LONG-1); p7 = addrr(p7, (GEN)p6[1]);
    setlg(p5[1], l1); affrr(p7, (GEN)p5[1]); p7 = (GEN)p6[2];
    setlg(p5[2], l1); affrr(p7, (GEN)p5[2]); avma=av1;
  }
  setlg(p5[1],l2);
  setlg(p5[2],l2);
  p6 = gdiv(p5,p2); setlg(p6[1],l2); setlg(p6[2],l2);
  p4 = gadd(p4,p6); setlg(p4[1],l2); setlg(p4[2],l2);

  if (n)
  {
    p7 = cgetg(3,t_COMPLEX); p7[2] = p2[2];
    for (i=1; i<=n; i++)
    {
      addsrz(-1,(GEN)p2[1], (GEN)p2[1]);
      if (i==1) p7[1] = lrcopy((GEN)p2[1]); else p7 = gmul(p7,p2);
    }
    gsubz(p4,glog(p7,l+1), p4);
  }
  if (flag)
  {
    setlg(pitemp,l+1); p1 = gmul(pitemp,x);
    p1 = gdiv(pitemp,gsin(p1,l+1));
    p4 = gsub(glog(p1,l+1),p4);
  }
  affrr((GEN)p4[1], (GEN)y[1]);
  
  setlg(p4[2],l+1);
  affrr(red_mod_2z((GEN)p4[2], pitemp), (GEN)y[2]);
  avma = av; return y;
}
#endif

GEN
glngamma(GEN x, long prec)
{
  long i, n;
  pari_sp av;
  GEN a, y, p1, p2;

  switch(typ(x))
  {
    case t_INT:
      if (signe(x)<=0) err(gamer2);
      p2 = cgetr(prec); av = avma;
/* heuristic */
      if (cmpis(x,200 + 50*(prec-2)) > 0)
	return transc(glngamma,x,prec);
      p1 = glog(mpfact(itos(x) - 1),prec);
      affrr(p1,p2); avma = av;
      return p2;

    case t_REAL: case t_COMPLEX:
      return cxgamma(x, 1, prec);

    default:
      av = avma; if (!(y = _toser(x))) break;
      if (valp(y)) err(negexper,"glngamma");
      p1 = gsubsg(1,y);
      if (!valp(p1)) err(impl,"lngamma around a!=1");
      n = (lg(y)-3) / valp(p1);
      a = ggrando(polx[varn(y)], lg(y)-2);
      for (i=n; i>=2; i--)
	a = gmul(p1, gadd(a, gdivgs(szeta(i, prec),i)));
      a = gadd(a, mpeuler(prec));
      return gerepileupto(av, gmul(a, p1));

    case t_PADIC:  err(impl,"p-adic lngamma function");
    case t_INTMOD: err(typeer,"glngamma");
  }
  return transc(glngamma,x,prec);
}

void
glngammaz(GEN x, GEN y)
{
  long prec = precision(y);
  pari_sp av=avma;

  if (!prec) err(infprecer,"glngammaz");
  gaffect(glngamma(x,prec),y); avma=av;
}

/********************************************************************/
/**                                                                **/
/**             FONCTION GAMMA DES DEMI-ENTIERS                    **/
/**                                                                **/
/********************************************************************/

static GEN
mpgamd(long x, long prec)
{
  long i, j, a, l;
  pari_sp av;
  GEN y,p1,p2;

  a = labs(x);
  l = prec+1+(a>>TWOPOTBITS_IN_LONG);
  if ((ulong)l > LGBITS>>1) err(talker,"argument too large in ggamd");
  y=cgetr(prec); av=avma;

  p1 = mpsqrt(mppi(l));
  j = 1; p2 = realun(l);
  for (i=1; i<a; i++)
  {
    j += 2;
    p2 = mulsr(j,p2); setlg(p2,l);
  }
  if (x>=0) p1 = mulrr(p1,p2);
  else
  {
    p1 = divrr(p1,p2); if (a&1) setsigne(p1,-1);
  }
  setexpo(p1, expo(p1)-x);
  affrr(p1,y); avma=av; return y;
}

void
mpgamdz(long s, GEN y)
{
  pari_sp av=avma;

  affrr(mpgamd(s,lg(y)),y); avma=av;
}

GEN
ggamd(GEN x, long prec)
{
  pari_sp av, tetpil;

  switch(typ(x))
  {
    case t_INT:
      return mpgamd(itos(x),prec);

    case t_REAL: case t_FRAC: case t_FRACN: case t_COMPLEX: case t_QUAD:
      av=avma; x = gadd(x,ghalf); tetpil=avma;
      return gerepile(av,tetpil,ggamma(x,prec));

    case t_INTMOD: case t_PADIC: err(typeer,"ggamd");
    case t_SER: err(impl,"gamd of a power series");
  }
  return transc(ggamd,x,prec);
}

void
ggamdz(GEN x, GEN y)
{
  long prec = precision(y);
  pari_sp av=avma;

  if (!prec) err(infprecer,"ggamdz");
  gaffect(ggamd(x,prec),y); avma=av;
}

/********************************************************************/
/**                                                                **/
/**                      FONCTION PSI                              **/
/**                                                                **/
/********************************************************************/

GEN
psinew(GEN s0, long prec)
{
  pari_sp av;
  GEN sum,z,a,res,tes,in2,sig,s,unr;
  long lim,nn,k;
  const long la = 3;
 

  if (DEBUGLEVEL>2) (void)timer2();
  s = trans_fix_arg(&prec,&s0,&sig,&av,&res);
  if (signe(sig) <= 0)
  {
    GEN pi = mppi(prec);
    z = gsub(psinew(gsubsg(1,s), prec), gmul(pi, gcotan(gmul(pi,s), prec)));
    gaffect(z, res); avma = av; return res;
  }
 
  {
    double ssig = rtodbl(sig);
    double st = rtodbl(gimag(s));
    double l;
    {
      double rlog, ilog; /* log (s-gamma) */
      dcxlog(ssig - rtodbl(mpeuler(3)), st, &rlog,&ilog);
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
  sum = gmul2n(a,-1);
  for (k = 0; k < nn; k++)
    sum = gadd(sum, gdiv(unr, gaddgs(s, k)));
  z = gsub(glog(gaddgs(s, nn), prec), sum);
  if (DEBUGLEVEL>2) msgtimer("sum from 0 to N-1");
 
  tes = divrs(bernreal(2*lim, prec), 2*lim);
  in2 = gsqr(a);
  for (k=2*lim-2; k>=2; k-=2)
  {
    tes = gadd(gmul(in2,tes), divrs(bernreal(k, prec), k));
  }
  if (DEBUGLEVEL>2) msgtimer("Bernoulli sum");
  z = gsub(z, gmul(in2,tes));
  gaffect(z, res); avma = av; return res;
}

#if 0
static GEN
mppsi(GEN z)  /* version p=2 */
{
  long l, n, k, x, xx;
  pari_sp av, av1, tetpil;
  GEN zk,u,v,a,b;

  av=avma; l=lg(z);
  x=(long)(1 + (bit_accuracy(l)>>1)*LOG2 + 1.58*rtodbl(absr(z)));
  if (expo(z)>=15 || x>46340) err(impl,"psi(x) for x>=29000");
  xx=x*x; n=(long)(1+3.591*x);
  a = stor(x, l);
  a = mplog(a);
  gaffect(a,u=cgetr(l));
  gaffsg(1,b=cgetr(l));
  gaffsg(1,v=cgetr(l)); av1=avma;
  for (k=1; k<=n; k++)
  {
    zk = (k>1)? addsr(k-1,z): z;
    divrrz(mulsr(xx,b),gsqr(zk),b);
    divrrz(subrr(divrr(mulsr(xx,a),zk),b),zk,a);
    addrrz(u,a,u); addrrz(v,b,v); avma=av1;
  }
  tetpil=avma; return gerepile(av,tetpil,divrr(u,v));
}
static GEN /* by Manfred Radimersky */
mppsi(GEN z)
{
  long head, tail;
  long len, num, k;
  GEN a, b, f, s, x;

  head = avma;
  len = lg(z);
  num = bit_accuracy(len);

  if(signe(z) < 0) {
    x = subsr(1, z);
    s = mppsi(x);
    f = mulrr(mppi(len), z);
    mpsincos(f, &a, &b);
    f = divrr(b, a);
    a = mulrr(mppi(len), f);
    tail = avma;
    gerepile(head, tail, subrr(s, a));
  }

  a = stor(0, len);
  x = cgetr(len);
  affrr(z, x);
  tail = avma;
  while(cmprs(x, num >> 2) < 0) {
    gaddz(a, ginv(x), a);
    gaddgsz(x, 1, x);
    avma = tail;
  }

  s = mplog(x);
  gsubz(s, a, s);
  b = gmul2n(x, 1);
  gsubz(s, ginv(b), s);

  mpbern(num, len);

  affsr(-1, a);
  gdivgsz(a, 2, a);
  f = mulrr(x, x);
  f = ginv(f);
  k = 1;
  do {
    gmulz(a, f, a);
    gdivgsz(a, k, b);
    gmulz(b, bern(k), b);
    gaddz(s, b, s);
    k++;
  } while(expo(s) - expo(b) < num);

  return gerepilecopy(head, s);
}
static GEN
cxpsi(GEN z, long prec) /* version p=2 */
{
  long l, n, k, x, xx;
  pari_sp av, av1, tetpil;
  GEN zk,u,v,a,b,p1;

  if (gcmp0((GEN)z[2])) return gpsi((GEN)z[1],prec);
  l = precision(z); if (!l) l = prec; av=avma;
  x=(long)(1 + (bit_accuracy(l)>>1)*LOG2 + 1.58*gtodouble(gabs(z,DEFAULTPREC)));
  xx=x*x; n=(long)(1+3.591*x);
  a=cgetc(l); gaffsg(x,a);
  b=cgetc(l); gaffsg(1,b);
  u=cgetc(l);
  v=cgetc(l); gaffsg(1,v);
  p1=glog(a,l); gaffect(p1,a); gaffect(p1,u); av1=avma;
  for (k=1; k<=n; k++)
  {
    zk=(k>1) ? gaddsg(k-1,z) : z;
    gdivz(gmulsg(xx,b),gsqr(zk),b);
    gdivz(gsub(gdiv(gmulsg(xx,a),zk),b),zk,a);
    gaddz(u,a,u); gaddz(v,b,v); avma=av1;
  }
  tetpil=avma; return gerepile(av,tetpil,gdiv(u,v));
}
GEN
cxpsi(GEN z, long prec) /* by Manfred Radimersky */
{
  long head, tail;
  long bord, nubi, k;
  GEN a, b, f, s, w, wn;

  if (gcmp0((GEN)z[2])) return gpsi((GEN)z[1],prec);
  head = avma;
  nubi = bit_accuracy(prec);
  bord = (nubi * nubi) >> 4;

  if(signe((GEN) z[1]) < 0) {
    w = gsubsg(1, z);
    s = cxpsi(w, prec);
    f = gmul(mppi(prec), z);
    gsincos(f, &a, &b, prec);
    f = gdiv(b, a);
    a = gmul(mppi(prec), f);
    tail = avma;
    gerepile(head, tail, gsub(s, a));
  }

  a = cgetc(prec); gaffsg(0, a);
  w = cgetc(prec); gaffect(z, w);
  wn = gnorm(w);
  tail = avma;
  while(cmprs(wn, bord) < 0) {
    gaddz(a, gdivsg(1, w), a);
    gaddgsz((GEN) w[1], 1, (GEN) w[1]);
    gaffect(gnorm(w), wn);
    avma = tail;
  }

  s = glog(w, prec);
  gsubz(s, a, s);
  b = gmul2n(w, 1);
  gsubz(s, gdivsg(1, b), s);

  mpbern(nubi, prec);

  gaffsg(-1, a);
  gdivgsz(a, 2, a);
  f = gmul(w, w);
  f = gdivsg(1, f);
  k = 1;
  tail = avma;
  do {
    gmulz(a, f, a);
    gdivgsz(a, k, b);
    gmulz(b, bern(k), b);
    gaddz(s, b, s);
    bord = expo(gnorm(s)) - expo(gnorm(b));
    k++;   
    avma = tail;
  } while(bord < nubi << 1);

  return gerepilecopy(head, s);
}
#endif

GEN
gpsi(GEN x, long prec)
{
  switch(typ(x))
  {
    case t_REAL: case t_COMPLEX: return psinew(x,prec);
    case t_INTMOD: case t_PADIC: err(typeer,"gpsi");
    case t_SER: err(impl,"psi of power series");
  }
  return transc(gpsi,x,prec);
}

void
gpsiz(GEN x, GEN y)
{
  long prec = precision(y);
  pari_sp av=avma;

  if (!prec) err(infprecer,"gpsiz");
  gaffect(gpsi(x,prec),y); avma=av;
}
