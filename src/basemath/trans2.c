/********************************************************************/
/**                                                                **/
/**                   TRANSCENDENTAL FONCTIONS                     **/
/**                          (part 2)                              **/
/**                                                                **/
/********************************************************************/
/* $Id$ */
#include "pari.h"

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
  long l,l1,l2,n,m,u,i,av0,av,lp,e,sx,s;
  double alpha,beta,gama=1.0,delta,fi;
  GEN y,p1,p2,p3,p4,p5,unr;

  sx=signe(x);
  if (!sx)
  {
    y=cgetr(3); y[1]=x[1]; y[2]=0; return y;
  }
  l = lp = lg(x);
  if (sx<0) setsigne(x,1);
  u = cmprs(x,1);
  if (!u)
  {
    y=mppi(l+1); setexpo(y,-1);
    if (sx<0)
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
  beta = (bit_accuracy(l)>>1) * LOG2;
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
  if (u==1)
  {
    p5 = mppi(lp+1); setexpo(p5,0);
    p4 = subrr(p5,p4);
  }
  if (sx == -1) setsigne(p4,-signe(p4));
  affrr(p4,y); avma=av0; return y;
}

GEN
gatan(GEN x, long prec)
{
  long av,tetpil;
  GEN y,p1;

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

    case t_SER:
      av=avma; if (valp(x)<0) err(negexper,"gatan");
      if (lg(x)==2) return gcopy(x);
      /*Now we can assume lg(x)>2*/
      p1=gdiv(derivser(x), gaddsg(1,gsqr(x)));
      y=integ(p1,varn(x)); if (valp(x)) return gerepileupto(av,y);

      p1=gatan((GEN)x[2],prec); tetpil=avma;
      return gerepile(av,tetpil,gadd(p1,y));

    case t_INTMOD: case t_PADIC:
      err(typeer,"gatan");
  }
  return transc(gatan,x,prec);
}

void
gatanz(GEN x, GEN y)
{
  long av=avma,prec = precision(y);

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
  long l,u,v,av;
  GEN y,p1;

  u=cmprs(x,1); v=cmpsr(-1,x);
  if (!u || !v)
  {
    y=mppi(lg(x)); setexpo(y,0);
    if (signe(x)<0) setsigne(y,-1);
    return y;
  }
  l = lg(x); y=cgetr(l); av=avma;

  p1 = cgetr(l+1); mulrrz(x,x,p1);
  subsrz(1,p1,p1);
  divrrz(x,mpsqrt(p1),p1);
  affrr(mpatan(p1),y); if (signe(x)<0) setsigne(y,-1);
  avma=av; return y;
}

GEN
gasin(GEN x, long prec)
{
  long av,tetpil,l,sx;
  GEN y,p1;

  switch(typ(x))
  {
    case t_REAL: sx=signe(x);
      if (!sx) { y=cgetr(3); y[1]=x[1]; y[2]=0; return y; }
      if (sx<0) setsigne(x,1);
      if (cmpsr(1,x)>=0) { setsigne(x,sx); return mpasin(x); }

      y=cgetg(3,t_COMPLEX);
      y[1]=lmppi(lg(x)); setexpo(y[1],0);
      y[2]=lmpach(x);
      if (sx<0)
      {
        setsigne(y[1],-signe(y[1]));
        setsigne(y[2],-signe(y[2]));
        setsigne(x,sx);
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

    case t_SER:
      if (gcmp0(x)) return gcopy(x);
      /*Now, we can assume lg(x)>2*/
      av=avma; if (valp(x)<0) err(negexper,"gasin");
      p1=gdiv(derivser(x), gsqrt(gsubsg(1,gsqr(x)),prec));
      y=integ(p1,varn(x)); if (valp(x)) return gerepileupto(av,y);

      p1=gasin((GEN)x[2],prec); tetpil=avma;
      return gerepile(av,tetpil,gadd(p1,y));

    case t_INTMOD: case t_PADIC:
      err(typeer,"gasin");
  }
  return transc(gasin,x,prec);
}

void
gasinz(GEN x, GEN y)
{
  long av=avma, prec = precision(y);

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
  long l,u,v,sx,av;
  GEN y,p1,p2;

  u=cmprs(x,1); v=cmpsr(-1,x); sx = signe(x);
  if (!sx)
  {
    l=expo(x)>>TWOPOTBITS_IN_LONG; if (l>=0) l = -1;
    y=mppi(2-l); setexpo(y,0); return y;
  }
  l=lg(x);
  if (!u)
  {
    y = cgetr(3);
    y[1] = evalexpo(-(bit_accuracy(l)>>1));
    y[2] = 0; return y;
  }
  if (!v) return mppi(l);
  y=cgetr(l); av=avma;

  p1=cgetr(l+1);
  if (expo(x)<0)
  {
    mulrrz(x,x,p1);
    subsrz(1,p1,p1);
    p1 = mpsqrt(p1); divrrz(x,p1,p1);
    p1 = mpatan(p1);
    p2 = mppi(l); setexpo(p2,0);
    p1 = subrr(p2,p1);
  }
  else
  {
    p2=cgetr(l+1);
    if (sx>0) addsrz(1,x,p1); else subsrz(1,x,p1);
    subsrz(2,p1,p2);
    mulrrz(p1,p2,p1);
    p1 = mpsqrt(p1); divrrz(p1,x,p1);
    p1 = mpatan(p1);
    if (sx<0) { setlg(p1,l); p1 = addrr(mppi(l),p1); }
  }
  affrr(p1,y); avma=av; return y;
}

GEN
gacos(GEN x, long prec)
{
  long av,tetpil,l,sx;
  GEN y,p1;

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

    case t_SER: av=avma;
      if (valp(x)<0) err(negexper,"gacos");
      if (lg(x)>2)
      {
	p1=integ(gdiv(derivser(x), gsqrt(gsubsg(1,gsqr(x)),prec)),varn(x));
	if (gcmp1((GEN)x[2]) && !valp(x))/*x=1+O(x^k);k>=1*/
	{
	  tetpil=avma; return gerepile(av,tetpil,gneg(p1));
	}
      } 
      else p1=x;
      if (lg(x)==2 || valp(x)) { y=mppi(prec); setexpo(y,0); }
      else y=gacos((GEN)x[2],prec);
      tetpil=avma; return gerepile(av,tetpil,gsub(y,p1));

    case t_INTMOD: case t_PADIC:
      err(typeer,"gacos");
  }
  return transc(gacos,x,prec);
}

void
gacosz(GEN x, GEN y)
{
  long av=avma, prec = precision(y);

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
    if (sx>0)
    {
      theta=cgetr(3); theta[1]=y[1]-expo(x);
      theta[2]=0; return theta;
    }
    return mppi(lg(x));
  }
  prec = lg(y); if (prec<lg(x)) prec = lg(x);
  if (!sx)
  {
    theta=mppi(prec); setexpo(theta,0);
    if (sy<0) setsigne(theta,-1);
    return theta;
  }

  if (expo(x)-expo(y) > -2)
  {
    theta = mpatan(divrr(y,x));
    if (sx>0) return theta;
    pitemp=mppi(prec);
    if (sy>0) return addrr(pitemp,theta);
    return subrr(theta,pitemp);
  }
  theta = mpatan(divrr(x,y));
  pitemp=mppi(prec); setexpo(pitemp,0);
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
  long av=avma;
  x = rfix(x,prec); y = rfix(y,prec);
  return gerepileupto(av,mparg(x,y));
}

GEN
garg(GEN x, long prec)
{
  GEN p1;
  long av,tx=typ(x),tetpil;

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
/**                 FONCTION COSINUS HYPERBOLIQUE                  **/
/**                                                                **/
/********************************************************************/

static GEN
mpch(GEN x)
{
  long l,av;
  GEN y,p1;

  if (gcmp0(x)) return gaddsg(1,x);

  l=lg(x); y=cgetr(l); av=avma;
  p1=mpexp(x); p1 = addrr(p1, divsr(1,p1));
  setexpo(p1, expo(p1)-1);
  affrr(p1,y); avma=av; return y;
}

GEN
gch(GEN x, long prec)
{
  long av,tetpil;
  GEN p1;

  switch(typ(x))
  {
    case t_REAL:
      return mpch(x);

    case t_COMPLEX:
      av=avma; p1=gexp(x,prec);
      p1=gadd(p1,ginv(p1)); tetpil=avma;
      return gerepile(av,tetpil,gmul2n(p1,-1));

    case t_SER:
      av=avma; p1=gexp(x,prec); p1=gadd(p1,gdivsg(1,p1));
      tetpil=avma; return gerepile(av,tetpil,gmul2n(p1,-1));

    case t_INTMOD: case t_PADIC:
      err(typeer,"gch");
  }
  return transc(gch,x,prec);
}

void
gchz(GEN x, GEN y)
{
  long av=avma,prec = precision(y);

  if (!prec) err(infprecer,"gchz");
  gaffect(gch(x,prec),y); avma=av;
}

/********************************************************************/
/**                                                                **/
/**                 FONCTION SINUS HYPERBOLIQUE                    **/
/**                                                                **/
/********************************************************************/

static GEN
mpsh(GEN x)
{
  long l,av;
  GEN y,p1;

  if (!signe(x))
  {
    y=cgetr(3); y[1]=x[1]; y[2]=0; return y;
  }
  l=lg(x); y=cgetr(l); av=avma;
  p1=mpexp(x); p1 = addrr(p1, divsr(-1,p1));
  setexpo(p1, expo(p1)-1);
  affrr(p1,y); avma=av; return y;
}

GEN
gsh(GEN x, long prec)
{
  long av,tetpil;
  GEN p1;

  switch(typ(x))
  {
    case t_REAL:
      return mpsh(x);

    case t_COMPLEX:
      av=avma; p1=gexp(x,prec);
      p1=gsub(p1,ginv(p1)); tetpil=avma;
      return gerepile(av,tetpil,gmul2n(p1,-1));

    case t_SER:
      if (gcmp0(x)) return gcopy(x);

      av=avma; p1=gexp(x,prec); p1=gsub(p1,gdivsg(1,p1));
      tetpil=avma; return gerepile(av,tetpil,gmul2n(p1,-1));

    case t_INTMOD: case t_PADIC:
      err(typeer,"gsh");
  }
  return transc(gsh,x,prec);
}

void
gshz(GEN x, GEN y)
{
  long av=avma, prec = precision(y);

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
  long l,av;
  GEN y,p1,p2;

  if (!signe(x))
  {
    y=cgetr(3); y[1]=x[1]; y[2]=0;
    return y;
  }
  l=lg(x); y=cgetr(l); av=avma;

  p1=cgetr(l+1); affrr(x,p1);
  setexpo(p1,expo(p1)+1);
  p1 = mpexp1(p1);
  p2 = addsr(2,p1); setlg(p2,l+1);
  p1 = divrr(p1,p2);
  affrr(p1,y); avma=av; return y;
}

GEN
gth(GEN x, long prec)
{
  long av,tetpil;
  GEN p1,p2,p3;

  switch(typ(x))
  {
    case t_REAL:
      return mpth(x);

    case t_COMPLEX:
      av=avma; p1=gexp(gmul2n(x,1),prec);
      p1=gdivsg(-2,gaddgs(p1,1)); tetpil=avma;
      return gerepile(av,tetpil,gaddsg(1,p1));

    case t_SER:
      if (gcmp0(x)) return gcopy(x);

      av=avma; p1=gexp(gmul2n(x ,1),prec);
      p2=gsubgs(p1,1); p3=gaddgs(p1,1);
      tetpil=avma; return gerepile(av,tetpil,gdiv(p2,p3));

    case t_INTMOD: case t_PADIC:
      err(typeer,"gth");
  }
  return transc(gth,x,prec);
}

void
gthz(GEN x, GEN y)
{
  long av=avma, prec = precision(y);

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
  long s=signe(x),av;
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
  long av,tetpil,sx,sy,sz;
  GEN y,p1;

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

    case t_SER:
      if (gcmp0(x)) return gcopy(x);
      if (valp(x)<0) err(negexper,"gash");

      av=avma; p1=gdiv(derivser(x),gsqrt(gaddsg(1,gsqr(x)),prec));
      y = integ(p1,varn(x)); if (valp(x)) return gerepileupto(av,y);
      p1=gash((GEN)x[2],prec);
      tetpil=avma; return gerepile(av,tetpil,gadd(p1,y));

    case t_INTMOD: case t_PADIC:
      err(typeer,"gash");
  }
  return transc(gash,x,prec);
}

void
gashz(GEN x, GEN y)
{
  long av=avma, prec = precision(y);

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
  long l,av;
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
  long av,tetpil;
  GEN y,p1;

  switch(typ(x))
  {
    case t_REAL:
      if (gcmpgs(x,1)>=0) return mpach(x);

      y=cgetg(3,t_COMPLEX);
      if (gcmpgs(x,-1)>=0)
      {
	y[2]=lmpacos(x); y[1]=zero;
	return y;
      }
      av=avma; p1=mpach(gneg_i(x)); tetpil=avma;
      y[1]=lpile(av,tetpil,gneg(p1));
      y[2]=lmppi(lg(x));
      return y;

    case t_COMPLEX:
      av=avma; p1=gaddsg(-1,gsqr(x));
      p1=gadd(x,gsqrt(p1,prec)); tetpil=avma;
      y=glog(p1,prec);
      if (signe(y[2])<0) { tetpil=avma; y=gneg(y); }
      return gerepile(av,tetpil,y);

    case t_SER:
      av=avma; if (valp(x)<0) err(negexper,"gach");
      p1=gdiv(derivser(x),gsqrt(gsubgs(gsqr(x),1),prec));
      y=integ(p1,varn(x));
      if (!valp(x) && gcmp1((GEN)x[2])) return gerepileupto(av,y);
      if (valp(x))
      {
	p1=cgetg(3,t_COMPLEX); p1[1]=zero; p1[2]=lmppi(prec);
	setexpo(p1[2],0);
      }
      else p1=gach((GEN)x[2],prec);
      tetpil=avma; return gerepile(av,tetpil,gadd(p1,y));

    case t_INTMOD: case t_PADIC:
      err(typeer,"gach");
  }
  return transc(gach,x,prec);
}

void
gachz(GEN x, GEN y)
{
  long av=avma,prec = precision(y);

  if (!prec) err(infprecer,"gachz");
  gaffect(gach(x,prec),y); avma=av;
}

/********************************************************************/
/**                                                                **/
/**           FONCTION ARGUMENT TANGENTE HYPERBOLIQUE              **/
/**                                                                **/
/********************************************************************/

static GEN
mpath(GEN x)
{
  long av;
  GEN y,p1;

  if (!signe(x))
  {
    y=cgetr(3); y[1]=x[1]; y[2]=0;
    return y;
  }
  y=cgetr(lg(x)); av=avma;
  p1 = addrs(divsr(2,subsr(1,x)),-1);
  affrr(mplog(p1), y); avma=av;
  setexpo(y,expo(y)-1); return y;
}

GEN
gath(GEN x, long prec)
{
  long av,tetpil;
  GEN y,p1;

  switch(typ(x))
  {
    case t_REAL:
      if (expo(x)<0) return mpath(x);

      av=avma; p1=addrs(divsr(2,addsr(-1,x)),1);
      tetpil=avma; y=cgetg(3,t_COMPLEX);
      p1=mplog(p1); setexpo(p1,expo(p1)-1);
      y[1]=(long)p1;
      y[2]=lmppi(lg(x)); setexpo(y[2],0);
      return gerepile(av,tetpil,y);

    case t_COMPLEX:
      av=avma;
      p1=gaddgs(gdivsg(2,gsubsg(1,x)),-1);
      p1=glog(p1,prec); tetpil=avma;
      return gerepile(av,tetpil,gmul2n(p1,-1));

    case t_SER:
      av=avma; if (valp(x)<0) err(negexper,"gath");
      p1=gdiv(derivser(x), gsubsg(1,gsqr(x)));
      y = integ(p1,varn(x)); if (valp(x)) return gerepileupto(av,y);
      p1=gath((GEN)x[2],prec); tetpil=avma;
      return gerepile(av,tetpil,gadd(p1,y));

    case t_INTMOD: case t_PADIC:
      err(typeer,"gath");
  }
  return transc(gath,x,prec);
}

void
gathz(GEN x, GEN y)
{
  long av=avma, prec = precision(y);

  if (!prec) err(infprecer,"gathz");
  gaffect(gath(x,prec),y); avma=av;
}

/********************************************************************/
/**                                                                **/
/**             FONCTION TABLEAU DES NOMBRES DE BERNOULLI          **/
/**                                                                **/
/********************************************************************/
#define BERN(i)       (B + 3 + (i)*B[2])
/* pour calculer B_0,B_2,...,B_2*nb */
void
mpbern(long nb, long prec)
{
  long n,m,i,j,d,d1,d2,l,av,av2,code0;
  GEN p1,p2, B;

  if (nb<0) nb=0;
  if (bernzone && bernzone[1]>=nb && bernzone[2]>=prec) return;
  d = 3 + prec*(nb+1); B=newbloc(d);
  B[0]=evallg(d);
  B[1]=nb;
  B[2]=prec;
  av=avma; l = prec+1; p1=realun(l);

  code0 = evaltyp(t_REAL) | evallg(prec);
  *(BERN(0)) = code0; affsr(1,BERN(0));
  p2 = p1; av2=avma;
  for (i=1; i<=nb; i++)
  {
    if (i>1)
    {
      n=8; m=5; d = d1 = i-1; d2 = 2*i-3;
      for (j=d; j>0; j--)
      {
        p2 = BERN(j);
        if (j<d) p2 = addrr(p2,p1);
        else
        {
          affrr(p2,p1); p2=p1;
        }
        p2 = mulsr(n*m,p2); setlg(p2,l);
        p2 = divrs(p2, d1*d2); affrr(p2,p1);
        n+=4; m+=2; d1--; d2-=2;
      }
      p2 = addsr(1,p1); setlg(p2,l);
    }
    p2 = divrs(p2,2*i+1); p2 = subsr(1,p2);
    setexpo(p2, expo(p2) - 2*i);
    *(BERN(i)) = code0; affrr(p2,BERN(i)); avma=av2;
  }
  if (bernzone) gunclone(bernzone);
  avma = av; bernzone = B;
}
#undef BERN

GEN
bernreal(long n, long prec)
{
  GEN B;

  if (n==1) { B=cgetr(prec); affsr(-1,B); setexpo(B,-1); return B; }
  if (n<0 || n&1) return gzero;
  n >>= 1; mpbern(n+1,prec); B=cgetr(prec);
  affrr(bern(n),B); return B;
}

/* k > 0 */
static GEN
bernfracspec(long k)
{
  long n,av,lim, K = k+1;
  GEN s,c,N,h;

  c = N = stoi(K); s = gun; h = gzero;
  av = avma; lim = stack_lim(av,2);
  for (n=2; ; n++)
  {
    c = gdivgs(gmulgs(c,n-k-2),n);
    h = gadd(h, gdivgs(gmul(c,s), n));
    if (n==K) return gerepileupto(av,h);
    N[2] = n; s = addii(s, gpuigs(N,k));
    if (low_stack(lim, stack_lim(av,2)))
    {
      GEN *gptr[3]; gptr[0]=&c; gptr[1]=&h; gptr[2]=&s;
      if (DEBUGMEM>1) err(warnmem,"bernfrac");
      gerepilemany(av,gptr,3);
    }
  }
}

GEN
bernfrac(long k)
{
  if (!k) return gun;
  if (k==1) return gneg(ghalf);
  if (k<0 || k&1) return gzero;
  return bernfracspec(k);
}

static GEN
bernvec2(long k)
{
  GEN B = cgetg(k+2,t_VEC);
  ulong i;

  for (i=1; i<=k; i++)
    B[i+1]=(long)bernfracspec(i<<1);
  B[1]=un; return B;
}

/* mpbern as exact fractions */
GEN
bernvec(long nb)
{
  long n,m,i,j,d1,d2,av,tetpil;
  GEN  p1,y;

  if (nb < 300) return bernvec2(nb);

  y=cgetg(nb+2,t_VEC); y[1]=un;
  for (i=1; i<=nb; i++)
  {
    av=avma; p1=gzero;
    n=8; m=5; d1=i-1; d2=2*i-3;
    for (j=d1; j>0; j--)
    {
      p1 = gmulsg(n*m, gadd(p1,(GEN)y[j+1]));
      p1 = gdivgs(p1, d1*d2);
      n+=4; m+=2; d1--; d2-=2;
    }
    p1 = gsubsg(1,gdivgs(gaddsg(1,p1),2*i+1));
    tetpil=avma; p1 = gmul2n(p1,-2*i);
    y[i+1] = lpile(av,tetpil,p1);
  }
  return y;
}

/********************************************************************/
/**                                                                **/
/**                      FONCTION GAMMA                            **/
/**                                                                **/
/********************************************************************/

static GEN
mpgamma(GEN x)
{
  GEN y,p1,p2,p3,p4,p5,p6,p7,p71,pitemp;
  long l,l1,l2,u,i,k,e,s,sx,n,p,av,av1;
  double alpha,beta,dk;

  sx=signe(x); if (!sx) err(gamer2);
  l=lg(x); y=cgetr(l); av=avma;

  l2=l+1; p1=cgetr(l2);
  u = (expo(x)<-1 || sx<0);
  if (!u) p2 = x;
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

  p4=realun(l2); setexpo(p4,-1);
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
  if (u)
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
  long l,l1,l2,u,i,k,e,s,n,p,av,av1;
  double alpha,beta,dk;

  l = precision(x); if (!l) l = prec;
  l2 = l+1; y=cgetg(3,t_COMPLEX);
  y[1]=lgetr(l); y[2]=lgetr(l); av=avma;

  p1=cgetg(3,t_COMPLEX); p1[1]=lgetr(l2); p1[2]=lgetr(l2);
  u = (typ(x[1])!=t_REAL && gsigne((GEN)x[1])<=0)? 1: (gexpo((GEN)x[1]) < -1);
  p2 = u? gsub(gun,x): x;
  gaffect(p2,p1);

  alpha=rtodbl(gabs(p1,DEFAULTPREC));
  beta = (bit_accuracy(l)>>1) * LOG2 / PI - alpha;
  if (beta>=0) n=(long)(1 + pariK2*beta); else n=0;
  if (n)
  {
    p = (long)(1+PI*(alpha+n));
    l2 += n>>TWOPOTBITS_IN_LONG;
    p2=cgetg(3,t_COMPLEX); p2[1]=lgetr(l2); p2[2]=lgetr(l2);
    addsrz(n,(GEN)p1[1],(GEN)p2[1]);
    affrr((GEN)p1[2],(GEN)p2[2]);
  }
  else
  {
    dk = pariK4*alpha/(l-2); beta = log(dk)/LOG2;
    if (beta>1.) beta += log(beta)/LOG2;
    p = (long)((bit_accuracy(l)>>1)/beta + 1);
    p2 = p1;
  }
  mpbern(p,l2); p3 = glog(p2,l2);

  p4=cgetg(3,t_COMPLEX);
  p4[1] = (long)realun(l2); setexpo(p4[1],-1);
  p4[2] = (long)rcopy((GEN)p2[2]);
  subrrz((GEN)p2[1],(GEN)p4[1],(GEN)p4[1]);
  gmulz(p4,p3,p4); gsubz(p4,p2,p4);

  pitemp = mppi(l2); setexpo(pitemp,2);
  p7 = mplog(pitemp); setexpo(pitemp,1);
  setexpo(p7,-1); addrrz((GEN)p4[1],p7, (GEN)p4[1]);

  gaffect(ginv(gsqr(p2)), p3); e=gexpo(p3);

  p5=cgetg(3,t_COMPLEX);
  p5[1]=lgetr(l2); setlg(p5[1],4);
  p5[2]=lgetr(l2); setlg(p5[2],4);
  p71=cgetr(l2); p7 = bern(p);
  if (bernzone[2]>4) { setlg(p71,4); affrr(p7,p71); p7=p71; }
  p7 = divrs(p7, 2*p*(2*p-1)); gaffect(p7,p5);

  s=0; l1=4; av1=avma;
  for (k=p-1; k>0; k--)
  {
    setlg(p3[1],l1); setlg(p3[2],l1);
    p6 = gmul(p3,p5); p7 = bern(k);
    if (bernzone[2]>l1) { setlg(p71,l1); affrr(p7,p71); p7=p71; }
    p7 = divrs(p7, (2*k)*(2*k-1));
    s -= e; l1 += (s>>TWOPOTBITS_IN_LONG); if (l1>l2) l1=l2;
    s &= (BITS_IN_LONG-1); p7 = addrr(p7, (GEN)p6[1]);
    setlg(p5[1],l1); affrr(p7, (GEN)p5[1]); p7 = (GEN)p6[2];
    setlg(p5[2],l1); affrr(p7, (GEN)p5[2]); avma=av1;
  }
  setlg(p5[1],l2); setlg(p5[2],l2);
  p6 = gdiv(p5,p2); setlg(p6[1],l2); setlg(p6[2],l2);
  p4 = gadd(p4,p6); setlg(p4[1],l2); setlg(p4[2],l2);
  p4 = gexp(p4,l2);
  for (i=1; i<=n; i++)
  {
    addsrz(-1,(GEN)p2[1],(GEN)p2[1]); p4 = gdiv(p4,p2);
  }
  if (u)
  {
    setlg(pitemp,l+1); p1 = gmul(pitemp,x);
    p4 = gmul(gsin(p1,l+1), p4); p4 = gdiv(pitemp,p4);
  }
  gaffect(p4,y); avma=av; return y;
}

GEN
ggamma(GEN x, long prec)
{
  switch(typ(x))
  {
    case t_INT:
      if (signe(x)<=0) err(gamer2);
      return transc(ggamma,x,prec);

    case t_REAL:
      return mpgamma(x);

    case t_COMPLEX:
      return gcmp0((GEN)x[2])? ggamma((GEN)x[1],prec): cxgamma(x,prec);

    case t_SER:
      return gexp(glngamma(x,prec),prec);

    case t_PADIC:
      err(impl,"p-adic gamma function");
    case t_INTMOD:
      err(typeer,"ggamma");
  }
  return transc(ggamma,x,prec);
}

void
ggammaz(GEN x, GEN y)
{
  long av=avma, prec = precision(y);

  if (!prec) err(infprecer,"ggammaz");
  gaffect(ggamma(x,prec),y); avma=av;
}

static GEN
mplngamma(GEN x)
{
  GEN z,y,p1,p2,p3,p4,p5,p6,p7,p71,pitemp;
  long l,l1,l2,u,i,k,e,f,s,sx,n,p,av,av1;
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

  p4=realun(l2); setexpo(p4,-1);
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
  affrr(p4,y); avma = (long)y; return y;
}

static GEN
cxlngamma(GEN x, long prec)
{
  GEN y,p1,p2,p3,p4,p5,p6,p7,p71,pitemp;
  long l,l1,l2,flag,i,k,e,s,n,p,av,av1;
  double alpha,beta,dk;

  l = precision(x); if (!l) l = prec;
  l2 = l+1; y=cgetg(3,t_COMPLEX);
  y[1]=lgetr(l); y[2]=lgetr(l); av=avma;

  p1=cgetg(3,t_COMPLEX); p1[1]=lgetr(l2); p1[2]=lgetr(l2);

  flag = (typ(x[1]) != t_REAL || gsigne((GEN)x[1]) <= 0);
  if (!flag) flag = (gexpo((GEN)x[1]) < -1);
  if (flag && (gcmp0((GEN)x[2]) || gexpo((GEN)x[2]) > 16)) flag = 0;
  p2 = flag? gsub(gun,x): x;
  gaffect(p2,p1);

  p2=gabs(p1,DEFAULTPREC);
  if (expo(p2)>1000)
  {
    n=0; beta = log(pariK4/(l-2)) / LOG2 + expo(p1);
    beta += log(beta)/LOG2;
    p = (long)((bit_accuracy(l)>>1)/beta + 1);
    p2 = p1;
  }
  else
  {
    alpha=rtodbl(p2); beta = ((bit_accuracy(l)>>1) * LOG2 / PI) - alpha;
    if (beta>=0) n=(long)(1+pariK2*beta); else n=0;
    if (n)
    {
      p = (long)(1+PI*(alpha+n));
      l2 += n>>TWOPOTBITS_IN_LONG;
      p2=cgetg(3,t_COMPLEX); p2[1]=lgetr(l2); p2[2]=lgetr(l2);
      addsrz(n,(GEN)p1[1],(GEN)p2[1]);
      affrr((GEN)p1[2],(GEN)p2[2]);
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

  p4=cgetg(3,t_COMPLEX);
  p4[1] = (long)realun(l2); setexpo(p4[1],-1);
  subrrz((GEN)p2[1],(GEN)p4[1],(GEN)p4[1]);
  p4[2] = (long)rcopy((GEN)p2[2]);
  gmulz(p4,p3,p4); gsubz(p4,p2,p4);

  pitemp = mppi(l2); setexpo(pitemp,2);
  p7 = mplog(pitemp); setexpo(pitemp,1);
  setexpo(p7,-1); addrrz((GEN)p4[1],p7, (GEN)p4[1]);

  gaffect(ginv(gsqr(p2)),p3); e=gexpo(p3);

  p5=cgetg(3,t_COMPLEX);
  p5[1]=lgetr(l2); setlg(p5[1],4);
  p5[2]=lgetr(l2); setlg(p5[2],4);
  p71=cgetr(l2); p7 = bern(p);
  if (bernzone[2]>4) { setlg(p71,4); affrr(p7,p71); p7=p71; }
  p7 = divrs(p7, 2*p*(2*p-1)); gaffect(p7,p5);

  s=0; l1=4; av1=avma;
  for (k=p-1; k>0; k--)
  {
    setlg(p3[1],l1); setlg(p3[2],l1);
    p6 = gmul(p3,p5); p7 = bern(k);
    if (bernzone[2]>l1) { setlg(p71,l1); affrr(p7,p71); p7=p71; }
    p7 = divrs(p7, (2*k)*(2*k-1));
    s -= e; l1 += (s>>TWOPOTBITS_IN_LONG); if (l1>l2) l1=l2;
    s &= (BITS_IN_LONG-1); p7 = addrr(p7, (GEN)p6[1]);
    setlg(p5[1],l1); affrr(p7, (GEN)p5[1]); p7 = (GEN)p6[2];
    setlg(p5[2],l1); affrr(p7, (GEN)p5[2]); avma=av1;
  }
  setlg(p5[1],l2); setlg(p5[2],l2);
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
  affrr((GEN)p4[1], (GEN)y[1]); setlg(p4[2],l+1);

  p1 = subrr(pitemp, (GEN)p4[2]); setexpo(pitemp,2);
  p1 = gfloor(divrr(p1,pitemp));
  p1 = addrr(mulir(p1,pitemp), (GEN)p4[2]);
  affrr(p1, (GEN)y[2]); avma=av; return y;
}

GEN
glngamma(GEN x, long prec)
{
  long i,av,tetpil,n;
  GEN y,p1;

  switch(typ(x))
  {
    case t_INT:
      if (signe(x)<=0) err(gamer2);
      return transc(glngamma,x,prec);

    case t_REAL:
      return mplngamma(x);

    case t_COMPLEX:
      return gcmp0((GEN)x[2])? glngamma((GEN)x[1],prec): cxlngamma(x,prec);

    case t_SER:
      av=avma; if (valp(x)) err(negexper,"glngamma");
      if (!gcmp1((GEN)x[2])) err(impl,"lngamma around a!=1");
      p1=gsubsg(1,x); n=(lg(x)-3)/valp(p1);
      y=ggrando(polx[varn(x)],lg(x)-2);
      for (i=n; i>=2; i--)
	y = gmul(p1,gadd(gdivgs(gzeta(stoi(i),prec),i),y));
      y = gadd(mpeuler(prec),y); tetpil=avma;
      return gerepile(av,tetpil,gmul(p1,y));

    case t_PADIC:
      err(impl,"p-adic lngamma function");
    case t_INTMOD:
      err(typeer,"glngamma");
  }
  return transc(glngamma,x,prec);
}

void
glngammaz(GEN x, GEN y)
{
  long av=avma, prec = precision(y);

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
  long i,j,a,l,av;
  GEN y,p1,p2;

  a = labs(x);
  l = prec+1+(a>>TWOPOTBITS_IN_LONG);
  if (l > LGBITS>>1) err(talker,"argument too large in ggamd");
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
  long av=avma;

  affrr(mpgamd(s,lg(y)),y); avma=av;
}

GEN
ggamd(GEN x, long prec)
{
  long av,tetpil;

  switch(typ(x))
  {
    case t_INT:
      return mpgamd(itos(x),prec);

    case t_REAL: case t_FRAC: case t_FRACN: case t_COMPLEX: case t_QUAD:
      av=avma; x = gadd(x,ghalf); tetpil=avma;
      return gerepile(av,tetpil,ggamma(x,prec));

    case t_INTMOD: case t_PADIC:
      err(typeer,"ggamd");
    case t_SER:
      err(impl,"gamd of a power series");
  }
  return transc(ggamd,x,prec);
}

void
ggamdz(GEN x, GEN y)
{
  long av=avma, prec = precision(y);

  if (!prec) err(infprecer,"ggamdz");
  gaffect(ggamd(x,prec),y); avma=av;
}

/********************************************************************/
/**                                                                **/
/**                      FONCTION PSI                              **/
/**                                                                **/
/********************************************************************/

#if 1
static GEN
mppsi(GEN z)  /* version p=2 */
{
  long l,n,k,x,xx,av,av1,tetpil;
  GEN zk,u,v,a,b;

  av=avma; l=lg(z);
  x=(long)(1 + (bit_accuracy(l)>>1)*LOG2 + 1.58*rtodbl(absr(z)));
  if (expo(z)>=15 || x>46340) err(impl,"psi(x) for x>=29000");
  xx=x*x; n=(long)(1+3.591*x);
  affsr(x,a=cgetr(l));
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
#else
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

  a = cgetr(len);
  affsr(0, a);
  x = cgetr(len);
  affrr(z, x);
  tail = avma;
  while(cmprs(x, num >> 2) < 0) {
    gaddz(a, divsr(1, x), a);
    gaddgsz(x, 1, x);
    avma = tail;
  }

  s = mplog(x);
  gsubz(s, a, s);
  b = gmul2n(x, 1);
  gsubz(s, divsr(1, b), s);

  mpbern(num, len);

  affsr(-1, a);
  gdivgsz(a, 2, a);
  f = mulrr(x, x);
  f = divsr(1, f);
  k = 1;
  do {
    gmulz(a, f, a);
    gdivgsz(a, k, b);
    gmulz(b, bern(k), b);
    gaddz(s, b, s);
    k++;
  } while(expo(s) - expo(b) < num);

  tail = avma;
  return gerepile(head, tail, gcopy(s));
}
#endif

#if 1
static GEN
cxpsi(GEN z, long prec) /* version p=2 */
{
  long l,n,k,x,xx,av,av1,tetpil;
  GEN zk,u,v,a,b,p1;

  l = precision(z); if (!l) l = prec; av=avma;
  x=(long)(1 + (bit_accuracy(l)>>1)*LOG2 + 1.58*rtodbl(gabs(z,DEFAULTPREC)));
  xx=x*x; n=(long)(1+3.591*x);
  a=cgetg(3,t_COMPLEX); a[1]=lgetr(l); a[2]=lgetr(l); gaffsg(x,a);
  b=cgetg(3,t_COMPLEX); b[1]=lgetr(l); b[2]=lgetr(l); gaffsg(1,b);
  u=cgetg(3,t_COMPLEX); u[1]=lgetr(l); u[2]=lgetr(l);
  v=cgetg(3,t_COMPLEX); v[1]=lgetr(l); v[2]=lgetr(l); gaffsg(1,v);
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
#else
GEN
cxpsi(GEN z, long prec) /* by Manfred Radimersky */
{
  long head, tail;
  long bord, nubi, k;
  GEN a, b, f, s, w, wn;

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

  a = cgetg(3, t_COMPLEX);
  a[1] = (long) cgetr(prec);
  a[2] = (long) cgetr(prec);
  gaffsg(0, a);
  w = cgetg(3, t_COMPLEX);
  w[1] = (long) cgetr(prec);
  w[2] = (long) cgetr(prec);
  gaffect(z, w);
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

  tail = avma;
  return gerepile(head, tail, gcopy(s));
}
#endif

GEN
gpsi(GEN x, long prec)
{
  switch(typ(x))
  {
    case t_REAL:
      return mppsi(x);

    case t_COMPLEX:
      return cxpsi(x,prec);

    case t_INTMOD: case t_PADIC:
      err(typeer,"gpsi");
    case t_SER:
      err(impl,"psi of power series");
  }
  return transc(gpsi,x,prec);
}

void
gpsiz(GEN x, GEN y)
{
  long av=avma, prec = precision(y);

  if (!prec) err(infprecer,"gpsiz");
  gaffect(gpsi(x,prec),y); avma=av;
}
