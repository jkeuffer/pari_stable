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
/**                       ELLIPTIC CURVES                          **/
/**                                                                **/
/********************************************************************/
#include "pari.h"

void
checkpt(GEN z)
{
  if (typ(z)!=t_VEC) err(elliper1);
}

long
checkell(GEN e)
{
  long lx=lg(e);
  if (typ(e)!=t_VEC || lx<14) err(elliper1);
  return lx;
}

void
checkbell(GEN e)
{
  if (typ(e)!=t_VEC || lg(e)<20) err(elliper1);
}

void
checksell(GEN e)
{
  if (typ(e)!=t_VEC || lg(e)<6) err(elliper1);
}

static void
checkch(GEN z)
{
  if (typ(z)!=t_VEC || lg(z)!=5) err(elliper1);
}

/* 4 X^3 + b2 X^2 + 2b4 X + b6 */
static GEN
RHSpol(GEN e)
{
  GEN z = cgetg(6, t_POL); z[1] = evalsigne(1)|evallgef(6);
  z[2] = e[8];
  z[3] = lmul2n((GEN)e[7],1);
  z[4] = e[6];
  z[5] = lstoi(4); return z;
}

/* x^3 + a2 x^2 + a4 x + a6 */
static GEN
ellRHS(GEN e, GEN x)
{
  GEN p1;
  p1 = gadd((GEN)e[2],x);
  p1 = gadd((GEN)e[4], gmul(x,p1));
  p1 = gadd((GEN)e[5], gmul(x,p1));
  return p1;
}

/* a1 x + a3 */
static GEN
ellLHS0(GEN e, GEN x)
{
  return gcmp0((GEN)e[1])? (GEN)e[3]: gadd((GEN)e[3], gmul(x,(GEN)e[1]));
}

static GEN
ellLHS0_i(GEN e, GEN x)
{
  return signe(e[1])? addii((GEN)e[3], mulii(x, (GEN)e[1])): (GEN)e[3];
}

/* y^2 + a1 xy + a3 y */
static GEN
ellLHS(GEN e, GEN z)
{
  GEN y = (GEN)z[2];
  return gmul(y, gadd(y, ellLHS0(e,(GEN)z[1])));
}

/* 2y + a1 x + a3 */
static GEN
d_ellLHS(GEN e, GEN z)
{
  return gadd(ellLHS0(e, (GEN)z[1]), gmul2n((GEN)z[2],1));
}

static void
smallinitell0(GEN x, GEN y)
{
  GEN b2,b4,b6,b8,d,j,a11,a13,a33,a64,b81,b22,c4,c6;
  long i;

  checksell(x); for (i=1; i<=5; i++) y[i]=x[i];

  b2=gadd(a11=gsqr((GEN)y[1]),gmul2n((GEN)y[2],2));
  y[6]=(long)b2;

  b4=gadd(a13=gmul((GEN)y[1],(GEN)y[3]),gmul2n((GEN)y[4],1));
  y[7]=(long)b4;

  b6=gadd(a33=gsqr((GEN)y[3]),a64=gmul2n((GEN)y[5],2));
  y[8]=(long)b6;

  b81=gadd(gadd(gmul(a11,(GEN)y[5]),gmul(a64,(GEN)y[2])),gmul((GEN)y[2],a33));
  b8=gsub(b81,gmul((GEN)y[4],gadd((GEN)y[4],a13)));
  y[9]=(long)b8;

  c4=gadd(b22=gsqr(b2),gmulsg(-24,b4));
  y[10]=(long)c4;

  c6=gadd(gmul(b2,gsub(gmulsg(36,b4),b22)),gmulsg(-216,b6));
  y[11]=(long)c6;

  b81=gadd(gmul(b22,b8),gmulsg(27,gsqr(b6)));
  d=gsub(gmul(b4,gadd(gmulsg(9,gmul(b2,b6)),gmulsg(-8,gsqr(b4)))),b81);
  y[12]=(long)d;

  if (gcmp0(d)) err(talker,"singular curve in ellinit");

  j = gdiv(gmul(gsqr(c4),c4),d);
  y[13]=(long)j;
}

GEN
smallinitell(GEN x)
{
  ulong av = avma;
  GEN y = cgetg(14,t_VEC);
  smallinitell0(x,y); return gerepilecopy(av,y);
}

GEN
ellinit0(GEN x, long flag,long prec)
{
  switch(flag)
  {
    case 0: return initell(x,prec);
    case 1: return smallinitell(x);
    default: err(flagerr,"ellinit");
  }
  return NULL; /* not reached */
}

void
ellprint(GEN e)
{
  long av = avma;
  long vx = fetch_var();
  long vy = fetch_var();
  GEN z = cgetg(3,t_VEC);
  if (typ(e) != t_VEC || lg(e) < 6)
    err(talker, "not an elliptic curve in ellprint");
  z[1] = lpolx[vx]; name_var(vx, "X");
  z[2] = lpolx[vy]; name_var(vy, "Y");
  fprintferr("%Z - (%Z)\n", ellLHS(e, z), ellRHS(e, polx[vx]));
  (void)delete_var();
  (void)delete_var(); avma = av;
}

static GEN
do_agm(GEN *ptx1, GEN a1, GEN b1, long prec, long sw)
{
  GEN p1,r1,a,b,x,x1;
  long G;

  x1 = gmul2n(gsub(a1,b1),-2);
  if (gcmp0(x1))
    err(precer,"initell");
  G = 6 - bit_accuracy(prec);
  for(;;)
  {
    a=a1; b=b1; x=x1;
    b1=gsqrt(gmul(a,b),prec); setsigne(b1,sw);
    a1=gmul2n(gadd(gadd(a,b),gmul2n(b1,1)),-2);
    r1=gsub(a1,b1);
    p1=gsqrt(gdiv(gadd(x,r1),x),prec);
    x1=gmul(x,gsqr(gmul2n(gaddsg(1,p1),-1)));
    if (gcmp0(r1) || gexpo(r1) <= G + gexpo(b1)) break;
  }
  if (gprecision(x1)*2 <= (prec+2))
    err(precer,"initell");
  *ptx1 = x1; return ginv(gmul2n(a1,2));
}

static GEN
do_padic_agm(GEN *ptx1, GEN a1, GEN b1, GEN p)
{
  GEN p1,r1,a,b,x,bmod1, bmod = modii((GEN)b1[4],p), x1 = *ptx1;

  if (!x1) x1 = gmul2n(gsub(a1,b1),-2);
  for(;;)
  {
    a=a1; b=b1; x=x1;
    b1=gsqrt(gmul(a,b),0); bmod1=modii((GEN)b1[4],p);
    if (!egalii(bmod1,bmod)) b1 = gneg_i(b1);
    a1=gmul2n(gadd(gadd(a,b),gmul2n(b1,1)),-2);
    r1=gsub(a1,b1);
    p1=gsqrt(gdiv(gadd(x,r1),x),0);
    if (! gcmp1(modii((GEN)p1[4],p))) p1 = gneg_i(p1);
    x1=gmul(x,gsqr(gmul2n(gaddsg(1,p1),-1)));
    if (gcmp0(r1)) break;
  }
  *ptx1 = x1; return ginv(gmul2n(a1,2));
}

static GEN
padic_initell(GEN y, GEN p, long prec)
{
  GEN b2,b4,c4,c6,p1,p2,w,pv,a1,b1,x1,u2,q,e0,e1;
  long i,alpha;

  if (valp(y[13]) >= 0) /* p | j */
    err(talker,"valuation of j must be negative in p-adic ellinit");
  if (egalii(p,gdeux))
    err(impl,"initell for 2-adic numbers"); /* pv=stoi(4); */

  pv=p; q=ggrandocp(p,prec);
  for (i=1; i<=5; i++) y[i]=ladd(q,(GEN)y[i]);
  b2= (GEN)y[6];
  b4= (GEN)y[7];
  c4= (GEN)y[10];
  c6= (GEN)y[11];
  alpha=valp(c4)>>1;
  setvalp(c4,0);
  setvalp(c6,0); e1=gdivgs(gdiv(c6,c4),6);
  c4=gdivgs(c4,48); c6=gdivgs(c6,864);
  do
  {
    e0=e1; p2=gsqr(e0);
    e1=gdiv(gadd(gmul2n(gmul(e0,p2),1),c6), gsub(gmulsg(3,p2),c4));
  }
  while (!gegal(e0,e1));
  setvalp(e1,valp(e1)+alpha);

  e1=gsub(e1,gdivgs(b2,12));
  w=gsqrt(gmul2n(gadd(b4,gmul(e1,gadd(b2,gmulsg(6,e1)))),1),0);

  p1=gaddgs(gdiv(gmulsg(3,e0),w),1);
  if (valp(p1)<=0) w=gneg_i(w);
  y[18]=(long)w;

  a1=gmul2n(gsub(w,gadd(gmulsg(3,e1),gmul2n(b2,-2))),-2);
  b1=gmul2n(w,-1); x1=NULL;
  u2 = do_padic_agm(&x1,a1,b1,pv);

  w = gaddsg(1,ginv(gmul2n(gmul(u2,x1),1)));
  w = gadd(w,gsqrt(gaddgs(gsqr(w),-1),0));
  if (gcmp0(w)) err(precer,"initell");
  q=ginv(w);
  if (valp(q)<0) q=ginv(q);

  p1=cgetg(2,t_VEC); p1[1]=(long)e1;
  y[14]=(long)p1;
  y[15]=(long)u2;
  y[16] = (kronecker((GEN)u2[4],p) <= 0 || (valp(u2)&1))? zero: lsqrt(u2,0);
  y[17]=(long)q;
  y[19]=zero; return y;
}

static int
invcmp(GEN x, GEN y) { return -gcmp(x,y); }

static GEN
initell0(GEN x, long prec)
{
  GEN b2,b4,D,p1,p2,p,w,a1,b1,x1,u2,q,e1,pi,pi2,tau,w1,w2;
  GEN y = cgetg(20,t_VEC);
  long ty,i,e,sw;

  smallinitell0(x,y);

  e = BIGINT; p = NULL;
  for (i=1; i<=5; i++)
  {
    q = (GEN)y[i];
    if (typ(q)==t_PADIC)
    {
      long e2 = signe(q[4])? precp(q)+valp(q): valp(q);
      if (e2 < e) e = e2;
      if (!p) p = (GEN)q[2];
      else if (!egalii(p,(GEN)q[2]))
        err(talker,"incompatible p-adic numbers in initell");
    }
  }
  if (e<BIGINT) return padic_initell(y,p,e);

  b2= (GEN)y[6];
  b4= (GEN)y[7];
  D = (GEN)y[12]; ty = typ(D);
  if (!prec || !is_const_t(ty) || ty==t_INTMOD)
    { y[14]=y[15]=y[16]=y[17]=y[18]=y[19]=zero; return y; }

  p1 = roots(RHSpol(y),prec);
  if (gsigne(D) < 0) p1[1] = lreal((GEN)p1[1]);
  else /* sort roots in decreasing order */
    p1 = gen_sort(greal(p1), 0, invcmp);
  y[14]=(long)p1;

  e1 = (GEN)p1[1];
  w  = gsqrt(gmul2n(gadd(b4,gmul(e1,gadd(b2,gmulsg(6,e1)))),1),prec);
  p2 = gadd(gmulsg(3,e1), gmul2n(b2,-2));
  if (gsigne(p2) > 0) w = gneg_i(w);
  a1 = gmul2n(gsub(w,p2),-2);
  b1 = gmul2n(w,-1); sw = signe(w);
  u2 = do_agm(&x1,a1,b1,prec,sw);

  w = gaddsg(1,ginv(gmul2n(gmul(u2,x1),1)));
  q = gsqrt(gaddgs(gsqr(w),-1),prec);
  if (gsigne(greal(w))>0)
    q = ginv(gadd(w,q));
  else
    q = gsub(w,q);
  if (gexpo(q) >= 0) q = ginv(q);
  pi = mppi(prec); pi2 = gmul2n(pi,1);
  tau = gmul(gdiv(glog(q,prec),pi2), gneg_i(gi));

  y[19] = lmul(gmul(gsqr(pi2),gabs(u2,prec)), gimag(tau));
  w1 = gmul(pi2,gsqrt(gneg_i(u2),prec));
  w2 = gmul(tau,w1);
  if (sw < 0)
    q = gsqrt(q,prec);
  else
  {
    w1= gmul2n(gabs((GEN)w2[1],prec),1);
    q = gexp(gmul2n(gmul(gmul(pi2,gi),gdiv(w2,w1)), -1), prec);
  }
  y[15] = (long)w1;
  y[16] = (long)w2;
  p1 = gdiv(gsqr(pi),gmulsg(6,w1));
  p2 = thetanullk(q,1,prec);
  if (gcmp0(p2)) err(precer,"initell");
  y[17] = lmul(p1,gdiv(thetanullk(q,3,prec),p2));
  y[18] = ldiv(gsub(gmul((GEN)y[17],w2),gmul(gi,pi)), w1);
  return y;
}

GEN
initell(GEN x, long prec)
{
  ulong av = avma;
  return gerepilecopy(av, initell0(x,prec));
}

GEN
coordch(GEN e, GEN ch)
{
  GEN y,p1,p2,v,v2,v3,v4,v6,r,s,t,u;
  long i,lx = checkell(e);
  ulong av = avma;

  checkch(ch);
  u=(GEN)ch[1]; r=(GEN)ch[2]; s=(GEN)ch[3]; t=(GEN)ch[4];
  y=cgetg(lx,t_VEC);
  v=ginv(u); v2=gsqr(v); v3=gmul(v,v2);v4=gsqr(v2); v6=gsqr(v3);
  y[1] = lmul(v,gadd((GEN)e[1],gmul2n(s,1)));
  y[2] = lmul(v2,gsub(gadd((GEN)e[2],gmulsg(3,r)),gmul(s,gadd((GEN)e[1],s))));
  p2 = ellLHS0(e,r);
  p1 = gadd(gmul2n(t,1), p2);
  y[3] = lmul(v3,p1);
  p1 = gsub((GEN)e[4],gadd(gmul(t,(GEN)e[1]),gmul(s,p1)));
  y[4] = lmul(v4,gadd(p1,gmul(r,gadd(gmul2n((GEN)e[2],1),gmulsg(3,r)))));
  p2 = gmul(t,gadd(t, p2));
  y[5] = lmul(v6,gsub(ellRHS(e,r),p2));
  y[6] = lmul(v2,gadd((GEN)e[6],gmulsg(12,r)));
  y[7] = lmul(v4,gadd((GEN)e[7],gmul(r,gadd((GEN)e[6],gmulsg(6,r)))));
  y[8] = lmul(v6,gadd((GEN)e[8],gmul(r,gadd(gmul2n((GEN)e[7],1),gmul(r,gadd((GEN)e[6],gmul2n(r,2)))))));
  p1 = gadd(gmulsg(3,(GEN)e[7]),gmul(r,gadd((GEN)e[6],gmulsg(3,r))));
  y[9] = lmul(gsqr(v4),gadd((GEN)e[9],gmul(r,gadd(gmulsg(3,(GEN)e[8]),gmul(r,p1)))));
  y[10] = lmul(v4,(GEN)e[10]);
  y[11] = lmul(v6,(GEN)e[11]);
  y[12] = lmul(gsqr(v6),(GEN)e[12]);
  y[13] = e[13];
  if (lx>14)
  {
    p1=(GEN)e[14];
    if (gcmp0(p1))
    {
      y[14] = y[15] = y[16] = y[17] = y[18] = y[19] = zero;
    }
    else
    {
      if (typ(e[1])==t_PADIC)
      {
        p2=cgetg(2,t_VEC); p2[1]=lmul(v2,gsub((GEN)p1[1],r));
        y[14]=(long)p2;
        y[15]=lmul(gsqr(u),(GEN)e[15]);
        y[16]=lmul(u,(GEN)e[16]);
/* FIXME: how do q and w change ??? */
        y[17]=e[17];
        y[18]=e[18];
        y[19]=zero;
      }
      else
      {
        p2=cgetg(4,t_COL);
        for (i=1; i<=3; i++) p2[i]=lmul(v2,gsub((GEN)p1[i],r));
        y[14]=(long)p2;
        y[15]=lmul(u,(GEN)e[15]);
        y[16]=lmul(u,(GEN)e[16]);
        y[17]=ldiv((GEN)e[17],u);
        y[18]=ldiv((GEN)e[18],u);
        y[19]=lmul(gsqr(u),(GEN)e[19]);
      }
    }
  }
  return gerepilecopy(av,y);
}

static GEN
pointch0(GEN x, GEN v2, GEN v3, GEN mor, GEN s, GEN t)
{
  GEN p1,z;

  if (lg(x) < 3) return x;

  z = cgetg(3,t_VEC); p1=gadd((GEN)x[1],mor);
  z[1] = lmul(v2,p1);
  z[2] = lmul(v3,gsub((GEN)x[2],gadd(gmul(s,p1),t)));
  return z;
}

GEN
pointch(GEN x, GEN ch)
{
  GEN y,v,v2,v3,mor,r,s,t,u;
  long tx,lx=lg(x),i;
  ulong av = avma;

  checkpt(x); checkch(ch);
  if (lx < 2) return gcopy(x);
  u=(GEN)ch[1]; r=(GEN)ch[2]; s=(GEN)ch[3]; t=(GEN)ch[4];
  tx=typ(x[1]); v=ginv(u); v2=gsqr(v); v3=gmul(v,v2); mor=gneg_i(r);
  if (is_matvec_t(tx))
  {
    y=cgetg(lx,tx);
    for (i=1; i<lx; i++)
      y[i]=(long) pointch0((GEN)x[i],v2,v3,mor,s,t);
  }
  else
    y = pointch0(x,v2,v3,mor,s,t);
  return gerepilecopy(av,y);
}

/* Exactness of lhs and rhs in the following depends in non-obvious ways
   on the coeffs of the curve as well as on the components of the point z.
   Thus if e is exact, with a1==0, and z has exact y coordinate only, the
   lhs will be exact but the rhs won't. */
int
oncurve(GEN e, GEN z)
{
  GEN p1,p2,x;
  long av=avma,p,q;

  checksell(e); checkpt(z); if (lg(z)<3) return 1; /* oo */
  p1 = ellLHS(e,z);
  p2 = ellRHS(e,(GEN)z[1]); x = gsub(p1,p2);
  if (gcmp0(x)) { avma=av; return 1; }
  p = precision(p1);
  q = precision(p2);
  if (!p && !q) { avma=av; return 0; } /* both of p1, p2 are exact */
  if (!q || (p && p < q)) q = p; /* min among nonzero elts of {p,q} */
  q = (gexpo(x) < gexpo(p1) - bit_accuracy(q) + 15);
  avma = av; return q;
}

GEN
addell(GEN e, GEN z1, GEN z2)
{
  GEN p1,p2,x,y,x1,x2,y1,y2;
  long av=avma,tetpil;

  checksell(e); checkpt(z1); checkpt(z2);
  if (lg(z1)<3) return gcopy(z2);
  if (lg(z2)<3) return gcopy(z1);

  x1=(GEN)z1[1]; y1=(GEN)z1[2];
  x2=(GEN)z2[1]; y2=(GEN)z2[2];
  if (x1 == x2 || gegal(x1,x2))
  { /* y1 = y2 or -LHS0-y2 */
    if (y1 != y2)
    {
      int eq;
      if (precision(y1) || precision(y2))
        eq = (gexpo(gadd(ellLHS0(e,x1),gadd(y1,y2))) >= gexpo(y1));
      else
        eq = gegal(y1,y2);
      if (!eq) { avma=av; y=cgetg(2,t_VEC); y[1]=zero; return y; }
    }
    p2 = d_ellLHS(e,z1);
    if (gcmp0(p2)) { avma=av; y=cgetg(2,t_VEC); y[1]=zero; return y; }
    p1 = gadd(gsub((GEN)e[4],gmul((GEN)e[1],y1)),
              gmul(x1,gadd(gmul2n((GEN)e[2],1),gmulsg(3,x1))));
  }
  else { p1=gsub(y2,y1); p2=gsub(x2,x1); }
  p1 = gdiv(p1,p2);
  x = gsub(gmul(p1,gadd(p1,(GEN)e[1])), gadd(gadd(x1,x2),(GEN)e[2]));
  y = gadd(gadd(y1, ellLHS0(e,x)), gmul(p1,gsub(x,x1)));
  tetpil=avma; p1=cgetg(3,t_VEC); p1[1]=lcopy(x); p1[2]=lneg(y);
  return gerepile(av,tetpil,p1);
}

static GEN
invell(GEN e, GEN z)
{
  GEN p1;

  if (lg(z)<3) return z;
  p1=cgetg(3,t_VEC); p1[1]=z[1];
  p1[2]=(long)gneg_i(gadd((GEN)z[2], ellLHS0(e,(GEN)z[1])));
  return p1;
}

GEN
subell(GEN e, GEN z1, GEN z2)
{
  long av=avma,tetpil;

  checksell(e); checkpt(z2);
  z2=invell(e,z2); tetpil=avma;
  return gerepile(av,tetpil,addell(e,z1,z2));
}

GEN
ordell(GEN e, GEN x, long prec)
{
  long av=avma,td,i,lx,tx=typ(x);
  GEN D,a,b,d,pd,p1,y;

  checksell(e);
  if (is_matvec_t(tx))
  {
    lx=lg(x); y=cgetg(lx,tx);
    for (i=1; i<lx; i++) y[i]=(long)ordell(e,(GEN)x[i],prec);
    return y;
  }

  a=ellRHS(e,x);
  b=ellLHS0(e,x); /* y*(y+b) = a */
  D=gadd(gsqr(b),gmul2n(a,2)); td=typ(D);
  if (gcmp0(D))
  {
    b = gneg_i(b);
    y = cgetg(2,t_VEC);
    if (td == t_INTMOD && egalii((GEN)D[1], gdeux))
      y[1] = (long)gmodulss(gcmp0(a)?0:1, 2);
    else
      y[1] = lmul2n(b,-1);
    return gerepileupto(av,y);
  }

  if (td==t_INT || is_frac_t(td))
  {
    pd = (td==t_INT)? NULL: (GEN)D[2];
    if (pd) D = mulii((GEN)D[1],pd);
    if (!carrecomplet(D,&d)) { avma=av; return cgetg(1,t_VEC); }
    if (pd) d = gdiv(d,pd);
  }
  else
  {
    if (td==t_INTMOD)
    {
      if (egalii((GEN)D[1],gdeux))
      {
        avma=av;
        if (!gcmp0(a)) return cgetg(1,t_VEC);
        y = cgetg(3,t_VEC);
        y[1] = (long)gmodulss(0,2);
        y[2] = (long)gmodulss(1,2); return y;
      }
      if (kronecker((GEN)D[2],(GEN)D[1]) == -1)
        { avma=av; return cgetg(1,t_VEC); }
    }
    d = gsqrt(D,prec);
  }
  p1=gsub(d,b); y = cgetg(3,t_VEC);
  y[1] = lmul2n(p1,-1);
  y[2] = lsub((GEN)y[1],d);
  return gerepileupto(av,y);
}

static GEN
CM_powell(GEN e, GEN z, GEN n)
{
  GEN x,y,p0,p1,q0,q1,p2,q2,z1,z2,pol,grdx;
  long av=avma,tetpil,ln,ep,vn;

  if (lg(z)<3) return gcopy(z);
  pol=(GEN)n[1];
  if (signe(discsr(pol))>=0)
    err(talker,"not a negative quadratic discriminant in CM");
  if (!gcmp1(denom((GEN)n[2])) || !gcmp1(denom((GEN)n[3])))
    err(impl,"powell for nonintegral CM exponent");

  p1=gaddgs(gmul2n(gnorm(n),2),4);
  if (gcmpgs(p1,(((ulong)MAXULONG)>>1)) > 0)
    err(talker,"norm too large in CM");
  ln=itos(p1); vn=(ln-4)>>2;
  z1 = weipell(e,ln);
  z2 = gsubst(z1,0,gmul(n,polx[0]));
  grdx=gadd((GEN)z[1],gdivgs((GEN)e[6],12));
  p0=gzero; p1=gun;
  q0=gun; q1=gzero;
  do
  {
    GEN ss=gzero;
    do
    {
      ep=(-valp(z2))>>1; ss=gadd(ss,gmul((GEN)z2[2],gpuigs(polx[0],ep)));
      z2=gsub(z2,gmul((GEN)z2[2],gpuigs(z1,ep)));
    }
    while (valp(z2)<=0);
    p2=gadd(p0,gmul(ss,p1)); p0=p1; p1=p2;
    q2=gadd(q0,gmul(ss,q1)); q0=q1; q1=q2;
    if (!signe(z2)) break;
    z2=ginv(z2);
  }
  while (degpol(p1) < vn);
  if (degpol(p1) > vn || signe(z2))
    err(talker,"not a complex multiplication in powell");
  x=gdiv(p1,q1); y=gdiv(deriv(x,0),n);
  x=gsub(poleval(x,grdx), gdivgs((GEN)e[6],12));
  y=gsub(gmul(d_ellLHS(e,z),poleval(y,grdx)), ellLHS0(e,x));
  tetpil=avma; z=cgetg(3,t_VEC); z[1]=lcopy(x); z[2]=lmul2n(y,-1);
  return gerepile(av,tetpil,z);
}

GEN
powell(GEN e, GEN z, GEN n)
{
  GEN y;
  long av=avma,i,j,tetpil,s;
  ulong m;

  checksell(e); checkpt(z);
  if (typ(n)==t_QUAD) return CM_powell(e,z,n);
  if (typ(n)!=t_INT)
    err(impl,"powell for nonintegral or non CM exponents");
  if (lg(z)<3) return gcopy(z);
  s=signe(n);
  if (!s) { y=cgetg(2,t_VEC); y[1]=zero; return y; }
  if (s < 0) { n=negi(n); z = invell(e,z); }
  if (is_pm1(n)) return gerepilecopy(av,z);

  y=cgetg(2,t_VEC); y[1]=zero;
  for (i=lgefint(n)-1; i>2; i--)
    for (m=n[i],j=0; j<BITS_IN_LONG; j++,m>>=1)
    {
      if (m&1) y = addell(e,y,z);
      z = addell(e,z,z);
    }
  for (m=n[2]; m>1; m>>=1)
  {
    if (m&1) y = addell(e,y,z);
    z = addell(e,z,z);
  }
  tetpil=avma; return gerepile(av,tetpil,addell(e,y,z));
}

GEN
mathell(GEN e, GEN x, long prec)
{
  GEN y,p1,p2, *pdiag;
  long lx=lg(x),i,j,tx=typ(x);
  ulong av = avma;

  if (!is_vec_t(tx)) err(elliper1);
  lx=lg(x); y=cgetg(lx,t_MAT); pdiag=(GEN*) new_chunk(lx);
  for (i=1; i<lx; i++)
  {
    pdiag[i]=ghell(e,(GEN)x[i],prec);
    y[i]=lgetg(lx,t_COL);
  }
  for (i=1; i<lx; i++)
  {
    p1=(GEN)y[i]; p1[i]=lmul2n(pdiag[i],1);
    for (j=i+1; j<lx; j++)
    {
      p2=ghell(e,addell(e,(GEN)x[i],(GEN)x[j]),prec);
      p2=gsub(p2, gadd(pdiag[i],pdiag[j]));
      p1[j]=(long)p2; coeff(y,i,j)=(long)p2;
    }
  }
  return gerepilecopy(av,y);
}

static GEN
bilhells(GEN e, GEN z1, GEN z2, GEN h2, long prec)
{
  long lz1=lg(z1),tx,av=avma,tetpil,i;
  GEN y,p1,p2;

  if (lz1==1) return cgetg(1,typ(z1));

  tx=typ(z1[1]);
  if (!is_matvec_t(tx))
  {
    p1 = ghell(e,addell(e,z1,z2),prec);
    p2 = gadd(ghell(e,z1,prec),h2);
    tetpil=avma; return gerepile(av,tetpil,gsub(p1,p2));
  }
  y=cgetg(lz1,typ(z1));
  for (i=1; i<lz1; i++)
    y[i]=(long)bilhells(e,(GEN)z1[i],z2,h2,prec);
  return y;
}

GEN
bilhell(GEN e, GEN z1, GEN z2, long prec)
{
  GEN p1,h2;
  long av=avma,tetpil,tz1=typ(z1),tz2=typ(z2);

  if (!is_matvec_t(tz1) || !is_matvec_t(tz2)) err(elliper1);
  if (lg(z1)==1) return cgetg(1,tz1);
  if (lg(z2)==1) return cgetg(1,tz2);

  tz1=typ(z1[1]); tz2=typ(z2[1]);
  if (is_matvec_t(tz2))
  {
    if (is_matvec_t(tz1))
      err(talker,"two vector/matrix types in bilhell");
    p1=z1; z1=z2; z2=p1;
  }
  h2=ghell(e,z2,prec); tetpil=avma;
  return gerepile(av,tetpil,bilhells(e,z1,z2,h2,prec));
}

static GEN
new_coords(GEN e, GEN x, GEN *pta, GEN *ptb, long prec)
{
  GEN a,b,r0,r1,p1,p2,w, e1 = gmael(e,14,1), b2 = (GEN)e[6];
  long ty = typ(e[12]);

  r0 = gmul2n(b2,-2);
  p2 = gadd(gmulsg(3,e1),r0);
  if (ty == t_PADIC)
    w = (GEN)e[18];
  else
  {
    GEN b4 = (GEN)e[7];
    if (!is_const_t(ty)) err(typeer,"zell");

    /* w = sqrt(2b4 + 2b2 e1 + 12 e1^2) */
    w = gsqrt(gmul2n(gadd(b4, gmul(e1,gadd(b2,gmulsg(6,e1)))),1),prec);
    if (gsigne(greal(p2)) > 0) w = gneg_i(w);
  }
  a = gmul2n(gsub(w,p2),-2);
  b = gmul2n(w,-1);
  r1 = gsub(a,b);
  p1 = gadd(x, gmul2n(gadd(e1,r0),-1));
  p1 = gmul2n(p1,-1);
  p1 = gadd(p1, gsqrt(gsub(gsqr(p1), gmul(a,r1)), prec));
  *pta = a; *ptb = b;
  return gmul(p1,gsqr(gmul2n(gaddsg(1,gsqrt(gdiv(gadd(p1,r1),p1),prec)),-1)));
}

GEN
zell(GEN e, GEN z, long prec)
{
  long av=avma,ty,sw,fl;
  GEN t,u,p1,p2,a,b,x1,u2,D = (GEN)e[12];

  checkbell(e);
  if (!oncurve(e,z)) err(heller1);
  ty=typ(D);
  if (ty==t_INTMOD) err(typeer,"zell");
  if (lg(z)<3) return (ty==t_PADIC)? gun: gzero;

  x1 = new_coords(e,(GEN)z[1],&a,&b,prec);
  if (ty==t_PADIC)
  {
    u2 = do_padic_agm(&x1,a,b,(GEN)D[2]);
    if (!gcmp0((GEN)e[16]))
    {
      t=gsqrt(gaddsg(1,gdiv(x1,a)),prec);
      t=gdiv(gaddsg(-1,t),gaddsg(1,t));
    }
    else t=gaddsg(2,ginv(gmul(u2,x1)));
    return gerepileupto(av,t);
  }

  sw = gsigne(greal(b)); fl=0;
  for(;;) /* agm */
  {
    GEN a0=a, b0=b, x0=x1, r1;

    b = gsqrt(gmul(a0,b0),prec);
    if (gsigne(greal(b)) != sw) b = gneg_i(b);
    a = gmul2n(gadd(gadd(a0,b0),gmul2n(b,1)),-2);
    r1 = gsub(a,b);
    if (gcmp0(r1) || gexpo(r1) < gexpo(a) - bit_accuracy(prec)) break;
    p1 = gsqrt(gdiv(gadd(x0,r1),x0),prec);
    x1 = gmul(x0,gsqr(gmul2n(gaddsg(1,p1),-1)));
    r1 = gsub(x1,x0);
    if (gcmp0(r1) || gexpo(r1) < gexpo(x1) - bit_accuracy(prec) + 5)
    {
      if (fl) break;
      fl = 1;
    }
    else fl = 0;
  }
  u = gdiv(x1,a); t = gaddsg(1,u);
  if (gcmp0(t) || gexpo(t) <  5 - bit_accuracy(prec))
    t = negi(gun);
  else
    t = gdiv(u,gsqr(gaddsg(1,gsqrt(t,prec))));
  u = gsqrt(ginv(gmul2n(a,2)),prec);
  t = gmul(u, glog(t,prec));

  /* which square root? test the reciprocal function (pointell) */
  if (!gcmp0(t))
  {
    GEN z1,z2;
    int bad;

    z1 = pointell(e,t,3); /* we don't need much precision */
    /* Either z = z1 (ok: keep t), or z = z2 (bad: t <-- -t) */
    z2 = invell(e, z1);
    bad = (gexpo(gsub(z,z1)) > gexpo(gsub(z,z2)));
    if (bad) t = gneg(t);
    if (DEBUGLEVEL)
    {
      if (DEBUGLEVEL>4)
      {
        fprintferr("  z  = %Z\n",z);
        fprintferr("  z1 = %Z\n",z1);
        fprintferr("  z2 = %Z\n",z2);
      }
      fprintferr("ellpointtoz: %s square root\n", bad? "bad": "good");
      flusherr();
    }
  }
  /* send t to the fundamental domain if necessary */
  p2 = gdiv(gimag(t),gmael(e,16,2));
  p1 = gsub(p2, gmul2n(gun,-2));
  if (gcmp(gabs(p1,prec),ghalf) >= 0)
    t = gsub(t, gmul((GEN)e[16],gfloor(gadd(p2,dbltor(0.1)))));
  if (gsigne(greal(t)) < 0) t = gadd(t,(GEN)e[15]);
  return gerepileupto(av,t);
}

/* compute gamma in SL_2(Z) and t'=gamma(t) so that t' is in the usual
   fundamental domain. Internal function no check, no garbage. */
static GEN
getgamma(GEN *ptt)
{
  GEN t = *ptt,a,b,c,d,n,m,p1,p2,run;

  run = gsub(realun(DEFAULTPREC), gpuigs(stoi(10),-8));
  a=d=gun; b=c=gzero;
  for(;;)
  {
    n = ground(greal(t));
    if (signe(n))
    { /* apply T^n */
      n = negi(n); t = gadd(t,n);
      a = addii(a, mulii(n,c));
      b = addii(b, mulii(n,d));
    }
    m = gnorm(t); if (gcmp(m,run) >= 0) break;
    t = gneg_i(gdiv(gconj(t),m)); /* apply S */
    p1=negi(c); c=a; a=p1;
    p1=negi(d); d=b; b=p1;
  }
  m=cgetg(3,t_MAT); *ptt = t;
  p1=cgetg(3,t_COL); m[1]=(long)p1;
  p2=cgetg(3,t_COL); m[2]=(long)p2;
  p1[1]=(long)a; p2[1]=(long)b;
  p1[2]=(long)c; p2[2]=(long)d; return m;
}

static GEN
get_tau(GEN *ptom1, GEN *ptom2, GEN *ptga)
{
  GEN om1 = *ptom1, om2 = *ptom2, tau = gdiv(om1,om2);
  long s = gsigne(gimag(tau));
  if (!s)
    err(talker,"omega1 and omega2 R-linearly dependent in elliptic function");
  if (s < 0) { *ptom1=om2; *ptom2=om1; tau=ginv(tau); }
  *ptga = getgamma(&tau); return tau;
}

static int
get_periods(GEN e, GEN *om1, GEN *om2)
{
  long tx = typ(e);
  if (is_vec_t(tx))
    switch(lg(e))
    {
      case  3: *om1=(GEN)e[1];  *om2=(GEN)e[2]; return 1;
      case 20: *om1=(GEN)e[16]; *om2=(GEN)e[15]; return 1;
    }
  return 0;
}

extern GEN PiI2(long prec);

/* computes the numerical values of eisenstein series. k is equal to a positive
   even integer. If k=4 or 6, computes g2 or g3. If k=2, or k>6 even,
   compute (2iPi/om2)^k*(1+2/zeta(1-k)*sum(n>=1,n^(k-1)q^n/(1-q^n)) with no
   constant factor. */
GEN
elleisnum(GEN om, long k, long flag, long prec)
{
  long av=avma,lim,av1;
  GEN om1,om2,p1,pii2,tau,q,y,qn,ga,court,asub = NULL; /* gcc -Wall */

  if (k%2 || k<=0) err(talker,"k not a positive even integer in elleisnum");
  if (!get_periods(om, &om1, &om2)) err(typeer,"elleisnum");
  pii2 = PiI2(prec);
  tau = get_tau(&om1,&om2, &ga);
  if (k==2) asub=gdiv(gmul(pii2,mulsi(12,gcoeff(ga,2,1))),om2);
  om2=gadd(gmul(gcoeff(ga,2,1),om1),gmul(gcoeff(ga,2,2),om2));
  if (k==2) asub=gdiv(asub,om2);
  q=gexp(gmul(pii2,tau),prec);
  y=gzero; court=stoi(3);
  av1=avma; lim=stack_lim(av1,1); qn=gun; court[2]=0;
  for(;;)
  {
    court[2]++; qn=gmul(q,qn);
    p1=gdiv(gmul(gpuigs(court,k-1),qn),gsub(gun,qn));
    y=gadd(y,p1);
    if (gcmp0(p1) || gexpo(p1) <= - bit_accuracy(prec) - 5) break;
    if (low_stack(lim, stack_lim(av1,1)))
    {
      GEN *gptr[2]; gptr[0]=&y; gptr[1]=&qn;
      if(DEBUGMEM>1) err(warnmem,"elleisnum");
      gerepilemany(av1,gptr,2);
    }
  }

  y=gadd(gun,gmul(gdiv(gdeux,gzeta(stoi(1-k),prec)),y));
  p1=gpuigs(gdiv(pii2,om2),k);
  y = gmul(p1,y);
  if (k==2) y=gsub(y,asub);
  else if (k==4 && flag) y=gdivgs(y,12);
  else if (k==6 && flag) y=gdivgs(y,216);
  return gerepileupto(av,y);
}

/* compute eta1, eta2 */
GEN
elleta(GEN om, long prec)
{
  long av=avma;
  GEN e2,y1,y2,y;

  e2 = gdivgs(elleisnum(om,2,0,prec),12);
  y2 = gmul((GEN)om[2],e2);
  y1 = gadd(gdiv(PiI2(prec),(GEN)om[2]), gmul((GEN)om[1],e2));
  y = cgetg(3,t_VEC);
  y[1] = lneg(y1);
  y[2] = lneg(y2); return gerepileupto(av, y);
}

/* computes the numerical value of wp(z | om1 Z + om2 Z),
   If flall=1, compute also wp'. Reduce to the fundamental domain first. */
static GEN
weipellnumall(GEN om1, GEN om2, GEN z, long flall, long prec)
{
  long av=avma,tetpil,lim,av1,toadd;
  GEN p1,pii2,pii4,a,tau,q,u,y,yp,u1,u2,qn,v,ga;

  pii2 = PiI2(prec);
  tau = get_tau(&om1,&om2, &ga);
  om2=gadd(gmul(gcoeff(ga,2,1),om1),gmul(gcoeff(ga,2,2),om2));
  z=gdiv(z,om2);
  a=ground(gdiv(gimag(z),gimag(tau))); z=gsub(z,gmul(a,tau));
  a=ground(greal(z)); z=gsub(z,a);
  if (gcmp0(z) || gexpo(z) < 5 - bit_accuracy(prec))
  {
    avma=av; v=cgetg(2,t_VEC); v[1]=zero; return v;
  }

  q=gexp(gmul(pii2,tau),prec);
  u=gexp(gmul(pii2,z),prec);
  u1=gsub(gun,u); u2=gsqr(u1);
  y=gadd(gdivgs(gun,12),gdiv(u,u2));
  if (flall) yp=gdiv(gadd(gun,u),gmul(u1,u2));
  toadd=(long)ceil(9.065*gtodouble(gimag(z)));

  av1=avma; lim=stack_lim(av1,1); qn=q;
  for(;;)
  {
    GEN p2,qnu,qnu1,qnu2,qnu3,qnu4;

    qnu=gmul(qn,u); qnu1=gsub(gun,qnu); qnu2=gsqr(qnu1);
    qnu3=gsub(qn,u); qnu4=gsqr(qnu3);
    p1=gsub(gmul(u,gadd(ginv(qnu2),ginv(qnu4))),
	    gmul2n(ginv(gsqr(gsub(gun,qn))),1));
    p1=gmul(qn,p1);
    y=gadd(y,p1);
    if (flall)
    {
      p2=gadd(gdiv(gadd(gun,qnu),gmul(qnu1,qnu2)),
              gdiv(gadd(qn,u),gmul(qnu3,qnu4)));
      p2=gmul(qn,p2);
      yp=gadd(yp,p2);
    }
    qn=gmul(q,qn);
    if (gexpo(qn) <= - bit_accuracy(prec) - 5 - toadd) break;
    if (low_stack(lim, stack_lim(av1,1)))
    {
      GEN *gptr[3]; gptr[0]=&y; gptr[1]=&qn; gptr[2]=&yp;
      if(DEBUGMEM>1) err(warnmem,"weipellnum");
      gerepilemany(av1,gptr,flall?3:2);
    }
  }

  pii2=gdiv(pii2,om2);
  pii4=gsqr(pii2);
  y = gmul(pii4,y);
  if (flall) yp=gmul(u,gmul(gmul(pii4,pii2),yp));
  tetpil=avma;
  if (flall) { v=cgetg(3,t_VEC); v[1]=lcopy(y); v[2]=lmul2n(yp,-1); }
  else v=gcopy(y);
  return gerepile(av,tetpil,v);
}

GEN
ellzeta(GEN om, GEN z, long prec)
{
  long av=avma,tetpil,lim,av1,toadd;
  GEN zinit,om1,om2,p1,pii2,tau,q,u,y,u1,qn,ga,x1,x2,et;

  if (!get_periods(om, &om1, &om2)) err(typeer,"ellzeta");
  pii2 = PiI2(prec);
  tau = get_tau(&om1,&om2, &ga);
  om2=gadd(gmul(gcoeff(ga,2,1),om1),gmul(gcoeff(ga,2,2),om2));
  om1=gmul(tau,om2); om=cgetg(3,t_VEC); om[1]=(long)om1; om[2]=(long)om2;
  z=gdiv(z,om2);

  x1=ground(gdiv(gimag(z),gimag(tau))); z=gsub(z,gmul(x1,tau));
  x2=ground(greal(z)); z=gsub(z,x2); zinit=gmul(z,om2);
  et=elleta(om,prec);
  et=gadd(gmul(x1,(GEN)et[1]),gmul(x2,(GEN)et[2]));
  if (gcmp0(z) || gexpo(z) < 5 - bit_accuracy(prec))
  {
    p1=ginv(zinit); tetpil=avma; return gerepile(av,tetpil,gadd(p1,et));
  }
  q=gexp(gmul(pii2,tau),prec);
  u=gexp(gmul(pii2,z),prec);
  u1=gsub(u,gun);
  y=gdiv(gmul(gsqr(om2),elleisnum(om,2,0,prec)),pii2);
  y=gadd(ghalf,gdivgs(gmul(z,y),-12));
  y=gadd(y,ginv(u1));
  toadd=(long)ceil(9.065*gtodouble(gimag(z)));
  av1=avma; lim=stack_lim(av1,1); qn=q;
  for(;;)
  {
    p1=gadd(gdiv(u,gsub(gmul(qn,u),gun)),ginv(gsub(u,qn)));
    p1=gmul(qn,p1);
    y=gadd(y,p1);
    qn=gmul(q,qn);
    if (gexpo(qn) <= - bit_accuracy(prec) - 5 - toadd) break;
    if (low_stack(lim, stack_lim(av1,1)))
    {
      GEN *gptr[2]; gptr[0]=&y; gptr[1]=&qn;
      if(DEBUGMEM>1) err(warnmem,"ellzeta");
      gerepilemany(av1,gptr,2);
    }
  }

  y=gmul(gdiv(pii2,om2),y);
  tetpil=avma;
  return gerepile(av,tetpil,gadd(y,et));
}

/* if flag=0, return ellsigma, otherwise return log(ellsigma) */
GEN
ellsigma(GEN om, GEN z, long flag, long prec)
{
  long av=avma,lim,av1,toadd;
  GEN zinit,om1,om2,p1,pii2,tau,q,u,y,y1,u1,qn,ga,negu,uinv,x1,x2,et,etnew,uhalf;
  int doprod = (flag >= 2);
  int dolog = (flag & 1);

  if (!get_periods(om, &om1, &om2)) err(typeer,"ellsigmaprod");
  pii2 = PiI2(prec);
  tau = get_tau(&om1,&om2, &ga);
  om2=gadd(gmul(gcoeff(ga,2,1),om1),gmul(gcoeff(ga,2,2),om2));
  om1=gmul(tau,om2); om=cgetg(3,t_VEC); om[1]=(long)om1; om[2]=(long)om2;
  z=gdiv(z,om2);

  x1=ground(gdiv(gimag(z),gimag(tau))); z=gsub(z,gmul(x1,tau));
  x2=ground(greal(z)); z=gsub(z,x2); zinit=gmul(z,om2);
  et=elleta(om,prec);
  etnew=gadd(gmul(x1,(GEN)et[1]),gmul(x2,(GEN)et[2]));
  etnew=gmul(etnew,gadd(gmul2n(gadd(gmul(x1,om1),gmul(x2,om2)),-1),zinit));
  if (mpodd(x1) || mpodd(x2)) etnew=gadd(etnew,gmul2n(pii2,-1));
  if (gexpo(z) < 5 - bit_accuracy(prec))
  {
    if (dolog)
      return gerepileupto(av, gadd(etnew,glog(zinit,prec)));
    else
      return gerepileupto(av, gmul(gexp(etnew,prec),zinit));
  }

  y1 = gadd(etnew,gmul2n(gmul(gmul(z,zinit),(GEN)et[2]),-1));

  /* 9.065 = 2*Pi/log(2) */
  toadd = (long)ceil(9.065*fabs(gtodouble(gimag(z))));
  uhalf = gexp(gmul(gmul2n(pii2,-1),z),prec);
  u = gsqr(uhalf);
  if (doprod)
  { /* use product */
    q=gexp(gmul(pii2,tau),prec);
    uinv=ginv(u);
    u1=gsub(uhalf,ginv(uhalf));
    y=gdiv(gmul(om2,u1),pii2);
    av1=avma; lim=stack_lim(av1,1); qn=q;
    negu=stoi(-1);
    for(;;)
    {
      p1=gmul(gadd(gmul(qn,u),negu),gadd(gmul(qn,uinv),negu));
      p1=gdiv(p1,gsqr(gadd(qn,negu)));
      y=gmul(y,p1);
      qn=gmul(q,qn);
      if (gexpo(qn) <= - bit_accuracy(prec) - 5 - toadd) break;
      if (low_stack(lim, stack_lim(av1,1)))
      {
        GEN *gptr[2]; gptr[0]=&y; gptr[1]=&qn;
        if(DEBUGMEM>1) err(warnmem,"ellsigma");
        gerepilemany(av1,gptr,2);
      }
    }
  }
  else
  { /* use sum */
    GEN q8,qn2,urn,urninv;
    long n;
    q8=gexp(gmul2n(gmul(pii2,tau),-3),prec);
    q=gpuigs(q8,8);
    u=gneg_i(u); uinv=ginv(u);
    y=gzero;
    av1=avma; lim=stack_lim(av1,1); qn=q; qn2=gun;
    urn=uhalf; urninv=ginv(uhalf);
    for(n=0;;n++)
    {
      y=gadd(y,gmul(qn2,gsub(urn,urninv)));
      qn2=gmul(qn,qn2);
      qn=gmul(q,qn);
      urn=gmul(urn,u); urninv=gmul(urninv,uinv);
      if (gexpo(qn2) + n*toadd <= - bit_accuracy(prec) - 5) break;
      if (low_stack(lim, stack_lim(av1,1)))
      {
        GEN *gptr[5]; gptr[0]=&y; gptr[1]=&qn; gptr[2]=&qn2; gptr[3]=&urn;
        gptr[4]=&urninv;
        if(DEBUGMEM>1) err(warnmem,"ellsigma");
        gerepilemany(av1,gptr,5);
      }
    }

    p1=gmul(q8,gmul(gdiv(gdiv((GEN)om[2],pii2),gpuigs(trueeta(tau,prec),3)),y));
  }

  if (dolog)
    return gerepileupto(av, gadd(y1,glog(p1,prec)));
  else
    return gerepileupto(av, gmul(p1,gexp(y1,prec)));
}

GEN
pointell(GEN e, GEN z, long prec)
{
  long av=avma,tetpil;
  GEN y,yp,v,p1;

  checkbell(e);
  p1=weipellnumall((GEN)e[16],(GEN)e[15],z,1,prec);
  if (lg(p1)==2) { avma=av; v=cgetg(2,t_VEC); v[1]=zero; return v; }
  y = gsub((GEN)p1[1], gdivgs((GEN)e[6],12));
  yp = gsub((GEN)p1[2], gmul2n(ellLHS0(e,y),-1));
  tetpil=avma; v=cgetg(3,t_VEC); v[1]=lcopy(y); v[2]=lcopy(yp);
  return gerepile(av,tetpil,v);
}

GEN
weipell(GEN e, long prec)
{
  long av1,tetpil,precres,i,k,l;
  GEN res,p1,s,t;

  checkell(e); precres = 2*prec+2;
  res=cgetg(precres,t_SER);
  res[1] = evalsigne(1) | evalvalp(-2) | evalvarn(0);
  if (!prec) { setsigne(res,0); return res; }
  for (i=3; i<precres; i+=2) res[i]=zero;
  switch(prec)
  {
    default: res[8]=ldivgs((GEN)e[11],6048);
    case 3: res[6]=ldivgs((GEN)e[10],240);
    case 2: res[4]=zero;
    case 1: res[2]=un;
    case 0: break;
  }
  for (k=4; k<prec; k++)
  {
    av1 = avma;
    s = k&1? gzero: gsqr((GEN)res[k+2]);
    t = gzero;
    for (l=2; l+l<k; l++)
      t = gadd(t, gmul((GEN)res[(l+1)<<1],(GEN)res[(k-l+1)<<1]));
    p1=gmulsg(3,gadd(s,gmul2n(t,1)));
    tetpil=avma;
    p1=gdivgs(p1,(k-3)*(2*k+1));
    res[(k+1)<<1] = lpile(av1,tetpil,p1);
  }
  return res;
}

GEN
ellwp0(GEN om, GEN z, long flag, long prec, long PREC)
{
  GEN v,om1,om2;
  long av = avma;

  if (z==NULL) return weipell(om,PREC);
  if (typ(z)==t_POL)
  {
    if (lgef(z) != 4 || !gcmp0((GEN)z[2]) || !gcmp1((GEN)z[3]))
      err(talker,"expecting a simple variable in ellwp");
    v = weipell(om,PREC); setvarn(v, varn(z));
    return v;
  }
  if (!get_periods(om, &om1, &om2)) err(typeer,"ellwp");
  switch(flag)
  {
    case 0: v=weipellnumall(om1,om2,z,0,prec);
      if (typ(v)==t_VEC && lg(v)==2) { avma=av; v=gpuigs(z,-2); }
      return v;
    case 1: v=weipellnumall(om1,om2,z,1,prec);
      if (typ(v)==t_VEC && lg(v)==2)
      {
        GEN p1 = gmul2n(gpuigs(z,3),1);
        long tetpil=avma;
        v=cgetg(3,t_VEC);
	v[1]=lpuigs(z,-2);
	v[2]=lneg(p1); return gerepile(av,tetpil,v);
      }
      return v;
    case 2: return pointell(om,z,prec);
    default: err(flagerr,"ellwp"); return NULL;
  }
}

/* compute a_2 using Jacobi sum */
static GEN
_a_2(GEN e)
{
  long av = avma;
  GEN unmodp = gmodulss(1,8);
  ulong e6 = itos((GEN)gmul(unmodp,(GEN)e[6])[2]);
  ulong e8 = itos((GEN)gmul(unmodp,(GEN)e[8])[2]);
  ulong e72= itos((GEN)gmul(unmodp,gmul2n((GEN)e[7],1))[2]);
  long s = kross(e8, 2) + kross(e8 + e72 + e6 + 4, 2);
  avma = av; return stoi(-s);
}

/* a_p using Jacobi sums */
static GEN
apell2_intern(GEN e, ulong p)
{
  if (p == 2) return _a_2(e);
  else
  {
    ulong av = avma, i;
    GEN unmodp = gmodulss(1,p);
    ulong e6 = itos((GEN)gmul(unmodp,(GEN)e[6])[2]);
    ulong e8 = itos((GEN)gmul(unmodp,(GEN)e[8])[2]);
    ulong e72= itos((GEN)gmul(unmodp,(GEN)e[7])[2]) << 1;
    long s = kross(e8, p);

    if (p < 757UL)
      for (i=1; i<p; i++)
        s += kross(e8 + i*(e72 + i*(e6 + (i<<2))), p);
    else
      for (i=1; i<p; i++)
        s += kross(e8 + mulssmod(i, e72 + mulssmod(i, e6 + (i<<2), p), p), p);
    avma=av; return stoi(-s);
  }
}

GEN
apell2(GEN e, GEN pp)
{
  checkell(e); if (typ(pp)!=t_INT) err(elliper1);
  if (expi(pp) > 29)
    err(talker,"prime too large in jacobi apell2, use apell instead");

  return apell2_intern(e, (ulong)pp[2]);
}

GEN ellap0(GEN e, GEN p, long flag)
{
  return flag? apell2(e,p): apell(e,p);
}

/* invert all elements of x mod p using Montgomery's trick */
GEN
multi_invmod(GEN x, GEN p)
{
  long i, lx = lg(x);
  GEN u,y = cgetg(lx, t_VEC);

  y[1] = x[1];
  for (i=2; i<lx; i++)
    y[i] = lresii(mulii((GEN)y[i-1], (GEN)x[i]), p);

  u = mpinvmod((GEN)y[--i], p);
  for ( ; i > 1; i--)
  {
    y[i] = lresii(mulii(u, (GEN)y[i-1]), p);
    u = resii(mulii(u, (GEN)x[i]), p); /* u = 1 / (x[1] ... x[i-1]) */
  }
  y[1] = (long)u; return y;
}

static GEN
addsell(GEN e, GEN z1, GEN z2, GEN p)
{
  GEN p1,p2,x,x1,x2,y,y1,y2;
  long av = avma;

  if (!z1) return z2;
  if (!z2) return z1;

  x1 = (GEN)z1[1]; y1 = (GEN)z1[2];
  x2 = (GEN)z2[1]; y2 = (GEN)z2[2];
  p2 = subii(x2, x1);
  if (p2 == gzero)
  {
    if (!signe(y1) || !egalii(y1,y2)) return NULL;
    p2 = shifti(y1,1);
    p1 = addii(e, mulii(x1,mulsi(3,x1)));
    p1 = resii(p1, p);
  }
  else p1 = subii(y2,y1);
  p1 = mulii(p1, mpinvmod(p2, p));
  p1 = resii(p1, p);
  x = subii(sqri(p1), addii(x1,x2)); x = modii(x,p);
  y = negi(addii(y1, mulii(p1,subii(x,x1))));
  avma = av; p1 = cgetg(3,t_VEC);
  p1[1] = licopy(x);
  p1[2] = lmodii(y, p); return p1;
}

/* z1 <-- z1 + z2 */
static void
addsell_part2(GEN e, GEN z1, GEN z2, GEN p, GEN p2inv)
{
  GEN p1,x,x1,x2,y,y1,y2;

  x1 = (GEN)z1[1]; y1 = (GEN)z1[2];
  x2 = (GEN)z2[1]; y2 = (GEN)z2[2];
  if (x1 == x2)
  {
    p1 = addii(e, mulii(x1,mulsi(3,x1)));
    p1 = resii(p1, p);
  }
  else p1 = subii(y2,y1);

  p1 = mulii(p1, p2inv);
  p1 = resii(p1, p);
  x = subii(sqri(p1), addii(x1,x2)); x = modii(x,p);
  y = negi(addii(y1, mulii(p1,subii(x,x1)))); y = modii(y,p);
  affii(x, x1);
  affii(y, y1);
}

static GEN
powsell(GEN e, GEN z, GEN n, GEN p)
{
  GEN y;
  long s=signe(n),i,j;
  ulong m;

  if (!s || !z) return NULL;
  if (s < 0)
  {
    n = negi(n); y = cgetg(3,t_VEC);
    y[2] = lnegi((GEN)z[2]);
    y[1] = z[1]; z = y;
  }
  if (is_pm1(n)) return z;

  y = NULL;
  for (i=lgefint(n)-1; i>2; i--)
    for (m=n[i],j=0; j<BITS_IN_LONG; j++,m>>=1)
    {
      if (m&1) y = addsell(e,y,z,p);
      z = addsell(e,z,z,p);
    }
  for (m=n[2]; m>1; m>>=1)
  {
    if (m&1) y = addsell(e,y,z,p);
    z = addsell(e,z,z,p);
  }
  return addsell(e,y,z,p);
}

/* make sure *x has lgefint >= k */
static void
_fix(GEN x, long k)
{
  GEN y = (GEN)*x;
  if (lgefint(y) < k) { GEN p1 = cgeti(k); affii(y,p1); *x = (long)p1; }
}

/* low word of integer x */
#define _low(x) (__x=(GEN)x, __x[lgefint(__x)-1])

/* compute a_p using Shanks/Mestre + Montgomery's trick. Assume p > 20, say */
GEN
apell1(GEN e, GEN p)
{
  long *tx, *ty, *ti, av = avma, av2,pfinal,i,j,j2,s,flc,flcc,x,nb;
  GEN p1,p2,p3,h,mfh,f,fh,fg,pordmin,u,v,p1p,p2p,acon,bcon,c4,c6,cp4,pts;
  GEN __x;

  if (DEBUGLEVEL) timer2();
  p1 = gmodulsg(1,p);
  c4 = gdivgs(gmul(p1,(GEN)e[10]), -48);
  c6 = gdivgs(gmul(p1,(GEN)e[11]), -864);
  pordmin = gceil(gmul2n(gsqrt(p,DEFAULTPREC),2));
  p1p = addsi(1,p); p2p = shifti(p1p,1);
  x=0; flcc=0; flc = kronecker((GEN)c6[2],p);
  u=c6; acon=gzero; bcon=gun; h=p1p;
  tx = ty = ti = NULL; /* gcc -Wall */
  for(;;)
  {
    while (flc==flcc || !flc)
    {
      x++;
      u = gadd(c6, gmulsg(x, gaddgs(c4,x*x)));
      flc = kronecker((GEN)u[2],p);
    }
    flcc = flc;
    f = cgetg(3,t_VEC);
    f[1] = (long)lift_intern(gmulsg(x,u));
    f[2] = (long)lift_intern(gsqr(u));
    cp4 = lift_intern(gmul(c4, (GEN)f[2]));
    fh = powsell(cp4,f,h,p);
    s = itos(gceil(gsqrt(gdiv(pordmin,bcon),DEFAULTPREC))) >> 1;
    nb = min(128, s >> 1);
    /* look for h s.t f^h = 0 */
    if (bcon == gun)
    { /* first time: initialize */
      tx = newbloc(s+1);
      ty = newbloc(s+1);
      ti = newbloc(s+1);
    }
    else f = powsell(cp4,f,bcon,p); /* F */
    *tx = evaltyp(t_VECSMALL) | evallg(s+1);
    if (!fh) goto FOUND;

    p1 = gcopy(fh);
    pts = new_chunk(nb+1);
    j = lgefint(p);
    for (i=1; i<=nb; i++)
    { /* baby steps */
      pts[i] = (long)p1; /* h.f + (i-1).F */
      _fix(p1+1, j); tx[i] = _low((GEN)p1[1]);
      _fix(p1+2, j); ty[i] = _low((GEN)p1[2]);
      p1 = addsell(cp4,p1,f,p); /* h.f + i.F */
      if (!p1) { h = addii(h, mulsi(i,bcon)); goto FOUND; }
    }
    mfh = dummycopy(fh);
    mfh[2] = lnegi((GEN)mfh[2]);
    fg = addsell(cp4,p1,mfh,p); /* nb.F */
    if (!fg) { h = mulsi(nb,bcon); goto FOUND; }
    u = cgetg(nb+1, t_VEC);
    av2 = avma; /* more baby steps, nb points at a time */
    while (i <= s)
    {
      long maxj;
      for (j=1; j<=nb; j++) /* adding nb.F (part 1) */
      {
        p1 = (GEN)pts[j]; /* h.f + (i-nb-1+j-1).F */
        u[j] = lsubii((GEN)fg[1], (GEN)p1[1]);
        if (u[j] == zero) /* sum = 0 or doubling */
        {
          long k = i+j-2;
          if (egalii((GEN)p1[2],(GEN)fg[2])) k -= 2*nb; /* fg = p1 */
          h = addii(h, mulsi(k,bcon));
          goto FOUND;
        }
      }
      v = multi_invmod(u, p);
      maxj = (i-1 + nb <= s)? nb: s % nb;
      for (j=1; j<=maxj; j++,i++) /* adding nb.F (part 2) */
      {
        p1 = (GEN)pts[j];
        addsell_part2(cp4,p1,fg,p, (GEN)v[j]);
        tx[i] = _low((GEN)p1[1]);
        ty[i] = _low((GEN)p1[2]);
      }
      avma = av2;
    }
    p1 = addsell(cp4,(GEN)pts[j-1],mfh,p); /* = f^(s-1) */
    if (DEBUGLEVEL) msgtimer("[apell1] baby steps, s = %ld",s);

    /* giant steps: fg = f^s */
    fg = addsell(cp4,p1,f,p);
    if (!fg) { h = addii(h, mulsi(s,bcon)); goto FOUND; }
    pfinal = _low(p); av2 = avma;

    p1 = gen_sort(tx, cmp_IND | cmp_C, NULL);
    for (i=1; i<=s; i++) ti[i] = tx[p1[i]];
    for (i=1; i<=s; i++) { tx[i] = ti[i]; ti[i] = ty[p1[i]]; }
    for (i=1; i<=s; i++) { ty[i] = ti[i]; ti[i] = p1[i]; }
    if (DEBUGLEVEL) msgtimer("[apell1] sorting");
    avma = av2;

    gaffect(fg, (GEN)pts[1]);
    for (j=2; j<=nb; j++) /* pts = first nb multiples of fg */
      gaffect(addsell(cp4,(GEN)pts[j-1],fg,p), (GEN)pts[j]);
    /* replace fg by nb.fg since we do nb points at a time */
    avma = av2;
    fg = gcopy((GEN)pts[nb]);
    av2 = avma;

    for (i=1,j=1; ; i++)
    {
      GEN ftest = (GEN)pts[j];
      ulong m, l = 1, r = s+1;
      long k, k2;

      avma = av2;
      k = _low((GEN)ftest[1]);
      while (l<r)
      {
        m = (l+r) >> 1;
        if (tx[m] < k) l = m+1; else r = m;
      }
      if (r <= (ulong)s && tx[r] == k)
      {
        while (tx[r] == k && r) r--;
        k2 = _low((GEN)ftest[2]);
        for (r++; tx[r] == k && r <= (ulong)s; r++)
          if (ty[r] == k2 || ty[r] == pfinal - k2)
          { /* [h+j2] f == ± ftest (= [i.s] f)? */
            if (DEBUGLEVEL) msgtimer("[apell1] giant steps, i = %ld",i);
            j2 = ti[r] - 1;
            p1 = addsell(cp4, powsell(cp4,f,stoi(j2),p),fh,p);
            if (egalii((GEN)p1[1], (GEN)ftest[1]))
            {
              if (egalii((GEN)p1[2], (GEN)ftest[2])) i = -i;
              h = addii(h, mulii(addis(mulss(s,i), j2), bcon));
              goto FOUND;
            }
          }
      }
      if (++j > nb)
      { /* compute next nb points */
        long save = 0; /* gcc -Wall */
        for (j=1; j<=nb; j++)
        {
          p1 = (GEN)pts[j];
          u[j] = lsubii((GEN)fg[1], (GEN)p1[1]);
          if (u[j] == zero) /* occurs once: i = j = nb, p1 == fg */
          {
            u[j] = lshifti((GEN)p1[2],1);
            save = fg[1]; fg[1] = p1[1];
          }
        }
        v = multi_invmod(u, p);
        for (j=1; j<=nb; j++)
          addsell_part2(cp4, (GEN)pts[j],fg,p, (GEN)v[j]);
        if (i == nb) { fg[1] = save; }
        j = 1;
      }
    }

FOUND: /* success, found a point of exponent h */
    p2 = decomp(h); p1=(GEN)p2[1]; p2=(GEN)p2[2];
    for (i=1; i<lg(p1); i++)
      for (j=itos((GEN)p2[i]); j; j--)
      {
        p3 = divii(h,(GEN)p1[i]);
        if (powsell(cp4,f,p3,p)) break;
	h = p3;
      }
    /* now h is the exact order */
    if (bcon == gun) bcon = h;
    else
    {
      p1 = chinois(gmodulcp(acon,bcon), gmodulsg(0,h));
      acon = (GEN)p1[2];
      bcon = (GEN)p1[1];
    }

    i = (cmpii(bcon, pordmin) < 0);
    if (i) acon = centermod(subii(p2p,acon), bcon);
    p1 = ground(gdiv(gsub(p1p,acon),bcon));
    h = addii(acon, mulii(p1,bcon));
    if (!i) break;
  }
  gunclone(tx);
  gunclone(ty);
  gunclone(ti);
  p1 = (flc==1)? subii(p1p,h): subii(h,p1p);
  return gerepileupto(av,p1);
}

typedef struct
{
  int isnull;
  long x,y;
} sellpt;

/* set p1 <-- p1 + p2, safe with p1 = p2 */
static void
addsell1(long e, long p, sellpt *p1, sellpt *p2)
{
  long num, den, lambda;

  if (p1->isnull) { *p1 = *p2; return; }
  if (p2->isnull) return;
  if (p1->x == p2->x)
  {
    if (! p1->y || p1->y != p2->y) { p1->isnull = 1; return; }
    num = addssmod(e, mulssmod(3, mulssmod(p1->x, p1->x, p), p), p);
    den = addssmod(p1->y, p1->y, p);
  }
  else
  {
    num = subssmod(p1->y, p2->y, p);
    den = subssmod(p1->x, p2->x, p);
  }
  lambda = divssmod(num, den, p);
  num = subssmod(mulssmod(lambda, lambda, p), addssmod(p1->x, p2->x, p), p);
  p1->y = subssmod(mulssmod(lambda, subssmod(p2->x, num, p), p), p2->y, p);
  p1->x = num; /* necessary in case p1 = p2: we need p2->x above */
}

static void
powssell1(long e, long p, long n, sellpt *p1, sellpt *p2)
{
  sellpt p3 = *p1;

  if (n < 0) { n = -n; if (p3.y) p3.y = p - p3.y; }
  p2->isnull = 1;
  for(;;)
  {
    if (n&1) addsell1(e, p, p2, &p3);
    n>>=1; if (!n) return;
    addsell1(e, p, &p3, &p3);
  }
}

typedef struct
{
  long x,y,i;
} multiple;

static int
compare_multiples(multiple *a, multiple *b)
{
  return a->x - b->x;
}

/* assume e has good reduction at p. Should use Montgomery. */
static GEN
apell0(GEN e, long p)
{
  GEN p1,p2;
  sellpt f,fh,fg,ftest,f2;
  long pordmin,u,p1p,p2p,acon,bcon,c4,c6,cp4;
  long av,i,j,s,flc,flcc,x,q,h,p3,l,r,m;
  multiple *table;

  if (p < 99) return apell2_intern(e,(ulong)p);

  av = avma; p1 = gmodulss(1,p);
  c4 = itos((GEN)gdivgs(gmul(p1,(GEN)e[10]), -48)[2]);
  c6 = itos((GEN)gdivgs(gmul(p1,(GEN)e[11]), -864)[2]);
  pordmin = (long)(1 + 4*sqrt((float)p));
  p1p = p+1; p2p = p1p << 1;
  x=0; flcc=0; flc = kross(c6, p);
  u=c6; acon=0; bcon=1; h=p1p;
  table = NULL; /* gcc -Wall */
  for(;;)
  {
    while (flc==flcc || !flc)
    {
      x++;
      u = addssmod(c6, mulssmod(x, c4+mulssmod(x,x,p), p), p);
      flc = kross(u,p);
    }
    flcc = flc;
    f.isnull = 0;
    f.x = mulssmod(x, u, p);
    f.y = mulssmod(u, u, p);
    cp4 = mulssmod(c4, f.y, p);
    powssell1(cp4, p, h, &f, &fh);
    s = (long) (sqrt(((float)pordmin)/bcon) / 2);
    if (!s) s=1;
    if (bcon==1)
    {
      table = (multiple *) gpmalloc((s+1)*sizeof(multiple));
      f2 = f;
    }
    else powssell1(cp4, p, bcon, &f, &f2);
    for (i=0; i < s; i++)
    {
      if (fh.isnull) { h += bcon*i; goto FOUND; }
      table[i].x = fh.x;
      table[i].y = fh.y;
      table[i].i = i;
      addsell1(cp4, p, &fh, &f2);
    }
    qsort(table,s,sizeof(multiple),(QSCOMP)compare_multiples);
    powssell1(cp4, p, s, &f2, &fg); ftest = fg;
    for (i=1; ; i++)
    {
      if (ftest.isnull) err(bugparier,"apell (f^(i*s) = 1)");
      l=0; r=s;
      while (l<r)
      {
	m = (l+r) >> 1;
	if (table[m].x < ftest.x) l=m+1; else r=m;
      }
      if (r < s && table[r].x == ftest.x) break;
      addsell1(cp4, p, &ftest, &fg);
    }
    h += table[r].i * bcon;
    if (table[r].y == ftest.y) i = -i;
    h += s * i * bcon;

FOUND:
    p2=decomp(stoi(h)); p1=(GEN)p2[1]; p2=(GEN)p2[2];
    for (i=1; i < lg(p1); i++)
      for (j = mael(p2,i,2); j; j--)
      {
	p3 = h / mael(p1,i,2);
	powssell1(cp4, p, p3, &f, &fh);
	if (!fh.isnull) break;
	h = p3;
      }
    if (bcon == 1) bcon = h;
    else
    {
      p1 = chinois(gmodulss(acon,bcon), gmodulss(0,h));
      acon = itos((GEN)p1[2]);
      if (is_bigint(p1[1])) { h = acon; break; }
      bcon = itos((GEN)p1[1]);
    }

    i = (bcon < pordmin);
    if (i)
    {
      acon = (p2p - acon) % bcon;
      if ((acon << 1) > bcon) acon -= bcon;
    }
    q = ((ulong)(p2p + bcon - (acon << 1))) / (bcon << 1);
    h = acon + q*bcon;
    avma = av; if (!i) break;
  }
  free(table); return stoi((flc==1)? p1p-h: h-p1p);
}

GEN
apell(GEN e, GEN p)
{
  checkell(e);
  if (typ(p)!=t_INT || signe(p)<0) err(talker,"not a prime in apell");
  if (gdivise((GEN)e[12],p)) /* e[12] may be an intmod */
  {
    long av = avma,s;
    GEN p0 = egalii(p,gdeux)? stoi(8): p;
    GEN c6 = gmul((GEN)e[11],gmodulsg(1,p0));
    s = kronecker(lift_intern(c6),p); avma=av;
    if (mod4(p) == 3) s = -s;
    return stoi(s);
  }
  if (cmpis(p, 0x3fffffff) > 0) return apell1(e, p);
  return apell0(e, itos(p));
}

/* TEMPC is the largest prime whose square is less than HIGHBIT */
#ifndef LONG_IS_64BIT
#  define TEMPC 46337
#  define TEMPMAX 16777215UL
#else
#  define TEMPC 3037000493
#  define TEMPMAX 4294967295UL
#endif

GEN
anell(GEN e, long n)
{
  long tab[4]={0,1,1,-1}; /* p prime; (-1/p) = tab[p&3]. tab[0] is not used */
  long p, i, m, av, tetpil;
  GEN p1,p2,an;

  checkell(e);
  for (i=1; i<=5; i++)
    if (typ(e[i]) != t_INT) err(typeer,"anell");
  if (n <= 0) return cgetg(1,t_VEC);
  if ((ulong)n>TEMPMAX)
    err(impl,"anell for n>=2^24 (or 2^32 for 64 bit machines)");
  an = cgetg(n+1,t_VEC); an[1] = un;
  for (i=2; i <= n; i++) an[i] = 0;
  for (p=2; p<=n; p++)
    if (!an[p])
    {
      if (!smodis((GEN)e[12],p)) /* mauvaise reduction, p | e[12] */
	switch (tab[p&3] * krogs((GEN)e[11],p)) /* renvoie (-c6/p) */
	{
	  case -1:  /* non deployee */
	    for (m=p; m<=n; m+=p)
	      if (an[m/p]) an[m]=lneg((GEN)an[m/p]);
	    continue;
	  case 0:   /* additive */
	    for (m=p; m<=n; m+=p) an[m]=zero;
	    continue;
	  case 1:   /* deployee */
	    for (m=p; m<=n; m+=p)
	      if (an[m/p]) an[m]=lcopy((GEN)an[m/p]);
	}
      else /* bonne reduction */
      {
        GEN ap = apell0(e,p);

	if (p < TEMPC)
	{
	  ulong pk, oldpk = 1;
	  for (pk=p; pk <= (ulong)n; oldpk=pk, pk *= p)
	  {
	    if (pk == (ulong)p) an[pk] = (long) ap;
	    else
	    {
	      av = avma;
	      p1 = mulii(ap, (GEN)an[oldpk]);
	      p2 = mulsi(p, (GEN)an[oldpk/p]);
	      tetpil = avma;
	      an[pk] = lpile(av,tetpil,subii(p1,p2));
	    }
	    for (m = n/pk; m > 1; m--)
	      if (an[m] && m%p) an[m*pk] = lmulii((GEN)an[m], (GEN)an[pk]);
	  }
	}
	else
	{
	  an[p] = (long) ap;
	  for (m = n/p; m > 1; m--)
	    if (an[m] && m%p) an[m*p] = lmulii((GEN)an[m], (GEN)an[p]);
	}
      }
    }
  return an;
}

GEN
akell(GEN e, GEN n)
{
  long i,j,ex,av=avma;
  GEN p1,p2,ap,u,v,w,y,pl;

  checkell(e);
  if (typ(n)!=t_INT) err(talker,"not an integer type in akell");
  if (signe(n)<= 0) return gzero;
  y=gun; if (gcmp1(n)) return y;
  p2=auxdecomp(n,1); p1=(GEN)p2[1]; p2=(GEN)p2[2];
  for (i=1; i<lg(p1); i++)
  {
    pl=(GEN)p1[i];
    if (divise((GEN)e[12], pl)) /* mauvaise reduction */
    {
      j = (((mod4(pl)+1)&2)-1)*kronecker((GEN)e[11],pl);
      if (j<0 && mpodd((GEN)p2[i])) y = negi(y);
      if (!j) { avma=av; return gzero; }
    }
    else /* bonne reduction */
    {
      ap=apell(e,pl); ex=itos((GEN)p2[i]);
      u=ap; v=gun;
      for (j=2; j<=ex; j++)
      {
	w = subii(mulii(ap,u), mulii(pl,v));
	v=u; u=w;
      }
      y = mulii(u,y);
    }
  }
  return gerepileupto(av,y);
}

GEN
hell(GEN e, GEN a, long prec)
{
  long av=avma,tetpil,n;
  GEN p1,p2,y,z,q,pi2surw,pi2isurw,qn,ps;

  checkbell(e);
  pi2surw=gdiv(gmul2n(mppi(prec),1),(GEN)e[15]);
  pi2isurw=cgetg(3,t_COMPLEX); pi2isurw[1]=zero; pi2isurw[2]=(long)pi2surw;
  z=gmul(greal(zell(e,a,prec)),pi2surw);
  q=greal(gexp(gmul((GEN)e[16],pi2isurw),prec));
  y=gsin(z,prec); n=0; qn=gun; ps=gneg_i(q);
  do
  {
    n++; p1=gsin(gmulsg(2*n+1,z),prec); qn=gmul(qn,ps);
    ps=gmul(ps,q); p1=gmul(p1,qn); y=gadd(y,p1);
  }
  while (gexpo(qn) >= - bit_accuracy(prec));
  p1=gmul(gsqr(gdiv(gmul2n(y,1), d_ellLHS(e,a))),pi2surw);
  p2=gsqr(gsqr(gdiv(p1,gsqr(gsqr(denom((GEN)a[1]))))));
  p1=gdiv(gmul(p2,q),(GEN)e[12]);
  p1=gmul2n(glog(gabs(p1,prec),prec),-5);
  tetpil=avma; return gerepile(av,tetpil,gneg(p1));
}

static GEN
hells(GEN e, GEN x, long prec)
{
  GEN w,z,t,mu,e72,e82;
  long n,lim;

  t = gdiv(realun(prec),(GEN)x[1]);
  mu = gmul2n(glog(numer((GEN)x[1]),prec),-1);
  e72 = gmul2n((GEN)e[7],1);
  e82 = gmul2n((GEN)e[8],1);
  lim = 6 + (bit_accuracy(prec) >> 1);
  for (n=0; n<lim; n++)
  {
    w = gmul(t,gaddsg(4,gmul(t,gadd((GEN)e[6],gmul(t,gadd(e72,gmul(t,(GEN)e[8])))))));
    z = gsub(gun,gmul(gsqr(t),gadd((GEN)e[7],gmul(t,gadd(e82,gmul(t,(GEN)e[9]))))));
    mu = gadd(mu,gmul2n(glog(z,prec), -((n<<1)+3)));
    t = gdiv(w,z);
  }
  return mu;
}

GEN
hell2(GEN e, GEN x, long prec)
{
  GEN ep,e3,ro,p1,p2,mu,d,xp;
  long av=avma,tetpil,lx,lc,i,j,tx;

  if (!oncurve(e,x)) err(heller1);
  d=(GEN)e[12]; ro=(GEN)e[14]; e3=(gsigne(d) < 0)?(GEN)ro[1]:(GEN)ro[3];
  p1=cgetg(5,t_VEC); p1[1]=un; p1[2]=laddgs(gfloor(e3),-1);
  p1[3]=p1[4]=zero; ep=coordch(e,p1); xp=pointch(x,p1);
  tx=typ(x[1]); lx=lg(x);
  if (!is_matvec_t(tx))
  {
    if (lx<3) { avma=av; return gzero; }
    tetpil=avma; return gerepile(av,tetpil,hells(ep,xp,prec));
  }
  tx=typ(x);
  tetpil=avma; mu=cgetg(lx,tx);
  if (tx != t_MAT)
    for (i=1; i<lx; i++) mu[i]=(long)hells(ep,(GEN)xp[i],prec);
  else
  {
    lc=lg(x[1]);
    for (i=1; i<lx; i++)
    {
      p1=cgetg(lc,t_COL); mu[i]=(long)p1; p2=(GEN)xp[i];
      for (j=1; j<lc; j++) p1[j]=(long)hells(ep,(GEN)p2[j],prec);
    }
  }
  return gerepile(av,tetpil,mu);
}

GEN
hell0(GEN e, GEN z, long prec)
{
  GEN a,b,s,x,u,v,u1,p1,p2,r;
  long n,i, ex = 5-bit_accuracy(prec);

  /* cf. zell mais ne marche pas. Comment corriger? K.B. */
  x = new_coords(e,(GEN)z[1],&a,&b,prec);

  u = gmul2n(gadd(a,b), -1);
  v = gsqrt(gmul(a,b), prec); s = gun;
  for(n=0; ; n++)
  {
    p1 = gmul2n(gsub(x, gsqr(v)), -1);
    p2 = gsqr(u);
    x = gadd(p1, gsqrt(gadd(gsqr(p1), gmul(x, p2)), prec));
    p2 = gadd(x, p2);
    for (i=1; i<=n; i++) p2 = gsqr(p2);
    s = gmul(s, p2);
    u1 = gmul2n(gadd(u,v), -1);
    r = gsub(u,u1);
    if (gcmp0(r) || gexpo(r) < ex) break;

    v = gsqrt(gmul(u,v), prec);
    u = u1;
  }
  return gmul2n(glog(gdiv(gsqr(p2), s), prec) ,-1);
}

/* On suppose que `e' est a coeffs entiers donnee par un modele minimal */
static GEN
ghell0(GEN e, GEN a, long flag, long prec)
{
  long av=avma,lx,i,n,n2,grandn,tx=typ(a);
  GEN p,p1,p2,x,y,z,phi2,psi2,psi3,logdep;

  checkbell(e); if (!is_matvec_t(tx)) err(elliper1);
  lx = lg(a); if (lx==1) return cgetg(1,tx);
  tx=typ(a[1]);
  if (is_matvec_t(tx))
  {
    z=cgetg(lx,tx);
    for (i=1; i<lx; i++) z[i]=(long)ghell0(e,(GEN)a[i],flag,prec);
    return z;
  }
  if (lg(a)<3) return gzero;
  if (!oncurve(e,a)) err(heller1);

  psi2=numer(d_ellLHS(e,a));
  if (!signe(psi2)) { avma=av; return gzero; }

  x=(GEN)a[1]; y=(GEN)a[2];
  p2=gadd(gmulsg(3,(GEN)e[7]),gmul(x,gadd((GEN)e[6],gmulsg(3,x))));
  psi3=numer(gadd((GEN)e[9],gmul(x,gadd(gmulsg(3,(GEN)e[8]),gmul(x,p2)))));
  if (!signe(psi3)) { avma=av; return gzero; }

  p1 = gmul(x,gadd(shifti((GEN)e[2],1),gmulsg(3,x)));
  phi2=numer(gsub(gadd((GEN)e[4],p1), gmul((GEN)e[1],y)));
  p1=(GEN)factor(mppgcd(psi2,phi2))[1]; lx=lg(p1);
  switch(flag)
  {
    case 0:  z = hell2(e,a,prec); break; /* Tate 4^n */
    case 1:  z = hell(e,a,prec);  break; /* Silverman's trick */
    default: z = hell0(e,a,prec); break; /* Mestre's trick */
  }
  for (i=1; i<lx; i++)
  {
    p=(GEN)p1[i];
    if (signe(resii((GEN)e[10],p)))
    {
      grandn=ggval((GEN)e[12],p);
      if (grandn)
      {
        n2=ggval(psi2,p); n=n2<<1;
        logdep=gneg_i(glog(p,prec));
	if (n>grandn) n=grandn;
	p2=divrs(mulsr(n*(grandn+grandn-n),logdep),grandn<<3);
	z=gadd(z,p2);
      }
    }
    else
    {
      n2=ggval(psi2,p);
      logdep=gneg_i(glog(p,prec));
      n=ggval(psi3,p);
      if (n>=3*n2) p2=gdivgs(mulsr(n2,logdep),3);
      else p2=gmul2n(mulsr(n,logdep),-3);
      z=gadd(z,p2);
    }
  }
  return gerepileupto(av,z);
}

GEN
ellheight0(GEN e, GEN a, long flag, long prec)
{
  switch(flag)
  {
    case 0: return ghell(e,a,prec);
    case 1: return ghell2(e,a,prec);
    case 2: return ghell0(e,a,2,prec);
  }
  err(flagerr,"ellheight");
  return NULL; /* not reached */
}

GEN
ghell2(GEN e, GEN a, long prec)
{
  return ghell0(e,a,0,prec);
}

GEN
ghell(GEN e, GEN a, long prec)
{
  return ghell0(e,a,1,prec);
}

static long ellrootno_all(GEN e, GEN p, GEN* ptcond);

GEN
lseriesell(GEN e, GEN s, GEN A, long prec)
{
  long av=avma,av1,tetpil,lim,l,n,eps,flun;
  GEN z,p1,p2,cg,cg1,v,cga,cgb,s2,ns,gs,N;

  if (!A) A = gun;
  else
  {
    if (gsigne(A)<=0)
      err(talker,"cut-off point must be positive in lseriesell");
    if (gcmpgs(A,1) < 0) A = ginv(A);
  }
  flun = gcmp1(A) && gcmp1(s);
  eps = ellrootno_all(e,gun,&N);
  if (flun && eps<0) { z=cgetr(prec); affsr(0,z); return z; }
  cg1=mppi(prec); setexpo(cg1,2); cg=divrr(cg1,gsqrt(N,prec));
  cga=gmul(cg,A); cgb=gdiv(cg,A);
  l=(long)((pariC2*(prec-2) + fabs(gtodouble(s)-1.)*log(rtodbl(cga)))
            / rtodbl(cgb)+1);
  v = anell(e, min((ulong)l,TEMPMAX));
  s2 = ns = NULL; /* gcc -Wall */
  if (!flun) { s2=gsubsg(2,s); ns=gpui(cg,gsubgs(gmul2n(s,1),2),prec); }
  z=gzero;
  if (typ(s)==t_INT)
  {
    if (signe(s)<=0) { avma=av; return gzero; }
    gs=mpfactr(itos(s)-1,prec);
  }
  else gs=ggamma(s,prec);
  av1=avma; lim=stack_lim(av1,1);
  for (n=1; n<=l; n++)
  {
    p1=gdiv(incgam4(s,gmulsg(n,cga),gs,prec),gpui(stoi(n),s,prec));
    p2=flun? p1: gdiv(gmul(ns,incgam(s2,gmulsg(n,cgb),prec)),
                      gpui(stoi(n),s2,prec));
    if (eps<0) p2=gneg_i(p2);
    z = gadd(z, gmul(gadd(p1,p2),
                     ((ulong)n<=TEMPMAX)? (GEN)v[n]: akell(e,stoi(n))));
    if (low_stack(lim, stack_lim(av1,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"lseriesell");
      z = gerepilecopy(av1,z);
    }
  }
  tetpil=avma; return gerepile(av,tetpil,gdiv(z,gs));
}

/********************************************************************/
/**                                                                **/
/**                 Tate's algorithm e (cf Anvers IV)              **/
/**               Kodaira types, global minimal model              **/
/**                                                                **/
/********************************************************************/

/* Given an integral elliptic curve in ellinit form, and a prime p, returns the
  type of the fiber at p of the Neron model, as well as the change of variables
  in the form [f, kod, v, c].

  * The integer f is the conductor's exponent.

  * The integer kod is the Kodaira type using the following notation:
    II , III , IV  -->  2, 3, 4
    I0  -->  1
    Inu --> 4+nu for nu > 0
  A '*' negates the code (e.g I* --> -2)

  * v is a quadruple [u, r, s, t] yielding a minimal model

  * c is the Tamagawa number.

  Uses Tate's algorithm (Anvers IV). Given the remarks at the bottom of
  page 46, the "long" algorithm is used for p < 4 only. */
static void cumule(GEN *vtotal, GEN *e, GEN u, GEN r, GEN s, GEN t);
static void cumule1(GEN *vtotal, GEN *e, GEN v2);

static GEN
localreduction_result(long av, long f, long kod, long c, GEN v)
{
  long tetpil = avma;
  GEN result = cgetg(5, t_VEC);
  result[1] = lstoi(f); result[2] = lstoi(kod);
  result[3] = lcopy(v); result[4] = lstoi(c);
  return gerepile(av,tetpil, result);
}

/* ici, p != 2 et p != 3 */
static GEN
localreduction_carac_not23(GEN e, GEN p)
{
  long av = avma, k, f, kod, c, nuj, nudelta;
  GEN pk, p2k, a2prime, a3prime;
  GEN p2, r = gzero, s = gzero, t = gzero, v;
  GEN c4, c6, delta, unmodp, xun, tri, var, p4k, p6k;

  nudelta = ggval((GEN)e[12], p);
  v = cgetg(5,t_VEC); v[1] = un; v[2] = v[3] = v[4] = zero;
  nuj = gcmp0((GEN)e[13])? 0: - ggval((GEN)e[13], p);
  k = (nuj > 0 ? nudelta - nuj : nudelta) / 12;
  c4 = (GEN)e[10]; c6 = (GEN)e[11]; delta = (GEN)e[12];
  if (k > 0) /* modele non minimal */
  {
    pk = gpuigs(p, k);
    if (mpodd((GEN)e[1]))
      s = shifti(subii(pk, (GEN)e[1]), -1);
    else
      s = negi(shifti((GEN)e[1], -1));
    p2k = sqri(pk);
    p4k = sqri(p2k);
    p6k = mulii(p4k, p2k);

    a2prime = subii((GEN)e[2], mulii(s, addii((GEN)e[1], s)));
    switch(smodis(a2prime, 3))
    {
      case 0: r = negi(divis(a2prime, 3)); break;
      case 1: r = divis(subii(p2k, a2prime), 3); break;
      case 2: r = negi(divis(addii(a2prime, p2k), 3)); break;
    }
    a3prime = ellLHS0_i(e,r);
    if (mpodd(a3prime))
      t = shifti(subii(mulii(pk, p2k), a3prime), -1);
    else
      t = negi(shifti(a3prime, -1));
    v[1] = (long)pk; v[2] = (long)r; v[3] = (long)s; v[4] = (long)t;
    nudelta -= 12 * k;
    c4 = divii(c4, p4k); c6 = divii(c6, p6k);
    delta = divii(delta, sqri(p6k));
  }
  if (nuj > 0) switch(nudelta - nuj)
  {
    case 0: f = 1; kod = 4+nuj; /* Inu */
      switch(kronecker(negi(c6),p))
      {
	case  1: c = nudelta; break;
	case -1: c = odd(nudelta)? 1: 2; break;
	default: err(bugparier,"localred (p | c6)");
          return NULL; /* not reached */
      }
      break;
    case 6: f = 2; kod = -4-nuj; /* Inu* */
      if (nuj & 1)
	c = 3 + kronecker(divii(mulii(c6, delta),gpuigs(p, 9+nuj)), p);
      else
	c = 3 + kronecker(divii(delta, gpuigs(p, 6+nuj)), p);
      break;
    default: err(bugparier,"localred (nu_delta - nu_j != 0,6)");
      return NULL; /* not reached */
  }
  else switch(nudelta)
  {
    case  0: f = 0; kod = 1; c = 1; break; /* I0, regulier */
    case  2: f = 2; kod = 2; c = 1; break; /* II   */
    case  3: f = 2; kod = 3; c = 2; break; /* III  */
    case  4: f = 2; kod = 4; /* IV   */
      c = 2 + kronecker(gdiv(mulis(c6, -6), sqri(p)), p);
      break;
    case  6: f = 2; kod = -1; /* I0*  */
      p2 = sqri(p);
      unmodp = gmodulsg(1,p);
      var = gmul(unmodp,polx[0]);
      tri = gsub(gsqr(var),gmul(divii(gmulsg(3, c4), p2),unmodp));
      tri = gsub(gmul(tri, var),
		 gmul(divii(gmul2n(c6,1), mulii(p2,p)),unmodp));
      xun = gmodulcp(var,tri);
      c = lgef(ggcd((GEN)(gsub(gpui(xun,p,0),xun))[2], tri)) - 2;
      break;
    case  8: f = 2; kod = -4; /* IV*  */
      c = 2 + kronecker(gdiv(mulis(c6,-6), gpuigs(p,4)), p);
      break;
    case  9: f = 2; kod = -3; c = 2; break; /* III* */
    case 10: f = 2; kod = -2; c = 1; break; /* II*  */
    default: err(bugparier,"localred");
      return NULL; /* not reached */
  }
  return localreduction_result(av,f,kod,c,v);
}

/* renvoie a_{ k,l } avec les notations de Tate */
static int
aux(GEN ak, int p, int l)
{
  long av = avma, pl = p, res;
  while (--l) pl *= p;
  res = smodis(divis(ak, pl), p);
  avma = av; return res;
}

static int
aux2(GEN ak, int p, GEN pl)
{
  long av = avma, res;
  res = smodis(divii(ak, pl), p);
  avma = av;
  return res;
}

/* renvoie le nombre de racines distinctes du polynome XXX + aXX + bX + c
 * modulo p s'il y a une racine multiple, elle est renvoyee dans *mult
 */
static int
numroots3(int a, int b, int c, int p, int *mult)
{
  if (p == 2)
  {
    if ((c + a * b) & 1) return 3;
    else { *mult = b; return (a + b) & 1 ? 2 : 1; }
  }
  else
  {
    if (a % 3) { *mult = a * b; return (a * b * (1 - b) + c) % 3 ? 3 : 2; }
    else { *mult = -c; return b % 3 ? 3 : 1; }
  }
}

/* idem pour aXX +bX + c */
static int
numroots2(int a, int b, int c, int p, int *mult)
{
  if (p == 2) { *mult = c; return b & 1 ? 2 : 1; }
  else { *mult = a * b; return (b * b - a * c) % 3 ? 2 : 1; }
}

/* ici, p1 = 2 ou p1 = 3 */
static GEN
localreduction_carac_23(GEN e, GEN p1)
{
  long av = avma, p, c, nu, nudelta;
  int a21, a42, a63, a32, a64, theroot, al, be, ga;
  GEN pk, p2k, pk1, p4, p6;
  GEN p2, p3, r = gzero, s = gzero, t = gzero, v;

  nudelta = ggval((GEN)e[12], p1);
  v = cgetg(5,t_VEC); v[1] = un; v[2] = v[3] = v[4] = zero;

  for(;;)
  {
    if (!nudelta)
      return localreduction_result(av, 0, 1, 1, v);
	/* I0   */
    p = itos(p1);
    if (!divise((GEN)e[6], p1))
    {
      if (smodis(negi((GEN)e[11]), p == 2 ? 8 : 3) == 1)
	c = nudelta;
      else
	c = 2 - (nudelta & 1);
      return localreduction_result(av, 1, 4 + nudelta, c, v);
    }
	/* Inu  */
    if (p == 2)
    {
      r = modis((GEN)e[4], 2);
      s = modis(addii(r, (GEN)e[2]), 2);
      if (signe(r)) t = modis(addii(addii((GEN)e[4], (GEN)e[5]), s), 2);
      else t = modis((GEN)e[5], 2);
    }
    else /* p == 3 */
    {
      r = negi(modis((GEN)e[8], 3));
      s = modis((GEN)e[1], 3);
      t = modis(ellLHS0_i(e,r), 3);
    }
    cumule(&v, &e, gun, r, s, t); /* p | a1, a2, a3, a4 et a6 */
    p2 = stoi(p*p);
    if (!divise((GEN)e[5], p2))
      return localreduction_result(av, nudelta, 2, 1, v);
	/* II   */
    p3 = stoi(p*p*p);
    if (!divise((GEN)e[9], p3))
      return localreduction_result(av, nudelta - 1, 3, 2, v);
	/* III  */
    if (!divise((GEN)e[8], p3))
    {
      if (smodis((GEN)e[8], (p==2)? 32: 27) == p*p)
	c = 3;
      else
	c = 1;
      return localreduction_result(av, nudelta - 2, 4, c, v);
    }
	/* IV   */

	/* now for the last five cases... */

    if (!divise((GEN)e[5], p3))
      cumule(&v, &e, gun, gzero, gzero, p == 2? gdeux: modis((GEN)e[3], 9));
	/* p | a1, a2; p^2  | a3, a4; p^3 | a6 */
    a21 = aux((GEN)e[2], p, 1); a42 = aux((GEN)e[4], p, 2);
    a63 = aux((GEN)e[5], p, 3);
    switch (numroots3(a21, a42, a63, p, &theroot))
    {
      case 3:
	if (p == 2)
	  c = 1 + (a63 == 0) + ((a21 + a42 + a63) & 1);
	else
	  c = 1 + (a63 == 0) + (((1 + a21 + a42 + a63) % 3) == 0)
	      + (((1 - a21 + a42 - a63) % 3) == 0);
	return localreduction_result(av, nudelta - 4, -1, c, v);
	    /* I0*  */
      case 2: /* calcul de nu */
	if (theroot) cumule(&v, &e, gun, stoi(theroot * p), gzero, gzero);
	    /* p | a1; p^2  | a2, a3; p^3 | a4; p^4 | a6 */
	nu = 1;
	pk = p2;
	p2k = stoi(p * p * p * p);
	for(;;)
	{
	  if (numroots2(al = 1, be = aux2((GEN)e[3], p, pk),
			ga = -aux2((GEN)e[5], p, p2k), p, &theroot) == 2)
	    break;
	  if (theroot) cumule(&v, &e, gun, gzero, gzero, mulsi(theroot,pk));
	  pk1 = pk; pk = mulsi(p, pk); p2k = mulsi(p, p2k);
	  nu++;
	  if (numroots2(al = a21, be = aux2((GEN)e[4], p, pk),
			ga = aux2((GEN)e[5], p, p2k), p, &theroot) == 2)
	    break;
	  if (theroot) cumule(&v, &e, gun, mulsi(theroot, pk1), gzero, gzero);
	  p2k = mulsi(p, p2k);
	  nu++;
	}
	if (p == 2)
	  c = 4 - 2 * (ga & 1);
	else
	  c = 3 + kross(be * be - al * ga, 3);
	return localreduction_result(av, nudelta - 4 - nu, -4 - nu, c, v);
	    /* Inu* */
      case 1:
	if (theroot) cumule(&v, &e, gun, stoi(theroot * p), gzero, gzero);
	    /* p | a1; p^2  | a2, a3; p^3 | a4; p^4 | a6 */
	a32 = aux((GEN)e[3], p, 2); a64 = aux((GEN)e[5], p, 4);
	if (numroots2(1, a32, -a64, p, &theroot) == 2)
	{
	  if (p == 2)
	    c = 3 - 2 * a64;
	  else
	    c = 2 + kross(a32 * a32 + a64, 3);
	  return localreduction_result(av, nudelta - 6, -4, c, v);
	}
	    /* IV*  */
	if (theroot) cumule(&v, &e, gun, gzero, gzero, stoi(theroot*p*p));
	    /* p | a1; p^2 | a2; p^3 | a3, a4; p^5 | a6 */
	p4 = sqri(p2);
	if (!divise((GEN)e[4], p4))
	  return localreduction_result(av, nudelta - 7, -3, 2, v);
	    /* III* */
	p6 = mulii(p4, p2);
	if (!divise((GEN)e[5], p6))
	  return localreduction_result(av, nudelta - 8, -2, 1, v);
	    /* II*  */
	cumule(&v, &e, p1, gzero, gzero, gzero); /* non minimal, on repart
						     pour un tour */
	nudelta -= 12;
    }
  }
  /* Not reached */
}

GEN
localreduction(GEN e, GEN p1)
{
  checkell(e);
  if (typ(e[12]) != t_INT)
    err(talker,"not an integral curve in localreduction");
  if (gcmpgs(p1, 3) > 0)       /* p different de 2 ou 3 */
    return localreduction_carac_not23(e,p1);
  else
    return localreduction_carac_23(e,p1);
}

#if 0
/*  Calcul de toutes les fibres non elliptiques d'une courbe sur Z.
 *  Etant donne une courbe elliptique sous forme longue e, dont les coefficients
 *  sont entiers, renvoie une matrice dont les lignes sont de la forme
 *  [p, fp, kodp, cp]. Il y a une ligne par diviseur premier du discriminant.
 */
GEN
globaltatealgo(GEN e)
{
  long k, l,av;
  GEN p1, p2, p3, p4, prims, result;

  checkell(e);
  prims = decomp((GEN)e[12]);
  l = lg(p1 = (GEN)prims[1]);
  p2 = (GEN)prims[2];
  if ((long)prims == avma) cgiv(prims);
  result = cgetg(5, t_MAT);
  result[1] = (long)p1;
  result[2] = (long)p2;
  result[3] = (long)(p3 = cgetg(l, t_COL));
  for (k = 1; k < l; k++) p3[k] = lgeti(3);
  result[4] = (long)(p4 = cgetg(l, t_COL));
  for (k = 1; k < l; k++) p4[k] = lgeti(3);
  av = avma;
  for (k = 1; k < l; k++)
  {
    GEN q = localreduction(e, (GEN)p1[k]);
    affii((GEN)q[1],(GEN)p2[k]);
    affii((GEN)q[2],(GEN)p3[k]);
    affii((GEN)q[4],(GEN)p4[k]);
    avma = av;
  }
  return result;
}
#endif

/* Algorithme de reduction d'une courbe sur Q a sa forme standard.  Etant
 * donne une courbe elliptique sous forme longue e, dont les coefficients
 * sont rationnels, renvoie son [N, [u, r, s, t], c], ou N est le conducteur
 * arithmetique de e, [u, r, s, t] est le changement de variables qui reduit
 * e a sa forme minimale globale dans laquelle a1 et a3 valent 0 ou 1, et a2
 * vaut -1, 0 ou 1 et tel que u est un rationnel positif. Enfin c est le
 * produit des nombres de Tamagawa locaux cp.
 */
GEN
globalreduction(GEN e1)
{
  long i, k, l, m, tetpil, av = avma;
  GEN p1, c = gun, prims, result, N = gun, u = gun, r, s, t;
  GEN v = cgetg(5, t_VEC), a = cgetg(7, t_VEC), e = cgetg(20, t_VEC);

  checkell(e1);
  for (i = 1; i < 5; i++) a[i] = e1[i]; a[5] = zero; a[6] = e1[5];
  prims = decomp(denom(a));
  p1 = (GEN)prims[1]; l = lg(p1);
  for (k = 1; k < l; k++)
  {
    int n = 0;
    for (i = 1; i < 7; i++)
      if (!gcmp0((GEN)a[i]))
      {
	m = i * n + ggval((GEN)a[i], (GEN)p1[k]);
	while (m < 0) { n++; m += i; }
      }
    u = gmul(u, gpuigs((GEN)p1[k], n));
  }
  v[1] = linv(u); v[2] = v[3] = v[4] = zero;
  for (i = 1; i < 14; i++) e[i] = e1[i];
  for (; i < 20; i++) e[i] = zero;
  if (!gcmp1(u)) e = coordch(e, v);
  prims = decomp((GEN)e[12]);
  l = lg(p1 = (GEN)prims[1]);
  for (k = (signe(e[12]) < 0) + 1; k < l; k++)
  {
    GEN q = localreduction(e, (GEN)p1[k]);
    GEN v1 = (GEN)q[3];
    N = mulii(N, gpui((GEN)p1[k],(GEN)q[1],0));
    c = mulii(c, (GEN)q[4]);
    if (!gcmp1((GEN)v1[1])) cumule1(&v, &e, v1);
  }
  s = gdiventgs((GEN)e[1], -2);
  r = gdiventgs(gaddgs(gsub(gsub((GEN)e[2], gmul(s,(GEN)e[1])), gsqr(s)), 1), -3);
  t = gdiventgs(ellLHS0(e,r), -2);
  cumule(&v, &e, gun, r, s, t);
  tetpil = avma;
  result = cgetg(4, t_VEC); result[1] = lcopy(N); result[2] = lcopy(v);
  result[3] = lcopy(c);
  return gerepile(av, tetpil, result);
}

/* cumule les effets de plusieurs chgts de variable. On traite a part les cas
 * particuliers frequents, tels que soit u = 1, soit r' = s' = t' = 0
 */
static void
cumulev(GEN *vtotal, GEN u, GEN r, GEN s, GEN t)
{
  long av = avma, tetpil;
  GEN temp, v = *vtotal, v3 = cgetg(5, t_VEC);
  if (gcmp1((GEN)v[1]))
  {
    v3[1] = lcopy(u);
    v3[2] = ladd((GEN)v[2], r);
    v3[3] = ladd((GEN)v[3], s);
    av = avma;
    temp = gadd((GEN)v[4], gmul((GEN)v[3], r));
    tetpil = avma;
    v3[4] = lpile(av, tetpil, gadd(temp, t));
  }
  else if (gcmp0(r) && gcmp0(s) && gcmp0(t))
  {
    v3[1] = lmul((GEN)v[1], u);
    v3[2] = lcopy((GEN)v[2]);
    v3[3] = lcopy((GEN)v[3]);
    v3[4] = lcopy((GEN)v[4]);
  }
  else /* cas general */
  {
    v3[1] = lmul((GEN)v[1], u);
    temp = gsqr((GEN)v[1]);
    v3[2] = ladd(gmul(temp, r), (GEN)v[2]);
    v3[3] = ladd(gmul((GEN)v[1], s), (GEN)v[3]);
    v3[4] = ladd((GEN)v[4], gmul(temp, gadd(gmul((GEN)v[1], t), gmul((GEN)v[3], r))));

    v3 = gerepilecopy(av, v3);
  }
  *vtotal = v3;
}

static void
cumule(GEN *vtotal, GEN *e, GEN u, GEN r, GEN s, GEN t)
{
  long av = avma, tetpil;
  GEN v2 = cgetg(5, t_VEC);
  v2[1] = (long)u; v2[2] = (long)r; v2[3] = (long)s; v2[4] = (long)t;
  tetpil = avma;
  *e = gerepile(av, tetpil, coordch(*e, v2));
  cumulev(vtotal, u, r, s, t);
}

static void
cumule1(GEN *vtotal, GEN *e, GEN v2)
{
  *e = coordch(*e, v2);
  cumulev(vtotal, (GEN)v2[1], (GEN)v2[2], (GEN)v2[3], (GEN)v2[4]);
}

/********************************************************************/
/**                                                                **/
/**                   Parametrisation modulaire                    **/
/**                                                                **/
/********************************************************************/

GEN
taniyama(GEN e)
{
  GEN v,w,c,d,s1,s2,s3;
  long n,m,av=avma,tetpil;

  checkell(e); v = cgetg(precdl+3,t_SER);
  v[1] = evalsigne(1) | evalvalp(-2) | evalvarn(0);
  v[2] = un;
  c=gtoser(anell(e,precdl+1),0); setvalp(c,1);
  d=ginv(c); c=gsqr(d);
  for (n=-3; n<=precdl-4; n++)
  {
    if (n!=2)
    {
      s3=n?gzero:(GEN)e[7];
      if (n>-3) s3=gadd(s3,gmul((GEN)e[6],(GEN)v[n+4]));
      s2=gzero;
      for (m=-2; m<=n+1; m++)
	s2 = gadd(s2,gmulsg(m*(n+m),gmul((GEN)v[m+4],(GEN)c[n-m+4])));
      s2=gmul2n(s2,-1);
      s1=gzero;
      for (m=-1; m+m<=n; m++)
      {
	if (m+m==n)
          s1=gadd(s1,gsqr((GEN)v[m+4]));
	else
          s1=gadd(s1,gmul2n(gmul((GEN)v[m+4],(GEN)v[n-m+4]),1));
      }
      v[n+6]=ldivgs(gsub(gadd(gmulsg(6,s1),s3),s2),(n+2)*(n+1)-12);
    }
    else
    {
      setlg(v,9); v[8]=(long)polx[MAXVARN];
      w=deriv(v,0); setvalp(w,-2);
      s1=gadd((GEN)e[8],gmul(v,gadd(gmul2n((GEN)e[7],1),gmul(v,gadd((GEN)e[6],gmul2n(v,2))))));
      setlg(v,precdl+3);
      s2=gsub(s1,gmul(c,gsqr(w)));
      s2=gsubst((GEN)s2[2],MAXVARN,polx[0]);
      v[n+6]=lneg(gdiv((GEN)s2[2],(GEN)s2[3]));
    }
  }
  w=gsub(gmul(polx[0],gmul(d,deriv(v,0))), ellLHS0(e,v));
  tetpil=avma; s1=cgetg(3,t_VEC); s1[1]=lcopy(v); s1[2]=lmul2n(w,-1);
  return gerepile(av,tetpil,s1);
}

/********************************************************************/
/**                                                                **/
/**                       TORSION POINTS (over Q)                  **/
/**                                                                **/
/********************************************************************/
/* assume e is defined over Q (use Mazur's theorem) */
GEN
orderell(GEN e, GEN p)
{
  GEN p1;
  long av=avma,k;

  checkell(e); checkpt(p);
  k=typ(e[13]);
  if (k!=t_INT && !is_frac_t(k))
    err(impl,"orderell for nonrational elliptic curves");
  p1=p; k=1;
  for (k=1; k<16; k++)
  {
    if (lg(p1)<3) { avma=av; return stoi(k); }
    p1 = addell(e,p1,p);
  }
  avma=av; return gzero;
}

/* one can do much better by factoring denom(D) (see ellglobalred) */
static GEN
ellintegralmodel(GEN e)
{
  GEN a = cgetg(6,t_VEC), v;
  long i;

  for (i=1; i<6; i++)
  {
    a[i]=e[i];
    switch(typ(a[i]))
    {
      case t_INT: case t_FRAC: case t_FRACN: break;
      default: err(talker, "not a rational curve in ellintegralmodel");
    }
  }
  a = denom(a); if (gcmp1(a)) return NULL;
  v = cgetg(5,t_VEC);
  v[1]=linv(a); v[2]=v[3]=v[4]=zero; return v;
}

/* Using Lutz-Nagell */

/* p is a polynomial of degree exactly 3 with integral coefficients
 * and leading term 4. Outputs the vector of rational roots of p
 */
static GEN
ratroot(GEN p)
{
  GEN v,a,ld;
  long i,t;

  i=2; while (!signe(p[i])) i++;
  if (i==5)
    { v=cgetg(2,t_VEC); v[1]=zero; return v; }
  if (i==4)
    { v=cgetg(3,t_VEC); v[1]=zero; v[2]=ldivgs((GEN)p[4],-4); return v; }

  v=cgetg(4,t_VEC); t=1;
  if (i==3) v[t++]=zero;
  ld=divisors(gmul2n((GEN)p[i],2));
  for (i=1; i<lg(ld); i++)
  {
    a = gmul2n((GEN)ld[i],-2);
    if (!gsigne(poleval(p,a))) v[t++]=(long)a;
    a = gneg_i(a);
    if (!gsigne(poleval(p,a))) v[t++]=(long)a;
  }
  setlg(v,t); return v;
}

static int
is_new_torsion(GEN e, GEN v, GEN p, long t2) {
  GEN pk = p, pkprec = NULL;
  long k,l;

  for (k=2; k<=6; k++)
  {
    pk=addell(e,pk,p);
    if (lg(pk)==2) return 1;

    for (l=2; l<=t2; l++)
      if (gegal((GEN)pk[1],gmael(v,l,1))) return 1;

    if (pkprec && k<=5)
      if (gegal((GEN)pk[1],(GEN)pkprec[1])) return 1;
    pkprec=pk;
  }
  return 0;
}

GEN
torsellnagelllutz(GEN e)
{
  GEN d,ld,pol,p1,lr,r,v,w,w2,w3;
  long i,j,nlr,t,t2,k,k2,av=avma;

  checkell(e);
  v = ellintegralmodel(e);
  if (v) e = coordch(e,v);
  pol = RHSpol(e);
  lr=ratroot(pol); nlr=lg(lr)-1;
  r=cgetg(17,t_VEC); p1=cgetg(2,t_VEC); p1[1]=zero; r[1]=(long)p1;
  for (t=1,i=1; i<=nlr; i++)
  {
    p1=cgetg(3,t_VEC);
    p1[1] = lr[i];
    p1[2] = lmul2n(gneg(ellLHS0(e,(GEN)lr[i])), -1);
    r[++t]=(long)p1;
  }
  ld = factor(gmul2n(absi((GEN)e[12]), 4));
  p1 = (GEN)ld[2]; k = lg(p1);
  for (i=1; i<k; i++) p1[i] = lshifti((GEN)p1[i], -1);
  ld = divisors(ld);
  for (t2=t,j=1; j<lg(ld); j++)
  {
    d=(GEN)ld[j]; lr=ratroot(gsub(pol,gsqr(d)));
    for (i=1; i<lg(lr); i++)
    {
      p1 = cgetg(3,t_VEC);
      p1[1] = lr[i];
      p1[2] = lmul2n(gsub(d,ellLHS0(e,(GEN)lr[i])), -1);

      if (is_new_torsion(e,r,p1,t2))
      {
        GEN p2 = cgetg(3,t_VEC);
        p2[1] = p1[1];
        p2[2] = lsub((GEN)p1[2],d);
	r[++t]=(long)p1;
        r[++t]=(long)p2;
      }
    }
  }
  if (t==1)
  {
    avma=av; w=cgetg(4,t_VEC);
    w[1] = un;
    w[2] = lgetg(1,t_VEC);
    w[3] = lgetg(1,t_VEC);
    return w;
  }

  if (nlr<3)
  {
    w2=cgetg(2,t_VEC); w2[1]=lstoi(t);
    for (k=2; k<=t; k++)
      if (itos(orderell(e,(GEN)r[k])) == t) break;
    if (k>t) err(bugparier,"torsell (bug1)");

    w3=cgetg(2,t_VEC); w3[1]=r[k];
  }
  else
  {
    if (t&3) err(bugparier,"torsell (bug2)");
    t2 = t>>1;
    w2=cgetg(3,t_VEC); w2[1]=lstoi(t2); w2[2]=(long)gdeux;
    for (k=2; k<=t; k++)
      if (itos(orderell(e,(GEN)r[k])) == t2) break;
    if (k>t) err(bugparier,"torsell (bug3)");

    p1 = powell(e,(GEN)r[k],stoi(t>>2));
    k2 = (lg(p1)==3 && gegal((GEN)r[2],p1))? 3: 2;
    w3=cgetg(3,t_VEC); w3[1]=r[k]; w3[2]=r[k2];
  }
  if (v)
  {
    v[1] = linv((GEN)v[1]);
    w3 = pointch(w3,v);
  }
  w=cgetg(4,t_VEC);
  w[1] = lstoi(t);
  w[2] = (long)w2;
  w[3] = (long)w3;
  return gerepilecopy(av, w);
}

/* Using Doud's algorithm */

/* finds a bound for #E_tor */
static long
torsbound(GEN e)
{
  long av = avma, m, b, c, d, prime = 2;
  byteptr p = diffptr;
  GEN D = (GEN)e[12];
  long n = lgefint(D); /* number of primes to try */
  b = c = m = 0; p++;
  while (m<n)
  {
    d = *p++; if (!d) err(primer1);
    prime += d;
    if (ggval(D,stoi(prime)) == 0)
    {
      b = cgcd(b, prime+1 - itos(apell0(e,prime)));
      if (b==c) m++; else {c = b; m = 0;}
      avma = av;
    }
  }
  return b;
}

static GEN
_round(GEN x, long *e)
{
  GEN y = grndtoi(x,e);
  if (*e > -5 && bit_accuracy(gprecision(x)) < gexpo(y) - 10)
    err(talker, "ellinit data not accurate enough. Increase precision");
  return y;
}

/* Input the curve, a point, and an integer n, returns a point of order n
   on the curve, or NULL if q is not rational. */
static GEN
torspnt(GEN E, GEN q, long n)
{
  GEN p = cgetg(3,t_VEC);
  long e;
  p[1] = lmul2n(_round(gmul2n((GEN)q[1],2), &e),-2);
  if (e > -5) return NULL;
  p[2] = lmul2n(_round(gmul2n((GEN)q[2],3), &e),-3);
  if (e > -5) return NULL;
  return (gcmp0(gimag(p)) && oncurve(E,p)
      && lg(powell(E,p,stoi(n))) == 2
      && itos(orderell(E,p)) == n)? greal(p): NULL;
}

static int
smaller_x(GEN p, GEN q)
{
  int s = absi_cmp(denom(p), denom(q));
  return (s<0 || (s==0 && absi_cmp(numer(p),numer(q)) < 0));
}

/* best generator in cycle of length k */
static GEN
best_in_cycle(GEN e, GEN p, long k)
{
  GEN p0 = p,q = p;
  long i;

  for (i=2; i+i<k; i++)
  {
    q = addell(e,q,p0);
    if (cgcd(i,k)==1 && smaller_x((GEN)q[1], (GEN)p[1])) p = q;
  }
  return (gsigne(d_ellLHS(e,p)) < 0)? invell(e,p): p;
}

static GEN
tors(GEN e, long k, GEN p, GEN q, GEN v)
{
  GEN p1,r;
  if (q)
  {
    long n = k>>1;
    GEN p1, best = q, np = powell(e,p,stoi(n));
    if (n % 2 && smaller_x((GEN)np[1], (GEN)best[1])) best = np;
    p1 = addell(e,q,np);
    if (smaller_x((GEN)p1[1], (GEN)best[1])) q = p1;
    else if (best == np) { p = addell(e,p,q); q = np; }
    p = best_in_cycle(e,p,k);
    if (v)
    {
      v[1] = linv((GEN)v[1]);
      p = pointch(p,v);
      q = pointch(q,v);
    }
    r = cgetg(4,t_VEC);
    r[1] = lstoi(2*k); p1 = cgetg(3,t_VEC); p1[1] = lstoi(k); p1[2] = deux;
    r[2] = (long)p1; p1 = cgetg(3,t_VEC); p1[1] = lcopy(p); p1[2] = lcopy(q);
    r[3] = (long)p1;
  }
  else
  {
    if (p)
    {
      p = best_in_cycle(e,p,k);
      if (v)
      {
        v[1] = linv((GEN)v[1]);
        p = pointch(p,v);
      }
      r = cgetg(4,t_VEC);
      r[1] = lstoi(k); p1 = cgetg(2,t_VEC); p1[1] = r[1];
      r[2] = (long)p1; p1 = cgetg(2,t_VEC); p1[1] = lcopy(p);
      r[3] = (long)p1;
    }
    else
    {
      r = cgetg(4,t_VEC);
      r[1] = un;
      r[2] = lgetg(1,t_VEC);
      r[3] = lgetg(1,t_VEC);
    }
  }
  return r;
}

GEN
torselldoud(GEN e)
{
  long b,i,ord,av=avma,prec, k = 1;
  GEN v,w1,w22,w1j,w12,p,tor1,tor2;

  checkbell(e);
  v = ellintegralmodel(e);
  if (v) e = coordch(e,v);

  b = lgefint((GEN)e[12]) >> 1; /* b = size of sqrt(D) */
  prec = precision((GEN)e[15]);
  if (prec < b) err(precer, "torselldoud");
  b = max(b, DEFAULTPREC);
  if (b < prec) { prec = b; e = gprec_w(e, b); }
  b = torsbound(e);
  if (b==1) { avma=av; return tors(e,1,NULL,NULL, v); }
  w22 = gmul2n((GEN)e[16],-1);
  w1 = (GEN)e[15];
  if (b % 4)
  {
    p = NULL;
    for (i=10; i>1; i--)
    {
      if (b%i != 0) continue;
      w1j = gdivgs(w1,i);
      p = torspnt(e,pointell(e,w1j,prec),i);
      if (!p && i%2==0)
      {
        p = torspnt(e,pointell(e,gadd(w22,w1j),prec),i);
        if (!p) p = torspnt(e,pointell(e,gadd(w22,gmul2n(w1j,1)),prec),i);
      }
      if (p) { k = i; break; }
    }
    return gerepileupto(av, tors(e,k,p,NULL, v));
  }

  ord = 0; tor1 = tor2 = NULL;
  w12 = gmul2n((GEN)e[15],-1);
  if ((p = torspnt(e,pointell(e,w12,prec),2)))
  {
    tor1 = p; ord++;
  }
  if ((p = torspnt(e,pointell(e,w22,prec),2))
   || (!ord && (p = torspnt(e,pointell(e,gadd(w12,w22),prec),2))))
  {
    tor2 = p; ord += 2;
  }

  switch(ord)
  {
    case 0:
      for (i=9; i>1; i-=2)
      {
        if (b%i!=0) continue;
        w1j=gdivgs((GEN)e[15],i);
        p = torspnt(e,pointell(e,w1j,prec),i);
        if (p) { k = i; break; }
      }
      break;

    case 1:
      p = NULL;
      for (i=12; i>2; i-=2)
      {
        if (b%i!=0) continue;
        w1j=gdivgs((GEN)e[15],i);
        p = torspnt(e,pointell(e,w1j,prec),i);
        if (!p && i%4==0)
          p = torspnt(e,pointell(e,gadd(w22,w1j),prec),i);
        if (p) { k = i; break; }
      }
      if (!p) { p = tor1; k = 2; }
      break;

    case 2:
      for (i=5; i>1; i-=2)
      {
        if (b%i!=0) continue;
        w1j = gdivgs((GEN)e[15],i);
        p = torspnt(e,pointell(e,gadd(w22,w1j),prec),i+i);
        if (p) { k = 2*i; break; }
      }
      if (!p) { p = tor2; k = 2; }
      tor2 = NULL; break;

    case 3:
      for (i=8; i>2; i-=2)
      {
        if (b%(2*i)!=0) continue;
        w1j=gdivgs((GEN)e[15],i);
        p = torspnt(e,pointell(e,w1j,prec),i);
        if (p) { k = i; break; }
      }
      if (!p) { p = tor1; k = 2; }
      break;
  }
  return gerepileupto(av, tors(e,k,p,tor2, v));
}

GEN
elltors0(GEN e, long flag)
{
  switch(flag)
  {
    case 0: return torselldoud(e);
    case 1: return torsellnagelllutz(e);
    default: err(flagerr,"torsell");
  }
  return NULL; /* not reached */
}

/* par compatibilite */
GEN torsell(GEN e) {return torselldoud(e);}

/* LOCAL ROOT NUMBERS, D'APRES HALBERSTADT halberst@math.jussieu.fr */

/* ici p=2 ou 3 */
static long
neron(GEN e, GEN p, long* ptkod)
{
  long av=avma,kod,v4,v6,vd;
  GEN c4, c6, d, nv;

  nv=localreduction(e,p);
  kod=itos((GEN)nv[2]); *ptkod=kod;
  c4=(GEN)e[10]; c6=(GEN)e[11]; d=(GEN)e[12];
  v4=gcmp0(c4) ? 12 : ggval(c4,p);
  v6=gcmp0(c6) ? 12 : ggval(c6,p);
  vd=ggval(d,p);
  avma=av;
  switch(itos(p))
  {
    case 3:
      if (labs(kod)>4) return 1;
      else
      {
	switch(kod)
	{
	  case -1: case 1: return v4&1 ? 2 : 1;
	  case -3: case 3: return (2*v6>vd+3) ? 2 : 1;
	  case -4: case 2:
	    switch (vd%6)
	    {
	      case 4: return 3;
	      case 5: return 4;
	      default: return v6%3==1 ? 2 : 1;
	    }
	  default: /* kod = -2 et 4 */
	    switch (vd%6)
	    {
	      case 0: return 2;
	      case 1: return 3;
	      default: return 1;
	    }
	}
      }
    case 2:
      if (kod>4) return 1;
      else
      {
	switch(kod)
        {
	  case 1: return (v6>0) ? 2 : 1;
	  case 2:
	    if (vd==4) return 1;
	    else
	    {
	      if (vd==7) return 3;
	      else return v4==4 ? 2 : 4;
	    }
	  case 3:
	    switch(vd)
	    {
	      case 6: return 3;
	      case 8: return 4;
	      case 9: return 5;
	      default: return v4==5 ? 2 : 1;
	    }
	  case 4: return v4>4 ? 2 : 1;
	  case -1:
	    switch(vd)
	    {
	      case 9: return 2;
	      case 10: return 4;
	      default: return v4>4 ? 3 : 1;
	    }
	  case -2:
	    switch(vd)
	    {
	      case 12: return 2;
	      case 14: return 3;
	      default: return 1;
	    }
	  case -3:
	    switch(vd)
	    {
	      case 12: return 2;
	      case 14: return 3;
	      case 15: return 4;
	      default: return 1;
	    }
	  case -4: return v6==7 ? 2 : 1;
	  case -5: return (v6==7 || v4==6) ? 2 : 1;
	  case -6:
	    switch(vd)
	    {
	      case 12: return 2;
	      case 13: return 3;
	      default: return v4==6 ? 2 : 1;
	    }
	  case -7: return (vd==12 || v4==6) ? 2 : 1;
	  default: return v4==6 ? 2 : 1;
	}
      }
    default: return 0; /* should not occur */
  }
}

static long
ellrootno_2(GEN e)
{
  long n2,kod,u,v,x1,y1,d1,av=avma,v4,v6,w2;
  GEN p=gdeux,c4,c6,tmp,p6;

  n2=neron(e,p,&kod); c4=(GEN)e[10]; c6=(GEN)e[11]; p6=stoi(64);
  if (gcmp0(c4)) {v4=12; u=0;}
  else {v4=pvaluation(c4,p,&tmp); u=itos(modii(tmp,p6));}
  if (gcmp0(c6)) {v6=12; v=0;}
  else {v6=pvaluation(c6,p,&tmp); v=itos(modii(tmp,p6));}
  (void)pvaluation((GEN)e[12],p,&tmp); d1=itos(modii(tmp,p6));
  avma=av; x1=u+v+v;
  if (kod>=5)
    {w2=mpodd(addii((GEN)e[2],(GEN)e[3])) ? 1 : -1; avma=av; return w2;}
  if (kod<-9) return (n2==2) ? -kross(-1,v) : -1;
  switch(kod)
  {
    case 1: return 1;
    case 2:
      switch(n2)
      {
	case 1:
	  switch(v4)
	  {
	    case 4: return kross(-1,u);
	    case 5: return 1;
	    default: return -1;
	  }
	case 2: return (v6==7) ? 1 : -1;
	case 3: return (v%8==5 || (u*v)%8==5) ? 1 : -1;
	case 4: if (v4>5) return kross(-1,v);
	  return (v4==5) ? -kross(-1,u) : -1;
      }
    case 3:
      switch(n2)
      {
	case 1: return -kross(2,u*v);
	case 2: return -kross(2,v);
	case 3: y1=itos(modis(gsubsg(u,gmul2n(c6,-5)),16)); avma=av;
	  return (y1==7 || y1==11) ? 1 : -1;
	case 4: return (v%8==3 || (2*u+v)%8==7) ? 1 : -1;
	case 5: return v6==8 ? kross(2,x1) : kross(-2,u);
      }
    case -1:
      switch(n2)
      {
	case 1: return -kross(2,x1);
	case 2: return (v%8==7) || (x1%32==11) ? 1 : -1;
	case 3: return v4==6 ? 1 : -1;
	case 4: if (v4>6) return kross(-1,v);
	  return v4==6 ? -kross(-1,u*v) : -1;
      }
    case -2: return n2==1 ? kross(-2,v) : kross(-1,v);
    case -3:
      switch(n2)
      {
	case 1: y1=(u-2*v)%64; if (y1<0) y1+=64;
	  return (y1==3) || (y1==19) ? 1 : -1;
	case 2: return kross(2*kross(-1,u),v);
	case 3: return -kross(-1,u)*kross(-2*kross(-1,u),u*v);
	case 4: return v6==11 ? kross(-2,x1) : -kross(-2,u);
      }
    case -5:
      if (n2==1) return x1%32==23 ? 1 : -1;
      else return -kross(2,2*u+v);
    case -6:
      switch(n2)
      {
	case 1: return 1;
	case 2: return v6==10 ? 1 : -1;
	case 3: return (u%16==11) || ((u+4*v)%16==3) ? 1 : -1;
      }
    case -7:
      if (n2==1) return 1;
      else
      {
	y1=itos(modis(gaddsg(u,gmul2n(c6,-8)),16)); avma=av;
	if (v6==10) return (y1==9) || (y1==13) ? 1 : -1;
	else return (y1==9) || (y1==5) ? 1 : -1;
      }
    case -8: return n2==2 ? kross(-1,v*d1) : -1;
    case -9: return n2==2 ? -kross(-1,d1) : -1;
    default: return -1;
  }
}

static long
ellrootno_3(GEN e)
{
  long n2,kod,u,v,d1,av=avma,r6,K4,K6,v4;
  GEN p=stoi(3),c4,c6,tmp,p4;

  n2=neron(e,p,&kod); c4=(GEN)e[10]; c6=(GEN)e[11]; p4=stoi(81);
  if (gcmp0(c4)) { v4=12; u=0; }
  else { v4=pvaluation(c4,p,&tmp); u=itos(modii(tmp,p4)); }
  if (gcmp0(c6)) v=0;
  else {(void)pvaluation(c6,p,&tmp); v=itos(modii(tmp,p4));}
  (void)pvaluation((GEN)e[12],p,&tmp); d1=itos(modii(tmp,p4));
  avma=av;
  r6=v%9; K4=kross(u,3); K6=kross(v,3);
  if (kod>4) return K6;
  switch(kod)
  {
    case 1: case 3: case -3: return 1;
    case 2:
      switch(n2)
      {
	case 1: return (r6==4 || r6>6) ? 1 : -1;
	case 2: return -K4*K6;
	case 3: return 1;
	case 4: return -K6;
      }
    case 4:
      switch(n2)
      {
	case 1: return K6*kross(d1,3);
	case 2: return -K4;
	case 3: return -K6;
      }
    case -2: return n2==2 ? 1 : K6;
    case -4:
      switch(n2)
      {
	case 1:
	  if (v4==4) return (r6==4 || r6==8) ? 1 : -1;
	  else return (r6==1 || r6==2) ? 1 : -1;
	case 2: return -K6;
	case 3: return (r6==2 || r6==7) ? 1 : -1;
	case 4: return K6;
      }
    default: return -1;
  }
}

static long
ellrootno_not23(GEN e, GEN p, GEN ex)
{
  GEN j;
  long ep,z;

  if (gcmp1(ex)) return -kronecker(negi((GEN)e[11]),p);
  j=(GEN)e[13];
  if (!gcmp0(j) && ggval(j,p) < 0) return kronecker(negi(gun),p);
  ep=12/cgcd(12,ggval((GEN)e[12],p));
  if (ep==4) z=2;
  else z=(ep%2==0) ? 1 : 3;
  return kronecker(stoi(-z),p);
}

static long
ellrootno_intern(GEN e, GEN p, GEN ex)
{
  if (cmpis(p,3) > 0) return ellrootno_not23(e,p,ex);
  switch(itos(p))
  {
    case 3: return ellrootno_3(e);
    case 2: return ellrootno_2(e);
    default: err(talker,"incorrect prime in ellrootno_intern");
  }
  return 0; /* not reached */
}
	
/* local epsilon factor at p, including p=0 for the infinite place. Global
   if p==1. The equation can be non minimal, but must be over Q. Internal,
   no garbage collection. */
static long
ellrootno_all(GEN e, GEN p, GEN* ptcond)
{
  long s,exs,i;
  GEN fa,gr,cond,pr,ex;

  gr=globalreduction(e);
  e=coordch(e,(GEN)gr[2]);
  cond=(GEN)gr[1]; if(ptcond) *ptcond=cond;
  if (typ(e[12]) != t_INT)
    err(talker,"not an integral curve in ellrootno");
  if (typ(p) != t_INT || signe(p)<0)
    err(talker,"not a nonnegative integer second arg in ellrootno");
  exs = 0; /* gcc -Wall */
  if (cmpis(p,2)>=0)
  {
    exs=ggval(cond,p);
    if (!exs) return 1;
  }
  if (cmpis(p,3)>0) return ellrootno_not23(e,p,stoi(exs));
  switch(itos(p))
  {
    case 3: return ellrootno_3(e);
    case 2: return ellrootno_2(e);
    case 1: s=-1; fa=factor(cond); pr=(GEN)fa[1]; ex=(GEN)fa[2];
      for (i=1; i<lg(pr); i++) s*=ellrootno_intern(e,(GEN)pr[i],(GEN)ex[i]);
      return s;
    default: return -1; /* case 0: local factor at infinity = -1 */
  }
}

long
ellrootno(GEN e, GEN p)
{
  long av=avma,s;
  if (!p) p = gun;
  s=ellrootno_all(e, p, NULL);
  avma=av; return s;
}
