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

void
checkell(GEN e)
{
  long lx=lg(e);
  if (typ(e)!=t_VEC || lx<14) err(elliper1);
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
  GEN z = cgetg(6, t_POL); z[1] = evalsigne(1);
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
  GEN b2, b4, b6, b8, d, j, a11, a13, a33, a64, b81, b22, c4, c6;
  long i;

  checksell(x); for (i=1; i<=5; i++) y[i] = x[i];
  a11 = gsqr((GEN)y[1]);
  b2 = gadd(a11, gmul2n((GEN)y[2],2));
  y[6] = (long)b2;

  a13 = gmul((GEN)y[1],(GEN)y[3]);
  b4 = gadd(a13, gmul2n((GEN)y[4],1));
  y[7] = (long)b4;

  a33 = gsqr((GEN)y[3]);
  a64 = gmul2n((GEN)y[5],2); b6 = gadd(a33,a64);
  y[8] = (long)b6;

  b81 = gadd(gadd(gmul(a11,(GEN)y[5]),gmul(a64,(GEN)y[2])),gmul((GEN)y[2],a33));
  b8 = gsub(b81,gmul((GEN)y[4],gadd((GEN)y[4],a13)));
  y[9] = (long)b8;

  b22 = gsqr(b2);
  c4 = gadd(b22,gmulsg(-24,b4));
  y[10] = (long)c4;

  c6 = gadd(gmul(b2,gsub(gmulsg(36,b4),b22)),gmulsg(-216,b6));
  y[11] = (long)c6;

  b81 = gadd(gmul(b22,b8),gmulsg(27,gsqr(b6)));
  d = gsub(gmul(b4,gadd(gmulsg(9,gmul(b2,b6)),gmulsg(-8,gsqr(b4)))),b81);
  y[12] = (long)d;
  if (gcmp0(d)) err(talker,"singular curve in ellinit");

  j = gdiv(gmul(gsqr(c4),c4), d);
  y[13] = (long)j;
}

GEN
smallinitell(GEN x)
{
  pari_sp av = avma;
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
  pari_sp av = avma;
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
  GEN p1, r1, a, b, x, x1;
  long G = 6 - bit_accuracy(prec);

  x1 = gmul2n(gsub(a1,b1),-2);
  if (gcmp0(x1)) err(precer,"initell");
  for(;;)
  {
    a = a1; b = b1; x = x1;
    b1 = gsqrt(gmul(a,b),prec); setsigne(b1, sw);
    a1 = gmul2n(gadd(gadd(a,b), gmul2n(b1,1)),-2);
    r1 = gsub(a1,b1);
    p1 = gsqrt(gdiv(gadd(x,r1),x),prec);
    x1 = gmul(x,gsqr(gmul2n(gaddsg(1,p1),-1)));
    if (gcmp0(r1) || gexpo(r1) <= G + gexpo(b1)) break;
  }
  if (gprecision(x1)*2 <= (prec+2)) err(precer,"initell");
  *ptx1 = x1; return ginv(gmul2n(a1,2));
}

static GEN
do_padic_agm(GEN *ptx1, GEN a1, GEN b1, GEN p)
{
  GEN p1, r1, a, b, x, bmod1, bmod = modii((GEN)b1[4],p), x1 = *ptx1;
  long mi;
  
  if (!x1) x1 = gmul2n(gsub(a1,b1),-2);
  mi = min(precp(a1),precp(b1));
  for(;;)
  {
    a = a1; b = b1; x = x1;
    b1 = gprec(gsqrt(gmul(a,b),0),mi); bmod1 = modii((GEN)b1[4],p);
    if (!egalii(bmod1,bmod)) b1 = gneg_i(b1);
    a1 = gprec(gmul2n(gadd(gadd(a,b),gmul2n(b1,1)),-2),mi);
    r1 = gsub(a1,b1);
    if (gcmp0(r1)) {x1 = x; break;}
    p1 = gsqrt(gdiv(gadd(x,r1),x),0);
    if (! gcmp1(modii((GEN)p1[4],p))) p1 = gneg_i(p1);
    x1 = gmul(x, gsqr(gmul2n(gaddsg(1,p1),-1)));
  }
  *ptx1 = x1; return ginv(gmul2n(a1,2));
}

static GEN
padic_initell(GEN y, GEN p, long prec)
{
 GEN b2, b4, c4, c6, p1, w, pv, a1, b1, x1, u2, q, e0, e1;
  long i, alpha;

  q=gadd(gun,ggrandocp(p,prec));
  for (i=1; i<=13; i++) y[i]=lmul(q,(GEN)y[i]);
  if (gcmp0((GEN)y[13]) || valp((GEN)y[13]) >= 0) /* p | j */
    err(talker,"valuation of j must be negative in p-adic ellinit");
  if (egalii(p,gdeux))
  {
    pv = stoi(4); 
    err(impl,"initell for 2-adic numbers");
  }
  else
    pv = p;

  b2 = (GEN)y[6];
  b4 = (GEN)y[7];
  c4 = (GEN)y[10];
  c6 = (GEN)y[11];
  alpha = valp(c4) >> 1;
  setvalp(c4,0);
  setvalp(c6,0);
  e1 = gdiv(c6, gmulsg(6,c4));
  c4 = gdivgs(c4,48);
  c6 = gdivgs(c6,864);
  do
  {
    GEN e2 = gsqr(e1);
    e0 = e1;
    e1 = gdiv(gadd(gmul2n(gmul(e0,e2),1),c6), gsub(gmulsg(3,e2),c4));
  }
  while (!gegal(e0,e1));
  setvalp(e1, valp(e1)+alpha);

  e1 = gsub(e1, gdivgs(b2,12));
  w = gsqrt(gmul2n(gadd(b4,gmul(e1,gadd(b2,gmulsg(6,e1)))),1), 0);

  p1 = gaddgs(gdiv(gmulsg(3,e0),w),1);
  if (valp(p1) <= 0) w = gneg_i(w);
  y[18] = (long)w;

  a1 = gmul2n(gsub(w,gadd(gmulsg(3,e1),gmul2n(b2,-2))),-2);
  b1 = gmul2n(w,-1); x1 = NULL;
  u2 = do_padic_agm(&x1,a1,b1,pv);

  w = gaddsg(1,ginv(gmul2n(gmul(u2,x1),1)));
  w = gadd(w,gsqrt(gaddgs(gsqr(w),-1),0));
  if (gcmp0(w)) err(precer,"initell");
  q = ginv(w);
  if (valp(q) < 0) q = ginv(q);

  y[14] = (long)_vec(e1);
  y[15] = (long)u2;
  y[16] = (kronecker((GEN)u2[4],p) <= 0 || (valp(u2)&1))? zero: lsqrt(u2,0);
  y[17] = (long)q;
  y[19] = zero; return y;
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
    p1 = gen_sort(real_i(p1), 0, invcmp);
  y[14] = (long)p1;

  e1 = (GEN)p1[1];
  w  = gsqrt(gmul2n(gadd(b4,gmul(e1,gadd(b2,gmulsg(6,e1)))),1),prec);
  p2 = gadd(gmulsg(3,e1), gmul2n(b2,-2));
  if (gsigne(p2) > 0) w = gneg_i(w);
  a1 = gmul2n(gsub(w,p2),-2);
  b1 = gmul2n(w,-1); sw = signe(w);
  u2 = do_agm(&x1,a1,b1,prec,sw); /* 1/4M */

  w = gaddsg(1, ginv(gmul2n(gmul(u2,x1),1)));
  q = gsqrt(gaddgs(gsqr(w),-1),prec);
  if (gsigne(real_i(w)) > 0)
    q = ginv(gadd(w, q));
  else
    q = gsub(w, q);
  if (gexpo(q) >= 0) q = ginv(q);
  pi = mppi(prec); pi2 = gmul2n(pi,1);
  tau = gmul(gdiv(glog(q,prec),pi2), gneg_i(gi));

  y[19] = lmul(gmul(gsqr(pi2),gabs(u2,prec)), imag_i(tau));
  w1 = gmul(pi2, gsqrt(gneg_i(u2),prec));
  w2 = gmul(tau, w1);
  if (sw < 0)
    q = gsqrt(q,prec);
  else
  {
    w1= gmul2n(gabs((GEN)w2[1],prec), 1);
    q = gexp(gmul(PiI2n(0,prec), gdiv(w2,w1)), prec);
  }
  y[15] = (long)w1;
  y[16] = (long)w2;
  p2 = thetanullk(q, 1, prec);
  if (gcmp0(p2)) err(precer,"initell");
  /* pi^2 / 6w1 * theta'''(q,0) / theta'(q,0) */
  y[17] = ldiv(gmul(gsqr(pi),thetanullk(q,3,prec)), gmul(gmulsg(6,w1), p2));
  y[18] = ldiv(gsub(gmul((GEN)y[17],w2), gmul(gi,pi)), w1);
  return y;
}

GEN
initell(GEN x, long prec)
{
  pari_sp av = avma;
  return gerepilecopy(av, initell0(x,prec));
}

GEN
_coordch(GEN e, GEN u, GEN r, GEN s, GEN t)
{
  GEN y, p1, p2, v, v2, v3, v4, v6;
  long i, lx = lg(e);
  pari_sp av = avma;

  y = cgetg(lx,t_VEC);
  v = ginv(u); v2 = gsqr(v); v3 = gmul(v,v2);v4 = gsqr(v2); v6 = gsqr(v3);
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
  if (lx > 14)
  {
    p1 = (GEN)e[14];
    if (gcmp0(p1))
    {
      y[14] = y[15] = y[16] = y[17] = y[18] = y[19] = zero;
    }
    else if (typ(e[1])==t_PADIC)
    {
      y[14] = (long)_vec( gmul(v2, gsub((GEN)p1[1],r)) );
      y[15] = lmul((GEN)e[15], gsqr(u));
      y[16] = lmul((GEN)e[16], u);
      y[17] = e[17];
      y[18] = e[18]; /* FIXME: how do q and w change ? */
      y[19] = zero;
    }
    else
    {
      p2 = cgetg(4,t_COL);
      for (i=1; i<=3; i++) p2[i] = lmul(v2, gsub((GEN)p1[i],r));
      y[14] = (long)p2;
      y[15] = lmul((GEN)e[15], u);
      y[16] = lmul((GEN)e[16], u);
      y[17] = ldiv((GEN)e[17], u);
      y[18] = ldiv((GEN)e[18], u);
      y[19] = lmul((GEN)e[19], gsqr(u));
    }
  }
  return gerepilecopy(av,y);
}

GEN
coordch(GEN e, GEN ch)
{
  checkch(ch); checkell(e);
  return _coordch(e, (GEN)ch[1], (GEN)ch[2], (GEN)ch[3], (GEN)ch[4]);
}

static GEN
pointch0(GEN x, GEN v2, GEN v3, GEN mor, GEN s, GEN t)
{
  GEN p1,z;

  if (lg(x) < 3) return x;

  z = cgetg(3,t_VEC); p1 = gadd((GEN)x[1],mor);
  z[1] = lmul(v2, p1);
  z[2] = lmul(v3, gsub((GEN)x[2], gadd(gmul(s,p1),t)));
  return z;
}

GEN
pointch(GEN x, GEN ch)
{
  GEN y,v,v2,v3,mor,r,s,t,u;
  long tx, i, lx = lg(x);
  pari_sp av = avma;

  checkpt(x); checkch(ch);
  if (lx < 2) return gcopy(x);
  u = (GEN)ch[1];
  r = (GEN)ch[2];
  s = (GEN)ch[3];
  t = (GEN)ch[4];
  v = ginv(u); v2 = gsqr(v); v3 = gmul(v,v2);
  mor = gneg_i(r);
  tx = typ(x[1]); 
  if (is_matvec_t(tx))
  {
    y = cgetg(lx,tx);
    for (i=1; i<lx; i++)
      y[i] = (long)pointch0((GEN)x[i],v2,v3,mor,s,t);
  }
  else
    y = pointch0(x,v2,v3,mor,s,t);
  return gerepilecopy(av,y);
}

static long
ellexpo(GEN E)
{
  long i, f, e = -(long)HIGHEXPOBIT;
  for (i=1; i<=5; i++)
  {
    f = gexpo((GEN)E[i]);
    if (f > e) e = f;
  }
  return e;
}

/* Exactness of lhs and rhs in the following depends in non-obvious ways
 * on the coeffs of the curve as well as on the components of the point z.
 * Thus if e is exact, with a1==0, and z has exact y coordinate only, the
 * lhs will be exact but the rhs won't. */
int
oncurve(GEN e, GEN z)
{
  GEN LHS, RHS, x;
  long pl, pr, ex, expx;
  pari_sp av;

  checksell(e); checkpt(z); if (lg(z) < 3) return 1; /* oo */
  av = avma;
  LHS = ellLHS(e,z);
  RHS = ellRHS(e,(GEN)z[1]); x = gsub(LHS,RHS);
  if (gcmp0(x)) { avma = av; return 1; }
  pl = precision(LHS);
  pr = precision(RHS);
  if (!pl && !pr) { avma = av; return 0; } /* both of LHS, RHS are exact */
  /* at least one of LHS,RHS is inexact */
  ex = pr? gexpo(RHS): gexpo(LHS); /* don't take exponent of exact 0 */
  if (!pr || (pl && pl < pr)) pr = pl; /* min among nonzero elts of {pl,pr} */
  expx = gexpo(x);
  pr = (expx < ex - bit_accuracy(pr) + 15
     || expx < ellexpo(e) - bit_accuracy(pr) + 5);
  avma = av; return pr;
}

GEN
addell(GEN e, GEN z1, GEN z2)
{
  GEN p1,p2,x,y,x1,x2,y1,y2;
  pari_sp av=avma, tetpil;

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
      if (!eq) { avma=av; return _vec(gzero); }
    }
    p2 = d_ellLHS(e,z1);
    if (gcmp0(p2)) { avma=av; return _vec(gzero); }
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
  pari_sp av=avma, tetpil;

  checksell(e); checkpt(z2);
  z2=invell(e,z2); tetpil=avma;
  return gerepile(av,tetpil,addell(e,z1,z2));
}

GEN
ordell(GEN e, GEN x, long prec)
{
  long td, i, lx, tx=typ(x);
  pari_sp av=avma;
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
  GEN x,y,p0,p1,q0,q1,z1,z2,pol,grdx;
  long ln, ep, vn;
  pari_sp av = avma;

  if (lg(z) < 3) return gcopy(z);
  pol = (GEN)n[1];
  if (signe(discsr(pol)) >= 0)
    err(talker,"not a negative quadratic discriminant in CM");
  if (!gcmp1(denom((GEN)n[2])) || !gcmp1(denom((GEN)n[3])))
    err(impl, "powell for nonintegral CM exponent");

  p1 = shifti(addsi(1, gnorm(n)), 2);
  if (is_bigint(p1) > 0) err(talker, "norm too large in CM");
  ln = itos(p1); vn = (ln-4)>>2;
  z1 = weipell(e, ln);
  z2 = gsubst(z1, 0, gmul(n,polx[0]));
  grdx = gadd((GEN)z[1], gdivgs((GEN)e[6],12));
  p0 = gzero; p1 = gun;
  q0 = gun;   q1 = gzero;
  do
  {
    GEN p2,q2, ss = gzero;
    do
    {
      ep = (-valp(z2)) >> 1;
      ss = gadd(ss, gmul((GEN)z2[2], gpowgs(polx[0], ep)));
      z2 = gsub(z2, gmul((GEN)z2[2], gpowgs(z1, ep)));
    }
    while (valp(z2) <= 0);
    p2 = gadd(p0, gmul(ss,p1)); p0 = p1; p1 = p2;
    q2 = gadd(q0, gmul(ss,q1)); q0 = q1; q1 = q2;
    if (!signe(z2)) break;
    z2 = ginv(z2);
  }
  while (degpol(p1) < vn);
  if (degpol(p1) > vn || signe(z2))
    err(talker,"not a complex multiplication in powell");
  x = gdiv(p1,q1); y = gdiv(deriv(x,0),n);
  x = gsub(poleval(x,grdx), gdivgs((GEN)e[6],12));
  y = gsub( gmul(d_ellLHS(e,z), poleval(y,grdx)), ellLHS0(e,x));
  z = cgetg(3,t_VEC);
  z[1] = lcopy(x);
  z[2] = lmul2n(y,-1); return gerepileupto(av, z);
}

static GEN
ell_sqr(void *e, GEN x) { return addell((GEN)e, x, x); }

GEN
powell(GEN e, GEN z, GEN n)
{
  pari_sp av = avma;
  long s;

  checksell(e); checkpt(z);
  if (typ(n)==t_QUAD) return CM_powell(e,z,n);
  if (typ(n) != t_INT) err(impl,"powell for non integral, non CM, exponents");
  s = signe(n);
  if (!s || lg(z) == 2) return _vec(gzero);
  if (s < 0) z = invell(e,z);
  if (is_pm1(n)) return s < 0? gerepilecopy(av, z): gcopy(z);
  z = leftright_pow(z, n, (void*)e, &ell_sqr, (GEN(*)(void*,GEN,GEN))&addell);
  return gerepileupto(av, z);
}

GEN
mathell(GEN e, GEN x, long prec)
{
  GEN y, h, *pdiag;
  long lx = lg(x),i,j,tx=typ(x);
  pari_sp av = avma;

  if (!is_vec_t(tx)) err(elliper1);
  y = cgetg(lx,t_MAT); pdiag = (GEN*) new_chunk(lx);
  for (i=1; i<lx; i++)
  {
    pdiag[i] = ghell(e,(GEN)x[i],prec);
    y[i] = lgetg(lx,t_COL);
  }
  for (i=1; i<lx; i++)
  {
    coeff(y,i,i) = lmul2n(pdiag[i],1);
    for (j=i+1; j<lx; j++)
    {
      h = ghell(e, addell(e,(GEN)x[i],(GEN)x[j]), prec);
      coeff(y,j,i) = coeff(y,i,j) = lsub(h, gadd(pdiag[i],pdiag[j]));
    }
  }
  return gerepilecopy(av,y);
}

static GEN
bilhells(GEN e, GEN z1, GEN z2, GEN h2, long prec)
{
  long lz1=lg(z1), tx, i;
  pari_sp av = avma;
  GEN y,p1,p2;

  if (lz1==1) return cgetg(1,typ(z1));

  tx = typ(z1[1]);
  if (!is_matvec_t(tx))
  {
    p1 = ghell(e, addell(e,z1,z2),prec);
    p2 = gadd(h2, ghell(e,z1,prec));
    return gerepileupto(av, gsub(p1,p2));
  }
  y = cgetg(lz1, typ(z1));
  for (i=1; i<lz1; i++) y[i] = (long)bilhells(e,(GEN)z1[i],z2,h2,prec);
  return y;
}

GEN
bilhell(GEN e, GEN z1, GEN z2, long prec)
{
  GEN p1, h2;
  long tz1 = typ(z1), tz2 = typ(z2);
  pari_sp av = avma;

  if (!is_matvec_t(tz1) || !is_matvec_t(tz2)) err(elliper1);
  if (lg(z1)==1) return cgetg(1,tz1);
  if (lg(z2)==1) return cgetg(1,tz2);

  tz1 = typ(z1[1]);
  tz2 = typ(z2[1]);
  if (is_matvec_t(tz2))
  {
    if (is_matvec_t(tz1)) err(talker,"two vector/matrix types in bilhell");
    p1 = z1; z1 = z2; z2 = p1;
  }
  h2 = ghell(e,z2,prec);
  return gerepileupto(av, bilhells(e,z1,z2,h2,prec));
}

/* compute a,b such that E1: y^2 = x(x-a)(x-b) ~ E0 */
static GEN
new_coords(GEN e, GEN x, GEN *pta, GEN *ptb, int flag, long prec)
{
  GEN a,b,r0,p1,p2,w, e1 = gmael(e,14,1), b2 = (GEN)e[6];
  long ty = typ(e[12]);

  r0 = gmul2n(b2,-2);
  p2 = gadd(gmulsg(3,e1),r0);
  if (ty == t_PADIC)
    w = (GEN)e[18];
  else
  {
    GEN b4 = (GEN)e[7];
    if (!is_const_t(ty)) err(typeer,"zell");

    /* w^2 = 2b4 + 2b2 e1 + 12 e1^2 = 4(e1-e2)(e1-e3) */
    w = gsqrt(gmul2n(gadd(b4, gmul(e1,gadd(b2,gmulsg(6,e1)))),1),prec);
    if (gsigne(real_i(p2)) > 0) w = gneg_i(w);
  }
  *pta = a = gmul2n(gsub(w,p2),-2);
  *ptb = b = gmul2n(w,-1);
  if (flag)
  {
    GEN r1 = gsub(a,b);
    p1 = gadd(x, gmul2n(gadd(e1,r0),-1));
    p1 = gmul2n(p1,-1);
    p1 = gadd(p1, gsqrt(gsub(gsqr(p1), gmul(a,r1)), prec));
    return gmul(p1, gsqr(gmul2n(gaddsg(1,gsqrt(gdiv(gadd(p1,r1),p1),prec)),-1)));
  }
  x = gsub(x, e1);
  p1 = gadd(x, b);
  return gmul2n(gadd(p1, gsqrt(gsub(gsqr(p1), gmul2n(gmul(a,x),2)),prec)), -1);
}

GEN
zell(GEN e, GEN z, long prec)
{
  long ty, sw, fl;
  pari_sp av = avma;
  GEN t,u,p1,p2,a,b,x1,u2,D = (GEN)e[12];

  checkbell(e);
  ty = typ(D);
  if (ty==t_INTMOD) err(typeer,"zell");
  if (lg(z)<3) return (ty==t_PADIC)? gun: gzero;

  x1 = new_coords(e,(GEN)z[1],&a,&b,1, prec);
  if (ty==t_PADIC)
  {
    u2 = do_padic_agm(&x1,a,b,(GEN)D[2]);
    if (!gcmp0((GEN)e[16]))
    {
      t = gsqrt(gaddsg(1,gdiv(x1,a)),prec);
      t = gdiv(gaddsg(-1,t), gaddsg(1,t));
    }
    else t = gaddsg(2, ginv(gmul(u2,x1)));
    return gerepileupto(av,t);
  }

  sw = gsigne(real_i(b)); fl=0;
  for(;;) /* ~ agm */
  {
    GEN a0=a, b0=b, x0=x1, r1;

    b = gsqrt(gmul(a0,b0),prec);
    if (gsigne(real_i(b)) != sw) b = gneg_i(b);
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
  p2 = gdiv(imag_i(t),gmael(e,16,2));
  p1 = gsub(p2, gmul2n(gun,-2));
  if (gcmp(gabs(p1,prec),ghalf) >= 0)
    t = gsub(t, gmul((GEN)e[16],gfloor(gadd(p2,dbltor(0.1)))));
  if (gsigne(real_i(t)) < 0) t = gadd(t,(GEN)e[15]);
  return gerepileupto(av,t);
}

typedef struct {
  GEN w1,w2,tau; /* original basis for L = <w1,w2> = w2 <1,tau> */
  GEN W1,W2,Tau; /* new basis for L = <W1,W2> = W2 <1,tau> */
  GEN a,b,c,d; /* tau in F = h/Sl2, tau = g.t, g=[a,b;c,d] in SL(2,Z) */
  GEN x,y; /* z/w2 defined mod <1,tau> --> z + x tau + y reduced mod <1,tau> */
  int swap; /* 1 if we swapped w1 and w2 */
} SL2_red;

/* compute gamma in SL_2(Z) gamma(t) is in the usual
   fundamental domain. Internal function no check, no garbage. */
static void
set_gamma(SL2_red *T)
{
  GEN t = T->tau, a, b, c, d, run;

  run = gsub(realun(DEFAULTPREC), gpowgs(stoi(10),-8));
  a = d = gun;
  b = c = gzero;
  for(;;)
  {
    GEN m, p1, n = ground(real_i(t));
    if (signe(n))
    { /* apply T^n */
      n = negi(n); t = gadd(t,n);
      a = addii(a, mulii(n,c));
      b = addii(b, mulii(n,d));
    }
    m = gnorm(t); if (gcmp(m,run) > 0) break;
    t = gneg_i(gdiv(gconj(t), m)); /* apply S */
    p1 = negi(c); c = a; a = p1;
    p1 = negi(d); d = b; b = p1;
  }
  T->a = a; T->b = b;
  T->c = c; T->d = d;
}

#define swap(x,y) { GEN _t=x; x=y; y=_t; }

/* swap w1, w2 so that Im(t := w1/w2) > 0. Set tau = representative of t in
 * the standard fundamental domain, and g in Sl_2, such that tau = g.t */
static void
red_modSL2(SL2_red *T)
{
  long s;
  T->tau = gdiv(T->w1,T->w2);
  s = gsigne(imag_i(T->tau));
  if (!s) err(talker,"w1 and w2 R-linearly dependent in elliptic function");
  T->swap = (s < 0);
  if (T->swap) { swap(T->w1, T->w2); T->tau = ginv(T->tau); }
  set_gamma(T);
  /* update lattice */
  T->W1 = gadd(gmul(T->a,T->w1), gmul(T->b,T->w2));
  T->W2 = gadd(gmul(T->c,T->w1), gmul(T->d,T->w2));
  T->Tau = gdiv(T->W1, T->W2);
}

static int
get_periods(GEN e, SL2_red *T)
{
  long tx = typ(e);
  if (is_vec_t(tx))
    switch(lg(e))
    {
      case  3: T->w1 = (GEN)e[1];  T->w2 = (GEN)e[2]; red_modSL2(T); return 1;
      case 20: T->w1 = (GEN)e[15]; T->w2 = (GEN)e[16];red_modSL2(T); return 1;
    }
  return 0;
}

static GEN
check_real(GEN q)
{
  return (typ(q) == t_COMPLEX && gcmp0((GEN)q[2]))? (GEN)q[1]: q;
}

/* Return E_k(tau). Slow if tau is not in standard fundamental domain */
static GEN 
trueE(GEN tau, long k, long prec)
{
  pari_sp lim, av;
  GEN p1, q, y, qn, n, pii2 = PiI2(prec);

  q = gexp(gmul(pii2, tau), prec);
  q = check_real(q);
  y = gzero; n = utoi(1);
  av = avma; lim = stack_lim(av,2); qn = gun; n[2] = 0;
  for(;;)
  { /* compute y := sum_{n>0} n^(k-1) q^n / (1-q^n) */
    n[2]++; qn = gmul(q,qn);
    p1 = gdiv(gmul(gpowgs(n,k-1),qn), gsub(gun,qn));
    if (gcmp0(p1) || gexpo(p1) <= - bit_accuracy(prec) - 5) break;
    y = gadd(y, p1);
    if (low_stack(lim, stack_lim(av,2)))
    {
      if(DEBUGMEM>1) err(warnmem,"elleisnum");
      gerepileall(av, 2, &y,&qn);
    }
  }
  return gadd(gun, gmul(y, gdiv(gdeux, szeta(1-k, prec))));
}

/* (2iPi/W2)^k E_k(W1/W2) */
static GEN
_elleisnum(SL2_red *T, long k, long prec)
{
  GEN y = trueE(T->Tau, k, prec);
  y = gmul(y, gpowgs(gdiv(PiI2(prec), T->W2),k));
  return check_real(y);
}

/* Return (2iPi)^k E_k(L) = (2iPi/w2)^k E_k(tau), with L = <w1,w2>, k > 0 even
 * E_k(tau) = 1 + 2/zeta(1-k) * sum(n>=1, n^(k-1) q^n/(1-q^n))
 * If flag is != 0 and k=4 or 6, compute g2 = E4/12 or g3 = -E6/216 resp. */
GEN
elleisnum(GEN om, long k, long flag, long prec)
{
  pari_sp av = avma;
  GEN p1, y;
  SL2_red T;

  if (k&1 || k<=0) err(talker,"k not a positive even integer in elleisnum");
  if (!get_periods(om, &T)) err(typeer,"elleisnum");
  y = _elleisnum(&T, k, prec);
  if (k==2 && signe(T.c))
  {
    p1 = gmul(PiI2(prec), mulsi(12, T.c));
    y = gsub(y, gdiv(p1, gmul(T.w2, T.W2)));
  }
  else if (k==4 && flag) y = gdivgs(y,  12);
  else if (k==6 && flag) y = gdivgs(y,-216);
  return gerepileupto(av,y);
}

/* return quasi-periods associated to [w1,w2] */
static GEN
_elleta(SL2_red *T, long prec)
{
  GEN y, y1, y2, e2 = gdivgs(_elleisnum(T,2,prec), 12); 
  y2 = gmul(T->W2, e2);
  y1 = gadd(gdiv(PiI2(prec), T->W2), gmul(T->W1,e2));
  y = cgetg(3,t_VEC);
  y[1] = lneg(y1);
  y[2] = lneg(y2); return y;
}

/* compute eta1, eta2 */
GEN
elleta(GEN om, long prec)
{
  pari_sp av = avma;
  GEN y, y1, y2, E2, pi = mppi(prec);
  SL2_red T;
  if (!get_periods(om, &T)) err(typeer,"elleta");
  E2 = trueE(T.Tau, 2, prec); /* E_2(Tau) */
  if (signe(T.c))
  {
    GEN u = gdiv(T.w2, T.W2);
    /* E2 := u^2 E2 + 6iuc/pi = E_2(tau) */
    E2 = gadd(gmul(gsqr(u), E2), gmul(gi, gdiv(gmul(mulsi(6,T.c), u), pi)));
  }
  y2 = gdiv(gmul(E2, gsqr(pi)), gmulsg(3, T.w2));
  if (T.swap)
  {
    y1 = y2; 
    y2 = gadd(gmul(T.tau,y1), gdiv(PiI2(prec), T.w2));
  }
  else
    y1 = gsub(gmul(T.tau,y2), gdiv(PiI2(prec), T.w2));
  y = cgetg(3, t_VEC);
  y[1] = (long)y1;
  y[2] = (long)y2; return gerepilecopy(av, y);
}

static GEN
reduce_z(GEN z, SL2_red *T)
{
  GEN Z = gdiv(z, T->W2);
  long t = typ(z), pr;

  if (!is_scalar_t(t) || t == t_INTMOD || t == t_PADIC || t == t_POLMOD)
    err(typeer,"reduction mod SL2 (reduce_z)");
  T->x = ground(gdiv(imag_i(Z), imag_i(T->Tau)));
  Z = gsub(Z, gmul(T->x,T->Tau));
  T->y = ground(real_i(Z));
  Z = gsub(Z, T->y);
  pr = gprecision(Z);
  if (gcmp0(Z) || (pr && gexpo(Z) < 5 - bit_accuracy(pr))) Z = NULL; /*z in L*/
  return Z;
}

/* computes the numerical value of wp(z | L), L = om1 Z + om2 Z
 * return NULL if z in L.  If flall=1, compute also wp' */
static GEN
weipellnumall(SL2_red *T, GEN z, long flall, long prec)
{
  long toadd;
  pari_sp av=avma, lim, av1;
  GEN p1,pii2,q,u,y,yp,u1,u2,qn,v;

  z = reduce_z(z, T);
  if (!z) return NULL;

  /* Now L,z normalized to <1,tau>. z in fund. domain of <1, tau> */
  pii2 = PiI2(prec);
  q = gexp(gmul(pii2,T->Tau),prec);
  u = gexp(gmul(pii2,z),prec);
  u1= gsub(gun,u); u2=gsqr(u1);
  y = gadd(ginv(utoi(12)), gdiv(u,u2));
  if (flall) yp = gdiv(gadd(gun,u), gmul(u1,u2));
  toadd = (long)ceil(9.065*gtodouble(imag_i(z)));

  av1 = avma; lim = stack_lim(av1,1); qn = q;
  for(;;)
  {
    GEN qnu,qnu1,qnu2,qnu3,qnu4;

    qnu = gmul(qn,u);     /* q^n u */
    qnu1 = gsub(gun,qnu); /* 1 - q^n u */
    qnu2 = gsqr(qnu1);    /* (1 - q^n u)^2 */
    qnu3 = gsub(qn,u);    /* q^n - u */
    qnu4 = gsqr(qnu3);    /* (q^n - u)^2 */
    p1 = gsub(gmul(u, gadd(ginv(qnu2),ginv(qnu4))),
              gmul2n(ginv(gsqr(gsub(gun,qn))), 1));
    y = gadd(y, gmul(qn,p1));
    if (flall)
    {
      p1 = gadd(gdiv(gadd(gun,qnu),gmul(qnu1,qnu2)),
                gdiv(gadd(qn,u),gmul(qnu3,qnu4)));
      
      yp = gadd(yp, gmul(qn,p1));
    }
    qn = gmul(q,qn);
    if (gexpo(qn) <= - bit_accuracy(prec) - 5 - toadd) break;
    if (low_stack(lim, stack_lim(av1,1)))
    {
      GEN *gptr[3]; gptr[0]=&y; gptr[1]=&qn; gptr[2]=&yp;
      if(DEBUGMEM>1) err(warnmem,"weipellnum");
      gerepilemany(av1,gptr,flall?3:2);
    }
  }

  u1 = gdiv(pii2, T->W2);
  u2 = gsqr(u1);
  y = gmul(u2,y); /* y *= (2i pi / w2)^2 */
  if (flall)
  {
    yp = gmul(u, gmul(gmul(u1,u2),yp));/* yp *= u (2i pi / w2)^3 */
    v = cgetg(3,t_VEC);
    v[1] = (long)y;
    v[2] = lmul2n(yp,-1);
  }
  else v = y;
  return gerepilecopy(av, v);
}

GEN
ellzeta(GEN om, GEN z, long prec)
{
  long toadd;
  pari_sp av = avma, lim, av1;
  GEN Z, pii2, q, u, y, qn, et = NULL;
  SL2_red T;

  if (!get_periods(om, &T)) err(typeer,"ellzeta");
  Z = reduce_z(z, &T);
  if (!Z) err(talker,"can't evaluate ellzeta at a pole");
  if (!gcmp0(T.x) || !gcmp0(T.y))
  {
    et = _elleta(&T,prec);
    et = gadd(gmul(T.x,(GEN)et[1]), gmul(T.y,(GEN)et[2]));
  }

  pii2 = PiI2(prec);
  q = gexp(gmul(pii2,T.Tau),prec);
  u = gexp(gmul(pii2,Z),prec);
  
  y = gdiv(gmul(gsqr(T.W2),_elleisnum(&T,2,prec)), pii2);
  y = gadd(ghalf, gdivgs(gmul(Z,y),-12));
  y = gadd(y, ginv(gsub(u,gun)));
  toadd = (long)ceil(9.065*gtodouble(imag_i(Z)));
  av1 = avma; lim = stack_lim(av1,1);
  
  /* y += sum q^n ( u/(u*q^n - 1) + 1/(u - q^n) ) */
  for (qn = q;;)
  {
    GEN p1 = gadd(gdiv(u,gsub(gmul(qn,u),gun)), ginv(gsub(u,qn)));
    y = gadd(y, gmul(qn,p1));
    qn = gmul(q,qn);
    if (gexpo(qn) <= - bit_accuracy(prec) - 5 - toadd) break;
    if (low_stack(lim, stack_lim(av1,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"ellzeta");
      gerepileall(av1,2, &y,&qn);
    }
  }
  y = gmul(gdiv(pii2,T.W2), y);
  if (et) y = gadd(y, et);
  return gerepileupto(av, y);
}

/* if flag=0, return ellsigma, otherwise return log(ellsigma) */
GEN
ellsigma(GEN w, GEN z, long flag, long prec)
{
  long toadd;
  pari_sp av = avma, lim, av1;
  GEN Z,zinit,p1,pii2,q,u,y,y1,u1,qn,negu,uinv,et,etnew,uhalf;
  int doprod = (flag >= 2);
  int dolog = (flag & 1);
  SL2_red T;

  if (!get_periods(w, &T)) err(typeer,"ellsigma");
  Z = reduce_z(z, &T);
  if (!Z)
  {
    if (!dolog) return gzero;
    err(talker,"can't evaluate log(ellsigma) at lattice point");
  }
  et = _elleta(&T, prec);
  etnew = gadd(gmul(T.x,(GEN)et[1]), gmul(T.y,(GEN)et[2]));

  pii2 = PiI2(prec);
  zinit = gmul(Z,T.W2);
  p1 = gadd(zinit, gmul2n(gadd(gmul(T.x,T.W1),gmul(T.y,T.W2)),-1));
  etnew = gmul(etnew, p1);
  if (mpodd(T.x) || mpodd(T.y)) etnew = gadd(etnew, gmul2n(pii2,-1));

  y1 = gadd(etnew, gmul2n(gmul(gmul(Z,zinit),(GEN)et[2]),-1));

  /* 9.065 = 2*Pi/log(2) */
  toadd = (long)ceil(9.065*fabs(gtodouble(imag_i(Z))));
  uhalf = gexp(gmul(gmul2n(pii2,-1),Z),prec);
  u = gsqr(uhalf);
  if (doprod)
  { /* use product */
    q = gexp(gmul(pii2,T.Tau),prec);
    uinv = ginv(u);
    u1 = gsub(uhalf,ginv(uhalf));
    y = gdiv(gmul(T.W2,u1),pii2);
    av1 = avma; lim = stack_lim(av1,1); qn=q;
    negu = stoi(-1);
    for(;;)
    {
      p1 = gmul(gadd(gmul(qn,u),negu),gadd(gmul(qn,uinv),negu));
      p1 = gdiv(p1,gsqr(gadd(qn,negu)));
      y = gmul(y,p1);
      qn = gmul(q,qn);
      if (gexpo(qn) <= - bit_accuracy(prec) - 5 - toadd) break;
      if (low_stack(lim, stack_lim(av1,1)))
      {
        if(DEBUGMEM>1) err(warnmem,"ellsigma");
        gerepileall(av1,2, &y,&qn);
      }
    }
  }
  else
  { /* use sum */
    GEN q8, qn2, urn, urninv;
    long n;
    q8 = gexp(gmul2n(gmul(pii2,T.Tau),-3),prec);
    q = gpowgs(q8,8);
    u = gneg_i(u); uinv = ginv(u);
    y = gzero;
    av1 = avma; lim = stack_lim(av1,1);
    qn = q; qn2 = gun;
    urn = uhalf; urninv = ginv(uhalf);
    for(n=0;;n++)
    {
      y = gadd(y,gmul(qn2,gsub(urn,urninv)));
      qn2 = gmul(qn,qn2);
      qn = gmul(q,qn);
      urn = gmul(urn,u);
      urninv = gmul(urninv,uinv);
      if (gexpo(qn2) + n*toadd <= - bit_accuracy(prec) - 5) break;
      if (low_stack(lim, stack_lim(av1,1)))
      {
        if(DEBUGMEM>1) err(warnmem,"ellsigma");
        gerepileall(av1,5, &y,&qn,&qn2,&urn,&urninv);
      }
    }
    p1 = gmul(q8,gmul(gdiv(gdiv(T.W2,pii2),gpowgs(trueeta(T.Tau,prec),3)),y));
  }

  if (dolog)
    return gerepileupto(av, gadd(y1, glog(p1,prec)));
  else
    return gerepileupto(av, gmul(p1, gexp(y1,prec)));
}

GEN
pointell(GEN e, GEN z, long prec)
{
  pari_sp av = avma;
  GEN v;
  SL2_red T;

  checkbell(e); (void)get_periods(e, &T);
  v = weipellnumall(&T,z,1,prec);
  if (!v) { avma = av; return _vec(gzero); }
  v[1] = lsub((GEN)v[1], gdivgs((GEN)e[6],12));
  v[2] = lsub((GEN)v[2], gmul2n(ellLHS0(e,(GEN)v[1]),-1));
  return gerepilecopy(av, v);
}

static GEN
_weipell(GEN c4, GEN c6, long PREC)
{
  long i, k, l, precres = 2*PREC;
  pari_sp av1, tetpil;
  GEN P,p1,s,t, res = cgetg(precres+2,t_SER);

  res[1] = evalsigne(1) | evalvalp(-2) | evalvarn(0);
  if (!PREC) { setsigne(res,0); return res; }

  P = res + 2;
  for (i=1; i<precres; i+=2) P[i]=zero;
  switch(PREC)
  {
    default:P[6] = ldivgs(c6,6048);
    case 3: P[4] = ldivgs(c4, 240);
    case 2: P[2] = zero;
    case 1: P[0] = un;
    case 0: break;
  }
  for (k=4; k<PREC; k++)
  {
    av1 = avma;
    s = k&1? gzero: gsqr((GEN)P[k]);
    t = gzero;
    for (l=2; l+l<k; l++)
      t = gadd(t, gmul((GEN)P[l<<1],(GEN)P[(k-l)<<1]));
    p1 = gmulsg(3,gadd(s,gmul2n(t,1)));
    tetpil = avma;
    p1 = gdivgs(p1, (k-3)*(2*k+1));
    P[k<<1] = lpile(av1,tetpil, p1);
  }
  return res;
}

GEN
weipell(GEN e, long PREC)
{
  GEN c4 = (GEN)e[10];
  GEN c6 = (GEN)e[11];
  checkell(e); return _weipell(c4,c6,PREC);
}

GEN
weipell0(GEN e, long prec, long PREC)
{
  GEN c4,c6;

  if (lg(e) > 3)
  {
    checkell(e);
    c4 = (GEN)e[10];
    c6 = (GEN)e[11];
  }
  else
  {
    c4 = elleisnum(e, 4, 0, prec);
    c6 = elleisnum(e, 6, 0, prec); c6 = gneg(c6);
  }
  return _weipell(c4,c6,PREC);
}

/* assume x a t_POL */
int
is_simple_var(GEN x)
{
  return (degpol(x) == 1 && gcmp0((GEN)x[2]) && gcmp1((GEN)x[3]));
}

GEN
ellwp0(GEN w, GEN z, long flag, long prec, long PREC)
{
  GEN v;
  pari_sp av = avma;
  SL2_red T;

  if (!z) return weipell0(w,prec,PREC);
  if (typ(z)==t_POL)
  {
    if (!is_simple_var(z)) err(talker,"expecting a simple variable in ellwp");
    v = weipell0(w,prec,PREC); setvarn(v, varn(z));
    return v;
  }
  if (!get_periods(w, &T)) err(typeer,"ellwp");
  switch(flag)
  {
    case 0: v = weipellnumall(&T,z,0,prec);
      if (!v) { avma = av; v = gpowgs(z,-2); }
      return v;
    case 1: v = weipellnumall(&T,z,1,prec);
      if (!v)
      {
        GEN p1 = gmul2n(gpowgs(z,3),1);
        pari_sp tetpil = avma;
        v = cgetg(3,t_VEC);
	v[1] = lpuigs(z,-2);
	v[2] = lneg(p1); return gerepile(av,tetpil,v);
      }
      return v;
    case 2: return pointell(w,z,prec);
    default: err(flagerr,"ellwp"); return NULL;
  }
}

/* compute a_2 using Jacobi sum */
static GEN
_a_2(GEN e)
{
  pari_sp av = avma;
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
    ulong i;
    pari_sp av = avma;
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
        s += kross(e8 + muluumod(i, e72 + muluumod(i, e6 + (i<<2), p), p), p);
    avma = av; return stoi(-s);
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
  GEN z,p1,p2,x,x1,x2,y,y1,y2;
  pari_sp av;

  if (!z1) return z2;
  if (!z2) return z1;

  x1 = (GEN)z1[1]; y1 = (GEN)z1[2];
  x2 = (GEN)z2[1]; y2 = (GEN)z2[2];
  z = cgetg(3, t_VEC); av = avma;
  if (x1 == x2 || egalii(x1, x2))
  {
    if (!signe(y1) || !egalii(y1,y2)) return NULL;
    p2 = shifti(y1,1);
    p1 = addii(e, mulii(x1,mulsi(3,x1)));
    p1 = resii(p1, p);
  }
  else { p1 = subii(y2,y1); p2 = subii(x2, x1); }
  p1 = mulii(p1, mpinvmod(p2, p));
  p1 = resii(p1, p);
  x = subii(sqri(p1), addii(x1,x2));
  y = negi(addii(y1, mulii(p1,subii(x,x1))));
  x = modii(x,p);
  y = modii(y,p); avma = av;
  z[1] = licopy(x);
  z[2] = licopy(y); return z;
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
negsell(GEN f, GEN p)
{
  GEN g = cgetg(3, t_VEC);
  g[1] = f[1];
  g[2] = signe(f[2])? lsubii(p, (GEN)f[2]): f[2];
  return g;
}

typedef struct {
  GEN e, p;
} sellp;

static GEN
mul_sell(void *d, GEN x, GEN y)
{
  sellp *S = (sellp*)d;
  return addsell(S->e, x, y, S->p);
}
static GEN
sqr_sell(void *d, GEN x)
{
  sellp *S = (sellp*)d;
  return addsell(S->e, x, x, S->p);
}

static GEN
powsell(GEN e, GEN z, GEN n, GEN p)
{
  long s = signe(n);
  sellp S;

  if (!s || !z) return NULL;
  if (s < 0) z = negsell(z, p);
  if (is_pm1(n)) return z;
  S.e = e;
  S.p = p;
  return leftright_pow(z, n, &S, &sqr_sell, &mul_sell);
}

/* assume H.f = 0, return exact order of f */
static GEN
exact_order(GEN H, GEN f, GEN c4, GEN p)
{
  GEN P, e, h = H, fa = decomp(H);
  long i, j, l;

  P = (GEN)fa[1]; l = lg(P);
  e = (GEN)fa[2];
  for (i=1; i<l; i++)
    for (j=itos((GEN)e[i]); j; j--)
    {
      GEN n = diviiexact(h,(GEN)P[i]);
      if (powsell(c4,f,n,p)) break;
      h = n;
    }
  return h;
}

/* make sure *x has lgefint >= k */
static void
_fix(GEN x, long k)
{
  GEN y = (GEN)*x;
  if (lgefint(y) < k) { GEN p1 = cgeti(k); affii(y,p1); *x = (long)p1; }
}

/* Return the lift of a (mod b), which is closest to h */
static GEN
closest_lift(GEN a, GEN b, GEN h)
{
  return addii(a, mulii(b, diviiround(gsub(h,a), b)));
}

/* compute a_p using Shanks/Mestre + Montgomery's trick. Assume p > 457 */
GEN
apell1(GEN e, GEN p)
{
  long *tx, *ty, *ti, pfinal, i, j, s, KRO, KROold, nb;
  ulong x;
  pari_sp av = avma, av2;
  GEN p1, h, mfh, F, f, fh, fg, pordmin, u, v, p1p, p2p, A, B, c4, c6, cp4, pts;
  tx = NULL;
  ty = ti = NULL; /* gcc -Wall */

  if (DEBUGLEVEL) (void)timer2();
  c4 = gmod(gdivgs((GEN)e[10],  -48), p);
  c6 = gmod(gdivgs((GEN)e[11], -864), p);
  /* once #E(Fp) is know mod B >= pordmin, it is completely determined */
  pordmin = gceil(gmul2n(gsqrt(p,DEFAULTPREC),2)); /* ceil( 4sqrt(p) ) */
  p1p = addsi(1, p);
  p2p = shifti(p1p, 1);
  x = 0; u = c6; KRO = kronecker(u, p); KROold = - KRO;
  A = gzero; B = gun; h = p1p;
  for(;;)
  {
    while (!KRO || KRO == KROold)
    { /* look for points alternatively on E and its quadratic twist E' */
      x++; /* u = x^3 + c4 x + c6 */
      u = modii(addii(c6, mului(x, addii(c4, muluu(x,x)))), p);
      KRO = kronecker(u, p);
    }
    KROold = KRO;
    /* [ux, u^2] is on E_u: y^2 = x^3 + c4 u^2 x + c6 u^3
     * E_u isomorphic to E (resp. E') iff KRO = 1 (resp. -1)
     * #E(F_p) = p+1 - a_p, #E'(F_p) = p+1 + a_p
     *
     * #E_u(Fp) = A (mod B),  h is close to #E_u(Fp) */

    f = cgetg(3,t_VEC);
    f[1] = lmodii(mului(x,u), p);
    f[2] = lmodii(sqri(u),    p);
    cp4 = modii(mulii(c4, (GEN)f[2]), p); /* c4 for E_u */
    fh = powsell(cp4,f,h,p);
    if (!fh) goto FOUND;

    s = itos( gceil(gsqrt(gdiv(pordmin,B),DEFAULTPREC)) ) >> 1;
    /* look for h s.t f^h = 0 */
    if (!tx)
    { /* first time: initialize */
      tx = newbloc(s+1);
      ty = newbloc(s+1);
      ti = newbloc(s+1);
    }
    F = powsell(cp4,f,B,p);
    *tx = evaltyp(t_VECSMALL) | evallg(s+1);

    /* F = B.f */
    p1 = gcopy(fh);
    if (s < 3)
    { /* we're nearly done: naive search */
      GEN q1 = p1, mF = negsell(F, p); /* -F */
      for (i=1;; i++)
      {
        p1 = addsell(cp4,p1, F,p); /* h.f + i.F */
        if (!p1) { h = addii(h, mulsi( i,B)); goto FOUND; }
        q1 = addsell(cp4,q1,mF,p); /* h.f - i.F */
        if (!q1) { h = addii(h, mulsi(-i,B)); goto FOUND; }
      }
    }
    /* Baby Step/Giant Step */
    nb = min(128, s >> 1); /* > 0. Will do nb pts at a time: faster inverse */
    pts = cgetg(nb+1, t_VEC);
    j = lgefint(p);
    for (i=1; i<=nb; i++)
    { /* baby steps */
      pts[i] = (long)p1; /* h.f + (i-1).F */
      _fix(p1+1, j); tx[i] = modBIL((GEN)p1[1]);
      _fix(p1+2, j); ty[i] = modBIL((GEN)p1[2]);
      p1 = addsell(cp4,p1,F,p); /* h.f + i.F */
      if (!p1) { h = addii(h, mulsi(i,B)); goto FOUND; }
    }
    mfh = negsell(fh, p);
    fg = addsell(cp4,p1,mfh,p); /* h.f + nb.F - h.f = nb.F */
    if (!fg) { h = mulsi(nb,B); goto FOUND; }
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
          if (egalii((GEN)p1[2],(GEN)fg[2])) k -= 2*nb; /* fg == p1 */
          h = addii(h, mulsi(k,B)); goto FOUND;
        }
      }
      v = multi_invmod(u, p);
      maxj = (i-1 + nb <= s)? nb: s % nb;
      for (j=1; j<=maxj; j++,i++) /* adding nb.F (part 2) */
      {
        p1 = (GEN)pts[j];
        addsell_part2(cp4,p1,fg,p, (GEN)v[j]);
        tx[i] = modBIL((GEN)p1[1]);
        ty[i] = modBIL((GEN)p1[2]);
      }
      avma = av2;
    }
    p1 = addsell(cp4,(GEN)pts[j-1],mfh,p); /* = (s-1).F */
    if (!p1) { h = mulsi(s-1,B); goto FOUND; }
    if (DEBUGLEVEL) msgtimer("[apell1] baby steps, s = %ld",s);

    /* giant steps: fg = s.F */
    fg = addsell(cp4,p1,F,p);
    if (!fg) { h = mulsi(s,B); goto FOUND; }
    pfinal = modBIL(p); av2 = avma;

    p1 = gen_sort(tx, cmp_IND | cmp_C, NULL);
    for (i=1; i<=s; i++) ti[i] = tx[p1[i]];
    for (i=1; i<=s; i++) { tx[i] = ti[i]; ti[i] = ty[p1[i]]; }
    for (i=1; i<=s; i++) { ty[i] = ti[i]; ti[i] = p1[i]; }
    if (DEBUGLEVEL) msgtimer("[apell1] sorting");
    avma = av2;

    gaffect(fg, (GEN)pts[1]);
    for (j=2; j<=nb; j++) /* pts[j] = j.fg = (s*j).F */
    {
      p1 = addsell(cp4,(GEN)pts[j-1],fg,p);
      if (!p1) { h = mulii(mulss(s,j), B); goto FOUND; }
      gaffect(p1, (GEN)pts[j]);
    }
    /* replace fg by nb.fg since we do nb points at a time */
    avma = av2;
    fg = gcopy((GEN)pts[nb]);
    av2 = avma;

    for (i=1,j=1; ; i++)
    {
      GEN ftest = (GEN)pts[j];
      ulong m, l = 1, r = s+1;
      long k, k2, j2;

      avma = av2;
      k = modBIL((GEN)ftest[1]);
      while (l<r)
      {
        m = (l+r) >> 1;
        if (tx[m] < k) l = m+1; else r = m;
      }
      if (r <= (ulong)s && tx[r] == k)
      {
        while (tx[r] == k && r) r--;
        k2 = modBIL((GEN)ftest[2]);
        for (r++; tx[r] == k && r <= (ulong)s; r++)
          if (ty[r] == k2 || ty[r] == pfinal - k2)
          { /* [h+j2] f == +/- ftest (= [i.s] f)? */
            j2 = ti[r] - 1;
            if (DEBUGLEVEL) msgtimer("[apell1] giant steps, i = %ld",i);
            p1 = addsell(cp4, powsell(cp4,F,stoi(j2),p),fh,p);
            if (egalii((GEN)p1[1], (GEN)ftest[1]))
            {
              if (egalii((GEN)p1[2], (GEN)ftest[2])) i = -i;
              h = addii(h, mulii(addis(mulss(s,i), j2), B));
              goto FOUND;
            }
          }
      }
      if (++j > nb)
      { /* compute next nb points */
        long save = 0; /* gcc -Wall */;
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
FOUND: /* found a point of exponent h on E_u */
    h = exact_order(h, f, cp4, p);
    /* h | #E_u(Fp) = A (mod B) */
    if (B == gun) B = h;
    else
    {
      p1 = chinois(gmodulcp(A,B), gmodulsg(0,h));
      A = (GEN)p1[2];
      B = (GEN)p1[1];
    }

    i = (cmpii(B, pordmin) < 0);
    /* If we are not done, update A mod B for the _next_ curve, isomorphic to
     * the quadratic twist of this one */
    if (i) A = resii(subii(p2p,A), B); /* #E(Fp)+#E'(Fp) = 2p+2 */
    
    /* h = A mod B, closest lift to p+1 */
    h = closest_lift(A, B, p1p);
    if (!i) break;
  }
  if (tx)
  {
    gunclone(tx);
    gunclone(ty);
    gunclone(ti);
  }
  return gerepileuptoint(av, KRO==1? subii(p1p,h): subii(h,p1p));
}

typedef struct
{
  int isnull;
  long x,y;
} sellpt;

/* P <-- P + Q, safe with P = Q */
static void
s_addell(sellpt *P, sellpt *Q, long c4, long p)
{
  ulong num, den, lambda;

  if (P->isnull) { *P = *Q; return; }
  if (Q->isnull) return;
  if (P->x == Q->x)
  {
    if (! P->y || P->y != Q->y) { P->isnull = 1; return; }
    num = adduumod(c4, muluumod(3, muluumod(P->x, P->x, p), p), p);
    den = adduumod(P->y, P->y, p);
  }
  else
  {
    num = subuumod(P->y, Q->y, p);
    den = subuumod(P->x, Q->x, p);
  }
  lambda = divuumod(num, den, p);
  num = subuumod(muluumod(lambda, lambda, p), adduumod(P->x, Q->x, p), p);
  P->y = subuumod(muluumod(lambda, subuumod(Q->x, num, p), p), Q->y, p);
  P->x = num; /* necessary in case P = Q: we need Q->x above */
}

/* Q <-- P^n */
static void
s_powell(sellpt *Q, sellpt *P, long n, long c4, long p)
{
  sellpt R = *P;

  if (n < 0) { n = -n; if (R.y) R.y = p - R.y; }
  Q->isnull = 1;
  for(;;)
  {
    if (n&1) s_addell(Q, &R, c4, p);
    n >>= 1; if (!n) return;
    s_addell(&R, &R, c4, p);
  }
}

/* assume H.f = 0, return exact order of f, cf. exact_order */
static long
sexact_order(long H, sellpt *f, long c4, long p)
{
  GEN P, e, fa = decomp(stoi(H));
  long h = H, pp, i, j, l;
  sellpt fh;

  P = (GEN)fa[1]; l = lg(P);
  e = (GEN)fa[2];
  for (i=1; i<l; i++)
  {
    pp = itos((GEN)P[i]);
    for (j=itos((GEN)e[i]); j; j--)
    {
      long n = h / pp;
      s_powell(&fh, f, n, c4, p);
      if (!fh.isnull) break;
      h = n;
    }
  }
  return h;
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

/* assume e has good reduction at p. Should use Montgomery.
 * See apell1() */
static GEN
apell0(GEN e, ulong p)
{
  sellpt f, fh, fg, ftest, F;
  ulong u, c4, c6, cp4, p1p, p2p, h;
  long pordmin,A,B;
  long i, s, KRO, KROold, x, l, r, m;
  pari_sp av;
  multiple *table;

  if (p < 99) return apell2_intern(e,(ulong)p);
  table = NULL;

  av = avma;
  c4 = itou( gmodgs(gdivgs((GEN)e[10],  -48), (long)p) );
  c6 = itou( gmodgs(gdivgs((GEN)e[11], -864), (long)p) );
  pordmin = (long)(1 + 4*sqrt((float)p));
  p1p = p+1;
  p2p = p1p << 1;
  x = 0; u = c6; KRO = kross(u, p); KROold = -KRO;
  A = 0; B = 1; h = p1p;
  for(;;)
  {
    while (!KRO || KRO == KROold)
    {
      x++;
      u = adduumod(c6, muluumod(x, c4 + muluumod(x,x,p), p), p);
      KRO = kross(u,p);
    }
    KROold = KRO;
    f.isnull = 0;
    f.x = muluumod(x, u, p);
    f.y = muluumod(u, u, p);
    cp4 = muluumod(c4, f.y, p);
    s_powell(&fh, &f, h, cp4, p);
    s = (long) (sqrt(((float)pordmin)/B) / 2);
    if (!s) s = 1;
    if (!table)
    {
      table = (multiple *) gpmalloc((s+1) * sizeof(multiple));
      F = f;
    }
    else
      s_powell(&F, &f, B, cp4, p);
    for (i=0; i < s; i++)
    {
      if (fh.isnull) { h += B*i; goto FOUND; }
      table[i].x = fh.x;
      table[i].y = fh.y;
      table[i].i = i;
      s_addell(&fh, &F, cp4, p);
    }
    qsort(table,s,sizeof(multiple),(QSCOMP)compare_multiples);
    s_powell(&fg, &F, s, cp4, p); ftest = fg;
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
      s_addell(&ftest, &fg, cp4, p);
    }
    h += table[r].i * B;
    if (table[r].y == ftest.y) i = -i;
    h += s * i * B;

FOUND:
    h = sexact_order(h, &f, cp4, p);
    if (B == 1) B = h;
    else
    {
      GEN p1 = chinois(gmodulss(A,B), gmodulss(0,h));
      A = itos((GEN)p1[2]);
      if (is_bigint(p1[1])) { h = A; break; }
      B = itos((GEN)p1[1]);
    }

    i = (B < pordmin);
    if (i)
    {
      A = (p2p - A) % B;
      if ((A << 1) > B) A -= B;
    }
    /* h = A mod B, closest lift to p+1 */
    h = A + B * (((ulong)(p2p + B - (A << 1))) / (B << 1));
    avma = av; if (!i) break;
  }
  if (table) free(table);
  return stoi(KRO==1? p1p-h: h-p1p);
}

GEN
apell(GEN e, GEN p)
{
  checkell(e);
  if (typ(p)!=t_INT || signe(p)<0) err(talker,"not a prime in apell");
  if (gdivise((GEN)e[12],p)) /* D may be an intmod */
  {
    long s;
    pari_sp av = avma;
    GEN p0 = egalii(p,gdeux)? stoi(8): p;
    GEN c6 = gmul((GEN)e[11],gmodulsg(1,p0));
    s = kronecker(lift_intern(c6),p); avma=av;
    if (mod4(p) == 3) s = -s;
    return stoi(s);
  }
  if (cmpis(p, 0x3fffffff) > 0) return apell1(e, p);
  return apell0(e, itou(p));
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
  long tab[4]={0,1,1,-1}; /* p prime; (-1/p) = tab[p&3]. tab[0] not used */
  long p, i, m;
  GEN p1, p2, *an;

  checkell(e);
  for (i=1; i<=5; i++)
    if (typ(e[i]) != t_INT) err(typeer,"anell");
  if (n <= 0) return cgetg(1,t_VEC);
  if ((ulong)n>TEMPMAX) err(impl,"anell for n > %lu", TEMPMAX);

  an = (GEN*)cgetg(n+1,t_VEC); an[1] = gun;
  for (i=2; i <= n; i++) an[i] = NULL;
  for (p=2; p<=n; p++)
  {
    if (an[p]) continue; /* p not prime */

    if (!smodis((GEN)e[12],p)) /* bad reduction, p | D */
      switch (tab[p&3] * krogs((GEN)e[11],p)) /* (-c6/p) */
      {
        case -1:  /* non deployee */
          for (m=p; m<=n; m+=p)
            if (an[m/p]) an[m] = negi(an[m/p]);
          continue;
        case 0:   /* additive */
          for (m=p; m<=n; m+=p) an[m] = gzero;
          continue;
        case 1:   /* deployee */
          for (m=p; m<=n; m+=p)
            if (an[m/p]) an[m] = icopy(an[m/p]);
          continue;
      }
    else /* good reduction */
    {
      GEN ap = apell0(e, (ulong)p);

      if (p < TEMPC)
      {
        ulong pk, oldpk = 1;
        for (pk=p; pk <= (ulong)n; oldpk=pk, pk *= p)
        {
          if (pk == (ulong)p) an[pk] = ap;
          else
          {
            pari_sp av = avma;
            p1 = mulii(ap, an[oldpk]);
            p2 = mulsi(p, an[oldpk/p]);
            an[pk] = gerepileuptoint(av, subii(p1,p2));
          }
          for (m = n/pk; m > 1; m--)
            if (an[m] && m%p) an[m*pk] = mulii(an[m], an[pk]);
        }
      }
      else
      {
        an[p] = ap;
        for (m = n/p; m > 1; m--)
          if (an[m] && m%p) an[m*p] = mulii(an[m], an[p]);
      }
    }
  }
  return (GEN)an;
}

GEN
akell(GEN e, GEN n)
{
  long i, j, ex;
  pari_sp av = avma;
  GEN fa, P, E, ap, u, v, w, y, p;

  checkell(e);
  if (typ(n) != t_INT) err(talker,"not an integer type in akell");
  if (signe(n)<= 0) return gzero;
  y = gun; if (gcmp1(n)) return y;
  fa = auxdecomp(n,1);
  P = (GEN)fa[1];
  E = (GEN)fa[2];
  for (i=1; i<lg(P); i++)
  {
    p = (GEN)P[i];
    ex = itos((GEN)E[i]);
    /* FIXME: should factor (n,D) first, then restrict to primes of good red. */
    if (divise((GEN)e[12], p)) /* bad reduction */
    {
      j = kronecker((GEN)e[11],p); /* (c6/p) */
      if (!j) { avma = av; return gzero; }
      if (odd(ex))
      {
        if (mod4(p) == 3) j = -j;
        if (j < 0) y = negi(y);
      }
    }
    else /* good reduction */
    {
      ap = apell(e,p);
      u = ap; v = gun;
      for (j=2; j<=ex; j++)
      {
	w = subii(mulii(ap,u), mulii(p,v));
	v = u; u = w;
      }
      y = mulii(u,y);
    }
  }
  return gerepileuptoint(av,y);
}

/* h' := h_oo(a) + 1/2 log(denom(a)) */
GEN
hell(GEN e, GEN a, long prec)
{
  long n;
  pari_sp av = avma;
  GEN p1, p2, y, z, q, pi2surw, qn, ps;

  checkbell(e);
  pi2surw = gdiv(Pi2n(1, prec), (GEN)e[15]);
  z = gmul(real_i(zell(e,a,prec)), pi2surw);
  q = real_i( gexp(gmul((GEN)e[16], pureimag(pi2surw)),prec) );
  y = gsin(z,prec); qn = gun; ps = gneg_i(q);
  for (n = 3; ; n += 2)
  {
    qn = gmul(qn, ps);
    ps = gmul(ps, q);
    y = gadd(y, gmul(qn, gsin(gmulsg(n,z),prec)));
    if (gexpo(qn) < - bit_accuracy(prec)) break;
  }
  p1 = gmul(gsqr(gdiv(gmul2n(y,1), d_ellLHS(e,a))), pi2surw);
  p2 = gsqr(gsqr(gdiv(p1, gsqr(gsqr(denom((GEN)a[1]))))));
  p1 = gdiv(gmul(p2,q), (GEN)e[12]);
  p1 = gmul2n(glog(gabs(p1,prec),prec), -5);
  return gerepileupto(av, gneg(p1));
}

/* h' := h_oo(x) + 1/2 log(denom(x)) */
static GEN
hells(GEN e, GEN x, long prec)
{
  GEN b8 = (GEN)e[9], b6 = (GEN)e[8], b4 = (GEN)e[7], b2 = (GEN)e[6];
  GEN w, z, t, mu, b42, b62;
  long n, lim;

  t = gdiv(realun(prec), (GEN)x[1]);
  mu = gmul2n(glog(numer((GEN)x[1]),prec),-1);
  b42 = gmul2n(b4,1);
  b62 = gmul2n(b6,1);
  lim = 15 + bit_accuracy(prec);
  for (n = 3; n < lim; n += 2)
  {
    w = gmul(t, gaddsg(4, gmul(t, gadd(b2, gmul(t, gadd(b42, gmul(t, b6)))))));
    z = gsub(gun, gmul(gsqr(t), gadd(b4, gmul(t, gadd(b62, gmul(t,b8))))));
    mu = gadd(mu, gmul2n(glog(z,prec), -n));
    t = gdiv(w, z);
  }
  return mu;
}

/* [1,0,0,0] */
static GEN
init_ch() {
  GEN v = cgetg(5,t_VEC);
  v[1] = un; v[2] = v[3] = v[4] = zero; return v;
}

GEN
hell2(GEN e, GEN x, long prec)
{
  GEN e3, ro, v, D;
  pari_sp av = avma;

  if (lg(x) < 3) return gzero;
  D = (GEN)e[12];
  ro= (GEN)e[14];
  e3 = (gsigne(D) < 0)? (GEN)ro[1]: (GEN)ro[3];
  v = init_ch(); v[2] = laddgs(gfloor(e3),-1);
  return gerepileupto(av, hells(coordch(e,v), pointch(x,v), prec));
}

/* exp( h_oo(z) ) */
static GEN
exphellagm(GEN e, GEN z, long prec)
{
  GEN x_a, a, b, r;
  GEN V = cgetg(1, t_VEC), x = (GEN)z[1];
  long n, ex = 5-bit_accuracy(prec);
  GEN e1 = gmael(e,14,1);

  if (gcmp(x, e1) < 0) /* z not on neutral component */
  {
    GEN exph = exphellagm(e, addell(e, z,z), prec);
    /* h_oo(2P) = 4h_oo(P) - log |2y + a1x + a3| */
    return mpsqrt(mpsqrt( gmul(exph, gabs(d_ellLHS(e, z), prec)) ));
  }
  
  x = new_coords(e, x, &a,&b, 0, prec);
  x_a = gsub(x, a);
  if (gsigne(a) > 0)
  {
    GEN a0 = a;
    x = gsub(x, b);
    a = gneg(b);
    b = gsub(a0, b);
  }
  a = gsqrt(gneg(a), prec);
  b = gsqrt(gneg(b), prec);

  /* compute height on isogenous curve E1 ~ E0 */
  for(n=0; ; n++)
  {
    GEN p1, p2, ab, a0 = a;
    a = gmul2n(gadd(a0,b), -1);
    r = gsub(a, a0);
    if (gcmp0(r) || gexpo(r) < ex) break;
    ab = gmul(a0, b);
    b = gsqrt(ab, prec);

    p1 = gmul2n(gsub(x, ab), -1);
    p2 = gsqr(a);
    x = gadd(p1, gsqrt(gadd(gsqr(p1), gmul(x, p2)), prec));
    V = concatsp(V, gadd(x, p2));
  }
  x = (GEN)V[n];
  while (--n > 0) x = gdiv(gsqr(x), (GEN)V[n]);
  /* height on E1 is log(x)/2. Go back to E0 */
  return gdiv(x, mpsqrt( mpabs(x_a) ));
}

/* Assume e integral, given by a minimal model */
static GEN
ghell0(GEN e, GEN a, long flag, long prec)
{
  long lx, i, tx = typ(a);
  pari_sp av = avma;
  GEN Lp, x, y, z, phi2, psi2, psi3;

  checkbell(e); if (!is_matvec_t(tx)) err(elliper1);
  lx = lg(a); if (lx==1) return cgetg(1,tx);
  tx = typ(a[1]);
  if (is_matvec_t(tx))
  {
    z = cgetg(lx,tx);
    for (i=1; i<lx; i++) z[i] = (long)ghell0(e,(GEN)a[i],flag,prec);
    return z;
  }
  if (lg(a) < 3) return gzero;
  if (!oncurve(e,a)) err(talker, "point not on elliptic curve");

  psi2 = numer(d_ellLHS(e,a));
  if (!signe(psi2)) { avma = av; return gzero; }
  switch(flag)
  {
    case 0:  z = hell2(e,a,prec); break; /* Tate 4^n */
    case 1:  z = hell(e,a,prec);  break; /* Silverman's log(sigma) */
    default: z = exphellagm(e,a,prec);
    {
      GEN d = denom((GEN)a[1]);
      if (!z) return gzero;
      if (!is_pm1(d)) z = gmul(z, gsqrt(d, prec));
      z = mplog(z); break; /* Mestre's AGM */
    }
  }
  x = (GEN)a[1];
  y = (GEN)a[2];
  psi3 = numer( /* b8 + 3x b6 + 3x^2 b4 + x^3 b2 + 3 x^4 */
     gadd((GEN)e[9], gmul(x,
     gadd(gmulsg(3,(GEN)e[8]), gmul(x,
     gadd(gmulsg(3,(GEN)e[7]), gmul(x, gadd((GEN)e[6], gmulsg(3,x)))))))) );
  if (!signe(psi3)) { avma=av; return gzero; }

  phi2 = numer( /* a4 + 2a2 x + 3x^2 - y a1*/
    gsub(gadd((GEN)e[4],gmul(x,gadd(shifti((GEN)e[2],1),gmulsg(3,x)))),
         gmul((GEN)e[1],y)) );
  Lp = (GEN)factor(mppgcd(psi2,phi2))[1];
  lx = lg(Lp);
  for (i=1; i<lx; i++)
  {
    GEN p = (GEN)Lp[i];
    long u, v, n, n2;
    if (signe(resii((GEN)e[10],p)))
    { /* p \nmid c4 */
      long N = ggval((GEN)e[12],p);
      if (!N) continue;
      n2 = ggval(psi2,p); n = n2<<1;
      if (n > N) n = N;
      u = n * ((N<<1) - n);
      v = N << 3;
    }
    else
    {
      n2 = ggval(psi2, p);
      n  = ggval(psi3, p);
      if (n >= 3*n2) { u = n2; v = 3; } else { u = n; v = 8; }
    }
    /* z -= u log(p) / v */
    z = gadd(z, divrs(mulsr(-u, glog(p,prec)), v));
  }
  return gerepileupto(av,z);
}

GEN
ellheight0(GEN e, GEN a, long flag, long prec)
{
  switch(flag)
  {
    case 0: return ghell0(e,a,0,prec);
    case 1: return ghell0(e,a,1,prec);
    case 2: return ghell0(e,a,2,prec);
  }
  err(flagerr,"ellheight");
  return NULL; /* not reached */
}

GEN
ghell2(GEN e, GEN a, long prec) { return ghell0(e,a,0,prec); }

GEN
ghell(GEN e, GEN a, long prec) { return ghell0(e,a,2,prec); }

static long ellrootno_all(GEN e, GEN p, GEN* ptcond);

GEN
lseriesell(GEN e, GEN s, GEN A, long prec)
{
  pari_sp av = avma, av1, lim;
  long l, n, eps, flun;
  GEN z, cg, v, cga, cgb, s2, ns, gs, N;

  if (!A) A = gun;
  else
  {
    if (gsigne(A)<=0)
      err(talker,"cut-off point must be positive in lseriesell");
    if (gcmpgs(A,1) < 0) A = ginv(A);
  }
  if (typ(s) == t_INT)
  {
    if (signe(s) <= 0) { avma = av; return gzero; }
    gs = mpfactr(itos(s)-1, prec);
  }
  else
    gs = ggamma(s,prec);
  flun = gcmp1(A) && gcmp1(s);
  eps = ellrootno_all(e,gun,&N);
  if (flun && eps < 0) return realzero(prec);

  cg = divrr(Pi2n(1, prec), gsqrt(N,prec));
  cga = gmul(cg, A);
  cgb = gdiv(cg, A);
  l = (long)((pariC2*(prec-2) + fabs(gtodouble(s)-1.) * log(rtodbl(cga)))
            / rtodbl(cgb)+1);
  v = anell(e, min((ulong)l,TEMPMAX));
  s2 = ns = NULL; /* gcc -Wall */
  if (!flun) { s2 = gsubsg(2,s); ns = gpow(cg, gsubgs(gmul2n(s,1),2),prec); }
  z = gzero;
  av1 = avma; lim = stack_lim(av1,1);
  for (n = 1; n <= l; n++)
  {
    GEN p1, p2;
    p1 = gdiv(incgam0(s,mulsr(n,cga),gs,prec), gpow(stoi(n),s,prec));
    p2 = flun? p1: gdiv(gmul(ns, incgam(s2,mulsr(n,cgb),prec)),
                        gpow(stoi(n), s2,prec));
    if (eps < 0) p2 = gneg_i(p2);
    z = gadd(z, gmul(gadd(p1,p2),
                     ((ulong)n<=TEMPMAX)? (GEN)v[n]: akell(e,stoi(n))));
    if (low_stack(lim, stack_lim(av1,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"lseriesell");
      z = gerepilecopy(av1,z);
    }
  }
  return gerepileupto(av, gdiv(z,gs));
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
static void cumulev(GEN *vtotal, GEN u, GEN r, GEN s, GEN t);

static GEN
localred_result(long f, long kod, long c, GEN v)
{
  GEN z = cgetg(5, t_VEC);
  z[1] = lstoi(f);
  z[2] = lstoi(kod);
  z[3] = lcopy(v);
  z[4] = lstoi(c); return z;
}

/* Here p > 3. e assumed integral */
static GEN
localred_carac_p(GEN e, GEN p, int minim)
{
  long k, f, kod, c, nuj, nudelta;
  GEN p2, v = init_ch();
  GEN c4, c6, delta, tri;

  c4    = (GEN)e[10];
  c6    = (GEN)e[11];
  delta = (GEN)e[12];
  nuj   = gcmp0((GEN)e[13])? 0: - ggval((GEN)e[13], p);
  nudelta = ggval(delta, p);
  k = (nuj > 0 ? nudelta - nuj : nudelta) / 12;
  if (k <= 0)
  {
    if (minim) return v;
  }
  else
  { /* model not minimal */
    GEN pk = gpowgs(p,k), p2k = sqri(pk), p4k = sqri(p2k), p6k = mulii(p4k,p2k);
    GEN r, s, t;

    s = negi((GEN)e[1]);
    if (mpodd(s)) s = addii(s, pk);
    s = shifti(s, -1);

    r = subii((GEN)e[2], mulii(s, addii((GEN)e[1], s))); /* a_2' */
    switch(smodis(r, 3))
    {
      default: break; /* 0 */
      case 2: r = addii(r, p2k); break;
      case 1: r = subii(r, p2k); break;
    }
    r = negi( divis(r, 3) );

    t = negi(ellLHS0_i(e,r)); /* - a_3' */
    if (mpodd(t)) t = addii(t, mulii(pk, p2k));
    t = shifti(t, -1);

    v[1] = (long)pk;
    v[2] = (long)r;
    v[3] = (long)s;
    v[4] = (long)t;
    if (minim) return v;

    nudelta -= 12 * k;
    c4 = diviiexact(c4, p4k);
    c6 = diviiexact(c6, p6k);
    delta = diviiexact(delta, sqri(p6k));
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
	c = 3 + kronecker(divii(mulii(c6, delta),gpowgs(p, 9+nuj)), p);
      else
	c = 3 + kronecker(divii(delta, gpowgs(p, 6+nuj)), p);
      break;
    default: err(bugparier,"localred (nu_delta - nu_j != 0,6)");
      return NULL; /* not reached */
  }
  else switch(nudelta)
  {
    case  0: f = 0; kod = 1; c = 1; break; /* I0, regular */
    case  2: f = 2; kod = 2; c = 1; break; /* II   */
    case  3: f = 2; kod = 3; c = 2; break; /* III  */
    case  4: f = 2; kod = 4; /* IV   */
      c = 2 + kronecker(divii(mulis(c6, -6), sqri(p)), p);
      break;
    case  6: f = 2; kod = -1; /* I0*  */
      p2 = sqri(p);
      /* x^3 - 3c4/p^2 x - 2c6/p^3 */
      tri = coefs_to_pol(4, gun, gzero,
                            negi(divii(gmulsg(3, c4), p2)),
                            negi(divii(gmul2n(c6,1),  mulii(p2,p))));
      c = 1 + FpX_nbroots(tri, p);
      break;
    case  8: f = 2; kod = -4; /* IV*  */
      c = 2 + kronecker(gdiv(mulis(c6,-6), gpowgs(p,4)), p);
      break;
    case  9: f = 2; kod = -3; c = 2; break; /* III* */
    case 10: f = 2; kod = -2; c = 1; break; /* II*  */
    default: err(bugparier,"localred");
      return NULL; /* not reached */
  }
  return localred_result(f, kod, c, v);
}

/* return a_{ k,l } in Tate's notation */
static int
aux(GEN ak, int p, int l)
{
  pari_sp av = avma;
  long res = smodis(divis(ak, u_pow(p, l)), p);
  avma = av; return res;
}

static int
aux2(GEN ak, int p, GEN pl)
{
  pari_sp av = avma;
  long res = smodis(divii(ak, pl), p);
  avma = av; return res;
}

/* number of distinct roots of X^3 + aX^2 + bX + c modulo p
 * if there's a multiple root, put it un *mult */
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

/* same for aX^2 +bX + c */
static int
numroots2(int a, int b, int c, int p, int *mult)
{
  if (p == 2) { *mult = c; return b & 1 ? 2 : 1; }
  else { *mult = a * b; return (b * b - a * c) % 3 ? 2 : 1; }
}

/* p = 2 or 3 */
static GEN
localred_carac_23(GEN e, long p)
{
  long c, nu, nudelta;
  int a21, a42, a63, a32, a64, theroot, al, be, ga, p2, p3, p4;
  GEN pk, p2k, pk1;
  GEN r, s, t, v;

  nudelta = ggval((GEN)e[12], stoi(p));
  v = init_ch();

  for (;;)
  {
    if (!nudelta)
      return localred_result(0, 1, 1, v);
        /* I0   */
    if (smodis((GEN)e[6], p)) /* p \nmid b2 */
    {
      if (smodis(negi((GEN)e[11]), p == 2 ? 8 : 3) == 1)
        c = nudelta;
      else
        c = 2 - (nudelta & 1);
      return localred_result(1, 4 + nudelta, c, v);
    }
        /* Inu  */
    if (p == 2)
    {
      r = modis((GEN)e[4], 2);
      s = modis(addii(r, (GEN)e[2]), 2);
      if (signe(r))
        t = modis(addii(addii((GEN)e[4], (GEN)e[5]), s), 2);
      else
        t = modis((GEN)e[5], 2);
    }
    else /* p == 3 */
    {
      r = negi(modis((GEN)e[8], 3));
      s = modis((GEN)e[1], 3);
      t = modis(ellLHS0_i(e,r), 3);
    }
    cumule(&v, &e, gun, r, s, t); /* p | (a1, a2, a3, a4, a6) */
    p2 = p * p;
    if (smodis((GEN)e[5], p2))
      return localred_result(nudelta, 2, 1, v);
        /* II   */
    p3 = p2 * p;
    if (smodis((GEN)e[9], p3))
      return localred_result(nudelta - 1, 3, 2, v);
        /* III  */
    if (smodis((GEN)e[8], p3))
    {
      if (smodis((GEN)e[8], (p==2)? 32: 27) == p2)
        c = 3;
      else
        c = 1;
      return localred_result(nudelta - 2, 4, c, v);
    }
        /* IV   */

    if (smodis((GEN)e[5], p3))
      cumule(&v, &e, gun, gzero, gzero, p == 2? gdeux: modis((GEN)e[3], 9));
        /* p | a1, a2; p^2  | a3, a4; p^3 | a6 */
    a21 = aux((GEN)e[2], p, 1);
    a42 = aux((GEN)e[4], p, 2);
    a63 = aux((GEN)e[5], p, 3);
    switch (numroots3(a21, a42, a63, p, &theroot))
    {
      case 3:
        if (p == 2)
          c = 1 + (a63 == 0) + ((a21 + a42 + a63) & 1);
        else
          c = 1 + (a63 == 0) + (((1 + a21 + a42 + a63) % 3) == 0)
                             + (((1 - a21 + a42 - a63) % 3) == 0);
        return localred_result(nudelta - 4, -1, c, v);
            /* I0*  */
      case 2: /* compute nu */
        if (theroot) cumule(&v, &e, gun, stoi(theroot * p), gzero, gzero);
            /* p | a1; p^2  | a2, a3; p^3 | a4; p^4 | a6 */
        nu = 1;
        pk  = stoi(p2);
        p2k = stoi(p2 * p2);
        for(;;)
        {
          be =  aux2((GEN)e[3], p, pk);
          ga = -aux2((GEN)e[5], p, p2k);
          al = 1;
          if (numroots2(al, be, ga, p, &theroot) == 2) break;
          if (theroot) cumule(&v, &e, gun, gzero, gzero, mulsi(theroot,pk));
          pk1 = pk;
          pk  = mulsi(p, pk);
          p2k = mulsi(p, p2k); nu++;

          al = a21;
          be = aux2((GEN)e[4], p, pk);
          ga = aux2((GEN)e[5], p, p2k);
          if (numroots2(al, be, ga, p, &theroot) == 2) break;
          if (theroot) cumule(&v, &e, gun, mulsi(theroot, pk1), gzero, gzero);
          p2k = mulsi(p, p2k); nu++;
        }
        if (p == 2)
          c = 4 - 2 * (ga & 1);
        else
          c = 3 + kross(be * be - al * ga, 3);
        return localred_result(nudelta - 4 - nu, -4 - nu, c, v);
            /* Inu* */
      case 1:
        if (theroot) cumule(&v, &e, gun, stoi(theroot * p), gzero, gzero);
            /* p | a1; p^2  | a2, a3; p^3 | a4; p^4 | a6 */
        a32 = aux((GEN)e[3], p, 2);
        a64 = aux((GEN)e[5], p, 4);
        if (numroots2(1, a32, -a64, p, &theroot) == 2)
        {
          if (p == 2)
            c = 3 - 2 * a64;
          else
            c = 2 + kross(a32 * a32 + a64, 3);
          return localred_result(nudelta - 6, -4, c, v);
        }
            /* IV*  */
        if (theroot) cumule(&v, &e, gun, gzero, gzero, stoi(theroot*p*p));
            /* p | a1; p^2 | a2; p^3 | a3, a4; p^5 | a6 */
        p4 = p2 * p2;
        if (smodis((GEN)e[4], p4))
          return localred_result(nudelta - 7, -3, 2, v);
            /* III* */
        
        if (smodis((GEN)e[5], p4 * p2))
          return localred_result(nudelta - 8, -2, 1, v);
            /* II*  */
        cumule(&v, &e, stoi(p), gzero, gzero, gzero); /* not minimal */
        nudelta -= 12;
    }
  }
  /* Not reached */
}

static GEN
localred(GEN e, GEN p, int minim)
{
  if (gcmpgs(p, 3) > 0) /* p != 2,3 */
    return localred_carac_p(e,p, minim);
  else
  {
    GEN z = localred_carac_23(e,itos(p));
    return minim? (GEN)z[3]: z;
  }
}

GEN
localreduction(GEN e, GEN p)
{
  pari_sp av = avma;
  checkell(e);
  if (typ(e[12]) != t_INT)
    err(talker,"not an integral curve in localreduction");
  return gerepileupto(av, localred(e, p, 0));
}

static GEN
ell_to_small(GEN E)
{
  long i;
  GEN e;
  if (lg(E) <= 14) return E;
  e = cgetg(14,t_VEC);
  for (i = 1; i < 14; i++) e[i] = E[i];
  return e;
}

static GEN
ellintegralmodel(GEN e)
{
  GEN a = cgetg(6,t_VEC), v, L, u;
  long i, l, k;

  checkell(e);
  L = cgetg(1, t_VEC);
  for (i = 1; i < 6; i++)
  {
    a[i] = e[i]; u = (GEN)a[i];
    switch(typ(u))
    {
      case t_INT: break;
      case t_FRAC: case t_FRACN: /* partial factorization */
        L = concatsp(L, (GEN)auxdecomp((GEN)u[2], 0)[1]);
        break;
      default: err(talker, "not a rational curve in ellintegralmodel");
    }
  }
  /* a = [a1, a2, a3, a4, a6] */
  l = lg(L);
  if (l == 1) return NULL;
  L = sort(L);
  for (k = i = 2; i < l; i++)
    if (!egalii((GEN)L[i], (GEN)L[i-1])) L[k++] = L[i];

  l = k; u = gun;
  for (k = 1; k < l; k++)
  {
    GEN p = (GEN)L[k];
    int n = 0, m;
    for (i = 1; i < 6; i++)
      if (!gcmp0((GEN)a[i]))
      {
        int r = (i == 5)? 6: i; /* a5 is missing */
	m = r * n + ggval((GEN)a[i], p);
	while (m < 0) { n++; m += r; }
      }
    u = mulii(u, gpowgs(p, n));
  }
  v = init_ch(); v[1] = linv(u); return v;
}

static void
standard_model(GEN e, GEN *pv)
{
  GEN r, s, t;
  s = gdiventgs((GEN)e[1], -2);
  r = gdiventgs(gaddgs(gsub(gsub((GEN)e[2], gmul(s,(GEN)e[1])), gsqr(s)), 1), -3);
  t = gdiventgs(ellLHS0(e,r), -2);
  cumulev(pv, gun, r, s, t);
}

GEN
ellminimalmodel(GEN E, GEN *ptv)
{
  pari_sp av = avma;
  GEN c4, c6, e, v, P;
  long l, k;

  v = ellintegralmodel(E);
  e = ell_to_small(E);
  if (v) e = coordch(e, v); else v = init_ch();
  c4 = (GEN)e[10];
  c6 = (GEN)e[11];
  P = (GEN)decomp(mppgcd(c4,c6))[1];
  l = lg(P);
  for (k = 1; k < l; k++)
  {
    GEN w = localred(e, (GEN)P[k], 1);
    if (!gcmp1((GEN)w[1]))
      cumule(&v, &e, (GEN)w[1], (GEN)w[2], (GEN)w[3], (GEN)w[4]);
  }
  standard_model(e, &v);
  e = coordch(E, v);
  if (ptv) { gerepileall(av, 2, &e, &v); *ptv = v; }
  else e = gerepileupto(av, e);
  return e;
}

/* Reduction of a rational curve E to its standard minimal model
 * (a1,a3 = 0 or 1, a2 = -1, 0 or 1).
 *
 * Return [N, [u,r,s,t], c], where
 *   N = arithmetic conductor of E
 *   c = product of the local Tamagawa numbers cp
 *   [u, r, s, t] = the change of variable reducing E to its minimal model,
 *     with u > 0 */
GEN
globalreduction(GEN E)
{
  long k, l;
  pari_sp av = avma;
  GEN c, P, result, N, v, e, c4, c6, D;

  v = ellintegralmodel(E);
  e = ell_to_small(E);
  if (v) e = coordch(e, v); else v = init_ch();

  c4 = (GEN)e[10];
  c6 = (GEN)e[11];
  D  = (GEN)e[12];
  P = (GEN)decomp(mppgcd(c4,c6))[1];
  l = lg(P);
  for (k = 1; k < l; k++) (long)pvaluation(D, (GEN)P[k], &D);
  if (!is_pm1(D)) P = concatsp(P, (GEN)decomp(absi(D))[1]);
  l = lg(P); c = N = gun;
  for (k = 1; k < l; k++)
  {
    GEN p = (GEN)P[k];
    GEN q = localreduction(e, p);
    GEN w = (GEN)q[3];
    N = mulii(N, powgi(p, (GEN)q[1]));
    c = mulii(c, (GEN)q[4]);
    if (!gcmp1((GEN)w[1]))
      cumule(&v, &e, (GEN)w[1], (GEN)w[2], (GEN)w[3], (GEN)w[4]);
  }
  standard_model(e, &v);
  result = cgetg(4, t_VEC);
  result[1] = (long)N;
  result[2] = (long)v;
  result[3] = (long)c; return gerepilecopy(av, result);
}

/* accumulate the effects of variable changes [u,r,s,t] and [U,R,S,T].
 * Frequent special cases: (U = 1) or (r = s = t = 0) */
static void
cumulev(GEN *vtotal, GEN u, GEN r, GEN s, GEN t)
{
  GEN U,R,S,T,UU,RR,SS,TT, v = *vtotal, w = cgetg(5, t_VEC);
  pari_sp av = avma;

  U = (GEN)v[1];
  R = (GEN)v[2];
  S = (GEN)v[3];
  T = (GEN)v[4];
  if (gcmp1(U))
  {
    UU = gcopy(u);
    RR = gadd(R, r);
    SS = gadd(S, s); av = avma;
    TT = gerepileupto(av, gadd(T, gadd(t, gmul(S, r))));
  }
  else if (gcmp0(r) && gcmp0(s) && gcmp0(t))
  {
    UU = gmul(U, u);
    RR = gcopy(R);
    SS = gcopy(S);
    TT = gcopy(T);
  }
  else /* general case */
  {
    GEN U2 = gsqr(U);
    UU = gmul(U, u);
    RR = gadd(R, gmul(U2, r));
    SS = gadd(S, gmul(U, s));
    TT = gadd(T, gmul(U2, gadd(gmul(U, t), gmul(S, r))));
    gerepileall(av, 4, &UU,&RR,&SS,&TT);
  }
  w[1] = (long)UU;
  w[2] = (long)RR;
  w[3] = (long)SS;
  w[4] = (long)TT; *vtotal = w;
}

static void
cumule(GEN *vtotal, GEN *e, GEN u, GEN r, GEN s, GEN t)
{
  *e = _coordch(*e, u, r, s, t);
  cumulev(vtotal, u, r, s, t);
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
  long n, m;
  pari_sp av=avma, tetpil;

  checkell(e); v = cgetg(precdl+3,t_SER);
  v[1] = evalsigne(1) | evalvalp(-2) | evalvarn(0);
  v[2] = un;
  c=gtoser(anell(e,precdl+1),0); setvalp(c,1);
  d=ginv(c); c=gsqr(d);
  for (n=-3; n<=(long)precdl-4; n++)
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
static long
_orderell(GEN e, GEN p)
{
  pari_sp av = avma;
  GEN p1 = p;
  long k;
  for (k = 1; k < 16; k++)
  {
    if (lg(p1) < 3) { avma = av; return k; }
    p1 = addell(e, p1, p);
  }
  avma = av; return 0;
}
GEN
orderell(GEN e, GEN p)
{
  long t;
  checkell(e); checkpt(p);
  t = typ(e[13]);
  if (t != t_INT && !is_frac_t(t))
    err(impl,"orderell for nonrational elliptic curves");
  return stoi( _orderell(e, p) );
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
  if (i==5) return _vec(gzero);
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
  long i, j, nlr, t, t2, k, k2;
  pari_sp av=avma;

  v = ellintegralmodel(e);
  if (v) e = coordch(e,v);
  pol = RHSpol(e);
  lr=ratroot(pol); nlr=lg(lr)-1;
  r=cgetg(17,t_VEC); r[1]=(long)_vec(gzero);
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
    w2 = _vec( stoi(t) );
    for (k=2; k<=t; k++)
      if (_orderell(e,(GEN)r[k]) == t) break;
    if (k>t) err(bugparier,"torsell (bug1)");

    w3 = _vec( (GEN)r[k] );
  }
  else
  {
    if (t&3) err(bugparier,"torsell (bug2)");
    t2 = t>>1;
    w2=cgetg(3,t_VEC); w2[1]=lstoi(t2); w2[2]=(long)gdeux;
    for (k=2; k<=t; k++)
      if (_orderell(e,(GEN)r[k]) == t2) break;
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
  long m, b, bold, prime = 2;
  pari_sp av = avma;
  byteptr p = diffptr;
  GEN D = (GEN)e[12];
  long n = bit_accuracy(lgefint(D)) >> 3;
  /* n = number of primes to try ~ 1 prime every 8 bits in D */
  b = bold = 5040; /* = 2^4 * 3^2 * 5 * 7 */
  m = 0; p++;
  while (m < n)
  {
    NEXT_PRIME_VIADIFF_CHECK(prime,p);
    if (smodis(D, prime))
    {
      b = cgcd(b, prime+1 - itos(apell0(e, (ulong)prime)));
      avma = av;
      if (b == 1) break;
      if (b == bold) m++; else { bold = b; m = 0; }
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

/* E the curve, w in C/Lambda ~ E of order n, returns q = pointell(w) as a
 * rational point on the curve, or NULL if q is not rational. */
static GEN
torspnt(GEN E, GEN w, long n, long prec)
{
  GEN p = cgetg(3,t_VEC), q = pointell(E, w, prec);
  long e;
  p[1] = lmul2n(_round(gmul2n((GEN)q[1],2), &e),-2);
  if (e > -5 || typ(p[1]) == t_COMPLEX) return NULL;
  p[2] = lmul2n(_round(gmul2n((GEN)q[2],3), &e),-3);
  if (e > -5 || typ(p[2]) == t_COMPLEX) return NULL;
  return (oncurve(E,p)
      && lg(powell(E,p,stoi(n))) == 2
      && _orderell(E,p) == n)? p: NULL;
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

/* <p,q> = E_tors, possibly NULL (= oo), p,q independent unless NULL
 * order p = k, order q = 2 unless NULL */
static GEN
tors(GEN e, long k, GEN p, GEN q, GEN v)
{
  GEN r;
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
      if (v) p = pointch(p,v);
      r = cgetg(4,t_VEC);
      r[1] = lstoi(k);
      r[2] = (long)_vec( (GEN)r[1] );
      r[3] = (long)_vec( gcopy(p) );
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
  long B, i, ord, pr, prec, k = 1;
  pari_sp av=avma;
  GEN v,w,w1,w22,w1j,w12,p,tor1,tor2;

  checkbell(e);
  v = ellintegralmodel(e);
  if (v) e = coordch(e,v);
 
  B = torsbound(e); /* #E_tor | B */
  if (B == 1) { avma = av; return tors(e,1,NULL,NULL, v); }

  pr = DEFAULTPREC + ((lgefint((GEN)e[12])-2) >> 1); /* pr >= size of sqrt(D) */
  w1 = (GEN)e[15];
  prec = precision(w1);
  if (prec < pr) err(precer, "torselldoud");
  if (pr < prec) { prec = pr; e = gprec_w(e, pr); w1 = (GEN)e[15]; }
  if (v) v[1] = linv((GEN)v[1]);
  w22 = gmul2n((GEN)e[16],-1);
  if (B % 4)
  { /* cyclic of order 1, p, 2p, p <= 5 */
    p = NULL;
    for (i=10; i>1; i--)
    {
      if (B%i != 0) continue;
      w1j = gdivgs(w1,i);
      p = torspnt(e,w1j,i,prec);
      if (!p && i%2==0)
      {
        p = torspnt(e,gadd(w22,w1j),i,prec);
        if (!p) p = torspnt(e,gadd(w22,gmul2n(w1j,1)),i,prec);
      }
      if (p) { k = i; break; }
    }
    return gerepileupto(av, tors(e,k,p,NULL, v));
  }

  ord = 0; tor1 = tor2 = NULL;
  w12 = gmul2n(w1,-1);
  if ((p = torspnt(e,w12,2,prec)))
  {
    tor1 = p; ord++;
  }
  w = w22;
  if ((p = torspnt(e,w,2,prec)))
  {
    tor2 = p; ord += 2;
  }
  if (!ord)
  {
    w = gadd(w12,w22);
    if ((p = torspnt(e,w,2,prec)))
    {
      tor2 = p; ord += 2;
    }
  }
  p = NULL;
  switch(ord)
  {
    case 0: /* no point of order 2 */
      for (i=9; i>1; i-=2)
      {
        if (B%i != 0) continue;
        w1j = gdivgs(w1,i);
        p = torspnt(e,w1j,i,prec);
        if (p) { k = i; break; }
      }
      break;

    case 1: /* 1 point of order 2: w1 / 2 */
      for (i=12; i>2; i-=2)
      {
        if (B%i != 0) continue;
        w1j = gdivgs(w1,i);
        p = torspnt(e,w1j,i,prec);
        if (!p && i%4==0)
          p = torspnt(e,gadd(w22,w1j),i,prec);
        if (p) { k = i; break; }
      }
      if (!p) { p = tor1; k = 2; }
      break;

    case 2: /* 1 point of order 2: w = w2/2 or (w1+w2)/2 */
      for (i=5; i>1; i-=2)
      {
        if (B%i != 0) continue;
        w1j = gdivgs(w1,i);
        p = torspnt(e,gadd(w,w1j),2*i,prec);
        if (p) { k = 2*i; break; }
      }
      if (!p) { p = tor2; k = 2; }
      tor2 = NULL; break;

    case 3: /* 2 points of order 2: w1/2 and w2/2 */
      for (i=8; i>2; i-=2)
      {
        if (B%(2*i) != 0) continue;
        w1j = gdivgs(w1,i);
        p = torspnt(e,w1j,i,prec);
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

/* LOCAL ROOT NUMBERS, after HALBERSTADT */

/* p = 2 or 3 */
static long
neron(GEN e, GEN p, long* ptkod)
{
  long kod, v4, v6, vd;
  pari_sp av=avma;
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
  long n2, kod, u, v, x1, y1, d1, v4, v6, w2;
  pari_sp av=avma;
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
  long n2, kod, u, v, d1, r6, K4, K6, v4;
  pari_sp av=avma;
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

/* assume p > 3 */
static long
ellrootno_p(GEN e, GEN p, GEN ex)
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
  if (cmpis(p,3) > 0) return ellrootno_p(e,p,ex);
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
  if (cmpis(p,3)>0) return ellrootno_p(e,p,stoi(exs));
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
  pari_sp av = avma;
  long s;
  if (!p) p = gun;
  s = ellrootno_all(e, p, NULL);
  avma = av; return s;
}
