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
#include "paripriv.h"

void
checkellpt(GEN z)
{ if (typ(z)!=t_VEC || lg(z) > 3) pari_err_TYPE("checkellpt", z); }
void
checkell5(GEN e)
{ if (typ(e)!=t_VEC || lg(e) < 6) pari_err_TYPE("checkell5",e); }
void
checksmallell(GEN e)
{ if (typ(e)!=t_VEC || lg(e) < 14) pari_err_TYPE("checksmallell",e); }
void
checkell(GEN e)
{ if (typ(e)!=t_VEC || lg(e) < 20) pari_err_TYPE("checkell",e); }
static void
checksmallell_real(GEN e)
{ checksmallell(e);
  switch (typ(ell_get_disc(e)))
  {
    case t_INT:
    case t_FRAC: break;
    default: pari_err_TYPE("checksmallell_real", e);
  }
}
void
checkell_real(GEN e)
{ if (typ(e)!=t_VEC || !ell_is_real(e)) pari_err_TYPE("checkell_real", e); }
void
checkell_padic(GEN e)
{ if (typ(e)!=t_VEC || !ell_is_padic(e)) pari_err_TYPE("checkell_padic",e); }
static void
checkcoordch(GEN z)
{ if (typ(z)!=t_VEC || lg(z) != 5) pari_err_TYPE("checkcoordch",z); }

/* 4 X^3 + b2 X^2 + 2b4 X + b6 */
static GEN
RHSpol(GEN e)
{
  GEN z = cgetg(6, t_POL); z[1] = evalsigne(1);
  gel(z,2) = ell_get_b6(e);
  gel(z,3) = gmul2n(ell_get_b4(e),1);
  gel(z,4) = ell_get_b2(e);
  gel(z,5) = utoipos(4); return z;
}

static int
invcmp(void *E, GEN x, GEN y) { (void)E; return -gcmp(x,y); }

INLINE GEN
ell_realroot(GEN e) { return gmael(e,14,1); }

static GEN
ell_realrootprec(GEN e, long prec)
{
  GEN R;
  if (lg(e)>14 && realprec(ell_realroot(e))>=prec)
    return ell_realroot(e);
  R = cleanroots(RHSpol(e), prec);
  /* sort roots in decreasing order */
  if (gsigne(ell_get_disc(e)) > 0) gen_sort_inplace(R, NULL, &invcmp, NULL);
  return gel(R,1);
}

/* x^3 + a2 x^2 + a4 x + a6 */
static GEN
ellRHS(GEN e, GEN x)
{
  GEN z;
  z = gadd(ell_get_a2(e),x);
  z = gadd(ell_get_a4(e), gmul(x,z));
  z = gadd(ell_get_a6(e), gmul(x,z));
  return z;
}

/* a1 x + a3 */
static GEN
ellLHS0(GEN e, GEN x)
{
  GEN a1 = ell_get_a1(e);
  GEN a3 = ell_get_a3(e);
  return gequal0(a1)? a3: gadd(a3, gmul(x,a1));
}

static GEN
ellLHS0_i(GEN e, GEN x)
{
  GEN a1 = ell_get_a1(e);
  GEN a3 = ell_get_a3(e);
  return signe(a1)? addii(a3, mulii(x, a1)): a3;
}

/* y^2 + a1 xy + a3 y */
static GEN
ellLHS(GEN e, GEN z)
{
  GEN y = gel(z,2);
  return gmul(y, gadd(y, ellLHS0(e,gel(z,1))));
}

/* 2y + a1 x + a3 */
static GEN
d_ellLHS(GEN e, GEN z)
{
  return gadd(ellLHS0(e, gel(z,1)), gmul2n(gel(z,2),1));
}

static GEN
ell_to_small(GEN E) { return (lg(E) <= 14)? E: vecslice(E, 1, 13); }

/* fill y from x[1], ..., x[5] */
static int
initsmall(GEN x, GEN y)
{
  GEN a1,a2,a3,a4,a6, b2,b4,b6,b8, c4,c6, D, j, a11, a13, a33, b22;
  long l = lg(x);

  switch(l)
  {
    case 1:
    case 2:
    case 4:
    case 5:
      pari_err_TYPE("ellxxx [not an elliptic curve (ell5)]",x);
      return 0; break; /* not reached */
    case 3:
      a1 = a2 = a3 = gen_0;
      a4 = gel(x,1);
      a6 = gel(x,2);
      break;
    default :  /* l > 5 */
      a1 = gel(x,1);
      a2 = gel(x,2);
      a3 = gel(x,3);
      a4 = gel(x,4);
      a6 = gel(x,5);
      break;
  }
  if (typ(x)!=t_VEC)
    pari_err_TYPE("ellxxx [not an elliptic curve (ell5)]",x);
  gel(y,1) = a1;
  gel(y,2) = a2;
  gel(y,3) = a3;
  gel(y,4) = a4;
  gel(y,5) = a6;
  a11 = gsqr(a1);
  b2 = gadd(a11, gmul2n(a2,2));
  gel(y,6) = b2; /* a1^2 + 4a2 */

  a13 = gmul(a1, a3);
  b4 = gadd(a13, gmul2n(a4,1));
  gel(y,7) = b4; /* a1 a3 + 2a4 */

  a33 = gsqr(a3);
  b6 = gadd(a33, gmul2n(a6,2));
  gel(y,8) = b6; /* a3^2 + 4 a6 */
  b8 = gsub(gadd(gmul(a11,a6), gmul(b6, a2)), gmul(a4, gadd(a4,a13)));
  gel(y,9) = b8; /* a1^2 a6 + 4a6 a2 + a2 a3^2 - a4(a4 + a1 a3) */

  b22 = gsqr(b2);
  c4 = gadd(b22, gmulsg(-24,b4));
  gel(y,10) = c4; /* b2^2 - 24 b4 */

  c6 = gadd(gmul(b2,gsub(gmulsg(36,b4),b22)), gmulsg(-216,b6));
  gel(y,11) = c6; /* 36 b2 b4 - b2^3 - 216 b6 */

  D = gsub(gmul(b4, gadd(gmulsg(9,gmul(b2,b6)),gmulsg(-8,gsqr(b4)))),
           gadd(gmul(b22,b8),gmulsg(27,gsqr(b6))));
  gel(y,12) = D;
  if (gequal0(D)) return 0;

  j = gdiv(gmul(gsqr(c4),c4), D);
  gel(y,13) = j; return 1;
}

void
ellprint(GEN e)
{
  pari_sp av = avma;
  long vx, vy;
  GEN z;
  checkell5(e);
  vx = fetch_var(); name_var(vx, "X");
  vy = fetch_var(); name_var(vy, "Y"); z = mkvec2(pol_x(vx), pol_x(vy));
  err_printf("%Ps - (%Ps)\n", ellLHS(e, z), ellRHS(e, pol_x(vx)));
  (void)delete_var();
  (void)delete_var(); avma = av;
}

/* compute a,b such that E1: y^2 = x(x-a)(x-b) ~ E0 */
/* e1 = ell_realroot(e) */
static GEN
new_coords(GEN e, GEN x, GEN e1, GEN *pta, GEN *ptb, int flag, long prec)
{
  GEN b2 = ell_get_b2(e), a, b, p1, p2, w;
  long ty = typ(e1);

  p2 = gmul2n(gadd(gmulsg(12,e1), b2), -2); /* = (12 e1 + b2) / 4 */
  if (ty == t_PADIC)
    w = gel(e,18);
  else
  {
    GEN b4 = ell_get_b4(e);
    if (!is_const_t(ty)) pari_err_TYPE("zell",e1);

    /* w^2 = 2b4 + 2b2 e1 + 12 e1^2 = 4(e1-e2)(e1-e3) */
    w = sqrtr( gmul2n(gadd(b4, gmul(e1,gadd(b2, mulur(6,e1)))),1) );
    if (gsigne(p2) > 0) setsigne(w, -1);
  }
  *pta = a = gmul2n(gsub(w,p2),-2);
  *ptb = b = gmul2n(w,-1); /* = sqrt( (e1 - e2)(e1 - e3) ) */
  if (!x) return NULL;
  if (flag)
  {
    GEN d = gsub(a,b);
    p1 = gadd(x, gmul2n(gadd(gmul2n(e1,2), b2),-3));
    p1 = gmul2n(p1,-1);
    p1 = gadd(p1, gsqrt(gsub(gsqr(p1), gmul(a,d)), prec));
    return gmul(p1, gsqr(gmul2n(gaddsg(1,gsqrt(gdiv(gadd(p1,d),p1),prec)),-1)));
  }
  x = gsub(x, e1);
  p1 = gadd(x, b);
  return gmul2n(gadd(p1, gsqrt(gsub(gsqr(p1), gmul2n(gmul(a,x),2)),prec)), -1);
}

/* a1, b1 are non-0 t_REALs */
static GEN
do_agm(GEN *ptx, GEN a1, GEN b1)
{
  const long s = signe(b1), l = minss(realprec(a1), realprec(b1)), G = 6 - prec2nbits(l);
  GEN p1, a, b, x;

  x = gmul2n(subrr(a1,b1),-2);
  if (!signe(x)) pari_err_PREC("ellinit");
  for(;;)
  {
    GEN d;
    a = a1; b = b1;
    b1 = sqrtr(mulrr(a,b)); setsigne(b1, s);
    a1 = gmul2n(addrr(addrr(a,b), gmul2n(b1,1)),-2);
    d = subrr(a1,b1);
    if (!signe(d)) break;
    p1 = sqrtr( divrr(addrr(x,d),x) );
    x = mulrr(x, sqrr(addsr(1,p1)));
    shiftr_inplace(x, -2);
    if (expo(d) <= G + expo(b1)) break;
  }
  *ptx = x; return ginv(gmul2n(a1,2));
}
/* a1, b1 are t_PADICs */
static GEN
do_padic_agm(GEN *ptx, GEN a1, GEN b1, GEN p)
{
  GEN p1, a, b, bmod1, bmod = modii(gel(b1,4),p), x = *ptx;
  long mi;

  if (!x) x = gmul2n(gsub(a1,b1),-2);
  if (gequal0(x)) pari_err_PREC("ellinit");
  mi = minss(precp(a1),precp(b1));
  for(;;)
  {
    GEN d;
    a = a1; b = b1;
    b1 = gprec(Qp_sqrt(gmul(a,b)),mi);
    bmod1 = modii(gel(b1,4),p);
    if (!equalii(bmod1,bmod)) b1 = gneg_i(b1);
    a1 = gprec(gmul2n(gadd(gadd(a,b),gmul2n(b1,1)),-2),mi);
    d = gsub(a1,b1);
    if (gequal0(d)) break;
    p1 = Qp_sqrt(gdiv(gadd(x,d),x));
    if (! gequal1(modii(gel(p1,4),p))) p1 = gneg_i(p1);
    x = gmul(x, gsqr(gmul2n(gaddsg(1,p1),-1)));
  }
  *ptx = x; return ginv(gmul2n(a1,2));
}

GEN
ellinit_padic(GEN x, GEN p, long prec)
{
  GEN y, j, b2, b4, c4, c6, p1, w, pv, a1, b1, x1, u2, q, e0, e1;
  long i, alpha;

  y = cgetg(20,t_VEC);
  if (!initsmall(x,y)) return cgetg(1,t_VEC);
  /* convert now, not before initsmall: better accuracy */
  for (i=1; i<=13; i++)
    if (typ(gel(y,i)) != t_PADIC) gel(y,i) = cvtop(gel(y,i), p, prec);
  j = ell_get_j(y);
  if (gequal0(j) || valp(j) >= 0) /* p | j */
    pari_err(e_MISC,"valuation of j must be negative in p-adic ellinit");
  if (equaliu(p,2))
  {
    pv = utoipos(4);
    pari_err_IMPL("ellinit for 2-adic numbers");
  }
  else
    pv = p;

  b2 = ell_get_b2(y);
  b4 = ell_get_b4(y);
  c4 = ell_get_c4(y);
  c6 = ell_get_c6(y); alpha = valp(c4) >> 1;
  setvalp(c4,0);
  setvalp(c6,0);
  e1 = gdiv(c6, gmulsg(6,c4));
  c4 = gdivgs(c4,48);
  c6 = gdivgs(c6,864);
  do
  {
    GEN e2 = gsqr(e1);
    e0 = e1;  /* (c6 + 2e1^3) / (3e1^2 - c4) */
    e1 = gdiv(gadd(gmul2n(gmul(e0,e2),1),c6), gsub(gmulsg(3,e2),c4));
  }
  while (!gequal(e0,e1));
  setvalp(e1, valp(e1)+alpha);

  e1 = gsub(e1, gdivgs(b2,12));
  w = Qp_sqrt(gmul2n(gadd(b4,gmul(e1,gadd(b2,gmulsg(6,e1)))),1));

  p1 = gaddgs(gdiv(gmulsg(3,e0),w),1);
  if (valp(p1) <= 0) w = gneg_i(w);
  gel(y,18) = w;

  a1 = gmul2n(gsub(w,gadd(gmulsg(3,e1),gmul2n(b2,-2))),-2);
  b1 = gmul2n(w,-1); x1 = NULL;
  u2 = do_padic_agm(&x1,a1,b1,pv);

  p1 = ginv(gmul2n(gmul(u2,x1),1));
  w = gaddsg(1,p1);
  q = Qp_sqrt(gmul(p1, gaddgs(p1,2))); /* sqrt(w^2 - 1) */
  p1 = gadd(w,q);
  q = gequal0(p1)? gsub(w,q): p1;
  if (valp(q) < 0) q = ginv(q);

  gel(y,14) = mkvec(e1);
  gel(y,15) = u2;
  gel(y,16) = ((valp(u2)&1) || kronecker(gel(u2,4),p) <= 0)? gen_0: Qp_sqrt(u2);
  gel(y,17) = q;
  gel(y,19) = gen_0; return y;
}

static void
set_dummy(GEN y) {
  gel(y,14)=gel(y,15)=gel(y,16)=gel(y,17)=gel(y,18)=gel(y,19) = gen_0;
}

static long
base_ring(GEN x, GEN *pp, long *prec)
{
  long i, e = LONG_MAX, imax = minss(lg(x), 6);
  GEN p = NULL;

  for (i = 1; i < imax; i++)
  {
    GEN q = gel(x,i);
    switch(typ(q)) {
      case t_PADIC: {
        long e2 = signe(q[4])? precp(q)+valp(q): valp(q);
        if (e2 < e) e = e2;
        if (!p)
          p = gel(q,2);
        else if (!equalii(p, gel(q,2)))
          pari_err(e_MISC,"incompatible p-adic numbers in ellinit");
        break;
      }
      case t_INT: case t_REAL: case t_FRAC:
        break;

      default: /* base ring too general */
        *prec = 0; break;
    }
  }
  if (p) { *pp = p; *prec = e; return t_PADIC; }
  return t_REAL;
}

GEN
ellinit_real(GEN x, long prec)
{
  GEN y, D, R, T, w, a1, b1, x1, u2, q, pi2, aw1, w1, w2;
  long PREC, e;

  y = cgetg(20,t_VEC);
  if (!initsmall(x,y)) return cgetg(1,t_VEC);
  if (!prec) { set_dummy(y); return y; }

  D = gel(y,12);
  switch(typ(D))
  {
    case t_INT: e = expi(D); break;
    case t_FRAC:e = maxss(expi(gel(D,1)), expi(gel(D,2))); break;
    default: e = -1; break;
  }
  PREC = prec;
  if (e > 0) PREC += nbits2extraprec(e >> 1);
  R = cleanroots(RHSpol(y), PREC);
  /* sort roots in decreasing order */
  if (gsigne(D) > 0) gen_sort_inplace(R, NULL, &invcmp, NULL);
  gel(y,14) = R;

  (void)new_coords(y, NULL, gel(R,1), &a1, &b1, 0, 0);
  u2 = do_agm(&x1,a1,b1); /* 1/4M */

  pi2 = Pi2n(1, prec);
  aw1 = mulrr(pi2, sqrtr_abs(u2));
  w1 = (signe(u2) < 0)? aw1: mkcomplex(gen_0,aw1);
  w = addsr(1, invr(shiftr(mulrr(u2,x1),1)));
  q = sqrtr( subrs(sqrr(w), 1) ); /* real or pure imaginary */
  /* same formula, split in two branches for efficiency */
  if (typ(q) == t_REAL) {
    GEN t, aw1t, aux;
    q = (signe(w) > 0)? addrr(w, q): subrr(w, q);
    /* if |q| > 1, we should have replaced it by 1/q. Instead, we change
     * the sign of log(q) */
    t = divrr(logr_abs(q), pi2); setsigne(t, -1);
    /* t = log|q|/2Pi, |q|<1 */
    /* w2 = w1 I log(q)/2Pi = I w1 t [- w1/2 if q < 0] */
    aw1t = mulrr(aw1,t); /* < 0 */
    aux = (signe(q) < 0)? negr(shiftr(aw1,-1)): gen_0;
    if (typ(w1) == t_COMPLEX)
      w2 = mkcomplex(negr(aw1t), aux);
    else
      w2 = mkcomplex(aux, aw1t);
  } else { /* FIXME: I believe this can't happen */
    GEN t;
    if (signe(w) < 0) togglesign(q);
    q = mkcomplex(w, q);
    t = mulcxI(gdiv(glog(q,prec), pi2));
    /* we want -t to belong to Poincare's half plane */
    if (signe(gel(t,2)) > 0) t = gneg(t);
    w2 = gmul(w1, t);
  }
  if (typ(w1) == t_COMPLEX) w1 = shiftr(gel(w2,1), 1);

  gel(y,15) = w1; /* > 0 */
  gel(y,16) = w2;
  T = elleta(mkvec2(w1,w2), prec);
  gel(y,17) = gel(T,1);
  gel(y,18) = gel(T,2);
  gel(y,19) = absr(mulrr(w1, gel(w2,2)));
  return y;
}

static GEN
get_ell(GEN x)
{
  switch(typ(x))
  {
    case t_STR: return gel(ellsearchcurve(x),2);
    case t_VEC: switch(lg(x)) { case 3: case 6: case 14: case 20: return x; }
    /*fall through*/
  }
  pari_err_TYPE("ellxxx [not an elliptic curve (ell5)]",x);
  return NULL;/*not reached*/
}
GEN
smallellinit(GEN x)
{
  pari_sp av = avma;
  GEN y = cgetg(14,t_VEC);
  if (!initsmall(get_ell(x),y)) y = cgetg(1,t_VEC);
  return gerepilecopy(av,y);
}
GEN
ellinit(GEN x, long prec)
{
  pari_sp av = avma;
  long tx;
  GEN p, y;
  x = get_ell(x);
  tx = base_ring(x, &p, &prec);
  y = (tx == t_PADIC)? ellinit_padic(x, p, prec): ellinit_real(x, prec);
  return gerepilecopy(av, y);
}
GEN
ellinit0(GEN x, long flag,long prec)
{
  switch(flag)
  {
    case 0: return ellinit(x,prec);
    case 1: return smallellinit(x);
    default: pari_err_FLAG("ellinit");
  }
  return NULL; /* not reached */
}

/********************************************************************/
/**                                                                **/
/**                       Coordinate Change                        **/
/**                                                                **/
/********************************************************************/
/* [1,0,0,0] */
static GEN
init_ch(void) {
  GEN v = cgetg(5, t_VEC);
  gel(v,1) = gen_1;
  gel(v,2) = gel(v,3) = gel(v,4) = gen_0;
  return v;
}

static GEN
coordch4(GEN e, GEN u, GEN r, GEN s, GEN t)
{
  GEN a1 = ell_get_a1(e);
  GEN a2 = ell_get_a2(e);
  GEN b4 = ell_get_b4(e);
  GEN b6 = ell_get_b6(e);
  GEN R, y, p1, p2, v, v2, v3, v4, v6, r2, b2r, rx3 = gmulsg(3,r);
  long i, lx = lg(e);

  y = cgetg(lx,t_VEC);
  v = ginv(u); v2 = gsqr(v); v3 = gmul(v,v2); v4 = gsqr(v2); v6 = gsqr(v3);
  /* A1 = (a1 + 2s) / u */
  gel(y,1) = gmul(v,gadd(a1,gmul2n(s,1)));
  /* A2 = (a2 + 3r - (a1 s + s^2)) / u^2 */
  gel(y,2) = gmul(v2,gsub(gadd(a2,rx3),gmul(s,gadd(a1,s))));
  p2 = ellLHS0(e,r);
  p1 = gadd(gmul2n(t,1), p2);
  /* A3 = (2t + a1 r + a3) / u^3 */
  gel(y,3) = gmul(v3,p1);
  p1 = gsub(ell_get_a4(e),gadd(gmul(t,a1),gmul(s,p1)));
  /* A4 = (a4 - (a1 t + s (2t + a1 r + a3)) + 2a2 r + 3r^2) / u^4 */
  gel(y,4) = gmul(v4,gadd(p1,gmul(r,gadd(gmul2n(a2,1),rx3))));
  /* A6 = (r^3 + a2 r^2 + a4 r + a6 - t(t + a1 r + a3)) / u^6 */
  gel(y,5) = gmul(v6,gsub(ellRHS(e,r), gmul(t,gadd(t, p2))));
  if (lx == 6) return y;
  if (lx < 14) pari_err_TYPE("coordch [not an elliptic curve]",e);

  /* B2 = (b2 + 12r) / u^2 */
  gel(y,6) = gmul(v2,gadd(ell_get_b2(e),gmul2n(rx3,2)));
  b2r = gmul(r, ell_get_b2(e));
  r2 = gsqr(r);
  /* B4 = (b4 + b2 r + 6r^2) / u^4 */
  gel(y,7) = gmul(v4,gadd(b4,gadd(b2r, gmulsg(6,r2))));
  /* B6 = (b6 + 2b4 r + 2b2 r^2 + 4r^3) / u^6 */
  gel(y,8) = gmul(v6,gadd(b6,gmul(r,gadd(gmul2n(b4,1),
                                            gadd(b2r,gmul2n(r2,2))))));
  /* B8 = (b8 + 3b6r + 3b4 r^2 + b2 r^3 + 3r^4) / u^8 */
  p1 = gadd(gmulsg(3,b4),gadd(b2r, gmulsg(3,r2)));
  gel(y,9) = gmul(gsqr(v4),
              gadd(ell_get_b8(e), gmul(r,gadd(gmulsg(3,b6), gmul(r,p1)))));
  gel(y,10) = gmul(v4,ell_get_c4(e));
  gel(y,11) = gmul(v6,ell_get_c6(e));
  gel(y,12) = gmul(gsqr(v6),ell_get_disc(e));
  gel(y,13) = ell_get_j(e);
  if (lx == 14) return y;
  if (lx < 20) pari_err_TYPE("coordch [not an elliptic curve]",e);
  R = ell_get_roots(e);
  if (typ(R) != t_COL) set_dummy(y);
  else if (typ(e[1])==t_PADIC)
  {
    gel(y,14) = mkvec( gmul(v2, gsub(gel(R,1),r)) );
    gel(y,15) = gmul(gel(e,15), gsqr(u));
    gel(y,16) = gmul(gel(e,16), u);
    gel(y,17) = gel(e,17);
    gel(y,18) = gmul(gel(e,18), v2);
    gel(y,19) = gen_0;
  }
  else
  {
    p2 = cgetg(4,t_COL);
    for (i=1; i<=3; i++) gel(p2,i) = gmul(v2, gsub(gel(R,i),r));
    gel(y,14) = p2;
    gel(y,15) = gmul(gel(e,15), u);
    gel(y,16) = gmul(gel(e,16), u);
    gel(y,17) = gdiv(gel(e,17), u);
    gel(y,18) = gdiv(gel(e,18), u);
    gel(y,19) = gmul(gel(e,19), gsqr(u));
  }
  return y;
}
static GEN
_coordch(GEN e, GEN w)
{ return coordch4(e, gel(w,1), gel(w,2), gel(w,3), gel(w,4)); }
GEN
ellchangecurve(GEN e, GEN w)
{
  pari_sp av = avma;
  checkcoordch(w); checkell5(e);
  return gerepilecopy(av, _coordch(e, w));
}

/* accumulate the effects of variable changes [u,r,s,t] and [U,R,S,T], all of
 * them integers. Frequent special cases: (U = 1) or (r = s = t = 0) */
static void
cumulev(GEN *vtotal, GEN u, GEN r, GEN s, GEN t)
{
  GEN U2,U,R,S,T, v = *vtotal;
  pari_sp av;

  U = gel(v,1);
  R = gel(v,2);
  S = gel(v,3);
  T = gel(v,4);
  if (gequal1(U))
  {
    gel(v,1) = u;
    gel(v,2) = addii(R, r);
    gel(v,3) = addii(S, s); av = avma;
    gel(v,4) = gerepileuptoint(av, addii(T, addii(t, mulii(S, r))));
  }
  else if (!signe(r) && !signe(s) && !signe(t))
    gel(v,1) = mulii(U, u);
  else /* general case */
  {
    U2 = sqri(U);
    gel(v,1) = mulii(U, u);
    gel(v,2) = addii(R, mulii(U2, r));
    gel(v,3) = addii(S, mulii(U, s));
    gel(v,4) = addii(T, mulii(U2, addii(mulii(U, t), mulii(S, r))));
  }
}
/* as above, no assumption */
static void
gcumulev(GEN *vtotal, GEN w)
{
  GEN u,r,s,t,U2,U,R,S,T, v = *vtotal;

  u = gel(w,1);
  r = gel(w,2);
  s = gel(w,3);
  t = gel(w,4);
  U = gel(v,1); gel(v,1) = gmul(U, u); U2 = gsqr(U);
  R = gel(v,2); gel(v,2) = gadd(R, gmul(U2, r));
  S = gel(v,3); gel(v,3) = gadd(S, gmul(U, s));
  T = gel(v,4); gel(v,4) = gadd(T, gmul(U2, gadd(gmul(U, t), gmul(S, r))));
}

static void
cumule(GEN *vtotal, GEN *e, GEN u, GEN r, GEN s, GEN t)
{
  *e = coordch4(*e, u, r, s, t);
  cumulev(vtotal, u, r, s, t);
}

/* X = (x-r)/u^2
 * Y = (y - s(x-r) - t) / u^3 */
static GEN
ellchangepoint0(GEN x, GEN v2, GEN v3, GEN r, GEN s, GEN t)
{
  GEN p1,z;

  if (ell_is_inf(x)) return x;

  z = cgetg(3,t_VEC); p1 = gsub(gel(x,1),r);
  gel(z,1) = gmul(v2, p1);
  gel(z,2) = gmul(v3, gsub(gel(x,2), gadd(gmul(s,p1),t)));
  return z;
}

GEN
ellchangepoint(GEN x, GEN ch)
{
  GEN y, v, v2, v3, r, s, t, u;
  long tx, i, lx = lg(x);
  pari_sp av = avma;

  if (typ(x) != t_VEC) pari_err_TYPE("ellchangepoint",x);
  checkcoordch(ch);
  if (lx == 1) return cgetg(1, t_VEC);
  u = gel(ch,1);
  r = gel(ch,2);
  s = gel(ch,3);
  t = gel(ch,4);
  v = ginv(u); v2 = gsqr(v); v3 = gmul(v,v2);
  tx = typ(x[1]);
  if (is_matvec_t(tx))
  {
    y = cgetg(lx,tx);
    for (i=1; i<lx; i++)
      gel(y,i) = ellchangepoint0(gel(x,i),v2,v3,r,s,t);
  }
  else
    y = ellchangepoint0(x,v2,v3,r,s,t);
  return gerepilecopy(av,y);
}

/* x =  u^2*X +r
 * y =  u^3*Y +s*u^2*X+t */
static GEN
ellchangepointinv0(GEN x, GEN u2, GEN u3, GEN r, GEN s, GEN t)
{
  GEN u2X, z, X, Y;
  if (ell_is_inf(x)) return x;

  X = gel(x,1);
  Y = gel(x,2);
  u2X = gmul(u2,X);
  z = cgetg(3, t_VEC);
  gel(z,1) = gadd(u2X, r);
  gel(z,2) = gadd(gmul(u3, Y), gadd(gmul(s, u2X), t));
  return z;
}

GEN
ellchangepointinv(GEN x, GEN ch)
{
  GEN y, u, r, s, t, u2, u3;
  long tx, i, lx = lg(x);
  pari_sp av = avma;

  if (typ(x) != t_VEC) pari_err_TYPE("ellchangepointinv",x);
  checkcoordch(ch);
  if (lx == 1) return cgetg(1, t_VEC);
  u = gel(ch,1);
  r = gel(ch,2);
  s = gel(ch,3);
  t = gel(ch,4);
  tx = typ(x[1]);
  u2 = gsqr(u); u3 = gmul(u,u2);
  if (is_matvec_t(tx))
  {
    y = cgetg(lx,tx);
    for (i=1; i<lx; i++)
      gel(y,i) = ellchangepointinv0(gel(x,i),u2,u3,r,s,t);
  }
  else
    y = ellchangepointinv0(x,u2,u3,r,s,t);
  return gerepilecopy(av,y);
}


static long
ellexpo(GEN E)
{
  long i, f, e = -(long)HIGHEXPOBIT;
  for (i=1; i<=5; i++)
  {
    f = gexpo(gel(E,i));
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

  checkellpt(z); if (ell_is_inf(z)) return 1; /* oo */
  av = avma;
  LHS = ellLHS(e,z);
  RHS = ellRHS(e,gel(z,1)); x = gsub(LHS,RHS);
  if (gequal0(x)) { avma = av; return 1; }
  pl = precision(LHS);
  pr = precision(RHS);
  if (!pl && !pr) { avma = av; return 0; } /* both of LHS, RHS are exact */
  /* at least one of LHS,RHS is inexact */
  ex = pr? gexpo(RHS): gexpo(LHS); /* don't take exponent of exact 0 */
  if (!pr || (pl && pl < pr)) pr = pl; /* min among nonzero elts of {pl,pr} */
  expx = gexpo(x);
  pr = (expx < ex - prec2nbits(pr) + 15
     || expx < ellexpo(e) - prec2nbits(pr) + 5);
  avma = av; return pr;
}

GEN
ellisoncurve(GEN e, GEN x)
{
  long i, tx = typ(x), lx;

  checkell5(e);
  if (!is_vec_t(tx)) pari_err_TYPE("ellisoncurve [point]", x);
  lx = lg(x); if (lx==1) return cgetg(1,tx);
  tx = typ(x[1]);
  if (is_vec_t(tx))
  {
    GEN z = cgetg(lx,tx);
    for (i=1; i<lx; i++) gel(z,i) = ellisoncurve(e,gel(x,i));
    return z;
  }
  return oncurve(e, x)? gen_1: gen_0;
}

GEN
addell(GEN e, GEN z1, GEN z2)
{
  GEN p1, p2, x, y, x1, x2, y1, y2;
  pari_sp av = avma, tetpil;

  checkell5(e); checkellpt(z1); checkellpt(z2);
  if (ell_is_inf(z1)) return gcopy(z2);
  if (ell_is_inf(z2)) return gcopy(z1);

  x1 = gel(z1,1); y1 = gel(z1,2);
  x2 = gel(z2,1); y2 = gel(z2,2);
  if (x1 == x2 || gequal(x1,x2))
  { /* y1 = y2 or -LHS0-y2 */
    if (y1 != y2)
    {
      int eq;
      if (precision(y1) || precision(y2))
        eq = (gexpo(gadd(ellLHS0(e,x1),gadd(y1,y2))) >= gexpo(y1));
      else
        eq = gequal(y1,y2);
      if (!eq) { avma = av; return ellinf(); }
    }
    p2 = d_ellLHS(e,z1);
    if (gequal0(p2)) { avma = av; return ellinf(); }
    p1 = gadd(gsub(ell_get_a4(e),gmul(ell_get_a1(e),y1)),
              gmul(x1,gadd(gmul2n(ell_get_a2(e),1),gmulsg(3,x1))));
  }
  else {
    p1 = gsub(y2,y1);
    p2 = gsub(x2,x1);
  }
  p1 = gdiv(p1,p2);
  x = gsub(gmul(p1,gadd(p1,ell_get_a1(e))), gadd(gadd(x1,x2),ell_get_a2(e)));
  y = gadd(gadd(y1, ellLHS0(e,x)), gmul(p1,gsub(x,x1)));
  tetpil = avma; p1 = cgetg(3,t_VEC);
  gel(p1,1) = gcopy(x);
  gel(p1,2) = gneg(y); return gerepile(av,tetpil,p1);
}

static GEN
invell(GEN e, GEN z)
{
  GEN t;
  if (ell_is_inf(z)) return z;
  t = cgetg(3,t_VEC);
  gel(t,1) = gel(z,1);
  gel(t,2) = gneg_i(gadd(gel(z,2), ellLHS0(e,gel(z,1))));
  return t;
}

GEN
subell(GEN e, GEN z1, GEN z2)
{
  pari_sp av = avma;
  checkell5(e); checkellpt(z2);
  return gerepileupto(av, addell(e, z1, invell(e,z2)));
}

/* e an ell5, x a scalar */
static GEN
ellordinate_i(GEN e, GEN x, long prec)
{
  long td;
  pari_sp av = avma;
  GEN D, a, b, d, y;

  a = ellRHS(e,x);
  b = ellLHS0(e,x); /* y*(y+b) = a */
  D = gadd(gsqr(b), gmul2n(a,2));
  td = typ(D);
  if (td == t_INTMOD && equaliu(gel(D,1), 2))
  { /* curve over F_2 */
    avma = av;
    if (!signe(D[2])) {
      y = cgetg(2,t_VEC);
      gel(y,1) = mkintmodu(gequal0(a)?0:1, 2);
    } else {
      if (!gequal0(a)) return cgetg(1,t_VEC);
      y = cgetg(3,t_VEC);
      gel(y,1) = mkintmodu(0,2);
      gel(y,2) = mkintmodu(1,2);
    }
    return y;
  }
  if (td == t_FFELT && equaliu(FF_p_i(D),2))
  {
    GEN F = FFX_roots(mkpoln(3, gen_1, b, gneg(a)), D);
    if (lg(F) == 1) { avma = av; return cgetg(1,t_VEC); }
    return gerepileupto(av, F);
  }

  if (gequal0(D)) {
    b = gneg_i(b);
    y = cgetg(2,t_VEC);
    gel(y,1) = gmul2n(b,-1);
    return gerepileupto(av,y);
  }
  switch(td)
  {
    case t_INT:
      if (!Z_issquareall(D,&d)) { avma = av; return cgetg(1,t_VEC); }
      break;
    case t_FRAC:
      if (gissquareall(D,&d) == gen_0) { avma = av; return cgetg(1,t_VEC); }
      break;
    case t_FFELT:
      if (!FF_issquareall(D,&d)) { avma = av; return cgetg(1,t_VEC); }
      break;
    case t_INTMOD:
      if (kronecker(gel(D,2),gel(D,1)) < 0) {
        avma = av; return cgetg(1,t_VEC);
      } /* fall through */
    default:
      d = gsqrt(D,prec);
  }
  a = gsub(d,b); y = cgetg(3,t_VEC);
  gel(y,1) = gmul2n(a, -1);
  gel(y,2) = gsub(gel(y,1),d);
  return gerepileupto(av,y);
}

GEN
ellordinate(GEN e, GEN x, long prec)
{
  checkell5(e);
  if (is_matvec_t(typ(x)))
  {
    long i, lx;
    GEN v = cgetg_copy(x, &lx);
    for (i=1; i<lx; i++) gel(v,i) = ellordinate(e,gel(x,i),prec);
    return v;
  }
  return ellordinate_i(e, x, prec);
}

GEN
ellrandom(GEN e)
{
  GEN x, y, j;
  pari_sp av = avma;
  checksmallell(e);
  j = ell_get_j(e);
  switch(typ(j))
  {
    case t_INTMOD:
    case t_FFELT:
      for (;; avma = av)
      {
        x = genrand(j);
        y = ellordinate_i(e, x, 0);
        if (lg(y) > 1) break;
      }
      return gerepilecopy(av, mkvec2(x, gel(y,1)));
    default:
      pari_err_IMPL("random point on elliptic curve over an infinite field");
  }
  return NULL; /* not reached */
}

/* n t_QUAD or t_COMPLEX, z != [0] */
static GEN
ellpow_CM(GEN e, GEN z, GEN n)
{
  GEN p1p, q1p, x, y, p0, p1, q0, q1, z1, z2, grdx, b2ov12, N = gnorm(n);
  long ln, ep, vn;

  if (typ(N) != t_INT)
    pari_err_TYPE("powell (non integral CM exponent)",N);
  ln = itos_or_0(shifti(addsi(1, N), 3));
  if (!ln) pari_err_OVERFLOW("ellpow_CM [norm too large]");
  vn = ((ln>>1)-4)>>2;
  z1 = ellwpseries(e, 0, ln);
  z2 = gsubst(z1, 0, monomial(n, 1, 0));
  p0 = gen_0; p1 = gen_1;
  q0 = gen_1; q1 = gen_0;
  do
  {
    GEN p2,q2, ss = gen_0;
    do
    {
      ep = (-valp(z2)) >> 1;
      ss = gadd(ss, gmul(gel(z2,2), monomial(gen_1, ep, 0)));
      z2 = gsub(z2, gmul(gel(z2,2), gpowgs(z1, ep)));
    }
    while (valp(z2) <= 0);
    p2 = gadd(p0, gmul(ss,p1)); p0 = p1; p1 = p2;
    q2 = gadd(q0, gmul(ss,q1)); q0 = q1; q1 = q2;
    if (!signe(z2)) break;
    z2 = ginv(z2);
  }
  while (degpol(p1) < vn);
  if (degpol(p1) > vn || signe(z2))
    pari_err_TYPE("powell [not a complex multiplication]", n);
  q1p = RgX_deriv(q1);
  b2ov12 = gdivgs(ell_get_b2(e), 12); /* x - b2/12 */
  grdx = gadd(gel(z,1), b2ov12);
  q1 = poleval(q1, grdx);
  if (gequal0(q1)) return ellinf();

  p1p = RgX_deriv(p1);
  p1 = poleval(p1, grdx);
  p1p = poleval(p1p, grdx);
  q1p = poleval(q1p, grdx);

  x = gdiv(p1,q1);
  y = gdiv(gsub(gmul(p1p,q1), gmul(p1,q1p)), gmul(n,gsqr(q1)));
  x = gsub(x, b2ov12);
  y = gsub( gmul(d_ellLHS(e,z), y), ellLHS0(e,x));
  return mkvec2(x, gmul2n(y,-1));
}

static GEN
_sqr(void *e, GEN x) { return addell((GEN)e, x, x); }
static GEN
_mul(void *e, GEN x, GEN y) { return addell((GEN)e, x, y); }

/* [n] z, n integral */
static GEN
ellpow_Z(GEN e, GEN z, GEN n)
{
  long s;

  if (ell_is_inf(z)) return ellinf();
  s = signe(n);
  if (!s) return ellinf();
  if (s < 0) z = invell(e,z);
  if (is_pm1(n)) return z;
  return gen_pow(z, n, (void*)e, &_sqr, &_mul);
}

/* x a t_REAL, try to round it to an integer */
enum { OK, LOW_PREC, NO };
static long
myroundr(GEN *px)
{
  GEN x = *px;
  long e;
  if (bit_prec(x) - expo(x) < 5) return LOW_PREC;
  *px = grndtoi(x, &e);
  if (e >= -5) return NO;
  return OK;
}

/* E has CM by Q, t_COMPLEX or t_QUAD. Return q such that E has CM by Q/q
 * or gen_1 (couldn't find q > 1)
 * or NULL (doesn't have CM by Q) */
static GEN
CM_factor(GEN E, GEN Q)
{
  GEN w1, w2, tau, D, v, x, y, F, dF, q, r, fk, fkb, fkc;
  long prec;

  if (!ell_is_real(E)) return gen_1;
  switch(typ(Q))
  {
    case t_COMPLEX:
      D = utoineg(4);
      v = gel(Q,2);
      break;
    case t_QUAD:
      D = quad_disc(Q);
      v = gel(Q,3);
      break;
    default:
      return NULL; /*-Wall*/
  }
  /* disc Q = v^2 D, D < 0 fundamental */
  w1 = gel(E,15);
  w2 = gel(E,16);
  tau = gdiv(w2, w1);
  prec = precision(tau);
  /* disc tau = -4 k^2 (Im tau)^2 for some integral k
   * Assuming that E has CM by Q, then disc Q / disc tau = f^2 is a square.
   * Compute f*k */
  x = gel(tau,1);
  y = gel(tau,2); /* tau = x + Iy */
  fk = gmul(gdiv(v, gmul2n(y, 1)), sqrtr_abs(itor(D, prec)));
  switch(myroundr(&fk))
  {
    case NO: return NULL;
    case LOW_PREC: return gen_1;
  }
  fk = absi(fk);

  fkb = gmul(fk, gmul2n(x,1));
  switch(myroundr(&fkb))
  {
    case NO: return NULL;
    case LOW_PREC: return gen_1;
  }

  fkc = gmul(fk, cxnorm(tau));
  switch(myroundr(&fkc))
  {
    case NO: return NULL;
    case LOW_PREC: return gen_1;
  }

  /* tau is a root of fk (X^2 - b X + c) \in Z[X],  */
  F = Q_primpart(mkvec3(fk, fkb, fkc));
  dF = qfb_disc(F); /* = disc tau, E has CM by orders of disc dF q^2, all q */
  q = dvmdii(dF, D, &r);
  if (r != gen_0 || !Z_issquareall(q, &q)) return NULL;
  /* disc(Q) = disc(tau) (v / q)^2 */
  v = dvmdii(absi(v), q, &r);
  if (r != gen_0) return NULL;
  return is_pm1(v)? gen_1: v; /* E has CM by Q/q: [Q] = [q] o [Q/q] */
}

/* [a + w] z, a integral, w pure imaginary */
static GEN
ellpow_CM_aux(GEN e, GEN z, GEN a, GEN w)
{
  GEN A, B, q;
  if (typ(a) != t_INT) pari_err_TYPE("ellpow_Z",a);
  q = CM_factor(e, w);
  if (!q) pari_err_TYPE("powell [not a complex multiplication]",w);
  if (q != gen_1) w = gdiv(w, q);
  /* compute [a + q w] z, z has CM by w */
  if (typ(w) == t_QUAD && is_pm1(gel(gel(w,1), 3)))
  { /* replace w by w - u, u in Z, so that N(w-u) is minimal
     * N(w - u) = N w - Tr w u + u^2, minimal for u = Tr w / 2 */
    GEN u = gtrace(w);
    if (typ(u) != t_INT) pari_err_TYPE("ellpow_CM",w);
    u = shifti(u, -1);
    if (signe(u))
    {
      w = gsub(w, u);
      a = addii(a, mulii(q,u));
    }
    /* [a + w]z = [(a + qu)] z + [q] [(w - u)] z */
  }
  A = ellpow_Z(e,z,a);
  B = ellpow_CM(e,z,w);
  if (q != gen_1) B = ellpow_Z(e, B, q);
  return addell(e, A, B);
}
GEN
powell(GEN e, GEN z, GEN n)
{
  pari_sp av = avma;

  checkell5(e); checkellpt(z);
  if (ell_is_inf(z)) return ellinf();
  switch(typ(n))
  {
    case t_INT: return gerepilecopy(av, ellpow_Z(e,z,n));
    case t_QUAD: {
      GEN pol = gel(n,1), a = gel(n,2), b = gel(n,3);
      if (signe(pol[2]) < 0) pari_err_TYPE("ellpow_CM",n); /* disc > 0 ? */
      return gerepileupto(av, ellpow_CM_aux(e,z,a,mkquad(pol, gen_0,b)));
    }
    case t_COMPLEX: {
      GEN a = gel(n,1), b = gel(n,2);
      return gerepileupto(av, ellpow_CM_aux(e,z,a,mkcomplex(gen_0,b)));
    }
  }
  pari_err_TYPE("powell (non integral, non CM exponent)",n);
  return NULL; /* not reached */
}

/********************************************************************/
/**                                                                **/
/**                       ELLIPTIC FUNCTIONS                       **/
/**                                                                **/
/********************************************************************/
static GEN
quot(GEN x, GEN y)
{
  GEN z = mpdiv(x, y), q = floorr(z);
  if (gsigne(y) < 0 && !gequal(z, q)) q = addis(q, 1);
  return q;
}
GEN
zell(GEN e, GEN z, long prec)
{
  long ty, sw, fl;
  pari_sp av = avma;
  GEN t, u, p1, p2, a, b, x1, u2, D;

  checkell(e); checkellpt(z);
  D = ell_get_disc(e);
  ty = typ(D); if (ty == t_INTMOD) pari_err_TYPE("zell",D);
  if (ell_is_inf(z)) return (ty==t_PADIC)? gen_1: gen_0;

  x1 = new_coords(e,gel(z,1),ell_realroot(e), &a,&b,1, prec);
  if (ty==t_PADIC)
  {
    u2 = do_padic_agm(&x1,a,b,gel(D,2));
    if (!gequal0(gel(e,16)))
    {
      t = Qp_sqrt(gaddsg(1, gdiv(x1,a)));
      t = gdiv(gaddsg(-1,t), gaddsg(1,t));
    }
    else t = gaddsg(2, ginv(gmul(u2,x1)));
    return gerepileupto(av,t);
  }

  sw = gsigne(real_i(b)); fl=0;
  for(;;) /* ~ agm */
  {
    GEN a0 = a, b0 = b, x0 = x1, d;

    b = gsqrt(gmul(a0,b0),prec);
    if (gsigne(real_i(b)) != sw) b = gneg_i(b);
    a = gmul2n(gadd(gadd(a0,b0),gmul2n(b,1)),-2);
    d = gsub(a,b);
    if (gequal0(d) || gexpo(d) < gexpo(a) - prec2nbits(prec) + 5) break;
    p1 = gsqrt(gdiv(gadd(x0,d),x0),prec);
    x1 = gmul(x0,gsqr(gmul2n(gaddsg(1,p1),-1)));
    d = gsub(x1,x0);
    if (gequal0(d) || gexpo(d) < gexpo(x1) - prec2nbits(prec) + 5)
    {
      if (fl) break;
      fl = 1;
    }
    else fl = 0;
  }
  u = gdiv(x1,a); t = gaddsg(1,u);
  if (gequal0(t) || gexpo(t) <  5 - prec2nbits(prec))
    t = gen_m1;
  else
    t = gdiv(u,gsqr(gaddsg(1,gsqrt(t,prec))));
  u = gsqrt(ginv(gmul2n(a,2)),prec);
  t = gmul(u, glog(t,prec));

  /* which square root? test the reciprocal function (pointell) */
  if (!gequal0(t))
  {
    GEN z1, z2;
    int bad;

    z1 = pointell(e,gprec_w(t,LOWDEFAULTPREC),LOWDEFAULTPREC); /* we don't need much precision */
    if (ell_is_inf(z1)) pari_err_PREC( "ellpointtoz");
    /* Either z = z1 (ok: keep t), or z = z2 (bad: t <-- -t) */
    z2 = invell(e, z1);
    bad = (gexpo(gsub(z,z1)) > gexpo(gsub(z,z2)));
    if (bad) t = gneg(t);
    if (DEBUGLEVEL) {
      if (DEBUGLEVEL>4) {
        err_printf("  z  = %Ps\n",z);
        err_printf("  z1 = %Ps\n",z1);
        err_printf("  z2 = %Ps\n",z2);
      }
      err_printf("ellpointtoz: %s square root\n", bad? "bad": "good");
      err_flush();
    }
  }
  /* send t to the fundamental domain if necessary */
  p2 = quot(imag_i(t), imag_i(gel(e,16)));
  if (signe(p2)) t = gsub(t, gmul(p2, gel(e,16)));
  p2 = quot(real_i(t), gel(e,15));
  if (signe(p2)) t = gsub(t, gmul(p2, gel(e,15)));
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
set_gamma(GEN t, GEN *pa, GEN *pb, GEN *pc, GEN *pd)
{
  GEN a, b, c, d, run = dbltor(1. - 1e-8);
  pari_sp av = avma, lim = stack_lim(av, 1);

  a = d = gen_1;
  b = c = gen_0;
  for(;;)
  {
    GEN m, n = ground(real_i(t));
    if (signe(n))
    { /* apply T^n */
      t = gsub(t,n);
      a = subii(a, mulii(n,c));
      b = subii(b, mulii(n,d));
    }
    m = cxnorm(t); if (gcmp(m,run) > 0) break;
    t = gneg_i(gdiv(gconj(t), m)); /* apply S */
    togglesign_safe(&c); swap(a,c);
    togglesign_safe(&d); swap(b,d);
    if (low_stack(lim, stack_lim(av, 1))) {
      if (DEBUGMEM>1) pari_warn(warnmem, "redimagsl2");
      gerepileall(av, 5, &t, &a,&b,&c,&d);
    }
  }
  *pa = a;
  *pb = b;
  *pc = c;
  *pd = d;
}
/* Im t > 0. Return U.t in PSl2(Z)'s standard fundamental domain.
 * Set *pU to U. */
GEN
redtausl2(GEN t, GEN *pU)
{
  pari_sp av = avma;
  GEN U, a,b,c,d;
  set_gamma(t, &a, &b, &c, &d);
  U = mkmat2(mkcol2(a,c), mkcol2(b,d));
  t = gdiv(gadd(gmul(a,t), b),
           gadd(gmul(c,t), d));
  gerepileall(av, 2, &t, &U);
  *pU = U; return t;
}

/* swap w1, w2 so that Im(t := w1/w2) > 0. Set tau = representative of t in
 * the standard fundamental domain, and g in Sl_2, such that tau = g.t */
static void
red_modSL2(SL2_red *T)
{
  long s;
  T->tau = gdiv(T->w1,T->w2);
  s = gsigne(imag_i(T->tau));
  if (!s) pari_err(e_MISC,"w1 and w2 R-linearly dependent in elliptic function");
  T->swap = (s < 0);
  if (T->swap) { swap(T->w1, T->w2); T->tau = ginv(T->tau); }
  set_gamma(T->tau, &T->a, &T->b, &T->c, &T->d);
  /* update lattice */
  T->W1 = gadd(gmul(T->a,T->w1), gmul(T->b,T->w2));
  T->W2 = gadd(gmul(T->c,T->w1), gmul(T->d,T->w2));
  T->Tau = gdiv(T->W1, T->W2);
}
static GEN
reduce_z(GEN z, SL2_red *T)
{
  GEN Z = gdiv(z, T->W2);
  long t = typ(z), pr;

  if (!is_scalar_t(t) || t == t_INTMOD || t == t_PADIC || t == t_POLMOD)
    pari_err_TYPE("reduction mod SL2 (reduce_z)", z);
  T->x = ground(gdiv(imag_i(Z), imag_i(T->Tau)));
  Z = gsub(Z, gmul(T->x,T->Tau));
  T->y = ground(real_i(Z));
  Z = gsub(Z, T->y);
  pr = gprecision(Z);
  if (gequal0(Z) || (pr && gexpo(Z) < 5 - prec2nbits(pr))) Z = NULL; /*z in L*/
  return Z;
}

static int
get_periods(GEN e, SL2_red *T)
{
  long tx = typ(e);
  if (is_vec_t(tx))
    switch(lg(e))
    {
      case  3: T->w1 = ell_get_a1(e);  T->w2 = ell_get_a2(e); red_modSL2(T); return 1;
      case 20: T->w1 = gel(e,15); T->w2 = gel(e,16);red_modSL2(T); return 1;
    }
  return 0;
}
static void
check_periods(GEN w)
{
  SL2_red T;
  if (lg(w) > 3) checksmallell(w);
  if (!get_periods(w, &T)) pari_err_TYPE("check_periods",w);
}

/* 2iPi/x, more efficient when x pure imaginary */
static GEN
PiI2div(GEN x, long prec) { return gdiv(Pi2n(1, prec), mulcxmI(x)); }
/* exp(I x y), more efficient for x in R, y pure imaginary */
static GEN
expIxy(GEN x, GEN y, long prec) { return gexp(gmul(x, mulcxI(y)), prec); }

static GEN
check_real(GEN q)
{ return (typ(q) == t_COMPLEX && gequal0(gel(q,2)))? gel(q,1): q; }

/* Return E_k(tau). Slow if tau is not in standard fundamental domain */
static GEN
trueE(GEN tau, long k, long prec)
{
  pari_sp lim, av;
  GEN p1, q, y, qn;
  long n = 1;

  q = expIxy(Pi2n(1, prec), tau, prec);
  q = check_real(q);
  y = gen_0;
  av = avma; lim = stack_lim(av,2); qn = gen_1;
  for(;; n++)
  { /* compute y := sum_{n>0} n^(k-1) q^n / (1-q^n) */
    qn = gmul(q,qn);
    p1 = gdiv(gmul(powuu(n,k-1),qn), gsubsg(1,qn));
    if (gequal0(p1) || gexpo(p1) <= - prec2nbits(prec) - 5) break;
    y = gadd(y, p1);
    if (low_stack(lim, stack_lim(av,2)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"elleisnum");
      gerepileall(av, 2, &y,&qn);
    }
  }
  return gadd(gen_1, gmul(y, gdiv(gen_2, szeta(1-k, prec))));
}

/* (2iPi/W2)^k E_k(W1/W2) */
static GEN
_elleisnum(SL2_red *T, long k, long prec)
{
  GEN y = trueE(T->Tau, k, prec);
  y = gmul(y, gpowgs(mulcxI(gdiv(Pi2n(1,prec), T->W2)),k));
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

  if (k&1 || k<=0) pari_err_TYPE("elleisnum [k not positive even]",stoi(k));
  if (!get_periods(om, &T)) pari_err_TYPE("elleisnum",om);
  y = _elleisnum(&T, k, prec);
  if (k==2 && signe(T.c))
  {
    p1 = gmul(Pi2n(1,prec), mului(12, T.c));
    y = gsub(y, mulcxI(gdiv(p1, gmul(T.w2, T.W2))));
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
  y1 = gadd(PiI2div(T->W2, prec), gmul(T->W1,e2));
  y = cgetg(3,t_VEC);
  gel(y,1) = gneg(y1);
  gel(y,2) = gneg(y2); return y;
}

/* compute eta1, eta2 */
GEN
elleta(GEN om, long prec)
{
  pari_sp av = avma;
  GEN y1, y2, E2, pi;
  SL2_red T;

  if (typ(om) == t_VEC && lg(om) == 20)
    return mkvec2copy(gel(om,17), gel(om,18));

  if (!get_periods(om, &T)) pari_err_TYPE("elleta",om);
  pi = mppi(prec);
  E2 = trueE(T.Tau, 2, prec); /* E_2(Tau) */
  if (signe(T.c))
  {
    GEN u = gdiv(T.w2, T.W2);
    /* E2 := u^2 E2 + 6iuc/pi = E_2(tau) */
    E2 = gadd(gmul(gsqr(u), E2), mulcxI(gdiv(gmul(mului(6,T.c), u), pi)));
  }
  y2 = gdiv(gmul(E2, sqrr(pi)), gmulsg(3, T.w2));
  if (T.swap)
  {
    y1 = y2;
    y2 = gadd(gmul(T.tau,y1), PiI2div(T.w2, prec));
  }
  else
    y1 = gsub(gmul(T.tau,y2), PiI2div(T.w2, prec));
  return gerepilecopy(av, mkvec2(y1,y2));
}

/* computes the numerical value of wp(z | L), L = om1 Z + om2 Z
 * return NULL if z in L.  If flall=1, compute also wp' */
static GEN
ellwpnum_all(SL2_red *T, GEN z, long flall, long prec0)
{
  long toadd, prec;
  pari_sp av=avma, lim, av1;
  GEN p1, pi2, q, u, y, yp, u1, u2, qn, v;

  z = reduce_z(z, T);
  if (!z) return NULL;
  prec = precision(z);
  if (!prec) { prec = precision(T->tau); if (!prec) prec = prec0; }

  /* Now L,z normalized to <1,tau>. z in fund. domain of <1, tau> */
  pi2 = Pi2n(1, prec);
  q = expIxy(pi2, T->Tau, prec);
  u = expIxy(pi2, z, prec);
  u1= gsubsg(1,u); u2 = gsqr(u1);
  y = gadd(mkfrac(gen_1, utoipos(12)), gdiv(u,u2));
  if (flall) yp = gdiv(gadd(gen_1,u), gmul(u1,u2));
  toadd = (long)ceil(9.065*gtodouble(imag_i(z)));

  av1 = avma; lim = stack_lim(av1,1); qn = q;
  for(;;)
  {
    GEN qnu,qnu1,qnu2,qnu3,qnu4;

    qnu = gmul(qn,u);     /* q^n u */
    qnu1 = gsubsg(1,qnu); /* 1 - q^n u */
    qnu2 = gsqr(qnu1);    /* (1 - q^n u)^2 */
    qnu3 = gsub(qn,u);    /* q^n - u */
    qnu4 = gsqr(qnu3);    /* (q^n - u)^2 */
    p1 = gsub(gmul(u, gadd(ginv(qnu2),ginv(qnu4))),
              gmul2n(ginv(gsqr(gsubsg(1,qn))), 1));
    y = gadd(y, gmul(qn,p1));
    if (flall)
    {
      p1 = gadd(gdiv(gadd(gen_1,qnu),gmul(qnu1,qnu2)),
                gdiv(gadd(qn,u),gmul(qnu3,qnu4)));

      yp = gadd(yp, gmul(qn,p1));
    }
    qn = gmul(q,qn);
    if (gexpo(qn) <= - prec2nbits(prec) - 5 - toadd) break;
    if (low_stack(lim, stack_lim(av1,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"ellwpnum_all");
      gerepileall(av1, flall? 3: 2, &y, &qn, &yp);
    }
  }

  u1 = gdiv(pi2, mulcxmI(T->W2));
  u2 = gsqr(u1);
  y = gmul(u2,y); /* y *= (2i pi / w2)^2 */
  if (flall)
  {
    yp = gmul(u, gmul(gmul(u1,u2),yp));/* yp *= u (2i pi / w2)^3 */
    v = mkvec2(y, gmul2n(yp,-1));
  }
  else v = y;
  return gerepilecopy(av, v);
}
static GEN
ellwpseries_aux(GEN c4, GEN c6, long v, long PRECDL)
{
  long i, k, l;
  pari_sp av;
  GEN t, res = cgetg(PRECDL+2,t_SER), *P = (GEN*)(res + 2);

  res[1] = evalsigne(1) | _evalvalp(-2) | evalvarn(v);
  if (!PRECDL) { setsigne(res,0); return res; }

  for (i=1; i<PRECDL; i+=2) P[i]= gen_0;
  switch(PRECDL)
  {
    default:P[6] = gdivgs(c6,6048);
    case 6:
    case 5: P[4] = gdivgs(c4, 240);
    case 4:
    case 3: P[2] = gen_0;
    case 2:
    case 1: P[0] = gen_1;
    case 0: break;
  }
  if (PRECDL <= 8) return res;
  av = avma;
  P[8] = gerepileupto(av, gdivgs(gsqr(P[4]), 3));
  for (k=5; (k<<1) < PRECDL; k++)
  {
    av = avma;
    t = gmul(P[4], P[(k-2)<<1]);
    for (l=3; (l<<1) < k; l++) t = gadd(t, gmul(P[l<<1], P[(k-l)<<1]));
    t = gmul2n(t, 1);
    if ((k & 1) == 0) t = gadd(gsqr(P[k]), t);
    if (k % 3 == 2)
      t = gdivgs(gmulsg(3, t), (k-3)*(2*k+1));
    else /* same value, more efficient */
      t = gdivgs(t, ((k-3)*(2*k+1)) / 3);
    P[k<<1] = gerepileupto(av, t);
  }
  return res;
}

GEN
ellwpseries(GEN e, long v, long PRECDL)
{
  GEN c4, c6;
  checksmallell(e);
  c4 = ell_get_c4(e);
  c6 = ell_get_c6(e); return ellwpseries_aux(c4,c6,v,PRECDL);
}

static GEN
ellwpseries0(GEN e, long v, long PRECDL, long prec)
{
  GEN c4,c6;

  if (lg(e) > 3) return ellwpseries(e, v, PRECDL);
  c4 = elleisnum(e, 4, 0, prec);
  c6 = elleisnum(e, 6, 0, prec); c6 = gneg(c6);
  return ellwpseries_aux(c4,c6,v,PRECDL);
}

GEN
ellwp(GEN w, GEN z, long prec)
{ return ellwp0(w,z,0,prec); }

GEN
ellwp0(GEN w, GEN z, long flag, long prec)
{
  GEN y;
  pari_sp av = avma;
  SL2_red T;

  if (flag && flag != 1) pari_err_FLAG("ellwp");
  if (!z) z = pol_x(0);
  y = toser_i(z);
  if (y)
  {
    long vy = varn(y), v = valp(y);
    GEN P, Q;
    if (v <= 0) pari_err(e_IMPL,"ellwp(t_SER) away from 0");
    if (gequal0(y)) {
      check_periods(w); avma = av;
      if (!flag) return zeroser(vy, -2*v);
      retmkvec2(zeroser(vy, -2*v), zeroser(vy, -3*v));
    }
    P = ellwpseries0(w, vy, lg(y)-2, prec);
    Q = gsubst(P, varn(P), y);
    if (!flag)
      return gerepileupto(av, Q);
    else
    {
      GEN R = mkvec2(Q, gdiv(derivser(Q), derivser(y)));
      return gerepilecopy(av, R);
    }
  }
  if (!get_periods(w, &T)) pari_err_TYPE("ellwp",w);
  y = ellwpnum_all(&T,z,flag,prec);
  if (!y) pari_err(e_MISC, "argument in lattice in ellwp");
  return gerepileupto(av, y);
}

GEN
ellzeta(GEN w, GEN z, long prec0)
{
  long toadd, prec;
  pari_sp av = avma, lim, av1;
  GEN Z, pi2, q, u, y, qn, et = NULL;
  SL2_red T;

  if (!z) z = pol_x(0);
  y = toser_i(z);
  if (y)
  {
    long vy = varn(y), v = valp(y);
    GEN P, Q;
    if (v <= 0) pari_err(e_IMPL,"ellzeta(t_SER) away from 0");
    if (gequal0(y)) { check_periods(w); avma = av; return zeroser(vy, -v); }
    P = ellwpseries0(w, vy, lg(y)-2, prec0);
    P = integ(gneg(P), vy); /* \zeta' = - \wp*/
    Q = gsubst(P, varn(P), y);
    return gerepileupto(av, Q);
  }
  if (!get_periods(w, &T)) pari_err_TYPE("ellzeta", w);
  Z = reduce_z(z, &T);
  if (!Z) pari_err(e_MISC,"can't evaluate ellzeta at a pole");
  prec = precision(Z);
  if (!prec) { prec = precision(T.tau); if (!prec) prec = prec0; }
  if (!gequal0(T.x) || !gequal0(T.y))
  {
    et = _elleta(&T,prec);
    et = gadd(gmul(T.x,gel(et,1)), gmul(T.y,gel(et,2)));
  }

  pi2 = Pi2n(1, prec);
  q = expIxy(pi2, T.Tau, prec);
  u = expIxy(pi2, Z, prec);

  y = mulcxmI(gdiv(gmul(gsqr(T.W2),_elleisnum(&T,2,prec)), pi2));
  y = gadd(ghalf, gdivgs(gmul(Z,y),-12));
  y = gadd(y, ginv(gsubgs(u, 1)));
  toadd = (long)ceil(9.065*gtodouble(imag_i(Z)));
  av1 = avma; lim = stack_lim(av1,1);

  /* y += sum q^n ( u/(u*q^n - 1) + 1/(u - q^n) ) */
  for (qn = q;;)
  {
    GEN p1 = gadd(gdiv(u,gsubgs(gmul(qn,u),1)), ginv(gsub(u,qn)));
    y = gadd(y, gmul(qn,p1));
    qn = gmul(q,qn);
    if (gexpo(qn) <= - prec2nbits(prec) - 5 - toadd) break;
    if (low_stack(lim, stack_lim(av1,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"ellzeta");
      gerepileall(av1,2, &y,&qn);
    }
  }
  y = mulcxI(gmul(gdiv(pi2,T.W2), y));
  return et? gerepileupto(av, gadd(y,et)): gerepilecopy(av, y);
}

/* if flag=0, return ellsigma, otherwise return log(ellsigma) */
GEN
ellsigma(GEN w, GEN z, long flag, long prec0)
{
  long toadd, prec;
  pari_sp av = avma, lim, av1;
  GEN Z, zinit, p1, pi, pi2, q, u, y, y1, u1, qn, uinv, et, etnew, uhalf;
  int doprod = (flag >= 2), dolog = (flag & 1);
  SL2_red T;

  if (!z) z = pol_x(0);
  y = toser_i(z);
  if (y)
  {
    long vy = varn(y), v = valp(y);
    GEN P, Q;
    if (v <= 0) pari_err(e_IMPL,"ellsigma(t_SER) away from 0");
    if (dolog) pari_err(e_MISC,"can't compute log(ellsigma(t_SER))");
    if (gequal0(y)) { check_periods(w); avma = av; return zeroser(vy, -v); }
    P = ellwpseries0(w, vy, lg(y)-2, prec0);
    P = integ(gneg(P), vy); /* \zeta' = - \wp*/
    /* (log \sigma)' = \zeta; remove log-singularity first */
    P = integ(gsub(P, monomial(gen_1,-1,vy)), vy);
    P = gexp(P, prec0);
    setvalp(P, valp(P)+1);
    Q = gsubst(P, varn(P), y);
    return gerepileupto(av, Q);
  }
  if (!get_periods(w, &T)) pari_err_TYPE("ellsigma",w);
  Z = reduce_z(z, &T);
  if (!Z)
  {
    if (!dolog) return gen_0;
    pari_err(e_MISC,"can't evaluate log(ellsigma) at lattice point");
  }
  prec = precision(Z);
  if (!prec) { prec = precision(T.tau); if (!prec) prec = prec0; }
  et = _elleta(&T, prec);
  etnew = gadd(gmul(T.x,gel(et,1)), gmul(T.y,gel(et,2)));

  pi2 = Pi2n(1,prec);
  pi  = mppi(prec);
  zinit = gmul(Z,T.W2);
  p1 = gadd(zinit, gmul2n(gadd(gmul(T.x,T.W1), gmul(T.y,T.W2)),-1));
  etnew = gmul(etnew, p1);
  if (mpodd(T.x) || mpodd(T.y)) etnew = gadd(etnew, mulcxI(pi));

  y1 = gadd(etnew, gmul2n(gmul(gmul(Z,zinit),gel(et,2)),-1));

  toadd = (long)ceil((2*PI/LOG2) * fabs(gtodouble(imag_i(Z))));
  uhalf = expIxy(pi, Z, prec); /* exp(i Pi Z) */
  u = gsqr(uhalf);
  if (doprod) { /* use product */
    q = expIxy(pi2, T.Tau, prec);
    uinv = ginv(u);
    u1 = gsub(uhalf,ginv(uhalf));
    y = mulcxmI(gdiv(gmul(T.W2,u1), pi2));
    av1 = avma; lim = stack_lim(av1,1); qn=q;
    for(;;)
    {
      p1 = gmul(gadd(gmul(qn,u),gen_m1),gadd(gmul(qn,uinv),gen_m1));
      p1 = gdiv(p1,gsqr(gadd(qn,gen_m1)));
      y = gmul(y,p1);
      qn = gmul(q,qn);
      if (gexpo(qn) <= - prec2nbits(prec) - 5 - toadd) break;
      if (low_stack(lim, stack_lim(av1,1)))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"ellsigma");
        gerepileall(av1,2, &y,&qn);
      }
    }
  } else { /* use sum */
    GEN q8, qn2, urn, urninv;
    long n;
    q8 = expIxy(gmul2n(pi2,-3), T.Tau, prec);
    q = gpowgs(q8,8);
    u = gneg_i(u); uinv = ginv(u);
    y = gen_0;
    av1 = avma; lim = stack_lim(av1,1);
    qn = q; qn2 = gen_1;
    urn = uhalf; urninv = ginv(uhalf);
    for(n=0;;n++)
    {
      y = gadd(y,gmul(qn2,gsub(urn,urninv)));
      qn2 = gmul(qn,qn2);
      qn  = gmul(q,qn);
      urn = gmul(urn,u);
      urninv = gmul(urninv,uinv);
      if (gexpo(qn2) + n*toadd <= - prec2nbits(prec) - 5) break;
      if (low_stack(lim, stack_lim(av1,1)))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"ellsigma");
        gerepileall(av1,5, &y,&qn,&qn2,&urn,&urninv);
      }
    }
    p1 = gmul(gmul(y,q8),
              gdiv(mulcxmI(T.W2), gmul(pi2,gpowgs(trueeta(T.Tau,prec),3))));
  }
  y1 = dolog? gadd(y1, glog(p1,prec)): gmul(p1, gexp(y1,prec));
  return gerepileupto(av, y1);
}

GEN
pointell(GEN e, GEN z, long prec)
{
  pari_sp av = avma;
  GEN v;
  SL2_red T;

  checkell_real(e); (void)get_periods(e, &T);
  v = ellwpnum_all(&T,z,1,prec);
  if (!v) { avma = av; return ellinf(); }
  gel(v,1) = gsub(gel(v,1), gdivgs(ell_get_b2(e),12));
  gel(v,2) = gsub(gel(v,2), gmul2n(ellLHS0(e,gel(v,1)),-1));
  return gerepilecopy(av, v);
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
  page 46, the "long" algorithm is used for p = 2,3 only. */
static GEN
localred_result(long f, long kod, long c, GEN v)
{
  GEN z = cgetg(5, t_VEC);
  gel(z,1) = stoi(f);
  gel(z,2) = stoi(kod);
  gel(z,3) = gcopy(v);
  gel(z,4) = stoi(c); return z;
}
static GEN
localredbug(GEN p, const char *s)
{
  if (BPSW_psp(p)) pari_err_BUG(s);
  pari_err_PRIME("localred",p);
  return NULL; /* not reached */
}

/* Here p > 3. e assumed integral, minim = 1 if we only want a minimal model */
static GEN
localred_p(GEN e, GEN p, int minim)
{
  long k, f, kod, c, nuj, nuD;
  GEN p2, v = init_ch();
  GEN c4, c6, D, tri;

  c4 = ell_get_c4(e);
  c6 = ell_get_c6(e);
  D  = ell_get_disc(e);
  nuj = gequal0(ell_get_j(e))? 0: - Q_pval(ell_get_j(e), p);
  nuD = Z_pval(D, p);
  k = (nuj > 0 ? nuD - nuj : nuD) / 12;
  if (k <= 0)
  {
    if (minim) return v;
  }
  else
  { /* model not minimal */
    GEN pk = powiu(p,k), p2k = sqri(pk), p4k = sqri(p2k), p6k = mulii(p4k,p2k);
    GEN r, s, t;

    s = negi(ell_get_a1(e));
    if (mpodd(s)) s = addii(s, pk);
    s = shifti(s, -1);

    r = subii(ell_get_a2(e), mulii(s, addii(ell_get_a1(e), s))); /* a_2' */
    switch(umodiu(r, 3))
    {
      default: break; /* 0 */
      case 2: r = addii(r, p2k); break;
      case 1: r = subii(r, p2k); break;
    }
    r = negi( diviuexact(r, 3) );

    t = negi(ellLHS0_i(e,r)); /* - a_3' */
    if (mpodd(t)) t = addii(t, mulii(pk, p2k));
    t = shifti(t, -1);

    gel(v,1) = pk;
    gel(v,2) = r;
    gel(v,3) = s;
    gel(v,4) = t;
    if (minim) return v;

    nuD -= 12 * k;
    c4 = diviiexact(c4, p4k);
    c6 = diviiexact(c6, p6k);
    D = diviiexact(D, sqri(p6k));
  }

  if (nuj > 0) switch(nuD - nuj)
  {
    case 0: f = 1; kod = 4+nuj; /* Inu */
      switch(kronecker(negi(c6),p))
      {
        case  1: c = nuD; break;
        case -1: c = odd(nuD)? 1: 2; break;
        default: return localredbug(p,"localred (p | c6)");
      }
      break;
    case 6: f = 2; kod = -4-nuj; /* Inu* */
      if (nuj & 1)
        c = 3 + kronecker(diviiexact(mulii(c6, D),powiu(p, 9+nuj)), p);
      else
        c = 3 + kronecker(diviiexact(D, powiu(p, 6+nuj)), p);
      break;
    default: return localredbug(p,"localred (nu_D - nu_j != 0,6)");
  }
  else switch(nuD)
  {
    case  0: f = 0; kod = 1; c = 1; break; /* I0, regular */
    case  2: f = 2; kod = 2; c = 1; break; /* II   */
    case  3: f = 2; kod = 3; c = 2; break; /* III  */
    case  4: f = 2; kod = 4; /* IV   */
      c = 2 + krosi(-6,p) * kronecker(diviiexact(c6,sqri(p)), p);
      break;
    case  6: f = 2; kod = -1; /* I0*  */
      p2 = sqri(p);
      /* x^3 - 3c4/p^2 x - 2c6/p^3 */
      tri = mkpoln(4, gen_1, gen_0,
                            negi(mului(3, diviiexact(c4, p2))),
                            negi(shifti(diviiexact(c6, mulii(p2,p)), 1)));
      c = 1 + FpX_nbroots(tri, p);
      break;
    case  8: f = 2; kod = -4; /* IV*  */
      c = 2 + krosi(-6,p) * kronecker(diviiexact(c6, sqri(sqri(p))), p);
      break;
    case  9: f = 2; kod = -3; c = 2; break; /* III* */
    case 10: f = 2; kod = -2; c = 1; break; /* II*  */
    default: return localredbug(p,"localred");
  }
  return localred_result(f, kod, c, v);
}

/* return a_{ k,l } in Tate's notation, pl = p^l */
static ulong
aux(GEN ak, ulong q, ulong pl)
{
  return umodiu(ak, q) / pl;
}

static ulong
aux2(GEN ak, ulong p, GEN pl)
{
  pari_sp av = avma;
  ulong res = umodiu(diviiexact(ak, pl), p);
  avma = av; return res;
}

/* number of distinct roots of X^3 + aX^2 + bX + c modulo p = 2 or 3
 * assume a,b,c in {0, 1} [ p = 2] or {0, 1, 2} [ p = 3 ]
 * if there's a multiple root, put it in *mult */
static long
numroots3(long a, long b, long c, long p, long *mult)
{
  if (p == 2)
  {
    if ((c + a * b) & 1) return 3;
    *mult = b; return (a + b) & 1 ? 2 : 1;
  }
  /* p = 3 */
  if (!a) { *mult = -c; return b ? 3 : 1; }
  *mult = a * b;
  if (b == 2)
    return (a + c) == 3 ? 2 : 3;
  else
    return c ? 3 : 2;
}

/* same for aX^2 +bX + c */
static long
numroots2(long a, long b, long c, long p, long *mult)
{
  if (p == 2) { *mult = c; return b & 1 ? 2 : 1; }
  /* p = 3 */
  *mult = a * b; return (b * b - a * c) % 3 ? 2 : 1;
}

/* p = 2 or 3 */
static GEN
localred_23(GEN e, long p)
{
  long c, nu, nuD, r, s, t;
  long theroot, p2, p3, p4, p5, p6, a21, a42, a63, a32, a64;
  GEN v;

  nuD = Z_lval(ell_get_disc(e), (ulong)p);
  v = init_ch();
  if (p == 2) { p2 = 4; p3 = 8;  p4 = 16; p5 = 32; p6 = 64;}
  else        { p2 = 9; p3 = 27; p4 = 81; p5 =243; p6 =729; }

  for (;;)
  {
    if (!nuD) return localred_result(0, 1, 1, v);
        /* I0   */
    if (umodiu(ell_get_b2(e), p)) /* p \nmid b2 */
    {
      if (umodiu(negi(ell_get_c6(e)), p == 2 ? 8 : 3) == 1)
        c = nuD;
      else
        c = 2 - (nuD & 1);
      return localred_result(1, 4 + nuD, c, v);
    }
        /* Inu  */
    if (p == 2)
    {
      r = umodiu(ell_get_a4(e), 2);
      s = umodiu(ell_get_a2(e), 2);
      t = umodiu(ell_get_a6(e), 2);
      if (r) { t = (s + t) & 1; s = (s + 1) & 1; }
    }
    else /* p == 3 */
    {
      r = - umodiu(ell_get_b6(e), 3);
      s = umodiu(ell_get_a1(e), 3);
      t = umodiu(ell_get_a3(e), 3);
      if (s) { t  = (t + r*s) % 3; if (t < 0) t += 3; }
    }
    /* p | (a1, a2, a3, a4, a6) */
    if (r || s || t) cumule(&v, &e, gen_1, stoi(r), stoi(s), stoi(t));
    if (umodiu(ell_get_a6(e), p2))
      return localred_result(nuD, 2, 1, v);
        /* II   */
    if (umodiu(ell_get_b8(e), p3))
      return localred_result(nuD - 1, 3, 2, v);
        /* III  */
    if (umodiu(ell_get_b6(e), p3))
    {
      if (umodiu(ell_get_b6(e), (p==2)? 32: 27) == (ulong)p2)
        c = 3;
      else
        c = 1;
      return localred_result(nuD - 2, 4, c, v);
    }
        /* IV   */

    if (umodiu(ell_get_a6(e), p3))
      cumule(&v, &e, gen_1, gen_0, gen_0, p == 2? gen_2: modis(ell_get_a3(e), 9));
        /* p | a1, a2; p^2  | a3, a4; p^3 | a6 */
    a21 = aux(ell_get_a2(e), p2, p);
    a42 = aux(ell_get_a4(e), p3, p2);
    a63 = aux(ell_get_a6(e), p4, p3);
    switch (numroots3(a21, a42, a63, p, &theroot))
    {
      case 3:
        c = a63 ? 1: 2;
        if (p == 2)
          c += ((a21 + a42 + a63) & 1);
        else {
          if (((1 + a21 + a42 + a63) % 3) == 0) c++;
          if (((1 - a21 + a42 - a63) % 3) == 0) c++;
        }
        return localred_result(nuD - 4, -1, c, v);
      case 2: /* I0*  */
      { /* compute nu */
        GEN pk, pk1, p2k;
        long al, be, ga;
        if (theroot) cumule(&v, &e, gen_1, stoi(theroot * p), gen_0, gen_0);
            /* p | a1; p^2  | a2, a3; p^3 | a4; p^4 | a6 */
        nu = 1;
        pk  = utoipos(p2);
        p2k = utoipos(p4);
        for(;;)
        {
          be =  aux2(ell_get_a3(e), p, pk);
          ga = -aux2(ell_get_a6(e), p, p2k);
          al = 1;
          if (numroots2(al, be, ga, p, &theroot) == 2) break;
          if (theroot) cumule(&v, &e, gen_1, gen_0, gen_0, mulsi(theroot,pk));
          pk1 = pk;
          pk  = mului(p, pk);
          p2k = mului(p, p2k); nu++;

          al = a21;
          be = aux2(ell_get_a4(e), p, pk);
          ga = aux2(ell_get_a6(e), p, p2k);
          if (numroots2(al, be, ga, p, &theroot) == 2) break;
          if (theroot) cumule(&v, &e, gen_1, mulsi(theroot, pk1), gen_0, gen_0);
          p2k = mului(p, p2k); nu++;
        }
        if (p == 2)
          c = 4 - 2 * (ga & 1);
        else
          c = 3 + kross(be * be - al * ga, 3);
        return localred_result(nuD - 4 - nu, -4 - nu, c, v);
      }
      case 1: /* Inu* */
        if (theroot) cumule(&v, &e, gen_1, stoi(theroot*p), gen_0, gen_0);
            /* p | a1; p^2  | a2, a3; p^3 | a4; p^4 | a6 */
        a32 = aux(ell_get_a3(e), p3, p2);
        a64 = aux(ell_get_a6(e), p5, p4);
        if (numroots2(1, a32, -a64, p, &theroot) == 2)
        {
          if (p == 2)
            c = 3 - 2 * a64;
          else
            c = 2 + kross(a32 * a32 + a64, 3);
          return localred_result(nuD - 6, -4, c, v);
        }
            /* IV*  */
        if (theroot) cumule(&v, &e, gen_1, gen_0, gen_0, stoi(theroot*p2));
            /* p | a1; p^2 | a2; p^3 | a3, a4; p^5 | a6 */
        if (umodiu(ell_get_a4(e), p4))
          return localred_result(nuD - 7, -3, 2, v);
            /* III* */

        if (umodiu(ell_get_a6(e), p6))
          return localred_result(nuD - 8, -2, 1, v);
            /* II*  */
        cumule(&v, &e, utoipos(p), gen_0, gen_0, gen_0); /* not minimal */
        nuD -= 12;
    }
  }
}

/* minim = 1 if we only want a minimal model */
static GEN
localred(GEN e, GEN p, int minim)
{
  if (cmpiu(p, 3) > 0) /* p != 2,3 */
    return localred_p(e,p, minim);
  else
  {
    long l = itos(p);
    GEN z;
    if (l < 2) pari_err_PRIME("localred",p);
    z = localred_23(e, l);
    return minim? gel(z,3): z;
  }
}

GEN
elllocalred(GEN e, GEN p)
{
  pari_sp av = avma;
  checksmallell(e);
  if (typ(ell_get_disc(e)) != t_INT)
    pari_err_TYPE("elllocalred [not an integral curve]",e);
  if (typ(p) != t_INT) pari_err_TYPE("elllocalred [prime]",p);
  if (signe(p) <= 0) pari_err_PRIME("elllocalred",p);
  return gerepileupto(av, localred(e, p, 0));
}

static GEN
ellintegralmodel(GEN e)
{
  GEN a = cgetg(6,t_VEC), v, L, u;
  long i, l, k;

  checksmallell(e);
  L = cgetg(1, t_VEC);
  for (i = 1; i < 6; i++)
  {
    GEN c = gel(e,i);
    gel(a,i) = c;
    switch(typ(c))
    {
      case t_INT: break;
      case t_FRAC: /* partial factorization */
        L = shallowconcat(L, gel(Z_factor_limit(gel(c,2), 0),1));
        break;
      default: pari_err_TYPE("ellintegralmodel [not a rational curve]",e);
    }
  }
  /* a = [a1, a2, a3, a4, a6] */
  l = lg(L);
  if (l == 1) return NULL;
  L = ZV_sort_uniq(L);
  l = lg(L);

  u = gen_1;
  for (k = 1; k < l; k++)
  {
    GEN p = gel(L,k);
    long n = 0, m;
    for (i = 1; i < 6; i++)
      if (!gequal0(gel(a,i)))
      {
        long r = (i == 5)? 6: i; /* a5 is missing */
        m = r * n + Q_pval(gel(a,i), p);
        while (m < 0) { n++; m += r; }
      }
    u = mulii(u, powiu(p, n));
  }
  v = init_ch(); gel(v,1) = ginv(u); return v;
}

/* e integral model */
static void
standard_model(GEN e, GEN *pv)
{
  GEN a1 = ell_get_a1(e), a2 = ell_get_a2(e);
  GEN r, t, s = truedivis(a1, -2);
  r = truedivis(addis(subii(a2, mulii(s,addii(s,a1))), 1), -3);
  t = truedivis(ellLHS0_i(e,r), -2);
  cumulev(pv, gen_1, r, s, t);
}

GEN
ellminimalmodel(GEN E, GEN *ptv)
{
  pari_sp av = avma;
  GEN c4, c6, e, v, v0, P;
  long l, k;

  v0 = ellintegralmodel(E);
  e = ell_to_small(E);
  if (v0) e = _coordch(e, v0);
  v = init_ch();
  c4 = ell_get_c4(e);
  c6 = ell_get_c6(e);
  P = gel(Z_factor(gcdii(c4,c6)),1);
  l = lg(P);
  for (k = 1; k < l; k++)
  {
    GEN w = localred(e, gel(P,k), 1);
    if (!gequal1(gel(w,1)))
      cumule(&v, &e, gel(w,1), gel(w,2), gel(w,3), gel(w,4));
  }
  standard_model(e, &v);
  if (v0) { gcumulev(&v0, v); v = v0; }
  e = _coordch(E, v);
  if (ptv) { gerepileall(av, 2, &e, &v); *ptv = v; }
  else e = gerepilecopy(av, e);
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
ellglobalred(GEN E)
{
  long k, l;
  pari_sp av = avma;
  GEN c, P, N, v, v0, e, c4, c6, D;

  v0 = ellintegralmodel(E);
  e = ell_to_small(E);
  if (v0) e = _coordch(e, v0);
  v = init_ch();
  c4 = ell_get_c4(e);
  c6 = ell_get_c6(e);
  D  = ell_get_disc(e);
  P = gel(Z_factor(gcdii(c4,c6)),1);
  l = lg(P);
  for (k = 1; k < l; k++) (long)Z_pvalrem(D, gel(P,k), &D);
  if (!is_pm1(D)) P = shallowconcat(P, gel(Z_factor(absi(D)),1));
  l = lg(P); c = N = gen_1;
  for (k = 1; k < l; k++)
  {
    GEN p = gel(P,k), q = localred(e, p, 0), w = gel(q,3);
    N = mulii(N, powii(p, gel(q,1)));
    c = mulii(c, gel(q,4));
    if (!gequal1(gel(w,1)))
      cumule(&v, &e, gel(w,1), gel(w,2), gel(w,3), gel(w,4));
  }
  standard_model(e, &v);
  if (v0) { gcumulev(&v0, v); v = v0; }
  return gerepilecopy(av, mkvec3(N,v,c));
}

GEN
ell_to_small_red(GEN e, GEN *N)
{
  GEN E = ell_to_small(e), gr = ellglobalred(E);
  E = _coordch(E,gel(gr,2));
  *N = gel(gr,1); return E;
}

/********************************************************************/
/**                                                                **/
/**           ROOT NUMBER (after Halberstadt at p = 2,3)           **/
/**                                                                **/
/********************************************************************/
/* x a t_INT */
static long
val_aux(GEN x, long p)
{ return signe(x)? Z_lval(x,p): 12; }
static long
val_auxrem(GEN x, long p, long pk, long *u) {
  long v;
  GEN z;
  if (!signe(x)) { *u = 0; return 12; }
  v = Z_lvalrem(x,p,&z);
  *u = umodiu(z,pk); return v;
}
static void
val_init(GEN e, long p, long pk,
         long *v4, long *u, long *v6, long *v, long *vd, long *d1)
{
  GEN c4 = ell_get_c4(e), c6 = ell_get_c6(e), D = ell_get_disc(e);
  pari_sp av = avma;
  *v4 = val_auxrem(c4, p,pk, u);
  *v6 = val_auxrem(c6, p,pk, v);
  *vd = val_auxrem(D , p,pk, d1); avma = av;
}

/* p = 2 or 3 */
static long
neron(GEN e, long p, long* ptkod)
{
  long kod, v4, v6, vd;
  pari_sp av = avma;
  GEN nv = localred_23(e,p);
  *ptkod = kod = itos(gel(nv,2));
  v4 = val_aux(ell_get_c4(e), p);
  v6 = val_aux(ell_get_c6(e), p);
  vd = Z_lval(ell_get_disc(e), p); avma = av;
  if (p == 2) {
    if (kod > 4) return 1;
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
  } else {
    if (labs(kod) > 4) return 1;
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
}

static long
ellrootno_2(GEN e)
{
  long n2, kod, u, v, x1, y1, d1, vd, v4, v6;

  val_init(e, 2, 64, &v4, &u, &v6, &v, &vd, &d1);
  if (!vd) return 1;
  n2 = neron(e,2,&kod);
  if (kod>=5)
    return odd(umodiu(ell_get_a2(e),2) + umodiu(ell_get_a3(e),2)) ? 1 : -1;
  if (kod<-9) return (n2==2) ? -kross(-1,v) : -1;
  x1 = u+v+v;
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
        case 3: y1 = (u - (v << (v6-5))) & 15;
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
        y1 = (u + (v << (v6-8))) & 15;
        if (v6==10) return (y1==9 || y1==13) ? 1 : -1;
        else return (y1==9 || y1==5) ? 1 : -1;
      }
    case -8: return n2==2 ? kross(-1,v*d1) : -1;
    case -9: return n2==2 ? -kross(-1,d1) : -1;
    default: return -1;
  }
}

static long
ellrootno_3(GEN e)
{
  long n2, kod, u, v, d1, r6, K4, K6, vd, v4, v6;

  val_init(e, 3, 81, &v4, &u, &v6, &v, &vd, &d1);
  if (!vd) return 1;
  n2 = neron(e,3,&kod);
  K6 = kross(v,3); if (kod>4) return K6;
  r6 = v%9; K4 = kross(u,3);
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

/* assume p > 3, p^ex || N(E) */
static long
ellrootno_p(GEN e, GEN p, ulong ex)
{
  GEN j;
  long ep,z;

  if (!ex) return 1;
  if (ex == 1) return -kronecker(negi(ell_get_c6(e)),p);
  j=ell_get_j(e);
  if (!gequal0(j) && Q_pval(j,p) < 0) return krosi(-1,p);
  ep = 12 / ugcd(12, Z_pval(ell_get_disc(e),p));
  if (ep==4) z = 2; else z = (ep&1) ? 3 : 1;
  return krosi(-z, p);
}

long
ellrootno_global(GEN e, GEN N)
{
  long i, v, s = -1;
  GEN fa, P, E;

  v = Z_lvalrem(N, 2, &N); if (v) s *= ellrootno_2(e);
  v = Z_lvalrem(N, 3, &N); if (v) s *= ellrootno_3(e);
  fa = Z_factor(N);
  P = gel(fa,1);
  E = gel(fa,2);
  for (i=1; i<lg(P); i++) s *= ellrootno_p(e, gel(P,i), itou(gel(E,i)));
  return s;
}

/* local epsilon factor at p (over Q), including p=0 for the infinite place.
 * Global if p==1 or NULL. */
long
ellrootno(GEN e, GEN p)
{
  pari_sp av = avma;
  long s;
  GEN N;
  checksmallell(e);
  if (!p || isint1(p))
  {
    e = ell_to_small_red(e, &N);
    s = ellrootno_global(e, N);
  }
  else
  {
    GEN v;
    ulong pp;
    if (typ(p) != t_INT) pari_err_TYPE("ellrootno", p);
    if (signe(p) < 0) pari_err_PRIME("ellrootno",p);
    if (!signe(p)) return -1; /* local factor at infinity */
    pp = itou_or_0(p);
    e = ell_to_small(e);
    v = ellintegralmodel(e);
    if (v) e = _coordch(e, v);
    v = localred(e, p, 0);
    switch(pp)
    {
      case 2: s = ellrootno_2(e); break;
      case 3: s = ellrootno_3(e); break;
      default: s = ellrootno_p(e,p, itou(gel(v,1))); break;
    }
  }
  avma = av; return s;
}

/********************************************************************/
/**                                                                **/
/**                       TRACE OF FROBENIUS                       **/
/**                                                                **/
/********************************************************************/

/* compute a_2 */
static long
a2(GEN e)
{ /* solve y(1 + a1x + a3) = x (1 + a2 + a4) + a6 */
  ulong a1 = Rg_to_Fl(ell_get_a1(e), 2);
  ulong a2 = Rg_to_Fl(ell_get_a2(e), 2);
  ulong a3 = Rg_to_Fl(ell_get_a3(e), 2);
  ulong a4 = Rg_to_Fl(ell_get_a4(e), 2);
  ulong a6 = Rg_to_Fl(ell_get_a6(e), 2);
  long N = 1; /* oo */
  if (!a3) N ++; /* x = 0, y=0 or 1 */
  else if (!a6) N += 2; /* x = 0, y arbitrary */
  if ((a3 ^ a1) == 0) N++; /* x = 1, y = 0 or 1 */
  else if (a2 ^ a4 ^ a6) N += 2; /* x = 1, y arbitrary */
  return 3 - N;
}
/* a_p using Jacobi sums */
static long
ap_jacobi(GEN e, ulong p)
{
  if (p == 2) return a2(e);
  else
  {
    ulong i;
    ulong e6 = Rg_to_Fl(ell_get_b2(e), p);
    ulong e72= Rg_to_Fl(ell_get_b4(e), p) << 1;
    ulong e8 = Rg_to_Fl(ell_get_b6(e), p);
    long s = krouu(e8, p) + krouu((e8 + e72 + e6 + 4) % p, p); /* i = 0,1 */
    if (p < 757UL)
      for (i=2; i<p; i++)
        s += krouu((e8 + i*(e72 + i*(e6 + (i<<2)))) % p, p);
    else
      for (i=2; i<p; i++)
        s += krouu(e8 + Fl_mul(i, e72 + Fl_mul(i, e6 + (i<<2), p), p), p);
    return -s;
  }
}

/* z1 <-- z1 + z2, with precomputed inverse */
static void
FpE_add_ip(GEN z1, GEN z2, GEN a4, GEN p, GEN p2inv)
{
  GEN p1,x,x1,x2,y,y1,y2;

  x1 = gel(z1,1); y1 = gel(z1,2);
  x2 = gel(z2,1); y2 = gel(z2,2);
  if (x1 == x2)
    p1 = Fp_add(a4, mulii(x1,mului(3,x1)), p);
  else
    p1 = Fp_sub(y2,y1, p);

  p1 = Fp_mul(p1, p2inv, p);
  x = Fp_sub(sqri(p1), addii(x1,x2), p);
  y = Fp_sub(mulii(p1,subii(x1,x)), y1, p);
  affii(x, x1);
  affii(y, y1);
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
  return addii(a, mulii(b, diviiround(subii(h,a), b)));
}

static long
get_table_size(GEN pordmin, GEN B)
{
  pari_sp av = avma;
  GEN t = ceilr( sqrtr( divri(itor(pordmin, DEFAULTPREC), B) ) );
  if (is_bigint(t))
    pari_err_OVERFLOW("ellap [large prime: install the 'seadata' package]");
  avma = av;
  return itos(t) >> 1;
}

/* compute a_p using Shanks/Mestre + Montgomery's trick. Assume p > 457 */
static GEN
ellap1(GEN e, GEN p)
{
  pari_timer T;
  long *tx, *ty, *ti, pfinal, i, j, s, KRO, KROold, nb;
  ulong x;
  pari_sp av = avma, av2;
  GEN p1, P, h, mfh, F,f, fh,fg, pordmin, u, v, p1p, p2p, A, B, c4,c6, a4, pts;
  tx = NULL;
  ty = ti = NULL; /* gcc -Wall */

  if (DEBUGLEVEL) timer_start(&T);
  c4 = Rg_to_Fp(gdivgs(ell_get_c4(e),  -48), p);
  c6 = Rg_to_Fp(gdivgs(ell_get_c6(e), -864), p);
  /* once #E(Fp) is know mod B >= pordmin, it is completely determined */
  pordmin = addis(sqrti(gmul2n(p,4)), 1); /* ceil( 4sqrt(p) ) */
  p1p = addsi(1, p);
  p2p = shifti(p1p, 1);
  x = 0; u = c6; KRO = kronecker(u, p); KROold = - KRO;
  /* how many 2-torsion points ? */
  switch(FpX_nbroots(mkpoln(4, gen_1, gen_0, c4, c6), p))
  {
    case 3:  A = gen_0; B = utoipos(4); break;
    case 1:  A = gen_0; B = gen_2; break;
    default: A = gen_1; B = gen_2; break; /* 0 */
  }
  h = closest_lift(A, B, p1p);
  for(;;)
  {
    long CODE;
    while (!KRO || KRO == KROold)
    { /* look for points alternatively on E and its quadratic twist E' */
      x++; /* u = x^3 + c4 x + c6 */
      u = modii(addii(c6, mului(x, addii(c4, sqru(x)))), p);
      KRO = kronecker(u, p);
    }
    KROold = KRO;
    /* [ux, u^2] is on E_u: y^2 = x^3 + c4 u^2 x + c6 u^3
     * E_u isomorphic to E (resp. E') iff KRO = 1 (resp. -1)
     * #E(F_p) = p+1 - a_p, #E'(F_p) = p+1 + a_p
     *
     * #E_u(Fp) = A (mod B),  h is close to #E_u(Fp) */

    f = cgetg(3,t_VEC);
    gel(f,1) = modii(mului(x,u), p);
    gel(f,2) = modii(sqri(u),    p);
    a4 = modii(mulii(c4, gel(f,2)), p); /* c4 for E_u */
    fh = FpE_mul(f, h, a4, p);
    if (ell_is_inf(fh)) goto FOUND;

    s = get_table_size(pordmin, B);
    CODE = evaltyp(t_VECSMALL) | evallg(s+1);
    /* look for h s.t f^h = 0 */
    if (!tx)
    { /* first time: initialize */
      tx = newblock(3*(s+1));
      ty = tx + (s+1);
      ti = ty + (s+1);
    }
    F = FpE_mul(f,B,a4,p);
    *tx = CODE;

    /* F = B.f */
    P = gcopy(fh);
    if (s < 3)
    { /* we're nearly done: naive search */
      GEN q1 = P, mF = FpE_neg(F, p); /* -F */
      for (i=1;; i++)
      {
        P = FpE_add(P,F,a4,p); /* h.f + i.F */
        if (ell_is_inf(P)) { h = addii(h, mului(i,B)); goto FOUND; }
        q1 = FpE_add(q1,mF,a4,p); /* h.f - i.F */
        if (ell_is_inf(q1)) { h = subii(h, mului(i,B)); goto FOUND; }
      }
    }
    /* Baby Step/Giant Step */
    nb = minss(128, s >> 1); /* > 0. Will do nb pts at a time: faster inverse */
    pts = cgetg(nb+1, t_VEC);
    j = lgefint(p);
    for (i=1; i<=nb; i++)
    { /* baby steps */
      gel(pts,i) = P; /* h.f + (i-1).F */
      _fix(P+1, j); tx[i] = mod2BIL(gel(P,1));
      _fix(P+2, j); ty[i] = mod2BIL(gel(P,2));
      P = FpE_add(P,F,a4,p); /* h.f + i.F */
      if (ell_is_inf(P)) { h = addii(h, mului(i,B)); goto FOUND; }
    }
    mfh = FpE_neg(fh, p);
    fg = FpE_add(P,mfh,a4,p); /* h.f + nb.F - h.f = nb.F */
    if (ell_is_inf(fg)) { h = mului(nb,B); goto FOUND; }
    u = cgetg(nb+1, t_VEC);
    av2 = avma; /* more baby steps, nb points at a time */
    while (i <= s)
    {
      long maxj;
      for (j=1; j<=nb; j++) /* adding nb.F (part 1) */
      {
        P = gel(pts,j); /* h.f + (i-nb-1+j-1).F */
        gel(u,j) = subii(gel(fg,1), gel(P,1));
        if (!signe(gel(u,j))) /* sum = 0 or doubling */
        {
          long k = i+j-2;
          if (equalii(gel(P,2),gel(fg,2))) k -= 2*nb; /* fg == P */
          h = addii(h, mulsi(k,B)); goto FOUND;
        }
      }
      v = FpV_inv(u, p);
      maxj = (i-1 + nb <= s)? nb: s % nb;
      for (j=1; j<=maxj; j++,i++) /* adding nb.F (part 2) */
      {
        P = gel(pts,j);
        FpE_add_ip(P,fg, a4,p, gel(v,j));
        tx[i] = mod2BIL(gel(P,1));
        ty[i] = mod2BIL(gel(P,2));
      }
      avma = av2;
    }
    P = FpE_add(gel(pts,j-1),mfh,a4,p); /* = (s-1).F */
    if (ell_is_inf(P)) { h = mului(s-1,B); goto FOUND; }
    if (DEBUGLEVEL) timer_printf(&T, "[ellap1] baby steps, s = %ld",s);

    /* giant steps: fg = s.F */
    fg = FpE_add(P,F,a4,p);
    if (ell_is_inf(fg)) { h = mului(s,B); goto FOUND; }
    pfinal = mod2BIL(p); av2 = avma;
    /* Goal of the following: sort points by increasing x-coordinate hash.
     * Done in a complicated way to avoid allocating a large temp vector */
    p1 = vecsmall_indexsort(tx); /* = permutation sorting tx */
    for (i=1; i<=s; i++) ti[i] = tx[p1[i]];
    /* ti = tx sorted */
    for (i=1; i<=s; i++) { tx[i] = ti[i]; ti[i] = ty[p1[i]]; }
    /* tx is sorted. ti = ty sorted */
    for (i=1; i<=s; i++) { ty[i] = ti[i]; ti[i] = p1[i]; }
    /* ty is sorted. ti = permutation sorting tx */
    if (DEBUGLEVEL) timer_printf(&T, "[ellap1] sorting");
    avma = av2;

    gaffect(fg, gel(pts,1));
    for (j=2; j<=nb; j++) /* pts[j] = j.fg = (s*j).F */
    {
      P = FpE_add(gel(pts,j-1),fg,a4,p);
      if (ell_is_inf(P)) { h = mulii(mulss(s,j), B); goto FOUND; }
      gaffect(P, gel(pts,j));
    }
    /* replace fg by nb.fg since we do nb points at a time */
    avma = av2;
    fg = gcopy(gel(pts,nb)); /* copy: we modify (temporarily) pts[nb] below */
    av2 = avma;

    for (i=1,j=1; ; i++)
    {
      GEN ftest = gel(pts,j);
      ulong m, l = 1, r = s+1;
      long k, k2, j2;

      avma = av2;
      k = mod2BIL(gel(ftest,1));
      while (l<r)
      {
        m = (l+r) >> 1;
        if (tx[m] < k) l = m+1; else r = m;
      }
      if (r <= (ulong)s && tx[r] == k)
      {
        while (tx[r] == k && r) r--;
        k2 = mod2BIL(gel(ftest,2));
        for (r++; tx[r] == k && r <= (ulong)s; r++)
          if (ty[r] == k2 || ty[r] == pfinal - k2)
          { /* [h+j2] f == +/- ftest (= [i.s] f)? */
            j2 = ti[r] - 1;
            if (DEBUGLEVEL) timer_printf(&T, "[ellap1] giant steps, i = %ld",i);
            P = FpE_add(FpE_mul(F,stoi(j2),a4,p),fh,a4,p);
            if (equalii(gel(P,1), gel(ftest,1)))
            {
              if (equalii(gel(P,2), gel(ftest,2))) i = -i;
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
          P = gel(pts,j);
          gel(u,j) = subii(gel(fg,1), gel(P,1));
          if (gel(u,j) == gen_0) /* occurs once: i = j = nb, P == fg */
          {
            gel(u,j) = shifti(gel(P,2),1);
            save = fg[1]; fg[1] = P[1];
          }
        }
        v = FpV_inv(u, p);
        for (j=1; j<=nb; j++)
          FpE_add_ip(gel(pts,j),fg,a4,p, gel(v,j));
        if (i == nb) { fg[1] = save; }
        j = 1;
      }
    }
FOUND: /* found a point of exponent h on E_u */
    h = FpE_order(f, h, a4, p);
    /* h | #E_u(Fp) = A (mod B) */
    if (B == gen_1)
      B = h;
    else
      A = Z_chinese_all(A, gen_0, B, h, &B);

    i = (cmpii(B, pordmin) < 0);
    /* If we are not done, update A mod B for the _next_ curve, isomorphic to
     * the quadratic twist of this one */
    if (i) A = remii(subii(p2p,A), B); /* #E(Fp)+#E'(Fp) = 2p+2 */

    /* h = A mod B, closest lift to p+1 */
    h = closest_lift(A, B, p1p);
    if (!i) break;
  }
  if (tx) killblock(tx);
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
    num = Fl_add(c4, Fl_mul(3, Fl_mul(P->x, P->x, p), p), p);
    den = Fl_add(P->y, P->y, p);
  }
  else
  {
    num = Fl_sub(P->y, Q->y, p);
    den = Fl_sub(P->x, Q->x, p);
  }
  lambda = Fl_div(num, den, p);
  num = Fl_sub(Fl_mul(lambda, lambda, p), Fl_add(P->x, Q->x, p), p);
  P->y = Fl_sub(Fl_mul(lambda, Fl_sub(Q->x, num, p), p), Q->y, p);
  P->x = num; /* necessary in case P = Q: we need Q->x above */
}

/* Q <-- P^n */
static void
s_powell(sellpt *Q, sellpt *P, long n, long c4, long p)
{
  sellpt R = *P;

  if (n < 0) { n = -n; if (R.y) R.y = p - R.y; }
  Q->isnull = 1;
  Q->x = Q->y = 0; /* -Wall */
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
  GEN P, e, fa = factoru(H);
  long h = H, pp, i, j, l;
  sellpt fh;

  P = gel(fa,1); l = lg(P);
  e = gel(fa,2);
  for (i=1; i<l; i++)
  {
    pp = P[i];
    for (j=e[i]; j; j--)
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
compare_multiples(multiple *a, multiple *b) { return a->x - b->x; }

static long
sclosest_lift(long A, long B, ulong p2p)
{
  return A + B * (((ulong)(p2p + B - (A << 1))) / (B << 1));
}

/* assume p > 99 and e has good reduction at p. Should use Montgomery.
 * See ellap1() */
static long
ellap2(GEN e, ulong p)
{
  sellpt f, fh, fg, ftest, F;
  ulong x, u, c4, c6, cp4, p1p, p2p, h;
  long pordmin,A,B;
  long i, s, KRO, KROold, l, r, m;
  pari_sp av;
  multiple *table = NULL;

  av = avma;
  c4 = Rg_to_Fl(gdivgs(ell_get_c4(e),  -48), p);
  c6 = Rg_to_Fl(gdivgs(ell_get_c6(e), -864), p);
  pordmin = (long)(1 + 4*sqrt((float)p));
  p1p = p+1;
  p2p = p1p << 1;
  x = 0; u = c6; KRO = kross(u, p); KROold = -KRO;

  switch(Flx_nbroots(mkvecsmalln(5,0, 1, 0, c4, c6), p))
  {
    case 3:  A = 0; B = 4; break;
    case 1:  A = 0; B = 2; break;
    default: A = 1; B = 2; break; /* 0 */
  }
  h = sclosest_lift(A, B, p2p);
  for(;;)
  {
    while (!KRO || KRO == KROold)
    {
      ulong t;
      if (++x >= p) pari_err_PRIME("ellap",utoi(p));
      t = Fl_add(c4, Fl_mul(x,x,p), p);
      u = Fl_add(c6, Fl_mul(x, t, p), p);
      KRO = kross(u,p);
    }
    KROold = KRO;
    f.isnull = 0;
    f.x = Fl_mul(x, u, p);
    f.y = Fl_mul(u, u, p);
    cp4 = Fl_mul(c4, f.y, p);
    s_powell(&fh, &f, h, cp4, p);
    s = (long) (sqrt(((float)pordmin)/B) / 2);
    if (!s) s = 1;
    if (!table)
    {
      table = (multiple *) pari_malloc((s+1) * sizeof(multiple));
      F = f;
    }
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
      if (ftest.isnull) {
        if (!uisprime(p)) pari_err_PRIME("ellap",utoi(p));
        pari_err_BUG("ellap (f^(i*s) = 1)");
      }
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
      GEN C;
      A = itos( Z_chinese_all(gen_0, modss(A,B), utoipos(h), utoipos(B), &C) );
      if (is_bigint(C)) { h = A; break; }
      B = itos(C);
    }

    i = (B < pordmin);
    if (i)
    {
      A = (p2p - A) % B;
      if ((A << 1) > B) A -= B;
    }
    /* h = A mod B, closest lift to p+1 */
    h = sclosest_lift(A, B, p2p);
    avma = av; if (!i) break;
  }
  if (table) pari_free(table);
  return KRO==1? p1p-h: h-p1p;
}

/** ellap from CM (original code contributed by Mark Watkins) **/

static ulong
Mod16(GEN x) {
  long s = signe(x);
  ulong m;
  if (!s) return 0;
  m = mod16(x); if (!m) return m;
  if (s < 0) m = 16 - m;
  return m;
}
#define Mod2(x) (Mod16(x) & 1)
#define Mod4(x) (Mod16(x) & 3)
#define Mod8(x) (Mod16(x) & 7)

static GEN
ap_j0(GEN E,GEN p)
{
  GEN a, b, e, d;
  if (umodiu(p,3) != 1) return gen_0;
  (void)cornacchia2(utoipos(27),p, &a,&b);
  if (umodiu(a, 3) == 1) a = negi(a);
  d = Rg_to_Fp(gmulgs(ell_get_c6(E), 8), p);
  e = diviuexact(shifti(p,-1), 3); /* (p-1) / 6 */
  return centermod(mulii(a, Fp_pow(d, e, p)), p);
}
static GEN
ap_j1728(GEN E,GEN p)
{
  GEN a, b, d, e;
  if (mod4(p) != 1) return gen_0;
  (void)cornacchia2(utoipos(4),p, &a,&b);
  if (Mod4(a)==0) a = b;
  if (Mod2(a)==1) a = shifti(a,1);
  if (Mod8(a)==6) a = negi(a);
  d = Rg_to_Fp(gmulgs(ell_get_c4(E), -27), p);
  e = shifti(p,-2); /* (p-1) / 4 */
  return centermod(mulii(a, Fp_pow(d, e, p)), p);
}
static GEN
ap_j8000(GEN p)
{
  GEN a, b;
  long r = mod8(p);
  if (r != 1 && r != 3) return gen_0;
  (void)cornacchia2(utoipos(8),p, &a,&b);
  switch(Mod16(a)) {
    case 2: case 6:   if (Mod4(b)) a = negi(a);
      break;
    case 10: case 14: if (!Mod4(b)) a = negi(a);
      break;
  }
  return a;
}
static GEN
ap_j287496(GEN p)
{
  GEN a, b;
  if (mod4(p) != 1) return gen_0;
  (void)cornacchia2(utoipos(4),p, &a,&b);
  if (Mod4(a)==0) a = b;
  if (Mod2(a)==1) a = shifti(a,1);
  if (Mod8(a)==6) a = negi(a);
  if (krosi(2,p) < 0) a = negi(a);
  return a;
}
static GEN
ap_cm(int CM, GEN p)
{
  GEN a, b;
  if (krosi(CM,p) < 0) return gen_0;
  (void)cornacchia2(utoipos(-CM),p, &a, &b);
  if ((CM&3) == 0) CM >>= 2;
  if ((krois(a, -CM) > 0) ^ (CM == -7)) a = negi(a);
  return a;
}
static GEN
ec_ap_cm(GEN J,GEN C6B,GEN C6E,int CM,GEN jd,GEN jn,GEN p)
{
  GEN a;
  if (!equalii(modii(mulii(jd,J),p), jn)) return NULL;
  if      (CM == -8)  a = ap_j8000(p);
  else if (CM == -16) a = ap_j287496(p);
  else                a = ap_cm(CM,p);
  if (kronecker(mulii(C6E,C6B), p) < 0) a = negi(a);
  return a;
}

static GEN
ap_bad_red(GEN e, GEN p)
{
  pari_sp av = avma;
  GEN c6 = ell_get_c6(e);
  long s;
  if (equaliu(p, 2))
  {
    long c;
    if (!signe(c6)) return gen_0;
    c = mod8(c6);
    if (!odd(c)) return gen_0;
    return (c == 3 || c == 5)? gen_m1: gen_1;
  }
  c6 = Rg_to_Fp(c6, p);
  s = kronecker(c6, p);
  if (mod4(p) == 3) s = -s;
  avma = av; return stoi(s);
}
static GEN
u2tonegi(ulong a, ulong b) { GEN z = uu32toi(a,b); setsigne(z, -1); return z; }

static GEN
CM_ellap(GEN E, GEN p)
{
  pari_sp av = avma;
  GEN C4E, C6E, j, jn, jd, a, t, u;

#define CHECK(CM,J,C6B) a = ec_ap_cm(J,C6B,C6E,CM,jd,jn,p); if (a) goto DONE;
  C4E = Rg_to_Fp(ell_get_c4(E), p);
  if (!signe(C4E)) { a = ap_j0(E,p); goto DONE;}
  C6E = Rg_to_Fp(ell_get_c6(E), p);
  if (!signe(C6E)) { a = ap_j1728(E,p); goto DONE;}
  j = ell_get_j(E);
  jn = Rg_to_Fp(numer(j), p);
  jd = Rg_to_Fp(denom(j), p); /* j = jn/jd */
  CHECK(-7,  utoineg(3375),      utoipos(1323));
  CHECK(-8,  utoipos(8000),      utoineg(1792));
  CHECK(-12, utoipos(54000),     utoineg(19008));
  CHECK(-11, utoineg(32768),     utoineg(6776));
  CHECK(-16, utoipos(287496),    utoipos(12096));
  CHECK(-19, utoineg(884736),    utoineg(77976));
  CHECK(-27, utoineg(12288000),  utoineg(54648));
  CHECK(-7,  utoipos(16581375),  utoipos(75411));
  CHECK(-43, utoineg(884736000), utoineg(8387064));
  t = u2tonegi(0x00000022UL, 0x45ae8000UL); /* -27878400*5280 */
  CHECK(-67, t, utoineg(210408408));
  t = u2tonegi(0x03a4b862UL, 0xc4b40000UL); /* -640320^3 */
  u = u2tonegi(0x000000f8UL, 0x4414c858UL); /* -705220967*1512 */
  CHECK(-163, t, u);
#undef CHECK
  avma = av; return NULL;
DONE:
  return gerepileuptoint(av, icopy(a));
}

static GEN
easy_ap(GEN E, GEN p)
{
  pari_sp av = avma;
  GEN D = Rg_to_Fp(ell_get_disc(E), p);
  avma = av;
  if (!signe(D)) return ap_bad_red(E,p);
  if (cmpiu(p, 99) < 0) return stoi(ap_jacobi(E, itou(p)));
  return CM_ellap(E, p);
}

/* assume e is at least a 'small ell' */
static GEN
get_p(GEN e)
{
  GEN j = ell_get_j(e);
  switch(typ(j))
  {
    case t_INTMOD: return gel(j,1);
    case t_PADIC: return gel(j,2);
  }
  pari_err(e_MISC,"cannot determine the prime p in elliptic curve function");
  return NULL; /*notreached*/
}

GEN
ellap(GEN e, GEN p)
{
  GEN a;
  long lp;
  checksmallell(e);
  if (!p)
    p = get_p(e);
  else
    if (typ(p)!=t_INT || signe(p) <= 0) pari_err_PRIME("ellap",p);
  if ( (a = easy_ap(e, p)) ) return a;
  lp = expi(p);
  if (lp < 30) return stoi(ellap2(e, itou(p)));
  if (lp >= 62) { a = ellsea(e, p, 0); if (a) return a; }
  return ellap1(e, p);
}

/* assume e has good reduction mod p */
static long
ellap_small_goodred(GEN E, ulong p)
{
  pari_sp av;
  GEN a;
  if (p < 99) return ap_jacobi(E, p);
  av = avma; a = CM_ellap(E, utoipos(p));
  avma = av; if (a) return itos(a);
  if (p > 0x3fffffff) { a = ellap1(E, utoipos(p)); avma = av; return itos(a); }
  return ellap2(E, p);
}

static void
checkell_int(GEN e)
{
  checksmallell(e);
  if (typ(ell_get_a1(e)) != t_INT ||
      typ(ell_get_a2(e)) != t_INT ||
      typ(ell_get_a3(e)) != t_INT ||
      typ(ell_get_a4(e)) != t_INT ||
      typ(ell_get_a6(e)) != t_INT) pari_err_TYPE("anellsmall [not an integral model]",e);
}

GEN
anellsmall(GEN e, long n0)
{
  const long tab[4]={0,1,1,-1}; /* p prime; (-1/p) = tab[p&3]. tab[0] unused */
  ulong p, m, SQRTn, n = (ulong)n0;
  GEN an, D, c6;

  checkell_int(e);
  if (n0 <= 0) return cgetg(1,t_VEC);
  if (n >= LGBITS) {
    char *s = stack_malloc(128);
    sprintf(s,"anell for n >= %lu", LGBITS);
    pari_err_IMPL(s);
  }
  SQRTn = (ulong)sqrt(n);
  c6= ell_get_c6(e);
  D = ell_get_disc(e);

  an = cgetg(n+1,t_VECSMALL); an[1] = 1;
  for (p=2; p <= n; p++) an[p] = LONG_MAX; /* not computed yet */
  for (p=2; p<=n; p++)
  {
    if (an[p] != LONG_MAX) continue; /* p not prime */

    if (!umodiu(D,p)) /* bad reduction, p | D */
      switch (tab[p&3] * krois(c6,p)) /* (-c6/p) */
      {
        case -1: /* non deployee */
          for (m=p; m<=n; m+=p)
            if (an[m/p] != LONG_MAX) an[m] = -an[m/p];
          continue;
        case 0: /* additive */
          for (m=p; m<=n; m+=p) an[m] = 0;
          continue;
        case 1: /* deployee */
          for (m=p; m<=n; m+=p)
            if (an[m/p] != LONG_MAX) an[m] = an[m/p];
          continue;
      }
    else /* good reduction */
    {
      long ap = ellap_small_goodred(e, p);
      if (p <= SQRTn) {
        ulong pk, oldpk = 1;
        for (pk=p; pk <= n; oldpk=pk, pk *= p)
        {
          if (pk == p)
            an[pk] = ap;
          else
            an[pk] = ap * an[oldpk] - p * an[oldpk/p];
          for (m = n/pk; m > 1; m--)
            if (an[m] != LONG_MAX && m%p) an[m*pk] = an[m] * an[pk];
        }
      } else {
        an[p] = ap;
        for (m = n/p; m > 1; m--)
          if (an[m] != LONG_MAX) an[m*p] = ap * an[m];
      }
    }
  }
  return an;
}

GEN
anell(GEN e, long n0)
{
  GEN v = anellsmall(e, n0);
  long i;
  for (i = 1; i <= n0; i++) gel(v,i) = stoi(v[i]);
  settyp(v, t_VEC); return v;
}

GEN
akell(GEN e, GEN n)
{
  long i, j, s, ex;
  pari_sp av = avma;
  GEN fa, P, E, D, c6, ap, u, v, w, y, p;

  checksmallell(e);
  if (typ(n) != t_INT) pari_err_TYPE("akell",n);
  if (signe(n)<= 0) return gen_0;
  if (gequal1(n)) return gen_1;
  c6= ell_get_c6(e);
  D = ell_get_disc(e);
  if (typ(D) != t_INT) pari_err_TYPE("akell [not an integral model]",e);
  u = coprime_part(n, D);
  s = 1;
  if (!equalii(u, n))
  { /* bad reduction at primes dividing n/u */
    fa = Z_factor(diviiexact(n, u));
    P = gel(fa,1);
    E = gel(fa,2);
    for (i=1; i<lg(P); i++)
    {
      p = gel(P,i);
      j = kronecker(c6,p); if (!j) { avma = av; return gen_0; }
      if (mod2(gel(E,i)))
      {
        if (mod4(p) == 3) j = -j;
        if (j < 0) s = -s;
      }
    }
  }
  y = stoi(s); fa = Z_factor(u);
  P = gel(fa,1);
  E = gel(fa,2);
  for (i=1; i<lg(P); i++)
  { /* good reduction */
    p = gel(P,i);
    ex = itos(gel(E,i));
    ap = ellap(e,p);
    u = ap; v = gen_1;
    for (j=2; j<=ex; j++)
    {
      w = subii(mulii(ap,u), mulii(p,v));
      v = u; u = w;
    }
    y = mulii(u,y);
  }
  return gerepileuptoint(av,y);
}

GEN
elllseries(GEN e, GEN s, GEN A, long prec)
{
  pari_sp av = avma, av1, lim;
  ulong l, n;
  long eps, flun;
  GEN z, cg, v, cga, cgb, s2, K, gs, N;

  if (!A) A = gen_1;
  else
  {
    if (gsigne(A)<=0)
      pari_err(e_MISC,"cut-off point must be positive in lseriesell");
    if (gcmpgs(A,1) < 0) A = ginv(A);
  }
  if (isint(s, &s) && signe(s) <= 0) { avma = av; return gen_0; }
  flun = gequal1(A) && gequal1(s);
  checksmallell(e);
  e = ell_to_small_red(e, &N);
  eps = ellrootno_global(e, N);
  if (flun && eps < 0) { avma = av; return real_0(prec); }

  gs = ggamma(s, prec);
  cg = divrr(Pi2n(1, prec), gsqrt(N,prec));
  cga = gmul(cg, A);
  cgb = gdiv(cg, A);
  l = (ulong)((prec2nbits_mul(prec, LOG2) +
              fabs(gtodouble(real_i(s))-1.) * log(rtodbl(cga)))
            / rtodbl(cgb) + 1);
  if ((long)l < 1) l = 1;
  v = anellsmall(e, minss(l,LGBITS-1));
  s2 = K = NULL; /* gcc -Wall */
  if (!flun) { s2 = gsubsg(2,s); K = gpow(cg, gsubgs(gmul2n(s,1),2),prec); }
  z = gen_0;
  av1 = avma; lim = stack_lim(av1,1);
  for (n = 1; n <= l; n++)
  {
    GEN p1, an, gn = utoipos(n), ns;
    an = ((ulong)n<LGBITS)? stoi(v[n]): akell(e,gn);
    if (!signe(an)) continue;

    ns = gpow(gn,s,prec);
    p1 = gdiv(incgam0(s,mulur(n,cga),gs,prec), ns);
    if (flun)
      p1 = gmul2n(p1, 1);
    else
    {
      GEN p2 = gdiv(gmul(gmul(K,ns), incgam(s2,mulur(n,cgb),prec)), sqru(n));
      if (eps < 0) p2 = gneg_i(p2);
      p1 = gadd(p1, p2);
    }
    z = gadd(z, gmul(p1, an));
    if (low_stack(lim, stack_lim(av1,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"lseriesell");
      z = gerepilecopy(av1,z);
    }
  }
  return gerepileupto(av, gdiv(z,gs));
}

/********************************************************************/
/**                                                                **/
/**                       CANONICAL HEIGHT                         **/
/**                                                                **/
/********************************************************************/

/* h' := h_oo(a) + 1/2 log(denom(a)) */
static GEN
hell(GEN e, GEN a, long prec)
{
  long n;
  pari_sp av = avma;
  GEN pi2 = Pi2n(1, prec), w1 = gel(e,15), w2 = gel(e,16);
  GEN p1, y, z, q, pi2surw, qn, ps;

  pi2surw = gdiv(pi2, w1);
  z = gmul(real_i(zell(e,a,prec)), pi2surw);
  q = real_i( expIxy(mpneg(pi2surw), w2, prec) );
  y = mpsin(z); qn = gen_1; ps = gneg_i(q);
  for (n = 3; ; n += 2)
  {
    qn = gmul(qn, ps);
    ps = gmul(ps, q);
    y = gadd(y, gmul(qn, gsin(gmulsg(n,z),prec)));
    if (gexpo(qn) < -prec2nbits(prec)) break;
  }
  p1 = gmul(gsqr(gdiv(gmul2n(y,1), d_ellLHS(e,a))), pi2surw);
  p1 = gsqr(gsqr(gdiv(p1, gsqr(gsqr(denom(gel(a,1)))))));
  p1 = gdiv(gmul(p1,q), ell_get_disc(e));
  p1 = gmul2n(glog(gabs(p1,prec),prec), -5);
  return gerepileupto(av, gneg(p1));
}

/* h' := h_oo(x) + 1/2 log(denom(x)) */
static GEN
hells(GEN e, GEN Q, long prec)
{
  GEN b2 = ell_get_b2(e);
  GEN b4 = ell_get_b4(e);
  GEN b6 = ell_get_b6(e);
  GEN b8 = ell_get_b8(e);
  GEN x = gel(Q,1), w, z, t, mu, b42, b62;
  long n, lim;

  mu = gmul2n(glog(numer(x),prec),-1);
  t = ginv(gtofp(x, prec));
  b42 = gmul2n(b4,1);
  b62 = gmul2n(b6,1);
  lim = 15 + prec2nbits(prec);
  for (n = 3; n < lim; n += 2)
  {
    /* 4 + b2 t + 2b4 t^2 + b6 t^3 */
    w = gmul(t, gaddsg(4, gmul(t, gadd(b2, gmul(t, gadd(b42, gmul(t, b6)))))));
    /* 1 - (b4 t^2 + 2b6 t^3 + b8 t^4) */
    z = gsubsg(1, gmul(gsqr(t), gadd(b4, gmul(t, gadd(b62, gmul(t, b8))))));
    mu = gadd(mu, gmul2n(glog(z,prec), -n));
    t = gdiv(w, z);
  }
  return mu;
}

static GEN
hell2(GEN e, GEN x, long prec)
{
  GEN e3, ro, v, D;
  pari_sp av = avma;

  if (ell_is_inf(x)) return gen_0;
  D = ell_get_disc(e);
  ro= ell_get_roots(e);
  e3 = (gsigne(D) < 0)? gel(ro,1): gel(ro,3);
  v = init_ch(); gel(v,2) = addis(gfloor(e3),-1);
  return gerepileupto(av, hells(_coordch(e,v), ellchangepoint(x,v), prec));
}

/* exp( h_oo(z) ), assume z on neutral component.
 * If flag, return exp(4 h_oo(z)) instead */
static GEN
exphellagm(GEN e, GEN z, GEN e1, int flag, long prec)
{
  GEN x_a, a, b, r, V = cgetg(1, t_VEC), x = gel(z,1);
  long n, ex = 5-prec2nbits(prec), prec_e = realprec(e1);

  if (typ(x) == t_REAL && realprec(x) < prec_e) x = gprec_w(x, prec_e);
  x = new_coords(e, x, e1, &a,&b, 0, prec);
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
    if (gequal0(r) || gexpo(r) < ex) break;
    ab = gmul(a0, b);
    b = gsqrt(ab, prec);

    p1 = gmul2n(gsub(x, ab), -1);
    p2 = gsqr(a);
    x = gadd(p1, gsqrt(gadd(gsqr(p1), gmul(x, p2)), prec));
    V = shallowconcat(V, gadd(x, p2));
  }
  if (n) {
    x = gel(V,n);
    while (--n > 0) x = gdiv(gsqr(x), gel(V,n));
  } else {
    x = gadd(x, gsqr(a));
  }
  /* height on E1 is log(x)/2. Go back to E0 */
  return flag? gsqr( gdiv(gsqr(x), x_a) )
             : gdiv(x, sqrtr( mpabs(x_a) ));
}
/* exp( 4h_oo(z) ) */
static GEN
exp4hellagm(GEN e, GEN z, long prec)
{
  GEN e1 = ell_realrootprec(e, prec), x = gel(z,1);
  if (gcmp(x, e1) < 0) /* z not on neutral component */
  {
    GEN eh = exphellagm(e, addell(e, z,z), e1, 0, prec);
    /* h_oo(2P) = 4h_oo(P) - log |2y + a1x + a3| */
    return gmul(eh, gabs(d_ellLHS(e, z), prec));
  }
  return exphellagm(e, z, e1, 1, prec);
}

GEN
ellheightoo(GEN e, GEN z, long prec)
{
  GEN e1, h, x = gel(z,1);
  pari_sp av = avma;
  checksmallell_real(e);
  e1 = ell_realrootprec(e, prec);
  if (gcmp(x, e1) < 0) /* z not on neutral component */
  {
    GEN eh = exphellagm(e, addell(e, z,z), e1, 0, prec);
    /* h_oo(2P) = 4h_oo(P) - log |2y + a1x + a3| */
    h = gmul(eh, gabs(d_ellLHS(e, z), prec));
  }
  else
    h = exphellagm(e, z, e1, 1, prec);
  return gerepileuptoleaf(av, gmul2n(mplog(h), -2));
}

/* Assume e integral, given by a minimal model */
GEN
ellheight0(GEN e, GEN a, long flag, long prec)
{
  long i, tx = typ(a), lx;
  pari_sp av = avma;
  GEN Lp, x, y, z, phi2, psi2, psi3;

  if (flag > 2 || flag < 0) pari_err_FLAG("ellheight");
  checksmallell_real(e); if (!is_matvec_t(tx)) pari_err_TYPE("ellheight",a);
  lx = lg(a); if (lx==1) return cgetg(1,tx);
  tx = typ(a[1]);
  if (is_matvec_t(tx))
  {
    z = cgetg(lx,tx);
    for (i=1; i<lx; i++) gel(z,i) = ellheight0(e,gel(a,i),flag,prec);
    return z;
  }
  if (ell_is_inf(a)) return gen_0;
  if (!oncurve(e,a)) pari_err(e_MISC, "point not on elliptic curve");

  psi2 = numer(d_ellLHS(e,a));
  if (!signe(psi2)) { avma = av; return gen_0; }
  switch(flag)
  {
    case 0:  z = hell2(e,a,prec); break; /* Tate 4^n */
    case 1:  z = hell(e,a,prec);  break; /* Silverman's log(sigma) */
    default:
    {
      GEN d = denom(gel(a,1));
      z = exp4hellagm(e,a,prec); /* = exp(4h_oo(a)), Mestre's AGM */
      if (!is_pm1(d)) z = gmul(z, sqri(d));
      z = gmul2n(mplog(z), -2); break;
    }
  }
  x = gel(a,1);
  y = gel(a,2);
  psi3 = numer( /* b8 + 3x b6 + 3x^2 b4 + x^3 b2 + 3 x^4 */
     gadd(ell_get_b8(e), gmul(x,
     gadd(gmulsg(3,ell_get_b6(e)), gmul(x,
     gadd(gmulsg(3,ell_get_b4(e)), gmul(x, gadd(ell_get_b2(e), gmulsg(3,x)))))))) );
  if (!signe(psi3)) { avma=av; return gen_0; }

  phi2 = numer( /* a4 + 2a2 x + 3x^2 - y a1*/
    gsub(gadd(ell_get_a4(e),gmul(x,gadd(shifti(ell_get_a2(e),1),gmulsg(3,x)))),
         gmul(ell_get_a1(e),y)) );
  Lp = gel(Z_factor(gcdii(psi2,phi2)),1);
  lx = lg(Lp);
  for (i=1; i<lx; i++)
  {
    GEN p = gel(Lp,i);
    long u, v, n, n2;
    if (signe(remii(ell_get_c4(e),p)))
    { /* p \nmid c4 */
      long N = Z_pval(ell_get_disc(e),p);
      if (!N) continue;
      n2 = Z_pval(psi2,p); n = n2<<1;
      if (n > N) n = N;
      u = n * ((N<<1) - n);
      v = N << 3;
    }
    else
    {
      n2 = Z_pval(psi2, p);
      n  = Z_pval(psi3, p);
      if (n >= 3*n2) { u = n2; v = 3; } else { u = n; v = 8; }
    }
    /* z -= u log(p) / v */
    z = gsub(z, divru(mulur(u, logr_abs(itor(p,prec))), v));
  }
  return gerepileupto(av, gmul2n(z, 1));
}

GEN
ghell(GEN e, GEN a, long prec) { return ellheight0(e,a,2,prec); }

GEN
mathell(GEN e, GEN x, long prec)
{
  GEN y, h, pdiag;
  long lx = lg(x),i,j,tx=typ(x);
  pari_sp av = avma;

  if (!is_vec_t(tx)) pari_err_TYPE("ellheightmatrix",x);
  y = cgetg(lx,t_MAT); pdiag = new_chunk(lx);
  for (i=1; i<lx; i++)
  {
    gel(pdiag,i) = ghell(e,gel(x,i),prec);
    gel(y,i) = cgetg(lx,t_COL);
  }
  for (i=1; i<lx; i++)
  {
    gcoeff(y,i,i) = gel(pdiag,i);
    for (j=i+1; j<lx; j++)
    {
      h = ghell(e, addell(e,gel(x,i),gel(x,j)), prec);
      h = gsub(h, gadd(gel(pdiag,i),gel(pdiag,j)));
      gcoeff(y,j,i) = gcoeff(y,i,j) = gmul2n(h, -1);
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
    return gerepileupto(av, gmul2n(gsub(p1,p2), -1));
  }
  y = cgetg(lz1, typ(z1));
  for (i=1; i<lz1; i++) gel(y,i) = bilhells(e,gel(z1,i),z2,h2,prec);
  return y;
}

GEN
bilhell(GEN e, GEN z1, GEN z2, long prec)
{
  GEN p1, h2;
  long tz1 = typ(z1), tz2 = typ(z2);
  pari_sp av = avma;

  if (!is_matvec_t(tz1)) pari_err_TYPE("ellbil",z1);
  if (!is_matvec_t(tz2)) pari_err_TYPE("ellbil",z2);
  if (lg(z1)==1) return cgetg(1,tz1);
  if (lg(z2)==1) return cgetg(1,tz2);

  tz1 = typ(z1[1]);
  tz2 = typ(z2[1]);
  if (is_matvec_t(tz2))
  {
    if (is_matvec_t(tz1)) pari_err_TYPE("bilhell",z1);
    p1 = z1; z1 = z2; z2 = p1;
  }
  h2 = ghell(e,z2,prec);
  return gerepileupto(av, bilhells(e,z1,z2,h2,prec));
}

/********************************************************************/
/**                                                                **/
/**                    Modular Parametrization                     **/
/**                                                                **/
/********************************************************************/
/* t*x^v (1 + O(x)), t != 0 */
static GEN
triv_ser(GEN t, long v)
{
  GEN s = cgetg(3,t_SER);
  s[1] = evalsigne(1) | _evalvalp(v) | evalvarn(0);
  gel(s,2) = t; return s;
}

GEN
elltaniyama(GEN e, long prec)
{
  GEN x, w, c, d, X, C, b2, b4;
  long n, m;
  pari_sp av = avma;

  checksmallell(e);
  if (prec < 0) pari_err(e_MISC, "negative precision in elltaniyama");
  if (!prec) retmkvec2(triv_ser(gen_1,-2), triv_ser(gen_m1,-3));

  x = cgetg(prec+3,t_SER);
  x[1] = evalsigne(1) | _evalvalp(-2) | evalvarn(0);
  d = ginv(gtoser(anell(e,prec+1), 0, prec)); setvalp(d,-1);
  /* 2y(q) + a1x + a3 = d qx'(q). Solve for x(q),y(q):
   * 4y^2 = 4x^3 + b2 x^2 + 2b4 x + b6 */
  c = gsqr(d);
  /* solve 4x^3 + b2 x^2 + 2b4 x + b6 = c (q x'(q))^2; c = 1/q^2 + O(1/q)
   * Take derivative then divide by 2x':
   *  b2 x + b4 = (1/2) (q c')(q x') + c q (q x')' - 6x^2.
   * Write X[i] = coeff(x, q^i), C[i] = coeff(c, q^i), we obtain for all n
   *  ((n+1)(n+2)-12) X[n+2] =  b2 X[n] + b4 delta_{n = 0}
   *   + 6    \sum_{m = -1}^{n+1} X[m] X[n-m]
   *   - (1/2)\sum_{m = -2}^{n+1} (n+m) m C[n-m]X[m].
   * */
  C = c+4;
  X = x+4;
  gel(X,-2) = gen_1;
  gel(X,-1) = gmul2n(gel(C,-1), -1); /* n = -3, X[-1] = C[-1] / 2 */
  b2 = ell_get_b2(e);
  b4 = ell_get_b4(e);
  for (n=-2; n <= prec-4; n++)
  {
    pari_sp av2 = avma;
    GEN s1, s2, s3;
    if (n != 2)
    {
      s3 = gmul(b2, gel(X,n));
      if (!n) s3 = gadd(s3, b4);
      s2 = gen_0;
      for (m=-2; m<=n+1; m++)
        if (m) s2 = gadd(s2, gmulsg(m*(n+m), gmul(gel(X,m),gel(C,n-m))));
      s2 = gmul2n(s2,-1);
      s1 = gen_0;
      for (m =- 1; m+m < n; m++) s1 = gadd(s1, gmul(gel(X,m),gel(X,n-m)));
      s1 = gmul2n(s1, 1);
      if (m+m==n) s1 = gadd(s1, gsqr(gel(X,m)));
      /* ( (n+1)(n+2) - 12 ) X[n+2] = (6 s1 + s3 - s2) */
      s1 = gdivgs(gsub(gadd(gmulsg(6,s1),s3),s2), (n+2)*(n+1)-12);
    }
    else
    {
      GEN b6 = ell_get_b6(e);
      GEN U = cgetg(9, t_SER);
      U[1] = evalsigne(1) | _evalvalp(-2) | evalvarn(0);
      gel(U,2) = gel(x,2);
      gel(U,3) = gel(x,3);
      gel(U,4) = gel(x,4);
      gel(U,5) = gel(x,5);
      gel(U,6) = gel(x,6);
      gel(U,7) = gel(x,7);
      gel(U,8) = gen_0; /* defined mod q^5 */
      /* write x = U + x_4 q^4 + O(q^5) and expand original equation */
      w = derivser(U); setvalp(w,-2); /* q X' */
      /* 4X^3 + b2 U^2 + 2b4 U + b6 */
      s1 = gadd(b6, gmul(U, gadd(gmul2n(b4,1), gmul(U,gadd(b2,gmul2n(U,2))))));
      /* s2 = (qX')^2 - (4X^3 + b2 U^2 + 2b4 U + b6) = 28 x_4 + O(q) */
      s2 = gsub(gmul(c,gsqr(w)), s1);
      s1 = signe(s2)? gdivgs(gel(s2,2), 28): gen_0; /* = x_4 */
    }
    gel(X,n+2) = gerepileupto(av2, s1);
  }
  w = gmul(d,derivser(x)); setvalp(w, valp(w)+1);
  w = gsub(w, ellLHS0(e,x));
  c = cgetg(3,t_VEC);
  gel(c,1) = gcopy(x);
  gel(c,2) = gmul2n(w,-1); return gerepileupto(av, c);
}

/********************************************************************/
/**                                                                **/
/**                       TORSION POINTS (over Q)                  **/
/**                                                                **/
/********************************************************************/
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
    if (ugcd(i,k)==1 && smaller_x(gel(q,1), gel(p,1))) p = q;
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
    GEN p1, best = q, np = ellpow_Z(e,p,utoipos(n));
    if (n % 2 && smaller_x(gel(np,1), gel(best,1))) best = np;
    p1 = addell(e,q,np);
    if (smaller_x(gel(p1,1), gel(best,1))) q = p1;
    else if (best == np) { p = addell(e,p,q); q = np; }
    p = best_in_cycle(e,p,k);
    if (v)
    {
      p = ellchangepoint(p,v);
      q = ellchangepoint(q,v);
    }
    r = cgetg(4,t_VEC);
    gel(r,1) = utoipos(2*k);
    gel(r,2) = mkvec2(utoipos(k), gen_2);
    gel(r,3) = mkvec2copy(p, q);
  }
  else
  {
    if (p)
    {
      p = best_in_cycle(e,p,k);
      if (v) p = ellchangepoint(p,v);
      r = cgetg(4,t_VEC);
      gel(r,1) = utoipos(k);
      gel(r,2) = mkvec( gel(r,1) );
      gel(r,3) = mkvec( gcopy(p) );
    }
    else
    {
      r = cgetg(4,t_VEC);
      gel(r,1) = gen_1;
      gel(r,2) = cgetg(1,t_VEC);
      gel(r,3) = cgetg(1,t_VEC);
    }
  }
  return r;
}

static GEN
_pow(void *E, GEN x, GEN n) { return ellpow_Z((GEN)E,x,n); }

static GEN
topol(GEN x)
{
  switch(typ(x))
  {
    case t_INTMOD: return gel(x,2);
    case t_POLMOD: return gtovecrev(gel(x,2));
    case t_FFELT:  return gtovecrev(FF_to_FpXQ(x));
  }
  return x;
}

static ulong
_hash(GEN x)
{
  pari_sp av;
  GEN r;
  ulong h=0;
  if (ell_is_inf(x)) return 0;
  av = avma;
  r = topol(gel(x,1));
  if (typ(r)==t_INT) h=signe(r)?mod2BIL(r):0;
  else
  {
    long i, l=lg(r);
    for (i=1;i<l;i++)
      if (signe(gel(r,i)))
        h ^= mod2BIL(gel(r,i))<<((i-1)&(BITS_IN_LONG-1));
  }
  avma = av; return h;
}

static int
_cmp(GEN x, GEN y)
{
  pari_sp av;
  int r;
  if (ell_is_inf(x)) return !ell_is_inf(y);
  if (ell_is_inf(y)) return -1;
  av = avma;
  r = lexcmp(topol(gel(x,1)), topol(gel(y,1)));
  if (!r) r = lexcmp(topol(gel(x,2)), topol(gel(y,2)));
  avma = av; return r;
}

static const struct bb_group ell_group={_mul,_pow,NULL,_hash,_cmp,ell_is_inf};

GEN
elllog(GEN e, GEN a, GEN g, GEN o)
{
  pari_sp av = avma;
  GEN j, z;
  checksmallell(e); checkellpt(a); checkellpt(g);
  j = ell_get_j(e);
  switch(typ(j))
  {
    case t_INTMOD:
      if (!o) { GEN p = gel(j,1); o = subii(addis(p,1), ellap(e,p)); }
      break;
    case t_FFELT:
      if (!o) pari_err(e_MISC,"curve order required over a finite field");
      break;
    default: pari_err_IMPL("elllog over infinite fields");
  }
  z = gen_PH_log(a,g,o, (void*)e,&ell_group,NULL);
  return gerepileupto(av, z? z: cgetg(1,t_VEC));
}

/* assume e is defined over Q (use Mazur's theorem) */
static long
_orderell(GEN e, GEN p)
{
  pari_sp av = avma;
  GEN p1 = p;
  long k;
  for (k = 1; k <= 12; k++)
  {
    if (ell_is_inf(p1)) { avma = av; return k; }
    p1 = addell(e, p1, p);
  }
  avma = av; return 0;
}

GEN
ellorder(GEN e, GEN z, GEN o)
{
  pari_sp av = avma;
  GEN j;
  checksmallell(e); checkellpt(z);
  j = ell_get_j(e);
  switch(typ(j))
  {
    case t_INTMOD:
      if (!o) { GEN p = gel(j,1); o = subii(addis(p,1), ellap(e,p)); }
      break;
    case t_FFELT:
      if (!o) pari_err(e_MISC,"curve order required over a finite field");
      break;
    case t_INT: case t_FRAC:
      return utoi( _orderell(e, z) );
    default: pari_err_IMPL("orderell for nonrational elliptic curves");
  }
  return gerepileuptoint(av, gen_order(z, o, (void*)e, &ell_group));
}

GEN
orderell(GEN e, GEN z) { return ellorder(e,z,NULL); }

/* Using Lutz-Nagell */

/* p in Z[X] of degree 3. Return vector of x/4, x integral root of p */
static GEN
ratroot(GEN p)
{
  GEN L, a, ld;
  long i, t, v = ZX_valrem(p, &p);

  if (v == 3) return ellinf();
  if (v == 2) return mkvec2(gen_0, gmul2n(negi(gel(p,2)), -2));

  L = cgetg(4,t_VEC); t = 1;
  if (v == 1) gel(L,t++) = gen_0;
  ld = divisors(gel(p,2));
  for (i=1; i<lg(ld); i++)
  {
    a = gel(ld,i);
    if (!signe(poleval(p,a))) gel(L,t++) = gmul2n(a, -2);
    a = negi(a);
    if (!signe(poleval(p,a))) gel(L,t++) = gmul2n(a, -2);
  }
  setlg(L,t); return L;
}

static int
is_new_torsion(GEN e, GEN v, GEN p, long t2) {
  GEN pk = p, pkprec = NULL;
  long k,l;

  for (k=2; k<=6; k++)
  {
    pk = addell(e,pk,p); /* = [k] p */
    if (ell_is_inf(pk)) return 1;

    for (l=2; l<=t2; l++)
      if (gequal(gel(pk,1),gmael(v,l,1))) return 1;

    if (pkprec && k<=5)
      if (gequal(gel(pk,1),gel(pkprec,1))) return 1;
    pkprec=pk;
  }
  return 0;
}

static GEN
nagelllutz(GEN e)
{
  GEN ld, pol, p1, lr, r, v, w2, w3;
  long i, j, nlr, t, t2, k, k2;
  pari_sp av=avma;

  v = ellintegralmodel(e);
  if (v) e = _coordch(e,v);
  pol = RgX_rescale(RHSpol(e), utoipos(4));
  r = cgetg(17, t_VEC);
  gel(r,1) = ellinf();
  lr = ratroot(pol); nlr=lg(lr)-1;
  for (t=1,i=1; i<=nlr; i++)
  {
    GEN x = gel(lr,i), y = gmul2n(gneg(ellLHS0(e,x)), -1);
    gel(r,++t) = mkvec2(x, y);
  }
  ld = Z_factor(gmul2n(absi(ell_get_disc(e)), 4));
  p1 = gel(ld,2); k = lg(p1);
  for (i=1; i<k; i++) gel(p1,i) = shifti(gel(p1,i), -1);
  ld = divisors(ld);
  for (t2=t,j=1; j<lg(ld); j++)
  {
    GEN d = gel(ld,j);
    lr = ratroot(ZX_Z_sub(pol, shifti(sqri(d), 6)));
    for (i=1; i<lg(lr); i++)
    {
      GEN x = gel(lr,i), y = gmul2n(gsub(d, ellLHS0(e,x)), -1);
      p1 = mkvec2(x, y);
      if (is_new_torsion(e,r,p1,t2))
      {
        gel(r,++t) = p1;
        gel(r,++t) = mkvec2(x, gsub(y, d));
      }
    }
  }
  if (t == 1) { avma = av; return tors(e,1,NULL,NULL,v); }

  if (nlr < 3)
  {
    w2 = mkvec( utoipos(t) );
    for (k=2; k<=t; k++)
      if (_orderell(e,gel(r,k)) == t) break;
    if (k>t) pari_err_BUG("elltors (bug1)");

    w3 = mkvec( gel(r,k) );
  }
  else
  {
    if (t&3) pari_err_BUG("elltors (bug2)");
    t2 = t>>1;
    w2 = mkvec2(utoipos(t2), gen_2);
    for (k=2; k<=t; k++)
      if (_orderell(e,gel(r,k)) == t2) break;
    if (k>t) pari_err_BUG("elltors (bug3)");

    p1 = ellpow_Z(e,gel(r,k),utoipos(t>>2));
    k2 = (!ell_is_inf(p1) && gequal(gel(r,2),p1))? 3: 2;
    w3 = mkvec2(gel(r,k), gel(r,k2));
  }
  if (v)
  {
    gel(v,1) = ginv(gel(v,1));
    w3 = ellchangepoint(w3,v);
  }
  return gerepilecopy(av, mkvec3(utoipos(t), w2,w3));
}

/* Using Doud's algorithm */

/* finds a bound for #E_tor */
static long
torsbound(GEN e)
{
  long m, b, bold, p = 2;
  pari_sp av = avma;
  byteptr diff = diffptr+1;
  GEN D = ell_get_disc(e);
  long n = expi(D) >> 3;
  /* n = number of primes to try ~ 1 prime every 8 bits in D */
  b = bold = 5040; /* = 2^4 * 3^2 * 5 * 7 */
  m = 0;
  while (m < n)
  {
    NEXT_PRIME_VIADIFF_CHECK(p,diff);
    if (!umodiu(D, p)) continue;

    b = ugcd(b, p+1 - ellap_small_goodred(e, p));
    avma = av;
    if (b == 1) break;
    if (b == bold) m++; else { bold = b; m = 0; }
  }
  return b;
}

static GEN
myround(GEN x, long *e)
{
  GEN y = grndtoi(x,e);
  if (*e > -5 && prec2nbits(gprecision(x)) < gexpo(y) - 10)
    pari_err(e_MISC, "ellinit data not accurate enough. Increase precision");
  return y;
}

/* E the curve, w in C/Lambda ~ E of order n, returns q = pointell(w) as a
 * rational point on the curve, or NULL if q is not rational. */
static GEN
torspnt(GEN E, GEN w, long n, long prec)
{
  GEN p = cgetg(3,t_VEC), q = pointell(E, w, prec);
  long e;
  gel(p,1) = gmul2n(myround(gmul2n(gel(q,1),2), &e),-2);
  if (e > -5 || typ(p[1]) == t_COMPLEX) return NULL;
  gel(p,2) = gmul2n(myround(gmul2n(gel(q,2),3), &e),-3);
  if (e > -5 || typ(p[2]) == t_COMPLEX) return NULL;
  return (oncurve(E,p)
      && ell_is_inf(ellpow_Z(E,p,utoipos(n)))
      && _orderell(E,p) == n)? p: NULL;
}

GEN
elltors(GEN e)
{
  long B, i, ord, pr, prec, k = 1;
  pari_sp av=avma;
  GEN v,w,w1,w22,w1j,w12,p,tor1,tor2;

  checkell_real(e);
  v = ellintegralmodel(e);
  if (v) e = _coordch(e,v);

  B = torsbound(e); /* #E_tor | B */
  if (B == 1) { avma = av; return tors(e,1,NULL,NULL, v); }

  pr = DEFAULTPREC + ((lgefint(ell_get_disc(e))-2) >> 1); /* pr >= size of sqrt(D) */
  w1 = gel(e,15);
  prec = precision(w1);
  if (pr < prec) { prec = pr; e = gprec_w(e, pr); w1 = gel(e,15); }
  if (v) gel(v,1) = ginv(gel(v,1));
  w22 = gmul2n(gel(e,16),-1);
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
  if ((p = torspnt(e,w12,2,prec))) { tor1 = p; ord++; }
  w = w22;
  if ((p = torspnt(e,w,2,prec))) { tor2 = p; ord += 2; }
  if (!ord)
  {
    w = gadd(w12,w22);
    if ((p = torspnt(e,w,2,prec))) { tor2 = p; ord += 2; }
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
        if (!p && i%4==0) p = torspnt(e,gadd(w22,w1j),i,prec);
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
    case 0: return elltors(e);
    case 1: return nagelllutz(e);
    default: pari_err_FLAG("elltors");
  }
  return NULL; /* not reached */
}

/********************************************************************/
/**                                                                **/
/**                       PAIRINGS                                 **/
/**                                                                **/
/********************************************************************/
/* Formulae from a GP script by J.E.Cremona */

static GEN
ellffvert(GEN t, GEN pt)
{
  return ell_is_inf(t)?gen_1:gsub(gel(pt, 1), gel(t, 1));
}

static GEN
ellfftang(GEN E, GEN t, GEN pt)
{
  GEN dyf, dxf;
  GEN a1 = ell_get_a1(E), a2 = ell_get_a2(E), a3 = ell_get_a3(E);
  GEN a4 = ell_get_a4(E);
  if (ell_is_inf(t)) return gen_1;
  dyf = gadd(gadd(gmulgs(gel(t, 2), 2),gmul(a1, gel(t, 1))), a3);
  if (gequal0(dyf))
    return gsub(gel(pt, 1), gel(t, 1));
  dxf = gsub(gmul(a1, gel(t, 2)), gadd(gadd(gmulsg(3, gsqr(gel(t, 1))),
                                       gmul(gmulsg(2, a2), gel(t, 1))), a4));
  return gadd(gsub(gel(pt, 2), gel(t, 2)), gmul(gdiv(dxf, dyf),
              gsub(gel(pt, 1), gel(t, 1))));
}

static GEN
ellffchord(GEN E, GEN t, GEN s, GEN pt)
{
  if (ell_is_inf(s)) return ellffvert(t, pt);
  if (ell_is_inf(t)) return ellffvert(s, pt);
  if (gequal(gel(s, 1), gel(t, 1)))
  {
    if (gequal(gel(s, 2), gel(t, 2))) return ellfftang(E, t, pt);
    else return ellffvert(t, pt);
  }
  return gsub(gsub(gel(pt, 2), gel(t, 2)), gmul(gdiv(gsub(gel(t, 2), gel(s, 2)), gsub(gel(t, 1), gel(s, 1))), gsub(gel(pt, 1), gel(t, 1))));
}

struct ellff
{
  GEN E, pt1, pt2;
};

static GEN
ellffadd(GEN E, GEN S, GEN T, GEN pt1, GEN pt2)
{
  GEN s=gel(S,1), t=gel(T,1);
  GEN a, b, h;
  GEN ST = cgetg(3, t_VEC);
  GEN st = addell(E, s, t);
  pari_sp av=avma;
  gel(ST, 1) = st;
  if (ell_is_inf(st))
  {
    a  = ellffvert(s, pt1);
    if (gequal0(a)) return gen_0;
    b  = ellffvert(s, pt2);
  } else
  {
    a  = gmul(ellffchord(E, s, t, pt1), ellffvert(st, pt2));
    if (gequal0(a)) return gen_0;
    b  = gmul(ellffchord(E, s, t, pt2), ellffvert(st, pt1));
  }
  if (gequal0(b)) return gen_0;
  h = gmul(gmul(gel(S,2), gel(T,2)),  gdiv(a, b));
  gel(ST, 2) = gerepileupto(av, h);
  return ST;
}
static GEN
_ellffadd(void *data, GEN s, GEN t)
{
  struct ellff* ff=(struct ellff*) data;
  if (s==gen_0 || t==gen_0) return gen_0;
  return ellffadd(ff->E,s,t,ff->pt1,ff->pt2);
}

static GEN
ellffdbl(GEN E, GEN S, GEN pt1, GEN pt2)
{
  GEN s=gel(S,1);
  GEN a, b, h;
  GEN S2 = cgetg(3, t_VEC);
  GEN s2 = addell(E, s, s);
  pari_sp av=avma;
  gel(S2, 1) = s2;
  if (ell_is_inf(s2))
  {
    a  = ellfftang(E, s, pt1);
    if (gequal0(a)) return gen_0;
    b  = ellfftang(E, s, pt2);
  } else
  {
    a  = gmul(ellfftang(E, s, pt1), ellffvert(s2, pt2));
    if (gequal0(a)) return gen_0;
    b  = gmul(ellfftang(E, s, pt2), ellffvert(s2, pt1));
  }
  if (gequal0(b)) return gen_0;
  h = gmul(gsqr(gel(S,2)), gdiv(a, b));
  gel(S2, 2) = gerepileupto(av, h);
  return S2;
}

static GEN
_ellffdbl(void *data, GEN s)
{
  struct ellff* ff=(struct ellff*) data;
  if (s==gen_0) return gen_0;
  return ellffdbl(ff->E, s,ff->pt1,ff->pt2);
}

static GEN
ellffmul(GEN E, GEN t, GEN m, GEN pt1, GEN pt2)
{
  struct ellff ff;
  ff.E=E;  ff.pt1=pt1; ff.pt2=pt2;
  return gen_pow(t, m, (void*)&ff, _ellffdbl, _ellffadd);
}

static GEN
ellweilpairing3(GEN E, GEN t, GEN s, GEN unit)
{
  GEN t2,s2,a,b;
  if (gequal(s,t)) return unit;
  t2 = addell(E,t,t);
  if (gequal(s,t2)) return unit;
  s2 = addell(E,s,s);
  a  = gmul(ellfftang(E, s, t),  ellfftang(E, t, s2));
  b  = gmul(ellfftang(E, s, t2), ellfftang(E, t, s));
  return gsqr(gdiv(a,b));
}

GEN
ellweilpairing(GEN E, GEN t, GEN s, GEN m)
{
  pari_sp ltop=avma;
  GEN w, unit;
  checksmallell(E); checkellpt(t); checkellpt(s);
  if (typ(m)!=t_INT) pari_err_TYPE("ellweilpairing",m);
  unit = gpowgs(ell_get_j(E), 0);
  if (ell_is_inf(s) || ell_is_inf(t)) return unit;
  if (equaliu(m, 2))
    return gequal(s, t)?unit:gerepileupto(ltop, gneg(unit));
  if (equaliu(m, 3))
    return gerepileupto(ltop,ellweilpairing3(E, s, t, unit));
  while(1)
  {
    GEN r, rs, tr, a, b;
    avma = ltop;
    r  = ellrandom(E);
    rs = addell(E, r, s);
    tr = subell(E, t, r);
    if (ell_is_inf(rs) || ell_is_inf(tr) || ell_is_inf(r) || gequal(rs, t))
      continue;
    a = ellffmul(E, mkvec2(t, gen_1), m, rs, r);
    if (a==gen_0) continue;
    b = ellffmul(E, mkvec2(s, gen_1), m, tr, invell(E,r));
    if (b==gen_0) continue;
    if (!ell_is_inf(gel(a,1)) || !ell_is_inf(gel(b,1)))
      pari_err(e_MISC,"Points of wrong order in ellweilpairing");
    w = gdiv(gel(a, 2), gel(b, 2));
    return gerepileupto(ltop,w);
  }
}

GEN
elltatepairing(GEN E, GEN t, GEN s, GEN m)
{
  pari_sp ltop=avma;
  checksmallell(E); checkellpt(t); checkellpt(s);
  if (typ(m)!=t_INT) pari_err_TYPE("elltatepairing",m);
  if (ell_is_inf(s) || ell_is_inf(t)) return gen_1;
  while(1)
  {
    GEN r, rs, a;
    avma = ltop;
    r  = ellrandom(E);
    rs = addell(E, r, s);
    if (ell_is_inf(rs) || gequal(t,r) || ell_is_inf(r) || gequal(rs, t))
      continue;
    a = ellffmul(E, mkvec2(t, gen_1), m, rs, r);
    if (a==gen_0) continue;
    if (!ell_is_inf(gel(a,1)))
      pari_err(e_MISC,"Points of wrong order in elltatepairing");
    return gerepilecopy(ltop, gel(a, 2));
  }
}

static GEN
ell_to_a4a6(GEN E, GEN p)
{
  GEN a1, a3, b2, c4, c6;
  checkell5(E);
  a1 = Rg_to_Fp(ell_get_a1(E),p);
  a3 = Rg_to_Fp(ell_get_a3(E),p);
  b2 = Rg_to_Fp(ell_get_b2(E),p);
  c4 = Rg_to_Fp(ell_get_c4(E),p);
  c6 = Rg_to_Fp(ell_get_c6(E),p);
  retmkvec3(Fp_neg(Fp_mulu(c4, 27, p), p), Fp_neg(Fp_mulu(c6, 54, p), p),
            mkvec4(modsi(6,p),Fp_mulu(b2,3,p),Fp_mulu(a1,3,p),Fp_mulu(a3,108,p)));
}

GEN
ellgroup(GEN E, GEN p)
{
  pari_sp av = avma;
  GEN N, N0, N1, r, F, F1, e, a4, a6;
  long i, j, l1;
  checksmallell(E);
  if (!p)
    p = get_p(E);
  else
    if (typ(p)!=t_INT) pari_err_TYPE("ellgroup",p);
  N = subii(addis(p, 1), ellap(E, p));
  r = gcdii(N, subis(p, 1));
  if (is_pm1(r)) goto ellgroup_cyclic; /* Takes care of p=2 */
  if (equaliu(p, 3))
  { /* The only possible non-cyclic group is [2,2] which happens 9 times */
    ulong b2, b4, b6;
    if (!equaliu(N, 4)) goto ellgroup_cyclic;
    /* If the group is not cyclic, T = 4x^3 + b2 x^2 + 2b4 x + b6
     * must have 3 roots else 1 root. Test T(0) = T(1) = 0 mod 3 */
    b6 = Rg_to_Fl(ell_get_b6(E), 3);
    if (b6) goto ellgroup_cyclic;
    /* b6 = T(0) = 0 mod 3. Test T(1) */
    b2 = Rg_to_Fl(ell_get_b2(E), 3);
    b4 = Rg_to_Fl(ell_get_b4(E), 3);
    if ((1 + b2 + (b4<<1)) % 3) goto ellgroup_cyclic;
    return gerepileupto(av, mkvec2s(2, 2));
  } /* Now assume p > 3 */
  F1 = gel(Z_factor(r), 1); l1 = lg(F1);
  F = cgetg(3, t_MAT);
  gel(F,1) = cgetg(l1, t_COL);
  gel(F,2) = cgetg(l1, t_COL);
  for (i = 1, j = 1; i < l1; ++i)
  {
    long v = Z_pval(N, gel(F1, i));
    if (v <=1) continue;
    gcoeff(F, j  , 1) = gel(F1, i);
    gcoeff(F, j++, 2) = stoi(v);
  }
  setlg(F[1],j); setlg(F[2],j);
  if (j==1) goto ellgroup_cyclic;
  N0 = factorback(F); N1 = diviiexact(N, N0);
  e = ell_to_a4a6(E, p); a4 = gel(e, 1); a6 = gel(e, 2);
  while(1)
  {
    pari_sp av2 = avma;
    GEN P, Q, d, s, t, m, z;

    P = FpE_mul(random_FpE(a4,a6,p), N1, a4, p);
    s = FpE_order(P, F, a4, p); if (equalii(s, N0)) goto ellgroup_cyclic;

    Q = FpE_mul(random_FpE(a4,a6,p), N1, a4, p);
    t = FpE_order(Q, F, a4, p); if (equalii(t, N0)) goto ellgroup_cyclic;

    m = lcmii(s, t);
    z = FpE_weilpairing(P, Q, m, a4, p);
    d = Fp_order(z, F, p);
    /* structure is [N/d, d] iff m d == N0. Note that N/d = N1 m */
    if (is_pm1(d) && equalii(m, N0)) goto ellgroup_cyclic;
    if (equalii(mulii(m, d), N0))
      return gerepilecopy(av, mkvec2(mulii(N1,m), d));
    avma = av2;
  }
ellgroup_cyclic:
  return gerepileupto(av, mkveccopy(N));
}

static GEN
elldivpol4(GEN e, long n, long v)
{
  GEN b2,b4,b6,b8, res;
  if (n==0) return pol_0(v);
  if (n<=2) return pol_1(v);
  b2  = ell_get_b2(e); b4  = ell_get_b4(e);
  b6  = ell_get_b6(e); b8  = ell_get_b8(e);
  if (n==3)
    res = mkpoln(5,utoi(3),b2,gmulsg(3,b4),gmulsg(3,b6),b8);
  else
  {
    GEN b10 = gsub(gmul(b2, b8), gmul(b4, b6));
    GEN b12 = gsub(gmul(b8, b4), gsqr(b6));
    res = mkpoln(7,gen_2,b2,gmulsg(5,b4),gmulsg(10,b6),gmulsg(10,b8),b10,b12);
  }
  setvarn(res, v); return res;
}

/* T = (2y + a1x + a3)^2 modulo the curve equation */
static GEN
elldivpol0(GEN e, GEN t, GEN T, long n, long v)
{
  GEN ret;
  long m = n/2;
  if (gel(t,n)) return gel(t,n);
  if (n<=4) ret = elldivpol4(e, n, v);
  else if (odd(n))
  {
    GEN t1 = RgX_mul(elldivpol0(e,t,T,m+2,v),
                     gpowgs(elldivpol0(e,t,T,m,v),3));
    GEN t2 = RgX_mul(elldivpol0(e,t,T,m-1,v),
                     gpowgs(elldivpol0(e,t,T,m+1,v),3));
    if (odd(m))/*f_{4l+3} = f_{2l+3}f_{2l+1}^3 - T f_{2l}f_{2l+2}^3, m=2l+1*/
      ret = RgX_sub(t1, RgX_mul(T,t2));
    else       /*f_{4l+1} = T f_{2l+2}f_{2l}^3 - f_{2l-1}f_{2l+1}^3, m=2l*/
      ret = RgX_sub(RgX_mul(T,t1), t2);
  }
  else
  { /* f_2m = f_m(f_{m+2}f_{m-1}^2 - f_{m-2}f_{m+1}^2) */
    GEN t1 = RgX_mul(elldivpol0(e,t,T,m+2,v),
                     RgX_sqr(elldivpol0(e,t,T,m-1,v)));
    GEN t2 = RgX_mul(elldivpol0(e,t,T,m-2,v),
                     RgX_sqr(elldivpol0(e,t,T,m+1,v)));
    ret = RgX_mul(elldivpol0(e,t,T,m,v), RgX_sub(t1,t2));
  }
  gel(t,n) = ret;
  return ret;
}

GEN
elldivpol(GEN e, long n, long v)
{
  pari_sp av = avma;
  GEN ret;
  checksmallell(e);
  if (v==-1) v = 0;
  if (varncmp(gvar(e), v) <= 0)
    pari_err(e_MISC,"variable must have higher priority in elldivpol");
  if (n<0) n = -n;
  if (n==1 || n==3)
    ret = elldivpol4(e, n, v);
  else
  {
    GEN a1 = ell_get_a1(e), a2 = ell_get_a2(e), a3 = ell_get_a3(e);
    GEN a4 = ell_get_a4(e), a6 = ell_get_a6(e);
    GEN f1 = mkpoln(4, gen_1, a2, a4, a6); /* x^3 + a2 x^2 + a4 x + a6 */
    GEN f2 = mkpoln(2, a1, a3); /* a1 x + a3 */
    GEN d2 = RgX_add(gmulsg(4, f1), RgX_sqr(f2)); /* (2y + a1x + 3)^2 mod E */
    setvarn(d2,v);
    if (n <= 4)
      ret = elldivpol4(e, n, v);
    else
      ret = elldivpol0(e, const_vec(n,NULL), RgX_sqr(d2), n, v);
    if (n%2==0) ret = RgX_mul(ret, d2);
  }
  return gerepilecopy(av, ret);
}
