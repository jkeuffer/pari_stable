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
/**                      GENERIC OPERATIONS                        **/
/**                         (first part)                           **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

#define fix_frac(z) if (signe(z[2])<0)\
{\
  setsigne(z[1],-signe(z[1]));\
  setsigne(z[2],1);\
}

/* assume z[1] was created last */
#define fix_frac_if_int(z) if (is_pm1(z[2]))\
  z = gerepileupto((pari_sp)(z+3), (GEN)z[1]);

/* assume z[1] was created last */
#define fix_frac_if_int_GC(z,tetpil) { if (is_pm1(z[2]))\
  z = gerepileupto((pari_sp)(z+3), (GEN)z[1]);\
else\
  gerepilecoeffssp((pari_sp)z, tetpil, z+1, 2); }

static long
kro_quad(GEN x, GEN y)
{
  long k;
  pari_sp av=avma;

  x = subii(sqri((GEN)x[3]), shifti((GEN)x[2],2));
  k = kronecker(x,y); avma=av; return k;
}

static GEN
to_primitive(GEN x, GEN *cx)
{
  if (typ(x) != t_POL)
    { *cx = x; x = gun; }
  else if (lg(x) == 3)
    { *cx = (GEN)x[2]; x = gun; }
  else
    { *cx = content(x); if (!gcmp1(*cx)) x = gdiv(x,*cx); }
  return x;
}

/* assume gvar(x) = varn(mod) */
GEN
to_polmod(GEN x, GEN mod)
{
  long tx = typ(x);
  GEN z = cgetg(3, t_POLMOD);

  if (tx == t_RFRAC) x = gmul((GEN)x[1], ginvmod((GEN)x[2],mod));
  z[1] = (long)mod;
  z[2] = (long)x;
  return z;
}

/* is -1 not a square in Zp, assume p prime */
INLINE int
Zp_nosquare_m1(GEN p) { return (mod4(p) & 2); /* 2 or 3 mod 4 */ }

static GEN addpp(GEN x, GEN y);
static GEN mulpp(GEN x, GEN y);
static GEN divpp(GEN x, GEN y);
/* Argument codes for inline routines
 * c: complex, p: padic, q: quad, f: floating point (REAL, some complex)
 * R: without imaginary part (INT, REAL, INTMOD, FRAC, PADIC if -1 not square)
 * T: some type (to be converted to PADIC)
 */
static GEN
addRc(GEN x, GEN y) {
  GEN z = cgetg(3,t_COMPLEX);
  z[1]=ladd(x,(GEN)y[1]);
  z[2]=lcopy((GEN)y[2]); return z;
}
static GEN
mulRc(GEN x, GEN y) {
  GEN z = cgetg(3,t_COMPLEX);
  z[1] = lmul(x,(GEN)y[1]);
  z[2] = lmul(x,(GEN)y[2]); return z;
}
static GEN
divRc(GEN x, GEN y) {
  GEN a, b, N, z = cgetg(3,t_COMPLEX);
  pari_sp tetpil, av = avma;
  a = gmul(x, (GEN)y[1]);
  b = gmul(x, (GEN)y[2]); if(!gcmp0(b)) b = gneg_i(b);
  N = gnorm(y); tetpil = avma;
  z[1] = ldiv(a, N);
  z[2] = ldiv(b, N); gerepilecoeffssp(av,tetpil,z+1,2); return z;
}
static GEN
divcR(GEN x, GEN y) {
  GEN z = cgetg(3,t_COMPLEX);
  z[1] = ldiv((GEN)x[1], y);
  z[2] = ldiv((GEN)x[2], y); return z;
}
static GEN
addRq(GEN x, GEN y) {
  GEN z = cgetg(4,t_QUAD); copyifstack(y[1], z[1]);
  z[2] = ladd(x, (GEN)y[2]);
  z[3] = lcopy((GEN)y[3]); return z;
}
static GEN
mulRq(GEN x, GEN y) {
  GEN z = cgetg(4,t_QUAD); copyifstack(y[1], z[1]);
  z[2] = lmul(x,(GEN)y[2]);
  z[3] = lmul(x,(GEN)y[3]); return z;
}
static GEN
addqf(GEN x, GEN y, long prec) { pari_sp av = avma;
  long i = gexpo(x) - gexpo(y);
  if (i <= 0) i = 0; else i >>= TWOPOTBITS_IN_LONG;
  return gerepileupto(av, gadd(y, quadtoc(x, prec + i)));
}
static GEN
mulqf(GEN x, GEN y, long prec) { pari_sp av = avma;
  return gerepileupto(av, gmul(y, quadtoc(x, prec)));
}
static GEN
divqf(GEN x, GEN y, long prec) { pari_sp av = avma;
  return gerepileupto(av, gdiv(quadtoc(x,prec), y));
}
static GEN
divfq(GEN x, GEN y, long prec) { pari_sp av = avma;
  return gerepileupto(av, gdiv(x, quadtoc(y,prec)));
}
/* y PADIC, x + y by converting x to padic */
static GEN
addTp(GEN x, GEN y) { pari_sp av = avma; GEN z;

  if (!valp(y)) z = cvtop2(x,y);
  else {
    long l = signe(y[4])? valp(y) + precp(y): valp(y);
    z  = cvtop(x, (GEN)y[2], l);
  }
  return gerepileupto(av, addpp(z, y));
}
/* y PADIC, x * y by converting x to padic */
static GEN
mulTp(GEN x, GEN y) { pari_sp av = avma;
  return gerepileupto(av, mulpp(cvtop2(x,y), y));
}
/* y PADIC, non zero x / y by converting x to padic */
static GEN
divTp(GEN x, GEN y) { pari_sp av = avma;
  return gerepileupto(av, divpp(cvtop2(x,y), y));
}
/* x PADIC, x / y by converting y to padic */
static GEN
divpT(GEN x, GEN y) { pari_sp av = avma;
  return gerepileupto(av, divpp(x, cvtop2(y,x)));
}

/* z := Mod(x,X) + Mod(y,X) [ t_INTMOD preallocated ], x,y,X INT, 0 <= x,y < X
 * clean memory from z on */
static GEN
add_intmod_same(GEN z, GEN X, GEN x, GEN y) {
  if (lgefint(X) == 3) {
    ulong u = Fl_add(itou(x),itou(y), X[2]);
    avma = (pari_sp)z; z[2] = lutoi(u);
  }
  else {
    GEN u = addii(x,y); if (cmpii(u, X) >= 0) u = subii(u, X);
    z[2] = lpileuptoint((pari_sp)z, u);
  }
  icopyifstack(X, z[1]); return z;
}
/* cf add_intmod_same */
static GEN
mul_intmod_same(GEN z, GEN X, GEN x, GEN y) {
  if (lgefint(X) == 3) {
    ulong u = Fl_mul(itou(x),itou(y), X[2]);
    avma = (pari_sp)z; z[2] = lutoi(u);
  }
  else
    z[2] = lpileuptoint((pari_sp)z, remii(mulii(x,y), X) );
  icopyifstack(X, z[1]); return z;
}
/* cf add_intmod_same */
static GEN
div_intmod_same(GEN z, GEN X, GEN x, GEN y)
{
  if (lgefint(X) == 3) {
    ulong m = (ulong)X[2], u = Fl_inv(itou(y), m);
    if (!u) err(invmoder,"%Z", gmodulcp(y, X));
    u = Fl_mul(itou(x), u, m);
    avma = (pari_sp)z; z[2] = lutoi(u);
  }
  else
    z[2] = lpileuptoint((pari_sp)z, remii(mulii(x, Fp_inv(y,X)), X) );
  icopyifstack(X, z[1]); return z;
}

/*******************************************************************/
/*                                                                 */
/*        REDUCTION to IRREDUCIBLE TERMS (t_FRAC/t_RFRAC)          */
/*                                                                 */
/* (static routines are not memory clean, but OK for gerepileupto) */
/*******************************************************************/
static GEN
gred_rfrac_copy(GEN n, GEN d)
{
  GEN y = cgetg(3,t_RFRAC);
  y[1] = lcopy(n);
  y[2] = lcopy(d); return y;
}

/* n is scalar, non-zero */
static GEN
gred_rfrac_simple(GEN n, GEN d)
{
  GEN y, c = content(d);

  if (gcmp1(c)) return gred_rfrac_copy(n,d);
  n = gdiv(n, c);
  d = gdiv(d, c);

  c = denom(n);
  y = cgetg(3,t_RFRAC);
  y[1] = lmul(n,c);
  y[2] = lmul(d,c); return y;
}

static GEN
gred_rfrac2_i(GEN n, GEN d)
{
  GEN y, p1, cn, cd, c;
  long tx,ty;

  if (isexactzero(n)) return gcopy(n);
  n = simplify_i(n); tx = typ(n);
  d = simplify_i(d); ty = typ(d);
  if (ty!=t_POL)
  {
    if (tx!=t_POL) return gred_rfrac_copy(n,d);
    if (varncmp(gvar2(d), varn(n)) > 0) return gdiv(n,d);
    err(talker,"incompatible variables in gred");
  }
  if (tx!=t_POL)
  {
    if (varncmp(varn(d), gvar2(n)) < 0) return gred_rfrac_simple(n,d);
    err(talker,"incompatible variables in gred");
  }
  if (varncmp(varn(d), varn(n)) < 0) return gred_rfrac_simple(n,d);
  if (varncmp(varn(d), varn(n)) > 0) return gdiv(n,d);

  /* now n and d are polynomials with the same variable */
  cd = content(d); if (!gcmp1(cd)) d = gdiv(d,cd);
  cn = content(n);
  if (gcmp0(cn))
  {
    long vn, vd = polvaluation(d, NULL);
    if (vd)
    {
      vn = polvaluation(n, NULL);
      if (vn)
      {
        long v = min(vn, vd);
        n = shiftpol_i(n, v);
        d = shiftpol_i(d, v);
        if (gcmp1(d)) d = NULL;
      }
    }
    n = gdiv(n,cd);
    return d? gred_rfrac_copy(n, d): n;
  }
  if (!gcmp1(cn))
  {
    n = gdiv(n,cn);
    c = gdiv(cn,cd);
  }
  else
    c = ginv(cd);
  y = RgX_divrem(n, d, &p1);
  if (!signe(p1)) return gmul(c,y);
  p1 = ggcd(d,p1);
  if (degpol(p1)) { n=gdeuc(n,p1); d=gdeuc(d,p1); }
  if (typ(c) == t_POL)
  {
    cd = denom(content(c));
    cn = gmul(c, cd);
  }
  else
  {
    cn = numer(c);
    cd = denom(c);
  }
  p1 = cgetg(3,t_RFRAC);
  p1[1] = lmul(n,cn);
  p1[2] = lmul(d,cd); return p1;
}

GEN
gred_rfrac2(GEN x1, GEN x2)
{
  pari_sp av = avma;
  return gerepileupto(av, gred_rfrac2_i(x1, x2));
}

/* x1,x2 t_INT, return x1/x2 in reduced form */
GEN
gred_frac2(GEN x1, GEN x2)
{
  GEN p1, y = dvmdii(x1,x2,&p1);
  pari_sp av;

  if (p1 == gzero) return y; /* gzero intended */
  av = avma;
  p1 = gcdii(x2,p1);
  if (is_pm1(p1))
  {
    avma = av; y = cgetg(3,t_FRAC);
    y[1] = licopy(x1);
    y[2] = licopy(x2);
  }
  else
  {
    p1 = gclone(p1);
    avma = av; y = cgetg(3,t_FRAC);
    y[1] = (long)diviiexact(x1,p1);
    y[2] = (long)diviiexact(x2,p1);
    gunclone(p1);
  }
  fix_frac(y); return y;
}

/********************************************************************/
/**                                                                **/
/**                          SUBTRACTION                           **/
/**                                                                **/
/********************************************************************/

GEN
gsub(GEN x, GEN y)
{
  pari_sp tetpil, av = avma;
  y = gneg_i(y); tetpil = avma;
  return gerepile(av,tetpil, gadd(x,y));
}

/********************************************************************/
/**                                                                **/
/**                           ADDITION                             **/
/**                                                                **/
/********************************************************************/
/* x, y compatible PADIC */
static GEN
addpp(GEN x, GEN y)
{
  pari_sp av = avma;
  long c,d,e,r,rx,ry;
  GEN u, z, mod, p = (GEN)x[2];

  (void)new_chunk(5 + lgefint(x[3]) + lgefint(y[3]));
  e = valp(x);
  r = valp(y); d = r-e;
  if (d < 0) { swap(x,y); e = r; d = -d; }
  rx = precp(x);
  ry = precp(y);
  if (d) /* v(x) < v(y) */
  {
    r = d+ry; z = gpowgs(p,d);
    if (r < rx) mod = mulii(z,(GEN)y[3]); else { r = rx; mod = (GEN)x[3]; }
    u = addii((GEN)x[4], mulii(z,(GEN)y[4]));
    u = remii(u, mod);
  }
  else
  {
    if (ry < rx) { r=ry; mod = (GEN)x[3]; } else { r=rx; mod = (GEN)y[3]; }
    u = addii((GEN)x[4], (GEN)y[4]);
    if (!signe(u) || (c = pvaluation(u,p,&u)) >= r)
    {
      avma = av; return zeropadic(p, e+r);
    }
    if (c)
    {
      mod = diviiexact(mod, gpowgs(p,c));
      r -= c;
      e += c;
    }
    u = remii(u, mod);
  }
  avma = av; z = cgetg(5,t_PADIC);
  z[1] = evalprecp(r) | evalvalp(e);
  z[3] = licopy(mod);
  z[4] = licopy(u);
  icopyifstack(p, z[2]); return z;
}

/* return x + y, where x is t_INT or t_FRAC(N), y t_PADIC */
static GEN
addQp(GEN x, GEN y)
{
  pari_sp av;
  long tx,vy,py,d,r,e;
  GEN z,q,p,p1,p2,mod,u;

  if (gcmp0(x)) return gcopy(y);

  av = avma; p = (GEN)y[2]; tx = typ(x);
  e = (tx == t_INT)? pvaluation(x,p,&p1)
                   : pvaluation((GEN)x[1],p,&p1) -
                     pvaluation((GEN)x[2],p,&p2);
  vy = valp(y); d = vy - e; py = precp(y); r = d + py;
  if (r <= 0) { avma = av; return gcopy(y); }
  mod = (GEN)y[3];
  u   = (GEN)y[4];
  (void)new_chunk(5 + ((lgefint(mod) + lgefint(p)*labs(d)) << 1));

  if (d > 0)
  {
    q = gpowgs(p,d);
    mod = mulii(mod, q);
    u   = mulii(u, q);
    if (tx != t_INT && !is_pm1(p2)) p1 = mulii(p1, Fp_inv(p2,mod));
    u = addii(u, p1);
  }
  else if (d < 0)
  {
    q = gpowgs(p,-d);
    if (tx != t_INT && !is_pm1(p2)) p1 = mulii(p1, Fp_inv(p2,mod));
    p1 = mulii(p1, q);
    u = addii(u, p1);
    r = py; e = vy;
  }
  else
  {
    long c;
    if (tx != t_INT && !is_pm1(p2)) p1 = mulii(p1, Fp_inv(p2,mod));
    u = addii(u, p1);
    if (!signe(u) || (c = pvaluation(u,p,&u)) >= r)
    {
      avma = av; return zeropadic(p,e+r);
    }
    if (c)
    {
      mod = diviiexact(mod, gpowgs(p,c));
      r -= c;
      e += c;
    }
  }
  u = modii(u, mod);
  avma = av; z = cgetg(5,t_PADIC);
  z[1] = evalprecp(r) | evalvalp(e);
  z[3] = licopy(mod);
  z[4] = licopy(u);
  icopyifstack(p, z[2]); return z;
}

/* Mod(x,X) + Mod(y,X) */
#define add_polmod_same add_polmod_scal
/* Mod(x,X) + Mod(y,Y) */
static GEN
add_polmod(GEN X, GEN Y, GEN x, GEN y)
{
  GEN z = cgetg(3,t_POLMOD);
  static long T[3]={ evaltyp(t_POLMOD) | _evallg(3),0,0 };
  long vx = varn(X), vy = varn(Y);
  if (vx==vy) {
    pari_sp av;
    z[1] = (long)srgcd(X,Y); av = avma;
    z[2] = lpileupto(av, gmod(gadd(x, y), (GEN)z[1])); return z;
  }
  if (varncmp(vx, vy) < 0)
  { copyifstack(X, z[1]); T[1]=(long)Y; T[2]=(long)y; y = T; }
  else
  { copyifstack(Y, z[1]); T[1]=(long)X; T[2]=(long)x; x = T; }
  z[2] = ladd(x, y); return z;
}
/* Mod(y, Y) + x,  assuming x scalar or polynomial in same var and reduced degree */
static GEN
add_polmod_scal(GEN Y, GEN y, GEN x)
{
  GEN z = cgetg(3,t_POLMOD); copyifstack(Y, z[1]);
  z[2] = ladd(x, y); return z;
}
/* typ(y) == t_POL, varn(y) = vy, x "scalar" [e.g object in lower variable] */
static GEN
add_pol_scal(GEN y, GEN x, long vy)
{
  long i, ly = lg(y);
  GEN z;
  if (ly <= 3) {
    if (ly == 2) return isexactzero(x)? zeropol(vy): scalarpol(x,vy);
    z = cgetg(3, t_POL); z[1] = y[1];
    z[2] = ladd(x,(GEN)y[2]);
    if (gcmp0((GEN)z[2])) {
      if (isexactzero((GEN)z[2])) { avma = (pari_sp)(z+3); return zeropol(vy); }
      setsigne(z, 0);
    }
    return z;
  }
  z = cgetg(ly,t_POL); z[1] = y[1];
  z[2] = ladd(x,(GEN)y[2]);
  for (i = 3; i < ly; i++) z[i] = lcopy((GEN)y[i]);
  /* normalize_pol optimized for this case */
  for (i = ly-1; i > 2; i--)
    if (!gcmp0((GEN)z[i])) { /* setsigne(z, 1); already true */ return z; }
  if (!gcmp0((GEN)z[2])) { setsigne(z, 1); return z; }
  setsigne(z, 0); return z;
}
/* typ(y) == t_POL, varn(y) = vy, x "scalar" [e.g object in lower variable] */
static GEN
add_ser_scal(GEN y, GEN x, long vy)
{
  long i, j, l, ly;
  pari_sp av;
  GEN z, t;

  if (isexactzero(x)) return gcopy(y);
  l = valp(y); ly = lg(y);
  if (l < 3-ly) return gcopy(y);
  if (l < 0)
  {
    z = cgetg(ly,t_SER); z[1] = y[1];
    for (i = 2; i <= 1-l; i++) z[i] = lcopy((GEN)y[i]);
    for (i = 3-l; i < ly; i++) z[i] = lcopy((GEN)y[i]);
    z[2-l] = ladd(x,(GEN)y[2-l]); return z;
  }
  if (l > 0)
  {
    if (gcmp0(y)) ly = 2;

    ly += l; z = cgetg(ly,t_SER);
    z[1] = evalsigne(1) | evalvalp(0) | evalvarn(vy);
    for (i=3; i<=l+1; i++) z[i] = zero;
    for (   ; i < ly; i++) z[i] = lcopy((GEN)y[i-l]);
    z[2] = lcopy(x); return z;
  }
  /* l = 0 */
  if (!signe(y)) return zeroser(vy, 0); /* 1 + O(1) --> O(1) */

  av = avma; z = cgetg(ly,t_SER);
  t = gadd(x, (GEN)y[2]);
  if (!isexactzero(t))
  {
    z[1] = evalsigne(1)|evalvalp(0) | evalvarn(vy);
    z[2] = (long)t;
    for (i=3; i<ly; i++) z[i] = lcopy((GEN)y[i]);
    return z;
  }
  avma = av; /* first coeff is 0 */
  i = 3; while (i < ly && isexactzero((GEN)y[i])) i++;
  ly -= i; if (!ly) return zeroser(vy,i-2);
  z = cgetg(ly+2,t_SER); z[1] = evalvalp(i-2)|evalvarn(vy)|evalsigne(1);
  for (j = 2; j <= ly+1; j++) z[j] = lcopy((GEN)y[j+i-2]);
  return z;
}
/* typ(y) == RFRAC, x polynomial in same variable or "scalar" */
static GEN
add_rfrac_scal(GEN y, GEN x)
{
  GEN p1,num, z = cgetg(3,t_RFRAC);
  pari_sp tetpil, av;

  p1 = gmul(x,(GEN)y[2]); tetpil = avma;
  num = gadd(p1,(GEN)y[1]);
  av = avma;
  p1 = content((GEN)y[2]);
  if (!gcmp1(p1))
  {
    p1 = ggcd(p1, content(num));
    if (!gcmp1(p1))
    {
      tetpil = avma;
      z[1] = ldiv(num, p1);
      z[2] = ldiv((GEN)y[2], p1);
      gerepilecoeffssp((pari_sp)z,tetpil,z+1,2); return z;
    }
  }
  avma = av;
  z[1]=lpile((pari_sp)z,tetpil, num);
  z[2]=lcopy((GEN)y[2]); return z;
}

/* x "scalar", ty != t_MAT and non-scalar */
static GEN
add_scal(GEN y, GEN x, long ty, long vy)
{
  long tx;
  switch(ty)
  {
    case t_POL: return add_pol_scal(y, x, vy);
    case t_SER: return add_ser_scal(y, x, vy);
    case t_RFRAC: return add_rfrac_scal(y, x);
    case t_VEC: case t_COL:
      tx = typ(x);
      if (!is_matvec_t(tx) && isexactzero(x)) return gcopy(y);
      break;
  }
  err(operf,"+",x,y);
  return NULL; /* not reached */
}

static GEN
addfrac(GEN x, GEN y)
{
  GEN x1 = (GEN)x[1], x2 = (GEN)x[2], z = cgetg(3,t_FRAC);
  GEN y1 = (GEN)y[1], y2 = (GEN)y[2], p1, r, n, d, delta;

  delta = gcdii(x2,y2);
  if (is_pm1(delta))
  { /* numerator is non-zero */
    z[1] = lpileuptoint((pari_sp)z, addii(mulii(x1,y2), mulii(y1,x2)));
    z[2] = lmulii(x2,y2); return z;
  }
  x2 = diviiexact(x2,delta);
  y2 = diviiexact(y2,delta);
  n = addii(mulii(x1,y2), mulii(y1,x2));
  if (!signe(n)) { avma = (pari_sp)(z+3); return gzero; }
  d = mulii(x2, y2);
  p1 = dvmdii(n, delta, &r);
  if (r == gzero)
  {
    if (is_pm1(d)) { avma = (pari_sp)(z+3); return icopy(p1); }
    avma = (pari_sp)z;
    z[2] = licopy(d);
    z[1] = licopy(p1); return z;
  }
  p1 = gcdii(delta, r);
  if (!is_pm1(p1))
  {
    delta = diviiexact(delta, p1);
    n     = diviiexact(n, p1);
  }
  d = mulii(d,delta); avma = (pari_sp)z;
  z[1] = licopy(n);
  z[2] = licopy(d); return z;
}

static GEN
add_rfrac(GEN x, GEN y)
{
  GEN x1 = (GEN)x[1], x2 = (GEN)x[2], z = cgetg(3,t_RFRAC);
  GEN y1 = (GEN)y[1], y2 = (GEN)y[2], p1, r, n, d, delta;
  pari_sp tetpil;

  delta = ggcd(x2,y2);
  if (gcmp1(delta))
  { /* numerator is non-zero */
    z[1] = lpileupto((pari_sp)z, gadd(gmul(x1,y2), gmul(y1,x2)));
    z[2] = lmul(x2, y2); return z;
  }
  x2 = gdeuc(x2,delta);
  y2 = gdeuc(y2,delta);
  n = gadd(gmul(x1,y2), gmul(y1,x2));
  if (gcmp0(n)) return gerepileupto((pari_sp)(z+3), n);
  tetpil = avma; d = gmul(x2, y2);
  p1 = poldivrem(n, delta, &r); /* we want gcd(n,delta) */
  if (gcmp0(r))
  {
    if (lg(d) == 3) /* "constant" denominator */
    {
      d = (GEN)d[2];
           if (gcmp_1(d)) p1 = gneg(p1);
      else if (!gcmp1(d)) p1 = gdiv(p1, d);
      return gerepileupto((pari_sp)(z+3), p1);
    }
    z[1]=(long)p1; z[2]=(long)d;
    gerepilecoeffssp((pari_sp)z,tetpil,z+1,2); return z;
  }
  p1 = ggcd(delta, r);
  if (gcmp1(p1))
  {
    tetpil = avma;
    z[1] = lcopy(n);
  }
  else
  {
    delta = gdeuc(delta, p1);
    tetpil = avma;
    z[1] = ldeuc(n,p1);
  }
  z[2] = lmul(d,delta);
  gerepilecoeffssp((pari_sp)z,tetpil,z+1,2); return z;
}

GEN
gadd(GEN x, GEN y)
{
  long tx = typ(x), ty = typ(y), vx, vy, lx, ly, i, j, l;
  pari_sp av, tetpil;
  GEN z, p1;

  if (tx == ty) switch(tx) /* shortcut to generic case */
  {
    case t_INT: return addii(x,y);
    case t_REAL: return addrr(x,y);
    case t_INTMOD:  { GEN X = (GEN)x[1], Y = (GEN)y[1];
      z = cgetg(3,t_INTMOD);
      if (X==Y || egalii(X,Y))
        return add_intmod_same(z, X, (GEN)x[2], (GEN)y[2]);
      z[1] = (long)gcdii(X,Y);
      av = avma; p1 = addii((GEN)x[2],(GEN)y[2]);
      z[2] = (long)gerepileuptoint(av, remii(p1, (GEN)z[1])); return z;
    }
    case t_FRAC: return addfrac(x,y);
    case t_COMPLEX: z = cgetg(3,t_COMPLEX);
      z[2] = ladd((GEN)x[2],(GEN)y[2]);
      if (isexactzero((GEN)z[2]))
      {
        avma = (pari_sp)(z+3);
        return gadd((GEN)x[1],(GEN)y[1]);
      }
      z[1] = ladd((GEN)x[1],(GEN)y[1]);
      return z;
    case t_PADIC:
      if (!egalii((GEN)x[2],(GEN)y[2])) err(operi,"+",x,y);
      return addpp(x,y);
    case t_QUAD: z = cgetg(4,t_QUAD);
      if (!gegal((GEN)x[1],(GEN)y[1])) err(operi,"+",x,y);
      copyifstack(x[1], z[1]);
      z[2] = ladd((GEN)x[2],(GEN)y[2]);
      z[3] = ladd((GEN)x[3],(GEN)y[3]); return z;
    case t_POLMOD:
      if (gegal((GEN)x[1], (GEN)y[1]))
        return add_polmod_same((GEN)x[1], (GEN)x[2], (GEN)y[2]);
      return add_polmod((GEN)x[1], (GEN)y[1], (GEN)x[2], (GEN)y[2]);
    case t_POL:
      vx = varn(x);
      vy = varn(y);
      if (vx != vy) {
        if (varncmp(vx, vy) < 0) return add_pol_scal(x, y, vx);
        else                     return add_pol_scal(y, x, vy);
      }
      /* same variable */
      lx = lg(x);
      ly = lg(y);
      if (lx == ly) {
        z = cgetg(lx, t_POL); z[1] = x[1];
        for (i=2; i < lx; i++) z[i] = ladd((GEN)x[i],(GEN)y[i]);
        return normalizepol_i(z, lx);
      }
      if (ly < lx) {
        z = cgetg(lx,t_POL); z[1] = x[1];
        for (i=2; i < ly; i++) z[i] = ladd((GEN)x[i],(GEN)y[i]);
        for (   ; i < lx; i++) z[i] = lcopy((GEN)x[i]);
        if (!signe(x)) z = normalizepol_i(z, lx);
      } else {
        z = cgetg(ly,t_POL); z[1] = y[1];
        for (i=2; i < lx; i++) z[i] = ladd((GEN)x[i],(GEN)y[i]);
        for (   ; i < ly; i++) z[i] = lcopy((GEN)y[i]);
        if (!signe(y)) z = normalizepol_i(z, ly);
      }
      return z;
    case t_SER:
      vx = varn(x);
      vy = varn(y);
      if (vx != vy) {
        if (varncmp(vx, vy) < 0) return add_ser_scal(x, y, vx);
        else                     return add_ser_scal(y, x, vy);
      }
      l = valp(y) - valp(x);
      if (l < 0) { l = -l; swap(x,y); }
      /* valp(x) <= valp(y) */
      if (!signe(x)) return gcopy(x);
      lx = lg(x);
      ly = signe(y)? lg(y): 2;
      ly += l; if (lx < ly) ly = lx;
      av = avma;
      z = cgetg(ly,t_SER);
      if (l)
      {
        if (l > lx-2) { avma = av; return gcopy(x); }
        for (i=2; i<=l+1; i++) z[i] = lcopy((GEN)x[i]);
        for (   ; i < ly; i++) z[i] = ladd((GEN)x[i],(GEN)y[i-l]);
        z[1] = x[1]; return z;
      }
      for (i = 2; i < ly; i++)
      {
        p1 = gadd((GEN)x[i],(GEN)y[i]);
        if (!isexactzero(p1))
        {
          l = i-2; stackdummy(z,l); z += l;
          z[0] = evaltyp(t_SER) | evallg(ly-l);
          z[1] = evalvalp(valp(x)+i-2) | evalsigne(1) | evalvarn(vx);
          for (j=i+1; j<ly; j++) z[j-l] = ladd((GEN)x[j],(GEN)y[j]);
          z[2] = (long)p1; return z;
        }
        avma = (pari_sp)z;
      }
      avma = av;
      return zeroser(vx, ly-2 + valp(y));
    case t_RFRAC:
      vx = gvar(x);
      vy = gvar(y);
      if (vx != vy) {
        if (varncmp(vx, vy) < 0) return add_rfrac_scal(x, y);
        else                     return add_rfrac_scal(y, x);
      }
      return add_rfrac(x,y);
    case t_VEC: case t_COL: case t_MAT:
      ly = lg(y);
      if (ly != lg(x)) err(operi,"+",x,y);
      z = cgetg(ly, ty);
      for (i = 1; i < ly; i++) z[i] = ladd((GEN)x[i],(GEN)y[i]);
      return z;

    default: err(operf,"+",x,y);
  }
  /* tx != ty */
  if (tx > ty) { swap(x,y); lswap(tx,ty); }

  if (is_const_t(ty)) switch(tx) /* tx < ty, is_const_t(tx) && is_const_t(ty) */
  {
    case t_INT:
      switch(ty)
      {
        case t_REAL: return addir(x,y);
        case t_INTMOD:
          z = cgetg(3, t_INTMOD);
          return add_intmod_same(z, (GEN)y[1], (GEN)y[2], modii(x, (GEN)y[1]));
        case t_FRAC: z = cgetg(3,t_FRAC);
          z[1] = lpileuptoint((pari_sp)z, addii((GEN)y[1], mulii((GEN)y[2],x)));
          z[2] = licopy((GEN)y[2]); return z;
        case t_COMPLEX: return addRc(x, y);
        case t_PADIC: return addQp(x,y);
        case t_QUAD: return addRq(x, y);
      }

    case t_REAL:
      switch(ty)
      {
        case t_FRAC:
          if (!signe(y[1])) return rcopy(x);
          if (!signe(x))
          {
            lx = expi((GEN)y[1]) - expi((GEN)y[2]) - expo(x);
            if (lx < 0) return rcopy(x);
            lx >>= TWOPOTBITS_IN_LONG;
            return rdivii((GEN)y[1],(GEN)y[2], lx+3);
          }
          av=avma; z=addir((GEN)y[1],mulir((GEN)y[2],x)); tetpil=avma;
          return gerepile(av,tetpil,divri(z,(GEN)y[2]));
        case t_COMPLEX: return addRc(x, y);
        case t_QUAD: return gcmp0(y)? rcopy(x): addqf(y, x, lg(x));

        default: err(operf,"+",x,y);
      }

    case t_INTMOD:
      switch(ty)
      {
        case t_FRAC: { GEN X = (GEN)x[1];
          z = cgetg(3, t_INTMOD);
          p1 = modii(mulii((GEN)y[1], Fp_inv((GEN)y[2],X)), X);
          return add_intmod_same(z, X, p1, (GEN)x[2]);
        }
        case t_COMPLEX: return addRc(x, y);
        case t_PADIC: { GEN X = (GEN)x[1];
          z = cgetg(3, t_INTMOD);
          return add_intmod_same(z, X, (GEN)x[2], ptolift(y, X));
        }
        case t_QUAD: return addRq(x, y);
      }

    case t_FRAC:
      switch (ty)
      {
        case t_COMPLEX: return addRc(x, y);
        case t_PADIC: return addQp(x,y);
        case t_QUAD: return addRq(x, y);
      }

    case t_COMPLEX:
      switch(ty)
      {
        case t_PADIC:
          return Zp_nosquare_m1((GEN)y[2])? addRc(y, x): addTp(x, y);
        case t_QUAD:
          lx = precision(x); if (!lx) err(operi,"+",x,y);
          return gcmp0(y)? rcopy(x): addqf(y, x, lx);
      }

    case t_PADIC: /* ty == t_QUAD */
      return (kro_quad((GEN)y[1],(GEN)x[2]) == -1)? addRq(x, y): addTp(y, x);
  }
  /* tx < ty, !is_const_t(y) */
  if (ty == t_MAT) {
    if (is_matvec_t(tx)) err(operf,"+",x,y);
    if (isexactzero(x)) return gcopy(y);
    return gaddmat(x,y);
  }
  if (ty == t_POLMOD) /* is_const_t(tx) in this case */
    return add_polmod_scal((GEN)y[1], (GEN)y[2], x);
  vy = gvar(y);
  if (is_scalar_t(tx))  {
    if (tx == t_POLMOD)
    {
      vx = varn(x[1]);
      if (vx == vy) y = gmod(y, (GEN)x[1]); /* error if ty == t_SER */
      else
        if (varncmp(vx,vy) > 0) return add_scal(y, x, ty, vy);
      return add_polmod_scal((GEN)x[1], (GEN)x[2], y);
    }
    return add_scal(y, x, ty, vy);
  }
  /* x and y are not scalars, ty != t_MAT */
  vx = gvar(x);
  if (vx != vy) { /* x or y is treated as a scalar */
    if (is_vec_t(tx) || is_vec_t(ty)) err(operf,"+",x,y);
    return (varncmp(vx, vy) < 0)? add_scal(x, y, tx, vx)
                                : add_scal(y, x, ty, vy);
  }
  /* vx = vy */
  switch(tx)
  {
    case t_POL:
      switch (ty)
      {
	case t_SER:
	  if (isexactzero(x)) return gcopy(y);
          ly = signe(y)? lg(y): 3;
	  i = ly + valp(y) - polvaluation(x, NULL);
	  if (i < 3) return gcopy(y);

	  p1 = greffe(x,i,0); y = gadd(p1,y);
          free(p1); return y;
	
        case t_RFRAC: return add_rfrac_scal(y, x);
      }
      break;

    case t_SER:
      switch(ty)
      {
	case t_RFRAC:
	  if (isexactzero(y)) return gcopy(x);

	  l = valp(x) - gval(y,vy); l += gcmp0(x)? 3: lg(x);
	  if (l < 3) return gcopy(x);

	  av = avma; p1 = (GEN)y[2]; ty = typ(p1);
          if (!is_scalar_t(ty)) p1 = greffe(p1,l,1);
          return gerepileupto(av, gadd(gdiv((GEN)y[1], p1), x));
      }
      break;
  }
  err(operf,"+",x,y);
  return NULL; /* not reached */
}

GEN
gaddsg(long x, GEN y)
{
  long ty = typ(y);
  GEN z;

  switch(ty)
  {
    case t_INT:  return addsi(x,y);
    case t_REAL: return addsr(x,y);
    case t_INTMOD:
      z = cgetg(3, t_INTMOD);
      return add_intmod_same(z, (GEN)y[1], (GEN)y[2], modsi(x, (GEN)y[1]));
    case t_FRAC: z = cgetg(3,t_FRAC);
      z[1] = lpileuptoint((pari_sp)z, addii((GEN)y[1], mulis((GEN)y[2],x)));
      z[2] = licopy((GEN)y[2]); return z;

    default: return gadd(stoi(x), y);
  }
}

/********************************************************************/
/**                                                                **/
/**                        MULTIPLICATION                          **/
/**                                                                **/
/********************************************************************/
GEN
fix_rfrac_if_pol(GEN x, GEN y)
{
  pari_sp av = avma;
  y = simplify(y);
  if (gcmp1(y)) { avma = av; return x; }
  if (typ(y) != t_POL)
  {
    if (typ(x) != t_POL || varncmp(gvar2(y), varn(x)) > 0)
      return gdiv(x,y);
  }
  else if (varncmp(varn(y), varn(x)) > 0) return gdiv(x,y);
  avma = av; return NULL;
}
/* (n/d) * x */
static GEN
mul_rfrac_scal(GEN n, GEN d, GEN x)
{
  GEN p1, z, cx, cn, cd;
  long vx, vn, vd;
  pari_sp av = avma, tetpil;

  if (gcmp0(x)) {
    if (isexactzero(x)) {
      vn = gvar(n);
      vd = gvar(d); return zeropol(varncmp(vn,vd) > 0? vd: vn);
    }
    return gerepileupto(av, gdiv(gmul(x,n), d));
  }
  if (gcmp0(n)) return gerepileupto(av, gdiv(gmul(x,n), d));
  vx = gvar(x);
  vn = gvar(n);
  vd = gvar(d);
  z = cgetg(3, t_RFRAC);
  if (varncmp(vx, vd) > 0 || varncmp(vx, vn) > 0) { cx = x; x = gun; }
  else
  {
    long td;
    p1 = ggcd(x,d);
    while (typ(p1) == t_POL && lg(p1) == 3) p1 = (GEN)p1[2];
    if (typ(p1) == t_POL && lg(p1) > 3) { x=gdeuc(x,p1); d=gdeuc(d,p1); }
    while (typ(x) == t_POL && lg(x) == 3) x = (GEN)x[2];
    while ((td = typ(d)) == t_POL && lg(d) == 3) d = (GEN)d[2];
    if (is_scalar_t(td))
      return gerepileupto(av, gdiv(gmul(x,n), d));
    x = to_primitive(x, &cx);
  }
  n = to_primitive(n, &cn); if (x != gun) n = gmul(n,x);
  d = to_primitive(d, &cd);
  cx = gdiv(gmul(cx,cn), cd);
  if (typ(cx) == t_POL)
  {
    cd = denom(content(cx));
    cn = gmul(cx, cd);
  }
  else
  {
    cn = numer(cx);
    cd = denom(cx);
  }
  tetpil = avma;
  z[2] = lmul(d, cd);
  z[1] = lmul(n, cn);
  p1 = fix_rfrac_if_pol((GEN)z[1],(GEN)z[2]);
  if (p1) return gerepileupto(av, p1);
  gerepilecoeffssp((pari_sp)z,tetpil,z+1,2); return z;
}
/* (x1/x2) * (y1/y2) */
static GEN
mul_rfrac(GEN x1, GEN x2, GEN y1, GEN y2)
{
  GEN z = cgetg(3,t_RFRAC), p1;
  pari_sp tetpil;

  p1 = ggcd(x1, y2); if (!gcmp1(p1)) { x1 = gdiv(x1,p1); y2 = gdiv(y2,p1); }
  p1 = ggcd(x2, y1); if (!gcmp1(p1)) { x2 = gdiv(x2,p1); y1 = gdiv(y1,p1); }
  tetpil = avma;
  z[2] = lmul(x2,y2);
  z[1] = lmul(x1,y1);
  p1 = fix_rfrac_if_pol((GEN)z[1],(GEN)z[2]);
  if (p1) return gerepileupto((pari_sp)(z+3), p1);
  gerepilecoeffssp((pari_sp)z,tetpil,z+1,2); return z;
}

/* Mod(y, Y) * x,  assuming x scalar */
static GEN
mul_polmod_scal(GEN Y, GEN y, GEN x)
{
  GEN z = cgetg(3,t_POLMOD); copyifstack(Y, z[1]);
  z[2] = lmul(x,y); return z;
}
/* Mod(x,X) * Mod(y,X) */
static GEN
mul_polmod_same(GEN X, GEN x, GEN y)
{
  GEN t, z = cgetg(3,t_POLMOD);
  pari_sp av;
  long v;
  copyifstack(X, z[1]); av = avma;
  t = gmul(x, y);
  /* gmod(t, (GEN)z[1])) optimised */
  if (typ(t) == t_POL  && (v = varn(X)) == varn(t) && lg(t) >= lg(X))
    z[2] = lpileupto(av, RgX_divrem(t, X, ONLY_REM));
  else
    z[2] = (long)t;
  return z;
}
/* Mod(x,X) * Mod(y,Y) */
static GEN
mul_polmod(GEN X, GEN Y, GEN x, GEN y)
{
  static long T[3]={ evaltyp(t_POLMOD) | _evallg(3),0,0 };
  long vx = varn(X), vy = varn(Y);
  GEN z = cgetg(3,t_POLMOD);
  pari_sp av;

  if (vx==vy) {
    z[1] = (long)srgcd(X,Y); av = avma;
    z[2] = lpileupto(av, gmod(gmul(x, y), (GEN)z[1])); return z;
  }
  if (varncmp(vx, vy) < 0)
  { copyifstack(X, z[1]); T[1]=(long)Y; T[2]=(long)y; y = T; }
  else
  { copyifstack(Y, z[1]); T[1]=(long)X; T[2]=(long)x; x = T; }
  z[2] = lmul(x, y); return z;
}

static GEN
mul_ser_scal(GEN y, GEN x) {
  long ly, i;
  GEN z;
  if (isexactzero(x)) { long vy = varn(y); return zeropol(vy); }
  if (!signe(y)) return gcopy(y);
  ly = lg(y); z = cgetg(ly,t_SER); z[1] = y[1];
  for (i = 2; i < ly; i++) z[i] = lmul(x,(GEN)y[i]);
  return normalize(z);
}
static GEN
mul_scal(GEN y, GEN x, long ty)
{
  switch(ty)
  {
    case t_POL: return RgX_Rg_mul(y, x);
    case t_SER: return mul_ser_scal(y, x);
    case t_RFRAC: return mul_rfrac_scal((GEN)y[1],(GEN)y[2], x);
    case t_QFI: case t_QFR:
      if (typ(x) == t_INT && gcmp1(x)) return gcopy(y); /* fall through */
  }
  err(operf,"*",x,y);
  return NULL; /* not reached */
}

/* compatible t_VEC * t_COL, l = lg(x) = lg(y) */
static GEN
VC_mul(GEN x, GEN y, long l)
{
  pari_sp av = avma;
  GEN z = gzero;
  long i;
  for (i=1; i<l; i++)
  {
    GEN c = (GEN)y[i];
    if (!isexactzeroscalar(c)) z = gadd(z, gmul((GEN)x[i], c));
  }
  return gerepileupto(av,z);
}
/* compatible t_MAT * t_COL, l = lg(x) = lg(y), lz = l>1? lg(x[1]): 1 */
static GEN
MC_mul(GEN x, GEN y, long l, long lz)
{
  GEN z = cgetg(lz,t_COL);
  long i, j;
  for (i=1; i<lz; i++)
  {
    pari_sp av = avma;
    GEN t = gzero;
    for (j=1; j<l; j++)
    {
      GEN c = (GEN)y[j];
      if (!isexactzeroscalar(c)) t = gadd(t, gmul(gcoeff(x,i,j), c));
    }
    z[i] = lpileupto(av,t);
  }
  return z;
}
/* x,y COMPLEX */
static GEN
mulcc(GEN x, GEN y)
{
  GEN p1, p2, z = cgetg(3,t_COMPLEX);
  pari_sp tetpil, av2, av = avma;
  p1 = gmul((GEN)x[1],(GEN)y[1]);
  p2 = gmul((GEN)x[2],(GEN)y[2]);
  x = gadd((GEN)x[1],(GEN)x[2]);
  y = gadd((GEN)y[1],(GEN)y[2]);
  y = gmul(x,y); x = gadd(p1,p2);
  tetpil = avma;
  z[1] = lsub(p1,p2); av2 = avma;
  z[2] = lsub(y,x);
  if (isexactzero((GEN)z[2]))
  {
    avma = av2;
    return gerepileupto((pari_sp)(z+3), (GEN)z[1]);
  }
  gerepilecoeffssp(av,tetpil, z+1,2); return z;
}
/* x,y PADIC */
static GEN
mulpp(GEN x, GEN y) {
  long l = valp(x) + valp(y);
  pari_sp av;
  GEN z, t;
  if (!egalii((GEN)x[2],(GEN)y[2])) err(operi,"*",x,y);
  if (!signe(x[4])) return zeropadic((GEN)x[2], l);
  if (!signe(y[4])) return zeropadic((GEN)x[2], l);

  t = (precp(x) > precp(y))? y: x;
  z = cgetp(t); setvalp(z,l); av = avma;
  remiiz(mulii((GEN)x[4],(GEN)y[4]), (GEN)t[3], (GEN)z[4]);
  avma = av; return z;
}
/* x,y QUAD */
static GEN
mulqq(GEN x, GEN y) {
  GEN p1,p2,p3,p4, z = cgetg(4,t_QUAD);
  pari_sp av, tetpil;
  p1 = (GEN)x[1];
  if (!gegal(p1, (GEN)y[1])) err(operi,"*",x,y);

  copyifstack(p1, z[1]); av = avma;
  p2 = gmul((GEN)x[2],(GEN)y[2]);
  p3 = gmul((GEN)x[3],(GEN)y[3]);
  p4 = gmul(gneg_i((GEN)p1[2]),p3);

  if (gcmp0((GEN)p1[3]))
  {
    tetpil = avma;
    z[2] = lpile(av,tetpil,gadd(p4,p2));
    av = avma;
    p2 = gmul((GEN)x[2],(GEN)y[3]);
    p3 = gmul((GEN)x[3],(GEN)y[2]); tetpil = avma;
    z[3] = lpile(av,tetpil,gadd(p2,p3)); return z;
  }

  p1 = gadd(gmul((GEN)x[2],(GEN)y[3]), gmul((GEN)x[3],(GEN)y[2]));
  tetpil = avma;
  z[2] = ladd(p2,p4);
  z[3] = ladd(p1,p3);
  gerepilecoeffssp(av,tetpil,z+2,2); return z;
}

GEN
gmul(GEN x, GEN y)
{
  long tx, ty, lx, ly, vx, vy, i, j, l;
  pari_sp av, tetpil;
  GEN z, p1, p2;

  if (x == y) return gsqr(x);
  tx = typ(x); ty = typ(y);
  if (tx == ty) switch(tx)
  {
    case t_INT: return mulii(x,y);
    case t_REAL: return mulrr(x,y);
    case t_INTMOD: { GEN X = (GEN)x[1], Y = (GEN)y[1];
      z = cgetg(3,t_INTMOD); 
      if (X==Y || egalii(X,Y))
        return mul_intmod_same(z, X, (GEN)x[2], (GEN)y[2]);
      z[1] = (long)gcdii(X,Y); av = avma; p1 = mulii((GEN)x[2],(GEN)y[2]);
      z[2] = (long)gerepileuptoint(av, remii(p1, (GEN)z[1])); return z;
    }
    case t_FRAC:
    {
      GEN x1 = (GEN)x[1], x2 = (GEN)x[2];
      GEN y1 = (GEN)y[1], y2 = (GEN)y[2];
      z=cgetg(3,t_FRAC);
      p1 = gcdii(x1, y2);
      if (!is_pm1(p1)) { x1 = diviiexact(x1,p1); y2 = diviiexact(y2,p1); }
      p1 = gcdii(x2, y1);
      if (!is_pm1(p1)) { x2 = diviiexact(x2,p1); y1 = diviiexact(y1,p1); }
      tetpil = avma;
      z[2] = lmulii(x2,y2);
      z[1] = lmulii(x1,y1);
      fix_frac_if_int_GC(z,tetpil); return z;
    }
    case t_COMPLEX: return mulcc(x, y);
    case t_PADIC: return mulpp(x, y);
    case t_QUAD: return mulqq(x, y);
    case t_POLMOD:
      if (gegal((GEN)x[1], (GEN)y[1]))
        return mul_polmod_same((GEN)x[1], (GEN)x[2], (GEN)y[2]);
      return mul_polmod((GEN)x[1], (GEN)y[1], (GEN)x[2], (GEN)y[2]);
    case t_POL:
      vx = varn(x);
      vy = varn(y);
      if (vx != vy) {
        if (varncmp(vx, vy) < 0) return RgX_Rg_mul(x, y);
        else                     return RgX_Rg_mul(y, x);
      }
      return RgX_mul(x, y);

    case t_SER: {
      long mix, miy;
      vx = varn(x);
      vy = varn(y);
      if (vx != vy) {
        if (varncmp(vx, vy) < 0) return mul_ser_scal(x, y);
        else                     return mul_ser_scal(y, x);
      }
      if (gcmp0(x) || gcmp0(y)) return zeroser(vx, valp(x)+valp(y));
      lx = lg(x); if (lx > lg(y)) { lx = lg(y); swap(x, y); }
      z = cgetg(lx,t_SER);
      z[1] = evalvalp(valp(x)+valp(y)) | evalvarn(vx) | evalsigne(1);
      if (lx > 200) /* threshold for 32bit coeffs: 400, 512 bits: 100 */
      {
        long ly;
        y = RgX_mul(ser_to_pol_i(x, lx), ser_to_pol_i(y, lx));
        ly = lg(y);
        if (ly >= lx) {
          for (i = 2; i < lx; i++) z[i] = y[i];
        } else {
          for (i = 2; i < ly; i++) z[i] = y[i];
          for (     ; i < lx; i++) z[i] = zero;
        }
        return gerepilecopy((pari_sp)(z + lx), z);
      }
      x += 2; y += 2; z += 2; lx -= 3;
      p2 = (GEN)gpmalloc((lx+1)*sizeof(long));
      mix = miy = 0;
      for (i=0; i<=lx; i++)
      {
        p2[i] = !isexactzero((GEN)y[i]); if (p2[i]) miy = i;
        if (!isexactzero((GEN)x[i])) mix = i;
        p1 = gzero; av = avma;
        for (j=i-mix; j<=min(i,miy); j++)
          if (p2[j]) p1 = gadd(p1, gmul((GEN)y[j],(GEN)x[i-j]));
        z[i] = lpileupto(av,p1);
      }
      z -= 2; /* back to normalcy */
      free(p2); return normalize(z);
    }
    case t_QFI: return compimag(x,y);
    case t_QFR: return compreal(x,y);
    case t_RFRAC: return mul_rfrac((GEN)x[1],(GEN)x[2], (GEN)y[1],(GEN)y[2]);
    case t_MAT:
      ly = lg(y); if (ly == 1) return cgetg(ly,t_MAT);
      lx = lg(x);
      if (lx != lg(y[1])) err(operi,"*",x,y);
      z = cgetg(ly,t_MAT);
      l = (lx == 1)? 1: lg(x[1]);
      for (j=1; j<ly; j++) z[j] = (long)MC_mul(x, (GEN)y[j], lx, l);
      return z;

    case t_VECSMALL: /* multiply as permutation. cf perm_mul */
      l = lg(x); z = cgetg(l, t_VECSMALL);
      if (l != lg(y)) break;
      for (i=1; i<l; i++)
      {
        long yi = y[i];
        if (yi < 1 || yi >= l) err(operf,"*",x,y);
        z[i] = x[yi];
      }
      return z;


    default:
      err(operf,"*",x,y);
  }
  /* tx != ty */
  if (is_const_t(ty) && is_const_t(tx))  {
    if (tx > ty) { swap(x,y); lswap(tx,ty); }
    switch(tx) {
    case t_INT:
      switch(ty)
      {
        case t_REAL: return mulir(x,y);
        case t_INTMOD:
          z = cgetg(3, t_INTMOD);
          return mul_intmod_same(z, (GEN)y[1], (GEN)y[2], modii(x, (GEN)y[1]));
        case t_FRAC:
          if (!signe(x)) return gzero;
          z=cgetg(3,t_FRAC);
          p1 = gcdii(x,(GEN)y[2]);
          if (is_pm1(p1))
          {
            avma = (pari_sp)z;
            z[2] = licopy((GEN)y[2]);
            z[1] = lmulii((GEN)y[1], x);
          }
          else
          {
            x = diviiexact(x,p1); tetpil = avma;
            z[2] = (long)diviiexact((GEN)y[2], p1);
            z[1] = lmulii((GEN)y[1], x);
            fix_frac_if_int_GC(z,tetpil);
          }
          return z;
        case t_COMPLEX: return mulRc(x, y);
        case t_PADIC: return signe(x)? mulTp(x, y): gzero;
        case t_QUAD: return mulRq(x,y);
      }

    case t_REAL:
      switch(ty)
      {
        case t_FRAC:
          if (!signe(y[1])) return gzero;
          av = avma;
          return gerepileuptoleaf(av, divri(mulri(x,(GEN)y[1]), (GEN)y[2]));
        case t_COMPLEX: return mulRc(x, y);
        case t_QUAD: return mulqf(y, x, lg(x));
        default: err(operf,"*",x,y);
      }

    case t_INTMOD:
      switch(ty)
      {
        case t_FRAC: { GEN X = (GEN)x[1];
          z = cgetg(3, t_INTMOD); p1 = modii(mulii((GEN)y[1], (GEN)x[2]), X);
          return div_intmod_same(z, X, p1, remii((GEN)y[2], X)); 
        }
        case t_COMPLEX: return mulRc(x, y);
        case t_PADIC: { GEN X = (GEN)x[1];
          z = cgetg(3, t_INTMOD);
          return mul_intmod_same(z, X, (GEN)x[2], ptolift(y, X));
        }
        case t_QUAD: return mulRq(x, y);
      }

    case t_FRAC:
      switch(ty)
      {
        case t_COMPLEX: return mulRc(x, y);
        case t_PADIC: return signe(x[1])? mulTp(x, y): gzero;
        case t_QUAD: return mulRq(x, y);
      }

    case t_COMPLEX:
      switch(ty)
      {
        case t_PADIC:
          return Zp_nosquare_m1((GEN)y[2])? mulRc(y, x): mulTp(x, y);
        case t_QUAD:
          lx = precision(x); if (!lx) err(operi,"*",x,y);
          return mulqf(y, x, lx);
      }

    case t_PADIC: /* ty == t_QUAD */
      return (kro_quad((GEN)y[1],(GEN)x[2])== -1)? mulRq(x, y): mulTp(y, x);
    }
  }

  if (is_matvec_t(ty))
  {
    ly = lg(y);
    if (!is_matvec_t(tx))
    {
      if (is_noncalc_t(tx)) err(operf, "*",x,y); /* necessary if ly = 1 */
      z = cgetg(ly,ty);
      for (i=1; i<ly; i++) z[i] = lmul(x,(GEN)y[i]);
      return z;
    }
    lx = lg(x);

    switch(tx)
    {
      case t_VEC:
        switch(ty)
        {
          case t_COL:
            if (lx != ly) err(operi,"*",x,y);
            return VC_mul(x, y, lx);

          case t_MAT:
            if (ly == 1) return cgetg(1,t_VEC);
            if (lx != lg(y[1])) err(operi,"*",x,y);
            z = cgetg(ly, t_VEC);
            for (i=1; i<ly; i++) z[i] = (long)VC_mul(x, (GEN)y[i], lx);
            return z;
        }
        break;

      case t_COL:
        switch(ty)
        {
          case t_VEC:
            z = cgetg(ly,t_MAT);
            for (i=1; i<ly; i++)
            {
              p1 = gmul((GEN)y[i],x);
              if (typ(p1) != t_COL) err(operi,"*",x,y);
              z[i] = (long)p1;
            }
            return z;

          case t_MAT:
            if (ly != 1 && lg(y[1]) != 2) err(operi,"*",x,y);
            z = cgetg(ly,t_MAT);
            for (i=1; i<ly; i++) z[i] = lmul(gcoeff(y,1,i),x);
            return z;
        }
        break;

      case t_MAT:
        switch(ty)
        {
          case t_VEC:
            if (lx != 2) err(operi,"*",x,y);
            z = cgetg(ly,t_MAT);
            for (i=1; i<ly; i++) z[i] = lmul((GEN)y[i],(GEN)x[1]);
            return z;

          case t_COL:
            if (lx != ly) err(operi,"*",x,y);
            return MC_mul(x, y, lx, (lx == 1)? 1: lg(x[1]));
        }
    }
  }
  if (is_matvec_t(tx))
  {
    if (is_noncalc_t(ty)) err(operf, "*",x,y); /* necessary if lx = 1 */
    lx = lg(x); z = cgetg(lx,tx);
    for (i=1; i<lx; i++) z[i] = lmul(y,(GEN)x[i]);
    return z;
  }
  if (tx > ty) { swap(x,y); lswap(tx,ty); }
  /* tx < ty, !ismatvec(x and y) */

  if (ty == t_POLMOD) /* is_const_t(tx) in this case */
    return mul_polmod_scal((GEN)y[1], (GEN)y[2], x);
  if is_scalar_t(tx) {
    if (tx == t_POLMOD) {
      vx = varn(x[1]);
      vy = gvar(y);
      if (vx != vy) {
        if (varncmp(vx,vy) > 0) return mul_scal(y, x, ty);
        return mul_polmod_scal((GEN)x[1], (GEN)x[2], y);
      }
      /* error if ty == t_SER */
      av = avma; y = gmod(y, (GEN)x[1]);
      return gerepileupto(av, mul_polmod_same((GEN)x[1], (GEN)x[2], y));
    }
    return mul_scal(y, x, ty);
  }

  /* x and y are not scalars, nor matvec */
  vx = gvar(x);
  vy = gvar(y);
  if (vx != vy) { /* x or y is treated as a scalar */
    return (varncmp(vx, vy) < 0)? mul_scal(x, y, tx)
                                : mul_scal(y, x, ty);
  }
  /* vx = vy */
  switch(tx)
  {
    case t_POL:
      switch (ty)
      {
	case t_SER:
	  if (gcmp0(x)) return zeropol(vx);
	  if (gcmp0(y)) return zeroser(vx, valp(y) + polvaluation(x,NULL));
	  p1 = greffe(x,lg(y),0);
          p2 = gmul(p1,y); free(p1); return p2;
	
        case t_RFRAC: return mul_rfrac_scal((GEN)y[1],(GEN)y[2], x);
      }
      break;
	
    case t_SER:
      switch (ty)
      {
	case t_RFRAC:
	  if (gcmp0(y)) return zeropol(vx);
	  if (gcmp0(x)) return zeroser(vx, valp(x) + gval(y,vx));
	  av = avma; return gerepileupto(av, gdiv(gmul((GEN)y[1],x), (GEN)y[2]));
      }
      break;
  }
  err(operf,"*",x,y);
  return NULL; /* not reached */
}

int
ff_poltype(GEN *x, GEN *p, GEN *pol)
{
  GEN Q, P = *x, pr,p1,p2,y;
  long i, lx;

  if (!signe(P)) return 0;
  lx = lg(P); Q = *pol;
  for (i=2; i<lx; i++)
  {
    p1 = (GEN)P[i]; if (typ(p1) != t_POLMOD) {Q=NULL;break;}
    p2 = (GEN)p1[1];
    if (Q==NULL) { Q = p2; if (degpol(Q) <= 0) return 0; }
    else if (p2 != Q)
    {
      if (!gegal(p2, Q))
      {
        if (DEBUGMEM) err(warner,"different modulus in ff_poltype");
        return 0;
      }
      if (DEBUGMEM > 2) err(warner,"different pointers in ff_poltype");
    }
  }
  if (Q) {
    *x = P = to_Kronecker(P, Q);
    *pol = Q; lx = lg(P);
  }
  pr = *p; y = cgetg(lx, t_POL);
  for (i=lx-1; i>1; i--)
  {
    p1 = (GEN)P[i];
    switch(typ(p1))
    {
      case t_INTMOD: break;
      case t_INT:
        if (*p) p1 = modii(p1, *p);
        y[i] = (long)p1; continue;
      default:
        return (Q && !pr)? 1: 0;
    }
    p2 = (GEN)p1[1];
    if (pr==NULL) pr = p2;
    else if (p2 != pr)
    {
      if (!egalii(p2, pr))
      {
        if (DEBUGMEM) err(warner,"different modulus in ff_poltype");
        return 0;
      }
      if (DEBUGMEM > 2) err(warner,"different pointers in ff_poltype");
    }
    y[i] = p1[2];
  }
  y[1] = P[1];
  *x = y; *p = pr; return (Q || pr);
}

GEN
gsqr(GEN x)
{
  long tx=typ(x), lx, i, j, l;
  pari_sp av, tetpil;
  GEN z, p1, p2, p3, p4;

  if (is_scalar_t(tx))
    switch(tx)
    {
      case t_INT: return sqri(x);
      case t_REAL: return mulrr(x,x);
      case t_INTMOD: { GEN X = (GEN)x[1];
        z = cgetg(3,t_INTMOD);
        z[2] = lpileuptoint((pari_sp)z, remii(sqri((GEN)x[2]), X));
        icopyifstack(X,z[1]); return z;
      }
      case t_FRAC: z=cgetg(3,t_FRAC);
	z[1]=lsqri((GEN)x[1]);
	z[2]=lsqri((GEN)x[2]); return z;

      case t_COMPLEX:
        if (isexactzero((GEN)x[1])) {
          av = avma;
          return gerepileupto(av, gneg(gsqr((GEN)x[2])));
        }
	z = cgetg(3,t_COMPLEX); av = avma;
	p1 = gadd((GEN)x[1],(GEN)x[2]);
	p2 = gadd((GEN)x[1], gneg_i((GEN)x[2]));
	p3 = gmul((GEN)x[1],(GEN)x[2]);
	tetpil = avma;
	z[1] = lmul(p1,p2);
        z[2] = lshift(p3,1); gerepilecoeffssp(av,tetpil,z+1,2); return z;
	
      case t_PADIC:
	z = cgetg(5,t_PADIC);
	i = (egalii((GEN)x[2], gdeux) && signe(x[4]))? 1: 0;
        if (i && precp(x) == 1) i = 2; /* (1 + O(2))^2 = 1 + O(2^3) */
        z[1] = evalprecp(precp(x)+i) | evalvalp(valp(x) << 1);
	icopyifstack(x[2], z[2]);
        z[3] = lshifti((GEN)x[3], i); av = avma;
	z[4] = lpileuptoint(av, remii(sqri((GEN)x[4]), (GEN)z[3]));
	return z;
	
      case t_QUAD: z = cgetg(4,t_QUAD);
	p1 = (GEN)x[1];
        copyifstack(p1,z[1]); av = avma;
	p2 = gsqr((GEN)x[2]);
        p3 = gsqr((GEN)x[3]);
	p4 = gmul(gneg_i((GEN)p1[2]),p3);

	if (gcmp0((GEN)p1[3]))
	{
	  tetpil = avma;
	  z[2] = lpile(av,tetpil,gadd(p4,p2));
	  av = avma;
          p2 = gmul((GEN)x[2],(GEN)x[3]); tetpil = avma;
	  z[3] = lpile(av,tetpil,gmul2n(p2,1)); return z;
	}

	p1 = gmul2n(gmul((GEN)x[2],(GEN)x[3]), 1);
        tetpil = avma;
	z[2] = ladd(p2,p4);
        z[3] = ladd(p1,p3);
	gerepilecoeffssp(av,tetpil,z+2,2); return z;

      case t_POLMOD:
        z=cgetg(3,t_POLMOD); copyifstack(x[1],z[1]);
	av=avma; p1=gsqr((GEN)x[2]); tetpil=avma;
        z[2]=lpile(av,tetpil, grem(p1,(GEN)z[1]));
	return z;
    }

  switch(tx)
  {
    case t_POL:
    {
      GEN a = x, p = NULL, pol = NULL;
      long vx = varn(x);
      av = avma;
      if (ff_poltype(&x,&p,&pol))
      {
        z = FpX_sqr(x, p);
        if (p) z = FpX_to_mod(z,p);
        if (pol) z = from_Kronecker(z,pol);
        z = gerepileupto(av, z);
      }
      else { avma = av; z = RgX_sqr(a); }
      setvarn(z, vx); return z;
    }

    case t_SER:
    {
      long mi;
      if (gcmp0(x)) return zeroser(varn(x), 2*valp(x));
      lx = lg(x); z = cgetg(lx, t_SER);
      z[1] = evalsigne(1) | evalvalp(2*valp(x)) | evalvarn(varn(x));
      x += 2; z += 2; lx -= 3;
      p2 = (GEN)gpmalloc((lx+1)*sizeof(long));
      mi = 0;
      for (i=0; i<=lx; i++)
      {
	p2[i] = !isexactzero((GEN)x[i]); if (p2[i]) mi = i;
        p1=gzero; av=avma; l=((i+1)>>1) - 1;
        for (j=i-mi; j<=min(l,mi); j++)
          if (p2[j] && p2[i-j]) p1 = gadd(p1, gmul((GEN)x[j],(GEN)x[i-j]));
        p1 = gshift(p1,1);
        if ((i&1) == 0 && p2[i>>1])
          p1 = gadd(p1, gsqr((GEN)x[i>>1]));
        z[i] = lpileupto(av,p1);
      }
      z -= 2; free(p2); return normalize(z);
    }
    case t_RFRAC: z = cgetg(3,t_RFRAC);
      z[1] = lsqr((GEN)x[1]);
      z[2] = lsqr((GEN)x[2]); return z;

    case t_MAT:
      lx = lg(x);
      if (lx!=1 && lx != lg(x[1])) err(operi,"*",x,x);
      z = cgetg(lx, t_MAT);
      for (j=1; j<lx; j++) z[j] = (long)MC_mul(x, (GEN)x[j], lx, lx);
      return z;

    case t_QFR: return sqcompreal(x);
    case t_QFI: return sqcompimag(x);
    case t_VECSMALL:
      l = lg(x); z = cgetg(l, t_VECSMALL);
      for (i=1; i<l; i++)
      {
        long xi = x[i];
        if (xi < 1 || xi >= l) err(operf,"*",x,x);
        z[i] = x[xi];
      }
      return z;
  }
  err(operf,"*",x,x);
  return NULL; /* not reached */
}

/********************************************************************/
/**                                                                **/
/**                           DIVISION                             **/
/**                                                                **/
/********************************************************************/
static GEN
div_rfrac_scal(GEN x, GEN y)
{ return mul_rfrac((GEN)x[1],(GEN)x[2], gun,y); }
static GEN
div_scal_rfrac(GEN x, GEN y)
{ return mul_rfrac_scal((GEN)y[2], (GEN)y[1], x); }
static GEN
div_rfrac(GEN x, GEN y)
{ return mul_rfrac((GEN)x[1],(GEN)x[2], (GEN)y[2],(GEN)y[1]); }

#define div_ser_scal div_pol_scal
static GEN
div_pol_scal(GEN x, GEN y) {
  long i, lx = lg(x);
  GEN z = cgetg_copy(lx, x); z[1] = x[1];
  for (i=2; i<lx; i++) z[i] = ldiv((GEN)x[i],y);
  return z;
}
static GEN
div_T_scal(GEN x, GEN y, long tx) {
  switch(tx)
  {
    case t_POL: return div_pol_scal(x, y);
    case t_SER: return div_ser_scal(x, y);
    case t_RFRAC: return div_rfrac_scal(x,y);
  }
  err(operf,"/",x,y);
  return NULL; /* not reached */
}

static GEN
div_scal_pol(GEN x, GEN y) {
  long ly = lg(y);
  if (ly == 3) return gdiv(x,(GEN)y[2]);
  if (isexactzero(x)) return zeropol(varn(y));
  return gred_rfrac2(x,y);
}
static GEN
div_scal_ser(GEN x, GEN y) { /* TODO: improve */
  GEN z;
  long ly, i;
  if (gcmp0(x)) { pari_sp av=avma; return gerepileupto(av, gmul(x, ginv(y))); }
  ly = lg(y); z = (GEN)gpmalloc(ly*sizeof(long));
  z[0] = evaltyp(t_SER) | evallg(ly);
  z[1] = evalsigne(1) | evalvalp(0) | evalvarn(varn(y));
  z[2] = (long)x; for (i=3; i<ly; i++) z[i] = zero;
  y = gdiv(z,y); free(z); return y;
}
static GEN
div_scal_T(GEN x, GEN y, long ty) {
  switch(ty)
  {
    case t_POL: return div_scal_pol(x, y);
    case t_SER: return div_scal_ser(x, y);
    case t_RFRAC: return div_scal_rfrac(x, y);
  }
  err(operf,"/",x,y);
  return NULL; /* not reached */
}

/* assume tx = ty = t_SER, same variable vx */
static GEN
div_ser(GEN x, GEN y, long vx)
{
  long i, j, l = valp(x) - valp(y), lx = lg(x), ly = lg(y);
  GEN y_lead, p1, p2, z;
  pari_sp av;

  if (gcmp0(x)) return zeroser(vx, l);
  if (ly <= 2) err(gdiver);
  y_lead = (GEN)y[2];
  if (gcmp0(y_lead)) /* normalize denominator if leading term is 0 */
  {
    err(warner,"normalizing a series with 0 leading term");
    for (i=3,y++; i<ly; i++,y++)
    {
      y_lead = (GEN)y[2]; ly--; l--;
      if (!gcmp0(y_lead)) break;
    }
    if (i>=ly) err(gdiver);
  }
  if (ly < lx) lx = ly;
  p2 = (GEN)gpmalloc(lx*sizeof(long));
  for (i=3; i<lx; i++)
  {
    p1 = (GEN)y[i];
    if (isexactzero(p1)) p2[i] = 0;
    else
    {
      av = avma; p2[i] = lclone(gneg_i(p1));
      avma = av;
    }
  }
  z = cgetg(lx,t_SER);
  z[1] = evalvalp(l) | evalvarn(vx) | evalsigne(1);
  z[2] = ldiv((GEN)x[2], y_lead);
  for (i=3; i<lx; i++)
  {
    av = avma; p1 = (GEN)x[i];
    for (j=2; j<i; j++)
    {
      l = i-j+2;
      if (p2[l]) p1 = gadd(p1, gmul((GEN)z[j], (GEN)p2[l]));
    }
    p1 = gdiv(p1, y_lead);
    z[i] = lpileupto(av, forcecopy(p1));
  }
  for (i=3; i<lx; i++)
    if (p2[i]) gunclone((GEN)p2[i]);
  free(p2); return z;
}
/* x,y compatible PADIC */
static GEN
divpp(GEN x, GEN y) {
  pari_sp av;
  long a, b;
  GEN z, M;

  if (!signe(x[4])) return zeropadic((GEN)x[2], valp(x)-valp(y));
  a = precp(x);
  b = precp(y); if (a > b) { M = (GEN)y[3]; } else { M = (GEN)x[3]; b = a; }
  z = cgetg(5, t_PADIC);
  z[1] = evalprecp(b) | evalvalp(valp(x) - valp(y));
  icopyifstack(x[2], z[2]);
  z[3] = licopy(M); av = avma;
  z[4] = lpileuptoint(av, remii(mulii((GEN)x[4], Fp_inv((GEN)y[4], M)), M) );
  return z;
}

GEN
gdiv(GEN x, GEN y)
{
  long tx = typ(x), ty = typ(y), lx, ly, vx, vy, i;
  pari_sp av, tetpil;
  GEN z, p1, p2;

  if (tx == ty) switch(tx)
  {
    case t_INT:
      if (is_pm1(y)) return (signe(y) < 0)? negi(x): icopy(x);
      if (is_pm1(x)) {
        long s = signe(y);
        if (!s) err(gdiver);
        if (signe(x) < 0) s = -s;
        z = cgetg(3, t_FRAC);
        z[1] = s<0? lnegi(gun): un;
        z[2] = labsi(y); return z;
      }
      return gred_frac2(x,y);

    case t_REAL: return divrr(x,y);
    case t_INTMOD: { GEN X = (GEN)x[1], Y = (GEN)y[1];
      z = cgetg(3,t_INTMOD);
      if (X==Y || egalii(X,Y))
        return div_intmod_same(z, X, (GEN)x[2], (GEN)y[2]);
      z[1] = (long)gcdii(X,Y); av = avma;
      p1 = mulii((GEN)x[2], Fp_inv((GEN)y[2], (GEN)z[1]));
      z[2] = lpileuptoint(av, remii(p1, (GEN)z[1])); return z;
    }
    case t_FRAC: {
      GEN x1 = (GEN)x[1], x2 = (GEN)x[2];
      GEN y1 = (GEN)y[1], y2 = (GEN)y[2];
      z = cgetg(3, t_FRAC);
      p1 = gcdii(x1, y1);
      if (!is_pm1(p1)) { x1 = diviiexact(x1,p1); y1 = diviiexact(y1,p1); }
      p1 = gcdii(x2, y2);
      if (!is_pm1(p1)) { x2 = diviiexact(x2,p1); y2 = diviiexact(y2,p1); }
      tetpil = avma;
      z[2] = lmulii(x2,y1);
      z[1] = lmulii(x1,y2);
      fix_frac(z);
      fix_frac_if_int_GC(z,tetpil);
      return z;
    }
    case t_COMPLEX:
      av=avma; p1 = gnorm(y); p2 = mulcc(x, gconj(y)); tetpil = avma;
      return gerepile(av, tetpil, gdiv(p2,p1));

    case t_PADIC:
      if (!egalii((GEN)x[2],(GEN)y[2])) err(operi,"/",x,y);
      return divpp(x, y);

    case t_QUAD:
      if (!gegal((GEN)x[1],(GEN)y[1])) err(operi,"/",x,y);
      av = avma; p1 = gnorm(y); p2 = mulqq(x, gconj(y)); tetpil = avma;
      return gerepile(av, tetpil, gdiv(p2,p1));

    case t_POLMOD: av = avma;
      if (gegal((GEN)x[1], (GEN)y[1]))
      {
        GEN X = (GEN)x[1];
        x = (GEN)x[2];
        y = (GEN)y[2];
        if (degpol(X) == 2) { /* optimized for speed */
          z = mul_polmod_same(X, x, quad_polmod_conj(y, X));
          return gdiv(z, quad_polmod_norm(y, X));
        }
        y = ginvmod(y, X);
        z = mul_polmod_same(X, x, y);
      } else z = gmul(x, ginv(y));
      return gerepileupto(av, z);

    case t_POL:
      vx = varn(x);
      vy = varn(y);
      if (vx != vy) {
        if (varncmp(vx, vy) < 0) return div_pol_scal(x, y);
                            else return div_scal_pol(x, y);
      }
      if (!signe(y)) err(gdiver);
      if (lg(y) == 3) return gdiv(x,(GEN)y[2]);
      if (isexactzero(x)) return zeropol(vy);
      return gred_rfrac2(x,y);

    case t_SER:
      vx = varn(x);
      vy = varn(y);
      if (vx != vy) {
        if (varncmp(vx, vy) < 0) return div_ser_scal(x, y);
                            else return div_scal_ser(x, y);
      }
      if (!signe(y)) err(gdiver);
      return div_ser(x, y, vx);
    case t_RFRAC:
      vx = gvar(x);
      vy = gvar(y);
      if (vx != vy) {
        if (varncmp(vx, vy) < 0) return div_rfrac_scal(x, y);
                            else return div_scal_rfrac(x, y);
      }
      return div_rfrac(x,y);

    case t_QFI:
      i = signe(y[2]); setsigne(y[2],-i);
      z = compimag(x,y);
      setsigne(y[2], i); return z;

    case t_QFR: { long j;
      i = signe(y[2]); setsigne(y[2], -i);
      j = signe(y[4]); setsigne(y[4], -j);
      z = compreal(x,y); setsigne(y[4], j);
      setsigne(y[2], i); return z;
    }

    case t_MAT:
      av = avma;
      return gerepileupto(av, gmul(x, invmat(y)));

    default: err(operf,"/",x,y);
  }

  if (tx==t_INT && is_const_t(ty)) /* optimized for speed */
  {
    long s = signe(x);
    if (!s) {
      if (gcmp0(y)) err(gdiver);
      if (ty != t_INTMOD) return gzero;
      z = cgetg(3,t_INTMOD); icopyifstack(y[1],z[1]); z[2] = zero;
      return z;
    }
    if (is_pm1(x)) {
      if (s > 0) return ginv(y);
      av = avma; return gerepileupto(av, ginv(gneg(y)));
    }
    switch(ty)
    {
      case t_REAL: return divir(x,y);
      case t_INTMOD:
        z = cgetg(3, t_INTMOD);
        return div_intmod_same(z, (GEN)y[1], modii(x, (GEN)y[1]), (GEN)y[2]);
      case t_FRAC:
        z = cgetg(3,t_FRAC); p1 = gcdii(x,(GEN)y[1]);
        if (is_pm1(p1))
        {
          avma = (pari_sp)z;
          z[2] = licopy((GEN)y[1]);
          z[1] = lmulii((GEN)y[2], x);
          fix_frac(z);
          fix_frac_if_int(z);
        }
        else
        {
          x = diviiexact(x,p1); tetpil = avma;
          z[2] = (long)diviiexact((GEN)y[1], p1);
          z[1] = lmulii((GEN)y[2], x);
          fix_frac(z);
          fix_frac_if_int_GC(z,tetpil);
        }
        return z;

      case t_COMPLEX: return divRc(x,y);
      case t_PADIC: return divTp(x, y);
      case t_QUAD:
        av = avma; p1 = gnorm(y); p2 = mulRq(x, gconj(y)); tetpil = avma;
        return gerepile(av, tetpil, gdiv(p2,p1));
    }
  }
  if (gcmp0(y) && ty != t_MAT) err(gdiver);

  if (is_const_t(tx) && is_const_t(ty)) switch(tx)
  {
    case t_REAL:
      switch(ty)
      {
        case t_INT: return divri(x,y);
        case t_FRAC:
          av = avma; z = divri(mulri(x,(GEN)y[2]), (GEN)y[1]);
          return gerepileuptoleaf(av, z);
        case t_COMPLEX: return divRc(x, y);
        case t_QUAD: return divfq(x, y, lg(x));
        default: err(operf,"/",x,y);
      }

    case t_INTMOD:
      switch(ty)
      {
        case t_INT:
          z = cgetg(3, t_INTMOD);
          return div_intmod_same(z, (GEN)x[1], (GEN)x[2], modii(y, (GEN)x[1]));
        case t_FRAC: { GEN X = (GEN)x[1];
          z = cgetg(3,t_INTMOD); p1 = remii(mulii((GEN)y[2], (GEN)x[2]), X);
          return div_intmod_same(z, X, p1, modii((GEN)y[1], X));
        }
        case t_COMPLEX:
          av = avma; p1 = gnorm(y); p2 = mulRc(x, gconj(y)); tetpil = avma;
          return gerepile(av,tetpil, gdiv(p2,p1));

        case t_QUAD:
          av = avma; p1 = gnorm(y); p2 = gmul(x,gconj(y)); tetpil = avma;
          return gerepile(av,tetpil, gdiv(p2,p1));

        case t_PADIC: { GEN X = (GEN)x[1];
          z = cgetg(3, t_INTMOD);
          return div_intmod_same(z, X, (GEN)x[2], ptolift(y, X));
        }
        case t_REAL: err(operf,"/",x,y);
      }

    case t_FRAC:
      switch(ty)
      {
        case t_INT: z = cgetg(3, t_FRAC);
        p1 = gcdii(y,(GEN)x[1]);
        if (is_pm1(p1))
        {
          avma = (pari_sp)z; tetpil = 0;
          z[1] = licopy((GEN)x[1]);
        }
        else
        {
          y = diviiexact(y,p1); tetpil = avma;
          z[1] = (long)diviiexact((GEN)x[1], p1);
        }
        z[2] = lmulii((GEN)x[2],y);
        fix_frac(z);
        if (tetpil) fix_frac_if_int_GC(z,tetpil);
        return z;

        case t_REAL:
          av=avma; p1=mulri(y,(GEN)x[2]); tetpil=avma;
          return gerepile(av, tetpil, divir((GEN)x[1], p1));

        case t_INTMOD: { GEN Y = (GEN)y[1];
          z = cgetg(3,t_INTMOD); p1 = remii(mulii((GEN)y[2],(GEN)x[2]), Y);
          return div_intmod_same(z, Y, (GEN)x[1], p1);
        }
        case t_COMPLEX: return divRc(x, y);

        case t_PADIC:
          if (!signe(x[1])) return gzero;
          return divTp(x, y);

        case t_QUAD:
          av=avma; p1=gnorm(y); p2=gmul(x,gconj(y)); tetpil=avma;
          return gerepile(av,tetpil,gdiv(p2,p1));
      }

    case t_COMPLEX:
      switch(ty)
      {
        case t_INT: case t_REAL: case t_INTMOD: case t_FRAC: return divcR(x,y);
        case t_PADIC:
          return Zp_nosquare_m1((GEN)y[2])? divcR(x,y): divTp(x, y);
        case t_QUAD:
          lx = precision(x); if (!lx) err(operi,"/",x,y);
          return divfq(x, y, lx);
      }

    case t_PADIC:
      switch(ty)
      {
        case t_INT: case t_FRAC: { GEN p = (GEN)x[2];
          return signe(x[4])? divpT(x, y)
                            : zeropadic(p, valp(x) - ggval(y,p));
        }
        case t_INTMOD: { GEN Y = (GEN)y[1];
          z = cgetg(3, t_INTMOD);
          return div_intmod_same(z, Y, ptolift(x, Y), (GEN)y[2]);
        }
        case t_COMPLEX: case t_QUAD:
          av=avma; p1=gmul(x,gconj(y)); p2=gnorm(y); tetpil=avma;
          return gerepile(av,tetpil,gdiv(p1,p2));

        case t_REAL: err(operf,"/",x,y);
      }

    case t_QUAD:
      switch (ty)
      {
        case t_INT: case t_INTMOD: case t_FRAC:
          z = cgetg(4,t_QUAD); copyifstack(x[1], z[1]);
          z[2] = ldiv((GEN)x[2], y);
          z[3] = ldiv((GEN)x[3], y); return z;
        case t_REAL: return divqf(x, y, lg(y));
        case t_PADIC: return divTp(x, y);
        case t_COMPLEX:
          ly = precision(y); if (!ly) err(operi,"/",x,y);
          return divqf(x, y, ly);
      }
  }
  switch(ty) {
    case t_REAL: case t_INTMOD: case t_PADIC: case t_POLMOD:
      return gmul(x, ginv(y)); /* missing gerepile, for speed */
    case t_MAT:
      av = avma; return gerepileupto(av, gmul(x, invmat(y)));
  }
  if (is_matvec_t(tx)) {
    lx = lg(x); z = cgetg_copy(lx, x);
    for (i=1; i<lx; i++) z[i] = ldiv((GEN)x[i],y);
    return z;
  }

  vy = gvar(y);
  if (tx == t_POLMOD) { GEN X = (GEN)x[1];
    vx = varn(X);
    if (vx != vy) {
      if (varncmp(vx, vy) > 0) return div_scal_T(x, y, ty);
      z = cgetg(3,t_POLMOD); copyifstack(X,z[1]);
      z[2] = ldiv((GEN)x[2], y); return z;
    }
    /* y is POL, SER or RFRAC */
    av = avma; y = ginvmod(gmod(y,X), X);
    return gerepileupto(av, mul_polmod_same(X, (GEN)x[2], y));
  }
  /* x and y are not both is_scalar_t. If one of them is scalar, it's not a
   * POLMOD (done already), hence its variable is BIGINT. If the other has
   * variable BIGINT, then the operation is incorrect */
  vx = gvar(x);
  if (vx != vy) { /* includes cases where one is scalar */
    if (varncmp(vx, vy) < 0) return div_T_scal(x, y, tx);
                        else return div_scal_T(x, y, ty);
  }
  switch(tx)
  {
    case t_POL:
      switch(ty)
      {
	case t_SER:
	  if (gcmp0(x)) return zeropol(vx);
	  p1 = greffe(x,lg(y),0); p2 = div_ser(p1, y, vx);
          free(p1); return p2;

        case t_RFRAC: return div_scal_rfrac(x,y);
      }
      break;

    case t_SER:
      switch(ty)
      {
	case t_POL:
	  p1 = greffe(y,lg(x),0); p2 = div_ser(x, p1, vx);
          free(p1); return p2;
	case t_RFRAC:
	  av = avma;
	  return gerepileupto(av, gdiv(gmul(x,(GEN)y[2]), (GEN)y[1]));
      }
      break;

    case t_RFRAC:
      switch(ty)
      {
	case t_POL: return div_rfrac_scal(x,y);
	case t_SER:
	  av = avma;
	  return gerepileupto(av, gdiv((GEN)x[1], gmul((GEN)x[2],y)));
      }
      break;
  }
  err(operf,"/",x,y);
  return NULL; /* not reached */
}

/********************************************************************/
/**                                                                **/
/**                     SIMPLE MULTIPLICATION                      **/
/**                                                                **/
/********************************************************************/
GEN
gmulsg(long s, GEN y)
{
  long ty = typ(y), ly, i;
  pari_sp av;
  GEN z;

  switch(ty)
  {
    case t_INT:  return mulsi(s,y);
    case t_REAL: return mulsr(s,y);
    case t_INTMOD: { GEN p = (GEN)y[1];
      z = cgetg(3,t_INTMOD);
      z[2] = lpileuptoint((pari_sp)z, modii(mulsi(s,(GEN)y[2]), p));
      icopyifstack(p, z[1]); return z;
    }
    case t_FRAC:
      if (!s) return gzero;
      z = cgetg(3,t_FRAC);
      i = cgcd(s, smodis((GEN)y[2], s));
      if (i == 1)
      {
        z[2] = licopy((GEN)y[2]);
        z[1] = lmulis((GEN)y[1], s);
      }
      else
      {
        z[2] = ldivis((GEN)y[2], i);
        z[1] = lmulis((GEN)y[1], s/i);
        fix_frac_if_int(z);
      }
      return z;

    case t_COMPLEX: z = cgetg(3, t_COMPLEX);
      z[1] = lmulsg(s,(GEN)y[1]);
      z[2] = lmulsg(s,(GEN)y[2]); return z;

    case t_PADIC:
      if (!s) return gzero;
      av = avma; return gerepileupto(av, mulpp(cvtop2(stoi(s),y), y));

    case t_QUAD: z = cgetg(4, t_QUAD);
      copyifstack(y[1],z[1]);
      z[2] = lmulsg(s,(GEN)y[2]);
      z[3] = lmulsg(s,(GEN)y[3]); return z;

    case t_POLMOD: z = cgetg(3, t_POLMOD);
      z[2] = lmulsg(s,(GEN)y[2]);
      copyifstack(y[1],z[1]); return z;

    case t_POL:
      if (!s || !signe(y)) return zeropol(varn(y));
      ly = lg(y); z = cgetg(ly,t_POL); z[1]=y[1];
      for (i=2; i<ly; i++) z[i] = lmulsg(s,(GEN)y[i]);
      return normalizepol_i(z, ly);

    case t_SER:
      if (!s) return zeropol(varn(y));
      if (gcmp0(y)) return gcopy(y);
      ly = lg(y); z = cgetg(ly,t_SER); z[1] = y[1];
      for (i=2; i<ly; i++) z[i] = lmulsg(s,(GEN)y[i]);
      return normalize(z);

    case t_RFRAC:
      if (!s) return zeropol(gvar(y));
      z = cgetg(3, t_RFRAC);
      i = ggcd(stoi(s),(GEN)y[2])[2];
      avma = (pari_sp)z;
      if (i == 1)
      {
        z[1] = lmulgs((GEN)y[1], s);
        z[2] = lcopy((GEN)y[2]);
      }
      else
      {
        z[1] = lmulgs((GEN)y[1], s/i);
        z[2] = ldivgs((GEN)y[2], i);
      }
      return z;

    case t_VEC: case t_COL: case t_MAT:
      ly = lg(y); z = cgetg(ly,ty);
      for (i=1; i<ly; i++) z[i] = lmulsg(s,(GEN)y[i]);
      return z;
  }
  err(typeer,"gmulsg");
  return NULL; /* not reached */
}

/********************************************************************/
/**                                                                **/
/**                       SIMPLE DIVISION                          **/
/**                                                                **/
/********************************************************************/

GEN
gdivgs(GEN x, long s)
{
  long tx = typ(x), lx, i;
  pari_sp av;
  GEN z, y, p1;

  if (!s) err(gdiver);
  switch(tx)
  {
    case t_INT:
      av = avma; z = divis_rem(x,s,&i);
      if (!i) return z;

      i = cgcd(s, i);
      avma=av; z = cgetg(3,t_FRAC);
      if (i == 1)
        y = icopy(x);
      else
      {
        s /= i; y = diviuexact(x, i);
        if (signe(x) < 0) setsigne(y, -1);
      }
      z[1] = (long)y;
      z[2] = lstoi(s); fix_frac(z); return z;

    case t_REAL:
      return divrs(x,s);

    case t_INTMOD:
      z = cgetg(3, t_INTMOD);
      return div_intmod_same(z, (GEN)x[1], (GEN)x[2], modsi(s, (GEN)x[1]));

    case t_FRAC: z = cgetg(3, t_FRAC);
      i = cgcd(s, smodis((GEN)x[1], s));
      if (i == 1)
      {
        z[2] = lmulsi(s, (GEN)x[2]);
        z[1] = licopy((GEN)x[1]);
      }
      else
      {
        z[2] = lmulsi(s/i, (GEN)x[2]);
        z[1] = ldivis((GEN)x[1], i);
      }
      fix_frac(z);
      fix_frac_if_int(z); return z;

    case t_COMPLEX: z = cgetg(3, t_COMPLEX);
      z[1] = ldivgs((GEN)x[1],s);
      z[2] = ldivgs((GEN)x[2],s); return z;

    case t_PADIC: return gdiv(x, stoi(s));

    case t_QUAD: z = cgetg(4, t_QUAD);
      copyifstack(x[1],z[1]);
      z[2] = ldivgs((GEN)x[2],s);
      z[3] = ldivgs((GEN)x[3],s); return z;

    case t_POLMOD: z = cgetg(3, t_POLMOD);
      copyifstack(x[1],z[1]);
      z[2] = ldivgs((GEN)x[2],s); return z;

    case t_RFRAC:
      av = avma;
      p1 = ggcd(stoi(s),(GEN)x[1]);
      if (typ(p1) == t_INT)
      {
        avma = av;
        z = cgetg(3, t_RFRAC);
        i = p1[2];
        if (i == 1)
        {
          z[1] = lcopy((GEN)x[1]);
          z[2] = lmulsg(s,(GEN)x[2]);
        }
        else
        {
          z[1] = ldivgs((GEN)x[1], i);
          z[2] = lmulgs((GEN)x[2], s/i);
        }
      }
      else /* t_FRAC */
      {
        z = cgetg(3, t_RFRAC);
        z[1] = ldiv((GEN)x[1], p1);
        z[2] = lmul((GEN)x[2], gdivsg(s,p1));
        z = gerepilecopy(av, z);
      }
      return z;

    case t_POL: case t_SER: case t_VEC: case t_COL: case t_MAT:
      z = init_gen_op(x, tx, &lx, &i);
      for (; i<lx; i++) z[i] = ldivgs((GEN)x[i],s);
      return z;
    
  }
  err(operf,"/",x, stoi(s));
  return NULL; /* not reached */
}

/* True shift (exact multiplication by 2^n) */
GEN
gmul2n(GEN x, long n)
{
  long tx, lx, i, k, l;
  pari_sp av, tetpil;
  GEN p2, p1, z;

  tx=typ(x);
  switch(tx)
  {
    case t_INT:
      if (n>=0) return shifti(x,n);
      if (!signe(x)) return gzero;
      l = vali(x); n = -n;
      if (n<=l) return shifti(x,-n);
      z = cgetg(3,t_FRAC);
      z[1] = lshifti(x,-l);
      z[2] = lshifti(gun,n-l); return z;
	
    case t_REAL:
      return shiftr(x,n);

    case t_INTMOD:
      z = cgetg(3,t_INTMOD);
      if (n > 0)
      {
        p2 = (GEN)x[1];
        z[2] = lpileuptoint((pari_sp)z, modii(shifti((GEN)x[2],n),p2));
        icopyifstack(p2,z[1]); return z;
      }
      return div_intmod_same(z, (GEN)x[1], (GEN)x[2],
                                           modii(shifti(gun,-n), (GEN)x[1]));
    case t_FRAC:
      l = vali((GEN)x[1]);
      k = vali((GEN)x[2]);
      if (n+l-k>=0)
      {
        if (expi((GEN)x[2]) == k) /* x[2] power of 2 */
          return shifti((GEN)x[1],n-k);
        l = n-k; k = -k;
      }
      else
      {
        k = -l-n; l = -l;
      }
      z = cgetg(3,t_FRAC);
      z[1] = lshifti((GEN)x[1],l);
      z[2] = lshifti((GEN)x[2],k); return z;

    case t_QUAD: z=cgetg(4,t_QUAD);
      copyifstack(x[1],z[1]);
      z[2] = lmul2n((GEN)x[2],n);
      z[3] = lmul2n((GEN)x[3],n); return z;

    case t_POLMOD: z=cgetg(3,t_POLMOD);
      copyifstack(x[1],z[1]);
      z[2] = lmul2n((GEN)x[2],n); return z;

    case t_COMPLEX: case t_POL: case t_SER:
    case t_VEC: case t_COL: case t_MAT:
      z = init_gen_op(x, tx, &lx, &i);
      for (; i<lx; i++) z[i] = lmul2n((GEN)x[i],n);
      return z;

    case t_RFRAC: av=avma; p1 = gmul2n(gun,n); tetpil = avma;
      return gerepile(av,tetpil, mul_rfrac_scal((GEN)x[1],(GEN)x[2], p1));

    case t_PADIC:
      av=avma; z=gmul2n(gun,n); tetpil=avma;
      return gerepile(av,tetpil,gmul(z,x));
  }
  err(typeer,"gmul2n");
  return NULL; /* not reached */
}
