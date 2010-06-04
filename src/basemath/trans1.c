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
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

#ifdef LONG_IS_64BIT
static const long SQRTVERYBIGINT = 3037000500; /* ceil(sqrt(LONG_MAX)) */
static const long CBRTVERYBIGINT = 2097152;    /* ceil(cbrt(LONG_MAX)) */
#else
static const long SQRTVERYBIGINT = 46341;
static const long CBRTVERYBIGINT =  1291;
#endif

static THREAD GEN geuler, glog2, gpi;
void
pari_init_floats(void)
{
  geuler = gpi = bernzone = glog2 = NULL;
}

void
pari_close_floats(void)
{
  if (geuler) gunclone(geuler);
  if (gpi) gunclone(gpi);
  if (bernzone) gunclone(bernzone);
  if (glog2) gunclone(glog2);
}

/********************************************************************/
/**                                                                **/
/**                               PI                               **/
/**                                                                **/
/********************************************************************/
#if 0
/* Ramanujan's formula:
 *                         ----
 *  53360 (640320)^(1/2)   \    (6n)! (545140134 n + 13591409)
 *  -------------------- = /    ------------------------------
 *        Pi               ----   (n!)^3 (3n)! (-640320)^(3n)
 *                         n>=0
 */
GEN
piold(long prec)
{
  const long k1 = 545140134, k2 = 13591409, k3 = 640320;
  const double alpha2 = 47.11041314/BITS_IN_LONG; /* 3log(k3/12) / log(2^BIL) */
  GEN p1,p2,p3,tmppi;
  long l, n, n1;
  pari_sp av = avma, av2;
  double alpha;

  tmppi = cgetr(prec);
  prec++;
  n = (long)(1 + (prec-2)/alpha2);
  n1 = 6*n - 1;
  p2 = addsi(k2, mulss(n,k1));
  p1 = itor(p2, prec);

  /* initialize mantissa length */
  if (prec>=4) l=4; else l=prec;
  setlg(p1,l); alpha = (double)l;

  av2 = avma;
  while (n)
  {
    if (n < CBRTVERYBIGINT) /* p3 = n1(n1-2)(n1-4) / n^3 */
      p3 = divru(mulur(n1-4,mulur(n1*(n1-2),p1)),n*n*n);
    else
    {
      if (n1 < SQRTVERYBIGINT)
        p3 = divru(divru(mulur(n1-4,mulur(n1*(n1-2),p1)),n*n),n);
      else
        p3 = divru(divru(divru(mulur(n1-4,mulur(n1,mulur(n1-2,p1))),n),n),n);
    }
    p3 = divru(divru(p3,100100025), 327843840);
    subisz(p2,k1,p2);
    subirz(p2,p3,p1);
    alpha += alpha2; l = (long)(1+alpha); /* new mantissa length */
    if (l > prec) l = prec;
    setlg(p1,l); avma = av2;
    n--; n1-=6;
  }
  p1 = divur(53360,p1);
  return gerepileuptoleaf(av, mulrr(p1,sqrtr_abs(stor(k3,prec))));
}
#endif
/* Gauss - Brent-Salamin AGM iteration */
GEN
constpi(long prec)
{
  GEN A, B, C, tmppi;
  long i, G;
  pari_sp av, av2;

  if (gpi && lg(gpi) >= prec) return gpi;

  av = avma; tmppi = newblock(prec);
  *tmppi = evaltyp(t_REAL) | evallg(prec);
  G = - bit_accuracy(prec);
  prec++;

  A = real_1(prec);
  i = A[1]; A[1] = evalsigne(1) | _evalexpo(-1);
  B = sqrtr_abs(A); /* = 1/sqrt(2) */
  A[1] = i;
  C = real2n(-2, prec); av2 = avma;
  for (i = 0;; i++)
  {
    GEN y, a, b, B_A = subrr(B, A);
    pari_sp av3 = avma;
    if (expo(B_A) < G) break;
    a = addrr(A,B); setexpo(a, expo(a)-1);
    b = mulrr(A,B);
    affrr(a, A);
    affrr(sqrtr_abs(b), B); avma = av3;
    y = sqrr(B_A); setexpo(y, expo(y) + i - 2);
    affrr(subrr(C, y), C); avma = av2;
  }
  setexpo(C, expo(C)+2);
  affrr(divrr(sqrr(addrr(A,B)), C), tmppi);
  if (gpi) gunclone(gpi);
  avma = av;  return gpi = tmppi;
}

GEN
mppi(long prec) { return rtor(constpi(prec), prec); }

/* Pi * 2^n */
GEN
Pi2n(long n, long prec)
{
  GEN x = mppi(prec); setexpo(x, 1+n);
  return x;
}

/* I * Pi * 2^n */
GEN
PiI2n(long n, long prec)
{
  GEN z = cgetg(3,t_COMPLEX);
  gel(z,1) = gen_0;
  gel(z,2) = Pi2n(n, prec); return z;
}

/* 2I * Pi */
GEN
PiI2(long prec) { return PiI2n(1, prec); }

/********************************************************************/
/**                                                                **/
/**                       EULER CONSTANT                           **/
/**                                                                **/
/********************************************************************/

GEN
consteuler(long prec)
{
  GEN u,v,a,b,tmpeuler;
  long l, n1, n, k, x;
  pari_sp av1, av2;

  if (geuler && lg(geuler) >= prec) return geuler;

  av1 = avma; tmpeuler = newblock(prec);
  *tmpeuler = evaltyp(t_REAL) | evallg(prec);

  prec++;

  l = prec+1; x = (long) (1 + bit_accuracy_mul(l, LOG2/4));
  a = utor(x,l); u=logr_abs(a); setsigne(u,-1); affrr(u,a);
  b = real_1(l);
  v = real_1(l);
  n = (long)(1+3.591*x); /* z=3.591: z*[ ln(z)-1 ]=1 */
  n1 = minss(n, SQRTVERYBIGINT);
  if (x < SQRTVERYBIGINT)
  {
    ulong xx = x*x;
    av2 = avma;
    for (k=1; k<n1; k++)
    {
      affrr(divru(mulur(xx,b),k*k), b);
      affrr(divru(addrr(divru(mulur(xx,a),k),b),k), a);
      affrr(addrr(u,a), u);
      affrr(addrr(v,b), v); avma = av2;
    }
    for (   ; k<=n; k++)
    {
      affrr(divru(divru(mulur(xx,b),k),k), b);
      affrr(divru(addrr(divru(mulur(xx,a),k),b),k), a);
      affrr(addrr(u,a), u);
      affrr(addrr(v,b), v); avma = av2;
    }
  }
  else
  {
    GEN xx = sqru(x);
    av2 = avma;
    for (k=1; k<n1; k++)
    {
      affrr(divru(mulir(xx,b),k*k), b);
      affrr(divru(addrr(divru(mulir(xx,a),k),b),k), a);
      affrr(addrr(u,a), u);
      affrr(addrr(v,b), v); avma = av2;
    }
    for (   ; k<=n; k++)
    {
      affrr(divru(divru(mulir(xx,b),k),k), b);
      affrr(divru(addrr(divru(mulir(xx,a),k),b),k), a);
      affrr(addrr(u,a), u);
      affrr(addrr(v,b), v); avma = av2;
    }
  }
  divrrz(u,v,tmpeuler);
  if (geuler) gunclone(geuler);
  avma = av1; return geuler = tmpeuler;
}

GEN
mpeuler(long prec) { return rtor(consteuler(prec), prec); }

/********************************************************************/
/**                                                                **/
/**          TYPE CONVERSION FOR TRANSCENDENTAL FUNCTIONS          **/
/**                                                                **/
/********************************************************************/

GEN
transc(GEN (*f)(GEN,long), GEN x, long prec)
{
  pari_sp tetpil, av = avma;
  GEN p1, y;
  long lx, i;

  if (prec < 3) pari_err(talker, "incorrect precision in transc");
  switch(typ(x))
  {
    case t_INT:
      p1 = itor(x, prec); tetpil=avma;
      return gerepile(av,tetpil,f(p1,prec));

    case t_FRAC:
      p1 = rdivii(gel(x,1), gel(x,2), prec); tetpil=avma;
      return gerepile(av,tetpil,f(p1,prec));

    case t_QUAD:
      p1 = quadtofp(x, prec); tetpil = avma;
      return gerepile(av,tetpil,f(p1,prec));

    case t_POL: case t_RFRAC:
      return gerepileupto(av, f(toser_i(x), prec));

    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = f(gel(x,i),prec);
      return y;

    case t_POLMOD:
      p1 = cleanroots(gel(x,1),prec); lx = lg(p1);
      for (i=1; i<lx; i++) gel(p1,i) = poleval(gel(x,2),gel(p1,i));
      tetpil = avma; y = cgetg(lx,t_COL);
      for (i=1; i<lx; i++) gel(y,i) = f(gel(p1,i),prec);
      return gerepile(av,tetpil,y);

    default: pari_err(typeer,"a transcendental function");
  }
  return f(x,prec);
}

/*******************************************************************/
/*                                                                 */
/*                            POWERING                             */
/*                                                                 */
/*******************************************************************/
static GEN
powr0(GEN x)
{
  long lx = lg(x);
  return lx == 2? mpexp(x): real_1(lx);
}
/* to be called by the generic function gpowgs(x,s) when s = 0 */
static GEN
gpowg0(GEN x)
{
  long lx, i;
  GEN y;

  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC: case t_PADIC:
      return gen_1;

    case t_QUAD: x++; /*fall through*/
    case t_COMPLEX: {
      pari_sp av = avma;
      GEN a = gpowg0(gel(x,1));
      GEN b = gpowg0(gel(x,2));
      if (a == gen_1) return b;
      if (b == gen_1) return a;
      return gerepileupto(av, gmul(a,b));
    }
    case t_INTMOD:
      y = cgetg(3,t_INTMOD);
      gel(y,1) = icopy(gel(x,1));
      gel(y,2) = gen_1; return y;

    case t_FFELT: return FF_1(x);

    case t_POLMOD:
      y = cgetg(3,t_POLMOD);
      gel(y,1) = gcopy(gel(x,1));
      gel(y,2) = RgX_get_1(gel(x,1)); return y;

    case t_RFRAC:
      return RgX_get_1(gel(x,2));
    case t_POL: case t_SER:
      return RgX_get_1(x);

    case t_MAT:
      lx=lg(x); if (lx==1) return cgetg(1,t_MAT);
      if (lx != lg(x[1])) pari_err(mattype1,"gpow");
      y = matid(lx-1);
      for (i=1; i<lx; i++) gcoeff(y,i,i) = gpowg0(gcoeff(x,i,i));
      return y;
    case t_QFR: return qfr_1(x);
    case t_QFI: return qfi_1(x);
    case t_VECSMALL: return identity_perm(lg(x) - 1);
  }
  pari_err(typeer,"gpow");
  return NULL; /* not reached */
}

static GEN
_sqr(void *data /* ignored */, GEN x) { (void)data; return gsqr(x); }
static GEN
_mul(void *data /* ignored */, GEN x, GEN y) { (void)data; return gmul(x,y); }
static GEN
_sqri(void *data /* ignored */, GEN x) { (void)data; return sqri(x); }
static GEN
_muli(void *data /* ignored */, GEN x, GEN y) { (void)data; return mulii(x,y); }
static GEN
_sqrr(void *data /* ignored */, GEN x) { (void)data; return sqrr(x); }
static GEN
_mulr(void *data /* ignored */, GEN x, GEN y) { (void)data; return mulrr(x,y); }

/* INTEGER POWERING (a^n for integer a != 0 and integer n > 0)
 *
 * Use left shift binary algorithm (RS is wasteful: multiplies big numbers,
 * with LS one of them is the base, hence small). Sign of result is set
 * to s (= 1,-1). Makes life easier for caller, which otherwise might do a
 * setsigne(gen_1 / gen_m1) */
static GEN
powiu_sign(GEN a, ulong N, long s)
{
  pari_sp av;
  GEN y;

  if (lgefint(a) == 3)
  { /* easy if |a| < 3 */
    if (a[2] == 1) return (s>0)? gen_1: gen_m1;
    if (a[2] == 2) { a = int2u(N); setsigne(a,s); return a; }
  }
  if (N == 1) { a = icopy(a); setsigne(a,s); return a; }
  if (N == 2) return sqri(a);
  av = avma;
  y = gen_powu(a, N, NULL, &_sqri, &_muli);
  setsigne(y,s); return gerepileuptoint(av, y);
}
/* a^N */
GEN
powiu(GEN a, ulong N)
{
  long s;
  if (!N) return gen_1;
  s = signe(a);
  if (!s) return gen_0;
  return powiu_sign(a, N, (s < 0 && odd(N))? -1: 1);
}
GEN
powis(GEN x, long n)
{
  long sx, s;
  GEN t, y;
  if (!n) return gen_1;
  sx = signe(x);
  if (!sx) {
    if (n < 0) pari_err(gdiver);
    return gen_0;
  }
  s = (sx < 0 && odd(n))? -1: 1;
  if (n > 0) return powiu_sign(x, n, s);
  t = (s > 0)? gen_1: gen_m1;
  if (is_pm1(x)) return t;
  /* n < 0, |x| > 1 */
  y = cgetg(3,t_FRAC);
  gel(y,1) = t;
  gel(y,2) = powiu_sign(x, -n, 1); /* force denominator > 0 */
  return y;
}
GEN
powuu(ulong p, ulong N)
{
  long P[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3),0};
  if (!N) return gen_1;
  if (!p) return gen_0;
  P[2] = p;
  return powiu_sign(P, N, 1);
}

/* assume p^k is SMALL */
ulong
upowuu(ulong p, ulong k)
{
  ulong i, pk;

  if (!k) return 1;
  if (p == 2) return 1UL<<k;
  pk = p; for (i=2; i<=k; i++) pk *= p;
  return pk;
}

typedef struct {
  long prec, a;
  GEN (*sqr)(GEN);
  GEN (*mulug)(ulong,GEN);
} sr_muldata;

static GEN
_rpowuu_sqr(void *data, GEN x)
{
  sr_muldata *D = (sr_muldata *)data;
  if (typ(x) == t_INT && lgefint(x) >= D->prec)
  { /* switch to t_REAL */
    D->sqr   = &sqrr;
    D->mulug = &mulur; x = itor(x, D->prec);
  }
  return D->sqr(x);
}

static GEN
_rpowuu_msqr(void *data, GEN x)
{
  GEN x2 = _rpowuu_sqr(data, x);
  sr_muldata *D = (sr_muldata *)data;
  return D->mulug(D->a, x2);
}

/* return a^n as a t_REAL of precision prec. Assume a > 0, n > 0 */
GEN
rpowuu(ulong a, ulong n, long prec)
{
  pari_sp av;
  GEN y;
  sr_muldata D;

  if (a == 1) return real_1(prec);
  if (a == 2) return real2n(n, prec);
  if (n == 1) return stor(a, prec);
  av = avma;
  D.sqr   = &sqri;
  D.mulug = &mului;
  D.prec = prec;
  D.a = (long)a;
  y = leftright_pow_u_fold(utoipos(a), n, (void*)&D, &_rpowuu_sqr,
                                                     &_rpowuu_msqr);
  if (typ(y) == t_INT) y = itor(y, prec);
  return gerepileuptoleaf(av, y);
}

GEN
powrs(GEN x, long n)
{
  pari_sp av = avma;
  GEN y;
  if (!n) return powr0(x);
  y = gen_powu(x, (ulong)labs(n), NULL, &_sqrr, &_mulr);
  if (n < 0) y = invr(y);
  return gerepileupto(av,y);
}
GEN
powru(GEN x, ulong n)
{
  if (!n) return powr0(x);
  return gen_powu(x, n, NULL, &_sqrr, &_mulr);
}

/* x^(s/2), assume x t_REAL */
GEN
powrshalf(GEN x, long s)
{
  if (s & 1) return sqrtr(powrs(x, s));
  return powrs(x, s>>1);
}
/* x^(s/2), assume x t_REAL */
GEN
powruhalf(GEN x, ulong s)
{
  if (s & 1) return sqrtr(powru(x, s));
  return powru(x, s>>1);
}
/* x^(n/d), assume x t_REAL, return t_REAL */
GEN
powrfrac(GEN x, long n, long d)
{
  long z;
  if (!n) return powr0(x);
  z = cgcd(n, d); if (z > 1) { n /= z; d /= z; }
  if (d == 1) return powrs(x, n);
  x = powrs(x, n);
  if (d == 2) return sqrtr(x);
  return sqrtnr(x, d);
}

/* assume x != 0 */
static GEN
pow_monome(GEN x, long n)
{
  long i, d, dx = degpol(x);
  GEN A, b, y;

  if (n < 0) { n = -n; y = cgetg(3, t_RFRAC); } else y = NULL;

  if (HIGHWORD(dx) || HIGHWORD(n))
  {
    LOCAL_HIREMAINDER;
    d = (long)mulll((ulong)dx, (ulong)n);
    if (hiremainder || (d &~ LGBITS)) d = LGBITS; /* overflow */
    d += 2;
  }
  else
    d = dx*n + 2;
  if ((d + 1) & ~LGBITS) pari_err(talker,"degree overflow in pow_monome");
  A = cgetg(d+1, t_POL); A[1] = x[1];
  for (i=2; i < d; i++) gel(A,i) = gen_0;
  b = gpowgs(gel(x,dx+2), n); /* not memory clean if (n < 0) */
  if (!y) y = A;
  else {
    GEN c = denom(b);
    gel(y,1) = c; if (c != gen_1) b = gmul(b,c);
    gel(y,2) = A;
  }
  gel(A,d) = b; return y;
}

/* x t_PADIC */
static GEN
powps(GEN x, long n)
{
  long e = n*valp(x), v;
  GEN t, y, mod, p = gel(x,2);
  pari_sp av;

  if (!signe(x[4])) {
    if (n < 0) pari_err(gdiver);
    return zeropadic(p, e);
  }
  v = z_pval(n, p);

  y = cgetg(5,t_PADIC);
  mod = gel(x,3);
  if (v == 0) mod = icopy(mod);
  else
  {
    if (precp(x) == 1 && equaliu(p, 2)) v++;
    mod = mulii(mod, powiu(p,v));
    mod = gerepileuptoint((pari_sp)y, mod);
  }
  y[1] = evalprecp(precp(x) + v) | evalvalp(e);
  gel(y,2) = icopy(p);
  gel(y,3) = mod;

  av = avma; t = gel(x,4);
  if (n < 0) { t = Fp_inv(t, mod); n = -n; }
  t = Fp_powu(t, n, mod);
  gel(y,4) = gerepileuptoint(av, t);
  return y;
}
/* x t_PADIC */
static GEN
powp(GEN x, GEN n)
{
  long v;
  GEN y, mod, p = gel(x,2);

  if (valp(x)) pari_err(overflower,"valp()");

  if (!signe(x[4])) {
    if (signe(n) < 0) pari_err(gdiver);
    return zeropadic(p, 0);
  }
  v = Z_pval(n, p);

  y = cgetg(5,t_PADIC);
  mod = gel(x,3);
  if (v == 0) mod = icopy(mod);
  else
  {
    mod = mulii(mod, powiu(p,v));
    mod = gerepileuptoint((pari_sp)y, mod);
  }
  y[1] = evalprecp(precp(x) + v) | _evalvalp(0);
  gel(y,2) = icopy(p);
  gel(y,3) = mod;
  gel(y,4) = Fp_pow(gel(x,4), n, mod);
  return y;
}
static GEN
pow_polmod(GEN x, GEN n)
{
  GEN z = cgetg(3, t_POLMOD), a = gel(x,2), T = gel(x,1);
  gel(z,1) = gcopy(T);
  if (typ(a) != t_POL || varn(a) != varn(T) || lg(a) <= 3)
    a = powgi(a, n);
  else {
    pari_sp av = avma;
    GEN p = NULL;
    if (RgX_is_FpX(T, &p) && RgX_is_FpX(a, &p) && p)
    {
      T = RgX_to_FpX(T, p); a = RgX_to_FpX(a, p);
      if (lgefint(p) == 3)
      {
        ulong pp = p[2];
        a = Flxq_pow(ZX_to_Flx(a, pp), n, ZX_to_Flx(T, pp), pp);
        a = Flx_to_ZX(a);
      }
      else
        a = FpXQ_pow(a, n, T, p);
      a = FpX_to_mod(a, p);
      a = gerepileupto(av, a);
    }
    else
    {
      avma = av;
      a = RgXQ_pow(a, n, gel(z,1));
    }
  }
  gel(z,2) = a; return z;
}

GEN
gpowgs(GEN x, long n)
{
  long m;
  pari_sp av;
  GEN y;

  if (n == 0) return gpowg0(x);
  if (n == 1)
    switch (typ(x)) {
      case t_QFI: return redimag(x);
      case t_QFR: return redreal(x);
      default: return gcopy(x);
    }
  if (n ==-1) return ginv(x);
  switch(typ(x))
  {
    case t_INT: return powis(x,n);
    case t_REAL: return powrs(x,n);
    case t_INTMOD:
      y = cgetg(3,t_INTMOD); gel(y,1) = icopy(gel(x,1));
      gel(y,2) = Fp_pows(gel(x,2), n, gel(x,1));
      return y;
    case t_FRAC:
    {
      GEN a = gel(x,1), b = gel(x,2);
      long sx = signe(a), s;
      if (!sx) {
        if (n < 0) pari_err(gdiver);
        return gen_0;
      }
      s = (sx < 0 && odd(n))? -1: 1;
      if (n < 0) {
        n = -n;
        if (is_pm1(a)) return powiu_sign(b, n, s); /* +-1/x[2] inverts to t_INT */
        swap(a, b);
      }
      y = cgetg(3, t_FRAC);
      gel(y,1) = powiu_sign(a, n, s);
      gel(y,2) = powiu_sign(b, n, 1);
      return y;
    }
    case t_PADIC: return powps(x, n);
    case t_RFRAC:
    {
      av = avma; y = cgetg(3, t_RFRAC); m = labs(n);
      gel(y,1) = gpowgs(gel(x,1),m);
      gel(y,2) = gpowgs(gel(x,2),m);
      if (n < 0) y = ginv(y);
      return gerepileupto(av,y);
    }
    case t_POLMOD: {
      long N[] = {evaltyp(t_INT) | _evallg(3),0,0};
      affsi(n,N); return pow_polmod(x, N);
    }
    case t_POL:
      if (RgX_is_monomial(x)) return pow_monome(x, n);
    default: {
      pari_sp av = avma;
      y = gen_powu(x, (ulong)labs(n), NULL, &_sqr, &_mul);
      if (n < 0) y = ginv(y);
      return gerepileupto(av,y);
    }
  }
}

/* n a t_INT */
GEN
powgi(GEN x, GEN n)
{
  GEN y;

  if (!is_bigint(n)) return gpowgs(x, itos(n));
  /* probable overflow for non-modular types (typical exception: (X^0)^N) */
  switch(typ(x))
  {
    case t_INTMOD:
      y = cgetg(3,t_INTMOD); gel(y,1) = icopy(gel(x,1));
      gel(y,2) = Fp_pow(gel(x,2), n, gel(x,1));
      return y;
    case t_FFELT: return FF_pow(x,n);
    case t_PADIC: return powp(x, n);

    case t_INT:
      if (is_pm1(x)) return (signe(x) < 0 && mpodd(n))? gen_m1: gen_1;
      if (signe(x)) pari_err(overflower,"lg()");
      if (signe(n) < 0) pari_err(gdiver);
      return gen_0;
    case t_FRAC:
      pari_err(overflower,"lg()");

    case t_QFR: return qfrpow(x, n);
    case t_POLMOD: return pow_polmod(x, n);
    default: {
      pari_sp av = avma;
      y = gen_pow(x, n, NULL, &_sqr, &_mul);
      if (signe(n) < 0) y = ginv(y);
      return gerepileupto(av,y);
    }
  }
}

/* we suppose n != 0, valp(x) = 0 and leading-term(x) != 0. Not stack clean */
static GEN
ser_pow(GEN x, GEN n, long prec)
{
  pari_sp av, tetpil;
  GEN y, p1, p2, lead;

  if (varncmp(gvar(n), varn(x)) <= 0) return gexp(gmul(n, glog(x,prec)), prec);
  lead = gel(x,2);
  if (gequal1(lead))
  {
    GEN X, Y, alp = gadd(n,gen_1); /* will be left on the stack */
    long lx, mi, i, j, d;

    lx = lg(x);
    y = cgetg(lx,t_SER);
    y[1] = evalsigne(1) | _evalvalp(0) | evalvarn(varn(x));
    X = x+2;
    Y = y+2;

    d = mi = lx-3; while (mi>=1 && isrationalzero(gel(X,mi))) mi--;
    gel(Y,0) = gen_1;
    for (i=1; i<=d; i++)
    {
      av = avma; p1 = gen_0;
      for (j=1; j<=minss(i,mi); j++)
      {
        p2 = gsubgs(gmulgs(alp,j),i);
        p1 = gadd(p1, gmul(gmul(p2,gel(X,j)),gel(Y,i-j)));
      }
      tetpil = avma; gel(Y,i) = gerepile(av,tetpil, gdivgs(p1,i));
    }
    return y;
  }
  p1 = gdiv(x,lead);
  if (typ(p1) != t_SER) pari_err(typeer, "ser_pow");
  gel(p1,2) = gen_1; /* in case it's inexact */
  if (typ(n) == t_FRAC && !isinexact(lead) && ispower(lead, gel(n,2), &p2))
    p2 = powgi(p2, gel(n,1));
  else
    p2 = gpow(lead,n, prec);
  return gmul(p2, gpow(p1,  n, prec));
}

static long
val_from_i(GEN E)
{
  if (is_bigint(E)) pari_err(talker,"valuation overflow in sqrtn");
  return itos(E);
}

/* return x^q, assume typ(x) = t_SER, typ(q) = t_FRAC and q != 0 */
static GEN
ser_powfrac(GEN x, GEN q, long prec)
{
  long e = valp(x);
  GEN y, E = gmulsg(e, q);

  if (!signe(x)) return zeroser(varn(x), val_from_i(gfloor(E)));
  if (typ(E) != t_INT)
    pari_err(talker,"%Ps should divide valuation (= %ld) in sqrtn",q[2], e);
  e = val_from_i(E);
  y = leafcopy(x); setvalp(y, 0);
  y = ser_pow(y, q, prec);
  if (typ(y) == t_SER) /* generic case */
    y[1] = evalsigne(1) | evalvalp(e) | evalvarn(varn(x));
  else /* e.g coeffs are POLMODs */
    y = gmul(y, monomial(gen_1, e, varn(x)));
  return y;
}

GEN
gpow(GEN x, GEN n, long prec)
{
  long i, lx, tx, tn = typ(n);
  pari_sp av;
  GEN y;

  if (tn == t_INT) return powgi(x,n);
  tx = typ(x);
  if (is_matvec_t(tx))
  {
    y = cgetg_copy(x, &lx);
    for (i=1; i<lx; i++) gel(y,i) = gpow(gel(x,i),n,prec);
    return y;
  }
  av = avma;
  switch (tx)
  {
    case t_POL: case t_RFRAC: x = toser_i(x); /* fall through */
    case t_SER:
      if (tn == t_FRAC) return gerepileupto(av, ser_powfrac(x, n, prec));
      if (valp(x))
        pari_err(talker,"gpow: need integer exponent if series valuation != 0");
      if (lg(x) == 2) return gerepilecopy(av, x); /* O(1) */
      return gerepileupto(av, ser_pow(x, n, prec));
  }
  if (gequal0(x))
  {
    if (!is_scalar_t(tn) || tn == t_PADIC || tn == t_INTMOD)
      pari_err(talker,"gpow: 0 to a forbidden power");
    n = real_i(n);
    if (gsigne(n) <= 0)
      pari_err(talker,"gpow: 0 to a non positive exponent");
    if (!precision(x)) return gcopy(x);

    x = ground(gmulsg(gexpo(x),n));
    if (is_bigint(x) || (ulong)x[2] >= HIGHEXPOBIT)
      pari_err(talker,"gpow: underflow or overflow");
    avma = av; return real_0_bit(itos(x));
  }
  if (tn == t_FRAC)
  {
    GEN z, d = gel(n,2), a = gel(n,1);
    switch (tx)
    {
    case t_INTMOD:
      if (!BPSW_psp(gel(x,1))) pari_err(talker,"gpow: modulus %Ps is not prime",x[1]);
      y = cgetg(3,t_INTMOD); gel(y,1) = icopy(gel(x,1));
      av = avma;
      z = Fp_sqrtn(gel(x,2), d, gel(x,1), NULL);
      if (!z) pari_err(talker,"gpow: nth-root does not exist");
      gel(y,2) = gerepileuptoint(av, Fp_pow(z, a, gel(x,1)));
      return y;

    case t_PADIC:
      z = equaliu(d, 2)? Qp_sqrt(x): Qp_sqrtn(x, d, NULL);
      if (!z) pari_err(talker, "gpow: nth-root does not exist");
      return gerepileupto(av, powgi(z, a));

    case t_FFELT:
      return gerepileupto(av,FF_pow(FF_sqrtn(x,d,NULL),a));
    }
  }
  i = (long) precision(n); if (i) prec=i;
  y = gmul(n, glog(x,prec));
  return gerepileupto(av, gexp(y,prec));
}

/********************************************************************/
/**                                                                **/
/**                        RACINE CARREE                           **/
/**                                                                **/
/********************************************************************/
/* assume x unit, precp(x) = pp > 3 */
static GEN
sqrt_2adic(GEN x, long pp)
{
  GEN z = mod16(x)==(signe(x)>=0?1:15)?gen_1: utoipos(3);
  long zp;
  pari_sp av, lim;

  if (pp == 4) return z;
  zp = 3; /* number of correct bits in z (compared to sqrt(x)) */

  av = avma; lim = stack_lim(av,2);
  for(;;)
  {
    GEN mod;
    zp = (zp<<1) - 1;
    if (zp > pp) zp = pp;
    mod = int2n(zp);
    z = addii(z, remi2n(mulii(x, Fp_inv(z,mod)), zp));
    z = shifti(z, -1); /* (z + x/z) / 2 */
    if (pp == zp) return z;

    if (zp < pp) zp--;

    if (low_stack(lim,stack_lim(av,2)))
    {
      if (DEBUGMEM > 1) pari_warn(warnmem,"Qp_sqrt");
      z = gerepileuptoint(av,z);
    }
  }
}

/* x unit defined modulo p^e, e > 0 */
static GEN
Up_sqrt(GEN x, GEN p, long e)
{
  pari_sp av = avma;
  if (equaliu(p,2))
  {
    long r = signe(x)>=0?mod8(x):8-mod8(x);
    if (e <= 3)
    {
      switch(e) {
      case 1: break;
      case 2: if ((r&3) == 1) break;
      case 3: if (r == 1) break;
              return NULL;
      }
      return gen_1;
    }
    else
    {
      if (r != 1) return NULL;
      return gerepileuptoint(av, sqrt_2adic(x, e));
    }
  }
  else
  {
    GEN z = Fp_sqrt(x, p);
    if (!z) return NULL;
    if (e <= 1) return z;
    return gerepileuptoint(av, Zp_sqrtlift(x, z, p, e));
  }
}

GEN
Qp_sqrt(GEN x)
{
  long pp, e = valp(x);
  GEN z,y,mod, p = gel(x,2);

  if (gequal0(x)) return zeropadic(p, (e+1) >> 1);
  if (e & 1) pari_err(talker,"odd exponent in p-adic sqrt");

  y = cgetg(5,t_PADIC);
  pp = precp(x);
  mod = gel(x,3);
  x   = gel(x,4); /* lift to t_INT */
  e >>= 1;
  z = Up_sqrt(x, p, pp);
  if (!z) pari_err(sqrter5);
  if (equaliu(p,2))
  {
    pp  = (pp <= 3) ? 1 : pp-1;
    mod = int2n(pp);
  }
  else mod = icopy(mod);
  y[1] = evalprecp(pp) | evalvalp(e);
  gel(y,2) = icopy(p);
  gel(y,3) = mod;
  gel(y,4) = z; return y;
}

GEN
Zn_sqrt(GEN d, GEN fn)
{
  pari_sp ltop = avma, btop, st_lim;
  GEN b = gen_0, m = gen_1;
  long j, np;
  if (typ(d) != t_INT)
    pari_err(typeer, "Zn_sqrt");
  if (typ(fn) == t_INT)
    fn = Z_factor(absi(fn));
  else if (!is_Z_factor(fn))
    pari_err(typeer, "Zn_sqrt");
  np = lg(gel(fn, 1))-1;
  btop = avma; st_lim = stack_lim(btop, 1);
  for (j = 1; j <= np; ++j)
  {
    GEN  bp, mp, pr, r;
    GEN  p = gcoeff(fn, j, 1);
    long e = itos(gcoeff(fn, j, 2));
    long v = Z_pvalrem(d,p,&r);
    if (v >= e) bp =gen_0;
    else
    {
      if (odd(v)) return NULL;
      bp = Up_sqrt(r, p, e-v);
      if (!bp)    return NULL;
      if (v) bp = mulii(bp, powiu(p, v>>1L));
    }
    mp = powiu(p, e);
    pr = mulii(m, mp);
    b = Z_chinese_coprime(b, bp, m, mp, pr);
    m = pr;
    if (low_stack(st_lim, stack_lim(btop, 1)))
      gerepileall(btop, 2, &b, &m);
  }
  return gerepileupto(ltop, b);
}

static GEN
sqrt_ser(GEN b, long prec)
{
  long e = valp(b), vx = varn(b), lx, lold, j;
  ulong mask;
  GEN a, x;

  if (!signe(b)) return zeroser(vx, e>>1);
  a = leafcopy(b);
  x = cgetg_copy(b, &lx);
  if (e & 1) pari_err(talker,"2 should divide valuation (= %ld) in sqrtn",e);
  a[1] = x[1] = evalsigne(1) | evalvarn(0) | _evalvalp(0);
  if (gissquareall(gel(a,2), &gel(x,2)) == gen_0)
    gel(x,2) = gsqrt(gel(a,2), prec);
  for (j = 3; j < lx; j++) gel(x,j) = gen_0;
  setlg(x,3);
  mask = quadratic_prec_mask(lx - 2);
  lold = 1;
  while (mask > 1)
  {
    GEN y, x2 = gmul2n(x,1);
    long l = lold << 1;

    if (mask & 1) l--;
    mask >>= 1;
    setlg(a, l + 2);
    setlg(x, l + 2);
    y = sqr_ser_part(x, lold, l-1) - lold;
    for (j = lold+2; j < l+2; j++) gel(y,j) = gsub(gel(y,j), gel(a,j));
    y += lold; setvalp(y, lold);
    y = gsub(x, gdiv(y, x2)); /* = gmuloldn(gadd(x, gdiv(a,x)), -1); */
    for (j = lold+2; j < l+2; j++) x[j] = y[j];
    lold = l;
  }
  x[1] = evalsigne(1) | evalvarn(vx) | _evalvalp(e >> 1);
  return x;
}

GEN
gsqrt(GEN x, long prec)
{
  pari_sp av;
  GEN y, p1;

  switch(typ(x))
  {
    case t_REAL: return sqrtr(x);

    case t_INTMOD:
      y = cgetg(3,t_INTMOD); gel(y,1) = icopy(gel(x,1));
      p1 = Fp_sqrt(gel(x,2),gel(y,1));
      if (!p1) pari_err(sqrter5);
      gel(y,2) = p1; return y;

    case t_COMPLEX:
      if (isrationalzero(gel(x,2))) return gsqrt(gel(x,1), prec);
      y = cgetg(3,t_COMPLEX); av = avma;

      p1 = gsqrt(cxnorm(x), prec);
      if (typ(p1) == t_INTMOD) pari_err(impl,"sqrt(complex of t_INTMODs)");
      if (!signe(p1)) { gel(y,1) = gel(y,2) = sqrtr(p1); return y; }
      if (gsigne(gel(x,1)) < 0)
      {
        p1 = sqrtr( gmul2n(gsub(p1,gel(x,1)), -1) );
        if (gsigne(gel(x,2)) < 0) togglesign(p1);
        gel(y,2) = gerepileuptoleaf(av, p1); av = avma;
        gel(y,1) = gerepileuptoleaf(av, gdiv(gel(x,2), gmul2n(p1,1)));
      } else {
        p1 = sqrtr( gmul2n(gadd(p1,gel(x,1)), -1) );
        gel(y,1) = gerepileuptoleaf(av, p1); av = avma;
        gel(y,2) = gerepileuptoleaf(av, gdiv(gel(x,2), gmul2n(p1,1)));
      }
      return y;

    case t_PADIC:
      return Qp_sqrt(x);

    case t_FFELT: return FF_sqrt(x);

    default:
      av = avma; if (!(y = toser_i(x))) break;
      return gerepilecopy(av, sqrt_ser(y, prec));
  }
  return transc(gsqrt,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                          N-th ROOT                             **/
/**                                                                **/
/********************************************************************/
/* exp(2Ipi/n), assume n positive t_INT */
GEN
rootsof1complex(GEN n, long prec)
{
  pari_sp av = avma;
  if (is_pm1(n)) return real_1(prec);
  if (lgefint(n)==3 && n[2]==2) return stor(-1, prec);
  return gerepileupto(av, exp_Ir( divri(Pi2n(1, prec), n) ));
}

/*Only the O() of y is used*/
GEN
rootsof1padic(GEN n, GEN y)
{
  pari_sp av0 = avma, av;
  GEN z, r = cgetp(y);

  av = avma; (void)Fp_sqrtn(gen_1,n,gel(y,2),&z);
  if (z==gen_0) { avma = av0; return gen_0; }/*should not happen*/
  z = Zp_sqrtnlift(gen_1, n, z, gel(y,2), precp(y));
  affii(z, gel(r,4)); avma = av; return r;
}

/* Let x = 1 mod p and y := (x-1)/(x+1) = 0 (p). Then
 * log(x) = log(1+y) - log(1-y) = 2 \sum_{k odd} y^k / k.
 * palogaux(x) returns the last sum (not multiplied by 2) */
static GEN
palogaux(GEN x)
{
  long k,e,pp;
  GEN y,s,y2, p = gel(x,2);

  if (equalii(gen_1, gel(x,4)))
  {
    long v = valp(x)+precp(x);
    if (equaliu(p,2)) v--;
    return zeropadic(p, v);
  }
  y = gdiv(gaddgs(x,-1), gaddgs(x,1));
  e = valp(y); /* > 0 */
  if (e <= 0) {
    if (!BPSW_psp(p))
      pari_err(talker, "error in p-adic log, %Ps is not a prime", p);
    pari_err(bugparier, "log_p");
  }
  pp = e+precp(y);
  if (equaliu(p,2)) pp--;
  else
  {
    GEN p1;
    for (p1=utoipos(e); cmpui(pp,p1) > 0; pp++) p1 = mulii(p1, p);
    pp -= 2;
  }
  k = pp/e; if (!odd(k)) k--;
  y2 = gsqr(y); s = gdivgs(gen_1,k);
  while (k > 2)
  {
    k -= 2; s = gadd(gmul(y2,s), gdivgs(gen_1,k));
  }
  return gmul(s,y);
}

GEN
Qp_log(GEN x)
{
  pari_sp av = avma;
  GEN y, p = gel(x,2), a = gel(x,4);

  if (!signe(a)) pari_err(talker,"zero argument in Qp_log");
  if (equaliu(p,2))
  {
    y = gsqr(x); setvalp(y,0);
    y = palogaux(y);
  }
  else if (gequal1(modii(a, p)))
  {
    y = gmul2n(palogaux(x), 1);
  }
  else
  { /* compute log(x^(p-1)) / (p-1) */
    GEN mod = gel(x,3), p1 = subis(p,1);
    y = cgetp(x);
    gel(y,4) = Fp_pow(a, p1, mod);
    p1 = diviiexact(subsi(1,mod), p1); /* 1/(p-1) */
    y = gmul(palogaux(y), shifti(p1,1));
  }
  return gerepileupto(av,y);
}

static GEN Qp_exp_safe(GEN x);

/*compute the p^e th root of x p-adic, assume x != 0 */
static GEN
Qp_sqrtn_ram(GEN x, long e)
{
  pari_sp ltop=avma;
  GEN a, p = gel(x,2), n = powiu(p,e);
  long v = valp(x);
  if (v)
  {
    long z;
    v = sdivsi_rem(v, n, &z);
    if (z) return NULL;
    x = gcopy(x); setvalp(x,0);
  }
  /*If p=2 -1 is an root of unity in U1,we need an extra check*/
  if (lgefint(p)==3 && p[2]==2 && mod8(gel(x,4))!=signe(gel(x,4)))
    return NULL;
  a = Qp_exp_safe(gdiv(Qp_log(x), n));
  if (!a) return NULL;
  /*Here n=p^e and a^n=z*x where z is a (p-1)th-root of unity. Note that
      z^p=z; hence for b = a/z, then b^n=x. We say b=x/a^(n-1)*/
  a = gdiv(x, powgi(a,addis(n,-1))); if (v) setvalp(a,v);
  return gerepileupto(ltop,a);
}

/*compute the nth root of x p-adic p prime with n*/
static GEN
Qp_sqrtn_unram(GEN x, GEN n, GEN *zetan)
{
  pari_sp av;
  GEN Z, a, r, p = gel(x,2);
  long v = valp(x);
  if (v)
  {
    long z;
    v = sdivsi_rem(v,n,&z);
    if (z) return NULL;
  }
  r = cgetp(x); setvalp(r,v);
  Z = NULL; /* -Wall */
  if (zetan) Z = cgetp(x);
  av = avma; a = Fp_sqrtn(gel(x,4), n, p, zetan);
  if (!a) return NULL;
  affii(Zp_sqrtnlift(gel(x,4), n, a, p, precp(x)), gel(r,4));
  if (zetan)
  {
    affii(Zp_sqrtnlift(gen_1, n, *zetan, p, precp(x)), gel(Z,4));
    *zetan = Z;
  }
  avma = av; return r;
}

GEN
Qp_sqrtn(GEN x, GEN n, GEN *zetan)
{
  pari_sp av = avma, tetpil;
  GEN q, p = gel(x,2);
  long e;
  if (!signe(x[4]))
  {
    long m = itos(n);
    if (zetan) *zetan = gen_1;
    return zeropadic(p, (valp(x)+m-1)/m);
  }
  /* treat the ramified part using logarithms */
  e = Z_pvalrem(n, p, &q);
  if (e) { x = Qp_sqrtn_ram(x,e); if (!x) return NULL; }
  if (is_pm1(q))
  { /* finished */
    if (signe(q) < 0) x = ginv(x);
    x = gerepileupto(av, x);
    if (zetan)
      *zetan = (e && lgefint(p)==3 && p[2]==2)? gen_m1 /*-1 in Q_2*/
                                              : gen_1;
    return x;
  }
  tetpil = avma;
  /* use hensel lift for unramified case */
  x = Qp_sqrtn_unram(x, q, zetan);
  if (!x) return NULL;
  if (zetan)
  {
    GEN *gptr[2];
    if (e && lgefint(p)==3 && p[2]==2)/*-1 in Q_2*/
    {
      tetpil = avma; x = gcopy(x); *zetan = gneg(*zetan);
    }
    gptr[0] = &x; gptr[1] = zetan;
    gerepilemanysp(av,tetpil,gptr,2);
    return x;
  }
  return gerepile(av,tetpil,x);
}

GEN
gsqrtn(GEN x, GEN n, GEN *zetan, long prec)
{
  long i, lx, tx;
  pari_sp av;
  GEN y, z;
  if (typ(n)!=t_INT) pari_err(talker,"second arg must be integer in gsqrtn");
  if (!signe(n)) pari_err(talker,"1/0 exponent in gsqrtn");
  if (is_pm1(n))
  {
    if (zetan) *zetan = gen_1;
    return (signe(n) > 0)? gcopy(x): ginv(x);
  }
  if (zetan) *zetan = gen_0;
  tx = typ(x);
  if (is_matvec_t(tx))
  {
    y = cgetg_copy(x, &lx);
    for (i=1; i<lx; i++) gel(y,i) = gsqrtn(gel(x,i),n,NULL,prec);
    return y;
  }
  av = avma;
  switch(tx)
  {
  case t_INTMOD:
    z = gen_0;
    y = cgetg(3,t_INTMOD);  gel(y,1) = icopy(gel(x,1));
    if (zetan) { z = cgetg(3,t_INTMOD); gel(z,1) = gel(y,1); }
    gel(y,2) = Fp_sqrtn(gel(x,2),n,gel(x,1),zetan);
    if (!y[2]) {
      if (zetan) {avma=av; return gen_0;}
      pari_err(talker,"nth-root does not exist in gsqrtn");
    }
    if (zetan) { gel(z,2) = *zetan; *zetan = z; }
    return y;

  case t_PADIC:
    y = Qp_sqrtn(x,n,zetan);
    if (!y) {
      if (zetan) return gen_0;
      pari_err(talker,"nth-root does not exist in gsqrtn");
    }
    return y;

  case t_FFELT: return FF_sqrtn(x,n,zetan);

  case t_INT: case t_FRAC: case t_REAL: case t_COMPLEX:
    i = precision(x); if (i) prec = i;
    if (tx==t_INT && is_pm1(x) && signe(x) > 0)
     /*speed-up since there is no way to call rootsof1complex from gp*/
      y = real_1(prec);
    else if (gequal0(x))
    {
      if (signe(n) < 0) pari_err(gdiver);
      if (isinexactreal(x))
      {
        long e = gexpo(x), junk;
        y = real_0_bit(e < 2? 0: sdivsi_rem(e, n, &junk));
      }
      else
        y = real_0(prec);
    }
    else
      y = gerepileupto(av, gexp(gdiv(glog(x,prec), n), prec));
    if (zetan) *zetan = rootsof1complex(n,prec);
    return y;

  case t_QUAD:
    return gsqrtn(quadtofp(x, prec), n, zetan, prec);

  default:
    av = avma; if (!(y = toser_i(x))) break;
    return gerepileupto(av, ser_powfrac(y, ginv(n), prec));
  }
  pari_err(typeer,"gsqrtn");
  return NULL;/* not reached */
}

/********************************************************************/
/**                                                                **/
/**                             EXP(X) - 1                         **/
/**                                                                **/
/********************************************************************/
/* exp(|x|) - 1, assume x != 0.
 * For efficiency, x should be reduced mod log(2): if so, we have a < 0 */
GEN
exp1r_abs(GEN x)
{
  long l = lg(x), a = expo(x), b = bit_accuracy(l), L, i, n, m, e, B;
  GEN y, p2, X;
  pari_sp av;
  double d;

  if (b + a <= 0) return mpabs(x);

  y = cgetr(l); av = avma;
  B = b/3 + BITS_IN_LONG + (BITS_IN_LONG*BITS_IN_LONG)/ b;
  d = a/2.; m = (long)(d + sqrt(d*d + B)); /* >= 0 */
  if (m < (-a) * 0.1) m = 0; /* not worth it */
  L = l + nbits2nlong(m);
 /* Multiplication is quadratic in this range (l is small, otherwise we
  * use logAGM + Newton). Set Y = 2^(-e-a) x, compute truncated series
  * sum x^k/k!: this costs roughly
  *    m b^2 + sum_{k <= n} (k e + BITS_IN_LONG)^2
  * bit operations with |x| <  2^(1+a), |Y| < 2^(1-e) , m = e+a and b bits of
  * accuracy needed, so
  *    B := (b / 3 + BITS_IN_LONG + BITS_IN_LONG^2 / b) ~ m(m-a)
  * we want b ~ 3 m (m-a) or m~b+a hence
  *     m = min( a/2 + sqrt(a^2/4 + B),  b + a )
  * NB: e ~ (b/3)^(1/2) as b -> oo
  *
  * Truncate the sum at k = n (>= 1), the remainder is
  *   sum_{k >= n+1} Y^k / k! < Y^(n+1) / (n+1)! (1-Y) < Y^(n+1) / n!
  * We want Y^(n+1) / n! <= Y 2^-b, hence -n log_2 |Y| + log_2 n! >= b
  *   log n! ~ (n + 1/2) log(n+1) - (n+1) + log(2Pi)/2,
  * error bounded by 1/6(n+1) <= 1/12. Finally, we want
  * n (-1/log(2) -log_2 |Y| + log_2(n+1)) >= b  */
  b += m;
  e = m - a; /* >= 1 */
  /* ~ -1/log(2) - log_2 Y */
  d = e+BITS_IN_LONG-1-1/LOG2 - log2((double)(ulong)x[2]);
  n = (long)(b / d);
  if (n > 1)
    n = (long)(b / (d + log2((double)n+1))); /* log~constant in small ranges */
  while (n*(d+log2((double)n+1)) < b) n++; /* expect few corrections */

  X = rtor(x,L); X[1] = evalsigne(1) | evalexpo(-e);
  if (n == 1) p2 = X;
  else
  {
    long s = 0, l1 = nbits2prec((long)(d + n + 16));
    GEN unr = real_1(L);
    pari_sp av2;

    p2 = cgetr(L); av2 = avma;
    for (i=n; i>=2; i--, avma = av2)
    { /* compute X^(n-1)/n! + ... + X/2 + 1 */
      GEN p1, p3;
      setlg(X,l1); p3 = divru(X,i);
      l1 += dvmdsBIL(s - expo(p3), &s); if (l1>L) l1=L;
      setlg(unr,l1); p1 = addrr_sign(unr,1, i == n? p3: mulrr(p3,p2),1);
      setlg(p2,l1); affrr(p1,p2); /* p2 <- 1 + (X/i)*p2 */
    }
    setlg(X,L); p2 = mulrr(X,p2);
  }

  for (i=1; i<=m; i++)
  {
    if (lg(p2) > L) setlg(p2,L);
    p2 = mulrr(p2, addsr(2,p2));
  }
  affrr_fixlg(p2,y); avma = av; return y;
}

GEN
mpexp1(GEN x)
{
  long sx = signe(x);
  GEN y, z;
  pari_sp av;
  if (!sx) return real_0_bit(expo(x));
  if (sx > 0) return exp1r_abs(x);
  /* compute exp(x) * (1 - exp(-x)) */
  av = avma; y = exp1r_abs(x);
  z = addsr(1, y); setsigne(z, -1);
  return gerepileupto(av, divrr(y, z));
}

/********************************************************************/
/**                                                                **/
/**                             EXP(X)                             **/
/**                                                                **/
/********************************************************************/

/* centermod(x, log(2)), set *sh to the quotient */
static GEN
modlog2(GEN x, long *sh)
{
  double d = rtodbl(x);
  long q = (long) ((fabs(d) + (LOG2/2))/LOG2);
  if (d > LOG2 * LONG_MAX)
    pari_err(overflower, "expo()"); /* avoid overflow in  q */
  if (d < 0) q = -q;
  *sh = q;
  if (q) {
    long l = lg(x) + 1;
    x = subrr(rtor(x,l), mulsr(q, mplog2(l)));
    if (!signe(x)) return NULL;
  }
  return x;
}

static GEN
mpexp_basecase(GEN x)
{
  pari_sp av = avma;
  long sh, l = lg(x);
  GEN y, z;

  y = modlog2(x, &sh);
  if (!y) { avma = av; return real2n(sh, l); }
  z = addsr(1, exp1r_abs(y));
  if (signe(y) < 0) z = invr(z);
  if (sh) {
    setexpo(z, expo(z)+sh);
    if (lg(z) > l) z = rtor(z, l); /* spurious precision increase */
  }
#ifdef DEBUG
{
  GEN t = mplog(z), u = divrr(subrr(x, t),x);
  if (signe(u) && expo(u) > 5-bit_accuracy(minss(l,lg(t)))) pari_err(talker,"");
}
#endif
  return gerepileuptoleaf(av, z); /* NOT affrr, precision often increases */
}

GEN
mpexp(GEN x)
{
  const long s = 6; /*Initial steps using basecase*/
  long i, p, l = lg(x), sh;
  GEN a, t, z;
  ulong mask;

  if (l <= maxss(EXPNEWTON_LIMIT, (1L<<s) + 2))
  {
    if (l == 2) {
      long e = expo(x);
      return e >= 0? real_0_bit(e): real_1(nbits2prec(-e));
    }
    return mpexp_basecase(x);
  }
  z = cgetr(l); /* room for result */
  x = modlog2(x, &sh);
  if (!x) { avma = (pari_sp)(z+l); return real2n(sh, l); }
  mask = quadratic_prec_mask(l-1);
  for(i=0, p=1; i<s; i++) { p <<= 1; if (mask & 1) p--; mask >>= 1; }
  a = mpexp_basecase(rtor(x, p+2));
  x = addrs(x,1);
  if (lg(x) < l+1) x = rtor(x, l+1);
  a = rtor(a, l+1); /*append 0s */
  t = NULL;
  for(;;)
  {
    p <<= 1; if (mask & 1) p--;
    mask >>= 1;
    setlg(x, p+2);
    setlg(a, p+2);
    t = mulrr(a, subrr(x, logr_abs(a))); /* a (x - log(a)) */
    if (mask == 1) break;
    affrr(t, a); avma = (pari_sp)a;
  }
  affrr(t,z);
  if (sh) setexpo(z, expo(z) + sh);
  avma = (pari_sp)z; return z;
}

static long
Qp_exp_prec(GEN x)
{
  long k, e = valp(x), n = e + precp(x);
  GEN p = gel(x,2);
  int is2 = equaliu(p,2);
  if (e < 1 || (e == 1 && is2)) return -1;
  if (is2)
  {
    n--; e--; k = n/e;
    if (n%e == 0) k--;
  }
  else
  { /* e > 0, n > 0 */
    GEN r, t = subis(p, 1);
    k = itos(dvmdii(subis(muliu(t,n), 1), subis(muliu(t,e), 1), &r));
    if (!signe(r)) k--;
  }
  return k;
}

static GEN
Qp_exp_safe(GEN x)
{
  long k;
  pari_sp av;
  GEN y;

  if (gequal0(x)) return gaddgs(x,1);
  k = Qp_exp_prec(x);
  if (k < 0) return NULL;
  av = avma;
  for (y=gen_1; k; k--) y = gaddsg(1, gdivgs(gmul(y,x), k));
  return gerepileupto(av, y);
}

GEN
Qp_exp(GEN x)
{
  GEN y = Qp_exp_safe(x);
  if (!y) pari_err(talker,"p-adic argument out of range in gexp");
  return y;
}

static GEN
cos_p(GEN x)
{
  long k;
  pari_sp av;
  GEN x2, y;

  if (gequal0(x)) return gaddgs(x,1);
  k = Qp_exp_prec(x);
  if (k < 0) return NULL;
  av = avma; x2 = gsqr(x);
  if (k & 1) k--;
  for (y=gen_1; k; k-=2)
  {
    GEN t = gdiv(gmul(y,x2), muluu(k, k-1));
    y = gsubsg(1, t);
  }
  return gerepileupto(av, y);
}
static GEN
sin_p(GEN x)
{
  long k;
  pari_sp av;
  GEN x2, y;

  if (gequal0(x)) return gaddgs(x,1);
  k = Qp_exp_prec(x);
  if (k < 0) return NULL;
  av = avma; x2 = gsqr(x);
  if (k & 1) k--;
  for (y=gen_1; k; k-=2)
  {
    GEN t = gdiv(gmul(y,x2), muluu(k, k+1));
    y = gsubsg(1, t);
  }
  return gerepileupto(av, gmul(y, x));
}

static GEN
cxexp(GEN x, long prec)
{
  GEN r,p1,p2, y = cgetg(3,t_COMPLEX);
  pari_sp av = avma, tetpil;
  r = gexp(gel(x,1),prec);
  if (gequal0(r)) { gel(y,1) = r; gel(y,2) = r; return y; }
  gsincos(gel(x,2),&p2,&p1,prec);
  tetpil = avma;
  gel(y,1) = gmul(r,p1);
  gel(y,2) = gmul(r,p2);
  gerepilecoeffssp(av,tetpil,y+1,2);
  return y;
}

static GEN
serexp(GEN x, long prec)
{
  pari_sp av;
  long i,j,lx,ly,ex,mi;
  GEN p1,y,xd,yd;

  ex = valp(x);
  if (ex < 0) pari_err(negexper,"gexp");
  if (gequal0(x)) return gaddsg(1,x);
  lx = lg(x);
  if (ex)
  {
    ly = lx+ex; y = cgetg(ly,t_SER);
    mi = lx-1; while (mi>=3 && isrationalzero(gel(x,mi))) mi--;
    mi += ex-2;
    y[1] = evalsigne(1) | _evalvalp(0) | evalvarn(varn(x));
    /* zd[i] = coefficient of X^i in z */
    xd = x+2-ex; yd = y+2; ly -= 2;
    gel(yd,0) = gen_1;
    for (i=1; i<ex; i++) gel(yd,i) = gen_0;
    for (   ; i<ly; i++)
    {
      av = avma; p1 = gen_0;
      for (j=ex; j<=minss(i,mi); j++)
        p1 = gadd(p1, gmulgs(gmul(gel(xd,j),gel(yd,i-j)),j));
      gel(yd,i) = gerepileupto(av, gdivgs(p1,i));
    }
    return y;
  }
  av = avma; y = cgetg(lx, t_SER);
  y[1] = x[1]; gel(y,2) = gen_0;
  for (i=3; i <lx; i++) y[i] = x[i];
  p1 = gexp(gel(x,2),prec);
  y = gmul(p1, serexp(normalize(y),prec));
  return gerepileupto(av, y);
}

GEN
gexp(GEN x, long prec)
{
  switch(typ(x))
  {
    case t_REAL: return mpexp(x);
    case t_COMPLEX: return cxexp(x,prec);
    case t_PADIC: return Qp_exp(x);
    case t_INTMOD: pari_err(typeer,"gexp");
    default:
    {
      pari_sp av = avma;
      GEN y;
      if (!(y = toser_i(x))) break;
      return gerepileupto(av, serexp(y,prec));
    }
  }
  return transc(gexp,x,prec);
}

/********************************************************************/
/**                                                                **/
/**                           AGM(X, Y)                            **/
/**                                                                **/
/********************************************************************/
static int
agmr_gap(GEN a, GEN b, long L)
{
  GEN d = subrr(b, a);
  return (signe(d) && expo(d) - expo(b) >= L);
}
/* assume x > 0 */
static GEN
agm1r_abs(GEN x)
{
  long l = lg(x), L = 5-bit_accuracy(l);
  GEN a1, b1, y = cgetr(l);
  pari_sp av = avma;

  a1 = addrr(real_1(l), x); setexpo(a1, expo(a1)-1);
  b1 = sqrtr_abs(x);
  while (agmr_gap(a1,b1,L))
  {
    GEN a = a1;
    a1 = addrr(a,b1); setexpo(a1, expo(a1)-1);
    b1 = sqrtr_abs(mulrr(a,b1));
  }
  affrr_fixlg(a1,y); avma = av; return y;
}

static int
agmcx_gap(GEN a, GEN b, long L)
{
  GEN d = gsub(b, a);
  return (!gequal0(d) && gexpo(d) - gexpo(b) >= L);
}
static GEN
agm1cx(GEN x, long prec)
{
  GEN a1, b1;
  pari_sp av = avma, av2;
  long L, l = precision(x); if (!l) l = prec;

  L = 5-bit_accuracy(l);
  a1 = gtofp(gmul2n(gadd(real_1(l), x), -1), l); /* avoid loss of accuracy */
  av2 = avma;
  b1 = gsqrt(x, prec);
  while (agmcx_gap(a1,b1,L))
  {
    GEN a = a1;
    a1 = gmul2n(gadd(a,b1),-1);
    av2 = avma;
    b1 = gsqrt(gmul(a,b1), prec);
  }
  avma = av2; return gerepileupto(av,a1);
}

/* agm(1,x) */
static GEN
agm1(GEN x, long prec)
{
  GEN p1, a, a1, b1, y;
  long l, l2, ep;
  pari_sp av;

  if (gequal0(x)) return gcopy(x);
  switch(typ(x))
  {
    case t_INT:
      if (!is_pm1(x)) break;
      return (signe(x) > 0)? real_1(prec): real_0(prec);

    case t_REAL: return signe(x) > 0? agm1r_abs(x): agm1cx(x, prec);

    case t_COMPLEX:
      if (gequal0(gel(x,2)) && gsigne(gel(x,1)) > 0)
        return agm1(gel(x,1), prec);
      return agm1cx(x, prec);

    case t_PADIC:
      av = avma;
      a1 = x; b1 = gen_1; l = precp(x);
      do
      {
        a = a1;
        a1 = gmul2n(gadd(a,b1),-1);
        b1 = Qp_sqrt(gmul(a,b1));
        p1 = gsub(b1,a1); ep = valp(p1)-valp(b1);
        if (ep<=0) { b1 = gneg_i(b1); p1 = gsub(b1,a1); ep=valp(p1)-valp(b1); }
      }
      while (ep<l && !gequal0(p1));
      return gerepilecopy(av,a1);

    default:
      av = avma; if (!(y = toser_i(x))) break;
      a1 = y; b1 = gen_1; l = lg(y)-2;
      l2 = 5-bit_accuracy(prec);
      do
      {
        a = a1;
        a1 = gmul2n(gadd(a,b1),-1);
        b1 = ser_powfrac(gmul(a,b1), ghalf, prec);
        p1 = gsub(b1,a1); ep = valp(p1)-valp(b1);
      }
      while (ep<l && !gequal0(p1)
                  && (!isinexactreal(p1) || gexpo(p1) - gexpo(b1) >= l2));
      return gerepilecopy(av,a1);
  }
  return transc(agm1,x,prec);
}

GEN
agm(GEN x, GEN y, long prec)
{
  long ty = typ(y);
  pari_sp av;

  if (is_matvec_t(ty))
  {
    ty = typ(x);
    if (is_matvec_t(ty)) pari_err(talker,"agm of two vector/matrices");
    swap(x, y);
  }
  if (gequal0(y)) return gcopy(y);
  av = avma;
  return gerepileupto(av, gmul(y, agm1(gdiv(x,y), prec)));
}

/********************************************************************/
/**                                                                **/
/**                             LOG(X)                             **/
/**                                                                **/
/********************************************************************/
/* cf logagmr_abs(). Compute Pi/2agm(1, 4/2^n) ~ log(2^n) = n log(2) */
GEN
constlog2(long prec)
{
  pari_sp av;
  long l, n;
  GEN y, tmplog2;

  if (glog2 && lg(glog2) >= prec) return glog2;

  tmplog2 = newblock(prec);
  *tmplog2 = evaltyp(t_REAL) | evallg(prec);
  av = avma;
  l = prec+1;
  n = bit_accuracy(l) >> 1;
  y = divrr(Pi2n(-1, l), agm1r_abs( real2n(2 - n, l) ));
  affrr(divru(y,n), tmplog2);
  if (glog2) gunclone(glog2);
  avma = av; return glog2 = tmplog2;
}

GEN
mplog2(long prec) { return rtor(constlog2(prec), prec); }

static GEN
logagmr_abs(GEN q)
{
  long prec = lg(q), lim, e = expo(q);
  GEN z, y, Q, _4ovQ;
  pari_sp av;

  if (absrnz_egal2n(q)) return e? mulsr(e, mplog2(prec)): real_0(prec);
  z = cgetr(prec); av = avma; prec++;
  lim = bit_accuracy(prec) >> 1;
  Q = rtor(q,prec);
  Q[1] = evalsigne(1) | evalexpo(lim);

  _4ovQ = invr(Q); setexpo(_4ovQ, expo(_4ovQ)+2); /* 4/Q */
  /* Pi / 2agm(1, 4/Q) ~ log(Q), q = Q * 2^(e-lim) */
  y = divrr(Pi2n(-1, prec), agm1r_abs(_4ovQ));
  y = addrr(y, mulsr(e - lim, mplog2(prec)));
  affrr_fixlg(y, z); avma = av; return z;
}
/*return log(|x|), assuming x != 0 */
GEN
logr_abs(GEN X)
{
  pari_sp ltop;
  long EX, L, m, k, a, b, l = lg(X);
  GEN z, x, y;
  ulong u;
  int neg;
  double d;

  if (l > LOGAGM_LIMIT) return logagmr_abs(X);

 /* Assuming 1 < x < 2, we want delta = x-1, 1-x/2, 1-1/x, or 2/x-1 small.
  * We have 2/x-1 > 1-x/2, 1-1/x < x-1. So one should be choosing between
  * 1-1/x and 1-x/2 ( crossover sqrt(2), worse ~ 0.29 ). To avoid an inverse,
  * we choose between x-1 and 1-x/2 ( crossover 4/3, worse ~ 0.33 ) */
  EX = expo(X);
  u = (ulong)X[2];
  k = 2;
  if (u > (~0UL / 3) * 2) { /* choose 1-x/2 */
    EX++; u = ~u;
    while (!u && ++k < l) { u = (ulong)X[k]; u = ~u; }
    neg = 1;
  } else { /* choose x - 1 */
    u &= ~HIGHBIT; /* u - HIGHBIT, assuming HIGHBIT set */
    while (!u && ++k < l) u = (ulong)X[k];
    neg = 0;
  }
  if (k == l) return EX? mulsr(EX, mplog2(l)): real_0(l);
  z = cgetr(EX? l: l - (k-2)); ltop = avma;

  a = bit_accuracy(k) + bfffo(u); /* ~ -log2 |1-x| */
 /* Multiplication is quadratic in this range (l is small, otherwise we
  * use AGM). Set Y = x^(1/2^m), y = (Y - 1) / (Y + 1) and compute truncated
  * series sum y^(2k+1)/(2k+1): the costs is less than
  *    m b^2 + sum_{k <= n} ((2k+1) e + BITS_IN_LONG)^2
  * bit operations with |x-1| <  2^(1-a), |Y| < 2^(1-e) , m = e-a and b bits of
  * accuracy needed (+ BITS_IN_LONG since bit accuracies increase by
  * increments of BITS_IN_LONG), so
  * 4n^3/3 e^2 + n^2 2e BITS_IN_LONG+ n BITS_IN_LONG ~ m b^2, with n ~ b/2e
  * or b/6e + BITS_IN_LONG/2e + BITS_IN_LONG/2be ~ m
  *    B := (b / 6 + BITS_IN_LONG/2 + BITS_IN_LONG^2 / 2b) ~ m(m+a)
  *     m = min( -a/2 + sqrt(a^2/4 + B),  b - a )
  * NB: e ~ (b/6)^(1/2) as b -> oo */
  L = l+1;
  b = bit_accuracy(L - (k-2)); /* take loss of accuracy into account */
  /* instead of the above pessimistic estimate for the cost of the sum, use
   * optimistic estimate (BITS_IN_LONG -> 0) */
  d = -a/2.; m = (long)(d + sqrt(d*d + b/6)); /* >= 0 */

  if (m > b-a) m = b-a;
  if (m < 0.2*a) m = 0; else L += divsBIL(m);
  x = rtor(X,L);
  if (neg) x[1] = evalsigne(1) | _evalexpo(-1);
  else     x[1] = evalsigne(1) | _evalexpo(0);
  /* 2/3 < x < 4/3 */
  for (k=1; k<=m; k++) x = sqrtr_abs(x);

  y = divrr(subrs(x,1), addrs(x,1)); /* = (x-1) / (x+1), close to 0 */
  L = lg(y); /* should be ~ l+1 - (k-2) */
  /* log(x) = log(1+y) - log(1-y) = 2 sum_{k odd} y^k / k
   * Truncate the sum at k = 2n+1, the remainder is
   *   2 sum_{k >= 2n+3} y^k / k < 2y^(2n+3) / (2n+3)(1-y) < y^(2n+3)
   * We want y^(2n+3) < y 2^(-bit_accuracy(L)), hence
   *   n+1 > bit_accuracy(L) /-log_2(y^2) */
  d = -2*dbllog2r(y); /* ~ -log_2(y^2) */
  k = (long)(2*(bit_accuracy(L) / d));
  k |= 1;
  if (k >= 3)
  {
    GEN S, T, y2 = sqrr(y), unr = real_1(L);
    pari_sp av = avma;
    long s = 0, incs = (long)d, l1 = nbits2prec((long)d);
    S = x;
    setlg(S,  l1);
    setlg(unr,l1); affrr(divru(unr,k), S); /* destroy x, not needed anymore */
    for (k -= 2;; k -= 2) /* k = 2n+1, ..., 1 */
    { /* S = y^(2n+1-k)/(2n+1) + ... + 1 / k */
      setlg(y2, l1); T = mulrr(S,y2);
      if (k == 1) break;

      l1 += dvmdsBIL(s + incs, &s); if (l1>L) l1=L;
      setlg(S, l1);
      setlg(unr,l1);
      affrr(addrr(divru(unr, k), T), S); avma = av;
    }
    /* k = 1 special-cased for eficiency */
    y = mulrr(y, addsr(1,T)); /* = log(X)/2 */
  }
  setexpo(y, expo(y)+m+1);
  if (EX) y = addrr(y, mulsr(EX, mplog2(l+1)));
  affrr_fixlg(y, z); avma = ltop; return z;
}

/* assume Im(q) != 0 */
GEN
logagmcx(GEN q, long prec)
{
  GEN z, y, Q, a, b;
  long lim, e, ea, eb;
  pari_sp av;
  int neg = 0;

  e = precision(q); if (e > prec) prec = e;
  z = cgetc(prec); av = avma; prec++;
  if (gsigne(gel(q,1)) < 0) { q = gneg(q); neg = 1; }
  lim = bit_accuracy(prec) >> 1;
  Q = gtofp(q, prec);
  a = gel(Q,1);
  b = gel(Q,2);
  if (gequal0(a)) {
    affrr_fixlg(logr_abs(b), gel(z,1));
    y = Pi2n(-1, prec);
    if (signe(b) < 0) setsigne(y, -1);
    affrr_fixlg(y, gel(z,2)); avma = av; return z;
  }
  ea = expo(a);
  eb = expo(b);
  if (ea <= eb)
  {
    setexpo(Q[1], lim - eb + ea);
    setexpo(Q[2], lim);
    e = lim - eb;
  } else {
    setexpo(Q[1], lim);
    setexpo(Q[2], lim - ea + eb);
    e = lim - ea;
  }

  /* Pi / 2agm(1, 4/Q) ~ log(Q), q = Q * 2^e */
  y = gdiv(Pi2n(-1, prec), agm1cx( gdivsg(4, Q), prec ));
  a = gel(y,1);
  b = gel(y,2);
  a = addrr(a, mulsr(-e, mplog2(prec)));
  if (lg(a) == 3) a = real_0_bit(expo(a));
  if (neg) b = gsigne(b) <= 0? gadd(b, mppi(prec))
                             : gsub(b, mppi(prec));
  affrr_fixlg(a, gel(z,1));
  affrr_fixlg(b, gel(z,2)); avma = av; return z;
}

GEN
mplog(GEN x)
{
  if (signe(x)<=0) pari_err(talker,"non positive argument in mplog");
  return logr_abs(x);
}

GEN
teich(GEN x)
{
  GEN p,q,y,z,aux,p1;
  long n, k;
  pari_sp av;

  if (typ(x)!=t_PADIC) pari_err(talker,"not a p-adic argument in teichmuller");
  if (!signe(x[4])) return gcopy(x);
  p = gel(x,2);
  q = gel(x,3);
  z = gel(x,4); y = cgetp(x); av = avma;
  if (equaliu(p,2))
    z = (mod4(z) & 2)? addsi(-1,q): gen_1;
  else
  {
    p1 = addsi(-1, p);
    z = remii(z, p);
    aux = diviiexact(addsi(-1,q),p1); n = precp(x);
    for (k=1; k<n; k<<=1)
      z = Fp_mul(z,addsi(1,mulii(aux,addsi(-1,Fp_pow(z,p1,q)))), q);
  }
  affii(z, gel(y,4)); avma = av; return y;
}

GEN
glog(GEN x, long prec)
{
  pari_sp av, tetpil;
  GEN y, p1;

  switch(typ(x))
  {
    case t_REAL:
      if (signe(x) >= 0)
      {
        if (!signe(x)) pari_err(talker,"zero argument in mplog");
        return logr_abs(x);
      }
      y = cgetg(3,t_COMPLEX);
      gel(y,1) = logr_abs(x);
      gel(y,2) = mppi(lg(x)); return y;

    case t_COMPLEX:
      if (gequal0(gel(x,2))) return glog(gel(x,1), prec);
      if (prec > LOGAGMCX_LIMIT) return logagmcx(x, prec);
      y = cgetg(3,t_COMPLEX);
      gel(y,2) = garg(x,prec);
      av = avma; p1 = glog(cxnorm(x),prec); tetpil = avma;
      gel(y,1) = gerepile(av,tetpil,gmul2n(p1,-1)); return y;

    case t_PADIC:
      return Qp_log(x);

    case t_INTMOD: pari_err(typeer,"glog");
    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (valp(y) || gequal0(y)) pari_err(talker,"log is not meromorphic at 0");
      p1 = integ(gdiv(derivser(y), y), varn(y)); /* log(y)' = y'/y */
      if (!gequal1(gel(y,2))) p1 = gadd(p1, glog(gel(y,2),prec));
      return gerepileupto(av, p1);
  }
  return transc(glog,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                        SINE, COSINE                            **/
/**                                                                **/
/********************************************************************/

/* Reduce x0 mod Pi/2 to x in [-Pi/4, Pi/4]. Return cos(x)-1 */
static GEN
mpsc1(GEN x, long *ptmod8)
{
  long a = expo(x), b, l,  L, i, n, m, e, B;
  GEN y, p2, x2;
  double d;

  n = 0;
  if (a >= 0)
  {
    GEN q;
    if (a > 30)
    {
      GEN z, pitemp = mppi(nbits2prec(a + 32));
      setexpo(pitemp,-1);
      z = addrr(x,pitemp); /* = x + Pi/4 */
      if (expo(z) >= bit_accuracy(lg(z)) + 3) pari_err(precer,"mpsc1");
      setexpo(pitemp, 0);
      q = floorr( divrr(z,pitemp) ); /* round ( x / (Pi/2) ) */
    } else {
      q = stoi((long)floor(rtodbl(x) / (PI/2) + 0.5));
    }
    if (signe(q))
    {
      x = subrr(x, mulir(q, Pi2n(-1, lg(x)+1))); /* x mod Pi/2  */
      a = expo(x);
      if (!signe(x) && a >= 0) pari_err(precer,"mpsc1");
      n = mod4(q); if (n && signe(q) < 0) n = 4 - n;
    }
  }
  /* a < 0 */
  l = lg(x);
  b = signe(x); *ptmod8 = (b < 0)? 4 + n: n;
  if (!b) return real_0_bit((expo(x)<<1) - 1);

  b = bit_accuracy(l);
  if (b + (a<<1) <= 0) {
    y = sqrr(x); y[1] = evalsigne(-1)|evalexpo(expo(y)-1);
    return y;
  }

  y = cgetr(l);
  B = b/6 + BITS_IN_LONG + (BITS_IN_LONG*BITS_IN_LONG/2)/ b;
  d = a/2.; m = (long)(d + sqrt(d*d + B)); /* >= 0 ,*/
  if (m < (-a) * 0.1) m = 0; /* not worth it */
  L = l + nbits2nlong(m);

  b += m;
  e = m - a; /* >= 1 */
  /* ~ 2( -1/log(2) - log_2 Y ) */
  d = 2.0 * (e+BITS_IN_LONG-1-1/LOG2 - log2((double)(ulong)x[2]));
  n = (long)(b / d);
  if (n > 1)
    n = (long)(b / (d + log2((double)n+1))); /* log~constant in small ranges */
  while (n*(d+log2((double)n+1)) < b) n++; /* expect few corrections */

 /* Multiplication is quadratic in this range (l is small, otherwise we
  * use logAGM + Newton). Set Y = 2^(-e-a) x, compute truncated series
  * sum Y^2k/(2k)!: this costs roughly
  *   m b^2 + sum_{k <= n} (2k e + BITS_IN_LONG)^2
  *   floor(b/2e) b^2 / 3  + m b^2
  * bit operations with |x| <  2^(1+a), |Y| < 2^(1-e) , m = e+a and b bits of
  * accuracy needed, so
  *    B := ( b / 6 + BITS_IN_LONG + BITS_IN_LONG^2 / 2b) ~ m(m-a)
  *
  * we want b ~ 6 m (m-a) or m~b+a hence
  *     m = min( a/2 + sqrt(a^2/4 + b/6),  b/2 + a )
  * NB1: e ~ (b/6)^(1/2) or b/2.
  * NB2: We use b/4 instead of b/6 in the formula above: hand-optimized...
  *
  * Truncate the sum at k = n (>= 1), the remainder is
  * < sum_{k >= n+1} Y^2k / 2k! < Y^(2n+2) / (2n+2)!(1-Y^2) < Y^(2n+2)/(2n+1)!
  * We want ... <= Y^2 2^-b, hence -2n log_2 |Y| + log_2 (2n+1)! >= b
  *   log n! ~ (n + 1/2) log(n+1) - (n+1) + log(2Pi)/2,
  * error bounded by 1/6(n+1) <= 1/12. Finally, we want
  * 2n (-1/log(2) - log_2 |Y| + log_2(2n+2)) >= b  */
  x = rtor(x, L); x[1] = evalsigne(1) | evalexpo(-e);
  x2 = sqrr(x);
  if (n == 1) p2 = x2;
  else
  {
    GEN unr = real_1(L);
    pari_sp av;
    long s = 0, l1 = nbits2prec((long)(d + n + 16));

    p2 = cgetr(L); av = avma;
    for (i=n; i>=2; i--)
    {
      GEN p1;
      setlg(x2,l1); p1 = divrunu(x2, 2*i-1);
      l1 += dvmdsBIL(s - expo(p1), &s); if (l1>L) l1=L;
      if (i != n) p1 = mulrr(p1,p2);
      setlg(unr,l1); p1 = addrr_sign(unr,1, p1,-signe(p1));
      setlg(p2,l1); affrr(p1,p2); avma = av;
    }
    p2[1] = evalsigne(-signe(p2)) | evalexpo(expo(p2)-1); /* p2 := -p2/2 */
    setlg(x2,L); p2 = mulrr(x2,p2);
  }
  /* Now p2 = sum {1<= i <=n} (-1)^i x^(2i) / (2i)! ~ cos(x) - 1 */
  for (i=1; i<=m; i++)
  { /* p2 = cos(x)-1 --> cos(2x)-1 */
    p2 = mulrr(p2, addsr(2,p2));
    setexpo(p2, expo(p2)+1);
    if ((i & 31) == 0) p2 = gerepileuptoleaf((pari_sp)y, p2);
  }
  affrr_fixlg(p2,y); return y;
}

/* sqrt (|1 - (1+x)^2|) = sqrt(|x*(x+2)|). Sends cos(x)-1 to |sin(x)| */
static GEN
mpaut(GEN x)
{
  pari_sp av = avma;
  GEN t = mulrr(x, addsr(2,x)); /* != 0 */
  if (!signe(t)) return real_0_bit(expo(t) >> 1);
  return gerepileuptoleaf(av, sqrtr_abs(t));
}

/********************************************************************/
/**                            COSINE                              **/
/********************************************************************/

GEN
mpcos(GEN x)
{
  long mod8;
  pari_sp av;
  GEN y,p1;

  if (!signe(x)) {
    long l = nbits2prec(-expo(x));
    if (l < 3) l = 3;
    return real_1(l);
  }

  av = avma; p1 = mpsc1(x,&mod8);
  switch(mod8)
  {
    case 0: case 4: y = addsr(1,p1); break;
    case 1: case 7: y = mpaut(p1); togglesign(y); break;
    case 2: case 6: y = subsr(-1,p1); break;
    default:        y = mpaut(p1); break; /* case 3: case 5: */
  }
  return gerepileuptoleaf(av, y);
}

/* convert INT or FRAC to REAL, which is later reduced mod 2Pi : avoid
 * cancellation */
static GEN
tofp_safe(GEN x, long prec)
{
  return (typ(x) == t_INT || gexpo(x) > 0)? gadd(x, real_0(prec))
                                          : fractor(x, prec);
}

GEN
gcos(GEN x, long prec)
{
  pari_sp av;
  GEN r, u, v, y, u1, v1;
  long i;

  switch(typ(x))
  {
    case t_REAL:
      return mpcos(x);

    case t_COMPLEX:
      if (isintzero(gel(x,1))) return gch(gel(x,2), prec);
      i = precision(x); if (!i) i = prec;
      y = cgetc(i); av = avma;
      r = gexp(gel(x,2),prec);
      v1 = gmul2n(addrr(invr(r),r), -1); /* = cos(I*Im(x)) */
      u1 = subrr(v1, r); /* = - I*sin(I*Im(x)) */
      gsincos(gel(x,1),&u,&v,prec);
      affrr_fixlg(gmul(v1,v), gel(y,1));
      affrr_fixlg(gmul(u1,u), gel(y,2)); avma = av; return y;

    case t_INT: case t_FRAC:
      y = cgetr(prec); av = avma;
      affrr_fixlg(mpcos(tofp_safe(x,prec)), y); avma = av; return y;

    case t_INTMOD: pari_err(typeer,"gcos");

    case t_PADIC: x = cos_p(x);
      if (!x) pari_err(talker,"p-adic argument out of range in gcos");
      return x;

    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y)) return gerepileupto(av, gaddsg(1,y));
      if (valp(y) < 0) pari_err(negexper,"gcos");
      gsincos(y,&u,&v,prec);
      return gerepilecopy(av,v);
  }
  return transc(gcos,x,prec);
}
/********************************************************************/
/**                             SINE                               **/
/********************************************************************/

GEN
mpsin(GEN x)
{
  long mod8;
  pari_sp av;
  GEN y,p1;

  if (!signe(x)) return real_0_bit(expo(x));

  av = avma; p1 = mpsc1(x,&mod8);
  switch(mod8)
  {
    case 0: case 6: y=mpaut(p1); break;
    case 1: case 5: y=addsr(1,p1); break;
    case 2: case 4: y=mpaut(p1); togglesign(y); break;
    default:        y=subsr(-1,p1); break; /* case 3: case 7: */
  }
  return gerepileuptoleaf(av, y);
}

GEN
gsin(GEN x, long prec)
{
  pari_sp av;
  GEN r, u, v, y, v1, u1;
  long i;

  switch(typ(x))
  {
    case t_REAL:
      return mpsin(x);

    case t_COMPLEX:
      if (isintzero(gel(x,1))) {
        GEN z = cgetg(3, t_COMPLEX);
        gel(z,1) = gen_0;
        gel(z,2) = gsh(gel(x,2),prec); return z;
      }
      i = precision(x); if (!i) i = prec;
      y = cgetc(i); av = avma;
      r = gexp(gel(x,2),prec);
      v1 = gmul2n(addrr(invr(r),r), -1); /* = cos(I*Im(x)) */
      u1 = subrr(r, v1); /* = I*sin(I*Im(x)) */
      gsincos(gel(x,1),&u,&v,prec);
      affrr_fixlg(gmul(v1,u), gel(y,1));
      affrr_fixlg(gmul(u1,v), gel(y,2)); avma = av; return y;

    case t_INT: case t_FRAC:
      y = cgetr(prec); av = avma;
      affrr_fixlg(mpsin(tofp_safe(x,prec)), y); avma = av; return y;

    case t_INTMOD: pari_err(typeer,"gsin");

    case t_PADIC: x = sin_p(x);
      if (!x) pari_err(talker,"p-adic argument out of range in gsin");
      return x;

    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y)) return gerepilecopy(av, y);
      if (valp(y) < 0) pari_err(negexper,"gsin");
      gsincos(y,&u,&v,prec);
      return gerepilecopy(av,u);
  }
  return transc(gsin,x,prec);
}
/********************************************************************/
/**                       SINE, COSINE together                    **/
/********************************************************************/

void
mpsincos(GEN x, GEN *s, GEN *c)
{
  long mod8;
  pari_sp av, tetpil;
  GEN p1, *gptr[2];

  if (!signe(x))
  {
    long e = expo(x);
    *s = real_0_bit(e);
    *c = e >= 0? real_0_bit(e): real_1(nbits2prec(-e));
    return;
  }

  av=avma; p1=mpsc1(x,&mod8); tetpil=avma;
  switch(mod8)
  {
    case 0: *c=addsr( 1,p1); *s=mpaut(p1); break;
    case 1: *s=addsr( 1,p1); *c=mpaut(p1); togglesign(*c); break;
    case 2: *c=subsr(-1,p1); *s=mpaut(p1); togglesign(*s); break;
    case 3: *s=subsr(-1,p1); *c=mpaut(p1); break;
    case 4: *c=addsr( 1,p1); *s=mpaut(p1); togglesign(*s); break;
    case 5: *s=addsr( 1,p1); *c=mpaut(p1); break;
    case 6: *c=subsr(-1,p1); *s=mpaut(p1); break;
    case 7: *s=subsr(-1,p1); *c=mpaut(p1); togglesign(*c); break;
  }
  gptr[0]=s; gptr[1]=c;
  gerepilemanysp(av,tetpil,gptr,2);
}

/* return exp(ix), x a t_REAL */
GEN
exp_Ir(GEN x)
{
  pari_sp av = avma;
  GEN v = cgetg(3,t_COMPLEX);
  mpsincos(x, (GEN*)(v+2), (GEN*)(v+1));
  if (!signe(gel(v,2))) return gerepilecopy(av, gel(v,1));
  return v;
}

void
gsincos(GEN x, GEN *s, GEN *c, long prec)
{
  long ii, i, j, ex, ex2, lx, ly, mi;
  pari_sp av, tetpil;
  GEN y, r, u, v, u1, v1, p1, p2, p3, p4, ps, pc;
  GEN *gptr[4];

  switch(typ(x))
  {
    case t_INT: case t_FRAC:
      *s = cgetr(prec);
      *c = cgetr(prec); av = avma;
      mpsincos(tofp_safe(x, prec), &ps, &pc);
      affrr_fixlg(ps,*s);
      affrr_fixlg(pc,*c); avma = av; return;

    case t_REAL:
      mpsincos(x,s,c); return;

    case t_COMPLEX:
      i = precision(x); if (!i) i = prec;
      ps = cgetc(i); *s = ps;
      pc = cgetc(i); *c = pc; av = avma;
      r = gexp(gel(x,2),prec);
      v1 = gmul2n(addrr(invr(r),r), -1); /* = cos(I*Im(x)) */
      u1 = subrr(r, v1); /* = I*sin(I*Im(x)) */
      gsincos(gel(x,1), &u,&v, prec);
      affrr_fixlg(mulrr(v1,u), gel(ps,1));
      affrr_fixlg(mulrr(u1,v), gel(ps,2));
      affrr_fixlg(mulrr(v1,v), gel(pc,1));
      affrr_fixlg(mulrr(u1,u), gel(pc,2)); togglesign(gel(pc,2));
      avma = av; return;

    case t_QUAD:
      av = avma; gsincos(quadtofp(x, prec), s, c, prec);
      gerepileall(av, 2, s, c); return;

    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y)) { *s = gerepilecopy(av,y); *c = gaddsg(1,*s); return; }

      ex = valp(y); lx = lg(y); ex2 = 2*ex+2;
      if (ex < 0) pari_err(talker,"non zero exponent in gsincos");
      if (ex2 > lx)
      {
        *s = x == y? gcopy(y): gerepilecopy(av, y); av = avma;
        *c = gerepileupto(av, gsubsg(1, gdivgs(gsqr(y),2)));
        return;
      }
      if (!ex)
      {
        p1 = leafcopy(y); gel(p1,2) = gen_0;
        gsincos(normalize(p1),&u,&v,prec);
        gsincos(gel(y,2),&u1,&v1,prec);
        p1 = gmul(v1,v);
        p2 = gmul(u1,u);
        p3 = gmul(v1,u);
        p4 = gmul(u1,v); tetpil = avma;
        *c = gsub(p1,p2);
        *s = gadd(p3,p4);
        gptr[0]=s; gptr[1]=c;
        gerepilemanysp(av,tetpil,gptr,2);
        return;
      }

      ly = lx+2*ex;
      mi = lx-1; while (mi>=3 && isrationalzero(gel(y,mi))) mi--;
      mi += ex-2;
      pc = cgetg(ly,t_SER); *c = pc;
      ps = cgetg(lx,t_SER); *s = ps;
      pc[1] = evalsigne(1) | _evalvalp(0) | evalvarn(varn(y));
      gel(pc,2) = gen_1; ps[1] = y[1];
      for (i=2; i<ex+2; i++) gel(ps,i) = gcopy(gel(y,i));
      for (i=3; i< ex2; i++) gel(pc,i) = gen_0;
      for (i=ex2; i<ly; i++)
      {
        ii = i-ex; av = avma; p1 = gen_0;
        for (j=ex; j<=minss(ii-2,mi); j++)
          p1 = gadd(p1, gmulgs(gmul(gel(y,j-ex+2),gel(ps,ii-j)),j));
        gel(pc,i) = gerepileupto(av, gdivgs(p1,2-i));
        if (ii < lx)
        {
          av = avma; p1 = gen_0;
          for (j=ex; j<=minss(i-ex2,mi); j++)
            p1 = gadd(p1,gmulgs(gmul(gel(y,j-ex+2),gel(pc,i-j)),j));
          p1 = gdivgs(p1,i-2);
          gel(ps,i-ex) = gerepileupto(av, gadd(p1,gel(y,i-ex)));
        }
      }
      return;
  }
  pari_err(typeer,"gsincos");
}

/********************************************************************/
/**                                                                **/
/**                     TANGENT and COTANGENT                      **/
/**                                                                **/
/********************************************************************/
static GEN
mptan(GEN x)
{
  pari_sp av = avma;
  GEN s, c;

  mpsincos(x,&s,&c);
  if (!signe(c)) pari_err(talker, "can't compute tan(Pi/2 + kPi)");
  return gerepileuptoleaf(av, divrr(s,c));
}

GEN
gtan(GEN x, long prec)
{
  pari_sp av;
  GEN y, s, c;

  switch(typ(x))
  {
    case t_REAL: return mptan(x);

    case t_COMPLEX: {
      if (isintzero(gel(x,1))) {
        GEN z = cgetg(3, t_COMPLEX);
        gel(z,1) = gen_0;
        gel(z,2) = gth(gel(x,2),prec); return z;
      }
      av = avma; y = mulcxmI(gth(mulcxI(x), prec)); /* tan x = -I th(I x) */
      gel(y,1) = gcopy(gel(y,1));
      return gerepileupto(av, y);
    }
    case t_INT: case t_FRAC:
      y = cgetr(prec); av = avma;
      affrr_fixlg(mptan(tofp_safe(x,prec)), y); avma = av; return y;

    case t_PADIC:
      av = avma;
      return gerepileupto(av, gdiv(gsin(x,prec), gcos(x,prec)));

    case t_INTMOD: pari_err(typeer,"gtan");

    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y)) return gerepilecopy(av, y);
      if (valp(y) < 0) pari_err(negexper,"gtan");
      gsincos(y,&s,&c,prec);
      return gerepileupto(av, gdiv(s,c));
  }
  return transc(gtan,x,prec);
}

static GEN
mpcotan(GEN x)
{
  pari_sp av=avma, tetpil;
  GEN s,c;

  mpsincos(x,&s,&c); tetpil=avma;
  return gerepile(av,tetpil,divrr(c,s));
}

GEN
gcotan(GEN x, long prec)
{
  pari_sp av;
  GEN y, s, c;

  switch(typ(x))
  {
    case t_REAL:
      return mpcotan(x);

    case t_COMPLEX:
      if (isintzero(gel(x,1))) {
        GEN z = cgetg(3, t_COMPLEX);
        gel(z,1) = gen_0;
        av = avma;
        gel(z,2) = gerepileupto(av, gneg(ginv(gth(gel(x,2),prec))));
        return z;
      }
      av = avma;
      gsincos(x,&s,&c,prec);
      return gerepileupto(av, gdiv(c,s));

    case t_INT: case t_FRAC:
      y = cgetr(prec); av = avma;
      affrr_fixlg(mpcotan(tofp_safe(x,prec)), y); avma = av; return y;

    case t_PADIC:
      av = avma;
      return gerepileupto(av, gdiv(gcos(x,prec), gsin(x,prec)));

    case t_INTMOD: pari_err(typeer,"gcotan");

    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y)) pari_err(talker,"0 argument in cotan");
      if (valp(y) < 0) pari_err(negexper,"cotan"); /* fall through */
      gsincos(y,&s,&c,prec);
      return gerepileupto(av, gdiv(c,s));
  }
  return transc(gcotan,x,prec);
}
