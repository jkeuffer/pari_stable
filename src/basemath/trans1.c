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
/**                   TRANSCENDENTAL FONCTIONS                     **/
/**                                                                **/
/********************************************************************/
#include "pari.h"

#ifdef LONG_IS_64BIT
# define C31 (9223372036854775808.0) /* VERYBIGINT * 1.0 */
# define SQRTVERYBIGINT 3037000500   /* ceil(sqrt(VERYBIGINT)) */
# define CBRTVERYBIGINT 2097152      /* ceil(cbrt(VERYBIGINT)) */
#else
# define C31 (2147483648.0)
# define SQRTVERYBIGINT 46341
# define CBRTVERYBIGINT  1291
#endif


/********************************************************************/
/**                                                                **/
/**                        FONCTION PI                             **/
/**                                                                **/
/********************************************************************/

void
constpi(long prec)
{
  GEN p1,p2,p3,tmppi;
  long l, n, n1;
  pari_sp av1, av2;
  double alpha;

#define k1  545140134
#define k2  13591409
#define k3  640320
#define alpha2 (1.4722004/(BYTES_IN_LONG/4))  /* 3*log(k3/12)/(32*log(2)) */

  if (gpi && lg(gpi) >= prec) return;

  av1 = avma; tmppi = newbloc(prec);
  *tmppi = evaltyp(t_REAL) | evallg(prec);

  prec++;

  n = (long)(1 + (prec-2)/alpha2);
  n1 = 6*n - 1;
  p2 = addsi(k2, mulss(n,k1));
  p1 = itor(p2, prec);

  /* initialisation longueur mantisse */
  if (prec>=4) l=4; else l=prec;
  setlg(p1,l); alpha=l;

  av2 = avma;
  while (n)
  {
    if (n < CBRTVERYBIGINT)
      p3 = divrs(mulsr(n1-4,mulsr(n1*(n1-2),p1)),n*n*n);
    else
    {
      if (n1 < SQRTVERYBIGINT)
	p3 = divrs(divrs(mulsr(n1-4,mulsr(n1*(n1-2),p1)),n*n),n);
      else
	p3 = divrs(divrs(divrs(mulsr(n1-4,mulsr(n1,mulsr(n1-2,p1))),n),n),n);
    }
    p3 = divrs(divrs(p3,100100025), 327843840);
    subisz(p2,k1,p2); subirz(p2,p3,p1);
    alpha += alpha2; l = (long)(1+alpha); /* nouvelle longueur mantisse */
    if (l>prec) l=prec;
    setlg(p1,l); avma = av2;
    n--; n1-=6;
  }
  p1 = divsr(53360,p1);
  mulrrz(p1,gsqrt(stoi(k3),prec), tmppi);
  gunclone(gpi); avma = av1;  gpi = tmppi;
}

GEN
mppi(long prec)
{
  GEN x = cgetr(prec);
  constpi(prec); affrr(gpi,x); return x;
}

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
  z[1] = zero;
  z[2] = (long)Pi2n(n, prec); return z;
}

/* 2I * Pi */
GEN
PiI2(long prec) { return PiI2n(1, prec); }

/********************************************************************/
/**                                                                **/
/**                      FONCTION EULER                            **/
/**                                                                **/
/********************************************************************/

void
consteuler(long prec)
{
  GEN u,v,a,b,tmpeuler;
  long l, n, k, x;
  pari_sp av1, av2;

  if (geuler && lg(geuler) >= prec) return;

  av1 = avma; tmpeuler = newbloc(prec);
  *tmpeuler = evaltyp(t_REAL) | evallg(prec);

  prec++;

  l = prec+1; x = (long) (1 + (bit_accuracy(l) >> 2) * LOG2);
  a = stor(x,l); u=mplog(a); setsigne(u,-1); affrr(u,a);
  b = realun(l);
  v = realun(l);
  n=(long)(1+3.591*x); /* z=3.591: z*[ ln(z)-1 ]=1 */
  av2 = avma;
  if (x < SQRTVERYBIGINT)
  {
    long xx = x*x;
    for (k=1; k<=n; k++)
    {
      divrsz(mulsr(xx,b),k*k, b);
      divrsz(addrr(divrs(mulsr(xx,a),k),b),k, a);
      addrrz(u,a,u); addrrz(v,b,v); avma = av2;
    }
  }
  else
  {
    GEN xx = mulss(x,x);
    for (k=1; k<=n; k++)
    {
      divrsz(mulir(xx,b),k*k, b);
      divrsz(addrr(divrs(mulir(xx,a),k),b),k, a);
      addrrz(u,a,u); addrrz(v,b,v); avma = av2;
    }
  }
  divrrz(u,v,tmpeuler);
  gunclone(geuler); avma = av1; geuler = tmpeuler;
}

GEN
mpeuler(long prec)
{
  GEN x = cgetr(prec);
  consteuler(prec); affrr(geuler,x); return x;
}

/********************************************************************/
/**                                                                **/
/**       CONVERSION DE TYPES POUR FONCTIONS TRANSCENDANTES        **/
/**                                                                **/
/********************************************************************/

GEN
transc(GEN (*f)(GEN,long), GEN x, long prec)
{
  pari_sp tetpil, av = avma;
  GEN p1, y;
  long lx, i;

  switch(typ(x))
  {
    case t_INT: case t_FRAC: case t_FRACN:
      p1=cgetr(prec); gaffect(x,p1); tetpil=avma;
      return gerepile(av,tetpil,f(p1,prec));

    case t_COMPLEX: case t_QUAD:
      p1=gmul(x,realun(prec)); tetpil=avma;
      return gerepile(av,tetpil,f(p1,prec));

    case t_POL: case t_RFRAC: case t_RFRACN:
      p1=tayl(x,gvar(x),precdl); tetpil=avma;
      return gerepile(av,tetpil,f(p1,prec));

    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); y = cgetg(lx,typ(x));
      for (i=1; i<lx; i++) y[i] = (long)f((GEN)x[i],prec);
      return y;

    case t_POLMOD:
      p1 = roots((GEN)x[1],prec); lx = lg(p1);
      for (i=1; i<lx; i++) p1[i] = lpoleval((GEN)x[2],(GEN)p1[i]);
      tetpil = avma; y = cgetg(lx,t_COL);
      for (i=1; i<lx; i++) y[i] = (long)f((GEN)p1[i],prec);
      return gerepile(av,tetpil,y);

    default: err(typeer,"a transcendental function");
  }
  return f(x,prec);
}

/*******************************************************************/
/*                                                                 */
/*                            POWERING                             */
/*                                                                 */
/*******************************************************************/
extern GEN real_unit_form(GEN x);
extern GEN imag_unit_form(GEN x);

static GEN
puiss0(GEN x)
{
  long lx,i;
  GEN y;

  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC: case t_FRACN: case t_PADIC:
      return gun;

    case t_INTMOD:
      y=cgetg(3,t_INTMOD); copyifstack(x[1],y[1]); y[2]=un; break;

    case t_COMPLEX:
      y=cgetg(3,t_COMPLEX); y[1]=un; y[2]=zero; break;

    case t_QUAD:
      y=cgetg(4,t_QUAD); copyifstack(x[1],y[1]);
      y[2]=un; y[3]=zero; break;

    case t_POLMOD:
      y=cgetg(3,t_POLMOD); copyifstack(x[1],y[1]);
      y[2]=lpolun[varn(x[1])]; break;

    case t_POL: case t_SER: case t_RFRAC: case t_RFRACN:
      return polun[gvar(x)];

    case t_MAT:
      lx=lg(x); if (lx==1) return cgetg(1,t_MAT);
      if (lx != (lg(x[1]))) err(mattype1,"gpowgs");
      y = idmat(lx-1);
      for (i=1; i<lx; i++) coeff(y,i,i) = lpuigs(gcoeff(x,i,i),0);
      break;
    case t_QFR: return real_unit_form(x);
    case t_QFI: return imag_unit_form(x);
    case t_VECSMALL:
      lx = lg(x);
      y = cgetg(lx, t_VECSMALL);
      for (i=1; i<lx; i++) y[i] = i;
      return y;
    default: err(typeer,"gpowgs");
      return NULL; /* not reached */
  }
  return y;
}

static GEN
_sqr(void *data /* ignored */, GEN x) {
  (void)data; return gsqr(x);
}
static GEN
_mul(void *data /* ignored */, GEN x, GEN y) {
  (void)data; return gmul(x,y);
}
static GEN
_sqri(void *data /* ignored */, GEN x) {
  (void)data; return sqri(x);
}
static GEN
_muli(void *data /* ignored */, GEN x, GEN y) {
  (void)data; return mulii(x,y);
}

/* INTEGER POWERING (a^|n| for integer a and integer |n| > 1)
 *
 * Nonpositive powers and exponent one should be handled by gpow() and
 * gpowgs() in trans1.c, which at the time of this writing is the only place
 * where the following is [slated to be] used.
 *
 * Use left shift binary algorithm (RS is wasteful: multiplies big numbers,
 * with LS one of them is the base, hence small). If result is nonzero, its
 * sign is set to s (= +-1) regardless of what it would have been. This makes
 * life easier for gpow()/gpowgs(), which otherwise might do a
 * setsigne(gun,-1)... -- GN1998May04
 */
static GEN
puissii(GEN a, GEN n, long s)
{
  pari_sp av;
  GEN y;

  if (!signe(a)) return gzero; /* a==0 */
  if (lgefint(a)==3)
  { /* easy if |a| < 3 */
    if (a[2] == 1) return (s>0)? gun: negi(gun);
    if (a[2] == 2) { a = shifti(gun, labs(itos(n))); setsigne(a,s); return a; }
  }
  if (lgefint(n)==3)
  { /* or if |n| < 3 */
    if (n[2] == 1) { a = icopy(a); setsigne(a,s); return a; }
    if (n[2] == 2) return sqri(a);
  }
  av = avma;
  y = leftright_pow(a, n, NULL, &_sqri, &_muli);
  setsigne(y,s); return gerepileuptoint(av,y);
}

typedef struct {
  long prec, a;
  GEN (*sqr)(GEN);
  GEN (*mulsg)(long,GEN);
} sr_muldata;

static GEN
_rpowsi_mul(void *data, GEN x, GEN y/*unused*/)
{
  sr_muldata *D = (sr_muldata *)data;
  return D->mulsg(D->a, x);
}

static GEN
_rpowsi_sqr(void *data, GEN x)
{
  sr_muldata *D = (sr_muldata *)data;
  if (typ(x) == t_INT && lgefint(x) >= D->prec)
  { /* switch to t_REAL */
    D->sqr   = &gsqr;
    D->mulsg = &mulsr;
    x = itor(x, D->prec);
  }
  return D->sqr(x);
}

/* return a^n as a t_REAL of precision prec. Adapted from puissii().
 * Assume a > 0, n > 0 */
GEN
rpowsi(ulong a, GEN n, long prec)
{
  pari_sp av;
  GEN y;
  sr_muldata D;

  if (a == 1) return realun(prec);
  if (a == 2) return real2n(itos(n), prec);
  if (is_pm1(n)) return stor(a, prec);
  av = avma;
  D.sqr   = &sqri; 
  D.mulsg = &mulsi;
  D.prec = prec;
  D.a = a;
  y = leftright_pow(stoi(a), n, (void*)&D, &_rpowsi_sqr, &_rpowsi_mul);
  if (typ(y) == t_INT) y = itor(y, prec);
  return gerepileuptoleaf(av, y);
}

GEN
gpowgs(GEN x, long n)
{
  long m, tx;
  pari_sp lim, av;
  static long gn[3] = {evaltyp(t_INT)|_evallg(3), 0, 0};
  GEN y;

  if (n == 0) return puiss0(x);
  if (n == 1) return gcopy(x);
  if (n ==-1) return ginv(x);
  if (n>0) { gn[1] = evalsigne( 1) | evallgefint(3); gn[2]= n; }
  else     { gn[1] = evalsigne(-1) | evallgefint(3); gn[2]=-n; }
 /* If gpowgs were only ever called from gpow, the switch wouldn't be needed.
  * In fact, under current word and bit field sizes, an integer power with
  * multiword exponent will always overflow.  But it seems easier to call
  * puissii|powmodulo() with a mock-up GEN as 2nd argument than to write
  * separate versions for a long exponent.  Note that n = HIGHBIT is an
  * invalid argument. --GN
  */
  switch((tx=typ(x)))
  {
    case t_INT:
    {
      long sx=signe(x), sr = (sx<0 && (n&1))? -1: 1;
      if (n>0) return puissii(x,(GEN)gn,sr);
      if (!sx) err(talker, "division by zero in gpowgs");
      if (is_pm1(x)) return (sr < 0)? icopy(x): gun;
      /* n<0, |x|>1 */
      y=cgetg(3,t_FRAC); setsigne(gn,1);
      y[1]=(sr>0)? un: lnegi(gun);
      y[2]=(long)puissii(x,(GEN)gn,1); /* force denominator > 0 */
      return y;
    }
    case t_INTMOD:
      y=cgetg(3,tx); copyifstack(x[1],y[1]);
      y[2]=(long)powmodulo((GEN)(x[2]),(GEN)gn,(GEN)(x[1]));
      return y;
    case t_FRAC: case t_FRACN:
    {
      GEN a = (GEN)x[1], b = (GEN)x[2];
      long sr = (n&1 && (signe(a)!=signe(b))) ? -1 : 1;
      if (n > 0) { if (!signe(a)) return gzero; }
      else
      { /* n < 0 */
        if (!signe(a)) err(talker, "division by zero fraction in gpowgs");
        /* +-1/x[2] inverts to an integer */
        if (is_pm1(a)) return puissii(b,(GEN)gn,sr);
        y = b; b = a; a = y;
      }
      /* HACK: puissii disregards the sign of gn */
      y = cgetg(3,tx);
      y[1] = (long)puissii(a,(GEN)gn,sr);
      y[2] = (long)puissii(b,(GEN)gn,1);
      return y;
    }
    case t_PADIC: case t_POL: case t_POLMOD:
      return powgi(x,gn);
    case t_RFRAC: case t_RFRACN:
    {
      av=avma; y=cgetg(3,tx); m = labs(n);
      y[1]=lpuigs((GEN)x[1],m);
      y[2]=lpuigs((GEN)x[2],m);
      if (n<0) y=ginv(y);	/* let ginv worry about normalizations */
      return gerepileupto(av,y);
    }
    default:
      m = labs(n);
      av=avma; y=NULL; lim=stack_lim(av,1);
      for (; m>1; m>>=1)
      {
        if (m&1) y = y? gmul(y,x): x;
        x=gsqr(x);
        if (low_stack(lim, stack_lim(av,1)))
        {
          GEN *gptr[2]; gptr[0]=&x; gptr[1]=&y;
          if(DEBUGMEM>1) err(warnmem,"[3]: gpowgs");
          gerepilemany(av,gptr,y? 2: 1);
        }
      }
      y = y? gmul(y,x): x;
      if (n<=0) y=ginv(y);
      return gerepileupto(av,y);
  }
}

GEN
pow_monome(GEN x, GEN nn)
{
  long n, m, i, j, dd;
  pari_sp tetpil, av = avma;
  GEN p1,y;
  if (is_bigint(nn)) err(talker,"power overflow in pow_monome");
  n = itos(nn); m = labs(n);
  j=lgef(x); dd=(j-3)*m+3;
  p1=cgetg(dd,t_POL); m = labs(n);
  p1[1] = evalsigne(1) | evallgef(dd) | evalvarn(varn(x));
  for (i=2; i<dd-1; i++) p1[i]=zero;
  p1[i]=lpuigs((GEN)x[j-1],m);
  if (n>0) return p1;

  tetpil=avma; y=cgetg(3,t_RFRAC);
  y[1]=(long)denom((GEN)p1[i]);
  y[2]=lmul(p1,(GEN)y[1]); return gerepile(av,tetpil,y);
}

extern GEN powrealform(GEN x, GEN n);

/* n is assumed to be an integer */
GEN
powgi(GEN x, GEN n)
{
  long tx, sn = signe(n);
  GEN y;

  if (typ(n) != t_INT) err(talker,"not an integral exponent in powgi");
  if (!sn) return puiss0(x);

  switch(tx=typ(x))
  {/* catch some types here, instead of trying gpowgs() first, because of
    * the simpler call interface to puissii() and powmodulo() -- even though
    * for integer/rational bases other than 0,+-1 and non-wordsized
    * exponents the result will be certain to overflow. --GN
    */
    case t_INT:
    {
      long sx=signe(x), sr = (sx<0 && mod2(n))? -1: 1;
      if (sn>0) return puissii(x,n,sr);
      if (!sx) err(talker, "division by zero in powgi");
      if (is_pm1(x)) return (sr < 0)? icopy(x): gun;
      /* n<0, |x|>1 */
      y=cgetg(3,t_FRAC); setsigne(n,1); /* temporarily replace n by abs(n) */
      y[1]=(sr>0)? un: lnegi(gun);
      y[2]=(long)puissii(x,n,1);
      setsigne(n,-1); return y;
    }
    case t_INTMOD:
      y=cgetg(3,tx); copyifstack(x[1],y[1]);
      y[2]=(long)powmodulo((GEN)x[2],n,(GEN)x[1]);
      return y;
    case t_FRAC: case t_FRACN:
    {
      GEN a = (GEN)x[1], b = (GEN)x[2];
      long sr = (mod2(n) && (signe(a)!=signe(b))) ? -1 : 1;
      if (sn > 0) { if (!signe(a)) return gzero; }
      else
      { /* n < 0 */
        if (!signe(a)) err(talker, "division by zero fraction in powgi");
        /* +-1/b inverts to an integer */
        if (is_pm1(a)) return puissii(b,n,sr);
        y = b; b = a; a = y;
      }
      /* HACK: puissii disregards the sign of n */
      y = cgetg(3,tx);
      y[1] = (long)puissii(a,n,sr);
      y[2] = (long)puissii(b,n,1);
      return y;
    }
    case t_PADIC:
    {
      long e = itos(n)*valp(x), v;
      GEN mod, p = (GEN)x[2];
      
      if (!signe(x[4]))
      {
        if (sn < 0) err(talker, "division by 0 p-adic in powgi");
        return padiczero(p, e);
      }
      y = cgetg(5,t_PADIC);
      mod = (GEN)x[3]; v = ggval(n, p);
      if (v == 0) mod = icopy(mod);
      else
      {
        mod = mulii(mod, gpowgs(p,v));
        mod = gerepileuptoint((pari_sp)y, mod);
      }
      y[1] = evalprecp(precp(x)+v) | evalvalp(e);
      icopyifstack(p, y[2]);
      y[3] = (long)mod;
      y[4] = (long)powmodulo((GEN)x[4], n, mod);
      return y;
    }
    case t_QFR:
      if (signe(x[4])) return powrealform(x,n);
    case t_POL:
      if (ismonome(x)) return pow_monome(x,n);
    default:
    {
      pari_sp av = avma;
      y = leftright_pow(x, n, NULL, &_sqr, &_mul);
      if (sn < 0) y = ginv(y);
      return av==avma? gcopy(y): gerepileupto(av,y);
    }
  }
}

/* we suppose n != 0, and valp(x) = 0 */
static GEN
ser_pui(GEN x, GEN n, long prec)
{
  pari_sp av, tetpil;
  GEN y, p1, p2, lead;

  if (gvar9(n) <= varn(x)) return gexp(gmul(n, glog(x,prec)), prec);
  lead = (GEN)x[2];
  if (gcmp1(lead))
  {
    GEN X, Y, alp;
    long lx, mi, i, j, d;

    av = avma; alp = gclone(gadd(n,gun)); avma = av;
    lx = lg(x);
    y = cgetg(lx,t_SER);
    y[1] = evalsigne(1) | evalvalp(0) | evalvarn(varn(x));
    X = x+2;
    Y = y+2;

    d = mi = lx-3; while (mi>=1 && gcmp0((GEN)X[mi])) mi--;
    Y[0] = un;
    for (i=1; i<=d; i++)
    {
      av = avma; p1 = gzero;
      for (j=1; j<=min(i,mi); j++)
      {
        p2 = gsubgs(gmulgs(alp,j),i);
        p1 = gadd(p1, gmul(gmul(p2,(GEN)X[j]),(GEN)Y[i-j]));
      }
      tetpil = avma; Y[i] = lpile(av,tetpil, gdivgs(p1,i));
    }
    gunclone(alp); return y;
  }
  p1 = gdiv(x,lead); p1[2] = un; /* in case it's inexact */
  p1 = gpow(p1,  n, prec);
  p2 = gpow(lead,n, prec); return gmul(p1, p2);
}

GEN
gpow(GEN x, GEN n, long prec)
{
  long i, lx, tx;
  pari_sp av;
  GEN y;

  if (typ(n) == t_INT) return powgi(x,n);
  tx = typ(x);
  if (is_matvec_t(tx))
  {
    lx = lg(x); y = cgetg(lx,tx);
    for (i=1; i<lx; i++) y[i] = lpui((GEN)x[i],n,prec);
    return y;
  }
  av = avma;
  if (tx == t_POL || tx == t_RFRAC || tx == t_RFRACN)
  {
    x = _toser(x); tx = t_SER;
  }
  if (tx == t_SER)
  {
    if (valp(x))
      err(talker,"need integer exponent for non-invertible series in gpow");
    if (lg(x) == 2) return gcopy(x); /* O(1) */
    return gerepileupto(av, ser_pui(x, n, prec));
  }
  if (gcmp0(x))
  {
    long tn = typ(n);
    if (!is_scalar_t(tn) || tn == t_PADIC || tn == t_INTMOD)
      err(talker,"zero to a forbidden power in gpow");
    n = greal(n);
    if (gsigne(n) <= 0)
      err(talker,"zero to a non positive exponent in gpow");
    if (!precision(x)) return gcopy(x);

    x = ground(gmulsg(gexpo(x),n));
    if (is_bigint(x) || (ulong)x[2] >= (ulong)HIGHEXPOBIT)
      err(talker,"underflow or overflow in gpow");
    avma = av; return realzero_bit(itos(x));
  }
  if (tx==t_INTMOD && typ(n)==t_FRAC)
  {
    GEN p1;
    if (!BSW_psp((GEN)x[1])) err(talker,"modulus must be prime in gpow");
    y = cgetg(3,tx); copyifstack(x[1],y[1]);
    av = avma;
    p1 = mpsqrtnmod((GEN)x[2],(GEN)n[2],(GEN)x[1],NULL);
    if (!p1) err(talker,"n-root does not exists in gpow");
    y[2] = lpileuptoint(av, powmodulo(p1, (GEN)n[1], (GEN)x[1]));
    return y;
  }
  i = (long) precision(n); if (i) prec=i;
  y = gmul(n,glog(x,prec));
  return gerepileupto(av, gexp(y,prec));
}

/********************************************************************/
/**                                                                **/
/**                        RACINE CARREE                           **/
/**                                                                **/
/********************************************************************/

GEN
mpsqrt(GEN x)
{
  pari_sp av, av0;
  long l,l0,l1,l2,s,eps,n,i,ex;
  double beta;
  GEN y,p1,p2,p3;

  if (typ(x) != t_REAL) err(typeer,"mpsqrt");
  s = signe(x); if (s < 0) err(talker,"negative argument in mpsqrt");
  if (!s) return realzero_bit(expo(x) >> 1);
 
  l = lg(x); y = cgetr(l); av0 = avma;

  p1 = cgetr(l+1); affrr(x,p1);
  ex = expo(x); eps = ex & 1; ex >>= 1;
  setexpo(p1,eps); /* x = 2^(2 ex) p1 */

  n = (long)(2 + log((double) (l-2))/LOG2);
  beta = sqrt((eps+1) * (2 + p1[2]/C31));
  p2 = cgetr(l+1);
  p2[1] = evalexpo(0) | evalsigne(1);
  p2[2] = (long)((beta-2)*C31);
  if (!p2[2]) { p2[2] = (long)HIGHBIT; setexpo(p2,1); }
  for (i=3; i<=l; i++) p2[i] = 0;

  p3 = cgetr(l+1); l -= 2; l1 = 1; l2 = 3;
  av = avma;
  for (i=1; i<=n; i++)
  { /* execute p2 := (p2 + p1/p2)/2 */
    l0 = l1<<1;
    if (l0 <= l)
      { l2 += l1; l1=l0; }
    else
      { l2 += l+1-l1; l1=l+1; }
    setlg(p1, l1+2);
    setlg(p3, l1+2);
    setlg(p2, l2);
    affrr(divrr(p1,p2), p3);
    affrr(addrr(p2,p3), p2); setexpo(p2, expo(p2)-1);
    avma = av;
  }
  affrr(p2,y); setexpo(y, expo(y)+ex);
  avma = av0; return y;
}

/* O(p^e) */
GEN
padiczero(GEN p, long e)
{
  GEN y = cgetg(5,t_PADIC);
  y[4] = zero;
  y[3] = un;
  copyifstack(p,y[2]);
  y[1] = evalvalp(e) | evalprecp(0);
  return y;
}

/* assume x unit, precp(x) = pp > 3 */
static GEN
sqrt_2adic(GEN x, long pp)
{
  GEN z = mod16(x)==1? gun: stoi(3);
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
    mod = shifti(gun, zp);
    z = addii(z, resmod2n(mulii(x, mpinvmod(z,mod)), zp));
    z = shifti(z, -1); /* (z + x/z) / 2 */
    if (pp == zp) return z;

    if (zp < pp) zp--;

    if (low_stack(lim,stack_lim(av,2)))
    {
      if (DEBUGMEM > 1) err(warnmem,"padic_sqrt");
      z = gerepileuptoint(av,z);
    }
  }
}

/* x unit defined modulo modx = p^pp, p != 2, pp > 0 */
static GEN
sqrt_padic(GEN x, GEN modx, long pp, GEN p)
{
  GEN mod, z = mpsqrtmod(x, p);
  long zp = 1;
  pari_sp av, lim;

  if (!z) err(sqrter5);
  if (pp <= zp) return z; 

  av = avma; lim = stack_lim(av,2);
  mod = p;
  for(;;)
  { /* could use the hensel_lift_accel idea. Not really worth it */
    GEN inv2;
    zp <<= 1;
    if (zp < pp) mod = sqri(mod); else { zp = pp; mod = modx; }
    inv2 = shifti(mod, -1); /* = (mod + 1)/2 = 1/2 */
    z = addii(z, resii(mulii(x, mpinvmod(z,mod)), mod));
    z = mulii(z, inv2);
    z = modii(z, mod); /* (z + x/z) / 2 */
    if (pp <= zp) return z;

    if (low_stack(lim,stack_lim(av,2)))
    {
      GEN *gptr[2]; gptr[0]=&z; gptr[1]=&mod;
      if (DEBUGMEM>1) err(warnmem,"padic_sqrt");
      gerepilemany(av,gptr,2);
    }
  }
}

static GEN
padic_sqrt(GEN x)
{
  long pp, e = valp(x);
  GEN z,y,mod, p = (GEN)x[2];
  pari_sp av;

  if (gcmp0(x)) return padiczero(p, (e+1) >> 1);
  if (e & 1) err(sqrter6);

  y = cgetg(5,t_PADIC);
  pp = precp(x);
  mod = (GEN)x[3];
  x   = (GEN)x[4]; /* lift to int */
  e >>= 1; av = avma;
  if (egalii(gdeux, p))
  {
    long r = mod8(x);
    if (pp <= 3)
    {
      switch(pp) {
        case 1: break;
        case 2: if ((r&3) == 1) break;
        case 3: if (r == 1) break;
        default: err(sqrter5);
      }
      z = gun;
      pp = 1;
    }
    else
    {
      if (r != 1) err(sqrter5);
      z = sqrt_2adic(x, pp);
      z = gerepileuptoint(av, z);
      pp--;
    }
    mod = shifti(gun, pp);
  }
  else /* p != 2 */
  {
    z = sqrt_padic(x, mod, pp, p);
    z = gerepileuptoint(av, z);
    mod = icopy(mod);
  }
  y[1] = evalprecp(pp) | evalvalp(e);
  copyifstack(p,y[2]);
  y[3] = (long)mod;
  y[4] = (long)z; return y;
}

/* return x^(1/n), assume typ(x) = t_SER */
static GEN
ser_sqrtn(GEN x, long n, long prec)
{
  long e = valp(x);
  GEN y;
  if (gcmp0(x)) return zeroser(varn(x), (e+n-1)/n);
  if (e % n) err(talker,"incorrect valuation in gsqrtn");
  y = dummycopy(x); setvalp(y, 0);
  y = ser_pui(y, ginv(stoi(n)), prec);
  if (typ(y) == t_SER) /* generic case */
    y[1] = evalsigne(1) | evalvalp(e/n) | evalvarn(varn(x));
  else /* e.g coeffs are POLMODs */
    y = gmul(y, gpowgs(polx[varn(x)], e/n));
  return y;
}

GEN
gsqrt(GEN x, long prec)
{
  pari_sp av, tetpil;
  GEN y,p1,p2;

  switch(typ(x))
  {
    case t_REAL:
      if (signe(x)>=0) return mpsqrt(x);
      y=cgetg(3,t_COMPLEX); y[1]=zero;
      setsigne(x,1); y[2]=lmpsqrt(x); setsigne(x,-1);
      return y;

    case t_INTMOD:
      y=cgetg(3,t_INTMOD); copyifstack(x[1],y[1]);
      p1 = mpsqrtmod((GEN)x[2],(GEN)y[1]);
      if (!p1) err(sqrter5);
      y[2] = (long)p1; return y;

    case t_COMPLEX:
      y=cgetg(3,t_COMPLEX); av=avma;
      if (gcmp0((GEN)x[2]))
      {
	long tx=typ(x[1]);

	if ((is_intreal_t(tx) || is_frac_t(tx)) && gsigne((GEN)x[1]) < 0)
	{
	  y[1]=zero; p1=gneg_i((GEN)x[1]); tetpil=avma;
	  y[2]=lpile(av,tetpil,gsqrt(p1,prec));
	  return y;
	}
	y[1]=lsqrt((GEN)x[1],prec);
	y[2]=zero; return y;
      }

      p1 = gsqr((GEN)x[1]);
      p2 = gsqr((GEN)x[2]);
      p1 = gsqrt(gadd(p1,p2),prec);
      if (gcmp0(p1))
      {
	y[1]=lsqrt(p1,prec);
	y[2]=lcopy((GEN)y[1]);
	return y;
      }

      if (gsigne((GEN)x[1]) < 0)
      {
	p1 = gmul2n(gsub(p1,(GEN)x[1]), -1);
	y[2] = lsqrt(p1,prec);
        y[1] = ldiv((GEN)x[2],gmul2n((GEN)y[2],1));
	tetpil=avma;
        y = (gsigne((GEN)x[2]) > 0)? gcopy(y): gneg(y);
	return gerepile(av,tetpil,y);
      }

      p1 = gmul2n(gadd(p1,(GEN)x[1]), -1); tetpil=avma;
      y[1] = lpile(av,tetpil,gsqrt(p1,prec));
      av=avma; p1=gmul2n((GEN)y[1],1); tetpil=avma;
      y[2] = lpile(av,tetpil,gdiv((GEN)x[2],p1));
      return y;

    case t_PADIC:
      return padic_sqrt(x);

    default:
      av = avma; if (!(y = _toser(x))) break;
      return gerepileupto(av, ser_sqrtn(y, 2, prec));
  }
  return transc(gsqrt,x,prec);
}

void
gsqrtz(GEN x, GEN y)
{
  long prec = precision(y);
  pari_sp av=avma;

  if (!prec) err(infprecer,"gsqrtz");
  gaffect(gsqrt(x,prec),y); avma=av;
}
/********************************************************************/
/**                                                                **/
/**                    FONCTION RACINE N-IEME                      **/
/**                                                                **/
/********************************************************************/
GEN
rootsof1complex(GEN n, long prec)
{
  pari_sp ltop = avma;
  GEN z;
  if (is_pm1(n)) return realun(prec);
  if (lgefint(n)==3 && n[2]==2) return stor(-1, prec);

  z = exp_Ir( divri(Pi2n(1, prec), n) ); /* exp(2Ipi/n) */
  return gerepileupto(ltop,z);  
}
/*Only the O() of y is used*/
GEN
rootsof1padic(GEN n, GEN y)
{
  pari_sp ltop=avma;
  GEN z,r;
  (void)mpsqrtnmod(gun,n,(GEN)y[2],&z);
  if (z==gzero){avma=ltop;return gzero;}/*should not happen*/
  r=cgetg(5,t_PADIC);
  r[1]=y[1];setvalp(r,0);/*rootsofunity are unramified*/
  r[2]=licopy((GEN)y[2]);
  r[3]=licopy((GEN)y[3]);
  r[4]=(long)padicsqrtnlift(gun,n,z,(GEN)y[2],precp(y));
  return gerepileupto(ltop,r);  
}
static GEN paexp(GEN x);
/*compute the p^e th root of x p-adic*/ 
GEN
padic_sqrtn_ram(GEN x, long e)
{
  pari_sp ltop=avma;
  GEN n,a;
  GEN p=(GEN)x[2];
  long v=0;
  n=gpowgs((GEN) x[2],e);
  if (valp(x))
  {
    GEN p1,z;
    p1=dvmdsi(valp(x),n,&z);
    if (signe(z))
      err(talker,"n-root does not exists in gsqrtn");
    v=itos(p1);
    x=gcopy(x);setvalp(x,0);
  }
  /*If p=2 -1 is an root of unity in U1,we need an extra check*/
  if (lgefint(p)==3 && p[2]==2 && mod8((GEN)x[4])!=signe((GEN)x[4]))
    err(talker,"n-root does not exists in gsqrtn");
  /*Other "n-root does not exists in gsqrtn" are caught by paexp...*/
  a=paexp(gdiv(palog(x),n));
  /*Here n=p^e and a^n=z*x where z is a root of unity. note that
      z^p=z, so z^n=z. and if b=a/z then b^n=x. We say b=x/(a^(n-1))*/
  a=gdiv(x,powgi(a,addis(n,-1)));
  if (v)  {  a=gcopy(a);setvalp(a,v);  }
  a=gerepileupto(ltop,a);
  return a;
}
/*compute the nth root of x p-adic p prime with n*/ 
GEN
padic_sqrtn_unram(GEN x, GEN n, GEN *zetan)
{
  pari_sp ltop=avma, tetpil;
  GEN a,r;
  GEN p=(GEN)x[2];
  long v=0;
  /*check valuation*/
  if (valp(x))
  {
    GEN p1,z;
    p1=dvmdsi(valp(x),n,&z);
    if (signe(z))
      err(talker,"n-root does not exists in gsqrtn");
    v=itos(p1);
  }
  a=mpsqrtnmod((GEN)x[4],n,p,zetan);
  if (!a)
    err(talker,"n-root does not exists in gsqrtn");
  tetpil=avma;
  r=cgetg(5,t_PADIC);
  r[1]=x[1];setvalp(r,v);
  r[2]=licopy(p);
  r[3]=licopy((GEN)x[3]);
  r[4]=(long)padicsqrtnlift((GEN)x[4],n,a,p,precp(x));
  if (zetan)
  {
    GEN z,*gptr[2];
    z=cgetg(5,t_PADIC);
    z[1]=x[1];setvalp(z,0);
    z[2]=licopy(p);
    z[3]=licopy((GEN)x[3]);
    z[4]=(long)padicsqrtnlift(gun,n,*zetan,p,precp(x));
    gptr[0]=&r;gptr[1]=&z;
    gerepilemanysp(ltop,tetpil,gptr,2);
    *zetan=z;
    return r;
  }
  else
    return gerepile(ltop,tetpil,r);
}

GEN
padic_sqrtn(GEN x, GEN n, GEN *zetan)
{
  pari_sp ltop=avma, tetpil;
  GEN p=(GEN)x[2];
  GEN q;
  long e;
  GEN *gptr[2];
  if (gcmp0(x))
  {
    long m = itos(n);
    return padiczero(p, (valp(x)+m-1)/m);
  }
  /*First treat the ramified part using logarithms*/
  e=pvaluation(n,p,&q);
  tetpil=avma;
  if (e)
  {
    x=padic_sqrtn_ram(x,e);
  }
  /*finished ?*/
  if (is_pm1(q))
  {
    if (signe(q)<0)
    {
      tetpil=avma;
      x=ginv(x);
    }
    if (zetan && e && lgefint(p)==3 && p[2]==2)/*-1 in Q_2*/
    {
      *zetan=negi(gun);
      gptr[0]=&x;gptr[1]=zetan;
      gerepilemanysp(ltop,tetpil,gptr,2);
      return x;
    }
    if (zetan) *zetan=gun;
    return gerepile(ltop,tetpil,x);
  }
  /*Now we use hensel lift for unramified case. 4x faster.*/
  tetpil=avma;
  x=padic_sqrtn_unram(x,q,zetan);
  if (zetan)
  {
    if (e && lgefint(p)==3 && p[2]==2)/*-1 in Q_2*/
    {
      tetpil=avma;
      x=gcopy(x);
      *zetan=gneg(*zetan);
    }
    gptr[0]=&x;gptr[1]=zetan;
    gerepilemanysp(ltop,tetpil,gptr,2);
    return x;
  }
  return gerepile(ltop,tetpil,x);
}

GEN
gsqrtn(GEN x, GEN n, GEN *zetan, long prec)
{
  long i, lx, tx;
  pari_sp av;
  GEN y, z;
  if (zetan) *zetan=gzero;
  if (typ(n)!=t_INT) err(talker,"second arg must be integer in gsqrtn");
  if (!signe(n)) err(talker,"1/0 exponent in gsqrtn");
  if (is_pm1(n))
  {
    if (zetan) *zetan=gun;
    if (signe(n)>0)
      return gcopy(x);
    return ginv(x);
  }
  tx = typ(x);
  if (is_matvec_t(tx))
  {
    lx=lg(x); y=cgetg(lx,tx);
    for (i=1; i<lx; i++) y[i]=(long)gsqrtn((GEN)x[i],n,NULL,prec);
    return y;
  }
  av = avma;
  switch(tx)
  {
  case t_INTMOD:
    z = gzero;
    /*This is not great, but else it will generate too much trouble*/
    if (!BSW_psp((GEN)x[1])) err(talker,"modulus must be prime in gsqrtn");
    if (zetan) 
    {
      z = cgetg(3,tx); copyifstack(x[1],z[1]);
      z[2] = lgeti(lgefint(z[1]));
    }
    y = cgetg(3,tx); copyifstack(x[1],y[1]);
    y[2] = (long)mpsqrtnmod((GEN)x[2],n,(GEN)x[1],zetan);
    if (!y[2]) err(talker,"n-root does not exists in gsqrtn");
    if (zetan)
    {
      affii(*zetan, (GEN)z[2]);
      cgiv(*zetan); *zetan = z;
    }
    return y;

  case t_PADIC: return padic_sqrtn(x,n,zetan);

  case t_INT: case t_FRAC: case t_FRACN: case t_REAL: case t_COMPLEX:
    i = (long) precision(n); if (i) prec=i;
    if (tx==t_INT && is_pm1(x) && signe(x)>0)
      y = gun;    /*speed-up since there is no way to call rootsof1complex
		    directly from gp*/
    else if (gcmp0(x))
    {
      if (gsigne(n) < 0) err(gdiver);
      if (isinexactreal(x))
        y = realzero_bit( itos( gfloor(gdivsg(gexpo(x), n)) ) );
      else
        y = realzero(prec);
    }
    else
    {
      y = gmul(ginv(n),glog(x,prec));
      y = gerepileupto(av, gexp(y,prec));
    }
    if (zetan) *zetan = rootsof1complex(n,prec);
    return y;

  default:
    av = avma; if (!(y = _toser(x))) break;
    return gerepileupto(av, ser_sqrtn(x, itos(n), prec));
  }
  err(typeer,"gsqrtn");
  return NULL;/* not reached */
}

/********************************************************************/
/**                                                                **/
/**                    FONCTION EXPONENTIELLE-1                    **/
/**                                                                **/
/********************************************************************/
#ifdef LONG_IS_64BIT
#  define EXMAX 46
#else
#  define EXMAX 22
#endif

GEN
mpexp1(GEN x)
{
  long l, l1, l2, i, n, m, ex, s, sx = signe(x);
  pari_sp av, av2;
  double a,b,alpha,beta, gama = 2.0 /* optimized for SUN3 */;
                                    /* KB: 3.0 is better for UltraSparc */
  GEN y,p1,p2,p3,p4,unr;

  if (typ(x)!=t_REAL) err(typeer,"mpexp1");
  if (!sx) return realzero_bit(expo(x));
  l=lg(x); y=cgetr(l); av=avma; /* room for result */

  l2 = l+1; ex = expo(x);
  if (ex > EXMAX) err(talker,"exponent too large in exp");
  alpha = -1-log(2+x[2]/C31)-ex*LOG2;
  beta = 5 + bit_accuracy(l)*LOG2;
  a = sqrt(beta/(gama*LOG2));
  b = (alpha + 0.5*log(beta*gama/LOG2))/LOG2;
  if (a>=b)
  {
    n=(long)(1+sqrt(beta*gama/LOG2));
    m=(long)(1+a-b);
    l2 += m>>TWOPOTBITS_IN_LONG;
  }
  else
  {
    n=(long)(1+beta/alpha);
    m=0;
  }
  unr=realun(l2);
  p2=rcopy(unr); setlg(p2,4);
  p4=cgetr(l2); affrr(x,p4); setsigne(p4,1);
  if (m) setexpo(p4,ex-m);

  s=0; l1=4; av2 = avma;
  for (i=n; i>=2; i--)
  {
    setlg(p4,l1); p3 = divrs(p4,i);
    s -= expo(p3); p1 = mulrr(p3,p2); setlg(p1,l1);
    l1 += s>>TWOPOTBITS_IN_LONG; if (l1>l2) l1=l2;
    s %= BITS_IN_LONG;
    setlg(unr,l1); p1 = addrr(unr,p1);
    setlg(p2,l1); affrr(p1,p2); avma = av2;
  }
  setlg(p2,l2); setlg(p4,l2); p2 = mulrr(p4,p2);

  for (i=1; i<=m; i++)
  {
    setlg(p2,l2);
    p2 = mulrr(addsr(2,p2),p2);
  }
  if (sx == -1)
  {
    setlg(unr,l2); p2 = addrr(unr,p2);
    setlg(p2,l2); p2 = ginv(p2);
    p2 = subrr(p2,unr);
  }
  affrr(p2,y); avma = av; return y;
}
#undef EXMAX

/********************************************************************/
/**                                                                **/
/**                   FONCTION EXPONENTIELLE                       **/
/**                                                                **/
/********************************************************************/

GEN
mpexp(GEN x)
{
  long sx = signe(x);
  pari_sp av;
  GEN y;

  if (!sx) return addsr(1,x);
  if (sx<0) setsigne(x,1);
  av = avma; y = addsr(1, mpexp1(x));
  if (sx<0) { y = ginv(y); setsigne(x,-1); }
  return gerepileupto(av,y);
}

static GEN
paexp(GEN x)
{
  long k, e = valp(x), pp = precp(x), n = e + pp;
  pari_sp av;
  GEN y,r,p1;

  if (gcmp0(x)) return gaddgs(x,1);
  if (e<=0 || (!cmpis((GEN)x[2],2) && e==1))
    err(talker,"p-adic argument out of range in gexp");
  av = avma;
  if (egalii(gdeux,(GEN)x[2]))
  {
    n--; e--; k = n/e;
    if (n%e==0) k--;
  }
  else
  {
    p1 = subis((GEN)x[2], 1);
    k = itos(dvmdii(subis(mulis(p1,n), 1), subis(mulis(p1,e), 1), &r));
    if (!signe(r)) k--;
  }
  for (y=gun; k; k--) y = gaddsg(1, gdivgs(gmul(y,x), k));
  return gerepileupto(av, y);
}

static GEN
cxexp(GEN x, long prec)
{
  GEN r,p1,p2, y = cgetg(3,t_COMPLEX);
  pari_sp av = avma, tetpil;
  r=gexp((GEN)x[1],prec);
  gsincos((GEN)x[2],&p2,&p1,prec);
  tetpil = avma;
  y[1] = lmul(r,p1);
  y[2] = lmul(r,p2);
  gerepilemanyvec(av,tetpil,y+1,2);
  return y;
}

static GEN
serexp(GEN x, long prec)
{
  pari_sp av;
  long i,j,lx,ly,ex,mi;
  GEN p1,y,xd,yd;
 
  ex = valp(x);
  if (ex < 0) err(negexper,"gexp");
  if (gcmp0(x)) return gaddsg(1,x);
  lx = lg(x);
  if (ex)
  {
    ly = lx+ex; y = cgetg(ly,t_SER);
    mi = lx-1; while (mi>=3 && gcmp0((GEN)x[mi])) mi--;
    mi += ex-2;
    y[1] = evalsigne(1) | evalvalp(0) | evalvarn(varn(x));
    /* zd[i] = coeff of X^i in z */
    xd = x+2-ex; yd = y+2; ly -= 2;
    yd[0] = un;
    for (i=1; i<ex; i++) yd[i]=zero;
    for (   ; i<ly; i++)
    {
      av = avma; p1 = gzero;
      for (j=ex; j<=min(i,mi); j++)
        p1 = gadd(p1, gmulgs(gmul((GEN)xd[j],(GEN)yd[i-j]),j));
      yd[i] = lpileupto(av, gdivgs(p1,i));
    }
    return y;
  }
  av = avma; y = cgetg(lx, t_SER);
  y[1] = x[1]; y[2] = zero;
  for (i=3; i <lx; i++) y[i] = x[i];
  p1 = gexp((GEN)x[2],prec);
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
    case t_PADIC: return paexp(x);
    case t_INTMOD: err(typeer,"gexp");
    default:
    {
      pari_sp av = avma;
      GEN y;
      if (!(y = _toser(x))) break;
      return gerepileupto(av, serexp(y,prec));
    }
  }
  return transc(gexp,x,prec);
}

void
gexpz(GEN x, GEN y)
{
  long prec = precision(y);
  pari_sp av=avma;

  if (!prec) err(infprecer,"gexpz");
  gaffect(gexp(x,prec),y); avma=av;
}

/********************************************************************/
/**                                                                **/
/**                      FONCTION LOGARITHME                       **/
/**                                                                **/
/********************************************************************/
/* 2 * atanh(1/3) */
GEN
constlog2(long prec)
{
  static GEN glog2 = NULL;
  const long _3 = 3, _9 = _3*_3;
  pari_sp av0, av;
  long k, l, G;
  GEN s, u, S, U, tmplog2;

  if (glog2 && lg(glog2) >= prec) return glog2;

  tmplog2 = newbloc(prec);
  *tmplog2 = evaltyp(t_REAL) | evallg(prec);
  av0 = avma;
  l = prec+1; G = bit_accuracy(l+1);

  s = S = divrs(realun(l), _3);
  u = U = mpcopy(s);
  av = avma;
  for (k = 3; ; k += 2)
  {
    u = divrs(u, _9);
    if (bit_accuracy(l) - expo(u) > G) {
      l--; if (l <= 2) break;
      setlg(U,l);
      affrr(s,S); s = S;
      affrr(u,U); u = U; avma = av;
    }
    s = addrr(s, divrs(u,k));
  }
  setexpo(s, -1); affrr(s, tmplog2);
  gunclone(glog2); glog2 = tmplog2;
  avma = av0; return glog2;
} 

GEN
mplog2(long prec)
{
  GEN x = cgetr(prec);
  affrr(constlog2(prec), x); return x;
} 

GEN
mplog(GEN x)
{
  pari_sp ltop, av;
  long EX,l,l1,l2,m,n,k,ex,s;
  double alpha,a,b;
  GEN z,p1,y,y2,p4,p5,unr;

  if (typ(x)!=t_REAL) err(typeer,"mplog");
  if (signe(x)<=0) err(talker,"non positive argument in mplog");

  av = avma;
  l = lg(x); EX = expo(x);
  z = cgetr(l); ltop = avma;

  l2 = l+1; y=p1=cgetr(l2); affrr(x,p1);
  setexpo(p1, 0);
  if (gcmp1(p1)) {
    if (!EX) { avma = av; return realzero(l); }
    affrr(mulsr(EX, mplog2(l)), z);
    avma = ltop; return z;
  }
  /* 1 < p1 < 2 */
  av = avma; l -= 2;
  alpha = 1+p1[2]/C31; if (!alpha) alpha = 0.00000001;
  a = -log(alpha)/LOG2;
  b = sqrt(BITS_IN_HALFULONG*l/3.0);
  if (a <= b)
  {
    n = 1 + (long)sqrt(BITS_IN_HALFULONG*3.0*l);
    m = 1 + (long)(b-a);
    l2 += m>>TWOPOTBITS_IN_LONG;
    p4 = cgetr(l2); affrr(p1,p4);
    p1 = p4; av = avma;
    for (k=1; k<=m; k++) p1 = mpsqrt(p1);
    affrr(p1,p4); avma = av;
  }
  else
  {
    n = 1 + (long)(BITS_IN_HALFULONG*l / a);
    m = 0; p4 = p1;
  }
  unr = realun(l2);
  y  = cgetr(l2);
  y2 = cgetr(l2); av = avma;

  /* want to compute log(X), X ~ 1  (X = p4) */
  /* y = (X-1)/(X+1).  log(X) = log(1+y) - log(1-y) = 2 \sum_{k odd} y^k / * k */

  /* affrr needed here instead of setlg since prec may DECREASE */
  p1 = cgetr(l2); affrr(subrr(p4,unr), p1);

  p5 = addrr(p4,unr); setlg(p5,l2);
  affrr(divrr(p1,p5), y); /* = (X-1) / (X+1) ~ 0 */
  affrr(gsqr(y), y2); /* = y^2 */
  k = 2*n + 1;
  affrr(divrs(unr,k), p4); setlg(p4,4); avma = av;

  s = 0; ex = expo(y2); l1 = 4;
  for (k -= 2; k > 0; k -= 2)
  { /* compute sum_i=0^n  y^2i / (2i + 1), k = 2i+1 */
    setlg(y2, l1); p5 = mulrr(p4,y2);
    setlg(unr,l1); p1 = divrs(unr, k);
    s -= ex;
    l1 += s>>TWOPOTBITS_IN_LONG; if (l1>l2) l1=l2;
    s &= (BITS_IN_LONG-1);
    setlg(p1, l1);
    setlg(p4, l1);
    setlg(p5, l1); affrr(addrr(p1,p5), p4); avma=av;
  }
  setlg(p4, l2);
  y = mulrr(y,p4); /* = log(X)/2 */
  setexpo(y, expo(y)+m+1);
  if (EX) y = addrr(y, mulsr(EX, mplog2(l2)));
  affrr(y, z); avma = ltop; return z;
}

GEN
teich(GEN x)
{
  GEN p,q,y,z,aux,p1;
  long n, k;
  pari_sp av;

  if (typ(x)!=t_PADIC) err(talker,"not a p-adic argument in teichmuller");
  if (!signe(x[4])) return gcopy(x);
  p = (GEN)x[2];
  q = (GEN)x[3];
  z = (GEN)x[4];
  y = cgetp(x); av = avma;
  if (egalii(p, gdeux))
    z = (mod4(z) & 2)? addsi(-1,q): gun;
  else
  {
    p1 = addsi(-1, p);
    z = resii(z, p);
    aux = divii(addsi(-1,q),p1); n = precp(x);
    for (k=1; k<n; k<<=1)
      z = modii(mulii(z,addsi(1,mulii(aux,addsi(-1,powmodulo(z,p1,q))))), q);
  }
  affii(z, (GEN)y[4]); avma = av; return y;
}

/* Let x = 1 mod p and y := (x-1)/(x+1) = 0 (p). Then
 * log(x) = log(1+y) - log(1-y) = 2 \sum_{k odd} y^k / k.
 * palogaux(x) returns the last sum (not multiplied by 2) */
static GEN
palogaux(GEN x)
{
  long k,e,pp;
  GEN y,s,y2, p = (GEN)x[2];

  if (egalii(gun, (GEN)x[4]))
  {
    long v = valp(x)+precp(x);
    if (egalii(gdeux,p)) v--;
    return padiczero(p, v);
  }
  y = gdiv(gaddgs(x,-1), gaddgs(x,1));
  e = valp(y); pp = e+precp(y);
  if (egalii(gdeux,p)) pp--;
  else
  {
    GEN p1;
    for (p1=stoi(e); cmpsi(pp,p1)>0; pp++) p1 = mulii(p1, p);
    pp -= 2;
  }
  k = pp/e; if (!odd(k)) k--;
  y2 = gsqr(y); s = gdivgs(gun,k);
  while (k > 2)
  {
    k -= 2; s = gadd(gmul(y2,s), gdivgs(gun,k));
  }
  return gmul(s,y);
}

GEN
palog(GEN x)
{
  pari_sp av = avma;
  GEN y, p = (GEN)x[2];

  if (!signe(x[4])) err(talker,"zero argument in palog");
  if (egalii(p, gdeux))
  {
    y = gsqr(x); setvalp(y,0);
    y = palogaux(y);
  }
  else
  { /* compute log(x^(p-1)) / (p-1) */
    GEN mod = (GEN)x[3], p1 = subis(p,1);
    y = cgetp(x);
    y[4] = (long)powmodulo((GEN)x[4], p1, mod);
    p1 = divii(subis(mod,1), p1); /* 1/(1-p) */
    y = gmul(palogaux(y), mulis(p1, -2));
  }
  return gerepileupto(av,y);
}

GEN
log0(GEN x, long flag,long prec)
{
  switch(flag)
  {
    case 0: return glog(x,prec);
    case 1: return glogagm(x,prec);
    default: err(flagerr,"log");
  }
  return NULL; /* not reached */
}

GEN
glog(GEN x, long prec)
{
  pari_sp av, tetpil;
  GEN y, p1;

  switch(typ(x))
  {
    case t_REAL:
      if (signe(x)>=0) return mplog(x);
      y=cgetg(3,t_COMPLEX); y[2]=lmppi(lg(x));
      setsigne(x,1); y[1]=lmplog(x);
      setsigne(x,-1); return y;

    case t_COMPLEX:
      y=cgetg(3,t_COMPLEX); y[2]=larg(x,prec);
      av=avma; p1=glog(gnorm(x),prec); tetpil=avma;
      y[1]=lpile(av,tetpil,gmul2n(p1,-1));
      return y;

    case t_PADIC:
      return palog(x);

    case t_INTMOD: err(typeer,"glog");
    default:
      av = avma; if (!(y = _toser(x))) break;
      if (valp(y) || gcmp0(y)) err(talker,"log is not analytic at 0");
      p1 = integ(gdiv(derivser(y), y), varn(y)); /* log(y)' = y'/y */
      if (!gcmp1((GEN)y[2])) p1 = gadd(p1, glog((GEN)y[2],prec));
      return gerepileupto(av, p1);
  }
  return transc(glog,x,prec);
}

void
glogz(GEN x, GEN y)
{
  long prec = precision(y);
  pari_sp av=avma;

  if (!prec) err(infprecer,"glogz");
  gaffect(glog(x,prec),y); avma=av;
}

/********************************************************************/
/**                                                                **/
/**                        SINE, COSINE                            **/
/**                                                                **/
/********************************************************************/

/* Reduce x0 mod Pi/2 to x in [-Pi/4, Pi/4]. Return cos(x)-1 */
static GEN
mpsc1(GEN x0, long *ptmod8)
{
  const long mmax = 23169; /* largest m such that (2m+2)(2m+1) < 2^31 */
 /* on a 64-bit machine with true 128 bit/64 bit division, one could
  * take mmax=1518500248; on the alpha it does not seem worthwhile */
  long l, l0, l1, l2, l4, i, n, m, s, t;
  pari_sp av;
  double alpha,beta,a,b,c,d;
  GEN y,p1,p2,p3,x2,pitemp, x = x0;

  if (typ(x) != t_REAL) err(typeer,"mpsc1");
  l = lg(x); y = cgetr(l); av = avma;

  l++; pitemp = mppi(l);
  setexpo(pitemp,-1);
  p1 = addrr(x,pitemp); /* = x + Pi/4 */
  l0 = min(l, lg(p1));
  if (expo(p1) >= bit_accuracy(l0) + 3) err(precer,"mpsc1");

  setexpo(pitemp, 0);
  p1 = mpent( divrr(p1,pitemp) ); /* round ( x / (Pi/2) ) */
  if (signe(p1)) x = subrr(x, mulir(p1,pitemp)); /* x mod Pi/2  */
  p2 = cgetr(l); affrr(x, p2); x = p2;

  *ptmod8 = (signe(x) < 0)? 4: 0;
  if (signe(p1))
  {
    long k = mod4(p1);
    if (signe(p1) < 0 && k) k = 4-k;
    /* x = x0 - k*Pi/2  (mod 2Pi) */
    *ptmod8 += k;
  }

  if (gcmp0(x)) alpha = 1000000.0;
  else
  {
    long e = expo(x);
    alpha = -1 - ((e<-1022)? e*LOG2: log(fabs(rtodbl(x))));
  }
  beta = 5 + bit_accuracy(l)*LOG2;
  a = 0.5 / LOG2;
  b = 0.5 * a;
  c = a + sqrt((beta+b) / LOG2);
  d = ((beta/c) - alpha - log(c)) / LOG2;
  if (d >= 0)
  {
    m = (long)(1+d);
    n = (long)((1+c) / 2.0);
    setexpo(x, expo(x)-m);
  }
  else { m = 0; n = (long)((2+beta/alpha) / 2.0); }
  l2=l+1+(m>>TWOPOTBITS_IN_LONG);
  p2 = realun(l2);
  x2 = cgetr(l2); av = avma;
  affrr(gsqr(x), x2);
  
  setlg(x2, 3);
  if (n > mmax)
    p3 = divrs(divrs(x2, 2*n+2), 2*n+1);
  else
    p3 = divrs(x2, (2*n+2)*(2*n+1));
  s = -expo(p3);
  l4 = l1 = 3 + (s>>TWOPOTBITS_IN_LONG);
  if (l4<=l2) { setlg(p2,l4); setlg(x2,l4); }
  s = 0;
  for (i=n; i>=2; i--)
  {
    if (i > mmax)
      p3 = divrs(divrs(x2, 2*i), 2*i-1);
    else
      p3 = divrs(x2, 2*i*(2*i-1));
    s -= expo(p3);
    t = s & (BITS_IN_LONG-1); l0 = (s>>TWOPOTBITS_IN_LONG);
    if (t) l0++;
    l1 += l0; if (l1>l2) { l0 += l2-l1; l1=l2; }
    l4 += l0;
    p3 = mulrr(p3,p2);
    if (l4<=l2) { setlg(p2,l4); setlg(x2,l4); }
    subsrz(1,p3, p2); avma = av;
  }
  setlg(p2,l2); setlg(x2,l2);
  setexpo(p2, expo(p2)-1); setsigne(p2, -signe(p2));
  p2 = mulrr(x2,p2);
  /* Now p2 = sum {1<= i <=n} (-1)^i x^(2i) / (2i)! ~ cos(x) - 1 */
  for (i=1; i<=m; i++)
  { /* p2 = cos(x)-1 --> cos(2x)-1 */
    p2 = mulrr(p2, addsr(2,p2)); setexpo(p2, expo(p2)+1);
  }
  affrr(p2,y); avma=av; return y;
}

/* sqrt (1 - (1+x)^2) = sqrt(-x*(x+2)). Sends cos(x)-1 to |sin(x)| */
static GEN
mpaut(GEN x)
{
  pari_sp av = avma;
  GEN p1 = mulrr(x, addsr(2,x));
  setsigne(p1, -signe(p1));
  return gerepileuptoleaf(av, mpsqrt(p1));
}

/********************************************************************/
/**                            COSINE                              **/
/********************************************************************/

static GEN
mpcos(GEN x)
{
  long mod8;
  pari_sp av;
  GEN y,p1;

  if (typ(x)!=t_REAL) err(typeer,"mpcos");
  if (!signe(x)) return addsr(1,x);

  av = avma; p1 = mpsc1(x,&mod8);
  switch(mod8)
  {
    case 0: case 4:
      y=addsr(1,p1); break;
    case 1: case 7:
      y=mpaut(p1); setsigne(y,-signe(y)); break;
    case 2: case 6:
      y=subsr(-1,p1); break;
    default: /* case 3: case 5: */
      y=mpaut(p1); break;
  }
  return gerepileuptoleaf(av, y);
}

GEN
gcos(GEN x, long prec)
{
  pari_sp av, tetpil;
  GEN r,u,v,y,p1,p2;

  switch(typ(x))
  {
    case t_REAL:
      return mpcos(x);

    case t_COMPLEX:
      y=cgetg(3,t_COMPLEX); av=avma;
      r=gexp((GEN)x[2],prec); p1=ginv(r);
      p2=gmul2n(gadd(p1,r),-1);
      p1=gsub(p2,r);
      gsincos((GEN)x[1],&u,&v,prec);
      tetpil=avma;
      y[1]=lmul(p2,v); y[2]=lmul(p1,u);
      gerepilemanyvec(av,tetpil,y+1,2);
      return y;

    case t_INTMOD: case t_PADIC: err(typeer,"gcos");

    default:
      av = avma; if (!(y = _toser(x))) break;
      if (gcmp0(y)) return gaddsg(1,y);
      if (valp(y) < 0) err(negexper,"gcos");
      gsincos(y,&u,&v,prec);
      return gerepilecopy(av,v);
  }
  return transc(gcos,x,prec);
}

void
gcosz(GEN x, GEN y)
{
  long prec = precision(y);
  pari_sp av = avma;

  if (!prec) err(infprecer,"gcosz");
  gaffect(gcos(x,prec),y); avma=av;
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

  if (typ(x)!=t_REAL) err(typeer,"mpsin");
  if (!signe(x)) return realzero_bit(expo(x));

  av = avma; p1 = mpsc1(x,&mod8);
  switch(mod8)
  {
    case 0: case 6:
      y=mpaut(p1); break;
    case 1: case 5:
      y=addsr(1,p1); break;
    case 2: case 4:
      y=mpaut(p1); setsigne(y,-signe(y)); break;
    default: /* case 3: case 7: */
      y=subsr(-1,p1); break;
  }
  return gerepileuptoleaf(av, y);
}

GEN
gsin(GEN x, long prec)
{
  pari_sp av, tetpil;
  GEN r,u,v,y,p1,p2;

  switch(typ(x))
  {
    case t_REAL:
      return mpsin(x);

    case t_COMPLEX:
      y=cgetg(3,t_COMPLEX); av=avma;
      r=gexp((GEN)x[2],prec); p1=ginv(r);
      p2=gmul2n(gadd(p1,r),-1);
      p1=gsub(p2,p1);
      gsincos((GEN)x[1],&u,&v,prec);
      tetpil=avma;
      y[1]=lmul(p2,u);
      y[2]=lmul(p1,v);
      gerepilemanyvec(av,tetpil,y+1,2);
      return y;

    case t_INTMOD: case t_PADIC: err(typeer,"gsin");

    default:
      av = avma; if (!(y = _toser(x))) break;
      if (gcmp0(y)) return gcopy(y);
      if (valp(y) < 0) err(negexper,"gsin");
      gsincos(y,&u,&v,prec);
      return gerepilecopy(av,u);
  }
  return transc(gsin,x,prec);
}

void
gsinz(GEN x, GEN y)
{
  long prec = precision(y);
  pari_sp av=avma;

  if (!prec) err(infprecer,"gsinz");
  gaffect(gsin(x,prec),y); avma=av;
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

  if (typ(x)!=t_REAL) err(typeer,"mpsincos");
  if (!signe(x))
  {
    *s = realzero_bit(expo(x));
    *c = addsr(1,x); return;
  }

  av=avma; p1=mpsc1(x,&mod8); tetpil=avma;
  switch(mod8)
  {
    case 0: *c=addsr( 1,p1); *s=mpaut(p1); break;
    case 1: *s=addsr( 1,p1); *c=mpaut(p1); setsigne(*c,-signe(*c)); break;
    case 2: *c=subsr(-1,p1); *s=mpaut(p1); setsigne(*s,-signe(*s)); break;
    case 3: *s=subsr(-1,p1); *c=mpaut(p1); break;
    case 4: *c=addsr( 1,p1); *s=mpaut(p1); setsigne(*s,-signe(*s)); break;
    case 5: *s=addsr( 1,p1); *c=mpaut(p1); break;
    case 6: *c=subsr(-1,p1); *s=mpaut(p1); break;
    case 7: *s=subsr(-1,p1); *c=mpaut(p1); setsigne(*c,-signe(*c)); break;
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
  if (!signe(x)) return gerepilecopy(av, (GEN)v[1]);
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
    case t_INT: case t_FRAC: case t_FRACN:
      av=avma; p1=cgetr(prec); gaffect(x,p1); tetpil=avma;
      mpsincos(p1,s,c); gptr[0]=s; gptr[1]=c;
      gerepilemanysp(av,tetpil,gptr,2);
      return;

    case t_REAL:
      mpsincos(x,s,c); return;

    case t_COMPLEX:
      ps=cgetg(3,t_COMPLEX); pc=cgetg(3,t_COMPLEX);
      *s=ps; *c=pc; av=avma;
      r=gexp((GEN)x[2],prec); p1=ginv(r);
      v1=gmul2n(gadd(p1,r),-1);
      u1=gsub(v1,p1); r=gsub(v1,r);/*u1=I*sin(I*Im(x));v1=cos(I*Im(x));r=-u1*/
      gsincos((GEN)x[1],&u,&v,prec);
      tetpil=avma;
      p1=gmul(v1,u); p2=gmul(u1,v);
      p3=gmul(v1,v); p4=gmul(r,u);
      gptr[0]=&p1; gptr[1]=&p2; gptr[2]=&p3; gptr[3]=&p4;
      gerepilemanysp(av,tetpil,gptr,4);
      ps[1]=(long)p1; pc[1]=(long)p3;
      ps[2]=(long)p2; pc[2]=(long)p4;
      return;

    case t_QUAD:
      av = avma; p1=gmul(x,realun(prec)); tetpil = avma;
      gsincos(p1,s,c,prec);
      gptr[0]=s; gptr[1]=c;
      gerepilemanysp(av,tetpil,gptr,2);
      return;

    default:
      av = avma; if (!(y = _toser(x))) break;
      if (gcmp0(y)) { *c = gaddsg(1,y); *s = gcopy(y); return; }

      ex = valp(y); lx = lg(y); ex2 = 2*ex+2;
      if (ex < 0) err(talker,"non zero exponent in gsincos");
      if (ex2 > lx)
      {
        *s = x == y? gcopy(y): gerepilecopy(av, y); av = avma;
        *c = gerepileupto(av, gsubsg(1, gdivgs(gsqr(y),2)));
	return;
      }
      if (!ex)
      {
        p1 = dummycopy(y); p1[2] = zero;
        gsincos(normalize(p1),&u,&v,prec);
        gsincos((GEN)y[2],&u1,&v1,prec);
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
      mi = lx-1; while (mi>=3 && gcmp0((GEN)y[mi])) mi--;
      mi += ex-2;
      pc = cgetg(ly,t_SER); *c = pc;
      ps = cgetg(lx,t_SER); *s = ps;
      pc[1] = evalsigne(1) | evalvalp(0) | evalvarn(varn(y));
      pc[2] = un; ps[1] = y[1];
      for (i=2; i<ex+2; i++) ps[i] = lcopy((GEN)y[i]);
      for (i=3; i< ex2; i++) pc[i] = zero;
      for (i=ex2; i<ly; i++)
      {
	ii = i-ex; av = avma; p1 = gzero;
	for (j=ex; j<=min(ii-2,mi); j++)
	  p1 = gadd(p1, gmulgs(gmul((GEN)y[j-ex+2],(GEN)ps[ii-j]),j));
	pc[i] = lpileupto(av, gdivgs(p1,2-i));
	if (ii < lx)
	{
	  av = avma; p1 = gzero;
	  for (j=ex; j<=min(i-ex2,mi); j++)
	    p1 = gadd(p1,gmulgs(gmul((GEN)y[j-ex+2],(GEN)pc[i-j]),j));
	  p1 = gdivgs(p1,i-2);
	  ps[i-ex] = lpileupto(av, gadd(p1,(GEN)y[i-ex]));
	}
      }
      return;
  }
  err(typeer,"gsincos");
}

/********************************************************************/
/**                                                                **/
/**                FONCTIONS TANGENTE ET COTANGENTE                **/
/**                                                                **/
/********************************************************************/

static GEN
mptan(GEN x)
{
  pari_sp av=avma, tetpil;
  GEN s,c;

  mpsincos(x,&s,&c); tetpil=avma;
  return gerepile(av,tetpil,divrr(s,c));
}

GEN
gtan(GEN x, long prec)
{
  pari_sp av;
  GEN y, s, c;

  switch(typ(x))
  {
    case t_REAL: return mptan(x);

    case t_COMPLEX:
      av = avma; gsincos(x,&s,&c,prec);
      return gerepileupto(av, gdiv(s,c));

    case t_INTMOD: case t_PADIC: err(typeer,"gtan");
    
    default:
      av = avma; if (!(y = _toser(x))) break;
      if (gcmp0(y)) return gcopy(y);
      if (valp(y) < 0) err(negexper,"gtan");
      gsincos(y,&s,&c,prec);
      return gerepileupto(av, gdiv(s,c));
  }
  return transc(gtan,x,prec);
}

void
gtanz(GEN x, GEN y)
{
  long prec = precision(y);
  pari_sp av=avma;

  if (!prec) err(infprecer,"gtanz");
  gaffect(gtan(x,prec),y); avma=av;
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
      av = avma; gsincos(x,&s,&c,prec);
      return gerepileupto(av, gdiv(c,s));

    case t_INTMOD: case t_PADIC: err(typeer,"gcotan");

    default:
      av = avma; if (!(y = _toser(x))) break;
      if (gcmp0(y)) err(talker,"0 argument in cotan");
      if (valp(y) < 0) err(negexper,"cotan"); /* fall through */
      gsincos(y,&s,&c,prec);
      return gerepileupto(av, gdiv(c,s));
  }
  return transc(gcotan,x,prec);
}

void
gcotanz(GEN x, GEN y)
{
  long prec = precision(y);
  pari_sp av=avma;

  if (!prec) err(infprecer,"gcotanz");
  gaffect(gcotan(x,prec),y); avma=av;
}
