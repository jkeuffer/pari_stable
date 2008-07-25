#line 2 "../src/kernel/none/level1.h"
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

/* This file defines "level 1" kernel functions.
 * These functions can be inline; they are also defined externally in
 * mpinl.c, which includes this file and never needs to be changed */

INLINE long
evallg(long x)
{
  if (x & ~LGBITS) pari_err(errlg);
  return _evallg(x);
}

INLINE long
evalvalp(long x)
{
  const long v = _evalvalp(x);
  if (v & ~VALPBITS) pari_err(errvalp);
  return v;
}

INLINE long
evalexpo(long x)
{
  const long v = _evalexpo(x);
  if (v & ~EXPOBITS) pari_err(errexpo);
  return v;
}

/* Inhibit some area gerepile-wise: declare it to be a non recursive
 * type, of length l. Thus gerepile won't inspect the zone, just copy it.
 * For the following situation:
 *   z = cgetg(t,a); av = avma; garbage(); ltop = avma;
 *   for (i=1; i<HUGE; i++) gel(z,i) = blah();
 *   stackdummy(av,ltop);
 * loses (av-ltop) words but save a costly gerepile.
 */
INLINE void
stackdummy(pari_sp av, pari_sp ltop) {
  long l = ((GEN)av) - ((GEN)ltop);
  if (l > 0) {
    GEN z = (GEN)ltop;
    z[0] = evaltyp(t_VECSMALL) | evallg(l);
#ifdef DEBUG
    { long i; for (i = 1; i < l; i++) z[i] = 0; }
#endif
  }
}
INLINE void
fixlg(GEN z, long ly) {
  long lz = lg(z);
  if (ly < lz)
  {
    setlg(z, ly);
    stackdummy((pari_sp)(z + lz), (pari_sp)(z + ly));
  }
}
/* update lg(z) before affrr(y, z)  [ to cater for precision loss ]*/
INLINE void
affrr_fixlg(GEN y, GEN z) { fixlg(z, lg(y)); affrr(y, z); }

INLINE GEN
new_chunk(size_t x) /* x is a number of bytes */
{
  const GEN z = ((GEN) avma) - x;
  if (x > (avma-bot) / sizeof(long)) pari_err(errpile);
#if defined(_WIN32) || defined(__CYGWIN32__)
  if (win32ctrlc) dowin32ctrlc();
#endif
  avma = (pari_sp)z;

#ifdef MEMSTEP
  if (DEBUGMEM && memused != DISABLE_MEMUSED) {
    long d = (long)memused - (long)z;
    if (d > 4*MEMSTEP || d < -4*MEMSTEP)
    {
      memused = (pari_sp)z;
      fprintferr("...%4.0lf Mbytes used\n",(top-memused)/1048576.);
    }
  }
#endif
  return z;
}

/* cgetg(lg(x), typ(x)), assuming lx = lg(x). Implicit unsetisclone() */
INLINE GEN
cgetg_copy(long lx, GEN x) {
  GEN y = new_chunk((size_t)lx);
  y[0] = x[0] & (TYPBITS|LGBITS); return y;
}
INLINE GEN
init_gen_op(GEN x, long tx, long *lx, long *i) {
  GEN y;
  *lx = lg(x); y = cgetg_copy(*lx, x);
  if (lontyp[tx] == 1) *i = 1; else { y[1] = x[1]; *i = 2; }
  return y;
}

INLINE void
cgiv(GEN x)
{
  pari_sp av = (pari_sp)(x+lg(x));
  if (isonstack(av)) avma = av;
}

INLINE GEN
cgetg(long x, long y)
{
  const GEN z = new_chunk((size_t)x);
  z[0] = evaltyp(y) | evallg(x);
  return z;
}

INLINE GEN
cgeti(long x)
{
  const GEN z = new_chunk((size_t)x);
  z[0] = evaltyp(t_INT) | evallg(x);
  return z;
}
INLINE GEN
cgetipos(long x)
{
  const GEN z = cgeti(x);
  z[1] = evalsigne(1) | evallgefint(x);
  return z;
}
INLINE GEN
cgetineg(long x)
{
  const GEN z = cgeti(x);
  z[1] = evalsigne(-1) | evallgefint(x);
  return z;
}

/* x 2^BIL + y */
INLINE GEN
uutoi(ulong x, ulong y)
{
  GEN z;
  if (!x) return utoi(y);
  z = cgetipos(4); 
  *int_W_lg(z, 1, 4) = x;
  *int_W_lg(z, 0, 4) = y; return z;
}
/* - (x 2^BIL + y) */
INLINE GEN
uutoineg(ulong x, ulong y)
{
  GEN z;
  if (!x) return y? utoineg(y): gen_0;
  z = cgetineg(4); 
  *int_W_lg(z, 1, 4) = x;
  *int_W_lg(z, 0, 4) = y; return z;
}

INLINE GEN
cgetr(long x)
{
  const GEN z = new_chunk((size_t)x);
  z[0] = evaltyp(t_REAL) | evallg(x);
  return z;
}
INLINE GEN
cgetc(long l)
{
  GEN u = cgetg(3,t_COMPLEX); gel(u,1) = cgetr(l); gel(u,2) = cgetr(l);
  return u;
}
/* cannot do memcpy because sometimes x and y overlap */
INLINE GEN
mpcopy(GEN x)
{
  register long lx = lg(x);
  const GEN y = cgetg_copy(lx, x);
  while (--lx > 0) y[lx] = x[lx];
  return y;
}
INLINE GEN
rcopy(GEN x){ return mpcopy(x); }
INLINE GEN
icopy(GEN x)
{
  register long lx = lgefint(x);
  const GEN y = cgeti(lx);
  while (--lx > 0) y[lx] = x[lx];
  return y;
}

/* copy integer x as if we had avma = av */
INLINE GEN
icopy_av(GEN x, GEN y)
{
  register long lx = lgefint(x);
  register long ly = lx;
  y -= lx;
  while (--lx > 0) y[lx]=x[lx];
  y[0] = evaltyp(t_INT)|evallg(ly);
  return y;
}
INLINE GEN
gerepileuptoleaf(pari_sp av, GEN q)
{
  long i;
  GEN q0;

  if (!isonstack(q) || (GEN)av==q) { avma = av; return q; }
  i = lg(q); avma = (pari_sp)(((GEN)av) -  i);
  q0 = (GEN)avma; while (--i >= 0) q0[i] = q[i];
  return q0;
}
INLINE GEN
gerepileuptoint(pari_sp av, GEN q)
{
  if (!isonstack(q) || (GEN)av==q) { avma = av; return q; }
  avma = (pari_sp)icopy_av(q, (GEN)av);
  return (GEN)avma;
}

INLINE GEN
mpneg(GEN x) { const GEN y=mpcopy(x); togglesign(y); return y; }

INLINE GEN
mpabs(GEN x)
{
  const GEN y=mpcopy(x);
  if (signe(x)<0) setsigne(y,1);
  return y;
}
INLINE GEN
absr(GEN x) { return mpabs(x); }
INLINE GEN
absi(GEN x) { return mpabs(x); }
INLINE GEN
negi(GEN x) { return mpneg(x); }
INLINE GEN
negr(GEN x) { return mpneg(x); }

INLINE long
smodis(GEN x, long y)
{
  long rem;
  const pari_sp av=avma; (void)divis_rem(x,y, &rem); avma=av;
  return (rem >= 0) ? rem: labs(y) + rem;
}

INLINE long
smodss(long x, long y)
{
  long rem = x%y;
  return (rem >= 0)? rem: labs(y) + rem;
}

/* assume x != 0, return -x as a t_INT */
INLINE GEN
utoineg(ulong x) { GEN y = cgetineg(3); y[2] = x; return y; }
/* assume x != 0, return utoi(x) */
INLINE GEN
utoipos(ulong x) { GEN y = cgetipos(3); y[2] = x; return y; }
INLINE GEN
utoi(ulong x) { return x? utoipos(x): gen_0; }
INLINE GEN
stoi(long x)
{
  if (!x) return gen_0;
  return x > 0? utoipos((ulong)x): utoineg((ulong)-x);
}

INLINE long
itos(GEN x)
{
  const long s = signe(x);
  long u;

  if (!s) return 0;
  u = x[2]; if (lgefint(x) > 3 || u < 0) pari_err(affer2);
  return (s>0) ? u : -u;
}
INLINE long
gtos(GEN x) {
  if (typ(x) != t_INT) pari_err(talker,"gtos expected an integer, got '%Ps'",x);
  return itos(x);
}

/* as itos, but return 0 if too large. Cf is_bigint */
INLINE long
itos_or_0(GEN x) {
  long n;
  if (lgefint(x) != 3 || (n = x[2]) & HIGHBIT) return 0;
  return signe(x) > 0? n: -n;
}
/* as itou, but return 0 if too large. Cf is_bigint */
INLINE ulong
itou_or_0(GEN x) {
  if (lgefint(x) != 3) return 0;
  return (ulong)x[2];
}

INLINE GEN
modss(long x, long y) { return stoi(smodss(x, y)); }

INLINE GEN
remss(long x, long y) { return stoi(x % y); }

INLINE void
affii(GEN x, GEN y)
{
  long lx;

  if (x==y) return;
  lx=lgefint(x); if (lg(y)<lx) pari_err(talker,"impossible assignment I-->I");

  while (--lx) y[lx]=x[lx];
}

INLINE void
affsi(long s, GEN x)
{
  if (!s) x[1] = evalsigne(0) | evallgefint(2);
  else
  {
    if (s > 0) { x[1] = evalsigne( 1) | evallgefint(3); x[2] =  s; }
    else       { x[1] = evalsigne(-1) | evallgefint(3); x[2] = -s; }
  }
}

INLINE void
affsr(long x, GEN y)
{
  long sh, i, ly = lg(y);

  if (!x)
  {
    y[1] = evalexpo(-bit_accuracy(ly));
    return;
  }
  if (x < 0) {
    x = -x; sh = bfffo(x);
    y[1] = evalsigne(-1) | _evalexpo((BITS_IN_LONG-1)-sh);
  }
  else
  {
    sh = bfffo(x);
    y[1] = evalsigne(1) | _evalexpo((BITS_IN_LONG-1)-sh);
  }
  y[2] = x<<sh; for (i=3; i<ly; i++) y[i]=0;
}

INLINE void
affur(ulong x, GEN y)
{
  long sh, i, ly = lg(y);

  if (!x)
  {
    y[1] = evalexpo(-bit_accuracy(ly));
    return;
  }
  sh = bfffo(x);
  y[1] = evalsigne(1) | _evalexpo((BITS_IN_LONG-1)-sh);
  y[2] = x<<sh; for (i=3; i<ly; i++) y[i] = 0;
}

INLINE void
affiz(GEN x, GEN y) { if (typ(y)==t_INT) affii(x,y); else affir(x,y); }
INLINE void
affsz(long x, GEN y) { if (typ(y)==t_INT) affsi(x,y); else affsr(x,y); }
INLINE void
mpaff(GEN x, GEN y) { if (typ(x)==t_INT) affiz(x, y); else affrr(x,y); }

INLINE GEN
real_0_bit(long bitprec) { GEN x=cgetr(2); x[1]=evalexpo(bitprec); return x; }
INLINE GEN
real_0(long prec) { return real_0_bit(-bit_accuracy(prec)); }
INLINE GEN
real_1(long prec) {
  GEN x = cgetr(prec);
  long i;
  x[1] = evalsigne(1) | _evalexpo(0);
  x[2] = (long)HIGHBIT; for (i=3; i<prec; i++) x[i] = 0;
  return x;
}
INLINE GEN
real_m1(long prec) {
  GEN x = cgetr(prec);
  long i;
  x[1] = evalsigne(-1) | _evalexpo(0);
  x[2] = (long)HIGHBIT; for (i=3; i<prec; i++) x[i] = 0;
  return x;
}

/* 2.^n */
INLINE GEN
real2n(long n, long prec) { GEN z = real_1(prec); setexpo(z, n); return z; }
INLINE GEN
stor(long s, long prec) { GEN z = cgetr(prec); affsr(s,z); return z; }
INLINE GEN
utor(ulong s, long prec){ GEN z = cgetr(prec); affur(s,z); return z; }
INLINE GEN
itor(GEN x, long prec) { GEN z = cgetr(prec); affir(x,z); return z; }
INLINE GEN
rtor(GEN x, long prec) { GEN z = cgetr(prec); affrr(x,z); return z; }

/* assume x != 0 and x t_REAL, return an approximation to log2(|x|) */
INLINE double
dbllog2r(GEN x)
{
  return log2((double)(ulong)x[2]) + (double)(expo(x) - (BITS_IN_LONG-1));
}

INLINE GEN
shiftr(GEN x, long n)
{
  const long e = evalexpo(expo(x)+n);
  const GEN y = rcopy(x);

  if (e & ~EXPOBITS) pari_err(errexpo);
  y[1] = (y[1]&~EXPOBITS) | e; return y;
}

INLINE int
cmpir(GEN x, GEN y)
{
  pari_sp av;
  GEN z;

  if (!signe(x)) return -signe(y);
  if (!signe(y)) return  signe(x);
  av=avma; z = itor(x, lg(y)); avma=av;
  return cmprr(z,y); /* cmprr does no memory adjustment */
}
INLINE int
cmpri(GEN x, GEN y) { return -cmpir(y,x); }
INLINE int
cmpsr(long x, GEN y)
{
  pari_sp av;
  GEN z;

  if (!x) return -signe(y);
  av=avma; z = stor(x, 3); avma=av;
  return cmprr(z,y);
}
INLINE int
cmprs(GEN x, long y) { return -cmpsr(y,x); }
/* compare x and |y| */
INLINE int
cmpui(ulong x, GEN y)
{
  long l = lgefint(y);
  ulong p;

  if (!x) return (l > 2)? -1: 0;
  if (l == 2) return 1;
  if (l > 3) return -1;
  p = y[2]; if (p == x) return 0;
  return p < x ? 1 : -1;
}
INLINE int
cmpiu(GEN x, ulong y) { return -cmpui(y,x); }
INLINE int
cmpsi(long x, GEN y)
{
  ulong p;

  if (!x) return -signe(y);

  if (x>0)
  {
    if (signe(y)<=0) return 1;
    if (lgefint(y)>3) return -1;
    p=y[2]; if (p == (ulong)x) return 0;
    return p < (ulong)x ? 1 : -1;
  }

  if (signe(y)>=0) return -1;
  if (lgefint(y)>3) return 1;
  p=y[2]; if (p == (ulong)-x) return 0;
  return p < (ulong)(-x) ? -1 : 1;
}
INLINE int
cmpis(GEN x, long y) { return -cmpsi(y,x); }

/* x == y ? */
INLINE int
equalsi(long x, GEN y)
{
  if (!x) return !signe(y);
  if (x > 0)
  {
    if (signe(y) <= 0 || lgefint(y) != 3) return 0;
    return ((ulong)y[2] == (ulong)x);
  }
  if (signe(y) >= 0 || lgefint(y) != 3) return 0;
  return ((ulong)y[2] == (ulong)-x);
}
/* x == |y| ? */
INLINE int
equalui(ulong x, GEN y)
{
  if (!x) return !signe(y);
  return (lgefint(y) == 3 && (ulong)y[2] == x);
}
INLINE int
equaliu(GEN x, ulong y) { return equalui(y,x); }
INLINE int
equalis(GEN x, long y) { return equalsi(y,x); }

INLINE long
maxss(long x, long y) { return x>y?x:y; }
INLINE long
minss(long x, long y) { return x<y?x:y; }

INLINE GEN
subuu(ulong x, ulong y)
{
  ulong z;
  LOCAL_OVERFLOW;
  z = subll(x, y);
  return overflow? utoineg(-z): utoi(z);
}
INLINE GEN
adduu(ulong x, ulong y) { ulong t = x+y; return uutoi((t < x), t); }

INLINE GEN
addss(long x, long y)
{
  if (!x) return stoi(y);
  if (!y) return stoi(x);
  if (x > 0) return y > 0? adduu(x,y): subuu(x, -y);

  if (y > 0) return subuu(y, -x);
  else { /* - adduu(-x, -y) */
    ulong t = (-x)+(-y); return uutoineg((t < (ulong)(-x)), t);
  }
}
INLINE GEN subss(long x, long y) { return addss(-y,x); }
INLINE void subssz(long x, long y, GEN z) { addssz(x,-y,z); }

INLINE GEN
subii(GEN x, GEN y)
{
  if (x==y) return gen_0; /* frequent with x = y = gen_0 */
  return addii_sign(x, signe(x), y, -signe(y));
}
INLINE GEN
addii(GEN x, GEN y) { return addii_sign(x, signe(x), y, signe(y)); }
INLINE GEN
addrr(GEN x, GEN y) { return addrr_sign(x, signe(x), y, signe(y)); }
INLINE GEN
subrr(GEN x, GEN y) { return addrr_sign(x, signe(x), y, -signe(y)); }
INLINE GEN
addir(GEN x, GEN y) { return addir_sign(x, signe(x), y, signe(y)); }
INLINE GEN
subir(GEN x, GEN y) { return addir_sign(x, signe(x), y, -signe(y)); }
INLINE GEN
subri(GEN x, GEN y) { return addir_sign(y, -signe(y), x, signe(x)); }
INLINE GEN
addsi(long x, GEN y) { return addsi_sign(x, y, signe(y)); }
INLINE GEN
subsi(long x, GEN y) { return addsi_sign(x, y, -signe(y)); }

INLINE GEN
addri(GEN x, GEN y) { return addir(y,x); }
INLINE GEN
addis(GEN x, long s) { return addsi(s,x); }
INLINE GEN
addrs(GEN x, long s) { return addsr(s,x); }
INLINE GEN
subis(GEN x, long y) { return addsi(-y,x); }
INLINE GEN
subrs(GEN x, long y) { return addsr(-y,x); }

INLINE long
vali(GEN x)
{
  long i;
  GEN xp;

  if (!signe(x)) return -1;
  xp=int_LSW(x);
  for (i=0; !*xp; i++) xp=int_nextW(xp);
  return vals(*xp) + i * BITS_IN_LONG;
}

INLINE GEN
divss(long x, long y) { return stoi(x / y); }

INLINE long
sdivss_rem(long x, long y, long *rem)
{
  long q;
  LOCAL_HIREMAINDER;
  if (!y) pari_err(gdiver);
  hiremainder = 0; q = divll((ulong)labs(x),(ulong)labs(y));
  if (x < 0) { hiremainder = -((long)hiremainder); q = -q; }
  if (y < 0) q = -q;
  *rem = hiremainder; return q;
}

INLINE GEN
divss_rem(long x, long y, long *rem) { return stoi(sdivss_rem(x,y,rem)); }

INLINE GEN
dvmdss(long x, long y, GEN *z)
{
  long rem;
  const GEN q = divss_rem(x,y, &rem);
  *z = stoi(rem); return q;
}

INLINE long
dvmdsBIL(long n, long *r) { *r = remsBIL(n); return divsBIL(n); }
INLINE ulong
dvmduBIL(ulong n, ulong *r) { *r = remsBIL(n); return divsBIL(n); }

INLINE ulong
udivui_rem(ulong x, GEN y, ulong *rem)
{
  long q, s = signe(y);
  LOCAL_HIREMAINDER;

  if (!s) pari_err(gdiver);
  if (!x || lgefint(y)>3) { *rem = x; return 0; }
  hiremainder=0; q = (long)divll(x, (ulong)y[2]);
  if (s < 0) q = -q;
  *rem = hiremainder; return q;
}

INLINE long
sdivsi_rem(long x, GEN y, long *rem)
{
  long q, s = signe(y);
  LOCAL_HIREMAINDER;

  if (!s) pari_err(gdiver);
  if (!x || lgefint(y)>3 || ((long)y[2]) < 0) { *rem = x; return 0; }
  hiremainder=0; q = (long)divll(labs(x), (ulong)y[2]);
  if (x < 0) { hiremainder = -((long)hiremainder); q = -q; }
  if (s < 0) q = -q;
  *rem = hiremainder; return q;
}

INLINE long
sdivsi(long x, GEN y)
{
  long q, s = signe(y);

  if (!s) pari_err(gdiver);
  if (!x || lgefint(y)>3 || ((long)y[2]) < 0) return 0;
  q = labs(x) / y[2];
  if (x < 0) q = -q;
  if (s < 0) q = -q;
  return q;
}

INLINE GEN
modsi(long x, GEN y) {
  long r;
  (void)sdivsi_rem(x, y, &r);
  return (r >= 0)? stoi(r): addsi_sign(r, y, 1);
}

INLINE GEN
divsi_rem(long s, GEN y, long *rem) { return stoi(sdivsi_rem(s,y,rem)); }

INLINE GEN
dvmdsi(long x, GEN y, GEN *z)
{
  long rem;
  const GEN q = divsi_rem(x,y, &rem);
  *z = stoi(rem); return q;
}

INLINE GEN
dvmdis(GEN x, long y, GEN *z)
{
  long rem;
  const GEN q = divis_rem(x,y, &rem);
  *z = stoi(rem); return q;
}

INLINE void
dvmdssz(long x, long y, GEN z, GEN t)
{
  long rem;
  const pari_sp av=avma; affiz(divss_rem(x,y, &rem), z); avma=av;
  affsi(rem,t);
}

INLINE void
dvmdsiz(long x, GEN y, GEN z, GEN t)
{
  long rem;
  const pari_sp av = avma; affiz(divsi_rem(x,y, &rem), z); avma = av;
  affsi(rem,t);
}

INLINE void
dvmdisz(GEN x, long y, GEN z, GEN t)
{
  long rem;
  const pari_sp av=avma; affiz(divis_rem(x,y, &rem),z); avma=av;
  affsz(rem,t);
}

INLINE void
dvmdiiz(GEN x, GEN y, GEN z, GEN t)
{
  const pari_sp av=avma;
  GEN p;

  affiz(dvmdii(x,y,&p),z); affiz(p,t); avma=av;
}

INLINE GEN
modis(GEN x, long y)
{
  return stoi(smodis(x,y));
}

INLINE ulong
umodui(ulong x, GEN y)
{
  if (!signe(y)) pari_err(gdiver);
  if (!x || lgefint(y) > 3) return x;
  return x % (ulong)y[2];
}

INLINE GEN
remsi(long x, GEN y)
{
  long rem; (void)sdivsi_rem(x,y, &rem); return stoi(rem);
}

INLINE GEN
remis(GEN x, long y)
{
  long rem;
  const pari_sp av=avma; (void)divis_rem(x,y, &rem); avma=av;
  return stoi(rem);
}

INLINE GEN
rdivis(GEN x, long y, long prec)
{
  GEN z = cgetr(prec);
  const pari_sp av = avma;
  affrr(divrs(itor(x,prec), y),z);
  avma = av; return z;
}

INLINE void
divsiz(long x, GEN y, GEN z)
{
  long junk;
  affsi(sdivsi_rem(x,y,&junk), z);
}

INLINE void
divssz(long x, long y, GEN z) { affsi(x/y, z); }

INLINE GEN
rdivsi(long x, GEN y, long prec)
{
  GEN z = cgetr(prec);
  const pari_sp av = avma;
  affrr(divsr(x, itor(y,prec)), z);
  avma = av; return z;
}

INLINE GEN
rdivss(long x, long y, long prec)
{
  GEN z = cgetr(prec);
  const pari_sp av = avma;
  affrr(divrs(stor(x, prec), y), z);
  avma = av; return z;
}

INLINE void
rdiviiz(GEN x, GEN y, GEN z)
{
  const pari_sp av = avma;
  long prec = lg(z);
  affir(x, z);
  if (!is_bigint(y)) {
    affrr(divrs(z, y[2]), z);
    if (signe(y) < 0) togglesign(z);
  }
  else
    affrr(divrr(z, itor(y,prec)), z);
  avma = av;
}

INLINE GEN
rdivii(GEN x, GEN y, long prec)
{
  GEN z = cgetr(prec);
  const pari_sp av = avma;
  affir(x, z);
  if (!is_bigint(y)) {
    affrr(divrs(z, y[2]), z);
    if (signe(y) < 0) togglesign(z);
  }
  else
    affrr(divrr(z, itor(y,prec)), z);
  avma = av; return z;
}
INLINE GEN
fractor(GEN x, long prec) { return rdivii(gel(x,1), gel(x,2), prec); }

INLINE void
divrrz(GEN x, GEN y, GEN z)
{
  const pari_sp av=avma;
  affrr(divrr(x,y),z); avma=av;
}

INLINE void
remiiz(GEN x, GEN y, GEN z)
{
  const pari_sp av=avma;
  affii(remii(x,y),z); avma=av;
}

INLINE int
dvdii(GEN x, GEN y)
{
  const pari_sp av=avma;
  const GEN p1=remii(x,y);
  avma=av; return p1 == gen_0;
}

INLINE int
mpcmp(GEN x, GEN y)
{
  if (typ(x)==t_INT)
    return (typ(y)==t_INT) ? cmpii(x,y) : cmpir(x,y);
  return (typ(y)==t_INT) ? -cmpir(y,x) : cmprr(x,y);
}

INLINE GEN
mptrunc(GEN x) { return typ(x)==t_INT? icopy(x): truncr(x); }
INLINE GEN
mpfloor(GEN x) { return typ(x)==t_INT? icopy(x): floorr(x); }
INLINE GEN
mpceil(GEN x) { return typ(x)==t_INT? icopy(x): ceilr(x); }
INLINE GEN
mpround(GEN x) { return typ(x) == t_INT? icopy(x): roundr(x); }

INLINE GEN
mpadd(GEN x, GEN y)
{
  if (typ(x)==t_INT)
    return (typ(y)==t_INT) ? addii(x,y) : addir(x,y);
  return (typ(y)==t_INT) ? addir(y,x) : addrr(x,y);
}

INLINE GEN
mpsub(GEN x, GEN y)
{
  if (typ(x)==t_INT)
    return (typ(y)==t_INT) ? subii(x,y) : subir(x,y);
  return (typ(y)==t_INT) ? subri(x,y) : subrr(x,y);
}

INLINE GEN
mpmul(GEN x, GEN y)
{
  if (typ(x)==t_INT)
    return (typ(y)==t_INT) ? mulii(x,y) : mulir(x,y);
  return (typ(y)==t_INT) ? mulir(y,x) : mulrr(x,y);
}

INLINE GEN
mpdiv(GEN x, GEN y)
{
  if (typ(x)==t_INT)
    return (typ(y)==t_INT) ? divii(x,y) : divir(x,y);
  return (typ(y)==t_INT) ? divri(x,y) : divrr(x,y);
}

INLINE int
dvdiiz(GEN x, GEN y, GEN z)
{
  const pari_sp av=avma;
  GEN p2;
  const GEN p1=dvmdii(x,y,&p2);

  if (signe(p2)) { avma=av; return 0; }
  affii(p1,z); avma=av; return 1;
}

INLINE int
mpodd(GEN x) { return signe(x) && mod2(x); }

/* assume 0 <= k <= BITS_IN_LONG. Return uniform random 0 <= x < (1<<k) */
INLINE long
random_bits(long k) { return pari_rand() >> (BITS_IN_LONG - k); }

INLINE ulong
itou(GEN x)
{
  switch(lgefint(x)) {
    case 2: return 0;
    case 3: return x[2];
    default: pari_err(affer2);
      return 0; /* not reached */
  }
}

INLINE void
affui(ulong u, GEN x)
{
  if (!u) x[1] = evalsigne(0) | evallgefint(2);
  else  { x[1] = evalsigne(1) | evallgefint(3); x[2] = u; }
}

INLINE int
dvdsi(long x, GEN y)
{
  if (!signe(y)) return x == 0;
  if (lgefint(y) != 3) return 0;
  return x % y[2] == 0;
}

INLINE int
dvdui(ulong x, GEN y)
{
  if (!signe(y)) return x == 0;
  if (lgefint(y) != 3) return 0;
  return x % y[2] == 0;
}

INLINE int
dvdis(GEN x, long y)
{
  return y? smodis(x, y) == 0: signe(x) == 0;
}

INLINE int
dvdiu(GEN x, ulong y)
{
  return y? umodiu(x, y) == 0: signe(x) == 0;
}

INLINE int
dvdisz(GEN x, long y, GEN z)
{
  const pari_sp av = avma;
  long rem;
  GEN p1 = divis_rem(x,y, &rem);
  avma = av; if (rem) return 0;
  affii(p1,z); return 1;
}

INLINE int
dvdiuz(GEN x, ulong y, GEN z)
{
  const pari_sp av = avma;
  ulong rem;
  GEN p1 = diviu_rem(x,y, &rem);
  avma = av; if (rem) return 0;
  affii(p1,z); return 1;
}

/* same as Fl_add, assume p <= 2^(BIL - 1), so that overflow can't occur */
INLINE ulong
Fl_add_noofl(ulong a, ulong b, ulong p)
{
  ulong res = a + b;
  return (res >= p) ? res - p : res;
}
INLINE ulong
Fl_add(ulong a, ulong b, ulong p)
{
  ulong res = a + b;
  return (res >= p || res < a) ? res - p : res;
}
INLINE ulong
Fl_neg(ulong x, ulong p) { return x ? p - x: 0; }

INLINE ulong
Fl_sub(ulong a, ulong b, ulong p)
{
  ulong res = a - b;
  return (res > a) ? res + p: res;
}

/* centerlift(u mod p) */
INLINE long
Fl_center(ulong u, ulong p, ulong ps2) { return (long) (u > ps2)? u - p: u; }

/* assume 0 <= u < p and ps2 = p>>1 */
INLINE GEN
Fp_center(GEN u, GEN p, GEN ps2) {
  return absi_cmp(u,ps2)<=0? icopy(u): subii(u,p);
}

INLINE ulong
Fl_mul(ulong a, ulong b, ulong p)
{
  LOCAL_HIREMAINDER;
  {
    register ulong x = mulll(a,b);
    (void)divll(x,p);
  }
  return hiremainder;
}
INLINE ulong
Fl_sqr(ulong a, ulong p)
{
  LOCAL_HIREMAINDER;
  {
    register ulong x = mulll(a,a);
    (void)divll(x,p);
  }
  return hiremainder;
}
INLINE ulong
Fl_div(ulong a, ulong b, ulong p)
{
  return Fl_mul(a, Fl_inv(b, p), p);
}

INLINE GEN
mulis(GEN x, long s) { return mulsi(s,x); }
INLINE GEN
muliu(GEN x, ulong s) { return mului(s,x); }
INLINE GEN
mulru(GEN x, ulong s) { return mulur(s,x); }
INLINE GEN
mulri(GEN x, GEN s) { return mulir(s,x); }
INLINE GEN
mulrs(GEN x, long s) { return mulsr(s,x); }

INLINE GEN
truedivii(GEN a,GEN b) { return truedvmdii(a,b,NULL); }
INLINE GEN
truedivis(GEN a, long b) { return truedvmdis(a,b,NULL); }
INLINE GEN
truedivsi(long a, GEN b) { return truedvmdsi(a,b,NULL); }
INLINE GEN
divii(GEN a, GEN b) { return dvmdii(a,b,NULL); }
INLINE GEN
remii(GEN a, GEN b) { return dvmdii(a,b,ONLY_REM); }

/* assume x > 0 */
INLINE long
expu(ulong x) { return (BITS_IN_LONG-1) - (long)bfffo(x); }

INLINE long
expi(GEN x)
{
  const long lx=lgefint(x);
  return lx==2? -(long)HIGHEXPOBIT: bit_accuracy(lx)-(long)bfffo(*int_MSW(x))-1;
}

INLINE GEN
mpshift(GEN x,long s) { return (typ(x)==t_INT)?shifti(x,s):shiftr(x,s); }

/* z2[imin..imax] := z1[imin..imax].f shifted left sh bits
 * (feeding f from the right). Assume sh > 0 */
INLINE void
shift_left2(GEN z2, GEN z1, long imin, long imax, ulong f, ulong sh, ulong m)
{
  GEN sb = z1 + imin, se = z1 + imax, te = z2 + imax;
  ulong l, k = f >> m;
  while (se > sb) {
    l     = *se--;
    *te-- = (l << sh) | k;
    k     = l >> m;
  }
  *te = (*se << sh) | k;
}
/* z2[imin..imax] := f.z1[imin..imax-1] shifted right sh bits
 * (feeding f from the left). Assume sh > 0 */
INLINE void
shift_right2(GEN z2, GEN z1, long imin, long imax, ulong f, ulong sh, ulong m)
{
  GEN sb = z1 + imin, se = z1 + imax, tb = z2 + imin;
  ulong k, l = *sb++;
  *tb++ = (l >> sh) | (f << m);
  while (sb < se) {
    k     = l << m;
    l     = *sb++;
    *tb++ = (l >> sh) | k;
  }
}
/* FIXME: adapt/use mpn_[lr]shift instead */
INLINE void
shift_left(GEN z2, GEN z1, long imin, long imax, ulong f,  ulong sh)
{ shift_left2(z2,z1,imin,imax,f,sh, BITS_IN_LONG - sh); }

INLINE void
shift_right(GEN z2, GEN z1, long imin, long imax, ulong f, ulong sh)
{ shift_right2(z2,z1,imin,imax,f,sh, BITS_IN_LONG - sh); }

/* Backward compatibility. Inefficient && unused */
extern ulong hiremainder;
INLINE ulong
shiftl(ulong x, ulong y)
{ hiremainder = x>>(BITS_IN_LONG-y); return (x<<y); }

INLINE ulong
shiftlr(ulong x, ulong y)
{ hiremainder = x<<(BITS_IN_LONG-y); return (x>>y); }
