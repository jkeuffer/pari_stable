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
 * These functions can be inline; if not they are defined externally in
 * level1.c, which includes this file and never needs to be changed
 * The following lines are necessary for level0.c and level1.c */
#ifdef LEVEL1
#  undef  INLINE_IS_STATIC
#  undef  INLINE
#  define INLINE
#endif
#ifdef LEVEL0
#  undef  INLINE_IS_STATIC
#  undef  INLINE
#endif

#if !defined(INLINE) || defined(INLINE_IS_STATIC)
GEN    addii(GEN x, GEN y);
GEN    addir(GEN x, GEN y);
GEN    addrr(GEN x, GEN y);
GEN    addsi(long x, GEN y);
void   addsii(long x, GEN y, GEN z);
ulong  adduumod(ulong a, ulong b, ulong p);
void   addssz(long x, long y, GEN z);
void   affii(GEN x, GEN y);
void   affsi(long s, GEN x);
void   affui(long s, GEN x);
void   affsr(long s, GEN x);
GEN    cgetg(long x, long y);
GEN    cgetg_copy(long lx, GEN x);
GEN    cgeti(long x);
GEN    cgetr(long x);
int    cmpir(GEN x, GEN y);
int    cmpsr(long x, GEN y);
int    divise(GEN x, GEN y);
long   divisii(GEN x, long y, GEN z);
void   divisz(GEN x, long y, GEN z);
void   divrrz(GEN x, GEN y, GEN z);
void   divsiz(long x, GEN y, GEN z);
GEN    divsi_rem(long x, GEN y, long *rem);
GEN    divss_rem(long x, long y, long *rem);
GEN    divss(long x, long y);
ulong  divuumod(ulong a, ulong b, ulong p);
void   divssz(long x, long y, GEN z);
void   dvmdiiz(GEN x, GEN y, GEN z, GEN t);
GEN    dvmdis(GEN x, long y, GEN *z);
void   dvmdisz(GEN x, long y, GEN z, GEN t);
GEN    dvmdsi(long x, GEN y, GEN *z);
void   dvmdsiz(long x, GEN y, GEN z, GEN t);
GEN    dvmdss(long x, long y, GEN *z);
void   dvmdssz(long x, long y, GEN z, GEN t);
long   evallg(long x);
long   evalvalp(long x);
long   evalexpo(long x);
long   expi(GEN x);
double gtodouble(GEN x);
GEN    icopy(GEN x);
GEN    icopy_av(GEN x, GEN y);
GEN    itor(GEN x, long prec);
long   itos(GEN x);
long   itos_or_0(GEN x);
ulong  itou_or_0(GEN x);
ulong  itou(GEN x);
GEN    modis(GEN x, long y);
GEN    modsi(long x, GEN y);
GEN    modss(long x, long y);
GEN    mpabs(GEN x);
GEN    mpadd(GEN x, GEN y);
void   mpaff(GEN x, GEN y);
int    mpcmp(GEN x, GEN y);
GEN    mpcopy(GEN x);
GEN    mpdiv(GEN x, GEN y);
int    mpdivis(GEN x, GEN y, GEN z);
int    mpdivisis(GEN x, long y, GEN z);
GEN    mpmul(GEN x, GEN y);
GEN    mpneg(GEN x);
GEN    mpsub(GEN x, GEN y);
void   mulsii(long x, GEN y, GEN z);
ulong  muluumod(ulong a, ulong b, ulong c);
void   mulssz(long x, long y, GEN z);
GEN    new_chunk(size_t x);
long   random_bits(long k);
GEN    realun(long prec);
GEN    realzero(long prec);
GEN    realzero_bit(long bitprec);
void   resiiz(GEN x, GEN y, GEN z);
GEN    resis(GEN x, long y);
GEN    ressi(long x, GEN y);
GEN    resss(long x, long y);
GEN    rtor(GEN x, long prec);
long   sdivsi_rem(long x, GEN y, long *rem);
long   sdivss_rem(long x, long y, long *rem);
GEN    shiftr(GEN x, long n);
long   smodis(GEN x, long y);
long   smodss(long x, long y);
GEN    stor(long x, long prec);
GEN    stoi(long x);
GEN    subii(GEN x, GEN y);
GEN    subir(GEN x, GEN y);
GEN    subri(GEN x, GEN y);
GEN    subrr(GEN x, GEN y);
GEN    subsi(long x, GEN y);
ulong  subuumod(ulong a, ulong b, ulong p);
ulong  umodui(ulong x, GEN y);
ulong  umuluu(ulong x, ulong y, ulong *rem);
GEN    utoi(ulong x);
long   vali(GEN x);

#else

INLINE long
evallg(long x)
{
  if (x & ~LGBITS) err(errlg);
  return _evallg(x);
}

INLINE long
evalvalp(long x)
{
  const long v = _evalvalp(x);
  if (v & ~VALPBITS) err(errvalp);
  return v;
}

INLINE long
evalexpo(long x)
{
  const long v = _evalexpo(x);
  if (v & ~EXPOBITS) err(errexpo);
  return v;
}

INLINE GEN
new_chunk(size_t x) /* x is a number of bytes */
{
  const GEN z = ((GEN) avma) - x;
  if (x > ((avma-bot)>>TWOPOTBYTES_IN_LONG)) err(errpile);
#ifdef _WIN32
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
cgetr(long x)
{
  const GEN z = new_chunk((size_t)x);
  z[0] = evaltyp(t_REAL) | evallg(x);
  return z;
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
mpneg(GEN x)
{
  const GEN y=mpcopy(x);
  setsigne(y,-signe(x)); return y;
}

INLINE GEN
mpabs(GEN x)
{
  const GEN y=mpcopy(x);
  if (signe(x)<0) setsigne(y,1);
  return y;
}

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

INLINE GEN
utoi(ulong x)
{
  GEN y;

  if (!x) return gzero;
  y=cgeti(3); y[1] = evalsigne(1) | evallgefint(3); y[2] = x;
  return y;
}

INLINE GEN stoi(long);
INLINE GEN realzero(long);

INLINE GEN
stosmall(long x)
{
  if (labs(x) & SMALL_MASK) return stoi(x);
  return (GEN) (1 | (x<<1));
}

INLINE GEN
stoi(long x)
{
  GEN y;

  if (!x) return gzero;
  y=cgeti(3);
  if (x>0) { y[1] = evalsigne(1) | evallgefint(3); y[2] = x; }
  else { y[1] = evalsigne(-1) | evallgefint(3); y[2] = -x; }
  return y;
}

INLINE long
itos(GEN x)
{
  const long s = signe(x);
  long u;

  if (!s) return 0;
  u = (long)x[2]; if (lgefint(x) > 3 || u < 0) err(affer2);
  return (s>0) ? u : -u;
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
resss(long x, long y) { return stoi(x % y); }

INLINE void
affii(GEN x, GEN y)
{
  long lx;

  if (x==y) return;
  lx=lgefint(x); if (lg(y)<lx) err(affer3);
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
    y[1] = evalsigne(-1) | evalexpo((BITS_IN_LONG-1)-sh);
  }
  else
  {
    sh = bfffo(x);
    y[1] = evalsigne(1) | evalexpo((BITS_IN_LONG-1)-sh);
  }
  y[2] = x<<sh; for (i=3; i<ly; i++) y[i]=0;
}

INLINE void
mpaff(GEN x, GEN y)
{
  if (typ(x)==t_INT)
   { if (typ(y)==t_INT) affii(x,y); else affir(x,y); }
  else
   { if (typ(y)==t_INT) err(operf,"",x,y); else affrr(x,y); }
}

INLINE GEN
realzero_bit(long bitprec) { GEN x=cgetr(2); x[1]=evalexpo(bitprec); return x; }

INLINE GEN
realzero(long prec) { return realzero_bit(-bit_accuracy(prec)); }

INLINE GEN
realun(long prec) { GEN x=cgetr(prec); affsr(1,x); return x; }

INLINE GEN
stor(long s, long prec) { GEN z = cgetr(prec); affsr(s,z); return z; }

INLINE GEN
itor(GEN x, long prec) { GEN z = cgetr(prec); affir(x,z); return z; }

INLINE GEN
rtor(GEN x, long prec) { GEN z = cgetr(prec); affrr(x,z); return z; }

INLINE GEN
shiftr(GEN x, long n)
{
  const long e = evalexpo(expo(x)+n);
  const GEN y = rcopy(x);

  if (e & ~EXPOBITS) err(talker,"overflow in real shift");
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
cmpsr(long x, GEN y)
{
  pari_sp av;
  GEN z;

  if (!x) return -signe(y);
  av=avma; z = stor(x, 3); avma=av;
  return cmprr(z,y);
}	

INLINE void
addssz(long x, long y, GEN z)
{
  if (typ(z)==t_INT) gops2ssz(addss,x,y,z);
  else
  {
    const pari_sp av=avma;
    affir(addss(x, y), z); avma=av;
  }
}

INLINE GEN
addii(GEN x, GEN y)
{
  return addii_sign(x, signe(x), y, signe(y));
}

INLINE GEN
subii(GEN x, GEN y)
{
  if (x==y) return gzero;
  return addii_sign(x, signe(x), y, -signe(y));
}

INLINE GEN
addrr(GEN x, GEN y)
{
  return addrr_sign(x, signe(x), y, signe(y));
}

INLINE GEN
subrr(GEN x, GEN y)
{
  return addrr_sign(x, signe(x), y, -signe(y));
}

INLINE GEN
addir(GEN x, GEN y)
{
  return addir_sign(x, signe(x), y, signe(y));
}

INLINE GEN
subir(GEN x, GEN y)
{
  return addir_sign(x, signe(x), y, -signe(y));
}

INLINE GEN
subri(GEN x, GEN y)
{
  return addir_sign(y, -signe(y), x, signe(x));
}

INLINE GEN
addsi(long x, GEN y)
{
  return addsi_sign(x, y, signe(y));
}

INLINE GEN
subsi(long x, GEN y)
{
  return addsi_sign(x, y, -signe(y));
}

INLINE void
mulssz(long x, long y, GEN z)
{
  if (typ(z)==t_INT) gops2ssz(mulss,x,y,z);
  else
  {
    const pari_sp av=avma;
    affir(mulss(x,y), z); avma=av;
  }
}

INLINE ulong
umuluu(ulong x, ulong y, ulong *rem)
{
  LOCAL_HIREMAINDER;
  x=mulll(x,y); *rem=hiremainder; return x;
}


INLINE void
mulsii(long x, GEN y, GEN z)
{
  const pari_sp av=avma;
  affii(mulsi(x,y),z); avma=av;
}

INLINE void
addsii(long x, GEN y, GEN z)
{
  const pari_sp av=avma;
  affii(addsi(x,y),z); avma=av;
}

INLINE long
divisii(GEN x, long y, GEN z)
{
  long rem;
  const pari_sp av=avma; affii(divis_rem(x,y, &rem),z); avma=av;
  return rem;
}

INLINE long
vali(GEN x)
{
  long i;
  GEN xp;

  if (!signe(x)) return -1;
  xp=int_LSW(x); 
  for (i=0; !*xp; i++) xp=int_nextW(xp);
  return (i<<TWOPOTBITS_IN_LONG) + vals(*xp);
}

INLINE GEN
divss(long x, long y) { return stoi(x / y); }

INLINE long
sdivss_rem(long x, long y, long *rem)
{
  long q;
  LOCAL_HIREMAINDER;
  if (!y) err(gdiver);
  hiremainder = 0; q = divll((ulong)labs(x),(ulong)labs(y));
  if (x < 0) { hiremainder = -((long)hiremainder); q = -q; }
  if (y < 0) q = -q;
  return q;
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
sdivsi_rem(long x, GEN y, long *rem)
{
  long q, s = signe(y);
  LOCAL_HIREMAINDER;

  if (!s) err(gdiver);
  if (!x || lgefint(y)>3 || ((long)y[2])<0) { *rem = x; return 0; }
  hiremainder=0; q = (long)divll(labs(x), (ulong)y[2]);
  if (x < 0) { hiremainder = -((long)hiremainder); q = -q; }
  if (s < 0) q = -q;
  *rem = hiremainder; return q;
}

INLINE GEN
modsi(long x, GEN y) {
  long r;
  (void)sdivsi_rem(x, y, &r);
  return (r >= 0)? stoi(r): addsi_sign(x, y, 1);
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
  const pari_sp av=avma; mpaff(divss_rem(x,y, &rem), z); avma=av;
  affsi(rem,t);
}

INLINE void
dvmdsiz(long x, GEN y, GEN z, GEN t)
{
  long rem;
  const pari_sp av = avma; mpaff(divsi_rem(x,y, &rem), z); avma = av;
  affsi(rem,t);
}

INLINE void
dvmdisz(GEN x, long y, GEN z, GEN t)
{
  long rem;
  const pari_sp av=avma; mpaff(divis_rem(x,y, &rem),z); avma=av;
  affsi(rem,t);
}

INLINE void
dvmdiiz(GEN x, GEN y, GEN z, GEN t)
{
  const pari_sp av=avma;
  GEN p;

  mpaff(dvmdii(x,y,&p),z); mpaff(p,t); avma=av;
}

INLINE GEN
modis(GEN x, long y)
{
  return stoi(smodis(x,y));
}

INLINE ulong
umodui(ulong x, GEN y)
{
  LOCAL_HIREMAINDER;
  if (!signe(y)) err(gdiver);
  if (!x || lgefint(y) > 3) return x;
  hiremainder = 0; (void)divll(x, y[2]); return hiremainder;
}

INLINE GEN
ressi(long x, GEN y)
{
  long rem;
  const pari_sp av=avma; (void)divsi_rem(x,y, &rem); avma=av;
  return stoi(rem);
}

INLINE GEN
resis(GEN x, long y)
{
  long rem;
  const pari_sp av=avma; (void)divis_rem(x,y, &rem); avma=av;
  return stoi(rem);
}

INLINE void
divisz(GEN x, long y, GEN z)
{
  if (typ(z)==t_INT) gops2gsz(divis,x,y,z);
  else
  {
    const pari_sp av=avma;
    affrr(divrs(itor(x,lg(z)), y),z); avma=av;
  }
}

INLINE void
divsiz(long x, GEN y, GEN z)
{
  const pari_sp av=avma;

  if (typ(z)==t_INT) gaffect(divsi(x,y),z);
  else
    affrr(divsr(x, itor(y,lg(z))),z);
  avma=av;
}

INLINE void
divssz(long x, long y, GEN z)
{
  const pari_sp av = avma;

  if (typ(z)==t_INT) affsi(x/y, z);
  else
    affrr(divrs(stor(x, lg(z)), y), z);
  avma = av;
}

INLINE void
divrrz(GEN x, GEN y, GEN z)
{
  const pari_sp av=avma;
  mpaff(divrr(x,y),z); avma=av;
}

INLINE void
resiiz(GEN x, GEN y, GEN z)
{
  const pari_sp av=avma;
  affii(resii(x,y),z); avma=av;
}

INLINE int
divise(GEN x, GEN y)
{
  const pari_sp av=avma;
  const GEN p1=resii(x,y);
  avma=av; return p1 == gzero;
}

INLINE int
mpcmp(GEN x, GEN y)
{
  if (typ(x)==t_INT)
    return (typ(y)==t_INT) ? cmpii(x,y) : cmpir(x,y);
  return (typ(y)==t_INT) ? -cmpir(y,x) : cmprr(x,y);
}

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
mpdivis(GEN x, GEN y, GEN z)
{
  const pari_sp av=avma;
  GEN p2;
  const GEN p1=dvmdii(x,y,&p2);

  if (signe(p2)) { avma=av; return 0; }
  affii(p1,z); avma=av; return 1;
}

/* assume 0 <= k < 32. Return random 0 <= x < (1<<k) */
INLINE long
random_bits(long k) { return pari_rand31() >> (31 - k); }

INLINE ulong
itou(GEN x)
{
  const long s = signe(x);

  if (!s) return 0;
  if (lgefint(x) > 3) err(affer2);
  return x[2];
}

INLINE void
affui(ulong u, GEN x)
{
  if (!u) x[1] = evalsigne(0) | evallgefint(2);
  else  { x[1] = evalsigne(1) | evallgefint(3); x[2] = u; }
}

INLINE int
mpdivisis(GEN x, long y, GEN z)
{
  const pari_sp av = avma;
  long rem;
  GEN p1 = divis_rem(x,y, &rem);
  if (rem) { avma = av; return 0; }
  affii(p1,z); avma = av; return 1;
}

INLINE double
gtodouble(GEN x)
{
  static long reel4[4]={ evaltyp(t_REAL) | _evallg(4),0,0,0 };

  if (typ(x)==t_REAL) return rtodbl(x);
  gaffect(x,(GEN)reel4); return rtodbl((GEN)reel4);
}

/* same as adduumod, assume p <= 2^(BIL - 1), so that overflow can't occur */
INLINE ulong
adduumod_noofl(ulong a, ulong b, ulong p)
{
  ulong res = a + b;
  return (res >= p) ? res - p : res;
}
INLINE ulong
adduumod(ulong a, ulong b, ulong p)
{
  ulong res = a + b;
  return (res >= p || res < a) ? res - p : res;
}

INLINE ulong
subuumod(ulong a, ulong b, ulong p)
{
  ulong res = a - b;
  return (res > a) ? res + p: res;
}

INLINE ulong
muluumod(ulong a, ulong b, ulong c)
{
  LOCAL_HIREMAINDER;
  {
    register ulong x = mulll(a,b);
    (void)divll(x,c);
  }
  return hiremainder;
}

INLINE ulong
divuumod(ulong a, ulong b, ulong p)
{
  return muluumod(a, invumod(b, p), p);
}

INLINE long
expi(GEN x)
{
  const long lx=lgefint(x);
  return lx==2? -(long)HIGHEXPOBIT: bit_accuracy(lx)-(long)bfffo(*int_MSW(x))-1;
}
#endif
