/* $Id$ */

/* This file defines some "level 1" kernel functions                 */
/* These functions can be inline, with gcc                           */
/* If not gcc, they are defined externally with "level1.c"           */

/* level1.c includes this file and never needs to be changed         */
/* The following seven lines are necessary for level0.c and level1.c */
#ifdef LEVEL1
#  undef  INLINE
#  define INLINE
#endif
#ifdef LEVEL0
#  undef  INLINE
#endif

#ifndef INLINE
void   addsii(long x, GEN y, GEN z);
long   addssmod(long a, long b, long p);
void   addssz(long x, long y, GEN z);
void   affii(GEN x, GEN y);
void   affsi(long s, GEN x);
void   affsr(long s, GEN x);
GEN    cgetg(long x, long y);
GEN    cgeti(long x);
GEN    cgetr(long x);
int    cmpir(GEN x, GEN y);
int    cmpsr(long x, GEN y);
int    divise(GEN x, GEN y);
long   divisii(GEN x, long y, GEN z);
void   divisz(GEN x, long y, GEN z);
void   divrrz(GEN x, GEN y, GEN z);
void   divsiz(long x, GEN y, GEN z);
GEN    divss(long x, long y);
long   divssmod(long a, long b, long p);
void   divssz(long x, long y, GEN z);
void   dvmdiiz(GEN x, GEN y, GEN z, GEN t);
GEN    dvmdis(GEN x, long y, GEN *z);
void   dvmdisz(GEN x, long y, GEN z, GEN t);
GEN    dvmdsi(long x, GEN y, GEN *z);
void   dvmdsiz(long x, GEN y, GEN z, GEN t);
GEN    dvmdss(long x, long y, GEN *z);
void   dvmdssz(long x, long y, GEN z, GEN t);
ulong  evallg(ulong x);
ulong  evallgef(ulong x);
#ifndef __M68K__
long   expi(GEN x);
#endif
double gtodouble(GEN x);
GEN    icopy(GEN x);
GEN    icopy_av(GEN x, GEN y);
long   itos(GEN x);
GEN    modis(GEN x, long y);
GEN    mpabs(GEN x);
GEN    mpadd(GEN x, GEN y);
void   mpaff(GEN x, GEN y);
int    mpcmp(GEN x, GEN y);
GEN    mpcopy(GEN x);
GEN    mpdiv(GEN x, GEN y);
int    mpdivis(GEN x, GEN y, GEN z);
GEN    mpmul(GEN x, GEN y);
GEN    mpneg(GEN x);
GEN    mpsub(GEN x, GEN y);
void   mulsii(long x, GEN y, GEN z);
long   mulssmod(ulong a, ulong b, ulong c);
void   mulssz(long x, long y, GEN z);
GEN    new_chunk(long x);
void   resiiz(GEN x, GEN y, GEN z);
GEN    resis(GEN x, long y);
GEN    ressi(long x, GEN y);
GEN    shiftr(GEN x, long n);
long   smodis(GEN x, long y);
GEN    stoi(long x);
GEN    subii(GEN x, GEN y);
GEN    subir(GEN x, GEN y);
GEN    subri(GEN x, GEN y);
GEN    subrr(GEN x, GEN y);
GEN    subsi(long x, GEN y);
GEN    subsr(long x, GEN y);
long   subssmod(long a, long b, long p);
GEN    utoi(ulong x);
long   vali(GEN x);

#else /* defined(INLINE) */
INLINE ulong
evallg(ulong x)
{
  if (x & ~LGBITS) err(errlg);
  return m_evallg(x);
}

INLINE ulong
evallgef(ulong x)
{
  if (x & ~LGEFBITS) err(errlgef);
  return m_evallgef(x);
}

INLINE GEN
new_chunk(long x)
{
  const GEN z = ((GEN) avma) - x;
  if ((ulong)x > (ulong)((GEN)avma-(GEN)bot)) err(errpile);
#ifdef MEMSTEP
  checkmemory(z);
#endif
#ifdef _WIN32
  if (win32ctrlc) dowin32ctrlc();
#endif
  avma = (long)z; return z;
}

/* THE FOLLOWING ONES ARE IN mp.s */
#  ifndef __M68K__

INLINE GEN
cgetg(long x, long y)
{
  const GEN z = new_chunk(x);
  z[0] = evaltyp(y) | evallg(x);
  return z;
}

INLINE GEN
cgeti(long x)
{
  const GEN z = new_chunk(x);
  z[0] = evaltyp(t_INT) | evallg(x);
  return z;
}

INLINE GEN
cgetr(long x)
{
  const GEN z = new_chunk(x);
  z[0] = evaltyp(t_REAL) | evallg(x);
  return z;
}
#  endif /* __M68K__ */

/* cannot do memcpy because sometimes x and y overlap */
INLINE GEN
mpcopy(GEN x)
{
  register long lx = lg(x);
  const GEN y = new_chunk(lx);

  while (--lx >= 0) y[lx]=x[lx];
  return y;
}

INLINE GEN
icopy(GEN x)
{
  register long lx = lgefint(x);
  const GEN y = cgeti(lx);

  while (--lx > 0) y[lx]=x[lx];
  return y;
}

/* copy integer x as if we had avma = av */
INLINE GEN
icopy_av(GEN x, GEN y)
{
  register long lx = lgefint(x);

  y -= lx; while (--lx >= 0) y[lx]=x[lx];
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
  const long av=avma; divis(x,y); avma=av;
  if (!hiremainder) return 0;
  return (signe(x)>0) ? hiremainder: labs(y)+hiremainder;
}

INLINE GEN
utoi(ulong x)
{
  GEN y;

  if (!x) return gzero;
  y=cgeti(3); y[1] = evalsigne(1) | evallgefint(3); y[2] = x;
  return y;
}

#  ifndef __M68K__
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
  const long s=signe(x);
  long p1;

  if (!s) return 0;
  if (lgefint(x)>3) err(affer2);
  p1=x[2]; if (p1 < 0) err(affer2);
  return (s>0) ? p1 : -(long)p1;
}
#endif

INLINE GEN
stosmall(long x)
{
  if (labs(x) & SMALL_MASK) return stoi(x);
  return (GEN) (1 | (x<<1));
}

#  ifndef __M68K__

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
  if (!s) { x[1]=2; return; }
  if (lg(x)<3) err(affer1);
  if (s>0) { x[1] = evalsigne(1) | evallgefint(3); x[2] = s; }
  else { x[1] = evalsigne(-1) | evallgefint(3); x[2] = -s; }
}

INLINE void
affsr(long s, GEN x)
{
  long l;

  if (!s)
  {
    l = -bit_accuracy(lg(x));
    x[1]=evalexpo(l); x[2]=0; return;
  }
  if (s<0) { x[1] = evalsigne(-1); s = -s; }
  else x[1] = evalsigne(1);
  l=bfffo(s); x[1] |= evalexpo((BITS_IN_LONG-1)-l);
  x[2] = s<<l; for (l=3; l<lg(x); l++) x[l]=0;
}

INLINE void
mpaff(GEN x, GEN y)
{
  if (typ(x)==t_INT)
   { if (typ(y)==t_INT) affii(x,y); else affir(x,y); }
  else
   { if (typ(y)==t_INT) affri(x,y); else affrr(x,y); }
}

INLINE GEN
shiftr(GEN x, long n)
{
  const long e = evalexpo(expo(x)+n);
  const GEN y = rcopy(x);

  if (e & ~EXPOBITS) err(shier2);
  y[1] = (y[1]&~EXPOBITS) | e; return y;
}

INLINE int
cmpir(GEN x, GEN y)
{
  long av;
  GEN z;

  if (!signe(x)) return -signe(y);
  av=avma; z=cgetr(lg(y)); affir(x,z); avma=av;
  return cmprr(z,y); /* cmprr does no memory adjustment */
}

INLINE int
cmpsr(long x, GEN y)
{
  long av;
  GEN z;

  if (!x) return -signe(y);
  av=avma; z=cgetr(3); affsr(x,z); avma=av;
  return cmprr(z,y);
}	

INLINE void
addssz(long x, long y, GEN z)
{
  if (typ(z)==t_INT) gops2ssz(addss,x,y,z);
  else
  {
    const long av=avma;
    const GEN p1=cgetr(lg(z));

    affsr(x,p1); affrr(addrs(p1,y),z); avma=av;
  }
}

INLINE GEN
subii(GEN x, GEN y)
{
  const long s=signe(y);
  GEN z;

  if (x==y) return gzero;
  setsigne(y,-s); z=addii(x,y);
  setsigne(y, s); return z;
}

INLINE GEN
subrr(GEN x, GEN y)
{
  const long s=signe(y);
  GEN z;

  if (x==y) return realzero(lg(x)+2);
  setsigne(y,-s); z=addrr(x,y);
  setsigne(y, s); return z;
}

INLINE GEN
subir(GEN x, GEN y)
{
  const long s=signe(y);
  GEN z;

  setsigne(y,-s); z=addir(x,y);
  setsigne(y, s); return z;
}

INLINE GEN
subri(GEN x, GEN y)
{
  const long s=signe(y);
  GEN z;

  setsigne(y,-s); z=addir(y,x);
  setsigne(y, s); return z;
}

INLINE GEN
subsi(long x, GEN y)
{
  const long s=signe(y);
  GEN z;

  setsigne(y,-s); z=addsi(x,y);
  setsigne(y, s); return z;
}

INLINE GEN
subsr(long x, GEN y)
{
  const long s=signe(y);
  GEN z;

  setsigne(y,-s); z=addsr(x,y);
  setsigne(y, s); return z;
}

INLINE void
mulssz(long x, long y, GEN z)
{
  if (typ(z)==t_INT) gops2ssz(mulss,x,y,z);
  else
  {
    const long av=avma;
    const GEN p1=cgetr(lg(z));

    affsr(x,p1); mpaff(mulsr(y,p1),z); avma=av;
  }
}

INLINE void
mulsii(long x, GEN y, GEN z)
{
  const long av=avma;
  affii(mulsi(x,y),z); avma=av;
}

INLINE void
addsii(long x, GEN y, GEN z)
{
  const long av=avma;
  affii(addsi(x,y),z); avma=av;
}

INLINE long
divisii(GEN x, long y, GEN z)
{
  const long av=avma;
  affii(divis(x,y),z); avma=av; return hiremainder;
}

INLINE long
vali(GEN x)
{
  long lx,i;

  if (!signe(x)) return -1;
  i = lx = lgefint(x)-1; while (!x[i]) i--;
  return ((lx-i)<<TWOPOTBITS_IN_LONG) + vals(x[i]);
}

INLINE GEN
divss(long x, long y)
{
  long p1;
  LOCAL_HIREMAINDER;

  if (!y) err(diver1);
  hiremainder=0; p1 = divll((ulong)labs(x),(ulong)labs(y));
  if (x<0) { hiremainder = -((long)hiremainder); p1 = -p1; }
  if (y<0) p1 = -p1;
  SAVE_HIREMAINDER; return stoi(p1);
}

INLINE GEN
dvmdss(long x, long y, GEN *z)
{
  const GEN p1=divss(x,y);
  *z = stoi(hiremainder); return p1;
}

INLINE GEN
dvmdsi(long x, GEN y, GEN *z)
{
  const GEN p1=divsi(x,y);
  *z = stoi(hiremainder); return p1;
}

INLINE GEN
dvmdis(GEN x, long y, GEN *z)
{
  const GEN p1=divis(x,y);
  *z=stoi(hiremainder); return p1;
}

INLINE void
dvmdssz(long x, long y, GEN z, GEN t)
{
  const long av=avma;
  const GEN p1=divss(x,y);

  affsi(hiremainder,t); mpaff(p1,z); avma=av;
}

INLINE void
dvmdsiz(long x, GEN y, GEN z, GEN t)
{
  const long av=avma;
  const GEN p1=divsi(x,y);

  affsi(hiremainder,t); mpaff(p1,z); avma=av;
}

INLINE void
dvmdisz(GEN x, long y, GEN z, GEN t)
{
  const long av=avma;
  const GEN p1=divis(x,y);

  affsi(hiremainder,t); mpaff(p1,z); avma=av;
}

INLINE void
dvmdiiz(GEN x, GEN y, GEN z, GEN t)
{
  const long av=avma;
  GEN p;

  mpaff(dvmdii(x,y,&p),z); mpaff(p,t); avma=av;
}

INLINE GEN
modis(GEN x, long y)
{
  return stoi(smodis(x,y));
}

INLINE GEN
ressi(long x, GEN y)
{
  const long av=avma;
  divsi(x,y); avma=av; return stoi(hiremainder);
}

INLINE GEN
resis(GEN x, long y)
{
  const long av=avma;
  divis(x,y); avma=av; return stoi(hiremainder);
}

INLINE void
divisz(GEN x, long y, GEN z)
{
  if (typ(z)==t_INT) gops2gsz(divis,x,y,z);
  else
  {
    const long av=avma;
    const GEN p1=cgetr(lg(z));

    affir(x,p1); affrr(divrs(p1,y),z); avma=av;
  }
}

INLINE void
divsiz(long x, GEN y, GEN z)
{
  const long av=avma;

  if (typ(z)==t_INT) gaffect(divsi(x,y),z);
  else
  {
    const long lz=lg(z);
    const GEN p1=cgetr(lz), p2=cgetr(lz);

    affsr(x,p1); affir(y,p2);
    affrr(divrr(p1,p2),z);
  }
  avma=av;
}

INLINE void
divssz(long x, long y, GEN z)
{
  const long av=avma;

  if (typ(z)==t_INT) gaffect(divss(x,y),z);
  else
  {
    const GEN p1=cgetr(lg(z));

    affsr(x,p1); affrr(divrs(p1,y),z);
  }
  avma=av;
}

INLINE void
divrrz(GEN x, GEN y, GEN z)
{
  const long av=avma;
  mpaff(divrr(x,y),z); avma=av;
}

INLINE void
resiiz(GEN x, GEN y, GEN z)
{
  const long av=avma;
  affii(resii(x,y),z); avma=av;
}

INLINE int
divise(GEN x, GEN y)
{
  const long av=avma;
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
  const long av=avma;
  GEN p2;
  const GEN p1=dvmdii(x,y,&p2);

  if (signe(p2)) { avma=av; return 0; }
  affii(p1,z); avma=av; return 1;
}

/* THE FOLLOWING ONES ARE NOT IN mp.s */
#  endif /* !defined(__M68K__) */

INLINE double
gtodouble(GEN x)
{
  static long reel4[4]={ evaltyp(t_REAL) | m_evallg(4),0,0,0 };

  if (typ(x)==t_REAL) return rtodbl(x);
  gaffect(x,(GEN)reel4); return rtodbl((GEN)reel4);
}

INLINE long
addssmod(long a, long b, long p)
{
  ulong res = a + b;
  return (res >= (ulong)p) ? res - p : res;
}

INLINE long
subssmod(long a, long b, long p)
{
  long res = a - b;
  return (res >= 0) ? res : res + p;
}

INLINE long
mulssmod(ulong a, ulong b, ulong c)
{
  LOCAL_HIREMAINDER;
  {
    register ulong x = mulll(a,b);

    /* alter the doubleword by a multiple of c: */
    if (hiremainder>=c) hiremainder %= c;
    (void)divll(x,c);
  }
  return hiremainder;
}

INLINE long
divssmod(long a, long b, long p)
{
  long v1 = 0, v2 = 1, v3, r, oldp = p;

  while (b > 1)
  {
    v3 = v1 - (p / b) * v2; v1 = v2; v2 = v3;
    r = p % b; p = b; b = r;
  }

  if (v2 < 0) v2 += oldp;
  return mulssmod(a, v2, oldp);
}

INLINE long
expi(GEN x)
{
  const long lx=lgefint(x);
  return lx==2? -HIGHEXPOBIT: bit_accuracy(lx)-bfffo(x[2])-1;
}

#endif
