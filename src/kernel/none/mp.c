/***********************************************************************/
/**								      **/
/**		         MULTIPRECISION KERNEL           	      **/
/**                                                                   **/
/***********************************************************************/
/* $Id$ */
/* most of the routines in this file are commented out in 68k */
/* version (#ifdef __M68K__) since they are defined in mp.s   */
#include "pari.h"

/* z2 := z1[imin..imax].f shifted left sh bits (feeding f from the right) */
#define shift_left2(z2,z1,imin,imax,f, sh,m) {\
  register ulong _i,_l,_k = ((ulong)f)>>m;\
  for (_i=imax; _i>imin; _i--) {\
    _l = z1[_i];\
    z2[_i] = (_l<<(ulong)sh) | _k;\
    _k = _l>>(ulong)m;\
  }\
  z2[imin]=(z1[imin]<<(ulong)sh) | _k;\
}
#define shift_left(z2,z1,imin,imax,f, sh) {\
  register const ulong _m = BITS_IN_LONG - sh;\
  shift_left2((z2),(z1),(imin),(imax),(f),(sh),(_m));\
}

/* z2 := f.z1[imin..imax-1] shifted right sh bits (feeding f from the left) */
#define shift_right2(z2,z1,imin,imax,f, sh,m) {\
  register ulong _i,_k,_l = z1[2];\
  z2[imin] = (_l>>(ulong)sh) | ((ulong)f<<(ulong)m);\
  for (_i=imin+1; _i<imax; _i++) {\
    _k = _l<<(ulong)m; _l = z1[_i];\
    z2[_i] = (_l>>(ulong)sh) | _k;\
  }\
}
#define shift_right(z2,z1,imin,imax,f, sh) {\
  register const ulong _m = BITS_IN_LONG - sh;\
  shift_right2((z2),(z1),(imin),(imax),(f),(sh),(_m));\
}

#ifdef INLINE
INLINE
#endif
GEN
addsispec(long s, GEN x, long nx)
{
  GEN xd, zd = (GEN)avma;
  long lz;
  LOCAL_OVERFLOW;

  lz = nx+3; (void)new_chunk(lz);
  xd = x + nx;
  *--zd = addll(*--xd, s);
  if (overflow)
    for(;;)
    {
      if (xd == x) { *--zd = 1; break; } /* enlarge z */
      *--zd = ((ulong)*--xd) + 1;
      if (*zd) { lz--; break; }
    }
  else lz--;
  while (xd > x) *--zd = *--xd;
  *--zd = evalsigne(1) | evallgefint(lz);
  *--zd = evaltyp(t_INT) | evallg(lz);
  avma=(long)zd; return zd;
}

#define swapspec(x,y, nx,ny) {long _a=nx;GEN _z=x; nx=ny; ny=_a; x=y; y=_z;}

#ifdef INLINE
INLINE
#endif
GEN
addiispec(GEN x, GEN y, long nx, long ny)
{
  GEN xd,yd,zd;
  long lz;
  LOCAL_OVERFLOW;

  if (nx < ny) swapspec(x,y, nx,ny);
  if (ny == 1) return addsispec(*y,x,nx);
  zd = (GEN)avma;
  lz = nx+3; (void)new_chunk(lz);
  xd = x + nx;
  yd = y + ny;
  *--zd = addll(*--xd, *--yd);
  while (yd > y) *--zd = addllx(*--xd, *--yd);
  if (overflow)
    for(;;)
    {
      if (xd == x) { *--zd = 1; break; } /* enlarge z */
      *--zd = ((ulong)*--xd) + 1;
      if (*zd) { lz--; break; }
    }
  else lz--;
  while (xd > x) *--zd = *--xd;
  *--zd = evalsigne(1) | evallgefint(lz);
  *--zd = evaltyp(t_INT) | evallg(lz);
  avma=(long)zd; return zd;
}

/* assume x >= y */
#ifdef INLINE
INLINE
#endif
GEN
subisspec(GEN x, long s, long nx)
{
  GEN xd, zd = (GEN)avma;
  long lz;
  LOCAL_OVERFLOW;

  lz = nx+2; (void)new_chunk(lz);
  xd = x + nx;
  *--zd = subll(*--xd, s);
  if (overflow)
    for(;;)
    {
      *--zd = ((ulong)*--xd) - 1;
      if (*xd) break;
    }
  if (xd == x)
    while (*zd == 0) { zd++; lz--; } /* shorten z */
  else
    do  *--zd = *--xd; while (xd > x);
  *--zd = evalsigne(1) | evallgefint(lz);
  *--zd = evaltyp(t_INT) | evallg(lz);
  avma=(long)zd; return zd;
}

/* assume x >= y */
#ifdef INLINE
INLINE
#endif
GEN
subiispec(GEN x, GEN y, long nx, long ny)
{
  GEN xd,yd,zd;
  long lz;
  LOCAL_OVERFLOW;

  if (ny==1) return subisspec(x,*y,nx);
  zd = (GEN)avma;
  lz = nx+2; (void)new_chunk(lz);
  xd = x + nx;
  yd = y + ny;
  *--zd = subll(*--xd, *--yd);
  while (yd > y) *--zd = subllx(*--xd, *--yd);
  if (overflow)
    for(;;)
    {
      *--zd = ((ulong)*--xd) - 1;
      if (*xd) break;
    }
  if (xd == x)
    while (*zd == 0) { zd++; lz--; } /* shorten z */
  else
    do  *--zd = *--xd; while (xd > x);
  *--zd = evalsigne(1) | evallgefint(lz);
  *--zd = evaltyp(t_INT) | evallg(lz);
  avma=(long)zd; return zd;
}

#ifndef __M68K__

/* prototype of positive small ints */
static long pos_s[] = {
  evaltyp(t_INT) | m_evallg(3), evalsigne(1) | evallgefint(3), 0 };

/* prototype of negative small ints */
static long neg_s[] = {
  evaltyp(t_INT) | m_evallg(3), evalsigne(-1) | evallgefint(3), 0 };

void
affir(GEN x, GEN y)
{
  const long s=signe(x),ly=lg(y);
  long lx,sh,i;

  if (!s)
  {
    y[1] = evalexpo(-bit_accuracy(ly));
    y[2] = 0; return;
  }

  lx=lgefint(x); sh=bfffo(x[2]);
  y[1] = evalsigne(s) | evalexpo(bit_accuracy(lx)-sh-1);
  if (sh)
  {
    if (lx>ly)
    { shift_left(y,x,2,ly-1, x[ly],sh); }
    else
    {
      for (i=lx; i<ly; i++) y[i]=0;
      shift_left(y,x,2,lx-1, 0,sh);
    }
    return;
  }

  if (lx>=ly)
    for (i=2; i<ly; i++) y[i]=x[i];
  else
  {
    for (i=2; i<lx; i++) y[i]=x[i];
    for (   ; i<ly; i++) y[i]=0;
  }
}

void
affrr(GEN x, GEN y)
{
  long lx,ly,i;

  y[1] = x[1]; if (!signe(x)) { y[2]=0; return; }

  lx=lg(x); ly=lg(y);
  if (lx>=ly)
    for (i=2; i<ly; i++) y[i]=x[i];
  else
  {
    for (i=2; i<lx; i++) y[i]=x[i];
    for (   ; i<ly; i++) y[i]=0;
  }
}

GEN
shifti(GEN x, long n)
{
  const long s=signe(x);
  long lx,ly,i,m;
  GEN y;

  if (!s) return gzero;
  if (!n) return icopy(x);
  lx = lgefint(x);
  if (n > 0)
  {
    GEN z = (GEN)avma;
    long d = n>>TWOPOTBITS_IN_LONG;

    ly = lx+d; y = new_chunk(ly);
    for ( ; d; d--) *--z = 0;
    m = n & (BITS_IN_LONG-1);
    if (!m) for (i=2; i<lx; i++) y[i]=x[i];
    else
    {
      register const ulong sh = BITS_IN_LONG - m;
      shift_left2(y,x, 2,lx-1, 0,m,sh);
      i = ((ulong)x[2]) >> sh;
      if (i) { ly++; y = new_chunk(1); y[2] = i; }
    }
  }
  else
  {
    n = -n;
    ly = lx - (n>>TWOPOTBITS_IN_LONG);
    if (ly<3) return gzero;
    y = new_chunk(ly);
    m = n & (BITS_IN_LONG-1);
    if (!m) for (i=2; i<ly; i++) y[i]=x[i];
    else
    {
      shift_right(y,x, 2,ly, 0,m);
      if (y[2] == 0)
      {
        if (ly==3) { avma = (long)(y+3); return gzero; }
        ly--; avma = (long)(++y);
      }
    }
  }
  y[1] = evalsigne(s)|evallgefint(ly);
  y[0] = evaltyp(t_INT)|evallg(ly); return y;
}

GEN
mptrunc(GEN x)
{
  long d,e,i,s,m;
  GEN y;

  if (typ(x)==t_INT) return icopy(x);
  if ((s=signe(x)) == 0 || (e=expo(x)) < 0) return gzero;
  d = (e>>TWOPOTBITS_IN_LONG) + 3;
  m = e & (BITS_IN_LONG-1);
  if (d > lg(x)) err(truer2);

  y=cgeti(d); y[1] = evalsigne(s) | evallgefint(d);
  if (++m == BITS_IN_LONG)
    for (i=2; i<d; i++) y[i]=x[i];
  else
  {
    const register ulong sh = BITS_IN_LONG - m;
    shift_right2(y,x, 2,d,0, sh,m);
  }
  return y;
}

/* integral part */
GEN
mpent(GEN x)
{
  long d,e,i,lx,m;
  GEN y;

  if (typ(x)==t_INT) return icopy(x);
  if (signe(x) >= 0) return mptrunc(x);
  if ((e=expo(x)) < 0) return stoi(-1);
  d = (e>>TWOPOTBITS_IN_LONG) + 3;
  m = e & (BITS_IN_LONG-1);
  lx=lg(x); if (d>lx) err(truer2);
  y = new_chunk(d);
  if (++m == BITS_IN_LONG)
  {
    for (i=2; i<d; i++) y[i]=x[i];
    i=d; while (i<lx && !x[i]) i++;
    if (i==lx) goto END;
  }
  else
  {
    const register ulong sh = BITS_IN_LONG - m;
    shift_right2(y,x, 2,d,0, sh,m);
    if (x[d-1]<<m == 0)
    {
      i=d; while (i<lx && !x[i]) i++;
      if (i==lx) goto END;
    }
  }
  /* set y:=y+1 */
  for (i=d-1; i>=2; i--) { y[i]++; if (y[i]) goto END; }
  y=new_chunk(1); y[2]=1; d++;
END:
  y[1] = evalsigne(-1) | evallgefint(d);
  y[0] = evaltyp(t_INT) | evallg(d); return y;
}

int
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

int
cmpii(GEN x, GEN y)
{
  const long sx = signe(x), sy = signe(y);
  long lx,ly,i;

  if (sx<sy) return -1;
  if (sx>sy) return 1;
  if (!sx) return 0;

  lx=lgefint(x); ly=lgefint(y);
  if (lx>ly) return sx;
  if (lx<ly) return -sx;
  i=2; while (i<lx && x[i]==y[i]) i++;
  if (i==lx) return 0;
  return ((ulong)x[i] > (ulong)y[i]) ? sx : -sx;
}

int
cmprr(GEN x, GEN y)
{
  const long sx = signe(x), sy = signe(y);
  long ex,ey,lx,ly,lz,i;

  if (sx<sy) return -1;
  if (sx>sy) return 1;
  if (!sx) return 0;

  ex=expo(x); ey=expo(y);
  if (ex>ey) return sx;
  if (ex<ey) return -sx;

  lx=lg(x); ly=lg(y); lz = (lx<ly)?lx:ly;
  i=2; while (i<lz && x[i]==y[i]) i++;
  if (i<lz) return ((ulong)x[i] > (ulong)y[i]) ? sx : -sx;
  if (lx>=ly)
  {
    while (i<lx && !x[i]) i++;
    return (i==lx) ? 0 : sx;
  }
  while (i<ly && !y[i]) i++;
  return (i==ly) ? 0 : -sx;
}

GEN
addss(long x, long y)
{
  if (!x) return stoi(y);
  if (x>0) { pos_s[2] = x; return addsi(y,pos_s); }
  neg_s[2] = -x; return addsi(y,neg_s);
}

GEN
addsi(long x, GEN y)
{
  long sx,sy,ly;
  GEN z;

  if (!x) return icopy(y);
  sy=signe(y); if (!sy) return stoi(x);
  if (x<0) { sx=-1; x=-x; } else sx=1;
  if (sx==sy)
  {
    z = addsispec(x,y+2, lgefint(y)-2);
    setsigne(z,sy); return z;
  }
  ly=lgefint(y);
  if (ly==3)
  {
    const long d = y[2] - x;
    if (!d) return gzero;
    z=cgeti(3);
    if (y[2] < 0 || d > 0) {
      z[1] = evalsigne(sy) | evallgefint(3);
      z[2] = d;
    }
    else {
      z[1] = evalsigne(-sy) | evallgefint(3);
      z[2] =-d;
    }
    return z;
  }
  z = subisspec(y+2,x, ly-2);
  setsigne(z,sy); return z;
}

GEN
addii(GEN x, GEN y)
{
  long sx = signe(x);
  long sy = signe(y);
  long lx,ly;
  GEN z;

  if (!sx) return sy? icopy(y): gzero;
  if (!sy) return icopy(x);
  lx=lgefint(x); ly=lgefint(y);

  if (sx==sy)
    z = addiispec(x+2,y+2,lx-2,ly-2);
  else
  { /* sx != sy */
    long i = lx - ly;
    if (i==0)
    {
      i = absi_cmp(x,y);
      if (!i) return gzero;
    }
    if (i<0) { sx=sy; swapspec(x,y, lx,ly); } /* ensure |x| >= |y| */
    z = subiispec(x+2,y+2,lx-2,ly-2);
  }
  setsigne(z,sx); return z;
}

GEN
addsr(long x, GEN y)
{
  if (!x) return rcopy(y);
  if (x>0) { pos_s[2]=x; return addir(pos_s,y); }
  neg_s[2] = -x; return addir(neg_s,y);
}

GEN
addir(GEN x, GEN y)
{
  long e,l,ly;
  GEN z;

  if (!signe(x)) return rcopy(y);
  if (!signe(y))
  {
    l=lgefint(x)-(expo(y)>>TWOPOTBITS_IN_LONG);
    if (l<3) err(adder3);
    z=cgetr(l); affir(x,z); return z;
  }

  e = expo(y)-expi(x); ly=lg(y);
  if (e>0)
  {
    l = ly - (e>>TWOPOTBITS_IN_LONG);
    if (l<3) return rcopy(y);
  }
  else l = ly + ((-e)>>TWOPOTBITS_IN_LONG)+1;
  z=cgetr(l); affir(x,z); y=addrr(z,y);
  z = y+l; ly = lg(y); while (ly--) z[ly] = y[ly];
  avma=(long)z; return z;
}

GEN
addrr(GEN x, GEN y)
{
  long sx=signe(x),sy=signe(y),ex=expo(x),ey=expo(y);
  long e,m,flag,i,j,f2,lx,ly,lz;
  GEN z;
  LOCAL_OVERFLOW;

  e = ey-ex;
  if (!sy)
  {
    if (!sx)
    {
      if (e > 0) ex=ey;
      z=cgetr(3); z[1]=evalexpo(ex); z[2]=0; return z;
    }
    if (e > 0) { z=cgetr(3); z[1]=evalexpo(ey); z[2]=0; return z; }
    lz = 3 + ((-e)>>TWOPOTBITS_IN_LONG);
    lx = lg(x); if (lz>lx) lz=lx;
    z = cgetr(lz); while(--lz) z[lz]=x[lz];
    return z;
  }
  if (!sx)
  {
    if (e < 0) { z=cgetr(3); z[1]=evalexpo(ex); z[2]=0; return z; }
    lz = 3 + (e>>TWOPOTBITS_IN_LONG);
    ly = lg(y); if (lz>ly) lz=ly;
    z = cgetr(lz); while (--lz) z[lz]=y[lz];
    return z;
  }

  if (e < 0) { z=x; x=y; y=z; ey=ex; i=sx; sx=sy; sy=i; e=-e; }
  /* now ey >= ex */
  lx=lg(x); ly=lg(y);
  if (e)
  {
    long d = e >> TWOPOTBITS_IN_LONG, l = ly-d;
    if (l > lx)     { flag=0; lz=lx+d+1; }
    else if (l > 2) { flag=1; lz=ly; lx=l; }
    else return rcopy(y);
    m = e & (BITS_IN_LONG-1);
  }
  else
  {
    if (lx > ly) lx = ly;
    flag=2; lz=lx; m=0;
  }
  z = cgetr(lz);
  if (m)
  { /* shift right x m bits */
    const ulong sh = BITS_IN_LONG-m;
    GEN p1 = x; x = new_chunk(lx+1);
    shift_right2(x,p1,2,lx, 0,m,sh);
    if (flag==0)
    {
      x[lx] = p1[lx-1] << sh;
      if (x[lx]) { flag = 3; lx++; }
    }
  }

  if (sx==sy)
  { /* addition */
    i=lz-1; avma = (long)z;
    if (flag==0) { z[i] = y[i]; i--; }
    overflow=0;
    for (j=lx-1; j>=2; i--,j--) z[i] = addllx(x[j],y[i]);

    if (overflow)
      for (;;)
      {
        if (i==1)
        {
          shift_right(z,z, 2,lz, 1,1);
          ey=evalexpo(ey+1); if (ey & ~EXPOBITS) err(adder4);
          z[1] = evalsigne(sx) | ey; return z;
        }
        z[i] = y[i]+1; if (z[i--]) break;
      }
    for (; i>=2; i--) z[i]=y[i];
    z[1] = evalsigne(sx) | evalexpo(ey); return z;
  }

  /* subtraction */
  if (e) f2 = 1;
  else
  {
    i=2; while (i<lx && x[i]==y[i]) i++;
    if (i==lx)
    {
      avma = (long)(z+lz);
      e = evalexpo(ey - bit_accuracy(lx));
      if (e & ~EXPOBITS) err(adder4);
      z=cgetr(3); z[1]=e; z[2]=0; return z;
    }
    f2 = ((ulong)y[i] > (ulong)x[i]);
  }

  /* result is non-zero. f2 = (y > x) */
  i=lz-1;
  if (f2)
  {
    if (flag==0) { z[i] = y[i]; i--; }
    j=lx-1; z[i] = subll(y[i],x[j]); i--; j--;
    for (; j>=2; i--,j--) z[i] = subllx(y[i],x[j]);
    if (overflow)
      for (;;) { z[i] = y[i]-1; if (y[i--]) break; }
    for (; i>=2; i--) z[i]=y[i];
    sx = sy;
  }
  else
  {
    if (flag==0) { z[i] = -y[i]; i--; overflow=1; } else overflow=0;
    for (; i>=2; i--) z[i]=subllx(x[i],y[i]);
  }

  x = z+2; i=0; while (!x[i]) i++;
  lz -= i; z += i; m = bfffo(z[2]);
  e = evalexpo(ey - (m | (i<<TWOPOTBITS_IN_LONG)));
  if (e & ~EXPOBITS) err(adder5);
  if (m) shift_left(z,z,2,lz-1, 0,m);
  z[1] = evalsigne(sx) | e;
  z[0] = evaltyp(t_REAL) | evallg(lz);
  avma = (long)z; return z;
}

GEN
mulss(long x, long y)
{
  long s,p1;
  GEN z;
  LOCAL_HIREMAINDER;

  if (!x || !y) return gzero;
  if (x<0) { s = -1; x = -x; } else s=1;
  if (y<0) { s = -s; y = -y; }
  p1 = mulll(x,y);
  if (hiremainder)
  {
    z=cgeti(4); z[1] = evalsigne(s) | evallgefint(4);
    z[2]=hiremainder; z[3]=p1; return z;
  }
  z=cgeti(3); z[1] = evalsigne(s) | evallgefint(3);
  z[2]=p1; return z;
}
#endif

GEN
muluu(ulong x, ulong y)
{
  long p1;
  GEN z;
  LOCAL_HIREMAINDER;

  if (!x || !y) return gzero;
  p1 = mulll(x,y);
  if (hiremainder)
  {
    z=cgeti(4); z[1] = evalsigne(1) | evallgefint(4);
    z[2]=hiremainder; z[3]=p1; return z;
  }
  z=cgeti(3); z[1] = evalsigne(1) | evallgefint(3);
  z[2]=p1; return z;
}

/* assume ny > 0 */
#ifdef INLINE
INLINE
#endif
GEN
mulsispec(long x, GEN y, long ny)
{
  GEN yd, z = (GEN)avma;
  long lz = ny+3;
  LOCAL_HIREMAINDER;

  (void)new_chunk(lz);
  yd = y + ny; *--z = mulll(x, *--yd);
  while (yd > y) *--z = addmul(x,*--yd);
  if (hiremainder) *--z = hiremainder; else lz--;
  *--z = evalsigne(1) | evallgefint(lz);
  *--z = evaltyp(t_INT) | evallg(lz);
  avma=(long)z; return z;
}

GEN
mului(ulong x, GEN y)
{
  long s = signe(y);
  GEN z;

  if (!s || !x) return gzero;
  z = mulsispec(x, y+2, lgefint(y)-2);
  setsigne(z,s); return z;
}

#ifndef __M68K__

GEN
mulsi(long x, GEN y)
{
  long s = signe(y);
  GEN z;

  if (!s || !x) return gzero;
  if (x<0) { s = -s; x = -x; }
  z = mulsispec(x, y+2, lgefint(y)-2);
  setsigne(z,s); return z;
}

GEN
mulsr(long x, GEN y)
{
  long lx,i,s,garde,e,sh,m;
  GEN z;
  LOCAL_HIREMAINDER;

  if (!x) return gzero;
  s = signe(y);
  if (!s)
  {
    if (x<0) x = -x;
    e = y[1] + (BITS_IN_LONG-1)-bfffo(x);
    if (e & ~EXPOBITS) err(muler2);
    z=cgetr(3); z[1]=e; z[2]=0; return z;
  }
  if (x<0) { s = -s; x = -x; }
  if (x==1) { z=rcopy(y); setsigne(z,s); return z; }

  lx = lg(y); e = expo(y);
  z=cgetr(lx); y--; garde=mulll(x,y[lx]);
  for (i=lx-1; i>=3; i--) z[i]=addmul(x,y[i]);
  z[2]=hiremainder;

  sh = bfffo(hiremainder); m = BITS_IN_LONG-sh;
  if (sh) shift_left2(z,z, 2,lx-1, garde,sh,m);
  e = evalexpo(m+e); if (e & ~EXPOBITS) err(muler2);
  z[1] = evalsigne(s) | e; return z;
}

GEN
mulrr(GEN x, GEN y)
{
  long sx = signe(x), sy = signe(y);
  long i,j,ly,lz,lzz,e,flag,p1;
  ulong garde;
  GEN z, y1;
  LOCAL_HIREMAINDER;
  LOCAL_OVERFLOW;

  e = evalexpo(expo(x)+expo(y)); if (e & ~EXPOBITS) err(muler4);
  if (!sx || !sy) { z=cgetr(3); z[1]=e; z[2]=0; return z; }
  if (sy<0) sx = -sx;
  lz=lg(x); ly=lg(y);
  if (lz>ly) { lz=ly; z=x; x=y; y=z; flag=1; } else flag = (lz!=ly);
  z=cgetr(lz); z[1] = evalsigne(sx) | e;
  if (lz==3)
  {
    if (flag)
    {
      (void)mulll(x[2],y[3]);
      garde = addmul(x[2],y[2]);
    }
    else
      garde = mulll(x[2],y[2]);
    if ((long)hiremainder<0) { z[2]=hiremainder; z[1]++; }
    else z[2]=(hiremainder<<1) | (garde>>(BITS_IN_LONG-1));
    return z;
  }

  if (flag) { (void)mulll(x[2],y[lz]); garde = hiremainder; } else garde=0;
  lzz=lz-1; p1=x[lzz];
  if (p1)
  {
    (void)mulll(p1,y[3]);
    garde = addll(addmul(p1,y[2]), garde);
    z[lzz] = overflow+hiremainder;
  }
  else z[lzz]=0;
  for (j=lz-2, y1=y-j; j>=3; j--)
  {
    p1 = x[j]; y1++;
    if (p1)
    {
      (void)mulll(p1,y1[lz+1]);
      garde = addll(addmul(p1,y1[lz]), garde);
      for (i=lzz; i>j; i--)
      {
        hiremainder += overflow;
	z[i] = addll(addmul(p1,y1[i]), z[i]);
      }
      z[j] = hiremainder+overflow;
    }
    else z[j]=0;
  }
  p1=x[2]; y1++;
  garde = addll(mulll(p1,y1[lz]), garde);
  for (i=lzz; i>2; i--)
  {
    hiremainder += overflow;
    z[i] = addll(addmul(p1,y1[i]), z[i]);
  }
  z[2] = hiremainder+overflow;
  if (z[2] < 0) z[1]++;
  else
    shift_left(z,z,2,lzz,garde, 1);
  return z;
}

GEN
mulir(GEN x, GEN y)
{
  long sx=signe(x),sy,lz,lzz,ey,e,p1,i,j;
  ulong garde;
  GEN z,y1;
  LOCAL_HIREMAINDER;
  LOCAL_OVERFLOW;

  if (!sx) return gzero;
  if (!is_bigint(x)) return mulsr(itos(x),y);
  sy=signe(y); ey=expo(y);
  if (!sy)
  {
    e = evalexpo(expi(x)+ey);
    if (e & ~EXPOBITS) err(muler6);
    z=cgetr(3); z[1]=e; z[2]=0; return z;
  }

  if (sy<0) sx = -sx;
  lz=lg(y); z=cgetr(lz);
  y1=cgetr(lz+1);
  affir(x,y1); x=y; y=y1;
  e = evalexpo(expo(y)+ey);
  if (e & ~EXPOBITS) err(muler4);
  z[1] = evalsigne(sx) | e;
  if (lz==3)
  {
    (void)mulll(x[2],y[3]);
    garde=addmul(x[2],y[2]);
    if ((long)hiremainder < 0) { z[2]=hiremainder; z[1]++; }
    else z[2]=(hiremainder<<1) | (garde>>(BITS_IN_LONG-1));
    avma=(long)z; return z;
  }

  (void)mulll(x[2],y[lz]); garde=hiremainder;
  lzz=lz-1; p1=x[lzz];
  if (p1)
  {
    (void)mulll(p1,y[3]);
    garde=addll(addmul(p1,y[2]),garde);
    z[lzz] = overflow+hiremainder;
  }
  else z[lzz]=0;
  for (j=lz-2, y1=y-j; j>=3; j--)
  {
    p1=x[j]; y1++;
    if (p1)
    {
      (void)mulll(p1,y1[lz+1]);
      garde = addll(addmul(p1,y1[lz]), garde);
      for (i=lzz; i>j; i--)
      {
        hiremainder += overflow;
        z[i] = addll(addmul(p1,y1[i]), z[i]);
      }
      z[j] = hiremainder+overflow;
    }
    else z[j]=0;
  }
  p1=x[2]; y1++;
  garde = addll(mulll(p1,y1[lz]), garde);
  for (i=lzz; i>2; i--)
  {
    hiremainder += overflow;
    z[i] = addll(addmul(p1,y1[i]), z[i]);
  }
  z[2] = hiremainder+overflow;
  if (z[2] < 0) z[1]++;
  else
    shift_left(z,z,2,lzz,garde, 1);
  avma=(long)z; return z;
}

/* written by Bruno Haible following an idea of Robert Harley */
long
vals(ulong z)
{
  static char tab[64]={-1,0,1,12,2,6,-1,13,3,-1,7,-1,-1,-1,-1,14,10,4,-1,-1,8,-1,-1,25,-1,-1,-1,-1,-1,21,27,15,31,11,5,-1,-1,-1,-1,-1,9,-1,-1,24,-1,-1,20,26,30,-1,-1,-1,-1,23,-1,19,29,-1,22,18,28,17,16,-1};
#ifdef LONG_IS_64BIT
  long s;
#endif

  if (!z) return -1;
#ifdef LONG_IS_64BIT
  if (! (z&0xffffffff)) { s = 32; z >>=32; } else s = 0;
#endif
  z |= ~z + 1;
  z += z << 4;
  z += z << 6;
  z ^= z << 16; /* or  z -= z<<16 */
#ifdef LONG_IS_64BIT
  return s + tab[(z&0xffffffff)>>26];
#else
  return tab[z>>26];
#endif
}

GEN
modss(long x, long y)
{
  LOCAL_HIREMAINDER;

  if (!y) err(moder1);
  if (y<0) y=-y;
  hiremainder=0; divll(labs(x),y);
  if (!hiremainder) return gzero;
  return (x < 0) ? stoi(y-hiremainder) : stoi(hiremainder);
}

GEN
resss(long x, long y)
{
  LOCAL_HIREMAINDER;

  if (!y) err(reser1);
  hiremainder=0; divll(labs(x),labs(y));
  return (x < 0) ? stoi(-((long)hiremainder)) : stoi(hiremainder);
}

GEN
divsi(long x, GEN y)
{
  long p1, s = signe(y);
  LOCAL_HIREMAINDER;

  if (!s) err(diver2);
  if (!x || lgefint(y)>3 || ((long)y[2])<0)
  {
    hiremainder=x; SAVE_HIREMAINDER; return gzero;
  }
  hiremainder=0; p1=divll(labs(x),y[2]);
  if (x<0) { hiremainder = -((long)hiremainder); p1 = -p1; }
  if (s<0) p1 = -p1;
  SAVE_HIREMAINDER; return stoi(p1);
}
#endif

GEN
modui(ulong x, GEN y)
{
  LOCAL_HIREMAINDER;

  if (!signe(y)) err(diver2);
  if (!x || lgefint(y)>3) hiremainder=x;
  else
  {
    hiremainder=0; (void)divll(x,y[2]);
  }
  return utoi(hiremainder);
}

GEN
modiu(GEN y, ulong x)
{
  long sy=signe(y),ly,i;
  LOCAL_HIREMAINDER;

  if (!x) err(diver4);
  if (!sy) return gzero;
  ly = lgefint(y);
  if (x <= (ulong)y[2]) hiremainder=0;
  else
  {
    if (ly==3) return utoi((sy > 0)? (ulong)y[2]: x - (ulong)y[2]);
    hiremainder=y[2]; ly--; y++;
  }
  for (i=2; i<ly; i++) (void)divll(y[i],x);
  return utoi((sy > 0)? hiremainder: x - hiremainder);
}

#ifndef __M68K__

GEN
modsi(long x, GEN y)
{
  long s = signe(y);
  GEN p1;
  LOCAL_HIREMAINDER;

  if (!s) err(diver2);
  if (!x || lgefint(y)>3 || ((long)y[2])<0) hiremainder=x;
  else
  {
    hiremainder=0; (void)divll(labs(x),y[2]);
    if (x<0) hiremainder = -((long)hiremainder);
  }
  if (!hiremainder) return gzero;
  if (x>0) return stoi(hiremainder);
  if (s<0)
    { setsigne(y,1); p1=addsi(hiremainder,y); setsigne(y,-1); }
  else
    p1=addsi(hiremainder,y);
  return p1;
}

GEN
divis(GEN y, long x)
{
  long sy=signe(y),ly,s,i;
  GEN z;
  LOCAL_HIREMAINDER;

  if (!x) err(diver4);
  if (!sy) { hiremainder=0; SAVE_HIREMAINDER; return gzero; }
  if (x<0) { s = -sy; x = -x; } else s=sy;

  ly = lgefint(y);
  if ((ulong)x <= (ulong)y[2]) hiremainder=0;
  else
  {
    if (ly==3) { hiremainder=itos(y); SAVE_HIREMAINDER; return gzero; }
    hiremainder=y[2]; ly--; y++;
  }
  z = cgeti(ly); z[1] = evallgefint(ly) | evalsigne(s);
  for (i=2; i<ly; i++) z[i]=divll(y[i],x);
  if (sy<0) hiremainder = - ((long)hiremainder);
  SAVE_HIREMAINDER; return z;
}

GEN
divir(GEN x, GEN y)
{
  GEN xr,z;
  long av,ly;

  if (!signe(y)) err(diver5);
  if (!signe(x)) return gzero;
  ly=lg(y); z=cgetr(ly); av=avma; xr=cgetr(ly+1); affir(x,xr);
  affrr(divrr(xr,y),z); avma=av; return z;
}

GEN
divri(GEN x, GEN y)
{
  GEN yr,z;
  long av,lx,s=signe(y);

  if (!s) err(diver8);
  if (!signe(x))
  {
    const long ex = evalexpo(expo(x) - expi(y));

    if (ex<0) err(diver12);
    z=cgetr(3); z[1]=ex; z[2]=0; return z;
  }
  if (!is_bigint(y)) return divrs(x, s>0? y[2]: -y[2]);

  lx=lg(x); z=cgetr(lx);
  av=avma; yr=cgetr(lx+1); affir(y,yr);
  affrr(divrr(x,yr),z); avma=av; return z;
}

void
diviiz(GEN x, GEN y, GEN z)
{
  long av=avma,lz;
  GEN xr,yr;

  if (typ(z)==t_INT) { affii(divii(x,y),z); avma=av; return; }
  lz=lg(z); xr=cgetr(lz); affir(x,xr); yr=cgetr(lz); affir(y,yr);
  affrr(divrr(xr,yr),z); avma=av;
}

void
mpdivz(GEN x, GEN y, GEN z)
{
  long av=avma;

  if (typ(z)==t_INT)
  {
    if (typ(x)==t_REAL || typ(y)==t_REAL) err(divzer1);
    affii(divii(x,y),z); avma=av; return;
  }
  if (typ(x)==t_INT)
  {
    GEN xr,yr;
    long lz;

    if (typ(y)==t_REAL) { affrr(divir(x,y),z); avma=av; return; }
    lz=lg(z); xr=cgetr(lz); affir(x,xr); yr=cgetr(lz); affir(y,yr);
    affrr(divrr(xr,yr),z); avma=av; return;
  }
  if (typ(y)==t_REAL) { affrr(divrr(x,y),z); avma=av; return; }
  affrr(divri(x,y),z); avma=av;
}

GEN
divsr(long x, GEN y)
{
  long av,ly;
  GEN p1,z;

  if (!signe(y)) err(diver3);
  if (!x) return gzero;
  ly=lg(y); z=cgetr(ly); av=avma;
  p1=cgetr(ly+1); affsr(x,p1); affrr(divrr(p1,y),z);
  avma=av; return z;
}

GEN
modii(GEN x, GEN y)
{
  switch(signe(x))
  {
    case 0: return gzero;
    case 1: return resii(x,y);
    default:
    {
      long av = avma;
      (void)new_chunk(lgefint(y));
      x = resii(x,y); avma=av;
      if (x==gzero) return x;
      return subiispec(y+2,x+2,lgefint(y)-2,lgefint(x)-2);
    }
  }
}

void
modiiz(GEN x, GEN y, GEN z)
{
  const long av = avma;
  affii(modii(x,y),z); avma=av;
}

GEN
divrs(GEN x, long y)
{
  long i,lx,ex,garde,sh,s=signe(x);
  GEN z;
  LOCAL_HIREMAINDER;

  if (!y) err(diver6);
  if (!s)
  {
    z=cgetr(3); z[1] = x[1] - (BITS_IN_LONG-1) + bfffo(y);
    if (z[1]<0) err(diver7);
    z[2]=0; return z;
  }
  if (y<0) { s = -s; y = -y; }
  if (y==1) { z=rcopy(x); setsigne(z,s); return z; }

  z=cgetr(lx=lg(x)); hiremainder=0;
  for (i=2; i<lx; i++) z[i]=divll(x[i],y);

  /* we may have hiremainder != 0 ==> garde */
  garde=divll(0,y); sh=bfffo(z[2]); ex=evalexpo(expo(x)-sh);
  if (ex & ~EXPOBITS) err(diver7);
  if (sh) shift_left(z,z, 2,lx-1, garde,sh);
  z[1] = evalsigne(s) | ex;
  return z;
}

GEN
divrr(GEN x, GEN y)
{
  long sx=signe(x), sy=signe(y), lx,ly,lz,e,i,j;
  ulong si,saux;
  GEN z,x1;

  if (!sy) err(diver9);
  e = evalexpo(expo(x) - expo(y));
  if (e & ~EXPOBITS) err(diver11);
  if (!sx) { z=cgetr(3); z[1]=e; z[2]=0; return z; }
  if (sy<0) sx = -sx;
  e = evalsigne(sx) | e;
  lx=lg(x); ly=lg(y);
  if (ly==3)
  {
    ulong k = x[2], l = (lx>3)? x[3]: 0;
    LOCAL_HIREMAINDER;
    if (k < (ulong)y[2]) e--;
    else
    {
      l >>= 1; if (k&1) l |= HIGHBIT;
      k >>= 1;
    }
    z=cgetr(3); z[1]=e;
    hiremainder=k; z[2]=divll(l,y[2]); return z;
  }

  lz = (lx<=ly)? lx: ly;
  x1 = (z=new_chunk(lz))-1;
  x1[1]=0; for (i=2; i<lz; i++) x1[i]=x[i];
  x1[lz] = (lx>lz)? x[lz]: 0;
  x=z; si=y[2]; saux=y[3];
  for (i=0; i<lz-1; i++)
  { /* x1 = x + (i-1) */
    ulong k,qp;
    LOCAL_HIREMAINDER;
    LOCAL_OVERFLOW;
    if ((ulong)x1[1] == si)
    {
      qp = MAXULONG; k=addll(si,x1[2]);
    }
    else
    {
      if ((ulong)x1[1] > si) /* can't happen if i=0 */
      {
        GEN y1 = y+1;
	overflow=0;
	for (j=lz-i; j>0; j--) x1[j] = subllx(x1[j],y1[j]);
	j=i; do x[--j]++; while (j && !x[j]);
      }
      hiremainder=x1[1]; overflow=0;
      qp=divll(x1[2],si); k=hiremainder;
    }
    if (!overflow)
    {
      long k3 = subll(mulll(qp,saux), x1[3]);
      long k4 = subllx(hiremainder,k);
      while (!overflow && k4) { qp--; k3=subll(k3,saux); k4=subllx(k4,si); }
    }
    j = lz-i+1;
    if (j<ly) (void)mulll(qp,y[j]); else { hiremainder=0 ; j=ly; }
    for (j--; j>1; j--)
    {
      x1[j] = subll(x1[j], addmul(qp,y[j]));
      hiremainder += overflow;
    }
    if (x1[1] != hiremainder)
    {
      if ((ulong)x1[1] < hiremainder)
      {
        qp--;
        overflow=0; for (j=lz-i; j>1; j--) x1[j]=addllx(x1[j], y[j]);
      }
      else
      {
	x1[1] -= hiremainder;
	while (x1[1])
	{
	  qp++; if (!qp) { j=i; do x[--j]++; while (j && !x[j]); }
          overflow=0; for (j=lz-i; j>1; j--) x1[j]=subllx(x1[j],y[j]);
	  x1[1] -= overflow;
	}
      }
    }
    x1[1]=qp; x1++;
  }
  x1 = x-1; for (j=lz-1; j>=2; j--) x[j]=x1[j];
  if (*x) { shift_right(x,x, 2,lz, 1,1); } else e--;
  x[0]=evaltyp(t_REAL)|evallg(lz);
  x[1]=e; return x;
}
#endif /* !defined(__M68K__) */
/* The following ones are not in mp.s (mulii is, with a different algorithm) */

/* Integer division x / y:
 *   if z = ONLY_REM return remainder, otherwise return quotient
 *   if z != NULL set *z to remainder
 *   *z is the last object on stack (and thus can be disposed of with cgiv
 *   instead of gerepile)
 * If *z is zero, we put gzero here and no copy.
 * space needed: lx + ly
 */
GEN
dvmdii(GEN x, GEN y, GEN *z)
{
  long sx=signe(x),sy=signe(y);
  long av,lx,ly,lz,i,j,sh,k,lq,lr;
  ulong si,qp,saux, *xd,*rd,*qd;
  GEN r,q,x1;

  if (!sy) err(dvmer1);
  if (!sx)
  {
    if (!z || z == ONLY_REM) return gzero;
    *z=gzero; return gzero;
  }
  lx=lgefint(x);
  ly=lgefint(y); lz=lx-ly;
  if (lz <= 0)
  {
    if (lz == 0)
    {
      for (i=2; i<lx; i++)
        if (x[i] != y[i])
        {
          if ((ulong)x[i] > (ulong)y[i]) goto DIVIDE;
          goto TRIVIAL;
        }
      if (z == ONLY_REM) return gzero;
      if (z) *z = gzero;
      if (sx < 0) sy = -sy;
      return stoi(sy);
    }
TRIVIAL:
    if (z == ONLY_REM) return icopy(x);
    if (z) *z = icopy(x);
    return gzero;
  }
DIVIDE: /* quotient is non-zero */
  av=avma; if (sx<0) sy = -sy;
  if (ly==3)
  {
    LOCAL_HIREMAINDER;
    si = y[2];
    if (si <= (ulong)x[2]) hiremainder=0;
    else
    {
      hiremainder = x[2]; lx--; x++;
    }
    q = new_chunk(lx); for (i=2; i<lx; i++) q[i]=divll(x[i],si);
    if (z == ONLY_REM)
    {
      avma=av; if (!hiremainder) return gzero;
      r=cgeti(3);
      r[1] = evalsigne(sx) | evallgefint(3);
      r[2]=hiremainder; return r;
    }
    q[1] = evalsigne(sy) | evallgefint(lx);
    q[0] = evaltyp(t_INT) | evallg(lx);
    if (!z) return q;
    if (!hiremainder) { *z=gzero; return q; }
    r=cgeti(3);
    r[1] = evalsigne(sx) | evallgefint(3);
    r[2] = hiremainder; *z=r; return q;
  }

  x1 = new_chunk(lx); sh = bfffo(y[2]);
  if (sh)
  { /* normalize so that highbit(y) = 1 (shift left x and y by sh bits)*/
    register const ulong m = BITS_IN_LONG - sh;
    r = new_chunk(ly);
    shift_left2(r, y,2,ly-1, 0,sh,m); y = r;
    shift_left2(x1,x,2,lx-1, 0,sh,m);
    x1[1] = ((ulong)x[2]) >> m;
  }
  else
  {
    x1[1]=0; for (j=2; j<lx; j++) x1[j]=x[j];
  }
  x=x1; si=y[2]; saux=y[3];
  for (i=0; i<=lz; i++)
  { /* x1 = x + i */
    LOCAL_HIREMAINDER;
    LOCAL_OVERFLOW;
    if ((ulong)x1[1] == si)
    {
      qp = MAXULONG; k=addll(si,x1[2]);
    }
    else
    {
      hiremainder=x1[1]; overflow=0;
      qp=divll(x1[2],si); k=hiremainder;
    }
    if (!overflow)
    {
      long k3 = subll(mulll(qp,saux), x1[3]);
      long k4 = subllx(hiremainder,k);
      while (!overflow && k4) { qp--; k3=subll(k3,saux); k4=subllx(k4,si); }
    }
    hiremainder=0;
    for (j=ly-1; j>1; j--)
    {
      x1[j] = subll(x1[j], addmul(qp,y[j]));
      hiremainder+=overflow;
    }
    if ((ulong)x1[1] < hiremainder)
    {
      overflow=0; qp--;
      for (j=ly-1; j>1; j--) x1[j] = addllx(x1[j],y[j]);
    }
    x1[1]=qp; x1++;
  }

  lq = lz+2;
  if (!z)
  {
    qd = (ulong*)av;
    xd = (ulong*)(x + lq);
    if (x[1]) { lz++; lq++; }
    while (lz--) *--qd = *--xd;
    *--qd = evalsigne(sy) | evallgefint(lq);
    *--qd = evaltyp(t_INT) | evallg(lq);
    avma = (long)qd; return (GEN)qd;
  }

  j=lq; while (j<lx && !x[j]) j++;
  if (z == ONLY_REM)
  {
    lz = lx-j; if (lz==0) { avma = av; return gzero; }
    rd = (ulong*)av; lr = lz+2;
    xd = (ulong*)(x + lx);
    if (!sh) while (lz--) *--rd = *--xd;
    else
    { /* shift remainder right by sh bits */
      const ulong shl = BITS_IN_LONG - sh;
      ulong l;
      xd--;
      while (--lz) /* fill r[3..] */
      {
        l = *xd >> sh;
        *--rd = l | (*--xd << shl);
      }
      l = *xd >> sh;
      if (l) *--rd = l; else lr--;
    }
    *--rd = evalsigne(sx) | evallgefint(lr);
    *--rd = evaltyp(t_INT) | evallg(lr);
    avma = (long)rd; return (GEN)rd;
  }

  lz = lx-j; lr = lz+2;
  if (lz)
  {
    xd = (ulong*)(x + lx);
    if (!sh)
    {
      rd = (ulong*)avma; r = new_chunk(lr);
      while (lz--) *--rd = *--xd;
    }
    else
    { /* shift remainder right by sh bits */
      const ulong shl = BITS_IN_LONG - sh;
      ulong l;
      rd = (ulong*)x; /* overwrite shifted y */
      xd--;
      while (--lz)
      {
        l = *xd >> sh;
        *--rd = l | (*--xd << shl);
      }
      l = *xd >> sh;
      if (l) *--rd = l; else lr--;
    }
    *--rd = evalsigne(sx) | evallgefint(lr);
    *--rd = evaltyp(t_INT) | evallg(lr);
    rd += lr;
  }
  qd = (ulong*)av;
  xd = (ulong*)(x + lq);
  if (x[1]) lq++;
  j = lq-2; while (j--) *--qd = *--xd;
  *--qd = evalsigne(sy) | evallgefint(lq);
  *--qd = evaltyp(t_INT) | evallg(lq);
  q = (GEN)qd;
  if (lr==2) *z = gzero;
  else
  {
    while (lr--) *--qd = *--rd;
    *z = (GEN)qd;
  }
  avma = (long)qd; return q;
}

/* assume y > x > 0. return y mod x */
ulong
mppgcd_resiu(GEN y, ulong x)
{
  long i, ly = lgefint(y);
  LOCAL_HIREMAINDER;

  hiremainder = 0;
  for (i=2; i<ly; i++) (void)divll(y[i],x);
  return hiremainder;
}

/* Assume x>y>0, both of them odd. return x-y if x=y mod 4, x+y otherwise */
void
mppgcd_plus_minus(GEN x, GEN y, GEN res)
{
  long av = avma;
  long lx = lgefint(x)-1;
  long ly = lgefint(y)-1, lt,m,i;
  GEN t;

  if ((x[lx]^y[ly]) & 3) /* x != y mod 4*/
    t = addiispec(x+2,y+2,lx-1,ly-1);
  else
    t = subiispec(x+2,y+2,lx-1,ly-1);

  lt = lgefint(t)-1; while (!t[lt]) lt--;
  m = vals(t[lt]); lt++;
  if (m == 0) /* 2^32 | t */
  {
    for (i = 2; i < lt; i++) res[i] = t[i];
  }
  else if (t[2] >> m)
  {
    shift_right(res,t, 2,lt, 0,m);
  }
  else
  {
    lt--; t++;
    shift_right(res,t, 2,lt, t[1],m);
  }
  res[1] = evalsigne(1)|evallgefint(lt);
  avma = av;
}

/* private version of mulss */
ulong
smulss(ulong x, ulong y, ulong *rem)
{
  LOCAL_HIREMAINDER;
  x=mulll(x,y); *rem=hiremainder; return x;
}

#ifdef LONG_IS_64BIT
#  define DIVCONVI 7
#else
#  define DIVCONVI 14
#endif

/* Conversion entier --> base 10^9. Assume x > 0 */
GEN
convi(GEN x)
{
  ulong av=avma, lim;
  long lz;
  GEN z,p1;

  lz = 3 + ((lgefint(x)-2)*15)/DIVCONVI;
  z=new_chunk(lz); z[1] = -1; p1 = z+2;
  lim = stack_lim(av,1);
  for(;;)
  {
    x = divis(x,1000000000); *p1++ = hiremainder;
    if (!signe(x)) { avma=av; return p1; }
    if (low_stack(lim, stack_lim(av,1))) x = gerepileuptoint((long)z,x);
  }
}
#undef DIVCONVI

/* Conversion partie fractionnaire --> base 10^9 (expo(x)<0) */
GEN
confrac(GEN x)
{
  long lx=lg(x), ex = -expo(x)-1, d,m,ly,ey,lr,nbdec,i,j;
  GEN y,y1;

  ey = ex + bit_accuracy(lx);
  ly = 1 + ((ey-1) >> TWOPOTBITS_IN_LONG);
  d = ex >> TWOPOTBITS_IN_LONG;
  m = ex & (BITS_IN_LONG-1);
  y = new_chunk(ly); y1 = y + (d-2);
  while (d--) y[d]=0;
  if (!m)
    for (i=2; i<lx; i++) y1[i] = x[i];
  else
  { /* shift x left sh bits */
    const ulong sh=BITS_IN_LONG-m;
    ulong k=0, l;
    for (i=2; i<lx; i++)
    {
      l = x[i];
      y1[i] = (l>>m)|k;
      k = l<<sh;
    }
    y1[i] = k;
  }
  nbdec = (long) (ey*L2SL10)+1; lr=(nbdec+17)/9;
  y1=new_chunk(lr); *y1=nbdec;
  for (j=1; j<lr; j++)
  {
    LOCAL_HIREMAINDER;
    hiremainder=0;
    for (i=ly-1; i>=0; i--) y[i]=addmul(y[i],1000000000);
    y1[j]=hiremainder;
  }
  return y1;
}

GEN
truedvmdii(GEN x, GEN y, GEN *z)
{
  long av=avma,tetpil;
  GEN res, qu = dvmdii(x,y,&res);
  GEN *gptr[2];

  if (signe(res)>=0)
  {
    if (z == ONLY_REM) return gerepileuptoint(av,res);
    if (z) *z = res; else cgiv(res);
    return qu;
  }

  tetpil=avma;
  if (z == ONLY_REM)
  {
    res = subiispec(y+2,res+2, lgefint(y)-2,lgefint(res)-2);
    return gerepile(av,tetpil,res);
  }
  qu = addsi(-signe(y),qu);
  if (!z) return gerepile(av,tetpil,qu);

  *z = subiispec(y+2,res+2, lgefint(y)-2,lgefint(res)-2);
  gptr[0]=&qu; gptr[1]=z; gerepilemanysp(av,tetpil,gptr,2);
  return qu;
}

#if 0
/* Exact integer division */

static ulong
invrev(ulong b)
/* Find c such that 1=c*b mod B (where B = 2^32 or 2^64), assuming b odd,
   which is not checked */
{
  int r;
  ulong x;

  r=b&7; x=(r==3 || r==5)? b+8: b; /* x=b^(-1) mod 2^4 */
  x=x*(2-b*x); x=x*(2-b*x); x=x*(2-b*x); /* x=b^(-1) mod 2^32 */
#ifdef LONG_IS_64BIT
  x=x*(2-b*x); /* x=b^(-1) mod 2^64 */
#endif
  return x;
}

#define divllrev(a,b) (((ulong)a)*invrev(b))

/* 2-adic division */
GEN
diviirev(GEN x, GEN y, long a)
/* Find z such that |x|=|y|*z mod B^a, where a<=lgefint(x)-2 */
{
  long lx,lgx,ly,vy,av=avma,tetpil,i,j,ii;
  ulong binv,q;
  GEN z;

  if (!signe(y)) err(dvmer1);
  if (!signe(x)) return gzero;
/* make y odd */
  vy=vali(y);
  if (vy)
  {
    if (vali(x)<vy) err(talker,"impossible division in diviirev");
    y=shifti(y,-vy); x=shifti(x,-vy); a-=(vy>>TWOPOTBITS_IN_LONG);
  }
  else x=icopy(x); /* necessary because we destroy x */
/* improve the above by touching only a words */
  if (a<=0) {avma=a;return gzero;}
/* now y is odd */
  lx=a+2; ly=lgefint(y); lgx=lgefint(x);
  if (lx>lgx) err(talker,"3rd parameter too large in diviirev");
  binv=invrev(y[ly-1]);
  z=cgeti(lx);
  for (ii=lgx-1,i=lx-1; i>=2; i--,ii--)
  {
    long limj;
    LOCAL_HIREMAINDER;
    LOCAL_OVERFLOW;

    z[i]=q=binv*((ulong)x[ii]); /* this is the i-th quotient */
    limj=max(lgx-a,3+ii-ly);
    mulll(q,y[ly-1]); overflow=0;
    for (j=ii-1; j>=limj; j--)
      x[j]=subllx(x[j],addmul(q,y[j+ly-ii-1]));
  }
  tetpil=avma; i=2; while((i<lx)&&(!z[i])) i++;
  if (i==lx) {avma=av; return gzero;}
  y=cgeti(lx-i+2); y[1]=evalsigne(1)|evallgefint(lx-i+2); j=2;
  for ( ; i<lx; i++) y[j++]=z[i];
  return gerepile(av,tetpil,y);
}

GEN
diviiexactfullrev(GEN x, GEN y)
/* Find z such that x=y*z knowing that y divides x */
{
  long lx,lz,ly,vy,av=avma,tetpil,i,j,ii,sx=signe(x),sy=signe(y);
  ulong binv,q;
  GEN z;

  if (!sy) err(dvmer1);
  if (!sx) return gzero;
/* make y odd */
  vy=vali(y);
  if (vy)
  {
    if (vali(x)<vy) err(talker,"impossible division in diviirev");
    y=shifti(y,-vy); x=shifti(x,-vy);
  }
  else x=icopy(x); /* necessary because we destroy x */
/* now y is odd */
  ly=lgefint(y); lx=lgefint(x);
  if (ly>lx) err(talker,"impossible division in diviirev");
  binv=invrev(y[ly-1]);
  i=2; while (i<ly && y[i]==x[i]) i++;
  lz=(i==ly || y[i]<x[i]) ? lx-ly+3 : lx-ly+2;
  z=cgeti(lz);
  for (ii=lx-1,i=lz-1; i>=2; i--,ii--)
  {
    long limj;
    LOCAL_HIREMAINDER;
    LOCAL_OVERFLOW;

    z[i]=q=binv*((ulong)x[ii]); /* this is the i-th quotient */
    limj=max(lx-lz+2,3+ii-ly);
    mulll(q,y[ly-1]); overflow=0;
    for (j=ii-1; j>=limj; j--)
      x[j]=subllx(x[j],addmul(q,y[j+ly-ii-1]));
  }
  tetpil=avma; i=2; while((i<lz)&&(!z[i])) i++;
  if (i==lz) err(talker,"bug in diviiexact");
  y=cgeti(lz-i+2); y[1]=evalsigne(sx*sy) | evallgefint(lz-i+2); j=2;
  for ( ; i<lz; i++) y[j++]=z[i];
  return gerepile(av,tetpil,y);
}

GEN
diviiexact2(GEN x, GEN y)
/* Find z such that x=y*z assuming y divides x (which is not checked) */
{
  long sx=signe(x),sy=signe(y),av=avma,tetpil,lyinv,lpr,a,lx,ly,lz,lzs,lp1;
  long i,j,vy;
  ulong aux;
  GEN yinv,p1,z,xinit,yinit;

  if (!sy) err(dvmer1);
  if (!sx) return gzero;
  xinit=x; yinit=y;
  setsigne(y,1);setsigne(x,1);
/* make y odd */
  vy=vali(y);
  if (vy)
  {
    if (vali(x)<vy) err(talker,"impossible division in diviirev");
    y=shifti(y,-vy); x=shifti(x,-vy);
  }
/* now y is odd */
  ly=lgefint(y); lx=lgefint(x);
  if (lx<ly) err(talker,"not an exact division in diviiexact");
  a=lx-ly+1; lz=a+2;
  aux=invrev(y[ly-1]);
  if (aux & HIGHBIT) {yinv=stoi(aux^HIGHBIT);yinv[2]|=HIGHBIT;}
  else yinv=stoi(aux); /* inverse of y mod 2^32 (or 2^64) */
  lpr=1; /* current accuracy */
  while(lpr<a)
  {
    long lycut;
    GEN ycut;

    lyinv=lgefint(yinv);
    lycut=min(2*lpr+2,ly);
    ycut=cgeti(lycut); ycut[1]=evalsigne(1) | evallgefint(lycut);
    for(i=2; i<lycut; i++) ycut[i]=y[ly+i-lycut];
    p1=mulii(yinv,ycut); lp1=lgefint(p1);
    if (lp1>lpr+2)
    {
      long lp1cut,lynew,lp2;
      GEN p1cut,p2,ynew;
      LOCAL_OVERFLOW;

      lp1cut=min(lp1-lpr,lpr+2);
      p1cut=cgeti(lp1cut); p1cut[1]=evalsigne(1) | evallgefint(lp1cut);
      overflow=0;
      for (i=lp1cut-1; i>=2; i--) p1cut[i]=subllx(0,p1[i+lp1-lpr-lp1cut]);
      p2=mulii(p1cut,yinv); lp2=lgefint(p2);
      lynew=(lp2<=lpr+2) ? lpr+lp2 : 2*lpr+2;
      ynew=cgeti(lynew); ynew[1]=evalsigne(1) | evallgefint(lynew);
      for (i=lynew-1; i>=lynew-lpr; i--) ynew[i]=yinv[i+lyinv-lynew];
      for (i=lynew-lpr-1; i>=2; i--) ynew[i]=p2[i+lp2+lpr-lynew];
      yinv=ynew;
    }
    lpr<<=1;
  }
  lyinv=lgefint(yinv); lzs=min(lz,lyinv);
  z=cgeti(lzs); z[1]=evalsigne(1) | evallgefint(lzs);
  for(i=2; i<lzs; i++) z[i]=yinv[i+lyinv-lzs];
  p1=mulii(z,x); lp1=lgefint(p1); lzs=min(lz,lp1);
  z=cgeti(lzs);
  for (i=2; i<lzs; i++) z[i]=p1[i+lp1-lzs];
  i=2; while (i<lzs && !z[i]) i++;
  if (i==lzs) err(talker,"bug in diviiexact");
  tetpil=avma; p1=cgeti(lzs-i+2);
  p1[1]=evalsigne(sx*sy) | evallgefint(lzs-i+2);
  for (j=2; j<=lzs-i+1; j++) p1[j]=z[j+i-2];
  setsigne(xinit,sx);setsigne(yinit,sy);
  return gerepile(av,tetpil,p1);
}
#endif

long
smodsi(long x, GEN y)
{
  if (x<0) err(talker,"negative small integer in smodsi");
  (void)divsi(x,y); return hiremainder;
}

/* x and y are integers. Return 1 if |x| == |y|, 0 otherwise */
int
absi_equal(GEN x, GEN y)
{
  long lx,i;

  if (!signe(x)) return !signe(y);
  if (!signe(y)) return 0;

  lx=lgefint(x); if (lx != lgefint(y)) return 0;
  i=2; while (i<lx && x[i]==y[i]) i++;
  return (i==lx);
}

/* x and y are integers. Return sign(|x| - |y|) */
int
absi_cmp(GEN x, GEN y)
{
  long lx,ly,i;

  if (!signe(x)) return signe(y)? -1: 0;
  if (!signe(y)) return 1;

  lx=lgefint(x); ly=lgefint(y);
  if (lx>ly) return 1;
  if (lx<ly) return -1;
  i=2; while (i<lx && x[i]==y[i]) i++;
  if (i==lx) return 0;
  return ((ulong)x[i] > (ulong)y[i])? 1: -1;
}

/* x and y are reals. Return sign(|x| - |y|) */
int
absr_cmp(GEN x, GEN y)
{
  long ex,ey,lx,ly,lz,i;

  if (!signe(x)) return signe(y)? -1: 0;
  if (!signe(y)) return 1;

  ex=expo(x); ey=expo(y);
  if (ex>ey) return  1;
  if (ex<ey) return -1;

  lx=lg(x); ly=lg(y); lz = (lx<ly)?lx:ly;
  i=2; while (i<lz && x[i]==y[i]) i++;
  if (i<lz) return ((ulong)x[i] > (ulong)y[i])? 1: -1;
  if (lx>=ly)
  {
    while (i<lx && !x[i]) i++;
    return (i==lx)? 0: 1;
  }
  while (i<ly && !y[i]) i++;
  return (i==ly)? 0: -1;
}

/********************************************************************/
/**                                                                **/
/**               INTEGER MULTIPLICATION (KARATSUBA)               **/
/**                                                                **/
/********************************************************************/

#if 0 /* for tunings */
long SQRI_LIMIT = 12;
long MULII_LIMIT = 16;

void
setsqi(long a) { SQRI_LIMIT=a; }
void
setmuli(long a) { MULII_LIMIT=a; }

GEN
speci(GEN x, long nx)
{
  GEN z = cgeti(nx+2);
  long i;
  for (i=0; i<nx; i++) z[i+2] = x[i];
  z[1]=evalsigne(1)|evallgefint(nx+2);
  return z;
}
#else
#  define SQRI_LIMIT 12
#  define MULII_LIMIT 16
#endif

/* nx >= ny = num. of digits of x, y (not GEN, see mulii) */
#ifdef INLINE
INLINE
#endif
GEN
muliispec(GEN x, GEN y, long nx, long ny)
{
  GEN z2e,z2d,yd,xd,ye,zd;
  long p1,lz;
  LOCAL_HIREMAINDER;

  if (!ny) return gzero;
  zd = (GEN)avma; lz = nx+ny+2;
  (void)new_chunk(lz);
  xd = x + nx;
  yd = y + ny;
  ye = yd; p1 = *--xd;

  *--zd = mulll(p1, *--yd); z2e = zd;
  while (yd > y) *--zd = addmul(p1, *--yd);
  *--zd = hiremainder;

  while (xd > x)
  {
    LOCAL_OVERFLOW;
    yd = ye; p1 = *--xd;

    z2d = --z2e;
    *z2d = addll(mulll(p1, *--yd), *z2d); z2d--;
    while (yd > y)
    {
      hiremainder += overflow;
      *z2d = addll(addmul(p1, *--yd), *z2d); z2d--;
    }
    *--zd = hiremainder + overflow;
  }
  if (*zd == 0) { zd++; lz--; } /* normalize */
  *--zd = evalsigne(1) | evallgefint(lz);
  *--zd = evaltyp(t_INT) | evallg(lz);
  avma=(long)zd; return zd;
}

/* return (x shifted left d words) + y. Assume d > 0, x > 0 and y >= 0 */
static GEN
addshiftw(GEN x, GEN y, long d)
{
  GEN z,z0,y0,yd, zd = (GEN)avma;
  long a,lz,ly = lgefint(y);

  z0 = new_chunk(d);
  a = ly-2; yd = y+ly;
  if (a >= d)
  {
    y0 = yd-d; while (yd > y0) *--zd = *--yd; /* copy last d words of y */
    a -= d;
    if (a)
      z = addiispec(x+2, y+2, lgefint(x)-2, a);
    else
      z = icopy(x);
  }
  else
  {
    y0 = yd-a; while (yd > y0) *--zd = *--yd; /* copy last a words of y */
    while (zd >= z0) *--zd = 0;    /* complete with 0s */
    z = icopy(x);
  }
  lz = lgefint(z)+d;
  z[1] = evalsigne(1) | evallgefint(lz);
  z[0] = evaltyp(t_INT) | evallg(lz); return z;
}

/* Fast product (Karatsuba) of integers a,b. These are not real GENs, a+2
 * and b+2 were sent instead. na, nb = number of digits of a, b.
 * c,c0,c1,c2 are genuine GENs.
 */
static GEN
quickmulii(GEN a, GEN b, long na, long nb)
{
  GEN a0,c,c0;
  long av,n0,n0a,i;

  if (na < nb) swapspec(a,b, na,nb);
  if (nb == 1) return mulsispec(*b, a, na);
  if (nb == 0) return gzero;
  if (nb < MULII_LIMIT) return muliispec(a,b,na,nb);
  i=(na>>1); n0=na-i; na=i;
  av=avma; a0=a+na; n0a=n0;
  while (!*a0 && n0a) { a0++; n0a--; }

  if (n0a && nb > n0)
  { /* nb <= na <= n0 */
    GEN b0,c1,c2;
    long n0b;

    nb -= n0;
    c = quickmulii(a,b,na,nb);
    b0 = b+nb; n0b = n0;
    while (!*b0 && n0b) { b0++; n0b--; }
    if (n0b)
    {
      c0 = quickmulii(a0,b0, n0a,n0b);

      c2 = addiispec(a0,a, n0a,na);
      c1 = addiispec(b0,b, n0b,nb);
      c1 = quickmulii(c1+2,c2+2, lgefint(c1)-2,lgefint(c2)-2);
      c2 = addiispec(c0+2, c+2, lgefint(c0)-2,lgefint(c) -2);

      c1 = subiispec(c1+2,c2+2, lgefint(c1)-2,lgefint(c2)-2);
    }
    else
    {
      c0 = gzero;
      c1 = quickmulii(a0,b, n0a,nb);
    }
    c = addshiftw(c,c1, n0);
  }
  else
  {
    c = quickmulii(a,b,na,nb);
    c0 = quickmulii(a0,b,n0a,nb);
  }
  return gerepileuptoint(av, addshiftw(c,c0, n0));
}

/* actual operations will take place on a+2 and b+2: we strip the codewords */
GEN
mulii(GEN a,GEN b)
{
  long sa,sb;
  GEN z;

  sa=signe(a); if (!sa) return gzero;
  sb=signe(b); if (!sb) return gzero;
  if (sb<0) sa = -sa;
  z = quickmulii(a+2,b+2, lgefint(a)-2,lgefint(b)-2);
  setsigne(z,sa); return z;
}

static GEN
quicksqri(GEN a, long na)
{
  GEN a0,c,c0,c1;
  long av,n0,n0a,i;

  if (na<SQRI_LIMIT) return muliispec(a,a,na,na);
  i=(na>>1); n0=na-i; na=i;
  av=avma; a0=a+na; n0a=n0;
  while (!*a0 && n0a) { a0++; n0a--; }
  c = quicksqri(a,na);
  if (n0a)
  {
    c0 = quicksqri(a0,n0a);
    c1 = shifti(quickmulii(a0,a, n0a,na),1);
    c = addshiftw(c,c1, n0);
    c = addshiftw(c,c0, n0);
  }
  else
    c = addshiftw(c,gzero,n0<<1);
  return gerepileuptoint(av, c);
}

GEN
sqri(GEN a) { return quicksqri(a+2, lgefint(a)-2); }

#define MULRR_LIMIT  32
#define MULRR2_LIMIT 32

#if 0
GEN
karamulrr1(GEN x, GEN y)
{
  long sx,sy;
  long i,i1,i2,lx=lg(x),ly=lg(y),e,flag,garde;
  long lz2,lz3,lz4;
  GEN z,lo1,lo2,hi;

  /* ensure that lg(y) >= lg(x) */
  if (lx>ly) { lx=ly; z=x; x=y; y=z; flag=1; } else flag = (lx!=ly);
  if (lx < MULRR_LIMIT) return mulrr(x,y);
  sx=signe(x); sy=signe(y);
  e = evalexpo(expo(x)+expo(y)); if (e & ~EXPOBITS) err(muler4);
  if (!sx || !sy) { z=cgetr(3); z[2]=0; z[1]=e; return z; }
  if (sy<0) sx = -sx;
  ly=lx+flag; z=cgetr(lx);
  lz2 = (lx>>1); lz3 = lx-lz2;
  x += 2; lx -= 2;
  y += 2; ly -= 2;
  hi = quickmulii(x,y,lz2,lz2);
  i1=lz2; while (i1<lx && !x[i1]) i1++;
  lo1 = quickmulii(y,x+i1,lz2,lx-i1);
  i2=lz2; while (i2<ly && !y[i2]) i2++;
  lo2 = quickmulii(x,y+i2,lz2,ly-i2);

  if (signe(lo1))
  {
    if (flag) { lo2 = addshiftw(lo1,lo2,1); lz3++; } else lo2=addii(lo1,lo2);
  }
  lz4=lgefint(lo2)-lz3;
  if (lz4>0) hi = addiispec(hi+2,lo2+2, lgefint(hi)-2,lz4);
  if (hi[2] < 0)
  {
    e++; garde=hi[lx+2];
    for (i=lx+1; i>=2 ; i--) z[i]=hi[i];
  }
  else
  {
    garde = (hi[lx+2] << 1);
    shift_left(z,hi,2,lx+1, garde, 1);
  }
  z[1]=evalsigne(sx) | e;
  if (garde < 0)
  { /* round to nearest */
    i=lx+2; do z[--i]++; while (z[i]==0);
    if (i==1) z[2]=HIGHBIT;
  }
  avma=(long)z; return z;
}

GEN
karamulrr2(GEN x, GEN y)
{
  long sx,sy,i,lx=lg(x),ly=lg(y),e,flag,garde;
  GEN z,hi;

  if (lx>ly) { lx=ly; z=x; x=y; y=z; flag=1; } else flag = (lx!=ly);
  if (lx < MULRR2_LIMIT) return mulrr(x,y);
  ly=lx+flag; sx=signe(x); sy=signe(y);
  e = evalexpo(expo(x)+expo(y)); if (e & ~EXPOBITS) err(muler4);
  if (!sx || !sy) { z=cgetr(3); z[2]=0; z[1]=e; return z; }
  if (sy<0) sx = -sx;
  z=cgetr(lx);
  hi=quickmulii(y+2,x+2,ly-2,lx-2);
  if (hi[2] < 0)
  {
    e++; garde=hi[lx];
    for (i=2; i<lx ; i++) z[i]=hi[i];
  }
  else
  {
    garde = (hi[lx] << 1);
    shift_left(z,hi,2,lx-1, garde, 1);
  }
  z[1]=evalsigne(sx) | e;
  if (garde < 0)
  { /* round to nearest */
    i=lx; do z[--i]++; while (z[i]==0);
    if (i==1) z[2]=HIGHBIT;
  }
  avma=(long)z; return z;
}

GEN
karamulrr(GEN x, GEN y, long flag)
{
  switch(flag)
  {
    case 1: return karamulrr1(x,y);
    case 2: return karamulrr2(x,y);
    default: err(flagerr,"karamulrr");
  }
  return NULL; /* not reached */
}

GEN
karamulir(GEN x, GEN y, long flag)
{
  long sx=signe(x),lz,i;
  GEN z,temp,z1;

  if (!sx) return gzero;
  lz=lg(y); z=cgetr(lz);
  temp=cgetr(lz+1); affir(x,temp);
  z1=karamulrr(temp,y,flag);
  for (i=1; i<lz; i++) z[i]=z1[i];
  avma=(long)z; return z;
}
#endif

#ifdef LONG_IS_64BIT

#if PARI_BYTE_ORDER == LITTLE_ENDIAN_64 || PARI_BYTE_ORDER == BIG_ENDIAN_64
#else
  error... unknown machine
#endif

GEN
dbltor(double x)
{
  GEN z = cgetr(3);
  long e;
  union { double f; ulong i; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */
  const int expo_len = 11; /* number of bits of exponent */
  LOCAL_HIREMAINDER;

  if (x==0) { z[1]=evalexpo(-308); z[2]=0; return z; }
  fi.f = x;
  e = evalexpo(((fi.i & (HIGHBIT-1)) >> mant_len) - exp_mid);
  z[1] = e | evalsigne(x<0? -1: 1);
  z[2] = (fi.i << expo_len) | HIGHBIT;
  return z;
}

double
rtodbl(GEN x)
{
  long ex,s=signe(x);
  ulong a;
  union { double f; ulong i; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */
  const int expo_len = 11; /* number of bits of exponent */
  LOCAL_HIREMAINDER;

  if (typ(x)==t_INT && !s) return 0.0;
  if (typ(x)!=t_REAL) err(typeer,"rtodbl");
  if (!s || (ex=expo(x)) < - exp_mid) return 0.0;

  /* start by rounding to closest */
  a = (x[2] & (HIGHBIT-1)) + 0x400;
  if (a & HIGHBIT) { ex++; a=0; }
  if (ex >= exp_mid) err(rtodber);
  fi.i = ((ex + exp_mid) << mant_len) | (a >> expo_len);
  if (s<0) fi.i |= HIGHBIT;
  return fi.f;
}

#else

#if   PARI_BYTE_ORDER == LITTLE_ENDIAN
#  define INDEX0 1
#  define INDEX1 0
#elif PARI_BYTE_ORDER == BIG_ENDIAN
#  define INDEX0 0
#  define INDEX1 1
#else
   error... unknown machine
#endif

GEN
dbltor(double x)
{
  GEN z;
  long e;
  union { double f; ulong i[2]; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */
  const int shift = mant_len-32;
  const int expo_len = 11; /* number of bits of exponent */

  if (x==0) { z=cgetr(3); z[1]=evalexpo(-308); z[2]=0; return z; }
  fi.f = x; z=cgetr(4);
  {
    const ulong a = fi.i[INDEX0];
    const ulong b = fi.i[INDEX1];
    e = evalexpo(((a & (HIGHBIT-1)) >> shift) - exp_mid);
    z[1] = e | evalsigne(x<0? -1: 1);
    z[3] = b << expo_len;
    z[2] = HIGHBIT | b >> (BITS_IN_LONG-expo_len) | (a << expo_len);
  }
  return z;
}

double
rtodbl(GEN x)
{
  long ex,s=signe(x),lx=lg(x);
  ulong a,b,k;
  union { double f; ulong i[2]; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */
  const int shift = mant_len-32;
  const int expo_len = 11; /* number of bits of exponent */

  if (typ(x)==t_INT && !s) return 0.0;
  if (typ(x)!=t_REAL) err(typeer,"rtodbl");
  if (!s || (ex=expo(x)) < - exp_mid) return 0.0;

  /* start by rounding to closest */
  a = x[2] & (HIGHBIT-1);
  if (lx > 3)
  {
    b = x[3] + 0x400UL; if (b < 0x400UL) a++;
    if (a & HIGHBIT) { ex++; a=0; }
  }
  else b = 0;
  if (ex > exp_mid) err(rtodber);
  ex += exp_mid;
  k = (a >> expo_len) | (ex << shift);
  if (s<0) k |= HIGHBIT;
  fi.i[INDEX0] = k;
  fi.i[INDEX1] = (a << (BITS_IN_LONG-expo_len)) | (b >> expo_len);
  return fi.f;
}
#endif

/* Old cgiv without reference count (which was not used anyway)
 * Should be a macro.
 */
void
cgiv(GEN x)
{
  if (x == (GEN) avma)
    avma = (long) (x+lg(x));
}

/********************************************************************/
/**                                                                **/
/**               INTEGER EXTENDED GCD  (AND INVMOD)               **/
/**                                                                **/
/********************************************************************/

/* GN 1998Oct25, originally developed in January 1998 under 2.0.4.alpha,
 * in the context of trying to improve elliptic curve cryptosystem attacking
 * algorithms.
 *
 * Two basic ideas - (1) avoid many integer divisions, especially when the
 * quotient is 1 (which happens more than 40% of the time).  (2) Use Lehmer's
 * trick as modified by Jebelean of extracting a couple of words' worth of
 * leading bits from both operands, and compute partial quotients from them
 * as long as we can be sure of their values.  The Jebelean modifications
 * consist in reliable inequalities from which we can decide fast whether
 * to carry on or to return to the outer loop, and in re-shifting after the
 * first word's worth of bits has been used up.  All of this is described
 * in R. Lercier's these [pp148-153 & 163f.], except his outer loop isn't
 * quite right  (the catch-up divisions needed when one partial quotient is
 * larger than a word are missing).
 *
 * The API is mpxgcd() below;  the single-word routines xgcduu and xxgcduu
 * may be called directly if desired;  lgcdii() probably doesn't make much
 * sense out of context.
 *
 * The whole lot is a factor 6 .. 8 faster on word-sized operands, and asym-
 * ptotically about a factor 2.5 .. 3, depending on processor architecture,
 * than the naive continued-division code.  Unfortunately, thanks to the
 * unrolled loops and all, the code is a bit lengthy.
 */

/*==================================
 * xgcduu(d,d1,f,v,v1,s)
 * xxgcduu(d,d1,f,u,u1,v,v1,s)
 *==================================*/
/*
 * Fast `final' extended gcd algorithm, acting on two ulongs.  Ideally this
 * should be replaced with assembler versions wherever possible.  The present
 * code essentially does `subtract, compare, and possibly divide' at each step,
 * which is reasonable when hardware division (a) exists, (b) is a bit slowish
 * and (c) does not depend a lot on the operand values (as on i486).  When
 * wordsize division is in fact an assembler routine based on subtraction,
 * this strategy may not be the most efficient one.
 *
 * xxgcduu() should be called with  d > d1 > 0, returns gcd(d,d1), and assigns
 * the usual signless cont.frac. recurrence matrix to [u, u1; v, v1]  (i.e.,
 * the product of all the [0, 1; 1 q_j] where the leftmost factor arises from
 * the quotient of the first division step),  and the information about the
 * implied signs to s  (-1 when an odd number of divisions has been done,
 * 1 otherwise).  xgcduu() is exactly the same except that u,u1 are not com-
 * puted (and not returned, of course).
 *
 * The input flag f should be set to 1 if we know in advance that gcd(d,d1)==1
 * (so we can stop the chain division one step early:  as soon as the remainder
 * equals 1).  Use this when you intend to use only what would be v, or only
 * what would be u and v, after that final division step, but not u1 and v1.
 * With the flag in force and thus without that final step, the interesting
 * quantity/ies will still sit in [u1 and] v1, of course.
 *
 * For computing the inverse of a single-word INTMOD known to exist, pass f=1
 * to xgcduu(), and obtain the result from s and v1.  (The routine does the
 * right thing when d1==1 already.)  For finishing a multiword modinv known
 * to exist, pass f=1 to xxgcduu(), and multiply the returned matrix  (with
 * properly adjusted signs)  onto the values v' and v1' previously obtained
 * from the multiword division steps.  Actually, just take the scalar product
 * of [v',v1'] with [u1,-v1], and change the sign if s==-1.  (If the final
 * step had been carried out, it would be [-u,v], and s would also change.)
 * For reducing a rational number to lowest terms, pass f=0 to xgcduu().
 * Finally, f=0 with xxgcduu() is useful for Bezout computations.
 * [Harrumph.  In the above prescription, the sign turns out to be precisely
 * wrong.]
 * (It is safe for inversemodulo() to call xgcduu() with f=1, because f&1
 * doesn't make a difference when gcd(d,d1)>1.  The speedup is negligible.)
 *
 * In principle, when gcd(d,d1) is known to be 1, it is straightforward to
 * recover the final u,u1 given only v,v1 and s.  However, it probably isn't
 * worthwhile, as it trades a few multiplications for a division.
 *
 * Note that these routines do not know and do not need to know about the
 * PARI stack.
 */

ulong
xgcduu(ulong d, ulong d1, int f, ulong* v, ulong* v1, long *s)
{
  ulong xv,xv1, xs, q,res;
  LOCAL_HIREMAINDER;

  /* The above blurb contained a lie.  The main loop always stops when d1
   * has become equal to 1.  If (d1 == 1 && !(f&1)) after the loop, we do
   * the final `division' of d by 1 `by hand' as it were.
   *
   * The loop has already been unrolled once.  Aggressive optimization could
   * well lead to a totally unrolled assembler version...
   *
   * On modern x86 architectures, this loop is a pig anyway.  The division
   * instruction always puts its result into the same pair of registers, and
   * we always want to use one of them straight away, so pipeline performance
   * will suck big time.  An assembler version should probably do a first loop
   * computing and storing all the quotients -- their number is bounded in
   * advance -- and then assembling the matrix in a second pass.  On other
   * architectures where we can cycle through four or so groups of registers
   * and exploit a fast ALU result-to-operand feedback path, this is much less
   * of an issue.  (Intel sucks.  See http://www.x86.org/ ...)
   */
  xs = res = 0;
  xv = 0UL; xv1 = 1UL;
  while (d1 > 1UL)
  {
    d -= d1;			/* no need to use subll */
    if (d >= d1)
    {
      hiremainder = 0; q = 1 + divll(d,d1); d = hiremainder;
      xv += q * xv1;
    }
    else
      xv += xv1;
				/* possible loop exit */
    if (d <= 1UL) { xs=1; break; }
				/* repeat with inverted roles */
    d1 -= d;
    if (d1 >= d)
    {
      hiremainder = 0; q = 1 + divll(d1,d); d1 = hiremainder;
      xv1 += q * xv;
    }
    else
      xv1 += xv;
  } /* while */

  if (!(f&1))			/* division by 1 postprocessing if needed */
  {
    if (xs && d==1)
    { xv1 += d1 * xv; xs = 0; res = 1UL; }
    else if (!xs && d1==1)
    { xv += d * xv1; xs = 1; res = 1UL; }
  }

  if (xs)
  {
    *s = -1; *v = xv1; *v1 = xv;
    return (res ? res : (d==1 ? 1UL : d1));
  }
  else
  {
    *s = 1; *v = xv; *v1 = xv1;
    return (res ? res : (d1==1 ? 1UL : d));
  }
}


ulong
xxgcduu(ulong d, ulong d1, int f,
       ulong* u, ulong* u1, ulong* v, ulong* v1, long *s)
{
  ulong xu,xu1, xv,xv1, xs, q,res;
  LOCAL_HIREMAINDER;

  xs = res = 0;
  xu = xv1 = 1UL;
  xu1 = xv = 0UL;
  while (d1 > 1UL)
  {
    d -= d1;			/* no need to use subll */
    if (d >= d1)
    {
      hiremainder = 0; q = 1 + divll(d,d1); d = hiremainder;
      xv += q * xv1;
      xu += q * xu1;
    }
    else
    { xv += xv1; xu += xu1; }
				/* possible loop exit */
    if (d <= 1UL) { xs=1; break; }
				/* repeat with inverted roles */
    d1 -= d;
    if (d1 >= d)
    {
      hiremainder = 0; q = 1 + divll(d1,d); d1 = hiremainder;
      xv1 += q * xv;
      xu1 += q * xu;
    }
    else
    { xv1 += xv; xu1 += xu; }
  } /* while */

  if (!(f&1))			/* division by 1 postprocessing if needed */
  {
    if (xs && d==1)
    {
      xv1 += d1 * xv;
      xu1 += d1 * xu;
      xs = 0; res = 1UL;
    }
    else if (!xs && d1==1)
    {
      xv += d * xv1;
      xu += d * xu1;
      xs = 1; res = 1UL;
    }
  }

  if (xs)
  {
    *s = -1; *u = xu1; *u1 = xu; *v = xv1; *v1 = xv;
    return (res ? res : (d==1 ? 1UL : d1));
  }
  else
  {
    *s = 1; *u = xu; *u1 = xu1; *v = xv; *v1 = xv1;
    return (res ? res : (d1==1 ? 1UL : d));
  }
}

/*==================================
 * lgcdii(d,d1,u,u1,v,v1)
 *==================================*/
/* Lehmer's partial extended gcd algorithm, acting on two t_INT GENs.
 *
 * Tries to determine, using the leading 2*BITS_IN_LONG significant bits of d
 * and a quantity of bits from d1 obtained by a shift of the same displacement,
 * as many partial quotients of d/d1 as possible, and assigns to [u,u1;v,v1]
 * the product of all the [0, 1; 1, q_j] thus obtained, where the leftmost
 * factor arises from the quotient of the first division step.
 *
 * MUST be called with  d > d1 > 0, and with  d  occupying more than one
 * significant word  (if it doesn't, the caller has no business with us;
 * he/she/it should use xgcduu() instead).  Returns the number of reduction/
 * swap steps carried out, possibly zero, or under certain conditions minus
 * that number.  When the return value is nonzero, the caller should use the
 * returned recurrence matrix to update its own copies of d,d1.  When the
 * return value is non-positive, and the latest remainder after updating
 * turns out to be nonzero, the caller should at once attempt a full division,
 * rather than first trying lgcdii() again -- this typically happens when we
 * are about to encounter a quotient larger than half a word.  (This is not
 * detected infallibly -- after a positive return value, it is perfectly
 * possible that the next stage will end up needing a full division.  After
 * a negative return value, however, this is certain, and should be acted
 * upon.)
 *
 * (The sign information, for which xgcduu() has its return argument s, is now
 * implicit in the LSB of our return value, and the caller may take advantage
 * of the fact that a return value of +-1 implies u==0,u1==v==1  [only v1 pro-
 * vides interesting information in this case].  One might also use the fact
 * that if the return value is +-2, then u==1, but this is rather marginal.)
 *
 * If it was not possible to determine even the first quotient, either because
 * we're too close to an integer quotient or because the quotient would be
 * larger than one word  (if the `leading digit' of d1 after shifting is all
 * zeros),  we return 0 and do not bother to assign anything to the last four
 * args.
 *
 * The division chain might (sometimes) even run to completion.  It will be
 * up to the caller to detect this case.
 *
 * This routine does _not_ change d or d1;  this will also be up to the caller.
 *
 * Note that this routine does not know and does not need to know about the
 * PARI stack.
 */
/*#define DEBUG_LEHMER 1 */
int
lgcdii(ulong* d, ulong* d1,
       ulong* u, ulong* u1, ulong* v, ulong* v1)
{
  /* Strategy:  (1) Extract/shift most significant bits.  We assume that d
   * has at least two significant words, but we can cope with a one-word d1.
   * Let dd,dd1 be the most significant dividend word and matching part of the
   * divisor.
   * (2) Check for overflow on the first division.  For our purposes, this
   * happens when the upper half of dd1 is zero.  (Actually this is detected
   * during extraction.)
   * (3) Get a fix on the first quotient.  We compute q = floor(dd/dd1), which
   * is an upper bound for floor(d/d1), and which gives the true value of the
   * latter if (and-almost-only-if) the remainder dd' = dd-q*dd1 is >= q.
   * (If it isn't, we give up.  This is annoying because the subsequent full
   * division will repeat some work already done, but it happens very infre-
   * quently.  Doing the extra-bit-fetch in this case would be awkward.)
   * (4) Finish initializations.
   *
   * The remainder of the action is comparatively boring... The main loop has
   * been unrolled once  (so we don't swap things and we can apply Jebelean's
   * termination conditions which alternatingly take two different forms during
   * successive iterations).  When we first run out of sufficient bits to form
   * a quotient, and have an extra word of each operand, we pull out two whole
   * word's worth of dividend bits, and divisor bits of matching significance;
   * to these we apply our partial matrix (disregarding overflow because the
   * result mod 2^(2*BITS_IN_LONG) will in fact give the correct values), and
   * re-extract one word's worth of the current dividend and a matching amount
   * of divisor bits.  The affair will normally terminate with matrix entries
   * just short of a whole word.  (We terminate the inner loop before these can
   * possibly overflow.)
   */
  ulong dd,dd1,ddlo,dd1lo, sh,shc;        /* `digits', shift count */
  ulong xu,xu1, xv,xv1, q,res;	/* recurrences, partial quotient, count */
  ulong tmp0,tmp1,tmp2,tmpd,tmpu,tmpv; /* temps */
  long ld, ld1, lz;		/* t_INT effective lengths */
  int skip = 0;			/* a boolean flag */
  LOCAL_OVERFLOW;
  LOCAL_HIREMAINDER;

#ifdef DEBUG_LEHMER
  voir(d, -1); voir(d1, -1);
#endif
  ld = lgefint(d); ld1 = lgefint(d1); lz = ld - ld1; /* >= 0 */
  if (lz > 1) return 0;		/* rare, quick and desperate exit */

  d += 2; d1 += 2;		/* point at the leading `digits' */
  dd1lo = 0;		        /* unless we find something better */
  sh = bfffo(*d);		/* obtain dividend left shift count */

  if (sh)
  {				/* do the shifting */
    shc = BITS_IN_LONG - sh;
    if (lz)
    {				/* dividend longer than divisor */
      dd1 = (*d1 >> shc);
      if (!(HIGHMASK & dd1)) return 0;  /* overflow detected */
      if (ld1 > 3)
        dd1lo = (*d1 << sh) + (d1[1] >> shc);
      else
        dd1lo = (*d1 << sh);
    }
    else
    {				/* dividend and divisor have the same length */
      /* dd1 = shiftl(d1,sh) would have left hiremainder==0, and dd1 != 0. */
      dd1 = (*d1 << sh);
      if (!(HIGHMASK & dd1)) return 0;
      if (ld1 > 3)
      {
        dd1 += (d1[1] >> shc);
        if (ld1 > 4)
          dd1lo = (d1[1] << sh) + (d1[2] >> shc);
        else
          dd1lo = (d1[1] << sh);
      }
    }
    /* following lines assume d to have 2 or more significant words */
    dd = (*d << sh) + (d[1] >> shc);
    if (ld > 4)
      ddlo = (d[1] << sh) + (d[2] >> shc);
    else
      ddlo = (d[1] << sh);
  }
  else
  {				/* no shift needed */
    if (lz) return 0;		/* div'd longer than div'r: o'flow automatic */
    dd1 = *d1;
    if (!(HIGHMASK & dd1)) return 0;
    if(ld1 > 3) dd1lo = d1[1];
    /* assume again that d has another significant word */
    dd = *d; ddlo = d[1];
  }
#ifdef DEBUG_LEHMER
  fprintf(stderr, "  %lx:%lx, %lx:%lx\n", dd, ddlo, dd1, dd1lo);
#endif

  /* First subtraction/division stage.  (If a subtraction initially suffices,
   * we don't divide at all.)  If a Jebelean condition is violated, and we
   * can't fix it even by looking at the low-order bits in ddlo,dd1lo, we
   * give up and ask for a full division.  Otherwise we commit the result,
   * possibly deciding to re-shift immediately afterwards.
   */
  dd -= dd1;
  if (dd < dd1)
  {				/* first quotient known to be == 1 */
    xv1 = 1UL;
    if (!dd)			/* !(Jebelean condition), extraspecial case */
    {				/* note this can actually happen...  Now
    				 * q==1 is known, but we underflow already.
				 * OTOH we've just shortened d by a whole word.
				 * Thus we feel pleased with ourselves and
				 * return.  (The re-shift code below would
				 * do so anyway.) */
      *u = 0; *v = *u1 = *v1 = 1UL;
      return -1;		/* Next step will be a full division. */
    } /* if !(Jebelean) then */
  }
  else
  {				/* division indicated */
    hiremainder = 0;
    xv1 = 1 + divll(dd, dd1);	/* xv1: alternative spelling of `q', here ;) */
    dd = hiremainder;
    if (dd < xv1)		/* !(Jebelean cond'), non-extra special case */
    {				/* Attempt to complete the division using the
				 * less significant bits, before skipping right
				 * past the 1st loop to the reshift stage. */
      ddlo = subll(ddlo, mulll(xv1, dd1lo));
      dd = subllx(dd, hiremainder);

      /* If we now have an overflow, q was _certainly_ too large.  Thanks to
       * our decision not to get here unless the original dd1 had bits set in
       * the upper half of the word, however, we now do know that the correct
       * quotient is in fact q-1.  Adjust our data accordingly. */
      if (overflow)
      {
	xv1--;
	ddlo = addll(ddlo,dd1lo);
	dd = addllx(dd,dd1);	/* overflows again which cancels the borrow */
	/* ...and fall through to skip=1 below */
      }
      else
      /* Test Jebelean condition anew, at this point using _all_ the extracted
       * bits we have.  This is clutching at straws; we have a more or less
       * even chance of succeeding this time.  Note that if we fail, we really
       * do not know whether the correct quotient would have been q or some
       * smaller value. */
	if (!dd && ddlo < xv1) return 0;

      /* Otherwise, we now know that q is correct, but we cannot go into the
       * 1st loop.  Raise a flag so we'll remember to skip past the loop.
       * Get here also after the q-1 adjustment case. */
      skip = 1;
    } /* if !(Jebelean) then */
  }
  xu = 0; xv = xu1 = 1UL; res = 1;
#ifdef DEBUG_LEHMER
  fprintf(stderr, "  q = %ld, %lx, %lx\n", xv1, dd1, dd);
#endif

  /* Some invariants from here across the first loop:
   *
   * At this point, and again after we are finished with the first loop and
   * subsequent conditional, a division and the associated update of the
   * recurrence matrix have just been carried out completely.  The matrix
   * xu,xu1;xv,xv1 has been initialized (or updated, possibly with permuted
   * columns), and the current remainder == next divisor (dd at the moment)
   * is nonzero (it might be zero here, but then skip will have been set).
   *
   * After the first loop, or when skip is set already, it will also be the
   * case that there aren't sufficiently many bits to continue without re-
   * shifting.  If the divisor after reshifting is zero, or indeed if it
   * doesn't have more than half a word's worth of bits, we will have to
   * return at that point.  Otherwise, we proceed into the second loop.
   *
   * Furthermore, when we reach the re-shift stage, dd:ddlo and dd1:dd1lo will
   * already reflect the result of applying the current matrix to the old
   * ddorig:ddlo and dd1orig:dd1lo.  (For the first iteration above, this
   * was easy to achieve, and we didn't even need to peek into the (now
   * no longer existent!) saved words.  After the loop, we'll stop for a
   * moment to merge in the ddlo,dd1lo contributions.)
   *
   * Note that after the first division, even an a priori quotient of 1 cannot
   * be trusted until we've checked Jebelean's condition -- it cannot be too
   * large, of course, but it might be too small.
   */

  if (!skip)
  {
    while (1)
    {
      /* First half of loop divides dd into dd1, and leaves the recurrence
       * matrix xu,...,xv1 groomed the wrong way round (xu,xv will be the newer
       * entries) when successful. */
      tmpd = dd1 - dd;
      if (tmpd < dd)
      {				/* quotient suspected to be 1 */
#ifdef DEBUG_LEHMER
	q = 1;
#endif
	tmpu = xu + xu1;	/* cannot overflow -- everything bounded by
				 * the original dd during first loop */
	tmpv = xv + xv1;
      }
      else
      {				/* division indicated */
	hiremainder = 0;
	q = 1 + divll(tmpd, dd);
	tmpd = hiremainder;
	tmpu = xu + q*xu1;	/* can't overflow, but may need to be undone */
	tmpv = xv + q*xv1;
      }

      tmp0 = addll(tmpv, xv1);
      if ((tmpd < tmpu) || overflow ||
	  (dd - tmpd < tmp0))	/* !(Jebelean cond.) */
	break;			/* skip ahead to reshift stage */
      else
      {				/* commit dd1, xu, xv */
	res++;
	dd1 = tmpd; xu = tmpu; xv = tmpv;
#ifdef DEBUG_LEHMER
	fprintf(stderr, "  q = %ld, %lx, %lx [%lu,%lu;%lu,%lu]\n",
		q, dd, dd1, xu1, xu, xv1, xv);
#endif
      }

      /* Second half of loop divides dd1 into dd, and the matrix returns to its
       * normal arrangement. */
      tmpd = dd - dd1;
      if (tmpd < dd1)
      {				/* quotient suspected to be 1 */
#ifdef DEBUG_LEHMER
	q = 1;
#endif
	tmpu = xu1 + xu;	/* cannot overflow */
	tmpv = xv1 + xv;
      }
      else
      {				/* division indicated */
	hiremainder = 0;
	q = 1 + divll(tmpd, dd1);
	tmpd = hiremainder;
	tmpu = xu1 + q*xu;
	tmpv = xv1 + q*xv;
      }

      tmp0 = addll(tmpu, xu);
      if ((tmpd < tmpv) || overflow ||
	  (dd1 - tmpd < tmp0))	/* !(Jebelean cond.) */
	break;			/* skip ahead to reshift stage */
      else
      {				/* commit dd, xu1, xv1 */
	res++;
	dd = tmpd; xu1 = tmpu; xv1 = tmpv;
#ifdef DEBUG_LEHMER
	fprintf(stderr, "  q = %ld, %lx, %lx [%lu,%lu;%lu,%lu]\n",
		q, dd1, dd, xu, xu1, xv, xv1);
#endif
      }

    } /* end of first loop */

    /* Intermezzo: update dd:ddlo, dd1:dd1lo.  (But not if skip is set.) */

    if (res&1)
    {
      /* after failed division in 1st half of loop:
       * [dd1:dd1lo,dd:ddlo] = [ddorig:ddlo,dd1orig:dd1lo]
       *                       * [ -xu, xu1 ; xv, -xv1 ]
       * (Actually, we only multiply [ddlo,dd1lo] onto the matrix and
       * add the high-order remainders + overflows onto [dd1,dd].)
       */
      tmp1 = mulll(ddlo, xu); tmp0 = hiremainder;
      tmp1 = subll(mulll(dd1lo,xv), tmp1);
      dd1 += subllx(hiremainder, tmp0);
      tmp2 = mulll(ddlo, xu1); tmp0 = hiremainder;
      ddlo = subll(tmp2, mulll(dd1lo,xv1));
      dd += subllx(tmp0, hiremainder);
      dd1lo = tmp1;
    }
    else
    {
      /* after failed division in 2nd half of loop:
       * [dd:ddlo,dd1:dd1lo] = [ddorig:ddlo,dd1orig:dd1lo]
       *                       * [ xu1, -xu ; -xv1, xv ]
       * (Actually, we only multiply [ddlo,dd1lo] onto the matrix and
       * add the high-order remainders + overflows onto [dd,dd1].)
       */
      tmp1 = mulll(ddlo, xu1); tmp0 = hiremainder;
      tmp1 = subll(tmp1, mulll(dd1lo,xv1));
      dd += subllx(tmp0, hiremainder);
      tmp2 = mulll(ddlo, xu); tmp0 = hiremainder;
      dd1lo = subll(mulll(dd1lo,xv), tmp2);
      dd1 += subllx(hiremainder, tmp0);
      ddlo = tmp1;
    }
#ifdef DEBUG_LEHMER
    fprintf(stderr, "  %lx:%lx, %lx:%lx\n", dd, ddlo, dd1, dd1lo);
#endif
  } /* end of skip-pable section:  get here also, with res==1, when there
     * was a problem immediately after the very first division. */

  /* Re-shift.  Note:  the shift count _can_ be zero, viz. under the following
   * precise conditions:  The original dd1 had its topmost bit set, so the 1st
   * q was 1, and after subtraction, dd had its topmost bit unset.  If now
   * dd==0, we'd have taken the return exit already, so we couldn't have got
   * here.  If not, then it must have been the second division which has gone
   * amiss  (because dd1 was very close to an exact multiple of the remainder
   * dd value, so this will be very rare).  At this point, we'd have a fairly
   * slim chance of fixing things by re-examining dd1:dd1lo vs. dd:ddlo, but
   * this is not guaranteed to work.  Instead of trying, we return at once.
   * The caller will see to it that the initial subtraction is re-done using
   * _all_ the bits of both operands, which already helps, and the next round
   * will either be a full division  (if dd occupied a halfword or less),  or
   * another llgcdii() first step.  In the latter case, since we try a little
   * harder during our first step, we may actually be able to fix the problem,
   * and get here again with improved low-order bits and with another step
   * under our belt.  Otherwise we'll have given up above and forced a full-
   * blown division.
   *
   * If res is even, the shift count _cannot_ be zero.  (The first step forces
   * a zero into the remainder's MSB, and all subsequent remainders will have
   * inherited it.)
   *
   * The re-shift stage exits if the next divisor has at most half a word's
   * worth of bits.
   *
   * For didactic reasons, the second loop will be arranged in the same way
   * as the first -- beginning with the division of dd into dd1, as if res
   * was odd.  To cater for this, if res is actually even, we swap things
   * around during reshifting.  (During the second loop, the parity of res
   * does not matter;  we know in which half of the loop we are when we decide
   * to return.)
   */
#ifdef DEBUG_LEHMER
  fprintf(stderr, "(sh)");
#endif

  if (res&1)
  {				/* after odd number of division(s) */
    if (dd1 && (sh = bfffo(dd1)))
    {
      shc = BITS_IN_LONG - sh;
      dd = (ddlo >> shc) + (dd << sh);
      if (!(HIGHMASK & dd))
      {
	*u = xu; *u1 = xu1; *v = xv; *v1 = xv1;
	return -res;		/* full division asked for */
      }
      dd1 = (dd1lo >> shc) + (dd1 << sh);
    }
    else
    {				/* time to return: <= 1 word left, or sh==0 */
      *u = xu; *u1 = xu1; *v = xv; *v1 = xv1;
      return res;
    }
  }
  else
  {				/* after even number of divisions */
    if (dd)
    {
      sh = bfffo(dd);		/* Known to be positive. */
      shc = BITS_IN_LONG - sh;
				/* dd:ddlo will become the new dd1, and v.v. */
      tmpd = (ddlo >> shc) + (dd << sh);
      dd = (dd1lo >> shc) + (dd1 << sh);
      dd1 = tmpd;
      /* This has completed the swap;  now dd is again the current divisor.
       * The following test originally inspected dd1 -- a most subtle and
       * most annoying bug. The Management. */
      if (HIGHMASK & dd)
      {
	/* recurrence matrix is the wrong way round;  swap it. */
	tmp0 = xu; xu = xu1; xu1 = tmp0;
	tmp0 = xv; xv = xv1; xv1 = tmp0;
      }
      else
      {
	/* recurrence matrix is the wrong way round;  fix this. */
	*u = xu1; *u1 = xu; *v = xv1; *v1 = xv;
	return -res;		/* full division asked for */
      }
    }
    else
    {				/* time to return: <= 1 word left */
      *u = xu1; *u1 = xu; *v = xv1; *v1 = xv;
      return res;
    }
  } /* end reshift */

#ifdef DEBUG_LEHMER
  fprintf(stderr, "  %lx:%lx, %lx:%lx\n", dd, ddlo, dd1, dd1lo);
#endif

  /* The Second Loop.  Rip-off of the first, but we now check for overflow
   * in the recurrences.  Returns instead of breaking when we cannot fix the
   * quotient any longer.
   */

  for(;;)
  {
    /* First half of loop divides dd into dd1, and leaves the recurrence
     * matrix xu,...,xv1 groomed the wrong way round (xu,xv will be the newer
     * entries) when successful. */
    tmpd = dd1 - dd;
    if (tmpd < dd)
    {				/* quotient suspected to be 1 */
#ifdef DEBUG_LEHMER
      q = 1;
#endif
      tmpu = xu + xu1;
      tmpv = addll(xv, xv1);	/* xv,xv1 will overflow first */
      tmp1 = overflow;
    }
    else
    {				/* division indicated */
      hiremainder = 0;
      q = 1 + divll(tmpd, dd);
      tmpd = hiremainder;
      tmpu = xu + q*xu1;
      tmpv = addll(xv, mulll(q,xv1));
      tmp1 = overflow | hiremainder;
    }

    tmp0 = addll(tmpv, xv1);
    if ((tmpd < tmpu) || overflow || tmp1 ||
	(dd - tmpd < tmp0))	/* !(Jebelean cond.) */
    {
      /* The recurrence matrix has not yet been warped... */
      *u = xu; *u1 = xu1; *v = xv; *v1 = xv1;
      return res;
    }
    else
    {				/* commit dd1, xu, xv */
      res++;
      dd1 = tmpd; xu = tmpu; xv = tmpv;
#ifdef DEBUG_LEHMER
      fprintf(stderr, "  q = %ld, %lx, %lx\n", q, dd, dd1);
#endif
    }

    /* Second half of loop divides dd1 into dd, and the matrix returns to its
     * normal arrangement. */
    tmpd = dd - dd1;
    if (tmpd < dd1)
    {				/* quotient suspected to be 1 */
#ifdef DEBUG_LEHMER
      q = 1;
#endif
      tmpu = xu1 + xu;
      tmpv = addll(xv1, xv);
      tmp1 = overflow;
    }
    else
    {				/* division indicated */
      hiremainder = 0;
      q = 1 + divll(tmpd, dd1);
      tmpd = hiremainder;
      tmpu = xu1 + q*xu;
      tmpv = addll(xv1, mulll(q, xv));
      tmp1 = overflow | hiremainder;
    }

    tmp0 = addll(tmpu, xu);
    if ((tmpd < tmpv) || overflow || tmp1 ||
	(dd1 - tmpd < tmp0))	/* !(Jebelean cond.) */
    {
      /* The recurrence matrix has not yet been unwarped, so it is
       * the wrong way round;  fix this. */
      *u = xu1; *u1 = xu; *v = xv1; *v1 = xv;
      return res;
    }
    else
    {				/* commit dd, xu1, xv1 */
      res++;
      dd = tmpd; xu1 = tmpu; xv1 = tmpv;
#ifdef DEBUG_LEHMER
      fprintf(stderr, "  q = %ld, %lx, %lx\n", q, dd1, dd);
#endif
    }

  } /* end of second loop */

  return(0);			/* never reached */
}

/*==================================
 * invmod(a,b,res)
 *==================================
 *    If a is invertible, return 1, and set res  = a^{ -1 }
 *    Otherwise, return 0, and set res = gcd(a,b)

 * Temporary - to be replaced with mpxgcd()
 * I think we won't need to change much ... just the parameter-passing and
 * return value conventions, and computing a final u in addition to a final
 * v value before returning (and doing so even when the gcd isn't 1)
 */

#define mysetsigne(d,s) { fprintferr("%ld %ld\n",s,signe(d)); if (signe(d)==-(s)) setsigne(d,s); }

int
invmod(GEN a, GEN b, GEN *res)
{
  GEN v,v1,d,d1,q,r;
  long av,av1,lim;
  long s;
  ulong g;
  ulong xu,xu1,xv,xv1;		/* Lehmer stage recurrence matrix */
  int lhmres;			/* Lehmer stage return value */

  if (typ(a) != t_INT || typ(b) != t_INT) err(arither1);
  if (!signe(b)) { *res=absi(a); return 0; }
  av = avma;
  if (lgefint(b) == 3) /* single-word affair */
  {
    d1 = modiu(a, (ulong)b[2]);
    if (d1 == gzero)
    {
      if (b[2] == 1L)
        { *res = gzero; return 1; }
      else
        { *res = absi(b); return 0; }
    }
    g = xgcduu((ulong)b[2], (ulong)d1[2], 1, &xv, &xv1, &s);
#ifdef DEBUG_LEHMER
    fprintferr(" <- %lu,%lu\n", (ulong)b[2], (ulong)d1[2]);
    fprintferr(" -> %lu,%ld,%lu; %lx\n", g,s,xv1,avma);
#endif
    avma = av;
    if (g != 1UL) { *res = utoi(g); return 0; }
    xv = xv1 % (ulong)b[2]; if (s < 0) xv = ((ulong)b[2]) - xv;
    *res = utoi(xv); return 1;
  }

  (void)new_chunk(lgefint(b));
  d = absi(b); d1 = modii(a,d);

  v=gzero; v1=gun;	/* general case */
#ifdef DEBUG_LEHMER
  fprintferr("INVERT: -------------------------\n");
  output(d1);
#endif
  av1 = avma; lim = stack_lim(av,1);

  while (lgefint(d) > 3 && signe(d1))
  {
#ifdef DEBUG_LEHMER
    fprintferr("Calling Lehmer:\n");
#endif
    lhmres = lgcdii((ulong*)d, (ulong*)d1, &xu, &xu1, &xv, &xv1);
    if (lhmres != 0)		/* check progress */
    {				/* apply matrix */
#ifdef DEBUG_LEHMER
      fprintferr("Lehmer returned %d [%lu,%lu;%lu,%lu].\n",
	      lhmres, xu, xu1, xv, xv1);
#endif
      if ((lhmres == 1) || (lhmres == -1))
      {
	if (xv1 == 1)
	{
	  r = subii(d,d1); d=d1; d1=r;
	  a = subii(v,v1); v=v1; v1=a;
	}
	else
	{
	  r = subii(d, mului(xv1,d1)); d=d1; d1=r;
	  a = subii(v, mului(xv1,v1)); v=v1; v1=a;
	}
      }
      else
      {
	r  = subii(muliu(d,xu),  muliu(d1,xv));
	a  = subii(muliu(v,xu),  muliu(v1,xv));
	d1 = subii(muliu(d,xu1), muliu(d1,xv1)); d = r;
	v1 = subii(muliu(v,xu1), muliu(v1,xv1)); v = a;
        if (lhmres&1) {
          setsigne(d,-signe(d));
          setsigne(v,-signe(v));
        }
        else {
          setsigne(d1,-signe(d1));
          setsigne(v1,-signe(v1));
        }
      }
    }
#ifdef DEBUG_LEHMER
    else
      fprintferr("Lehmer returned 0.\n");
    output(d); output(d1); output(v); output(v1);
    sleep(1);
#endif

    if (lhmres <= 0 && signe(d1))
    {
      q = dvmdii(d,d1,&r);
#ifdef DEBUG_LEHMER
      fprintferr("Full division:\n");
      printf("  q = "); output(q); sleep (1);
#endif
      a = subii(v,mulii(q,v1));
      v=v1; v1=a;
      d=d1; d1=r;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[4]; gptr[0]=&d; gptr[1]=&d1; gptr[2]=&v; gptr[3]=&v1;
      if(DEBUGMEM>1) err(warnmem,"invmod");
      gerepilemany(av1,gptr,4);
    }
  } /* end while */

  /* Postprocessing - final sprint */
  if (signe(d1))
  {
    /* Assertions: lgefint(d)==lgefint(d1)==3, and
     * gcd(d,d1) is nonzero and fits into one word
     */
    g = xxgcduu(d[2], d1[2], 1, &xu, &xu1, &xv, &xv1, &s);
#ifdef DEBUG_LEHMER
    output(d);output(d1);output(v);output(v1);
    fprintferr(" <- %lu,%lu\n", (ulong)d[2], (ulong)d1[2]);
    fprintferr(" -> %lu,%ld,%lu; %lx\n", g,s,xv1,avma);
#endif
    if (g != 1UL) { avma = av; *res = utoi(g); return 0; }
    /* (From the xgcduu() blurb:)
     * For finishing the multiword modinv, we now have to multiply the
     * returned matrix  (with properly adjusted signs)  onto the values
     * v' and v1' previously obtained from the multiword division steps.
     * Actually, it is sufficient to take the scalar product of [v',v1']
     * with [u1,-v1], and change the sign if s==1.
     */
    v = subii(muliu(v,xu1),muliu(v1,xv1));
    if (s > 0) setsigne(v,-signe(v));
    avma = av; *res = modii(v,b);
#ifdef DEBUG_LEHMER
    output(*res); fprintfderr("============================Done.\n");
    sleep(1);
#endif
    return 1;
  }
  /* get here when the final sprint was skipped (d1 was zero already) */
  avma = av;
  if (!egalii(d,gun)) { *res = icopy(d); return 0; }
  *res = modii(v,b);
#ifdef DEBUG_LEHMER
  output(*res); fprintferr("============================Done.\n");
  sleep(1);
#endif
  return 1;
}
