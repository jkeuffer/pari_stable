/***********************************************************************/
/**                                                                   **/
/**               ARITHMETIC OPERATIONS ON POLYNOMIALS                **/
/**                         (third part)                              **/
/**                                                                   **/
/***********************************************************************/
/* $Id$ */
#include "pari.h"

/*******************************************************************/
/*                                                                 */
/*                  KARATSUBA (for polynomials)                    */
/*                                                                 */
/*******************************************************************/
#define swapspec(x,y, nx,ny) {long _a=nx;GEN _z=x; nx=ny; ny=_a; x=y; y=_z;}

#if 1 /* for tunings */
long SQR_LIMIT = 6;
long MUL_LIMIT = 10;

void
setsqpol(long a) { SQR_LIMIT=a; }
void
setmulpol(long a) { MUL_LIMIT=a; }

GEN
specpol(GEN x, long nx)
{
  GEN z = cgetg(nx+2,t_POL);
  long i;
  for (i=0; i<nx; i++) z[i+2] = x[i];
  z[1]=evalsigne(1)|evallgef(nx+2);
  return z;
}
#else
#  define SQR_LIMIT 6
#  define MUL_LIMIT 10
#endif

static GEN
addpol(GEN x, GEN y, long lx, long ly)
{
  long i,lz;
  GEN z;

  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx+2; z = cgetg(lz,t_POL) + 2;
  for (i=0; i<ly; i++) z[i]=ladd((GEN)x[i],(GEN)y[i]);
  for (   ; i<lx; i++) z[i]=x[i];
  z -= 2; z[1]=0; return normalizepol_i(z, lz);
}

static GEN
addpolcopy(GEN x, GEN y, long lx, long ly)
{
  long i,lz;
  GEN z;

  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx+2; z = cgetg(lz,t_POL) + 2;
  for (i=0; i<ly; i++) z[i]=ladd((GEN)x[i],(GEN)y[i]);
  for (   ; i<lx; i++) z[i]=lcopy((GEN)x[i]);
  z -= 2; z[1]=0; return normalizepol_i(z, lz);
}

#ifdef INLINE
INLINE
#endif
GEN
mulpol_limb(GEN x, GEN y, char *ynonzero, long a, long b)
{
  GEN p1 = NULL;
  long i,av = avma;
  for (i=a; i<b; i++)
    if (ynonzero[i]) 
    {
      GEN p2 = gmul((GEN)y[i],(GEN)x[-i]);
      p1 = p1 ? gadd(p1, p2): p2;
    }
  return p1 ? gerepileupto(av, p1): gzero;
}

static GEN
mulpol(GEN x, GEN y, long nx, long ny)
{
  long i,lz,nz;
  GEN z;
  char *p1;

  if (!ny) return zeropol(0);
  lz = nx+ny+1; nz = lz-2;
  z = cgetg(lz, t_POL) + 2; /* x:y:z [i] = term of degree i */
  p1 = gpmalloc(ny);
  for (i=0; i<ny; i++)
  {
    p1[i] = !isexactzero((GEN)y[i]);
    z[i] = (long)mulpol_limb(x+i,y,p1,0,i+1);
  }
  for (  ; i<nx; i++) z[i] = (long)mulpol_limb(x+i,y,p1,0,ny);
  for (  ; i<nz; i++) z[i] = (long)mulpol_limb(x+i,y,p1,i-nx+1,ny);
  free(p1); z -= 2; z[1]=0; return normalizepol_i(z, lz);
}

/* return (x * X^d) + y. Assume d > 0, x > 0 and y >= 0 */
GEN
addshiftw(GEN x, GEN y, long d)
{
  GEN xd,yd,zd = (GEN)avma;
  long a,lz,ny = lgef(y)-2, nx = lgef(x)-2;

  x += 2; y += 2; a = ny-d;
  if (a <= 0)
  {
    lz = (a>nx)? ny+2: nx+d+2;
    (void)new_chunk(lz); xd = x+nx; yd = y+ny;
    while (xd > x) *--zd = *--xd;
    x = zd + a;
    while (zd > x) *--zd = zero;
  }
  else
  {
    xd = new_chunk(d); yd = y+d;
    x = addpol(x,yd, nx,a);
    lz = (a>nx)? ny+2: lgef(x)+d;
    x += 2; while (xd > x) *--zd = *--xd;
  }
  while (yd > y) *--zd = *--yd;
  *--zd = evalsigne(1) | evallgef(lz);
  *--zd = evaltyp(t_POL) | evallg(lz); return zd;
}

GEN
addshiftpol(GEN x, GEN y, long d)
{
  long v = varn(x);
  if (!signe(x)) return y;
  x = addshiftw(x,y,d);
  setvarn(x,v); return x;
}

/* as above, producing a clean stack */
static GEN
addshiftwcopy(GEN x, GEN y, long d)
{
  GEN xd,yd,zd = (GEN)avma;
  long a,lz,ny = lgef(y)-2, nx = lgef(x)-2;

  x += 2; y += 2; a = ny-d;
  if (a <= 0)
  {
    lz = nx+d+2;
    (void)new_chunk(lz); xd = x+nx; yd = y+ny;
    while (xd > x) *--zd = lcopy((GEN)*--xd);
    x = zd + a;
    while (zd > x) *--zd = zero;
  }
  else
  {
    xd = new_chunk(d); yd = y+d;
    x = addpolcopy(x,yd, nx,a);
    lz = (a>nx)? ny+2: lgef(x)+d;
    x += 2; while (xd > x) *--zd = *--xd;
  }
  while (yd > y) *--zd = lcopy((GEN)*--yd);
  *--zd = evalsigne(1) | evallgef(lz);
  *--zd = evaltyp(t_POL) | evallg(lz); return zd;
}

/* fast product (Karatsuba) of polynomials a,b. These are not real GENs, a+2,
 * b+2 were sent instead. na, nb = number of terms of a, b.
 * Only c, c0, c1, c2 are genuine GEN.
 */
GEN
quickmul(GEN a, GEN b, long na, long nb)
{
  GEN a0,c,c0;
  long av,n0,n0a,i;

  if (na < nb) swapspec(a,b, na,nb);
  if (nb < MUL_LIMIT) return mulpol(a,b,na,nb);
  i=(na>>1); n0=na-i; na=i;
  av=avma; a0=a+n0; n0a=n0;
  while (n0a && isexactzero((GEN)a[n0a-1])) n0a--;

  if (nb > n0)
  {
    GEN b0,c1,c2;
    long n0b;

    nb -= n0; b0 = b+n0; n0b = n0;
    while (n0b && isexactzero((GEN)b[n0b-1])) n0b--;
    c = quickmul(a,b,n0a,n0b);
    c0 = quickmul(a0,b0, na,nb);

    c2 = addpol(a0,a, na,n0a);
    c1 = addpol(b0,b, nb,n0b);

    c1 = quickmul(c1+2,c2+2, lgef(c1)-2,lgef(c2)-2);
    c2 = gneg_i(gadd(c0,c));
    c0 = addshiftw(c0, gadd(c1,c2), n0);
  }
  else
  {
    c = quickmul(a,b,n0a,nb);
    c0 = quickmul(a0,b,na,nb);
  }
  c0 = addshiftwcopy(c0,c,n0);
  return gerepileupto(av,c0);
}

GEN
sqrpol(GEN x, long nx)
{
  long av,i,j,l,lz,nz;
  GEN p1,z;
  char *p2;

  if (!nx) return zeropol(0);
  lz = (nx << 1) + 1, nz = lz-2;
  z = cgetg(lz,t_POL) + 2;
  p2 = gpmalloc(nx);
  for (i=0; i<nx; i++)
  {
    p2[i] = !isexactzero((GEN)x[i]);
    p1=gzero; av=avma; l=(i+1)>>1;
    for (j=0; j<l; j++)
      if (p2[j] && p2[i-j])
        p1 = gadd(p1, gmul((GEN)x[j],(GEN)x[i-j]));
    p1 = gshift(p1,1);
    if ((i&1) == 0 && p2[i>>1])
      p1 = gadd(p1, gsqr((GEN)x[i>>1]));
    z[i] = lpileupto(av,p1);
  }
  for (  ; i<nz; i++)
  {
    p1=gzero; av=avma; l=(i+1)>>1;
    for (j=i-nx+1; j<l; j++)
      if (p2[j] && p2[i-j])
        p1 = gadd(p1, gmul((GEN)x[j],(GEN)x[i-j]));
    p1 = gshift(p1,1);
    if ((i&1) == 0 && p2[i>>1])
      p1 = gadd(p1, gsqr((GEN)x[i>>1]));
    z[i] = lpileupto(av,p1);
  }
  free(p2); z -= 2; z[1]=0; return normalizepol_i(z,lz);
}

GEN
quicksqr(GEN a, long na)
{
  GEN a0,c,c0,c1;
  long av,n0,n0a,i;

  if (na<SQR_LIMIT) return sqrpol(a,na);
  i=(na>>1); n0=na-i; na=i;
  av=avma; a0=a+n0; n0a=n0;
  while (n0a && isexactzero((GEN)a[n0a-1])) n0a--;

  c = quicksqr(a,n0a);
  c0 = quicksqr(a0,na);
  c1 = gmul2n(quickmul(a0,a, na,n0a), 1);
  c0 = addshiftw(c0,c1, n0);
  c0 = addshiftwcopy(c0,c,n0);
  return gerepileupto(av,c0);
}

/* x,pol in Z[X], p in Z, n in N, compute lift(x^n mod (p, pol)) */
GEN
Fp_pow_mod_pol(GEN x, GEN n, GEN pol, GEN p)
{
  long m,i,j,av=avma, lim=stack_lim(av,1), vx = varn(x);
  GEN p1 = n+2, y = x, z;
  if (!signe(n)) return polun[vx];
  if (is_pm1(n)) return gcopy(x);
  m = *p1;
  j=1+bfffo(m); m<<=j; j = BITS_IN_LONG-j;
  for (i=lgefint(n)-2;;)
  {
    for (; j; m<<=1,j--)
    {
      z = quicksqr(y+2, lgef(y)-2);
      y = Fp_pol_red(z, p);
      y = Fp_res(y,pol, p);
      if (low_stack(lim, stack_lim(av,1)))
      {
        if(DEBUGMEM>1) err(warnmem,"[1]: Fp_pow_mod_pol");
        y = gerepileupto(av, y);
      }
      if (m<0)
      {
        z = quickmul(y+2, x+2, lgef(y)-2, lgef(x)-2);
        y = Fp_pol_red(z, p);
        y = Fp_res(y,pol, p);
      }
      if (low_stack(lim, stack_lim(av,1)))
      {
        if(DEBUGMEM>1) err(warnmem,"[2]: Fp_pow_mod_pol");
        y = gerepileupto(av, y);
      }
    }
    if (--i == 0) break;
    m = *++p1, j = BITS_IN_LONG;
  }
  setvarn(y,vx); return gerepileupto(av,y);
}

int ff_poltype(GEN *x, GEN *p, GEN *pol);

/* z in Z[X], return z * Mod(1,p), normalized*/
GEN
Fp_pol(GEN z, GEN p)
{
  long i,l = lgef(z);
  GEN a,x = cgetg(l,t_POL);
  if (isonstack(p)) p = icopy(p);
  for (i=2; i<l; i++)
  {
    a = cgetg(3,t_INTMOD); x[i] = (long)a;
    a[1] = (long)p;
    a[2] = lmodii((GEN)z[i],p);
  }
  x[1] = z[1]; return normalizepol_i(x,l);
}

/* z in Z^n, return z * Mod(1,p), normalized*/
GEN
Fp_vec(GEN z, GEN p)
{
  long i,l = lg(z);
  GEN a,x = cgetg(l,typ(z));
  if (isonstack(p)) p = icopy(p);
  for (i=1; i<l; i++)
  {
    a = cgetg(3,t_INTMOD); x[i] = (long)a;
    a[1] = (long)p;
    a[2] = lmodii((GEN)z[i],p);
  }
  return x;
}

/* z in Z[X], return lift(z * Mod(1,p)), normalized*/
GEN
Fp_pol_red(GEN z, GEN p)
{
  long i,l = lgef(z);
  GEN x = cgetg(l,t_POL);
  for (i=2; i<l; i++) x[i] = lmodii((GEN)z[i],p);
  x[1] = z[1]; return normalizepol_i(x,l);
}

/* z in Z^n, return lift(z * Mod(1,p)) */
GEN
Fp_vec_red(GEN z, GEN p)
{
  long i,l = lg(z);
  GEN x = cgetg(l,typ(z));
  for (i=1; i<l; i++) x[i] = lmodii((GEN)z[i],p);
  return x;
}

/* no garbage collection, divide by leading coeff, mod p */
GEN
normalize_mod_p(GEN z, GEN p)
{
  long l = lgef(z)-1;
  GEN p1 = (GEN)z[l]; /* leading term */
  if (gcmp1(p1)) return z;
  z = gmul(z, mpinvmod(p1,p));
  return Fp_pol_red(z, p);
}

/* as above, p is guaranteed small, and coeffs of z are C longs in [0,p-1],
 * coeffs are in z[0..l-1] (instead of z[2] for regular pols)
 * Set varn(z) = 0
 */
GEN
Fp_pol_small(GEN z, GEN p, long l)
{
  long i;
  GEN a,x = cgetg(l,t_POL);
  if (isonstack(p)) p = icopy(p);
  if (is_bigint(p)) err(talker, "not a small prime in Fp_pol_small");
  z -= 2;
  for (i=2; i<l; i++) {
    a = cgetg(3,t_INTMOD); x[i] = (long)a;
    a[1] = (long)p;
    a[2] = lstoi(z[i]);
  }
  return normalizepol_i(x,l);
}

/* assume z[i] % p has been done. But we may have z[i] < 0 */
GEN
small_to_pol(GEN z, long l, long p)
{
  GEN x = cgetg(l,t_POL);
  long i;
  z -= 2; for (i=2; i<l; i++) x[i] = lstoi(z[i]<0? p+z[i]: z[i]);
  return normalizepol_i(x,l);
}

/* z in ?[X,Y] mod Q(Y) in Kronecker form ((subst(lift(z), x, y^(2deg(z)-1)))
 * Recover the "real" z, normalized */
GEN
from_Kronecker(GEN z, GEN pol)
{
  long i,j,lx,l = lgef(z), N = ((lgef(pol)-3)<<1) + 1;
  GEN a,x, t = cgetg(N,t_POL);
  t[1] = pol[1] & VARNBITS;
  lx = (l-2) / (N-2); x = cgetg(lx+3,t_POL);
  if (isonstack(pol)) pol = gcopy(pol);
  for (i=2; i<lx+2; i++)
  {
    a = cgetg(3,t_POLMOD); x[i] = (long)a;
    a[1] = (long)pol;
    for (j=2; j<N; j++) t[j] = z[j];
    z += (N-2);
    a[2] = lres(normalizepol_i(t,N), pol);
  }
  a = cgetg(3,t_POLMOD); x[i] = (long)a;
  a[1] = (long)pol;
  N = (l-2) % (N-2) + 2;
  for (j=2; j<N; j++) t[j] = z[j];
  a[2] = lres(normalizepol_i(t,N), pol);
  return normalizepol_i(x, i+1);
}

/*******************************************************************/
/*                                                                 */
/*                          MODULAR GCD                            */
/*                                                                 */
/*******************************************************************/
static GEN
maxnorm(GEN p)
{
  long i,n=lgef(p)-3,ltop=avma,lbot;
  GEN x, m = gzero;

  p += 2;
  for (i=0; i<n; i++)
  {
    x = (GEN)p[i];
    if (absi_cmp(x,m) > 0) m = absi(x);
  }
  m = divii(m, absi((GEN)p[n])); lbot = avma;
  return gerepile(ltop,lbot,addis(m,1));
}

/* return x[0 .. dx] mod p as C-long in a malloc'ed array */
static GEN
Fp_to_pol_long(GEN x, long dx, long p, long *d)
{
  long i, m;
  GEN a;

  for (i=dx; i>=0; i--)
  {
    m = smodis((GEN)x[i],p);
    if (m) break;
  }
  if (i < 0) { *d = -1; return NULL; }
  a = (GEN) gpmalloc((i+1)*sizeof(long));
  *d = i; a[i] = m;
  for (i--; i>=0; i--) a[i] = smodis((GEN)x[i],p);
  return a;
}

/* idem as Fp_poldivres but working only on C-long types
 * ASSUME pr != ONLY_DIVIDES (TODO ???)
 */
static long *
Fp_poldivres_long(long *x,long *y,long p,long dx, long dy, long *dc, GEN *pr)
{
  long dz,i,j,p1,*z,*c,inv;

  if (!dy) { *dc=-1; return NULL; }
  dz=dx-dy;
  if (dz<0)
  {
    if (pr)
    {
      c=(long *) gpmalloc((dx+1)*sizeof(long));
      for (i=0; i<=dx; i++) c[i]=x[i];
      *dc = dx;
      if (pr == ONLY_REM) return c;
      *pr = c;
    }
    return NULL;
  }
  z=(long *) gpmalloc((dz+1)*sizeof(long));
  inv = y[dy];
  if (inv!=1)
  {
    long av = avma;
    GEN res = mpinvmod(stoi(y[dy]),stoi(p));
    inv = itos(res); avma = av;
  }

  z[dz]=(inv*x[dx])%p;
  for (i=dx-1; i>=dy; --i)
  {
    p1=x[i];
    for (j=i-dy+1; j<=i && j<=dz; j++)
    {
      p1 -= z[j]*y[i-j];
      if (p1 & (HIGHBIT>>1)) p1=p1%p;
    }
    z[i-dy]=((p1%p)*inv)%p;
  }
  if (!pr) return z;

  c=(long *) gpmalloc(dy*sizeof(long));
  for (i=0; i<dy; i++)
  {
    p1=z[0]*y[i];
    for (j=1; j<=i && j<=dz; j++)
    {
      p1 += z[j]*y[i-j];
      if (p1 & (HIGHBIT>>1)) p1=p1%p;
    }
    c[i]=(x[i]-p1)%p;
  }

  i=dy-1; while (i>=0 && c[i]==0) i--;
  *dc=i;
  if (pr == ONLY_REM) { free(z); return c; }
  *pr = c; return z;
}

/* x and y in Z[X] */
GEN
Fp_poldivres(GEN x, GEN y, GEN p, GEN *pr)
{
  long vx,dx,dy,dz,i,j,av0,av,tetpil,sx,lrem;
  GEN z,p1,rem,lead;

  if (!signe(y)) err(talker,"division by zero in Fp_poldivres");
  vx=varn(x); dy=lgef(y)-3; dx=lgef(x)-3;
  if (dx < dy)
  {
    if (pr)
    {
      av0 = avma; x = Fp_pol_red(x, p);
      if (pr == ONLY_DIVIDES) { avma=av0; return signe(x)? NULL: gzero; }
      if (pr == ONLY_REM) return x;
      *pr = x;
    }
    return zeropol(vx);
  }
  lead = leading_term(y);
  if (!dy) /* y is constant */
  {
    if (pr && pr != ONLY_DIVIDES)
    {
      if (pr == ONLY_REM) return zeropol(vx);
      *pr = zeropol(vx);
    }
    if (gcmp1(lead)) return gcopy(x);
    av0 = avma; x = gmul(x, mpinvmod(lead,p)); tetpil = avma;
    return gerepile(av0,tetpil,Fp_pol_red(x,p));
  }
  av0 = avma; dz = dx-dy;
  if (2*expi(p)+6<BITS_IN_LONG)
  { /* assume ab != 0 mod p */
    long *a, *b, *zz, da,db,dr, pp = p[2];
    a = Fp_to_pol_long(x+2, dx, pp, &da);
    b = Fp_to_pol_long(y+2, dy, pp, &db);
    zz = Fp_poldivres_long(a,b,pp,da,db, &dr, pr);
    if (pr == ONLY_REM) dz = dr;
    else if (pr && pr != ONLY_DIVIDES)
    {
      rem = small_to_pol(*pr, dr+3, pp);
      free(*pr); setvarn(rem, vx); *pr = rem;
    }
    z = small_to_pol(zz, dz+3, pp);
    free(zz); free(a); free(b); setvarn(z, vx); return z;
  }
  lead = gcmp1(lead)? NULL: gclone(mpinvmod(lead,p));
  avma = av0;
  z=cgetg(dz+3,t_POL);
  z[1]=evalsigne(1) | evallgef(dz+3) | evalvarn(vx);
  x += 2; y += 2; z += 2;

  p1 = (GEN)x[dx]; av = avma;
  z[dz] = lead? lpileupto(av, modii(mulii(p1,lead), p)): licopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av=avma; p1=(GEN)x[i];
    for (j=i-dy+1; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii((GEN)z[j],(GEN)y[i-j]));
    if (lead) p1 = mulii(p1,lead);
    tetpil=avma; z[i-dy] = lpile(av,tetpil,modii(p1, p));
  }
  if (!pr) { if (lead) gunclone(lead); return z-2; }

  rem = (GEN)avma; av = (long)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = (GEN)x[i];
    for (j=0; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii((GEN)z[j],(GEN)y[i-j]));
    tetpil=avma; p1 = modii(p1,p); if (signe(p1)) { sx = 1; break; }
    if (!i) break;
    avma=av;
  }
  if (pr == ONLY_DIVIDES)
  {
    if (lead) gunclone(lead);
    if (sx) { avma=av0; return NULL; }
    avma = (long)rem; return z-2;
  }
  lrem=i+3; rem -= lrem;
  rem[0]=evaltyp(t_POL) | evallg(lrem);
  rem[1]=evalsigne(1) | evalvarn(vx) | evallgef(lrem);
  p1 = gerepile((long)rem,tetpil,p1);
  rem += 2; rem[i]=(long)p1;
  for (i--; i>=0; i--)
  {
    av=avma; p1 = (GEN)x[i];
    for (j=0; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii((GEN)z[j],(GEN)y[i-j]));
    tetpil=avma; rem[i]=lpile(av,tetpil, modii(p1,p));
  }
  rem -= 2;
  if (lead) gunclone(lead);
  if (!sx) normalizepol_i(rem, lrem);
  if (pr == ONLY_REM) return gerepileupto(av0,rem);
  *pr = rem; return z-2;
}

static GEN
Fp_pol_gcd_long(GEN x, GEN y, GEN p)
{
  long *a,*b,*c,da,db,dc, pp = (long)p[2];
  GEN z;

  a = Fp_to_pol_long(x+2, lgef(x)-3, pp, &da);
  if (!a) return Fp_pol_red(y,p);
  b = Fp_to_pol_long(y+2, lgef(y)-3, pp, &db);
  while (db>=0)
  {
    c = Fp_poldivres_long(a,b, pp, da,db,&dc, ONLY_REM);
    free(a); a=b; da=db; b=c; db=dc;
  }
  if (b) free(b);
  z = small_to_pol(a, da+3, pp);
  setvarn(z, varn(x));
  free(a); return z;
}

/* x and y in Z[X], return lift(gcd(x mod p, y mod p)) */
GEN
Fp_pol_gcd(GEN x, GEN y, GEN p)
{
  GEN a,b,c;
  long av0,av;

  if (2*expi(p)+6<BITS_IN_LONG) return Fp_pol_gcd_long(x,y,p);
  av0=avma;
  a = Fp_pol_red(x, p); av = avma;
  b = Fp_pol_red(y, p);
  while (signe(b))
  {
    av = avma; c = Fp_res(a,b,p); a=b; b=c;
  }
  avma = av; return gerepileupto(av0, a);
}

/* x and y in Z[X], return lift(gcd(x mod p, y mod p)). Set u and v st
 * ux + vy = gcd (mod p)
 */
GEN
Fp_pol_extgcd(GEN x, GEN y, GEN p, GEN *ptu, GEN *ptv)
{
  GEN a,b,q,r,u,v,d,d1,v1;
  long ltop,lbot;

#if 0 /* TODO */
  if (2*expi(p)+6<BITS_IN_LONG) return Fp_pol_extgcd_long(x,y,p);
#endif
  ltop=avma;
  a = Fp_pol_red(x, p);
  b = Fp_pol_red(y, p);
  d = a; d1 = b; v = gzero; v1 = gun;
  while (signe(d1))
  {
    q = Fp_poldivres(d,d1,p, &r);
    v = gadd(v, gneg_i(gmul(q,v1)));
    v = Fp_pol_red(v,p);
    u=v; v=v1; v1=u;
    u=r; d=d1; d1=u;
  }
  u = gadd(d, gneg_i(gmul(b,v)));
  u = Fp_pol_red(u, p);
  lbot = avma;
  u = Fp_deuc(u,a,p);
  d = gcopy(d);
  v = gcopy(v);
  {
    GEN *gptr[3]; gptr[0] = &d; gptr[1] = &u; gptr[2] = &v;
    gerepilemanysp(ltop,lbot,gptr,3);
  }
  *ptu = u; *ptv = v; return d;
}

GEN chinois_int_coprime(GEN x2, GEN y2, GEN x1, GEN y1, GEN z1);

/* a and b in Q[X] */
GEN
modulargcd(GEN a, GEN b)
{
  GEN D,A,B,Cp,p,q,H,g,limit,ma,mb,p1;
  long av=avma,avlim=stack_lim(av,1), m,n,nA,nB,av2,lbot,i;
  long prime[]={evaltyp(t_INT)|m_evallg(3),evalsigne(1)|evallgefint(3),0};
  byteptr d = diffptr;

  if (typ(a)!=t_POL || typ(b)!=t_POL) err(notpoler,"modulargcd");
  if (!signe(a)) return gcopy(b);
  if (!signe(b)) return gcopy(a);
  A = content(a);
  B = content(b); D = ggcd(A,B);
  A = gcmp1(A)? a: gdiv(a,A); nA=lgef(A)-3;
  B = gcmp1(B)? b: gdiv(b,B); nB=lgef(B)-3;
  g = mppgcd((GEN)A[nA+2], (GEN)B[nB+2]);
  av2=avma; n=1+min(nA,nB);
  ma=maxnorm(A); mb=maxnorm(B);
  if (cmpii(ma,mb) > 0) limit=mb; else limit=ma;
  limit = shifti(mulii(limit,g), n+1);

  /* initial p could be 1 << (BITS_IN_LONG/2-6), but diffptr is nice */
  prime[2] = 1021; d += 172; /* p = prime(172) = precprime(1<<10) */
  p = prime; H = NULL;
  for(;;)
  {
    do
    {
      if (*d) p[2] += *d++;
      else p = nextprime(addis(p,1)); /* never used */
    }
    while (!signe(resii(g,p)));
    Cp = Fp_pol_gcd(A,B,p);
    m = lgef(Cp)-3;
    if (m==0) return gerepileupto(av,gmul(D,polun[varn(A)]));
    if (gcmp1(g))
      Cp = normalize_mod_p(Cp, p);
    else
    { /* very rare */
      p1 = mulii(g, mpinvmod((GEN)Cp[m+2],p));
      Cp = Fp_pol_red(gmul(p1,Cp), p);
    }
    if (m<n) { q=icopy(p); H=Cp; limit=shifti(limit,m-n); n=m; }
    else
      if (m==n && H)
      {
        GEN q2 = mulii(q,p);
        for (i=2; i<=n+2; i++)
          H[i]=(long) chinois_int_coprime((GEN)H[i],(GEN)Cp[i],q,p,q2);
        q = q2;
	if (cmpii(limit,q) <= 0)
	{
	  GEN limit2=shifti(limit,-1);
	  for (i=2; i<=n+2; i++)
	  {
	    p1 = (GEN)H[i];
	    if (cmpii(p1,limit2) > 0) H[i]=lsubii(p1,q);
	  }
          p1 = content(H); if (!gcmp1(p1)) H = gdiv(H,p1);
	  if (!signe(gres(A,H)) && !signe(gres(B,H)))
	  {
	    lbot=avma;
	    return gerepile(av,lbot,gmul(D,H));
	  }
	  H = NULL; /* failed */
	}
      }
    if (low_stack(avlim, stack_lim(av,1)))
    {
      GEN *gptr[4]; gptr[0]=&H; gptr[1]=&p; gptr[2]=&q; gptr[3]=&limit;
      if (DEBUGMEM>1) err(warnmem,"modulargcd");
      gerepilemany(av2,gptr,4);
    }
  }
}

/* returns a polynomial in variable v, whose coeffs correspond to the digits
 * of m (in base p)
 */
GEN
stopoly(long m, long p, long v)
{
  GEN y = cgetg(BITS_IN_LONG + 2, t_POL);
  long l=2;

  do { y[l++] = lstoi(m%p); m=m/p; } while (m);
  y[1] = evalsigne(1)|evallgef(l)|evalvarn(v);
  return y;
}

GEN
stopoly_gen(GEN m, GEN p, long v)
{
  GEN y = cgetg(bit_accuracy(lgefint(m))+2, t_POL);
  long l=2;

  do { y[l++] = lmodii(m,p); m=divii(m,p); } while (signe(m));
  y[1] = evalsigne(1)|evallgef(l)|evalvarn(v);
  return y;
}

