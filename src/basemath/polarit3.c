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

/* assume nx >= ny > 0 */
static GEN
mulpol(GEN x, GEN y, long nx, long ny)
{
  long i,lz,nz;
  GEN z;
  char *p1;

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

/* shift polynomial in place. assume i free cells have been left before x */
static GEN
shiftpol_ip(GEN x, long v)
{
  long i, lx;
  GEN y;
  if (v <= 0 || !signe(x)) return x;
  lx = lgef(x);
  x += 2; y = x + v;
  for (i = lx-3; i>=0; i--) y[i] = x[i];
  for (i = 0   ; i< v; i++) x[i] = zero;
  lx += v;
  *--x = evalsigne(1) | evallgef(lx);
  *--x = evaltyp(t_POL) | evallg(lx); return x;
}

/* fast product (Karatsuba) of polynomials a,b. These are not real GENs, a+2,
 * b+2 were sent instead. na, nb = number of terms of a, b.
 * Only c, c0, c1, c2 are genuine GEN.
 */
GEN
quickmul(GEN a, GEN b, long na, long nb)
{
  GEN a0,c,c0;
  long av,n0,n0a,i, v = 0;

  while (na && isexactzero((GEN)a[0])) { a++; na--; v++; }
  while (nb && isexactzero((GEN)b[0])) { b++; nb--; v++; }
  if (na < nb) swapspec(a,b, na,nb);
  if (!nb) return zeropol(0);

  if (v) (void)new_chunk(v); /* free cells for shiftpol_ip */
  if (nb < MUL_LIMIT)
    return shiftpol_ip(mulpol(a,b,na,nb), v);
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
  return shiftpol_ip(gerepileupto(av,c0), v);
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
  long av,n0,n0a,i, v = 0;

  while (na && isexactzero((GEN)a[0])) { a++; na--; v += 2; }
  if (v) (void)new_chunk(v);
  if (na<SQR_LIMIT) return shiftpol_ip(sqrpol(a,na), v);
  i=(na>>1); n0=na-i; na=i;
  av=avma; a0=a+n0; n0a=n0;
  while (n0a && isexactzero((GEN)a[n0a-1])) n0a--;

  c = quicksqr(a,n0a);
  c0 = quicksqr(a0,na);
  c1 = gmul2n(quickmul(a0,a, na,n0a), 1);
  c0 = addshiftw(c0,c1, n0);
  c0 = addshiftwcopy(c0,c,n0);
  return shiftpol_ip(gerepileupto(av,c0), v);
}
/*****************************************
 * Arithmetic in Z/pZ[X]                 *
 *****************************************/

/*********************************************************************
This functions supposes polynomials already reduced.
There are clean and memory efficient.
**********************************************************************/
GEN
Fp_centermod(GEN T,GEN mod)
{/*OK centermod exists, but is not so clean*/
  ulong av;
  long i, l=lg(T);
  GEN P,mod2;
  P=cgetg(l,t_POL);
  P[1]=T[1];
  av=avma;
  mod2=gclone(shifti(mod,-1));/*clone*/
  avma=av;
  for(i=2;i<l;i++)
    P[i]=cmpii((GEN)T[i],mod2)<0?licopy((GEN)T[i]):lsubii((GEN)T[i],mod);
  gunclone(mod2);/*unclone*/
  return P;
}
GEN
Fp_neg(GEN x,GEN p)
{
  long i,d=lgef(x);
  GEN y;
  y=cgetg(d,t_POL); y[1]=x[1];
  for(i=2;i<d;i++)
    if (signe(x[i])) y[i]=lsubii(p,(GEN)x[i]);
    else y[i]=zero;
  return y;
}
/**********************************************************************
Unclean functions, do not garbage collect.
This is a feature: The stack is corrupted only by the call to Fp_pol_red
so garbage collecting so often is not desirable.
Fp_pol_red can sometime be avoided by passing NULL for p.
In this case the function is usually clean (see below for detail)
Added to help not using POLMOD of INTMOD which are deadly slow.
gerepileupto of the result is legible.   Bill.
I don't like C++.  I am wrong.
**********************************************************************/
/*
 *If p is NULL no reduction is performed and the function is clean.
 * for Fp_add,Fp_mul,Fp_sqr,Fp_mul_pol_scal
 */
GEN
Fp_add(GEN x,GEN y,GEN p)
{
  long lx,ly,i;
  GEN z;
  lx = lgef(x); ly = lgef(y); if (lx < ly) swapspec(x,y, lx,ly);
  z = cgetg(lx,t_POL); z[1] = x[1];
  for (i=2; i<ly; i++) z[i]=laddii((GEN)x[i],(GEN)y[i]);
  for (   ; i<lx; i++) z[i]=licopy((GEN)x[i]);
  (void)normalizepol_i(z, lx);
  if (lgef(z) == 2) { avma = (long)(z + lx); z = zeropol(varn(x)); }
  if (p) z= Fp_pol_red(z, p);
  return z;
}
GEN
Fp_sub(GEN x,GEN y,GEN p)
{
  long lx,ly,i,lz;
  GEN z;
  lx = lgef(x); ly = lgef(y); 
  lz=max(lx,ly);
  z = cgetg(lz,t_POL);
  if (lx >= ly)
  {  
    z[1] = x[1];
    for (i=2; i<ly; i++) z[i]=lsubii((GEN)x[i],(GEN)y[i]);
    for (   ; i<lx; i++) z[i]=licopy((GEN)x[i]);
    (void)normalizepol_i(z, lz);
  }
  else
  {  
    z[1] = y[1];
    for (i=2; i<lx; i++) z[i]=lsubii((GEN)x[i],(GEN)y[i]);
    for (   ; i<ly; i++) z[i]=lnegi((GEN)y[i]);
    /*polynomial is always normalized*/
  }
  if (lgef(z) == 2) { avma = (long)(z + lz); z = zeropol(varn(x)); }
  if (p) z= Fp_pol_red(z, p);
  return z;
}
GEN
Fp_mul(GEN x,GEN y,GEN p)
{
  GEN z;
  long vx=varn(x);
  z = quickmul(y+2, x+2, lgef(y)-2, lgef(x)-2);
  setvarn(z,vx); 
  if (!p) return z;
  return Fp_pol_red(z, p);
}
GEN
Fp_sqr(GEN x,GEN p)
{
  GEN z;
  long vx=varn(x);
  z = quicksqr(x+2, lgef(x)-2);
  setvarn(z,vx); 
  if (!p) return z;
  return Fp_pol_red(z, p);
}

/* Product of y and x in Z/pZ[X]/(pol)
 * return lift(lift(Mod(x*y*Mod(1,p),pol*Mod(1,p))));
 */
GEN
Fp_mul_mod_pol(GEN y,GEN x,GEN pol,GEN p)
{
  GEN z;
  long vy=varn(y);
  z = quickmul(y+2, x+2, lgef(y)-2, lgef(x)-2);
  setvarn(z,vy); 
  z = Fp_pol_red(z, p);
  return Fp_res(z,pol, p);
}
/* 
 * Square of y in Z/pZ[X]/(pol)
 * return lift(lift(Mod(y^2*Mod(1,p),pol*Mod(1,p))));
 */
GEN
Fp_sqr_mod_pol(GEN y,GEN pol,GEN p)
{
  GEN z;
  long vy=varn(y);
  z = quicksqr(y+2,lgef(y)-2);
  setvarn(z,vy); 
  z = Fp_pol_red(z, p);
  return Fp_res(z,pol, p);
}
/*Modify y[2].
 *No reduction if p is NULL
 */
GEN 
Fp_add_pol_scal(GEN y,GEN x,GEN p)
{
  if (!signe(x)) return y;
  if (!signe(y))
    return scalarpol(x,varn(y));
  y[2]=laddii((GEN)y[2],x);
  if (!p) return y;
  y[2]=lmodii((GEN)y[2],p);
  return y;
}
/* y is a polynomial in ZZ[X] and x an integer.
 * If p is NULL, no reduction is perfomed and return x*y
 * 
 * else the result is lift(y*x*Mod(1,p))
 */

GEN 
Fp_mul_pol_scal(GEN y,GEN x,GEN p)
{
  GEN z;
  int i;
  if (!signe(x))
    return zeropol(varn(y));
  z=cgetg(lg(y),t_POL);
  z[1]=y[1];
  for(i=2;i<lgef(y);i++)
    z[i]=lmulii((GEN)y[i],x);
  if(!p) return z; 
  return Fp_pol_red(z,p);
}
/*****************************************************************
 *                 End of unclean functions.                     *
 *                                                               *
 *****************************************************************/
/*****************************************************************
 Clean and with no reduced hypothesis.  Beware that some operations
 will be must slower with big unreduced coefficient
*****************************************************************/



/* Inverse of x in Z/pZ[X]/(pol)
 * return lift(lift(Mod(x*Mod(1,p),pol*Mod(1,p))^-1));
 */
GEN
Fp_inv_mod_pol(GEN x,GEN pol,GEN p)
{
  ulong ltop=avma;
  GEN ptu,ptv;
  GEN z;
  z=Fp_pol_extgcd(x,pol,p,&ptu,&ptv);
  if (lgef(z)!=3)
    err(talker,"non invertible polynomial in Fp_inv_mod_pol");
  z=mpinvmod((GEN)z[2],p);
  ptu=Fp_mul_pol_scal(ptu,z,p);
  return gerepileupto(ltop,ptu);
}
/* T in Z[X] and  x in Z/pZ[X]/(pol)
 * return lift(lift(subst(T,variable(T),Mod(x*Mod(1,p),pol*Mod(1,p)))));
 */
GEN
Fp_compo_mod_pol(GEN T,GEN x,GEN pol,GEN p)
{
  ulong ltop=avma;
  GEN z;
  long i,d=lgef(T)-1;
  if (!signe(T)) return zeropol(varn(T));
  z = scalarpol((GEN)T[d],varn(T));
  for(i=d-1;i>1;i--)
  {
    z=Fp_mul_mod_pol(z,x,pol,p);
    z=Fp_add_pol_scal(z,(GEN) T[i],p);
  }
  return gerepileupto(ltop,Fp_pol_red(z, p));
}
/* Evaluation in Fp
 * x in Z[X] and y in Z return x(y) mod p
 */
GEN
Fp_poleval(GEN x,GEN y,GEN p)
{
  ulong av;
  GEN p1,r,res;
  long i,j;
  i=lgef(x)-1;
  if (i<=2)
    return (i==2)? modii((GEN)x[2],p): gzero;
  res=cgetg(lgefint(p),t_INT);
  av=avma; p1=(GEN)x[i];
  /* specific attention to sparse polynomials (see poleval)*/
  /*You've guess it! It's a copy-paste(tm)*/
  for (i--; i>=2; i=j-1)
  {
    for (j=i; !signe((GEN)x[j]); j--)
      if (j==2)
      {
	if (i!=j) y = powmodulo(y,stoi(i-j+1),p);
	p1=mulii(p1,y);
	goto fppoleval;/*sorry break(2) no implemented*/
      }
    r = (i==j)? y: powmodulo(y,stoi(i-j+1),p);
    p1 = modii(addii(mulii(p1,r), (GEN)x[j]),p);
  }
 fppoleval:
  modiiz(p1,p,res);
  avma=av;
  return res;
}
/* Tz=Tx*Ty where Tx and Ty coprime
 * return lift(chinese(Mod(x*Mod(1,p),Tx*Mod(1,p)),Mod(y*Mod(1,p),Ty*Mod(1,p))))
 * if Tz is NULL it is computed
 * =======>: As we do not return it, and the caller will frequently need it, 
 * it must compute it and pass it.
 */
GEN
Fp_chinese_coprime(GEN x,GEN y,GEN Tx,GEN Ty,GEN Tz,GEN p)
{
  long av = avma;
  GEN ax,p1;
  ax = Fp_mul(Fp_inv_mod_pol(Tx,Ty,p), Tx,p);
  p1=Fp_mul(ax, Fp_sub(y,x,p),p);
  p1 = Fp_add(x,p1,p);
  if (!Tz) Tz=Fp_mul(Tx,Ty,p);
  p1 = Fp_res(p1,Tz,p);
  return gerepileupto(av,p1);
}
/* x,pol in Z[X], p in Z, n in Z, compute lift(x^n mod (p, pol)) */
GEN
Fp_pow_mod_pol(GEN x, GEN n, GEN pol, GEN p)
{
  long m,i,j,ltop=avma, av, lim=stack_lim(avma,1), vx = varn(x);
  GEN p1 = n+2, y;
  if (!signe(n)) return polun[vx];
  if (signe(n)<0) 
  {
    x=Fp_inv_mod_pol(x,pol,p);
    if (is_pm1(n)) return x;/*n=-1*/
  }
  else
    if (is_pm1(n)) return gcopy(x);/*n=1*/
  m = *p1; y = x; av=avma;
  j=1+bfffo(m); m<<=j; j = BITS_IN_LONG-j;
  for (i=lgefint(n)-2;;)
  {
    for (; j; m<<=1,j--)
    {
      y = Fp_sqr_mod_pol(y,pol,p);
      if (low_stack(lim, stack_lim(av,1)))
      {
        if(DEBUGMEM>1) err(warnmem,"[1]: Fp_pow_mod_pol");
        y = gerepileupto(av, y);
      }
      if (m<0)
	y = Fp_mul_mod_pol(y,x,pol,p);
      if (low_stack(lim, stack_lim(av,1)))
      {
        if(DEBUGMEM>1) err(warnmem,"[2]: Fp_pow_mod_pol");
        y = gerepileupto(av, y);
      }
    }
    if (--i == 0) break;
    m = *++p1, j = BITS_IN_LONG;
  }
  return gerepileupto(ltop,y);
}

/*******************************************************************/
/*                                                                 */
/*                       n-th ROOT in Fq                           */
/*                                                                 */
/*******************************************************************/
/*NO clean stack*/
static GEN fflgen(GEN l, GEN q, long e, GEN r,GEN T ,GEN p,GEN *zeta)
{
  ulong av1;
  GEN z,m,m1;
  long x=varn(T),k,u,v,pp,i;
  if (is_bigint(p))
    pp=VERYBIGINT;
  else
    pp=itos(p); 
  z=(lgef(T)==4)?polun[x]:polx[x];
 
  av1 = avma;
  for (k=1; ; k++)
  {
    u=k;v=0;
    while (u%pp==0){u/=pp;v++;}
    if(!v)
      z=gadd(z,gun);
    else
    {
      z=gadd(z,gpowgs(polx[x],v));
      if (DEBUGLEVEL>=6)
	fprintferr("FF l-Gen:next %Z  +d",z);
    }
    m1 = m = Fp_pow_mod_pol(z,r,T,p);
    for (i=1; i<e; i++)
      if (gcmp1(m=Fp_pow_mod_pol(m,l,T,p))) break;
    if (i==e) break;
    avma = av1;
  }
  *zeta=m;
  return m1;
}
/* resoud x^l=a mod (p,T)
 * l doit etre premier
 * q=p^deg(T)-1
 * q=(l^e)*r
 * e>=1
 * pgcd(r,l)=1
 * m=y^(q/l)
 * y n'est pas une puissance l-ieme
 * m!=1
 * ouf!
 */
GEN
ffsqrtlmod(GEN a, GEN l, GEN T ,GEN p ,GEN q,long e, GEN r, GEN y, GEN m)
{
  long av = avma,tetpil,lim,i,k;
  GEN p1,p2,u1,u2,v,w,z;
  long x;
  x=varn(T);
  bezout(r,l,&u1,&u2);
  v=Fp_pow_mod_pol(a,u2,T,p);
  w=Fp_pow_mod_pol(a,modii(mulii(negi(u1),r),q),T,p);
  lim = stack_lim(av,1);
  while (!gcmp1(w))
  {
    /* if p is not prime, next loop will not end */
    k=0;
    p1=w;
    do
    {
      z=p1;
      p1=Fp_pow_mod_pol(p1,l,T,p);
      k++;
    }while(!gcmp1(p1));
    if (k==e) { avma=av; return NULL; }
    p2 = Fp_mul_mod_pol(z,m,T,p);
    for(i=1; !gcmp1(p2); i++) p2 = Fp_mul_mod_pol(p2,m,T,p);/*should be a baby step
							      giant step instead*/
    p1= Fp_pow_mod_pol(y,modii(mulsi(i,gpowgs(l,e-k-1)),q),T,p);
    m = Fp_pow_mod_pol(m,stoi(i),T,p);
    e = k;
    v = Fp_mul_mod_pol(p1,v,T,p);
    y = Fp_pow_mod_pol(p1,l,T,p);
    w = Fp_mul_mod_pol(y,w,T,p);
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[4];
      if(DEBUGMEM>1) err(warnmem,"ffsqrtlmod");
      gptr[0]=&y; gptr[1]=&v; gptr[2]=&w; gptr[3]=&m;
      gerepilemany(av,gptr,4);
    }
  }
  tetpil=avma; return gerepile(av,tetpil,gcopy(v));
}
/*  n is an integer, a is in Fp[X]/(T), p is prime, T is irreducible mod p

return a solution of 

x^n=a mod p 

1)If there is no solution return NULL and if zetan is not NULL set zetan to gzero.

2) If there is solution there are exactly  m=gcd(p-1,n) of them.

If zetan is not NULL, zetan is set to a primitive mth root of unity so that
the set of solutions is {x*zetan^k;k=0 to m-1}

If a=0 ,return 0 and if zetan is not NULL zetan is set to gun
*/
GEN ffsqrtnmod(GEN a, GEN n, GEN T, GEN p, GEN *zetan)
{
  ulong ltop=avma,lbot=0,av1,lim;
  long i,j,e;
  GEN m,u1,u2;
  GEN q,r,zeta,y,l,z;
  GEN *gptr[2];
  if (typ(a) != t_POL || typ(n) != t_INT || typ(T) != t_POL || typ(p)!=t_INT)
    err(typeer,"ffsqrtnmod");
  if (lgef(T)==3)
    err(constpoler,"ffsqrtnmod");
  if(!signe(n))
    err(talker,"1/0 exponent in ffsqrtnmod");
  if(gcmp1(n)) {if (zetan) *zetan=gun;return gcopy(a);}
  if(gcmp0(a)) {if (zetan) *zetan=gun;return gzero;}
  q=addsi(-1,gpowgs(p,lgef(T)-3));
  m=bezout(n,q,&u1,&u2);
  if (gcmp(m,n))
  {
    GEN b=modii(u1,q);
    lbot=avma;
    a=Fp_pow_mod_pol(a,b,T,p);
  }
  if (zetan) z=polun[varn(T)];
  lim=stack_lim(ltop,1);
  if (!gcmp1(m))
  {
    m=decomp(m);
    av1=avma;
    for (i = lg(m[1])-1; i; i--)
    {
      l=gcoeff(m,i,1); j=itos(gcoeff(m,i,2));
      e=pvaluation(q,l,&r);
      y=fflgen(l,q,e,r,T,p,&zeta);
      if (zetan) z=Fp_mul_mod_pol(z,Fp_pow_mod_pol(y,gpowgs(l,e-j),T,p),T,p);
      do
      {
	lbot=avma;
	a=ffsqrtlmod(a,l,T,p,q,e,r,y,zeta);
	if (!a){avma=ltop;return NULL;}
	j--;
	if (low_stack(lim, stack_lim(ltop,1)))/* n can have lots of prime factors*/
	{
	  if(DEBUGMEM>1) err(warnmem,"ffsqrtnmod");
	  if (zetan)
	  {
	    z=gcopy(z);
	    gptr[0]=&a;gptr[1]=&z;
	    gerepilemanysp(av1,lbot,gptr,2);
	  }
	  else
	    a=gerepileupto(av1,a);
	}
      }
      while (j);
    }
  }  
  if (zetan)
  {
    *zetan=gcopy(z);
    gptr[0]=&a;gptr[1]=zetan;
    gerepilemanysp(ltop,lbot,gptr,2);
  }
  else
    a=gerepileupto(ltop,a);
  return a;
}
/*******************************************************************/
/*  Isomorphisms between finite fields                             */
/*                                                                 */
/*******************************************************************/
static GEN
matrixpow(long n, GEN y, GEN P,GEN l)
{
  ulong av=avma;
  GEN M,Z;
  long d,i,j;
  Z=cgetg(n+1,t_VEC);
  if(n>0)
    Z[1]=lpolun[varn(P)];
  for(i=2;i<=n;i++)
    Z[i]=(long)Fp_mul_mod_pol(y,(GEN)Z[i-1],P,l);
  M=cgetg(n+1,t_MAT);
  for (i=1;i<=n;i++)
  {
    M[i] = lgetg(n+1, t_COL);
    d=lgef((GEN)Z[i])-3;
    for (j = 1; j <= d+1 ; j++)
      mael(M,i,j) = licopy((GEN) mael(Z,i,1 + j));
    for (     ; j <= n; j++)
      mael(M,i,j) = zero;
  }
  return gerepileupto(av,M);
}
/* compute the reciprocical ismorphism of S mod Tp, i.e. V such that
   V(S)=X  mod T,p*/  
GEN
Fp_inv_isom(GEN S,GEN Tp, GEN p)
{
  ulong   ltop = avma, lbot;
  GEN     M, U, V;
  int     n, i;
  long    x;
  x = varn(Tp);
  U = polun[x];
  n = degree(Tp);
  M = matrixpow(n,S,Tp,p);
  V = cgetg(n + 1, t_COL);
  for (i = 1; i <= n; i++)
    V[i] = zero;
  V[2] = un;
  V = inverseimage_mod_p(M,V,p);
  lbot = avma;
  V = gtopolyrev(V, x);
  return gerepile(ltop, lbot, V);
}
/* Let l be a prime number P, Q in ZZ[X].
 * P and Q are both irreducible modulo l and of the same degree.
 * Output an isomorphism between FF_l[X]/P and FF_l[X]/Q
 * as a polynomial R such that Q|P(R) mod l
 */

GEN
Fp_isom(GEN l,GEN P,GEN Q)
{  
  ulong ltop=avma;
  long x,n,e,pg;
  GEN q,m,MA,MB,R=gzero;
  GEN A,B,Ap,Bp;
  x=varn(P);n=degree(P);
  e=pvaluation(stoi(n),l,&q);
  pg=itos(q);
  avma=ltop; 
  if (DEBUGLEVEL>=2) timer2();
  m=Fp_pow_mod_pol(polx[x],l,P,l);
  MA=matrixpow(n,m,P,l);
  m=Fp_pow_mod_pol(polx[x],l,Q,l);
  MB=matrixpow(n,m,Q,l);
  if (DEBUGLEVEL>=2) msgtimer("matrixpow");
  A=B=Ap=Bp=zeropol(x);
  if (pg>1)
  {
    if (gcmp0(modis(addis(l,-1),pg)))
      /*We do not need to use relative extension in this setting, so
        we don't*/
    {
      GEN L,An,Bn,ipg,z;
      z=lift((GEN)rootmod(cyclo(pg,x),l)[1]);
      z=negi(z);
      ipg=stoi(pg);
      if (DEBUGLEVEL>=4) timer2();
      A=(GEN)ker_mod_p(gaddmat(z, MA),l)[1];/*SEGV on bad input*/
      A=gtopolyrev(A,x);
      B=(GEN)ker_mod_p(gaddmat(z, MB),l)[1];/*SEGV on bad input*/
      B=gtopolyrev(B,x);
      if (DEBUGLEVEL>=4) msgtimer("ker_mod_p");
      An=(GEN) Fp_pow_mod_pol(A,ipg,P,l)[2];
      Bn=(GEN) Fp_pow_mod_pol(B,ipg,Q,l)[2];
      z=modii(mulii(An,mpinvmod(Bn,l)),l);
      L=mpsqrtnmod(z,ipg,l,NULL); 
      if (DEBUGLEVEL>=4) msgtimer("mpsqrtnmod");
      B=Fp_mul_pol_scal(B,L,l);
    }
    else
    {
      GEN L,An,Bn,ipg,U,lU,z;
      z=gneg(polx[MAXVARN]);
      U=gmael(factmod(cyclo(pg,MAXVARN),l),1,1);
      lU=lift(U);
      ipg=stoi(pg);
      if (DEBUGLEVEL>=4) timer2();
      A=(GEN)Fq_ker(gaddmat(z, MA),lU,l)[1];/*SEGV on bad input*/
      A=gmul(A,gmodulcp(gmodulcp(gun,l),U));
      A=gtopolyrev(A,x);  
      B=(GEN)Fq_ker(gaddmat(z, MB),lU,l)[1];/*SEGV on bad input*/
      B=gmul(B,gmodulcp(gmodulcp(gun,l),U));
      B=gtopolyrev(B,x);
      if (DEBUGLEVEL>=4) msgtimer("Fq_ker");
      An=lift(lift((GEN)lift(gpowgs(gmodulcp(A,P),pg))[2])); 
      Bn=lift(lift((GEN)lift(gpowgs(gmodulcp(B,Q),pg))[2]));
      z=Fp_inv_mod_pol(Bn,lU,l);
      z=Fp_mul_mod_pol(An,z,lU,l);
      L=ffsqrtnmod(z,ipg,lU,l,NULL); 
      if (DEBUGLEVEL>=4) msgtimer("ffsqrtn");
      B=gsubst(lift(lift(gmul(B,L))),MAXVARN,gzero);
      A=gsubst(lift(lift(A)),MAXVARN,gzero);
    }
  }
  if (e!=0)
  {
    GEN V1,moinsun,Ay,By,lmun;
    int i,j;
    moinsun=stoi(-1);
    lmun=addis(l,-1);
    MA=gaddmat(moinsun,MA);
    MB=gaddmat(moinsun,MB);
    Ay=By=polun[x];
    V1=cgetg(n+1,t_COL);
    V1[1]=un;
    for(i=2;i<=n;i++) V1[i]=zero;
    for(j=0;j<e;j++)
    { 
      if (j)
      {
	Ay=Fp_mul_mod_pol(Ay,Fp_pow_mod_pol(Ap,lmun,P,l),P,l);
	for(i=1;i<lgef(Ay)-1;i++) V1[i]=Ay[i+1];
	for(;i<=n;i++) V1[i]=zero;
      }
      Ap=inverseimage_mod_p(MA,V1,l);
      Ap=gtopolyrev(Ap,x);
      if (j)
      {
	By=Fp_mul_mod_pol(By,Fp_pow_mod_pol(Bp,lmun,Q,l),Q,l);
	for(i=1;i<lgef(By)-1;i++) V1[i]=By[i+1];
	for(;i<=n;i++) V1[i]=zero;
      }
      Bp=inverseimage_mod_p(MB,V1,l);
      Bp=gtopolyrev(Bp,x);
      if (DEBUGLEVEL>=4) msgtimer("inverseimage_mod_p");
    }
  }
  A=Fp_add(A,Ap,l);
  B=Fp_add(B,Bp,l);
  R=Fp_inv_isom(A,P,l);
  R=Fp_compo_mod_pol(R,B,Q,l);
  return gerepileupto(ltop,R);
}

/*******************************************************************/
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

/* z in Z[X,Y] representing an elt in F_p[X,Y] mod pol(Y) i.e F_q[X])
 * in Kronecker form. Recover the "real" z, normalized
 * If p = NULL, use generic functions and the coeff. ring implied by the
 * coefficients of z */
GEN
FqX_from_Kronecker(GEN z, GEN pol, GEN p)
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
    a[2] = (long)Fp_res(normalizepol_i(t,N), pol,p);
  }
  a = cgetg(3,t_POLMOD); x[i] = (long)a;
  a[1] = (long)pol;
  N = (l-2) % (N-2) + 2;
  for (j=2; j<N; j++) t[j] = z[j];
  a[2] = (long)Fp_res(normalizepol_i(t,N), pol,p);
  return normalizepol_i(x, i+1);
}

/* z in ?[X,Y] mod Q(Y) in Kronecker form ((subst(lift(z), x, y^(2deg(z)-1)))
 * Recover the "real" z, normalized */
GEN
from_Kronecker(GEN z, GEN pol)
{
  return FqX_from_Kronecker(z,pol,NULL);
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
  long i, m=0;
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

  if (!p) return poldivres(x,y,pr);
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
      p1 = modii(mulii(g, mpinvmod((GEN)Cp[m+2],p)),p);
      Cp = Fp_pol_red(gmul(p1,Cp), p);
    }
    if (m<n) { q=icopy(p); H=Cp; limit=shifti(limit,m-n); n=m; }
    else
      if (m==n && H)
      {
        GEN q2 = mulii(q,p);
        for (i=2; i<=n+2; i++) /* lc(H) = g (mod q2) */
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

