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

/***********************************************************************/
/**                                                                   **/
/**               ARITHMETIC OPERATIONS ON POLYNOMIALS                **/
/**                         (first part)                              **/
/**                                                                   **/
/***********************************************************************/
#include "pari.h"
extern GEN get_bas_den(GEN bas);
extern GEN get_mul_table(GEN x,GEN bas,GEN invbas);
extern GEN pol_to_monic(GEN pol, GEN *lead);

#define lswap(x,y) { long _t=x; x=y; y=_t; }
#define swap(x,y) { GEN _t=x; x=y; y=_t; }

/* see splitgen() for how to use these two */
GEN
setloop(GEN a)
{
  a=icopy(a); (void)new_chunk(2); /* dummy to get two cells of extra space */
  return a;
}

/* assume a > 0 */
GEN
incpos(GEN a)
{
  long i,l=lgefint(a);

  for (i=l-1; i>1; i--)
    if (++a[i]) return a;
  i=l+1; a--; /* use extra cell */
  a[0]=evaltyp(1) | evallg(i);
  a[1]=evalsigne(1) | evallgefint(i);
  return a;
}

GEN
incloop(GEN a)
{
  long i,l;

  switch(signe(a))
  {
    case 0:
      a--; /* use extra cell */
      a[0]=evaltyp(t_INT) | evallg(3);
      a[1]=evalsigne(1) | evallgefint(3);
      a[2]=1; return a;

    case -1:
      l=lgefint(a);
      for (i=l-1; i>1; i--)
        if (a[i]--) break;
      if (a[2] == 0)
      {
        a++; /* save one cell */
        a[0] = evaltyp(t_INT) | evallg(2);
        a[1] = evalsigne(0) | evallgefint(2);
      }
      return a;

    default:
      return incpos(a);
  }
}

/*******************************************************************/
/*                                                                 */
/*                           DIVISIBILITE                          */
/*                 Return 1 if y  |  x,  0 otherwise               */
/*                                                                 */
/*******************************************************************/

int
gdivise(GEN x, GEN y)
{
  gpmem_t av=avma;
  x=gmod(x,y); avma=av; return gcmp0(x);
}

int
poldivis(GEN x, GEN y, GEN *z)
{
  gpmem_t av = avma;
  GEN p1 = poldivres(x,y,ONLY_DIVIDES);
  if (p1) { *z = p1; return 1; }
  avma=av; return 0;
}

/*******************************************************************/
/*                                                                 */
/*                  POLYNOMIAL EUCLIDEAN DIVISION                  */
/*                                                                 */
/*******************************************************************/
/* Polynomial division x / y:
 *   if z = ONLY_REM  return remainder, otherwise return quotient
 *   if z != NULL set *z to remainder
 *   *z is the last object on stack (and thus can be disposed of with cgiv
 *   instead of gerepile) */
GEN
poldivres(GEN x, GEN y, GEN *pr)
{
  gpmem_t avy, av, av1;
  long ty=typ(y),tx,vx,vy,dx,dy,dz,i,j,sx,lrem;
  GEN z,p1,rem,y_lead,mod;
  GEN (*f)(GEN,GEN);

  f = gdiv;
  if (is_scalar_t(ty))
  {
    if (pr == ONLY_REM) return gzero;
    if (pr && pr != ONLY_DIVIDES) *pr=gzero;
    return f(x,y);
  }
  tx=typ(x); vy=gvar9(y);
  if (is_scalar_t(tx) || gvar9(x)>vy)
  {
    if (pr == ONLY_REM) return gcopy(x);
    if (pr == ONLY_DIVIDES) return gcmp0(x)? gzero: NULL;
    if (pr) *pr=gcopy(x);
    return gzero;
  }
  if (tx!=t_POL || ty!=t_POL) err(typeer,"euclidean division (poldivres)");

  vx=varn(x);
  if (vx<vy)
  {
    if (pr && pr != ONLY_DIVIDES)
    {
      p1 = zeropol(vx); if (pr == ONLY_REM) return p1;
      *pr = p1;
    }
    return f(x,y);
  }

  if (!signe(y)) err(talker,"division by zero in poldivrem");
  dy = degpol(y);
  y_lead = (GEN)y[dy+2];
  if (gcmp0(y_lead)) /* normalize denominator if leading term is 0 */
  {
    err(warner,"normalizing a polynomial with 0 leading term");
    for (dy--; dy>=0; dy--)
    {
      y_lead = (GEN)y[dy+2];
      if (!gcmp0(y_lead)) break;
    }
  }
  if (!dy) /* y is constant */
  {
    if (pr && pr != ONLY_DIVIDES)
    {
      if (pr == ONLY_REM) return zeropol(vx);
      *pr = zeropol(vx);
    }
    return f(x, constant_term(y));
  }
  dx = degpol(x);
  if (vx>vy || dx<dy)
  {
    if (pr)
    {
      if (pr == ONLY_DIVIDES) return gcmp0(x)? gzero: NULL;
      if (pr == ONLY_REM) return gcopy(x);
      *pr = gcopy(x);
    }
    return zeropol(vy);
  }

  /* x,y in R[X], y non constant */
  dz = dx-dy; av = avma;
  p1 = new_chunk(dy+3);
  for (i=2; i<dy+3; i++)
  {
    GEN p2 = (GEN)y[i];
    /* gneg to avoid gsub's later on */
    p1[i] = isexactzero(p2)? 0: (long)gneg_i(p2);
  }
  y = p1;
  switch(typ(y_lead))
  {
    case t_INTMOD:
    case t_POLMOD: y_lead = ginv(y_lead);
      f = gmul; mod = gmodulcp(gun, (GEN)y_lead[1]);
      break;
    default: if (gcmp1(y_lead)) y_lead = NULL;
      mod = NULL;
  }
  avy=avma;
  z = cgetg(dz+3,t_POL);
  z[1] = evalsigne(1) | evallgef(dz+3) | evalvarn(vx);
  x += 2; y += 2; z += 2;

  p1 = (GEN)x[dx];
  z[dz] = y_lead? (long)f(p1,y_lead): lcopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av1=avma; p1=(GEN)x[i];
    for (j=i-dy+1; j<=i && j<=dz; j++)
      if (y[i-j] && z[j] != zero) p1 = gadd(p1, gmul((GEN)z[j],(GEN)y[i-j]));
    if (y_lead) p1 = f(p1,y_lead);

    if (isexactzero(p1)) { avma=av1; p1 = gzero; }
    else
      p1 = avma==av1? gcopy(p1): gerepileupto(av1,p1);
    z[i-dy] = (long)p1;
  }
  if (!pr) return gerepileupto(av,z-2);

  rem = (GEN)avma; av1 = (gpmem_t)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = (GEN)x[i];
    /* we always enter this loop at least once */
    for (j=0; j<=i && j<=dz; j++)
      if (y[i-j] && z[j] != zero) p1 = gadd(p1, gmul((GEN)z[j],(GEN)y[i-j]));
    if (mod && avma==av1) p1 = gmul(p1,mod);
    if (!gcmp0(p1)) { sx = 1; break; } /* remainder is non-zero */
    if (!isinexactreal(p1) && !isexactzero(p1)) break;
    if (!i) break;
    avma=av1;
  }
  if (pr == ONLY_DIVIDES)
  {
    if (sx) { avma=av; return NULL; }
    avma = (gpmem_t)rem;
    return gerepileupto(av,z-2);
  }
  lrem=i+3; rem -= lrem;
  if (avma==av1) { avma = (gpmem_t)rem; p1 = gcopy(p1); }
  else p1 = gerepileupto((gpmem_t)rem,p1);
  rem[0]=evaltyp(t_POL) | evallg(lrem);
  rem[1]=evalsigne(1) | evalvarn(vx) | evallgef(lrem);
  rem += 2;
  rem[i]=(long)p1;
  for (i--; i>=0; i--)
  {
    av1=avma; p1 = (GEN)x[i];
    for (j=0; j<=i && j<=dz; j++)
      if (y[i-j] && z[j] != zero) p1 = gadd(p1, gmul((GEN)z[j],(GEN)y[i-j]));
    if (mod && avma==av1) p1 = gmul(p1,mod);
    rem[i]=avma==av1? lcopy(p1):lpileupto(av1,p1);
  }
  rem -= 2;
  if (!sx) (void)normalizepol_i(rem, lrem);
  if (pr == ONLY_REM) return gerepileupto(av,rem);
  z -= 2;
  {
    GEN *gptr[2]; gptr[0]=&z; gptr[1]=&rem;
    gerepilemanysp(av,avy,gptr,2); *pr = rem; return z;
  }
}

/*******************************************************************/
/*                                                                 */
/*           ROOTS MODULO a prime p (no multiplicities)            */
/*                                                                 */
/*******************************************************************/
static GEN
mod(GEN x, GEN y)
{
  GEN z = cgetg(3,t_INTMOD);
  z[1]=(long)y; z[2]=(long)x; return z;
}

static long
factmod_init(GEN *F, GEN pp, long *p)
{
  GEN f = *F;
  long i,d;
  if (typ(f)!=t_POL || typ(pp)!=t_INT) err(typeer,"factmod");
  if (expi(pp) > BITS_IN_LONG - 3) *p = 0;
  else
  {
    *p = itos(pp);
    if (*p < 2) err(talker,"not a prime in factmod");
  }
  f = gmul(f, mod(gun,pp));
  if (!signe(f)) err(zeropoler,"factmod");
  f = lift_intern(f); d = lgef(f);
  for (i=2; i <d; i++)
    if (typ(f[i])!=t_INT) err(impl,"factormod for general polynomials");
  *F = f; return d-3;
}

#define mods(x,y) mod(stoi(x),y)
static GEN
root_mod_2(GEN f)
{
  int z1, z0 = !signe(constant_term(f));
  long i,n;
  GEN y;

  for (i=2, n=1; i < lgef(f); i++)
    if (signe(f[i])) n++;
  z1 = n & 1;
  y = cgetg(z0+z1+1, t_COL); i = 1;
  if (z0) y[i++] = (long)mods(0,gdeux);
  if (z1) y[i]   = (long)mods(1,gdeux);
  return y;
}

#define i_mod4(x) (signe(x)? mod4((GEN)(x)): 0)
static GEN
root_mod_4(GEN f)
{
  long no,ne;
  int z0 = !signe(constant_term(f));
  int z2 = ((i_mod4(constant_term(f)) + 2*i_mod4(f[3])) & 3) == 0;
  int i,z1,z3;
  GEN y,p;

  for (ne=0,i=2; i<lgef(f); i+=2)
    if (signe(f[i])) ne += mael(f,i,2);
  for (no=0,i=3; i<lgef(f); i+=2)
    if (signe(f[i])) no += mael(f,i,2);
  no &= 3; ne &= 3;
  z3 = (no == ne);
  z1 = (no == ((4-ne)&3));
  y=cgetg(1+z0+z1+z2+z3,t_COL); i = 1; p = stoi(4);
  if (z0) y[i++] = (long)mods(0,p);
  if (z1) y[i++] = (long)mods(1,p);
  if (z2) y[i++] = (long)mods(2,p);
  if (z3) y[i]   = (long)mods(3,p);
  return y;
}
#undef i_mod4

/* p even, accept p = 4 for p-adic stuff */
static GEN
root_mod_even(GEN f, long p)
{
  switch(p)
  {
    case 2: return root_mod_2(f);
    case 4: return root_mod_4(f);
  }
  err(talker,"not a prime in rootmod");
  return NULL; /* not reached */
}

/* by checking f(0..p-1) */
GEN
rootmod2(GEN f, GEN pp)
{
  GEN g,y,ss,q,r, x_minus_s;
  long p, d, i, nbrac;
  gpmem_t av = avma, av1;

  if (!(d = factmod_init(&f, pp, &p))) { avma=av; return cgetg(1,t_COL); }
  if (!p) err(talker,"prime too big in rootmod2");
  if ((p & 1) == 0) { avma = av; return root_mod_even(f,p); }
  x_minus_s = gadd(polx[varn(f)], stoi(-1));

  nbrac=1;
  y=(GEN)gpmalloc((d+1)*sizeof(long));
  if (gcmp0(constant_term(f))) y[nbrac++] = 0;
  ss = icopy(gun); av1 = avma;
  do
  {
    mael(x_minus_s,2,2) = ss[2];
    /* one might do a FFT-type evaluation */
    q = FpX_divres(f, x_minus_s, pp, &r);
    if (signe(r)) avma = av1;
    else
    {
      y[nbrac++] = ss[2]; f = q; av1 = avma;
    }
    ss[2]++;
  }
  while (nbrac<d && p>ss[2]);
  if (nbrac == 1) { avma=av; return cgetg(1,t_COL); }
  if (nbrac == d && p != ss[2])
  {
    g = mpinvmod((GEN)f[3], pp); setsigne(g,-1);
    ss = modis(mulii(g, (GEN)f[2]), p);
    y[nbrac++]=ss[2];
  }
  avma=av; g=cgetg(nbrac,t_COL);
  if (isonstack(pp)) pp = icopy(pp);
  for (i=1; i<nbrac; i++) g[i]=(long)mods(y[i],pp);
  free(y); return g;
}

/* assume x reduced mod p, monic, squarefree. Return one root, or NULL if
 * irreducible */
static GEN
quadsolvemod(GEN x, GEN p, int unknown)
{
  GEN b = (GEN)x[3], c = (GEN)x[2];
  GEN s,u,D;

  if (egalii(p, gdeux))
  {
    if (signe(c)) return NULL;
    return gun;
  }
  D = subii(sqri(b), shifti(c,2));
  D = resii(D,p);
  if (unknown && kronecker(D,p) == -1) return NULL;

  s = mpsqrtmod(D,p);
  if (!s) err(talker,"not a prime in quadsolvemod");
  u = addis(shifti(p,-1), 1); /* = 1/2 */
  return modii(mulii(u, subii(s,b)), p);
}

static GEN
otherroot(GEN x, GEN r, GEN p)
{
  GEN s = addii((GEN)x[3], r);
  s = subii(p, s); if (signe(s) < 0) s = addii(s,p);
  return s;
}

/* by splitting */
GEN
rootmod(GEN f, GEN p)
{
  long n, i, j, la, lb;
  gpmem_t av = avma, tetpil;
  GEN y,pol,a,b,q,pol0;

  if (!factmod_init(&f, p, &i)) { avma=av; return cgetg(1,t_COL); }
  i = modBIL(p);
  if ((i & 1) == 0) { avma = av; return root_mod_even(f,i); }
  i=2; while (!signe(f[i])) i++;
  if (i == 2) j = 1;
  else
  {
    j = lgef(f) - (i-2);
    if (j==3) /* f = x^n */
    {
      avma = av; y = cgetg(2,t_COL);
      y[1] = (long)gmodulsg(0,p);
      return y;
    }
    a = cgetg(j, t_POL); /* a = f / x^{v_x(f)} */
    a[1] =  evalsigne(1) | evalvarn(varn(f)) | evallgef(j);
    f += i-2; for (i=2; i<j; i++) a[i]=f[i];
    j = 2; f = a;
  }
  q = shifti(p,-1);
  /* take gcd(x^(p-1) - 1, f) by splitting (x^q-1) * (x^q+1) */
  b = FpXQ_pow(polx[varn(f)],q, f,p);
  if (lgef(b)<3) err(talker,"not a prime in rootmod");
  b = ZX_s_add(b,-1); /* b = x^((p-1)/2) - 1 mod f */
  a = FpX_gcd(f,b, p);
  b = ZX_s_add(b, 2); /* b = x^((p-1)/2) + 1 mod f */
  b = FpX_gcd(f,b, p);
  la = degpol(a);
  lb = degpol(b); n = la + lb;
  if (!n)
  {
    avma = av; y = cgetg(n+j,t_COL);
    if (j>1) y[1] = (long)gmodulsg(0,p);
    return y;
  }
  y = cgetg(n+j,t_COL);
  if (j>1) { y[1] = zero; n++; }
  y[j] = (long)FpX_normalize(b,p);
  if (la) y[j+lb] = (long)FpX_normalize(a,p);
  pol = gadd(polx[varn(f)], gun); pol0 = constant_term(pol);
  while (j<=n)
  { /* cf FpX_split_berlekamp */
    a = (GEN)y[j]; la = degpol(a);
    if (la==1)
      y[j++] = lsubii(p, constant_term(a));
    else if (la==2)
    {
      GEN r = quadsolvemod(a, p, 0);
      y[j++] = (long)r;
      y[j++] = (long)otherroot(a,r, p);
    }
    else for (pol0[2]=1; ; pol0[2]++)
    {
      b = ZX_s_add(FpXQ_pow(pol,q, a,p), -1); /* pol^(p-1)/2 - 1 */
      b = FpX_gcd(a,b, p); lb = degpol(b);
      if (lb && lb < la)
      {
        b = FpX_normalize(b, p);
        y[j+lb] = (long)FpX_div(a,b, p);
        y[j]    = (long)b; break;
      }
      if (pol0[2] == 100 && !BSW_psp(p))
        err(talker, "not a prime in polrootsmod");
    }
  }
  tetpil = avma; y = gerepile(av,tetpil,sort(y));
  if (isonstack(p)) p = icopy(p);
  for (i=1; i<=n; i++) y[i] = (long)mod((GEN)y[i], p);
  return y;
}

GEN
rootmod0(GEN f, GEN p, long flag)
{
  switch(flag)
  {
    case 0: return rootmod(f,p);
    case 1: return rootmod2(f,p);
    default: err(flagerr,"polrootsmod");
  }
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                     FACTORISATION MODULO p                      */
/*                                                                 */
/*******************************************************************/
#define FqX_div(x,y,T,p) FpXQX_divres((x),(y),(T),(p),NULL)
#define FqX_rem(x,y,T,p) FpXQX_divres((x),(y),(T),(p),ONLY_REM)
#define FqX_red FpXQX_red
#define FqX_sqr FpXQX_sqr
static GEN spec_FpXQ_pow(GEN x, GEN p, GEN S);
extern GEN pol_to_vec(GEN x, long N);
extern GEN FqXQ_pow(GEN x, GEN n, GEN S, GEN T, GEN p);
extern GEN FpXQX_from_Kronecker(GEN z, GEN pol, GEN p);
extern GEN FpXQX_safegcd(GEN P, GEN Q, GEN T, GEN p);
extern GEN u_normalizepol(GEN x, long lx);
extern GEN Fq_pow(GEN x, GEN n, GEN pol, GEN p);
/* Functions giving information on the factorisation. */

/* u in Z[X], return kernel of (Frob - Id) over Fp[X] / u */
static GEN
FpM_Berlekamp_ker(GEN u, GEN p)
{
  long j,N = degpol(u);
  GEN vker,v,w,Q,p1;
  if (DEBUGLEVEL > 7) (void)timer2();
  Q = cgetg(N+1,t_MAT); Q[1] = (long)zerocol(N);
  w = v = FpXQ_pow(polx[varn(u)],p,u,p);
  for (j=2; j<=N; j++)
  {
    p1 = pol_to_vec(w, N);
    p1[j] = laddis((GEN)p1[j], -1);
    Q[j] = (long)p1;
    if (j < N)
    {
      gpmem_t av = avma;
      w = gerepileupto(av, FpX_res(gmul(w,v), u, p));
    }
  }
  if (DEBUGLEVEL > 7) msgtimer("frobenius");
  vker = FpM_ker(Q,p);
  if (DEBUGLEVEL > 7) msgtimer("kernel");
  return vker;
}

static GEN
FqM_Berlekamp_ker(GEN u, GEN T, GEN q, GEN p)
{
  long j,N = degpol(u);
  GEN vker,v,w,Q,p1;
  if (DEBUGLEVEL > 7) (void)timer2();
  Q = cgetg(N+1,t_MAT); Q[1] = (long)zerocol(N);
  w = v = FqXQ_pow(polx[varn(u)], q, u, T, p);
  for (j=2; j<=N; j++)
  {
    p1 = pol_to_vec(w, N);
    p1[j] = laddgs((GEN)p1[j], -1);
    Q[j] = (long)p1;
    if (j < N)
    {
      gpmem_t av = avma;
      w = gerepileupto(av, FpXQX_divres(FpXQX_mul(w,v, T,p), u,T,p,ONLY_REM));
    }
  }
  if (DEBUGLEVEL > 7) msgtimer("frobenius");
  vker = FqM_ker(Q,T,p);
  if (DEBUGLEVEL > 7) msgtimer("kernel");
  return vker;
}

/* f in ZZ[X] and p a prime number. */
long
FpX_is_squarefree(GEN f, GEN p)
{
  gpmem_t av = avma;
  GEN z;
  z = FpX_gcd(f,derivpol(f),p);
  avma = av;
  return lgef(z)==3;
}
/* idem
 * leading term of f must be prime to p.
 */
/* Compute the number of roots in Fp without counting multiplicity
 * return -1 for 0 polynomial.
 */
long
FpX_nbroots(GEN f, GEN p)
{
  long n=lgef(f);
  gpmem_t av = avma;
  GEN z;
  if (n <= 4) return n-3;
  f = FpX_red(f, p);
  z = FpXQ_pow(polx[varn(f)], p, f, p);
  z = FpX_sub(z,polx[varn(f)],NULL);
  z = FpX_gcd(z,f,p),
  avma = av; return degpol(z);
}
long
FpX_is_totally_split(GEN f, GEN p)
{
  long n=degpol(f);
  gpmem_t av = avma;
  GEN z;
  if (n <= 1) return 1;
  if (!is_bigint(p) && n > p[2]) return 0;
  f = FpX_red(f, p);
  z = FpXQ_pow(polx[varn(f)], p, f, p);
  avma = av; return lgef(z)==4 && gcmp1((GEN)z[3]) && !signe(z[2]);
}
/* u in ZZ[X] and p a prime number.
 * u must be squarefree mod p.
 * leading term of u must be prime to p. */
long
FpX_nbfact(GEN u, GEN p)
{
  gpmem_t av = avma;
  GEN vker = FpM_Berlekamp_ker(u,p);
  avma = av; return lg(vker)-1;
}

/* Please use only use this function when you it is false, or that there is a
 * lot of factors. If you believe f is irreducible or that it has few factors,
 * then use `FpX_nbfact(f,p)==1' instead (faster).
 */
static GEN factcantor0(GEN f, GEN pp, long flag);
long FpX_is_irred(GEN f, GEN p) { return !!factcantor0(f,p,2); }

static GEN modulo;
static GEN gsmul(GEN a,GEN b){return FpX_mul(a,b,modulo);}
GEN
FpV_roots_to_pol(GEN V, GEN p, long v)
{
  gpmem_t ltop=avma;
  long i;
  GEN g=cgetg(lg(V),t_VEC);
  for(i=1;i<lg(V);i++)
    g[i]=(long)deg1pol(gun,modii(negi((GEN)V[i]),p),v);
  modulo=p;
  g=divide_conquer_prod(g,&gsmul);
  return gerepileupto(ltop,g);
}

/************************************************************/
GEN
trivfact(void)
{
  GEN y=cgetg(3,t_MAT);
  y[1]=lgetg(1,t_COL);
  y[2]=lgetg(1,t_COL); return y;
}

static GEN
try_pow(GEN w0, GEN pol, GEN p, GEN q, long r)
{
  GEN w2, w = FpXQ_pow(w0,q, pol,p);
  long s;
  if (gcmp1(w)) return w0;
  for (s=1; s<r; s++,w=w2)
  {
    w2 = gsqr(w);
    w2 = FpX_res(w2, pol, p);
    if (gcmp1(w2)) break;
  }
  return gcmp_1(w)? NULL: w;
}

/* INPUT:
 *  m integer (converted to polynomial w in Z[X] by stopoly)
 *  p prime; q = (p^d-1) / 2^r
 *  t[0] polynomial of degree k*d product of k irreducible factors of degree d
 *  t[0] is expected to be normalized (leading coeff = 1)
 * OUTPUT:
 *  t[0],t[1]...t[k-1] the k factors, normalized
 */
static void
split(long m, GEN *t, long d, GEN p, GEN q, long r, GEN S)
{
  long ps, l, v, dv;
  gpmem_t av0, av;
  GEN w,w0;

  dv=degpol(*t); if (dv==d) return;
  v=varn(*t); av0=avma; ps = p[2];
  for(av=avma;;avma=av)
  {
    if (ps==2)
    {
      w0 = w = FpXQ_pow(polx[v], stoi(m-1), *t, gdeux); m += 2;
      for (l=1; l<d; l++)
        w = gadd(w0, spec_FpXQ_pow(w, p, S));
    }
    else
    {
      w = FpX_res(stopoly(m,ps,v),*t, p);
      m++; w = try_pow(w,*t,p,q,r);
      if (!w) continue;
      w = ZX_s_add(w, -1);
    }
    w = FpX_gcd(*t,w, p);
    l = degpol(w); if (l && l!=dv) break;
  }
  w = FpX_normalize(w, p);
  w = gerepileupto(av0, w);
  l /= d; t[l]=FpX_div(*t,w,p); *t=w;
  split(m,t+l,d,p,q,r,S);
  split(m,t,  d,p,q,r,S);
}

static void
splitgen(GEN m, GEN *t, long d, GEN  p, GEN q, long r)
{
  long l, v, dv;
  gpmem_t av;
  GEN w;

  dv=degpol(*t); if (dv==d) return;
  v=varn(*t); m=setloop(m); m=incpos(m);
  av=avma;
  for(;; avma=av, m=incpos(m))
  {
    w = FpX_res(stopoly_gen(m,p,v),*t, p);
    w = try_pow(w,*t,p,q,r);
    if (!w) continue;
    w = ZX_s_add(w,-1);
    w = FpX_gcd(*t,w, p); l=degpol(w);
    if (l && l!=dv) break;

  }
  w = FpX_normalize(w, p);
  w = gerepileupto(av, w);
  l /= d; t[l]=FpX_div(*t,w,p); *t=w;
  splitgen(m,t+l,d,p,q,r);
  splitgen(m,t,  d,p,q,r);
}

/* return S = [ x^p, x^2p, ... x^(n-1)p ] mod (p, T), n = degree(T) > 0 */
static GEN
init_pow_p_mod_pT(GEN p, GEN T)
{
  long i, n = degpol(T), v = varn(T);
  GEN p1, S = cgetg(n, t_VEC);
  if (n == 1) return S;
  S[1] = (long)FpXQ_pow(polx[v], p, T, p);
  /* use as many squarings as possible */
  for (i=2; i < n; i+=2)
  {
    p1 = gsqr((GEN)S[i>>1]);
    S[i]   = (long)FpX_res(p1, T, p);
    if (i == n-1) break;
    p1 = gmul((GEN)S[i], (GEN)S[1]);
    S[i+1] = (long)FpX_res(p1, T, p);
  }
  return S;
}

/* compute x^p, S is as above */
static GEN
spec_FpXQ_pow(GEN x, GEN p, GEN S)
{
  long i, dx = degpol(x);
  gpmem_t av = avma, lim = stack_lim(av, 1);
  GEN x0 = x+2, z;
  z = (GEN)x0[0];
  if (dx < 0) err(talker, "zero polynomial in FpXQ_pow. %Z not prime", p);
  for (i = 1; i <= dx; i++)
  {
    GEN d, c = (GEN)x0[i]; /* assume coeffs in [0, p-1] */
    if (!signe(c)) continue;
    d = (GEN)S[i]; if (!gcmp1(c)) d = gmul(c,d);
    z = gadd(z, d);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"spec_FpXQ_pow");
      z = gerepileupto(av, z);
    }
  }
  z = FpX_red(z, p);
  return gerepileupto(av, z);
}

/* factor f mod pp.
 * If (flag = 1) return the degrees, not the factors
 * If (flag = 2) return NULL if f is not irreducible
 */
static GEN
factcantor0(GEN f, GEN pp, long flag)
{
  long i, j, k, d, e, vf, p, nbfact;
  gpmem_t tetpil, av = avma;
  GEN ex,y,f2,g,g1,u,v,pd,q;
  GEN *t;

  if (!(d = factmod_init(&f, pp, &p))) { avma=av; return trivfact(); }
  /* to hold factors and exponents */
  t = (GEN*)cgetg(d+1,t_VEC); ex = new_chunk(d+1);
  vf=varn(f); e = nbfact = 1;
  for(;;)
  {
    f2 = FpX_gcd(f,derivpol(f), pp);
    if (flag > 1 && lgef(f2) > 3) return NULL;
    g1 = FpX_div(f,f2,pp);
    k = 0;
    while (lgef(g1)>3)
    {
      long du,dg;
      GEN S;
      k++; if (p && !(k%p)) { k++; f2 = FpX_div(f2,g1,pp); }
      u = g1; g1 = FpX_gcd(f2,g1, pp);
      if (lgef(g1)>3)
      {
        u = FpX_div( u,g1,pp);
        f2= FpX_div(f2,g1,pp);
      }
      du = degpol(u);
      if (du <= 0) continue;

      /* here u is square-free (product of irred. of multiplicity e * k) */
      S = init_pow_p_mod_pT(pp, u);
      pd=gun; v=polx[vf];
      for (d=1; d <= du>>1; d++)
      {
        if (!flag) pd = mulii(pd,pp);
        v = spec_FpXQ_pow(v, pp, S);
        g = FpX_gcd(gadd(v, gneg(polx[vf])), u, pp);
        dg = degpol(g);
        if (dg <= 0) continue;

        /* Ici g est produit de pol irred ayant tous le meme degre d; */
        j=nbfact+dg/d;

        if (flag)
        {
          if (flag > 1) return NULL;
          for ( ; nbfact<j; nbfact++) { t[nbfact]=(GEN)d; ex[nbfact]=e*k; }
        }
        else
        {
          long r;
          g = FpX_normalize(g, pp);
          t[nbfact]=g; q = subis(pd,1); /* also ok for p=2: unused */
          r = vali(q); q = shifti(q,-r);
         /* le premier parametre est un entier variable m qui sera
          * converti en un polynome w dont les coeff sont ses digits en
          * base p (initialement m = p --> X) pour faire pgcd de g avec
          * w^(p^d-1)/2 jusqu'a casser. p = 2 is treated separately.
          */
          if (p)
            split(p,t+nbfact,d,pp,q,r,S);
          else
            splitgen(pp,t+nbfact,d,pp,q,r);
          for (; nbfact<j; nbfact++) ex[nbfact]=e*k;
        }
        du -= dg;
        u = FpX_div(u,g,pp);
        v = FpX_res(v,u,pp);
      }
      if (du)
      {
        t[nbfact] = flag? (GEN)du: FpX_normalize(u, pp);
        ex[nbfact++]=e*k;
      }
    }
    j = lgef(f2); if (j==3) break;

    e*=p; j=(j-3)/p+3; setlg(f,j); setlgef(f,j);
    for (i=2; i<j; i++) f[i]=f2[p*(i-2)+2];
  }
  if (flag > 1) { avma = av; return gun; } /* irreducible */
  tetpil=avma; y=cgetg(3,t_MAT);
  if (!flag)
  {
    y[1]=(long)t; setlg(t, nbfact);
    y[2]=(long)ex; (void)sort_factor(y,cmpii);
  }
  u=cgetg(nbfact,t_COL); y[1]=(long)u;
  v=cgetg(nbfact,t_COL); y[2]=(long)v;
  if (flag)
    for (j=1; j<nbfact; j++)
    {
      u[j] = lstoi((long)t[j]);
      v[j] = lstoi(ex[j]);
    }
  else
    for (j=1; j<nbfact; j++)
    {
      u[j] = (long)FpX(t[j], pp);
      v[j] = lstoi(ex[j]);
    }
  return gerepile(av,tetpil,y);
}

GEN
factcantor(GEN f, GEN p)
{
  return factcantor0(f,p,0);
}

GEN
simplefactmod(GEN f, GEN p)
{
  return factcantor0(f,p,1);
}

GEN
col_to_ff(GEN x, long v)
{
  long i, k = lg(x);
  GEN p;

  while (--k && gcmp0((GEN)x[k]));
  if (k <= 1) return k? (GEN)x[1]: gzero;
  i = k+2; p = cgetg(i,t_POL);
  p[1] = evalsigne(1) | evallgef(i) | evalvarn(v);
  x--; for (k=2; k<i; k++) p[k] = x[k];
  return p;
}

GEN
vec_to_pol(GEN x, long v)
{
  long i, k = lg(x);
  GEN p;

  while (--k && gcmp0((GEN)x[k]));
  if (!k) return zeropol(v);
  i = k+2; p = cgetg(i,t_POL);
  p[1] = evalsigne(1) | evallgef(i) | evalvarn(v);
  x--; for (k=2; k<i; k++) p[k] = x[k];
  return p;
}

GEN
u_vec_to_pol(GEN x)
{
  long i, k = lg(x);
  GEN p;

  while (--k && !x[k]);
  if (!k) return u_zeropol();
  i = k+2; p = cgetg(i,t_POL);
  p[1] = evalsigne(1) | evallgef(i) | evalvarn(0);
  x--; for (k=2; k<i; k++) p[k] = x[k];
  return p;
}

#if 0
static GEN
u_FpM_FpV_mul(GEN x, GEN y, ulong p)
{
  long i,k,l,lx=lg(x), ly=lg(y);
  GEN z;
  if (lx != ly) err(operi,"* [mod p]",x,y);
  if (lx==1) return cgetg(1,t_VECSMALL);
  l = lg(x[1]);
  z = cgetg(l,t_VECSMALL);
  for (i=1; i<l; i++)
  {
    ulong p1 = 0;
    for (k=1; k<lx; k++)
    {
      p1 += coeff(x,i,k) * y[k];
      if (p1 & HIGHBIT) p1 %= p;
    }
    z[i] = p1 % p;
  }
  return z;
}
#endif

/* u_vec_to_pol(u_FpM_FpV_mul(x, u_pol_to_vec(y), p)) */
GEN
u_FpM_FpX_mul(GEN x, GEN y, ulong p)
{
  long i,k,l, ly=lgef(y)-1;
  GEN z;
  if (ly==1) return u_zeropol();
  l = lg(x[1]);
  y++;
  z = vecsmall_const(l,0) + 1;
  for (k=1; k<ly; k++)
  {
    GEN c;
    if (!y[k]) continue;
    c = (GEN)x[k];
    if (y[k] == 1)
      for (i=1; i<l; i++)
      {
        z[i] += c[i];
        if (z[i] & HIGHBIT) z[i] %= p;
      }
    else
      for (i=1; i<l; i++)
      {
        z[i] += c[i] * y[k];
        if (z[i] & HIGHBIT) z[i] %= p;
      }
  }
  for (i=1; i<l; i++) z[i] %= p;
  while (--l && !z[l]);
  if (!l) return u_zeropol();
  *z-- = evalsigne(1) | evallgef(l+2) | evalvarn(0);
  return z;
}

/* return the (N-dimensional) vector of coeffs of p */
GEN
pol_to_vec(GEN x, long N)
{
  long i, l;
  GEN z = cgetg(N+1,t_COL);
  if (typ(x) != t_POL)
  {
    z[1] = (long)x;
    for (i=2; i<=N; i++) z[i]=zero;
    return z;
  }
  l = lgef(x)-1; x++;
  for (i=1; i<l ; i++) z[i]=x[i];
  for (   ; i<=N; i++) z[i]=zero;
  return z;
}

/* return the (N-dimensional) vector of coeffs of p */
GEN
u_pol_to_vec(GEN x, long N)
{
  long i, l;
  GEN z = cgetg(N+1,t_VECSMALL);
  if (typ(x) != t_VECSMALL) err(typeer,"u_pol_to_vec");
  l = lgef(x)-1; x++;
  for (i=1; i<l ; i++) z[i]=x[i];
  for (   ; i<=N; i++) z[i]=0;
  return z;
}

/* vector of polynomials (in v) whose coeffs are given by the columns of x */
GEN
mat_to_vecpol(GEN x, long v)
{
  long j, lx = lg(x);
  GEN y = cgetg(lx, t_VEC);
  for (j=1; j<lx; j++) y[j] = (long)vec_to_pol((GEN)x[j], v);
  return y;
}

/* matrix whose entries are given by the coeffs of the polynomials in
 * vector v (considered as degree n-1 polynomials) */
GEN
vecpol_to_mat(GEN v, long n)
{
  long j, N = lg(v);
  GEN y = cgetg(N, t_MAT);
  if (typ(v) != t_VEC) err(typeer,"vecpol_to_mat");
  for (j=1; j<N; j++) y[j] = (long)pol_to_vec((GEN)v[j], n);
  return y;
}

/* polynomial (in v) of polynomials (in w) whose coeffs are given by the columns of x */
GEN
mat_to_polpol(GEN x, long v,long w)
{
  long j, lx = lg(x);
  GEN y = cgetg(lx+1, t_POL);
  y[1]=evalsigne(1) | evallgef(lx+1) | evalvarn(v);
  y++;
  for (j=1; j<lx; j++) y[j] = (long)vec_to_pol((GEN)x[j], w);
  return normalizepol_i(--y, lx+1);
}

/* matrix whose entries are given by the coeffs of the polynomial v in
 * two variables (considered as degree n polynomials) */
GEN
polpol_to_mat(GEN v, long n)
{
  long j, N = lgef(v)-1;
  GEN y = cgetg(N, t_MAT);
  if (typ(v) != t_POL) err(typeer,"polpol_to_mat");
  v++;
  for (j=1; j<N; j++) y[j] = (long)pol_to_vec((GEN)v[j], n);
  return y;
}

/* P(X,Y) --> P(Y,X), n-1 is the degree in Y */
GEN
swap_polpol(GEN x, long n, long w)
{
  long j, lx = lgef(x), ly = n+3;
  long v=varn(x);
  GEN y = cgetg(ly, t_POL);
  y[1]=evalsigne(1) | evallgef(ly) | evalvarn(v);
  for (j=2; j<ly; j++)
  {
    long k;
    GEN p1=cgetg(lx,t_POL);
    p1[1] = evalsigne(1) | evallgef(lx) | evalvarn(w);
    for (k=2; k<lx; k++)
      if( j<lgef(x[k]))
        p1[k] = mael(x,k,j);
      else
        p1[k] = zero;
    y[j] = (long)normalizepol_i(p1,lx);
  }
  return normalizepol_i(y,ly);
}

/* set x <-- x + c*y mod p */
static void
u_FpX_addmul(GEN x, GEN y, long c, long p)
{
  long i,lx,ly,l;
  if (!c) return;
  lx = lgef(x);
  ly = lgef(y); l = min(lx,ly);
  if (p & ~MAXHALFULONG)
  {
    for (i=2; i<l;  i++) x[i] = ((ulong)x[i]+ (ulong)mulssmod(c,y[i],p)) % p;
    if (l == lx)
      for (   ; i<ly; i++) x[i] = mulssmod(c,y[i],p);
  }
  else
  {
    for (i=2; i<l;  i++) x[i] = ((ulong)x[i] + (ulong)(c*y[i])) % p;
    if (l == lx)
      for (   ; i<ly; i++) x[i] = (c*y[i]) % p;
  }
  (void)u_normalizepol(x,i);
}

static long
small_rand(long p)
{
  return (p==2)? ((mymyrand() & 0x1000) == 0): mymyrand() % p;
}

GEN
FpX_rand(long d1, long v, GEN p)
{
  long i, d = d1+2;
  GEN y;
  y = cgetg(d,t_POL); y[1] = evalsigne(1) | evalvarn(v);
  for (i=2; i<d; i++) y[i] = (long)genrand(p);
  (void)normalizepol_i(y,d); return y;
}

/* return a random polynomial in F_q[v], degree < d1 */
GEN
FqX_rand(long d1, long v, GEN T, GEN p)
{
  long i, d = d1+2, k = degpol(T), w = varn(T);
  GEN y;
  y = cgetg(d,t_POL); y[1] = evalsigne(1) | evalvarn(v);
  for (i=2; i<d; i++) y[i] = (long)FpX_rand(k, w, p);
  (void)normalizepol_i(y,d); return y;
}

#define set_irred(i) { if ((i)>ir) swap(t[i],t[ir]); ir++;}

long
FpX_split_berlekamp(GEN *t, GEN p)
{
  GEN u = *t, a,b,po2,vker,pol;
  long N = degpol(u), d, i, ir, L, la, lb, ps, vu = varn(u);
  gpmem_t av0 = avma;

  vker = FpM_Berlekamp_ker(u,p);
  vker = mat_to_vecpol(vker,vu);
  d = lg(vker)-1;
  ps = is_bigint(p)? 0: p[2];
  if (ps)
  {
    avma = av0; a = cgetg(d+1, t_VEC); /* hack: hidden gerepile */
    for (i=1; i<=d; i++) a[i] = (long)pol_to_small((GEN)vker[i]);
    vker = a;
  }
  po2 = shifti(p, -1); /* (p-1) / 2 */
  pol = cgetg(N+3,t_POL);
  ir = 0;
  /* t[i] irreducible for i <= ir, still to be treated for i < L */
  for (L=1; L<d; )
  {
    GEN polt;
    if (ps)
    {
      pol[2] = small_rand(ps); /* vker[1] = 1 */
      pol[1] = evallgef(pol[2]? 3: 2);
      for (i=2; i<=d; i++)
        u_FpX_addmul(pol,(GEN)vker[i],small_rand(ps), ps);
      polt = small_to_pol(pol,vu);
    }
    else
    {
      pol[2] = (long)genrand(p);
      pol[1] = evallgef(signe(pol[2])? 3: 2) | evalvarn(vu);
      for (i=2; i<=d; i++)
        pol = gadd(pol, gmul((GEN)vker[i], genrand(p)));
      polt = FpX_red(pol,p);
    }
    for (i=ir; i<L && L<d; i++)
    {
      a = t[i]; la = degpol(a);
      if (la == 1) { set_irred(i); }
      else if (la == 2)
      {
        GEN r = quadsolvemod(a,p,1);
        if (r)
        {
          t[i] = deg1pol_i(gun, subii(p,r), vu); r = otherroot(a,r,p);
          t[L] = deg1pol_i(gun, subii(p,r), vu); L++;
        }
        set_irred(i);
      }
      else
      {
        gpmem_t av = avma;
        b = FpX_res(polt, a, p);
        if (degpol(b) == 0) { avma=av; continue; }
        b = ZX_s_add(FpXQ_pow(b,po2, a,p), -1);
        b = FpX_gcd(a,b, p); lb = degpol(b);
        if (lb && lb < la)
        {
          b = FpX_normalize(b, p);
          t[L] = FpX_div(a,b,p);
          t[i]= b; L++;
        }
        else avma = av;
      }
    }
  }
  return d;
}

static GEN
FqX_deriv(GEN f, GEN T, GEN p)
{
  return FqX_red(derivpol(f), T, p);
}
GEN
FqX_gcd(GEN P, GEN Q, GEN T, GEN p)
{
  GEN g = T? FpXQX_safegcd(P,Q,T,p): FpX_gcd(P,Q,p);
  if (!g) err(talker,"factmod9: %Z is reducible mod p!", T);
  return g;
}
long
FqX_is_squarefree(GEN P, GEN T, GEN p)
{
  gpmem_t av = avma;
  GEN z = FqX_gcd(P, derivpol(P), T, p);
  avma = av;
  return degpol(z)==0;

}

long
FqX_split_berlekamp(GEN *t, GEN q, GEN T, GEN p)
{
  GEN u = *t, a,b,qo2,vker,pol;
  long N = degpol(u), vu = varn(u), vT = varn(T), dT = degpol(T);
  long d, i, ir, L, la, lb;

  vker = FqM_Berlekamp_ker(u,T,q,p);
  vker = mat_to_vecpol(vker,vu);
  d = lg(vker)-1;
  qo2 = shifti(q, -1); /* (q-1) / 2 */
  pol = cgetg(N+3,t_POL);
  ir = 0;
  /* t[i] irreducible for i < ir, still to be treated for i < L */
  for (L=1; L<d; )
  {
    GEN polt;
    pol[2] = (long)FpX_rand(dT,vT,p);
    pol[1] = evallgef(signe(pol[2])? 3: 2) | evalvarn(vu);
    for (i=2; i<=d; i++)
      pol = gadd(pol, gmul((GEN)vker[i], FpX_rand(dT,vT,p)));
    polt = FqX_red(pol,T,p);
    for (i=ir; i<L && L<d; i++)
    {
      a = t[i]; la = degpol(a);
      if (la == 1) { set_irred(i); }
      else
      {
        gpmem_t av = avma;
        b = FqX_rem(polt, a, T,p);
        if (!degpol(b)) { avma=av; continue; }
        b = FqXQ_pow(b,qo2, a,T,p);
        if (!degpol(b)) { avma=av; continue; }
        b[2] = ladd((GEN)b[2], gun);
        b = FqX_gcd(a,b, T,p); lb = degpol(b);
        if (lb && lb < la)
        {
          b = FpXQX_normalize(b, T,p);
          t[L] = FqX_div(a,b,T,p);
          t[i]= b; L++;
        }
        else avma = av;
      }
    }
  }
  return d;
}

GEN
factmod0(GEN f, GEN pp)
{
  long i, j, k, e, p, N, nbfact, d;
  gpmem_t av = avma, tetpil;
  GEN pps2,ex,y,f2,p1,g1,u, *t;

  if (!(d = factmod_init(&f, pp, &p))) { avma=av; return trivfact(); }
  /* to hold factors and exponents */
  t = (GEN*)cgetg(d+1,t_VEC); ex = cgetg(d+1,t_VECSMALL);
  e = nbfact = 1;
  pps2 = shifti(pp,-1);

  for(;;)
  {
    f2 = FpX_gcd(f,derivpol(f), pp);
    g1 = lgef(f2)==3? f: FpX_div(f,f2,pp);
    k = 0;
    while (lgef(g1)>3)
    {
      k++; if (p && !(k%p)) { k++; f2 = FpX_div(f2,g1,pp); }
      p1 = FpX_gcd(f2,g1, pp); u = g1; g1 = p1;
      if (degpol(p1))
      {
        u = FpX_div( u,p1,pp);
        f2= FpX_div(f2,p1,pp);
      }
      /* u is square-free (product of irred. of multiplicity e * k) */
      N = degpol(u);
      if (N)
      {
        t[nbfact] = FpX_normalize(u,pp);
        d = (N==1)? 1: FpX_split_berlekamp(t+nbfact, pp);
        for (j=0; j<d; j++) ex[nbfact+j] = e*k;
        nbfact += d;
      }
    }
    if (!p) break;
    j=(degpol(f2))/p+3; if (j==3) break;

    e*=p; setlg(f,j); setlgef(f,j);
    for (i=2; i<j; i++) f[i] = f2[p*(i-2)+2];
  }
  tetpil=avma; y=cgetg(3,t_VEC);
  setlg((GEN)t, nbfact);
  setlg(ex, nbfact);
  y[1]=lcopy((GEN)t);
  y[2]=lcopy(ex);
  (void)sort_factor(y,cmpii);
  return gerepile(av,tetpil,y);
}
GEN
factmod(GEN f, GEN pp)
{
  gpmem_t tetpil, av=avma;
  long nbfact;
  long j;
  GEN y,u,v;
  GEN z=factmod0(f,pp),t=(GEN)z[1],ex=(GEN)z[2];
  nbfact=lg(t);
  tetpil=avma; y=cgetg(3,t_MAT);
  u=cgetg(nbfact,t_COL); y[1]=(long)u;
  v=cgetg(nbfact,t_COL); y[2]=(long)v;
  for (j=1; j<nbfact; j++)
  {
    u[j] = (long)FpX((GEN)t[j], pp);
    v[j] = lstoi(ex[j]);
  }
  return gerepile(av,tetpil,y);
}
GEN
factormod0(GEN f, GEN p, long flag)
{
  switch(flag)
  {
    case 0: return factmod(f,p);
    case 1: return simplefactmod(f,p);
    default: err(flagerr,"factormod");
  }
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                Recherche de racines  p-adiques                  */
/*                                                                 */
/*******************************************************************/
/* make f suitable for [root|factor]padic */
static GEN
padic_pol_to_int(GEN f)
{
  long i, l = lgef(f);
  GEN c = content(f);
  if (gcmp0(c)) /*  O(p^n) can occur */
  {
    if (typ(c) != t_PADIC) err(typeer,"padic_pol_to_int");
    f = gdiv(f, gpowgs((GEN)c[2], valp(c)));
  }
  else
    f = gdiv(f,c);
  for (i=2; i<l; i++)
    switch(typ(f[i]))
    {
      case t_INT: break;
      case t_PADIC: f[i] = ltrunc((GEN)f[i]); break;
      default: err(talker,"incorrect coeffs in padic_pol_to_int");
    }
  return f;
}

/* return invlead * (x + O(pr)), x in Z or Z_p, pr = p^r. May return gzero */
static GEN
int_to_padic(GEN x, GEN p, GEN pr, long r, GEN invlead)
{
  GEN p1,y;
  long v, sx;
  gpmem_t av = avma;

  if (typ(x) == t_PADIC)
  {
    v = valp(x);
    if (r >= precp(x) + v) return invlead? gmul(x, invlead): gcopy(x);
    sx = !gcmp0(x);
    p1 = (GEN)x[4];
  }
  else
  {
    sx = signe(x);
    if (!sx) return gzero;
    v = pvaluation(x,p,&p1);
  }
  y = cgetg(5,t_PADIC);
  if (sx && v < r)
  {
    y[4] = lmodii(p1,pr); r -= v;
  }
  else
  {
    y[4] = zero; v = r; r = 0;
  }
  y[3] = (long)pr;
  y[2] = (long)p;
  y[1] = evalprecp(r)|evalvalp(v);
  return invlead? gerepileupto(av, gmul(invlead,y)): y;
}

/* as above. always return a t_PADIC */
static GEN
strict_int_to_padic(GEN x, GEN p, GEN pr, long r, GEN invlead)
{
  GEN y = int_to_padic(x, p, pr, r, invlead);
  if (y == gzero) y = ggrandocp(p,r);
  return y;
}

/* return (x + O(p^r)) normalized (multiply by a unit such that leading coeff
 * is a power of p), x in Z[X] (or Z_p[X]) */
static GEN
pol_to_padic(GEN x, GEN pr, GEN p, long r)
{
  long v = 0,i,lx = lgef(x);
  GEN z = cgetg(lx,t_POL), lead = leading_term(x);

  if (gcmp1(lead)) lead = NULL;
  else
  {
    gpmem_t av = avma;
    v = ggval(lead,p);
    if (v) lead = gdiv(lead, gpowgs(p,v));
    lead = int_to_padic(lead,p,pr,r,NULL);
    lead = gerepileupto(av, ginv(lead));
  }
  for (i=lx-1; i>1; i--)
    z[i] = (long)int_to_padic((GEN)x[i],p,pr,r,lead);
  z[1] = x[1]; return z;
}

static GEN
padic_trivfact(GEN x, GEN p, long r)
{
  GEN y = cgetg(3,t_MAT);
  p = icopy(p);
  y[1]=(long)_col(pol_to_padic(x,gpowgs(p,r),p,r));
  y[2]=(long)_col(gun); return y;
}

/* Assume x reduced mod p. q = p^e (simplified version of int_to_padic).
 * If p = 2, is defined (and reduced) mod 4 [from rootmod] */
GEN
Fp_to_Zp(GEN x, GEN p, GEN q, long e)
{
  GEN y = cgetg(5, t_PADIC);
  if (egalii(p, x)) /* implies p = x = 2 */
  {
    x = gun; q = shifti(q, -1);
    y[1] = evalprecp(e-1) | evalvalp(1);
  }
  else if (!signe(x)) y[1] = evalprecp(0) | evalvalp(e);
  else                y[1] = evalprecp(e) | evalvalp(0);
  y[2] = (long)p;
  y[3] = (long)q;
  y[4] = (long)x; return y;
}

/* f != 0 in Z[X], primitive, a t_PADIC s.t f(a) = 0 mod p */
static GEN
apprgen_i(GEN f, GEN a)
{
  GEN fp,u,p,q,P,res,a0,rac;
  long prec,i,j,k;

  prec = gcmp0(a)? valp(a): precp(a);
  if (prec <= 1) return _vec(a);
  fp = derivpol(f); u = ggcd(f,fp);
  if (degpol(u) > 0) { f = gdeuc(f,u); fp = derivpol(f); }
  p = (GEN)a[2];
  P = egalii(p,gdeux)? stoi(4): p;
  a0= gmod(a, P);
#if 0 /* assumption */
  if (!gcmp0(FpX_eval(f,a0,P))) err(rootper2);
#endif
  if (!gcmp0(FpX_eval(fp,a0,p))) /* simple zero */
  {
    res = rootpadiclift(f, a0, p, prec);
    res = strict_int_to_padic(res,p,gpowgs(p,prec),prec,NULL);
    return _vec(res);
  }

  f = poleval(f, gadd(a, gmul(P,polx[varn(f)])));
  f = padic_pol_to_int(f);
  f = gdiv(f, gpowgs(p,ggval(f, p)));

  res = cgetg(degpol(f)+1,t_VEC);
  q = gpowgs(p,prec);
  rac = lift_intern(rootmod(f, P));
  for (j=i=1; i<lg(rac); i++)
  {
    u = apprgen_i(f, Fp_to_Zp((GEN)rac[i], p,q,prec));
    for (k=1; k<lg(u); k++) res[j++] = ladd(a, gmul(P,(GEN)u[k]));
  }
  setlg(res,j); return res;
}

/* a t_PADIC, return vector of p-adic roots of f equal to a (mod p)
 * We assume 1) f(a) = 0 mod p (mod 4 if p=2).
 *           2) leading coeff prime to p. */
GEN
apprgen(GEN f, GEN a)
{
  gpmem_t av = avma;
  if (typ(f) != t_POL) err(notpoler,"apprgen");
  if (gcmp0(f)) err(zeropoler,"apprgen");
  if (typ(a) != t_PADIC) err(rootper1);
  return gerepilecopy(av, apprgen_i(padic_pol_to_int(f), a));
}

static GEN
rootpadic_i(GEN f, GEN p, long prec)
{
  GEN fp,y,z,q,rac;
  long lx,i,j,k;

  fp = derivpol(f); z = ggcd(f,fp);
  if (degpol(z) > 0) { f = gdeuc(f,z); fp = derivpol(f); }
  rac = rootmod(f, (egalii(p,gdeux) && prec>=2)? stoi(4): p);
  rac = lift_intern(rac); lx = lg(rac);
  if (prec==1)
  {
    y = cgetg(lx,t_COL);
    for (i=1; i<lx; i++)
      y[i] = (long)Fp_to_Zp((GEN)rac[i],p,p,1);
    return y;
  }
  y = cgetg(degpol(f)+1,t_COL);
  q = gpowgs(p,prec);
  for (j=i=1; i<lx; i++)
  {
    z = apprgen_i(f, Fp_to_Zp((GEN)rac[i], p,q,prec));
    for (k=1; k<lg(z); k++,j++) y[j] = z[k];
  }
  setlg(y,j); return y;
}

/* reverse x in place */
static void
polreverse(GEN x)
{
  long i, j;
  if (typ(x) != t_POL) err(typeer,"polreverse");
  for (i=2, j=lgef(x)-1; i<j; i++, j--) lswap(x[i], x[j]);
  (void)normalizepol(x);
}

static GEN
pnormalize(GEN f, GEN p, long prec, long n, GEN *plead, long *pprec, int *prev)
{
  *plead = leading_term(f);
  *pprec = prec;
  *prev = 0;
  if (!gcmp1(*plead))
  {
    long val = ggval(*plead,p), val1 = ggval(constant_term(f),p);
    if (val1 < val)
    {
      *prev = 1; polreverse(f);
     /* take care of loss of precision from leading coeff of factor
      * (whose valuation is <= val) */
      *pprec += val;
      val = val1;
    }
    *pprec += val * n;
  }
  return pol_to_monic(f, plead);
}

/* return p-adic roots of f, precision prec */
GEN
rootpadic(GEN f, GEN p, long prec)
{
  gpmem_t av = avma;
  GEN lead,y;
  long PREC,i,k;
  int reverse;

  if (typ(f)!=t_POL) err(notpoler,"rootpadic");
  if (gcmp0(f)) err(zeropoler,"rootpadic");
  if (prec <= 0) err(rootper4);
  f = padic_pol_to_int(f);
  f = pnormalize(f, p, prec, 1, &lead, &PREC, &reverse);

  y = rootpadic_i(f,p,PREC);
  k = lg(y);
  if (lead)
    for (i=1; i<k; i++) y[i] = ldiv((GEN)y[i], lead);
  if (reverse)
    for (i=1; i<k; i++) y[i] = linv((GEN)y[i]);
  return gerepilecopy(av, y);
}
/*************************************************************************/
/*                             rootpadicfast                             */
/*************************************************************************/

/* lift accelerator */
long hensel_lift_accel(long n, long *pmask)
{
  long a,j;
  long mask;
  mask=0;
  for(j=BITS_IN_LONG-1, a=n ;; j--)
  {
    mask|=(a&1)<<j;
    a=(a>>1)+(a&1);
    if (a==1) break;
  }
  *pmask=mask>>j;
  return BITS_IN_LONG-j;
}
/*
  SPEC:
  q is an integer > 1
  e>=0
  f in ZZ[X], with leading term prime to q.
  S must be a simple root mod p for all p|q.

  return roots of f mod q^e, as integers (implicitly mod Q)
*/

/* STANDARD USE
   There exists p a prime number and a>0 such that
   q=p^a
   f in ZZ[X], with leading term prime to p.
   S must be a simple root mod p.

   return p-adics roots of f with prec b, as integers (implicitly mod q^e)
*/

GEN
rootpadiclift(GEN T, GEN S, GEN p, long e)
{
  gpmem_t ltop=avma;
  long    x;
  GEN     qold, q, qm1;
  GEN     W, Tr, Sr, Wr = gzero;
  long     i, nb, mask;
  x = varn(T);
  qold = p ;  q = p; qm1 = gun;
  nb=hensel_lift_accel(e, &mask);
  Tr = FpX_red(T,q);
  W=FpX_eval(deriv(Tr, x),S,q);
  W=mpinvmod(W,q);
  for(i=0;i<nb;i++)
  {
    qm1 = (mask&(1<<i))?sqri(qm1):mulii(qm1, q);
    q   =  mulii(qm1, p);
    Tr = FpX_red(T,q);
    Sr = S;
    if (i)
    {
      W = modii(mulii(Wr,FpX_eval(deriv(Tr,x),Sr,qold)),qold);
      W = subii(gdeux,W);
      W = modii(mulii(Wr, W),qold);
    }
    Wr = W;
    S = subii(Sr, mulii(Wr, FpX_eval(Tr, Sr,q)));
    S = modii(S,q);
    qold = q;
  }
  return gerepileupto(ltop,S);
}
/*
 * Apply rootpadiclift to all roots in S and trace trick.
 * Elements of S must be distinct simple roots mod p for all p|q.
 */

GEN
rootpadicliftroots(GEN f, GEN S, GEN q, long e)
{
  GEN y;
  long i,n=lg(S);
  if (n==1)
    return gcopy(S);
  y=cgetg(n,typ(S));
  for (i=1; i<n-1; i++)
    y[i]=(long) rootpadiclift(f, (GEN) S[i], q, e);
  if (n!=lgef(f)-2)/* non totally split*/
    y[n-1]=(long) rootpadiclift(f, (GEN) S[n-1], q, e);
  else/* distinct-->totally split-->use trace trick */
  {
    gpmem_t av=avma;
    GEN z;
    z=(GEN)f[lgef(f)-2];/*-trace(roots)*/
    for(i=1; i<n-1;i++)
      z=addii(z,(GEN) y[i]);
    z=modii(negi(z),gpowgs(q,e));
    y[n-1]=lpileupto(av,z);
  }
  return y;
}
/*
 p is a prime number, pr a power of p,

 f in ZZ[X], with leading term prime to p.
 f must have no multiple roots mod p.

 return p-adics roots of f with prec pr, as integers (implicitly mod pr)

*/
GEN
rootpadicfast(GEN f, GEN p, long e)
{
  gpmem_t ltop=avma;
  GEN S,y;
  S=lift(rootmod(f,p));/*no multiplicity*/
  if (lg(S)==1)/*no roots*/
  {
    avma=ltop;
    return cgetg(1,t_COL);
  }
  S=gclone(S);
  avma=ltop;
  y=rootpadicliftroots(f,S,p,e);
  gunclone(S);
  return y;
}
/* Same as rootpadiclift for the polynomial X^n-a,
 * but here, n can be much larger.
 * TODO: generalize to sparse polynomials.
 */
GEN
padicsqrtnlift(GEN a, GEN n, GEN S, GEN p, long e)
{
  gpmem_t ltop=avma;
  GEN     qold, q, qm1;
  GEN     W, Sr, Wr = gzero;
  long    i, nb, mask;
  qold = p ; q = p; qm1 = gun;
  nb   = hensel_lift_accel(e, &mask);
  W    = modii(mulii(n,powmodulo(S,subii(n,gun),q)),q);
  W    = mpinvmod(W,q);
  for(i=0;i<nb;i++)
  {
    qm1 = (mask&(1<<i))?sqri(qm1):mulii(qm1, q);
    q   =  mulii(qm1, p);
    Sr = S;
    if (i)
    {
      W = modii(mulii(Wr,mulii(n,powmodulo(Sr,subii(n,gun),qold))),qold);
      W = subii(gdeux,W);
      W = modii(mulii(Wr, W),qold);
    }
    Wr = W;
    S = subii(Sr, mulii(Wr, subii(powmodulo(Sr,n,q),a)));
    S = modii(S,q);
    qold = q;
  }
  return gerepileupto(ltop,S);
}
/**************************************************************************/
static void
scalar_getprec(GEN x, long *pprec, GEN *pp)
{
  if (typ(x)==t_PADIC)
  {
    long e = valp(x); if (signe(x[4])) e += precp(x);
    if (e < *pprec) *pprec = e;
    if (*pp && !egalii(*pp, (GEN)x[2])) err(consister,"apprpadic");
    *pp = (GEN)x[2];
  }
}

static void
getprec(GEN x, long *pprec, GEN *pp)
{
  long i;
  if (typ(x) != t_POL)
    scalar_getprec(x, pprec, pp);
  else
    for (i = lgef(x)-1; i>1; i--)
      scalar_getprec((GEN)x[i], pprec, pp);
}

/* a belongs to finite extension of Q_p, return all roots of f equal to a
 * mod p. We assume f(a) = 0 (mod p) [mod 4 if p=2] */
GEN
apprgen9(GEN f, GEN a)
{
  GEN fp, p1, P, p, pro, x, x2, u, ip, T, vecg;
  long v, ps_1, i, j, k, n, prec, d, va, fl2;
  gpmem_t av = avma;

  if (typ(f)!=t_POL) err(notpoler,"apprgen9");
  if (gcmp0(f)) err(zeropoler,"apprgen9");
  if (typ(a)==t_PADIC) return apprgen(f,a);
  if (typ(a)!=t_POLMOD) err(rootper1);
  fp = derivpol(f); u = ggcd(f,fp);
  if (degpol(u) > 0) { f = gdeuc(f,u); fp = derivpol(f); }
  T = (GEN)a[1];
  p = NULL;
  prec = BIGINT;
  getprec((GEN)a[2], &prec, &p);
  getprec(T, &prec, &p);
  if (!p) err(rootper1);

  p1 = poleval(f,a); v = ggval(lift_intern(p1),p); if (v<=0) err(rootper2);
  fl2 = egalii(p,gdeux);
  if (fl2 && v==1) err(rootper2);
  v = ggval(lift_intern(poleval(fp,a)), p);
  if (!v)
  {
    while (!gcmp0(p1))
    {
      a = gsub(a, gdiv(p1, poleval(fp,a)));
      p1 = poleval(f,a);
    }
    return gerepilecopy(av, _col(a));
  }
  n = degpol(f);
  pro = cgetg(n+1,t_COL);

  if (is_bigint(p)) err(impl,"apprgen9 for p>=2^31");
  x = gmodulcp(ggrandocp(p,prec), T);
  if (fl2)
  {
    x2 = ggrandocp(p,2);
    P = stoi(4);
  }
  else
  {
    x2 = ggrandocp(p,1);
    P = p;
  }
  ps_1 = itos(p)-1;
  f = poleval(f, gadd(a, gmul(P,polx[varn(f)])));
  f = gdiv(f, gpowgs(p, ggval(f,p)));

  d = degpol(T); vecg = cgetg(d+1,t_COL);
  for (i=1; i<=d; i++) vecg[i] = (long)setloop(gzero);
  va = varn(T); j = 1;
  for(;;) /* loop through F_q */
  {
    ip = gmodulcp(gtopoly(vecg,va), T);
    if (gcmp0(poleval(f, gadd(ip,x2))))
    {
      u = apprgen9(f, gadd(ip,x));
      for (k=1; k<lg(u); k++) pro[j++] = ladd(a, gmul(P,(GEN)u[k]));
    }
    for (i=d; i; i--)
    {
      p1 = (GEN)vecg[i];
      if (itos(p1) != ps_1) { vecg[i] = (long)incloop(p1); break; }
      affsi(0, p1);
    }
    if (!i) break;
  }
  setlg(pro,j); return gerepilecopy(av, pro);
}

/*******************************************************************/
/*                                                                 */
/*                      FACTORIZATION in Zp[X]                     */
/*                                                                 */
/*******************************************************************/
extern GEN ZX_squff(GEN f, GEN *ex);
extern GEN fact_from_DDF(GEN fa, GEN e, long n);

int
cmp_padic(GEN x, GEN y)
{
  long vx, vy;
  if (x == gzero) return -1;
  if (y == gzero) return  1;
  vx = valp(x);
  vy = valp(y);
  if (vx < vy) return  1;
  if (vx > vy) return -1;
  return cmpii((GEN)x[4], (GEN)y[4]);
}

/*******************************/
/*   Using Buchmann--Lenstra   */
/*******************************/

/* factor T = nf[1] in Zp to precision k */
static GEN
padicff2(GEN nf,GEN p,long k)
{
  GEN z, mat, D, U,fa, pk, dec_p, Ui, mulx;
  long i, l;

  mulx = eltmul_get_table(nf, gmael(nf,8,2)); /* mul by (x mod T) */
  dec_p = primedec(nf,p);
  l = lg(dec_p); fa = cgetg(l,t_COL);
  D = NULL; /* -Wall */
  for (i=1; i<l; i++)
  {
    GEN P = (GEN)dec_p[i];
    long e = itos((GEN)P[3]), ef = e * itos((GEN)P[4]);
    D = smithall(idealpows(nf,P, k*e), &U, NULL);
    Ui= ginv(U); setlg(Ui, ef+1); /* cf smithrel */
    U = rowextract_i(U, 1, ef);
    mat = gmul(U, gmul(mulx, Ui));
    fa[i] = (long)caradj(mat,0,NULL);
  }
  pk = gcoeff(D,1,1); /* = p^k */
  z = cgetg(l,t_COL); pk = icopy(pk);
  for (i=1; i<l; i++)
    z[i] = (long)pol_to_padic((GEN)fa[i],pk,p,k);
  return z;
}

static GEN
padicff(GEN x,GEN p,long pr)
{
  GEN q,basden,bas,invbas,mul,dx,dK,nf,fa,g,e;
  long n=degpol(x);
  gpmem_t av=avma;

  nf=cgetg(10,t_VEC); nf[1]=(long)x;
  fa = cgetg(3,t_MAT);
  g = cgetg(3,t_COL); fa[1] = (long)g;
  e = cgetg(3,t_COL); fa[2] = (long)e;
  dx = ZX_disc(x);
  g[1] = (long)p; e[1] = lstoi(pvaluation(absi(dx),p,&q));
  g[2] = (long)q; e[2] = un;

  bas = nfbasis(x, &dK, 0, fa);
  nf[3] = (long)dK;
  nf[4] = divise( diviiexact(dx, dK), p )? (long)p: un;
  basden = get_bas_den(bas);
  invbas = QM_inv(vecpol_to_mat(bas,n), gun);
  mul = get_mul_table(x,basden,invbas);
  nf[7]=(long)bas;
  nf[8]=(long)invbas;
  nf[9]=(long)mul; nf[2]=nf[5]=nf[6]=zero;
  return gerepileupto(av,padicff2(nf,p,pr));
}

GEN
factorpadic2(GEN f, GEN p, long prec)
{
  gpmem_t av = avma;
  GEN fa,ex,y;
  long n,i,l;

  if (typ(f)!=t_POL) err(notpoler,"factorpadic");
  if (gcmp0(f)) err(zeropoler,"factorpadic");
  if (prec<=0) err(rootper4);

  n = degpol(f);
  if (n==0) return trivfact();
  if (n==1) return padic_trivfact(f,p,prec);
  if (!gcmp1(leading_term(f)))
    err(impl,"factorpadic2 for non-monic polynomial");
  f = padic_pol_to_int(f);

  fa = ZX_squff(f, &ex);
  l = lg(fa); n = 0;
  for (i=1; i<l; i++)
  {
    fa[i] = (long)padicff((GEN)fa[i],p,prec);
    n += lg(fa[i])-1;
  }

  y = fact_from_DDF(fa,ex,n);
  return gerepileupto(av, sort_factor(y, cmp_padic));
}

/***********************/
/*   Using ROUND 4     */
/***********************/
extern GEN Decomp(GEN p,GEN f,long mf,GEN theta,GEN chi,GEN nu,long r);
extern GEN nilord(GEN p, GEN fx, long mf, GEN gx, long flag);
extern GEN hensel_lift_fact(GEN pol, GEN Q, GEN T, GEN p, GEN pev, long e);

static int
expo_is_squarefree(GEN e)
{
  long i, l = lg(e);
  for (i=1; i<l; i++)
    if (e[i] != 1) return 0;
  return 1;
}

GEN
factorpadic4(GEN f,GEN p,long prec)
{
  gpmem_t av = avma;
  GEN w,g,poly,y,p1,p2,ex,pols,exps,ppow,lead,lead_orig;
  long v=varn(f),n=degpol(f),mfx,i,k,j,r,pr,d;
  int reverse = 0;

  if (typ(f)!=t_POL) err(notpoler,"factorpadic");
  if (typ(p)!=t_INT) err(arither1);
  if (gcmp0(f)) err(zeropoler,"factorpadic");
  if (prec<=0) err(rootper4);

  if (n==0) return trivfact();
  if (n==1) return padic_trivfact(f,p,prec);
  lead_orig = pollead(f, -1);
  f = padic_pol_to_int(f);
  f = pnormalize(f, p, prec, n-1, &lead, &pr, &reverse);

  poly = ZX_squff(f,&ex);
  pols = cgetg(n+1,t_COL);
  exps = cgetg(n+1,t_COL); n = lg(poly);
  for (j=i=1; i<n; i++)
  {
    gpmem_t av1 = avma;
    GEN fx = (GEN)poly[i], fa = factmod0(fx,p);
    w = (GEN)fa[1];
    if (expo_is_squarefree((GEN)fa[2]))
    { /* no repeated factors: Hensel lift */
      p1 = hensel_lift_fact(fx, w, NULL, p, gpowgs(p,pr), pr);
      p2 = stoi(ex[i]);
      for (k=1; k<lg(p1); k++,j++)
      {
        pols[j] = p1[k];
        exps[j] = (long)p2;
      }
      continue;
    }
    /* use Round 4 */
    mfx = ggval(ZX_disc(fx),p);
    r = lg(w)-1;
    g = (GEN)w[r];
    p2 = (r == 1)? nilord(p,fx,mfx,g,pr)
                 : Decomp(p,fx,mfx,polx[v],fx,g, (pr<=mfx)? mfx+1: pr);
    if (p2)
    {
      p2 = gerepilecopy(av1,p2);
      p1 = (GEN)p2[1];
      p2 = (GEN)p2[2];
      for (k=1; k<lg(p1); k++,j++)
      {
        pols[j] = p1[k];
        exps[j] = lmulis((GEN)p2[k],ex[i]);
      }
    }
    else
    {
      avma = av1;
      pols[j] = (long)fx;
      exps[j] = lstoi(ex[i]); j++;
    }
  }
  if (lead)
    for (i=1; i<j; i++)
      pols[i] = (long)primpart( unscale_pol((GEN)pols[i], lead) );
  y = cgetg(3,t_MAT);
  p1 = cgetg(j,t_COL); p = icopy(p); ppow = gpowgs(p,prec);
  for (i=1; i<j; i++)
  {
    if (reverse) polreverse((GEN)pols[i]);
    p1[i] = (long)pol_to_padic((GEN)pols[i],ppow,p,prec);
  }
  d = ggval(lead_orig, p);
  lead_orig = gmul(lead_orig, gpowgs(p, -d));
  p1[1] = lmul((GEN)p1[1], lead_orig);
  y[1] = (long)p1; setlg(exps,j);
  y[2] = lcopy(exps);
  return gerepileupto(av, sort_factor(y, cmp_padic));
}

GEN
factorpadic0(GEN f,GEN p,long r,long flag)
{
  switch(flag)
  {
     case 0: return factorpadic4(f,p,r);
     case 1: return factorpadic2(f,p,r);
     default: err(flagerr,"factorpadic");
  }
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                     FACTORISATION DANS F_q                      */
/*                                                                 */
/*******************************************************************/
extern GEN to_Kronecker(GEN P, GEN Q);
static GEN spec_Fq_pow_mod_pol(GEN x, GEN S, GEN T, GEN p);

static GEN
to_Fq(GEN x, GEN T, GEN p)
{
  long i,lx, tx = typ(x);
  GEN z = cgetg(3,t_POLMOD), y;

  if (tx == t_INT)
    y = mod(x,p);
  else
  {
    if (tx != t_POL) err(typeer,"to_Fq");
    lx = lgef(x);
    y = cgetg(lx,t_POL);
    y[1] = x[1];
    if (lx == 2) setsigne(y, 0);
    else
      for (i=2; i<lx; i++) y[i] = (long)mod((GEN)x[i], p);
  }
  /* assume deg(y) < deg(T) */
  z[1] = (long)T;
  z[2] = (long)y; return z;
}

static GEN
to_Fq_pol(GEN x, GEN T, GEN p)
{
  long i, lx, tx = typ(x);
  if (tx != t_POL) err(typeer,"to_Fq_pol");
  lx = lgef(x);
  for (i=2; i<lx; i++) x[i] = (long)to_Fq((GEN)x[i],T,p);
  return x;
}

/* assume T a clone */
static GEN
copy_then_free(GEN T)
{
  GEN t = forcecopy(T); gunclone(T); return t;
}

static GEN
to_Fq_fact(GEN t, GEN ex, long nbf, int sort, GEN unfq, gpmem_t av)
{
  GEN T = (GEN)unfq[1]/*clone*/, y = cgetg(3,t_MAT), u,v,p;
  long j,k, l = lg(t);

  u = cgetg(nbf,t_COL); y[1] = (long)u;
  v = cgetg(nbf,t_COL); y[2] = (long)v;
  for (j=1,k=0; j<l; j++)
    if (ex[j])
    {
      k++;
      u[k] = (long)simplify((GEN)t[j]); /* may contain pols of degree 0 */
      v[k] = lstoi(ex[j]);
    }
  y = gerepileupto(av, y);
  if (sort) y = sort_factor(y,cmp_pol);
  T = copy_then_free(T);
  p = (GEN)leading_term(T)[1];
  u = (GEN)y[1];
  for (j=1; j<nbf; j++) u[j] = (long)to_Fq_pol((GEN)u[j], T,p);
  return y;
}

/* split into r factors of degree d */
static void
FqX_split(GEN *t, long d, GEN q, GEN S, GEN T, GEN p)
{
  long l, v, is2, cnt, dt = degpol(*t), dT = degpol(T);
  gpmem_t av;
  GEN w,w0;

  if (dt == d) return;
  v = varn(*t);
  if (DEBUGLEVEL > 6) (void)timer2();
  av = avma; is2 = egalii(p, gdeux);
  for(cnt = 1;;cnt++)
  { /* splits *t with probability ~ 1 - 2^(1-r) */
    w = w0 = FqX_rand(dt,v, T,p);
    for (l=1; l<d; l++) /* sum_{0<i<d} w^(q^i), result in (F_q)^r */
      w = gadd(w0, spec_Fq_pow_mod_pol(w, S, T, p));
    w = FqX_red(w, T,p);
    if (is2)
    {
      w0 = w;
      for (l=1; l<dT; l++) /* sum_{0<i<k} w^(2^i), result in (F_2)^r */
      {
        w = FqX_rem(FqX_sqr(w,T,p), *t, T,p);
        w = FqX_red(gadd(w0,w), NULL,p);
      }
    }
    else
    {
      w = FqXQ_pow(w, shifti(q,-1), *t, T, p);
      /* w in {-1,0,1}^r */
      if (!degpol(w)) continue;
      w[2] = ladd((GEN)w[2], gun);
    }
    w = FqX_gcd(*t,w, T,p); l = degpol(w);
    if (l && l != dt) break;
    avma = av;
  }
  w = gerepileupto(av,w);
  if (DEBUGLEVEL > 6)
    fprintferr("[FqX_split] splitting time: %ld (%ld trials)\n",timer2(),cnt);
  l /= d; t[l] = FqX_div(*t,w, T,p); *t = w;
  FqX_split(t+l,d,q,S,T,p);
  FqX_split(t  ,d,q,S,T,p);
}

/* to "compare" (real) scalars and t_INTMODs */
static int
cmp_coeff(GEN x, GEN y)
{
  if (typ(x) == t_INTMOD) x = (GEN)x[2];
  if (typ(y) == t_INTMOD) y = (GEN)y[2];
  return gcmp(x,y);
}

int
cmp_pol(GEN x, GEN y)
{
  long fx[3], fy[3];
  long i,lx,ly;
  int fl;
  if (typ(x) == t_POLMOD) x = (GEN)x[2];
  if (typ(y) == t_POLMOD) y = (GEN)y[2];
  if (typ(x) == t_POL) lx = lgef(x); else { lx = 3; fx[2] = (long)x; x = fx; }
  if (typ(y) == t_POL) ly = lgef(y); else { ly = 3; fy[2] = (long)y; y = fy; }
  if (lx > ly) return  1;
  if (lx < ly) return -1;
  for (i=lx-1; i>1; i--)
    if ((fl = cmp_coeff((GEN)x[i], (GEN)y[i]))) return fl;
  return 0;
}

/* assume n > 1, X over FqX */
/* return S = [ X^q, X^2q, ... X^(n-1)q ] mod u (in Fq[X]) in Kronecker form */
static GEN
init_pow_q_mod_pT(GEN X, GEN q, GEN u, GEN T, GEN p)
{
  long i, n = degpol(u);
  GEN p1, S = cgetg(n, t_VEC);

  S[1] = (long)FqXQ_pow(X, q, u, T, p);
#if 1 /* use as many squarings as possible */
  for (i=2; i < n; i+=2)
  {
    p1 = gsqr((GEN)S[i>>1]);
    S[i]   = (long)FqX_rem(p1, u, T,p);
    if (i == n-1) break;
    p1 = gmul((GEN)S[i], (GEN)S[1]);
    S[i+1] = (long)FqX_rem(p1, u, T,p);
  }
#else
  for (i=2; i < n; i++)
  {
    p1 = gmul((GEN)S[i-1], (GEN)S[1]);
    S[i] = (long)FqX_rem(p1, u, T,p);
  }
#endif
  for (i=1; i < n; i++)
    S[i] = (long)to_Kronecker((GEN)S[i], T);
  return S;
}

/* compute x^q, S is as above */
static GEN
spec_Fq_pow_mod_pol(GEN x, GEN S, GEN T, GEN p)
{
  long i, dx = degpol(x);
  gpmem_t av = avma, lim = stack_lim(av, 1);
  GEN x0 = x+2, z,c;

  z = c = (GEN)x0[0];
  for (i = 1; i <= dx; i++)
  {
    GEN d;
    c = (GEN)x0[i];
    if (gcmp0(c)) continue;
    d = (GEN)S[i];
    if (!gcmp1(c)) d = gmul(c,d);
    z = gadd(z, d);
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"spec_Fq_pow_mod_pol");
      z = gerepileupto(av, z);
    }
  }
  z = FpXQX_from_Kronecker(z, T, p);
  setvarn(z, varn(x)); return gerepileupto(av, z);
}

static long
isabsolutepol(GEN f)
{
  int i, l = lgef(f);
  for(i=2; i<l; i++)
  {
    GEN c = (GEN)f[i];
    if (typ(c) == t_POL && degpol(c) > 0) return 0;
  }
  return 1;
}

GEN
factmod9(GEN f, GEN p, GEN T)
{
  gpmem_t av = avma;
  long pg, i, j, k, d, e, N, vf, va, nbfact, nbf, pk;
  GEN S,ex,f2,f3,df1,df2,g1,u,v,q,unfp,unfq, *t;
  GEN frobinv,X;

  if (typ(T)!=t_POL || typ(f)!=t_POL || gcmp0(T)) err(typeer,"factmod9");
  vf = varn(f);
  va = varn(T);
  if (va <= vf)
    err(talker,"polynomial variable must have higher priority in factorff");
  unfp = gmodulsg(1,p); T = gmul(unfp,T);
  unfq = gmodulo(gmul(unfp,polun[va]), T);
  f = gmul(unfq,f);
  if (!signe(f)) err(zeropoler,"factmod9");
  d = degpol(f); if (!d) { avma = av; return trivfact(); }

  f = simplify(lift_intern(lift_intern(f)));
  T = lift_intern(T);
  if (isabsolutepol(f))
  {
    GEN z = Fp_factor_rel0(f, p, T);
    return to_Fq_fact((GEN)z[1],(GEN)z[2],lg(z[1]), 0, unfq,av);
  }

  pg = is_bigint(p)? 0: itos(p);
  S = df2  = NULL; /* gcc -Wall */
  t = (GEN*)cgetg(d+1,t_VEC); ex = new_chunk(d+1);

  frobinv = gpowgs(p, degpol(T)-1);

  X = polx[vf];
  q = gpowgs(p, degpol(T));
  e = nbfact = 1;
  pk = 1;
  f3 = NULL;
  df1 = FqX_deriv(f, T, p);
  for(;;)
  {
    while (gcmp0(df1))
    { /* needs d >= p: pg = 0 can't happen  */
      pk *= pg; e = pk;
      j = (degpol(f))/pg+3; setlg(f,j); setlgef(f,j);
      for (i=2; i<j; i++)
        f[i] = (long)Fq_pow((GEN)f[pg*(i-2)+2], frobinv, T,p);
      df1 = FqX_deriv(f, T, p); f3 = NULL;
    }
    f2 = f3? f3: FqX_gcd(f,df1, T,p);
    if (!degpol(f2)) u = f;
    else
    {
      g1 = FqX_div(f,f2, T,p); df2 = FqX_deriv(f2, T,p);
      if (gcmp0(df2)) { u = g1; f3 = f2; }
      else
      {
        f3 = FqX_gcd(f2,df2, T,p);
        if (!degpol(f3)) u = FqX_div(g1,f2, T,p);
        else
          u = FqX_div(g1, FqX_div(f2,f3, T,p), T,p);
      }
    }
    /* u is square-free (product of irreducibles of multiplicity e) */

#if 0
    N = degpol(u);
    if (N)
    {
      t[nbfact] = FpXQX_normalize(u, T,p);
      d = (N==1)? 1: FqX_split_berlekamp(t+nbfact, q, T, p);
      for (j=0; j<d; j++) ex[nbfact+j] = e;
      nbfact += d;
    }
#else
{
    GEN qqd = gun, g;
    long dg;

    N = degpol(u); v = X;
    if (N > 1) S = init_pow_q_mod_pT(X, q, u, T, p);
    for (d=1; d <= N>>1; d++)
    {
      qqd = mulii(qqd,q);
      v = spec_Fq_pow_mod_pol(v, S, T, p);
      g = FqX_gcd(gsub(v,X),u, T,p);
      dg = degpol(g);
      if (dg <= 0) continue;

      /* all factors of g have degree d */
      j = nbfact+dg/d;

      t[nbfact] = g;
      FqX_split(t+nbfact,d,q,S,T,p);
      for (; nbfact<j; nbfact++) ex[nbfact] = e;
      N -= dg;
      u = FqX_div(u,g, T,p);
      v = FqX_rem(v,u, T,p);
    }
    if (N) { t[nbfact] = u; ex[nbfact++] = e; }
}
#endif
    if (!degpol(f2)) break;

    f = f2; df1 = df2; e += pk;
  }

  nbf = nbfact; setlg(t, nbfact);
  for (j=1; j<nbfact; j++)
  {
    t[j] = FpXQX_normalize((GEN)t[j], T,p);
    for (k=1; k<j; k++)
      if (ex[k] && gegal(t[j],t[k]))
      {
        ex[k] += ex[j]; ex[j]=0;
        nbf--; break;
      }
  }
  return to_Fq_fact((GEN)t,ex,nbf, 1, unfq,av);
}
/* See also: Isomorphisms between finite field and relative
 * factorization in polarit3.c */

/*******************************************************************/
/*                                                                 */
/*                         RACINES COMPLEXES                       */
/*        l represente la longueur voulue pour les parties         */
/*            reelles et imaginaires des racines de x              */
/*                                                                 */
/*******************************************************************/
GEN square_free_factorization(GEN pol);
static GEN laguer(GEN pol,long N,GEN y0,GEN EPS,long PREC);
GEN zrhqr(GEN a,long PREC);

GEN
rootsold(GEN x, long l)
{
  long i, j, f, g, gg, fr, deg, ln;
  gpmem_t av=avma, av0, av1, av2, av3;
  long exc,expmin,m,deg0,k,ti,h,ii,e, v = varn(x);
  GEN y,xc,xd0,xd,xdabs,p1,p2,p3,p4,p5,p6,p7,p8;
  GEN p9,p10,p11,p12,p14,p15,pa,pax,pb,pp,pq,ps;

  if (typ(x)!=t_POL) err(typeer,"rootsold");
  deg0=degpol(x); expmin=12 - bit_accuracy(l);
  if (!signe(x)) err(zeropoler,"rootsold");
  y=cgetg(deg0+1,t_COL); if (!deg0) return y;
  for (i=1; i<=deg0; i++)
  {
    p1=cgetg(3,t_COMPLEX); p1[1]=lgetr(l); p1[2]=lgetr(l); y[i]=(long)p1;
    for (j=3; j<l; j++) ((GEN)p1[2])[j]=((GEN)p1[1])[j]=0;
  }
  g=1; gg=1;
  for (i=2; i<=deg0+2; i++)
  {
    ti=typ(x[i]);
    if (ti==t_REAL) gg=0;
    else if (ti==t_QUAD)
    {
      p2 = gmael3(x,i,1,2);
      if (gsigne(p2) > 0) g = 0;
    } else if (ti != t_INT && ti != t_INTMOD && !is_frac_t(ti)) g=0;
  }
  av1 = avma;
  for (i=2; i<=deg0+2 && gcmp0((GEN)x[i]); i++) gaffsg(0,(GEN)y[i-1]);
  k = i-2;
  if (k==deg0) return y;

  p2=cgetg(3,t_COMPLEX);
  p2[1] = lmppi(DEFAULTPREC);
  p2[2] = ldivrs((GEN)p2[1],10); /* Pi * (1+I/10) */
  p11=cgetg(4,t_POL); p11[1]=evalsigne(1)|evalvarn(v)|evallgef(4);
  p11[3]=un;

  p12=cgetg(5,t_POL); p12[1]=evalsigne(1)|evalvarn(v)|evallgef(5);
  p12[4]=un;
  if (k)
  {
    j=deg0+3-k; pax=cgetg(j,t_POL);
    pax[1] = evalsigne(1) | evalvarn(v) | evallgef(j);
    for (i=2; i<j; i++) pax[i]=x[i+k];
  }
  else pax=x;
  xd0=deriv(pax,v); pa=pax;
  pq = NULL; /* for lint */
  if (gg) { pp=ggcd(pax,xd0); h=isnonscalar(pp); if (h) pq=gdeuc(pax,pp); }
  else{ pp=gun; h=0; }
  m = 0;
  while (k != deg0)
  {
    m++;
    if (h)
    {
      pa=pp; pb=pq; pp=ggcd(pa,deriv(pa,v)); h=isnonscalar(pp);
      if (h) pq=gdeuc(pa,pp); else pq=pa; ps=gdeuc(pb,pq);
    }
    else ps = pa;
    deg = degpol(ps); if (!deg) continue;

    /* roots of exact order m */
    av3 = avma;
    e = gexpo(ps) - gexpo(leading_term(ps));
    if (e < 0) e = 0; if (ps!=pax) xd0=deriv(ps,v);
    xdabs=cgetg(deg+2,t_POL); xdabs[1]=xd0[1];
    for (i=2; i<deg+2; i++)
    {
      av3=avma; p3=(GEN)xd0[i];
      p4=gabs(greal(p3),l);
      p5=gabs(gimag(p3),l);
      xdabs[i]=lpileupto(av3, gadd(p4,p5));
    }
    av0=avma; xc=gcopy(ps); xd=gcopy(xd0); av2=avma;
    for (i=1; i<=deg; i++)
    {
      if (i==deg)
      {
        p1=(GEN)y[k+m*i]; gdivz(gneg_i((GEN)xc[2]),(GEN)xc[3],p1);
        p14=(GEN)p1[1]; p15=(GEN)p1[2];
      }
      else
      {
        p3=gshift(p2,e); p4=poleval(xc,p3); p5=gnorm(p4); exc=0;
        while (exc >= -20)
        {
          p7 = gneg_i(gdiv(p4, poleval(xd,p3)));
          av3 = avma;
          if (gcmp0(p5)) exc = -32;
          else exc = expo(gnorm(p7))-expo(gnorm(p3));
          avma = av3;
          for (j=1; j<=10; j++)
          {
            p8=gadd(p3,p7); p9=poleval(xc,p8); p10=gnorm(p9);
            if (exc < -20 || cmprr(p10,p5) < 0)
            {
              GEN *gptr[3];
              p3=p8; p4=p9; p5=p10;
              gptr[0]=&p3; gptr[1]=&p4; gptr[2]=&p5;
              gerepilemanysp(av2,av3,gptr,3);
              break;
            }
            gshiftz(p7,-2,p7); avma=av3;
          }
          if (j > 10)
          {
            avma = av;
            if (DEBUGLEVEL)
              err(warner,"too many iterations in rootsold(): using roots2()");
            return roots2(x,l);
          }
        }
        p1=(GEN)y[k+m*i]; setlg(p1[1],3); setlg(p1[2],3); gaffect(p3,p1);
        avma=av2; p14=(GEN)p1[1]; p15=(GEN)p1[2];
        for (ln=4; ln<=l; ln=(ln<<1)-2)
        {
          setlg(p14,ln); setlg(p15,ln);
          if (gcmp0(p14)) { settyp(p14,t_INT); p14[1]=2; }
          if (gcmp0(p15)) { settyp(p15,t_INT); p15[1]=2; }
          p4=poleval(xc,p1);
          p5=poleval(xd,p1); p6=gneg_i(gdiv(p4,p5));
          settyp(p14,t_REAL); settyp(p15,t_REAL);
          gaffect(gadd(p1,p6),p1); avma=av2;
        }
      }
      setlg(p14,l); setlg(p15,l);
      p7=gcopy(p1); p14=(GEN)(p7[1]); p15=(GEN)(p7[2]);
      setlg(p14,l+1); setlg(p15,l+1);
      if (gcmp0(p14)) { settyp(p14,t_INT); p14[1]=2; }
      if (gcmp0(p15)) { settyp(p15,t_INT); p15[1]=2; }
      for (ii=1; ii<=5; ii++)
      {
        p4=poleval(ps,p7); p5=poleval(xd0,p7);
        p6=gneg_i(gdiv(p4,p5)); p7=gadd(p7,p6);
        p14=(GEN)(p7[1]); p15=(GEN)(p7[2]);
        if (gcmp0(p14)) { settyp(p14,t_INT); p14[1]=2; }
        if (gcmp0(p15)) { settyp(p15,t_INT); p15[1]=2; }
      }
      gaffect(p7,p1); p4=poleval(ps,p7);
      p6=gdiv(p4,poleval(xdabs,gabs(p7,l)));
      if (gexpo(p6)>=expmin)
      {
        avma=av;
        if (DEBUGLEVEL)
          err(warner,"internal error in rootsold(): using roots2()");
        return roots2(x,l);
      }
      avma=av2;
      if (expo(p1[2])<expmin && g)
      {
        gaffect(gzero,(GEN)p1[2]);
        for (j=1; j<m; j++) gaffect(p1,(GEN)y[k+(i-1)*m+j]);
        p11[2]=lneg((GEN)p1[1]);
        xc=gerepileupto(av0, gdeuc(xc,p11));
      }
      else
      {
        for (j=1; j<m; j++) gaffect(p1,(GEN)y[k+(i-1)*m+j]);
        if (g)
        {
          p1=gconj(p1);
          for (j=1; j<=m; j++) gaffect(p1,(GEN)y[k+i*m+j]);
          i++;
          p12[2]=lnorm(p1); p12[3]=lmulsg(-2,(GEN)p1[1]);
          xc=gerepileupto(av0, gdeuc(xc,p12));
        }
        else
        {
          p11[2]=lneg(p1);
          xc=gerepileupto(av0, gdeuc(xc,p11));
        }
      }
      xd=deriv(xc,v); av2=avma;
    }
    k += deg*m;
  }
  avma = av1;
  for (j=2; j<=deg0; j++)
  {
    p1 = (GEN)y[j];
    if (gcmp0((GEN)p1[2])) fr=0; else fr=1;
    for (k=j-1; k>=1; k--)
    {
      p2 = (GEN)y[k];
      if (gcmp0((GEN)p2[2])) f=0; else f=1;
      if (f<fr) break;
      if (f==fr && gcmp((GEN)p2[1],(GEN)p1[1]) <= 0) break;
      y[k+1] = y[k];
    }
    y[k+1] = (long)p1;
  }
  return y;
}

GEN
roots2(GEN pol,long PREC)
{
  gpmem_t av = avma;
  long N,flagexactpol,flagrealpol,flagrealrac,ti,i,j;
  long nbpol, k, multiqol, deg, nbroot, fr, f;
  gpmem_t av1;
  GEN p1,p2,rr,EPS,qol,qolbis,x,b,c,*ad,v,tabqol;

  if (typ(pol)!=t_POL) err(typeer,"roots2");
  if (!signe(pol)) err(zeropoler,"roots2");
  N=degpol(pol);
  if (!N) return cgetg(1,t_COL);
  if (N==1)
  {
    p1 = gmul(realun(PREC),(GEN)pol[3]);
    p2 = gneg_i(gdiv((GEN)pol[2],p1));
    return gerepilecopy(av,p2);
  }
  EPS = real2n(12 - bit_accuracy(PREC), 3);
  flagrealpol=1; flagexactpol=1;
  for (i=2; i<=N+2; i++)
  {
    ti=typ(pol[i]);
    if (ti!=t_INT && ti!=t_INTMOD && !is_frac_t(ti))
    {
      flagexactpol=0;
      if (ti!=t_REAL) flagrealpol=0;
    }
    if (ti==t_QUAD)
    {
      p1=gmael3(pol,i,1,2);
      flagrealpol = (gsigne(p1)>0)? 0 : 1;
    }
  }
  rr=cgetg(N+1,t_COL);
  for (i=1; i<=N; i++)
  {
    p1 = cgetc(PREC); rr[i] = (long)p1;
    for (j=3; j<PREC; j++) mael(p1,2,j)=mael(p1,1,j)=0;
  }
  if (flagexactpol) tabqol = square_free_factorization(pol);
  else
  {
    tabqol = cgetg(3,t_MAT);
    tabqol[1] = (long)_col(gun);
    tabqol[2] = (long)_col(gcopy(pol));
  }
  nbpol=lg(tabqol[1])-1; nbroot=0;
  for (k=1; k<=nbpol; k++)
  {
    av1=avma; qol=gmael(tabqol,2,k); qolbis=gcopy(qol);
    multiqol=itos(gmael(tabqol,1,k)); deg=degpol(qol);
    for (j=deg; j>=1; j--)
    {
      x = gzero; flagrealrac = 0;
      if (j==1) x = gneg_i(gdiv((GEN)qolbis[2],(GEN)qolbis[3]));
      else
      {
        x = laguer(qolbis,j,x,EPS,PREC);
        if (x == NULL) goto RLAB;
      }
      if (flagexactpol)
      {
        x = gprec_w(x, PREC+2);
        x = laguer(qol,deg,x,gmul2n(EPS,-32),PREC+1);
      }
      else x = laguer(qol,deg,x,EPS,PREC);
      if (x == NULL) goto RLAB;

      if (typ(x)==t_COMPLEX &&
          gcmp(gabs(gimag(x),PREC), gmul2n(gmul(EPS,gabs(greal(x),PREC)),1))<=0)
        { x[2]=zero; flagrealrac = 1; }
      else if (j==1 && flagrealpol)
        { x[2]=zero; flagrealrac = 1; }
      else if (typ(x)!=t_COMPLEX) flagrealrac = 1;

      for (i=1; i<=multiqol; i++) gaffect(x, (GEN)rr[nbroot+i]);
      nbroot += multiqol;
      if (!flagrealpol || flagrealrac)
      {
        ad = (GEN*)new_chunk(j+1);
        for (i=0; i<=j; i++) ad[i] = (GEN)qolbis[i+2];
        b = ad[j];
        for (i=j-1; i>=0; i--)
        {
          c = ad[i]; ad[i] = b;
          b = gadd(gmul((GEN)rr[nbroot],b),c);
        }
        v = cgetg(j+1,t_VEC); for (i=1; i<=j; i++) v[i] = (long)ad[j-i];
        qolbis = gtopoly(v,varn(qolbis));
        if (flagrealpol)
          for (i=2; i<=j+1; i++)
            if (typ(qolbis[i])==t_COMPLEX) mael(qolbis,i,2)=zero;
      }
      else
      {
        ad = (GEN*)new_chunk(j-1);
        ad[j-2] = (GEN)qolbis[j+2];
        p1 = gmulsg(2,greal((GEN)rr[nbroot]));
        p2 = gnorm((GEN)rr[nbroot]);
        ad[j-3] = gadd((GEN)qolbis[j+1],gmul(p1,ad[j-2]));
        for (i=j-2; i>=2; i--)
          ad[i-2] = gadd((GEN)qolbis[i+2], gsub(gmul(p1,ad[i-1]), gmul(p2,ad[i])));
        v = cgetg(j,t_VEC); for (i=1; i<=j-1; i++) v[i] = (long)ad[j-1-i];
        qolbis = gtopoly(v,varn(qolbis));
        for (i=2; i<=j; i++)
          if (typ(qolbis[i])==t_COMPLEX) mael(qolbis,i,2)=zero;
        for (i=1; i<=multiqol; i++)
          gaffect(gconj((GEN)rr[nbroot]), (GEN)rr[nbroot+i]);
        nbroot+=multiqol; j--;
      }
    }
    avma=av1;
  }
  for (j=2; j<=N; j++)
  {
    x=(GEN)rr[j]; if (gcmp0((GEN)x[2])) fr=0; else fr=1;
    for (i=j-1; i>=1; i--)
    {
      if (gcmp0(gmael(rr,i,2))) f=0; else f=1;
      if (f<fr) break;
      if (f==fr && gcmp(greal((GEN)rr[i]),greal(x)) <= 0) break;
      rr[i+1]=rr[i];
    }
    rr[i+1]=(long)x;
  }
  return gerepilecopy(av,rr);

 RLAB:
  avma = av;
  for(i=2;i<=N+2;i++)
  {
    ti = typ(pol[i]);
    if (!is_intreal_t(ti)) err(talker,"too many iterations in roots");
  }
  if (DEBUGLEVEL)
  {
    fprintferr("too many iterations in roots2() ( laguer() ):\n");
    fprintferr("     real coefficients polynomial, using zrhqr()\n");
  }
  return zrhqr(pol,PREC);
}

#define MR 8
#define MT 10

static GEN
laguer(GEN pol,long N,GEN y0,GEN EPS,long PREC)
{
  long MAXIT, iter, j;
  gpmem_t av = avma, av1;
  GEN rac,erre,I,x,abx,abp,abm,dx,x1,b,d,f,g,h,sq,gp,gm,g2,*ffrac;

  MAXIT = MR*MT; rac = cgetc(PREC);
  av1 = avma;
  I=cgetg(3,t_COMPLEX); I[1]=un; I[2]=un;
  ffrac = (GEN*)new_chunk(MR+1);
  ffrac[0] = dbltor(0.0);
  ffrac[1] = dbltor(0.5);
  ffrac[2] = dbltor(0.25);
  ffrac[3] = dbltor(0.75);
  ffrac[4] = dbltor(0.13);
  ffrac[5] = dbltor(0.38);
  ffrac[6] = dbltor(0.62);
  ffrac[7] = dbltor(0.88);
  ffrac[8] = dbltor(1.0);
  x=y0;
  for (iter=1; iter<=MAXIT; iter++)
  {
    b=(GEN)pol[N+2]; erre=QuickNormL1(b,PREC);
    d=gzero; f=gzero; abx=QuickNormL1(x,PREC);
    for (j=N-1; j>=0; j--)
    {
      f = gadd(gmul(x,f),d);
      d = gadd(gmul(x,d),b);
      b = gadd(gmul(x,b), (GEN)pol[j+2]);
      erre = gadd(QuickNormL1(b,PREC), gmul(abx,erre));
    }
    erre = gmul(erre,EPS);
    if (gcmp(QuickNormL1(b,PREC),erre)<=0)
    {
      gaffect(x,rac); avma = av1; return rac;
    }
    g=gdiv(d,b); g2=gsqr(g); h=gsub(g2, gmul2n(gdiv(f,b),1));
    sq=gsqrt(gmulsg(N-1,gsub(gmulsg(N,h),g2)),PREC);
    gp=gadd(g,sq); gm=gsub(g,sq); abp=gnorm(gp); abm=gnorm(gm);
    if (gcmp(abp,abm)<0) gp=gcopy(gm);
    if (gsigne(gmax(abp,abm))==1)
      dx = gdivsg(N,gp);
    else
      dx = gmul(gadd(gun,abx),gexp(gmulgs(I,iter),PREC));
    x1=gsub(x,dx);
    if (gcmp(QuickNormL1(gsub(x,x1),PREC),EPS)<0)
    {
      gaffect(x,rac); avma = av1; return rac;
    }
    if (iter%MT) x=gcopy(x1); else x=gsub(x,gmul(ffrac[iter/MT],dx));
  }
  avma=av; return NULL;
}

#undef MR
#undef MT

/***********************************************************************/
/**                                                                   **/
/**             ROOTS of a polynomial with REAL coeffs                **/
/**                                                                   **/
/***********************************************************************/
#define RADIX 1L
#define COF 0.95

/* ONLY FOR REAL COEFFICIENTS MATRIX : replace the matrix x with
   a symmetric matrix a with the same eigenvalues */
static GEN
balanc(GEN x)
{
  gpmem_t av = avma;
  long last,i,j, sqrdx = (RADIX<<1), n = lg(x);
  GEN r,c,cofgen,a;

  a = dummycopy(x);
  last = 0; cofgen = dbltor(COF);
  while (!last)
  {
    last = 1;
    for (i=1; i<n; i++)
    {
      r = c = gzero;
      for (j=1; j<n; j++)
        if (j!=i)
        {
          c = gadd(c, gabs(gcoeff(a,j,i),0));
          r = gadd(r, gabs(gcoeff(a,i,j),0));
        }
      if (!gcmp0(r) && !gcmp0(c))
      {
        GEN g, s = gmul(cofgen, gadd(c,r));
        long ex = 0;
        g = gmul2n(r,-RADIX); while (gcmp(c,g) < 0) {ex++; c=gmul2n(c, sqrdx);}
        g = gmul2n(r, RADIX); while (gcmp(c,g) > 0) {ex--; c=gmul2n(c,-sqrdx);}
        if (gcmp(gadd(c,r), gmul2n(s,ex)) < 0)
        {
          last = 0;
          for (j=1; j<n; j++) coeff(a,i,j)=lmul2n(gcoeff(a,i,j),-ex);
          for (j=1; j<n; j++) coeff(a,j,i)=lmul2n(gcoeff(a,j,i), ex);
        }
      }
    }
  }
  return gerepilecopy(av, a);
}

#define SIGN(a,b) ((b)>=0.0 ? fabs(a) : -fabs(a))
static GEN
hqr(GEN mat) /* find all the eigenvalues of the matrix mat */
{
  long nn,n,m,l,k,j,its,i,mmin,flj,flk;
  double **a,p,q,r,s,t,u,v,w,x,y,z,anorm,*wr,*wi;
  const double eps = 0.000001;
  GEN eig;

  n=lg(mat)-1; a=(double**)gpmalloc(sizeof(double*)*(n+1));
  for (i=1; i<=n; i++) a[i]=(double*)gpmalloc(sizeof(double)*(n+1));
  for (j=1; j<=n; j++)
    for (i=1; i<=n; i++) a[i][j]=gtodouble((GEN)((GEN)mat[j])[i]);
  wr=(double*)gpmalloc(sizeof(double)*(n+1));
  wi=(double*)gpmalloc(sizeof(double)*(n+1));

  anorm=fabs(a[1][1]);
  for (i=2; i<=n; i++) for (j=(i-1); j<=n; j++) anorm+=fabs(a[i][j]);
  nn=n; t=0.;
  if (DEBUGLEVEL>3) { fprintferr("* Finding eigenvalues\n"); flusherr(); }
  while (nn>=1)
  {
    its=0;
    do
    {
      for (l=nn; l>=2; l--)
      {
        s=fabs(a[l-1][l-1])+fabs(a[l][l]); if (s==0.) s=anorm;
        if ((double)(fabs(a[l][l-1])+s)==s) break;
      }
      x=a[nn][nn];
      if (l==nn){ wr[nn]=x+t; wi[nn--]=0.; }
      else
      {
        y=a[nn-1][nn-1];
        w=a[nn][nn-1]*a[nn-1][nn];
        if (l == nn-1)
        {
          p=0.5*(y-x); q=p*p+w; z=sqrt(fabs(q)); x+=t;
          if (q>=0. || fabs(q)<=eps)
          {
            z=p+SIGN(z,p); wr[nn-1]=wr[nn]=x+z;
            if (fabs(z)>eps) wr[nn]=x-w/z;
            wi[nn-1]=wi[nn]=0.;
          }
          else{ wr[nn-1]=wr[nn]=x+p; wi[nn-1]=-(wi[nn]=z); }
          nn-=2;
        }
        else
        {
          p = q = r = 0.; /* for lint */
          if (its==30) err(talker,"too many iterations in hqr");
          if (its==10 || its==20)
          {
            t+=x; for (i=1; i<=nn; i++) a[i][i]-=x;
            s = fabs(a[nn][nn-1]) + fabs(a[nn-1][nn-2]);
            y=x=0.75*s; w=-0.4375*s*s;
          }
          its++;
          for (m=nn-2; m>=l; m--)
          {
            z=a[m][m]; r=x-z; s=y-z;
            p=(r*s-w)/a[m+1][m]+a[m][m+1];
            q=a[m+1][m+1]-z-r-s;
            r=a[m+2][m+1]; s=fabs(p)+fabs(q)+fabs(r); p/=s; q/=s; r/=s;
            if (m==l) break;
            u=fabs(a[m][m-1])*(fabs(q)+fabs(r));
            v=fabs(p)*(fabs(a[m-1][m-1])+fabs(z)+fabs(a[m+1][m+1]));
            if ((double)(u+v)==v) break;
          }
          for (i=m+2; i<=nn; i++){ a[i][i-2]=0.; if (i!=(m+2)) a[i][i-3]=0.; }
          for (k=m; k<=nn-1; k++)
          {
            if (k!=m)
            {
              p=a[k][k-1]; q=a[k+1][k-1];
              r = (k != nn-1)? a[k+2][k-1]: 0.;
              x = fabs(p)+fabs(q)+fabs(r);
              if (x != 0.) { p/=x; q/=x; r/=x; }
            }
            s = SIGN(sqrt(p*p+q*q+r*r),p);
            if (s == 0.) continue;

            if (k==m)
              { if (l!=m) a[k][k-1] = -a[k][k-1]; }
            else
              a[k][k-1] = -s*x;
            p+=s; x=p/s; y=q/s; z=r/s; q/=p; r/=p;
            for (j=k; j<=nn; j++)
            {
              p = a[k][j]+q*a[k+1][j];
              if (k != nn-1) { p+=r*a[k+2][j]; a[k+2][j]-=p*z; }
              a[k+1][j] -= p*y; a[k][j] -= p*x;
            }
            mmin = (nn < k+3)? nn: k+3;
            for (i=l; i<=mmin; i++)
            {
              p = x*a[i][k]+y*a[i][k+1];
              if (k != nn-1) { p+=z*a[i][k+2]; a[i][k+2]-=p*r; }
              a[i][k+1] -= p*q; a[i][k] -= p;
            }
          }
        }
      }
    }
    while (l<nn-1);
  }
  for (j=2; j<=n; j++) /* ordering the roots */
  {
    x=wr[j]; y=wi[j]; if (y != 0.) flj=1; else flj=0;
    for (k=j-1; k>=1; k--)
    {
      if (wi[k] != 0.) flk=1; else flk=0;
      if (flk<flj) break;
      if (!flk && !flj && wr[k]<=x) break;
      if (flk&&flj&& wr[k]<x) break;
      if (flk&&flj&& wr[k]==x && wi[k]>0) break;
      wr[k+1]=wr[k]; wi[k+1]=wi[k];
    }
    wr[k+1]=x; wi[k+1]=y;
  }
  if (DEBUGLEVEL>3) { fprintferr("* Eigenvalues computed\n"); flusherr(); }
  for (i=1; i<=n; i++) free(a[i]); free(a); eig=cgetg(n+1,t_COL);
  for (i=1; i<=n; i++)
  {
    if (wi[i] != 0.)
    {
      GEN p1 = cgetg(3,t_COMPLEX);
      eig[i]=(long)p1;
      p1[1]=(long)dbltor(wr[i]);
      p1[2]=(long)dbltor(wi[i]);
    }
    else eig[i]=(long)dbltor(wr[i]);
  }
  free(wr); free(wi); return eig;
}

/* ONLY FOR POLYNOMIAL WITH REAL COEFFICIENTS : give the roots of the
 * polynomial a (first, the real roots, then the non real roots) in
 * increasing order of their real parts MULTIPLE ROOTS ARE FORBIDDEN.
 */
GEN
zrhqr(GEN a,long prec)
{
  gpmem_t av = avma;
  long i,j,prec2, n = degpol(a), ex = -bit_accuracy(prec);
  GEN aa,b,p1,rt,rr,hess,x,dx,y,newval,oldval;

  hess = cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++)
  {
    p1 = cgetg(n+1,t_COL); hess[j] = (long)p1;
    p1[1] = lneg(gdiv((GEN)a[n-j+2],(GEN)a[n+2]));
    for (i=2; i<=n; i++) p1[i] = (i==(j+1))? un: zero;
  }
  rt = hqr(balanc(hess));
  prec2 = 2*prec; /* polishing the roots */
  aa = gprec_w(a, prec2);
  b = derivpol(aa); rr = cgetg(n+1,t_COL);
  for (i=1; i<=n; i++)
  {
    x = gprec_w((GEN)rt[i], prec2);
    for (oldval=NULL;; oldval=newval, x=y)
    { /* Newton iteration */
      dx = poleval(b,x);
      if (gexpo(dx) < ex)
        err(talker,"polynomial has probably multiple roots in zrhqr");
      y = gsub(x, gdiv(poleval(aa,x),dx));
      newval = gabs(poleval(aa,y),prec2);
      if (gexpo(newval) < ex || (oldval && gcmp(newval,oldval) > 0)) break;
    }
    if (DEBUGLEVEL>3) fprintferr("%ld ",i);
    rr[i] = (long)cgetc(prec); gaffect(y, (GEN)rr[i]);
  }
  if (DEBUGLEVEL>3) { fprintferr("\npolished roots = %Z",rr); flusherr(); }
  return gerepilecopy(av, rr);
}
