/* $Id$

Copyright (C) 2007  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

#include "pari.h"
#include "paripriv.h"

/* Not so fast arithmetic with polynomials over F_2 */

/***********************************************************************/
/**                                                                   **/
/**                             F2x                                   **/
/**                                                                   **/
/***********************************************************************/
/* F2x objects are defined as follows:
   An F2x is a t_VECSMALL:
   x[0] = codeword
   x[1] = evalvarn(variable number)  (signe is not stored).
   x[2] = a_0...a_31 x[3] = a_32..a_63, etc.  on 32bit
   x[2] = a_0...a_63 x[3] = a_64..a_127, etc. on 64bit

   where the a_i are bits.

   signe(x) is not valid. Use lgpol(x)!=0 instead.
   Note: pol0_F2x=pol0_Flx and pol1_F2x=pol1_Flx
*/

INLINE long
F2x_degree_lg(GEN x, long l)
{
  return (l==2)?-1:bit_accuracy(l)-bfffo(x[l-1])-1;
}

long
F2x_degree(GEN x)
{
  return F2x_degree_lg(x, lg(x));
}

INLINE ulong
F2x_coeff(GEN x,long v)
{
   ulong u=(ulong)x[2+divsBIL(v)];
   return (u>>remsBIL(v))&1UL;
}

INLINE void
F2x_set(GEN x,long v)
{
   ulong* u=(ulong*)&x[2+divsBIL(v)];
   *u^=1UL<<remsBIL(v);
}

GEN
F2x_to_ZX(GEN x)
{
  long l=3+F2x_degree(x);
  GEN z=cgetg(l,t_POL);
  long i,j,k;
  for(i=2,k=2;i<lg(x);i++)
    for(j=0; j<BITS_IN_LONG && k<l; j++,k++)
      gel(z,k)=(x[i]&(1UL<<j))?gen_1:gen_0;
  z[1]=evalsigne(l>=3)|x[1];
  return z;
}

GEN
F2x_to_Flx(GEN x)
{
  long l=3+F2x_degree(x);
  GEN z=cgetg(l,t_VECSMALL);
  long i,j,k;
  z[1]=x[1];
  for(i=2,k=2;i<lg(x);i++)
    for(j=0;j<BITS_IN_LONG && k<l; j++,k++)
      z[k]=(x[i]>>j)&1UL;
  return z;
}

GEN
ZX_to_F2x(GEN x)
{
  long l=nbits2prec(lgpol(x));
  GEN z=cgetg(l,t_VECSMALL);
  long i,j,k;
  z[1]=((ulong)x[1])&VARNBITS;
  for(i=2, k=1,j=BITS_IN_LONG;i<lg(x);i++,j++)
  {
    if (j==BITS_IN_LONG)
    {
      j=0; k++; z[k]=0;
    }
    if (mpodd(gel(x,i)))
      z[k]|=1UL<<j;
  }
  return F2x_renormalize(z,l);
}

GEN
Flx_to_F2x(GEN x)
{
  long l=nbits2prec(lgpol(x));
  GEN z=cgetg(l,t_VECSMALL);
  long i,j,k;
  z[1]=x[1];
  for(i=2, k=1,j=BITS_IN_LONG;i<lg(x);i++,j++)
  {
    if (j==BITS_IN_LONG)
    {
      j=0; k++; z[k]=0;
    }
    if (x[i])
      z[k]|=1UL<<j;
  }
  return F2x_renormalize(z,l);
}

GEN
F2x_to_F2v(GEN x, long N)
{
  long i, l = lg(x);
  long n = nbits2prec(N);
  GEN z = cgetg(n,t_VECSMALL);
  z[1] = N;
  for (i=2; i<l ; i++) z[i]=x[i];
  for (   ; i<n; i++) z[i]=0;
  return z;
}

GEN
F2x_add(GEN x, GEN y)
{
  long i,lz;
  GEN z;
  long lx=lg(x);
  long ly=lg(y);
  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx; z = cgetg(lz, t_VECSMALL); z[1]=x[1];
  for (i=2; i<ly; i++) z[i] = x[i]^y[i];
  for (   ; i<lx; i++) z[i] = x[i];
  return F2x_renormalize(z, lz);
}

static GEN
F2x_addspec(GEN x, GEN y, long lx, long ly)
{
  long i,lz;
  GEN z;

  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx+2; z = cgetg(lz, t_VECSMALL) + 2;
  for (i=0; i<ly; i++) z[i] = x[i]^y[i];
  for (   ; i<lx; i++) z[i] = x[i];
  z -= 2; return F2x_renormalize(z, lz);
}

GEN
F2x_1_add(GEN y)
{
  GEN z;
  long lz, i;
  if (!lgpol(y))
    return pol1_F2x(y[1]);
  lz=lg(y);
  z=cgetg(lz,t_VECSMALL);
  z[1] = y[1];
  z[2] = y[2]^1UL;
  for(i=3;i<lz;i++)
    z[i] = y[i];
  if (lz==3) z = F2x_renormalize(z,lz);
  return z;
}

static GEN
F2x_addshift(GEN x, GEN y, long d)
{
  GEN xd,yd,zd = (GEN)avma;
  long a,lz,ny = lgpol(y), nx = lgpol(x);
  long vs = x[1];

  x += 2; y += 2; a = ny-d;
  if (a <= 0)
  {
    lz = (a>nx)? ny+2: nx+d+2;
    (void)new_chunk(lz); xd = x+nx; yd = y+ny;
    while (xd > x) *--zd = *--xd;
    x = zd + a;
    while (zd > x) *--zd = 0;
  }
  else
  {
    xd = new_chunk(d); yd = y+d;
    x = F2x_addspec(x,yd,nx,a);
    lz = (a>nx)? ny+2: lg(x)+d;
    x += 2; while (xd > x) *--zd = *--xd;
  }
  while (yd > y) *--zd = *--yd;
  *--zd = vs;
  *--zd = evaltyp(t_VECSMALL) | evallg(lz); return zd;
}

/* shift polynomial + gerepile */
/* Do not set evalvarn*/
static GEN
F2x_shiftip(pari_sp av, GEN x, long v)
{
  long i, lx = lg(x), ly;
  GEN y;
  if (!v || lx==2) return gerepileuptoleaf(av, x);
  avma = av; ly = lx + v;
  x += lx; y = new_chunk(ly) + ly; /*cgetg could overwrite x!*/
  for (i = 2; i<lx; i++) *--y = *--x;
  for (i = 0; i< v; i++) *--y = 0;
  y -= 2; y[0] = evaltyp(t_VECSMALL) | evallg(ly);
  return y;
}

static GEN
F2x_mul1(ulong x, ulong y)
{
  ulong x1=(x&HIGHMASK)>>BITS_IN_HALFULONG;
  ulong x2=x&LOWMASK;
  ulong y1=(y&HIGHMASK)>>BITS_IN_HALFULONG;
  ulong y2=y&LOWMASK;
  ulong r1,r2,rr;
  GEN z;
  ulong i;
  rr=r1=r2=0UL;
  if (x2)
    for(i=0;i<BITS_IN_HALFULONG;i++)
      if (x2&(1UL<<i))
      {
        r2^=y2<<i;
        rr^=y1<<i;
      }
  if (x1)
    for(i=0;i<BITS_IN_HALFULONG;i++)
      if (x1&(1UL<<i))
      {
        r1^=y1<<i;
        rr^=y2<<i;
      }
  r2^=(rr&LOWMASK)<<BITS_IN_HALFULONG;
  r1^=(rr&HIGHMASK)>>BITS_IN_HALFULONG;
  z=cgetg((r1?4:3),t_VECSMALL);
  z[2]=r2;
  if (r1) z[3]=r1;
  return z;
}

/* fast product (Karatsuba) of polynomials a,b. These are not real GENs, a+2,
 * b+2 were sent instead. na, nb = number of terms of a, b.
 * Only c, c0, c1, c2 are genuine GEN.
 */
static GEN
F2x_mulspec(GEN a, GEN b, long na, long nb)
{
  GEN a0,c,c0;
  long n0, n0a, i, v = 0;
  pari_sp av;

  while (na && !a[0]) { a++; na-=1; v++; }
  while (nb && !b[0]) { b++; nb-=1; v++; }
  if (na < nb) swapspec(a,b, na,nb);
  if (!nb) return pol0_F2x(0);

  av = avma;
  if (na <=1) return F2x_shiftip(av,F2x_mul1(*a,*b),v);
  i=(na>>1); n0=na-i; na=i;
  a0=a+n0; n0a=n0;
  while (n0a && !a[n0a-1]) n0a--;

  if (nb > n0)
  {
    GEN b0,c1,c2;
    long n0b;

    nb -= n0; b0 = b+n0; n0b = n0;
    while (n0b && !b[n0b-1]) n0b--;
    c =  F2x_mulspec(a,b,n0a,n0b);
    c0 = F2x_mulspec(a0,b0,na,nb);

    c2 = F2x_addspec(a0,a,na,n0a);
    c1 = F2x_addspec(b0,b,nb,n0b);

    c1 = F2x_mul(c1,c2);
    c2 = F2x_add(c0,c);

    c2 = F2x_add(c1,c2);
    c0 = F2x_addshift(c0,c2,n0);
  }
  else
  {
    c  = F2x_mulspec(a,b,n0a,nb);
    c0 = F2x_mulspec(a0,b,na,nb);
  }
  c0 = F2x_addshift(c0,c,n0);
  return F2x_shiftip(av,c0, v);
}

GEN
F2x_mul(GEN x, GEN y)
{
  GEN z = F2x_mulspec(x+2,y+2, lgpol(x),lgpol(y));
  z[1] = x[1]; return z;
}

GEN
F2x_sqr(GEN x)
{
  const ulong sq[]={0,1,4,5,16,17,20,21,64,65,68,69,80,81,84,85};
  long i,ii,j,jj;
  long lx=lg(x), lz=2+((lx-2)<<1);
  GEN z;
  z = cgetg(lz, t_VECSMALL); z[1]=x[1];
  for (j=2,jj=2;j<lx;j++,jj++)
  {
    ulong x1=((ulong)x[j]&HIGHMASK)>>BITS_IN_HALFULONG;
    ulong x2=(ulong)x[j]&LOWMASK;
    z[jj]=0;
    if (x2)
      for(i=0,ii=0;i<BITS_IN_HALFULONG;i+=4,ii+=8)
        z[jj]|=sq[(x2>>i)&15UL]<<ii;
    z[++jj]=0;
    if (x1)
      for(i=0,ii=0;i<BITS_IN_HALFULONG;i+=4,ii+=8)
        z[jj]|=sq[(x1>>i)&15UL]<<ii;
  }
  return F2x_renormalize(z, lz);
}

INLINE void
F2x_addshiftip(GEN x, GEN y, ulong d)
{
  ulong db, dl=dvmduBIL(d, &db);
  long i;
  if (db)
  {
    ulong dc=BITS_IN_LONG-db;
    ulong r=0;
    for(i=2; i<lg(y); i++)
    {
      x[i+dl] ^= (((ulong)y[i])<<db)|r;
      r = ((ulong)y[i])>>dc;
    }
    if (r) x[i+dl] ^= r;
  }
  else
    for(i=2; i<lg(y); i++)
      x[i+dl] ^= y[i];
}

/* separate from F2x_divrem for maximal speed. */
GEN
F2x_rem(GEN x, GEN y)
{
  long dx,dy;
  long lx=lg(x);
  dy = F2x_degree(y); if (!dy) return pol0_F2x(x[1]);
  dx = F2x_degree_lg(x,lx);
  x  = vecsmall_copy(x);
  while (dx>=dy)
  {
    F2x_addshiftip(x,y,dx-dy);
    while (lx>2 && x[lx-1]==0) lx--;
    dx = F2x_degree_lg(x,lx);
  }
  return F2x_renormalize(x, lx);
}

GEN
F2x_divrem(GEN x, GEN y, GEN *pr)
{
  long dx, dy, dz, lx = lg(x), vs = x[1];
  GEN z;

  dy = F2x_degree(y);
  if (dy<0) pari_err(gdiver);
  if (pr == ONLY_REM) return F2x_rem(x, y);
  if (!dy)
  {
    z = vecsmall_copy(x);
    if (pr && pr != ONLY_DIVIDES) *pr = pol0_F2x(vs);
    return z;
  }
  dx = F2x_degree_lg(x,lx);
  dz = dx-dy;
  if (dz < 0)
  {
    if (pr == ONLY_DIVIDES) return dx < 0? vecsmall_copy(x): NULL;
    z = pol0_F2x(vs);
    if (pr) *pr = vecsmall_copy(x);
    return z;
  }
  z = const_vecsmall(lg(x)-lg(y)+2, 0); z[1] = vs;
  x = vecsmall_copy(x);
  while (dx>=dy)
  {
    F2x_set(z,dx-dy);
    F2x_addshiftip(x,y,dx-dy);
    while (lx>2 && x[lx-1]==0) lx--;
    dx = F2x_degree_lg(x,lx);
  }
  z = F2x_renormalize(z, lg(z));
  if (!pr) { cgiv(x); return z; }
  x = F2x_renormalize(x, lx);
  if (pr == ONLY_DIVIDES) {
    if (lg(x) == 2) { cgiv(x); return z; }
    avma = (pari_sp)(z + lg(z)); return NULL;
  }
  *pr = x; return z;
}

GEN
F2x_gcd(GEN a, GEN b)
{
  pari_sp av = avma, lim = stack_lim(av,2);
  if (lg(b) > lg(a)) swap(a, b);
  while (lgpol(b))
  {
    GEN c = F2x_rem(a,b);
    a = b; b = c;
    if (low_stack(lim,stack_lim(av,2)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"F2x_gcd (d = %ld)",F2x_degree(c));
      gerepileall(av,2, &a,&b);
    }
  }
  if (low_stack(lim,stack_lim(av,2))) a = gerepileuptoleaf(av, a);
  return a;
}

GEN
F2x_extgcd(GEN a, GEN b, GEN *ptu, GEN *ptv)
{
  pari_sp av=avma, lim = stack_lim(av,2);
  GEN u,v,d,d1,v1;
  long vx = a[1];
  d = a; d1 = b;
  v = pol0_F2x(vx); v1 = pol1_F2x(vx);
  while (lgpol(d1))
  {
    GEN r, q = F2x_divrem(d,d1, &r);
    v = F2x_add(v,F2x_mul(q,v1));
    u=v; v=v1; v1=u;
    u=r; d=d1; d1=u;
    if (low_stack(lim,stack_lim(av,2)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"F2x_extgcd (d = %ld)",F2x_degree(d));
      gerepileall(av,5, &d,&d1,&u,&v,&v1);
    }
  }
  if (ptu) *ptu = F2x_div(F2x_add(d, F2x_mul(b,v)), a);
  *ptv = v;
  if (low_stack(lim,stack_lim(av,2))) gerepileall(av,ptu?3:2,&d,ptv,ptu);
  return d;
}

GEN
F2xq_mul(GEN x,GEN y,GEN pol)
{
  GEN z = F2x_mul(x,y);
  return F2x_rem(z,pol);
}

GEN
F2xq_sqr(GEN x,GEN pol)
{
  GEN z = F2x_sqr(x);
  return F2x_rem(z,pol);
}

GEN
F2xq_invsafe(GEN x, GEN T)
{
  GEN V, z = F2x_extgcd(T, x, NULL, &V);
  if (F2x_degree(z)) return NULL;
  return V;
}

GEN
F2xq_inv(GEN x,GEN T)
{
  pari_sp av=avma;
  GEN U = F2xq_invsafe(x, T);
  if (!U) pari_err(gdiver);
  return gerepileuptoleaf(av, U);
}

GEN
F2xq_div(GEN x,GEN y,GEN T)
{
  pari_sp av = avma;
  return gerepileuptoleaf(av, F2xq_mul(x,F2xq_inv(y,T),T));
}

static GEN
_F2xq_sqr(void *data, GEN x)
{
  GEN pol = (GEN) data;
  return F2xq_sqr(x, pol);
}

static GEN
_F2xq_mul(void *data, GEN x, GEN y)
{
  GEN pol = (GEN) data;
  return F2xq_mul(x,y, pol);
}

GEN
F2xq_pow(GEN x, GEN n, GEN pol)
{
  pari_sp av=avma;
  GEN y;

  if (!signe(n)) return pol1_F2x(x[1]);
  if (is_pm1(n)) /* +/- 1 */
    return (signe(n) < 0)? F2xq_inv(x,pol): vecsmall_copy(x);

  if (signe(n) < 0) x = F2xq_inv(x,pol);
  y = gen_pow(x, n, (void*)pol, &_F2xq_sqr, &_F2xq_mul);
  return gerepileupto(av, y);
}

/* generates the list of powers of x of degree 0,1,2,...,l*/
GEN
F2xq_powers(GEN x, long l, GEN T)
{
  GEN V = cgetg(l+2,t_VEC);
  long i, v = T[1];
  gel(V,1) = pol1_F2x(v);  if (l==0) return V;
  gel(V,2) = vecsmall_copy(x); if (l==1) return V;
  gel(V,3) = F2xq_sqr(x,T);
  if ((F2x_degree(x)<<1) < F2x_degree(T)) {
    for(i = 4; i < l+2; i++)
      gel(V,i) = F2xq_mul(gel(V,i-1),x,T);
  } else {
    for(i = 4; i < l+2; i++) {
      gel(V,i) = (i&1)? F2xq_sqr(gel(V, (i+1)>>1),T)
                      : F2xq_mul(gel(V, i-1),x,T);
    }
  }
  return V;
}

GEN
F2xq_matrix_pow(GEN y, long n, long m, GEN P)
{
  return F2xV_to_F2m(F2xq_powers(y,m-1,P),n);
}

GEN
F2xq_conjvec(GEN x, GEN T)
{
  long i, l = F2x_degree(T);
  GEN z = cgetg(l,t_COL);
  gel(z,1) = vecsmall_copy(x);
  for (i=2; i<l; i++) gel(z,i) = F2xq_sqr(gel(z,i-1), T);
  return z;
}

GEN
random_F2x(long d, long vs)
{
  long i, l = nbits2prec(d+1);
  GEN y = cgetg(l,t_VECSMALL); y[1] = vs;
  for (i=2; i<l; i++) y[i] = pari_rand();
  y[l-1] &= (1UL<<remsBIL(d))-1UL;
  return F2x_renormalize(y,l);
}

static GEN
_F2xq_pow(void *data, GEN x, GEN n)
{
  GEN pol = (GEN) data;
  return F2xq_pow(x,n, pol);
}

static GEN
_F2xq_rand(void *data)
{
  pari_sp av=avma;
  GEN pol = (GEN) data;
  long d = F2x_degree(pol);
  GEN z;
  do
  {
    avma = av;
    z = random_F2x(d,pol[1]);
  } while (lgpol(z)==0);
  return z;
}

static ulong
_F2xq_hash(GEN x)
{
  return x[2];
}

static const struct bb_group F2xq_star={_F2xq_mul,_F2xq_pow,_F2xq_rand,_F2xq_hash,vecsmall_lexcmp,F2x_equal1};

GEN
F2xq_order(GEN a, GEN ord, GEN T)
{
  return gen_eltorder(a,ord,(void*)T,&F2xq_star);
}

GEN
F2xq_log(GEN a, GEN g, GEN ord, GEN T)
{
  return gen_PH_log(a,g,ord,(void*)T,&F2xq_star,NULL);
}

GEN
F2xq_sqrtn(GEN a, GEN n, GEN T, GEN *zeta)
{
  if (!lgpol(a))
  {
    if (zeta)
      *zeta=pol1_F2x(T[1]);
    return pol0_F2x(T[1]);
  }
  return gen_Shanks_sqrtn(a,n,addis(powuu(2,F2x_degree(T)),-1),zeta,(void*)T,&F2xq_star);
}

GEN
gener_F2xq(GEN T, GEN *po)
{
  long i, j, vT = T[1], f = F2x_degree(T);
  pari_sp av0 = avma, av;
  GEN g, L2, o, q;

  if (f == 1) {
    if (po) *po = mkvec2(gen_1, trivfact());
    return pol1_F2x(vT);
  }
  q = subis(powuu(2,f), 1);
  o = factor_pn_1(gen_2,f);
  L2 = leafcopy( gel(o, 1) );
  for (i = j = 1; i < lg(L2); i++)
  {
    if (equaliu(gel(L2,i),2)) continue;
    gel(L2,j++) = diviiexact(q, gel(L2,i));
  }
  setlg(L2, j);
  for (av = avma;; avma = av)
  {
    g = random_F2x(f, vT);
    if (F2x_degree(g) < 1) continue;
    for (i = 1; i < j; i++)
    {
      GEN a = F2xq_pow(g, gel(L2,i), T);
      if (F2x_equal1(a)) break;
    }
    if (i == j) break;
  }
  if (!po) g = gerepilecopy(av0, g);
  else {
    *po = mkvec2(subis(int2n(f), 1), o);
    gerepileall(av0, 2, &g, po);
  }
  return g;
}
/***********************************************************************/
/**                                                                   **/
/**                             F2v                                   **/
/**                                                                   **/
/***********************************************************************/
/* F2v objects are defined as follows:
   An F2v is a t_VECSMALL:
   v[0] = codeword
   v[1] = number of components
   x[2] = a_0...a_31 x[3] = a_32..a_63, etc.  on 32bit
   x[2] = a_0...a_63 x[3] = a_64..a_127, etc. on 64bit

   where the a_i are bits.
*/

GEN
F2c_to_ZC(GEN x)
{
  long l=x[1]+1;
  GEN  z=cgetg(l, t_COL);
  long i,j,k;
  for (i=2,k=1; i<lg(x); i++)
    for (j=0; j<BITS_IN_LONG && k<l; j++,k++)
      gel(z,k)=(x[i]&(1UL<<j))?gen_1:gen_0;
  return z;
}

GEN
F2m_to_ZM(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_MAT);
  for (i=1; i<l; i++) gel(x,i) = F2c_to_ZC(gel(z,i));
  return x;
}

GEN
ZV_to_F2v(GEN x)
{
  long l = lg(x)-1;
  GEN z = cgetg(nbits2prec(l), t_VECSMALL);
  long i,j,k;
  z[1] = l;
  for(i=1, k=1,j=BITS_IN_LONG;i<=l;i++,j++)
  {
    if (j==BITS_IN_LONG)
    {
      j=0; k++; z[k]=0;
    }
    if (mpodd(gel(x,i)))
      z[k]|=1UL<<j;
  }
  return z;
}

GEN
Flv_to_F2v(GEN x)
{
  long l = lg(x)-1;
  GEN z = cgetg(nbits2prec(l), t_VECSMALL);
  long i,j,k;
  z[1] = l;
  for(i=1, k=1,j=BITS_IN_LONG;i<=l;i++,j++)
  {
    if (j==BITS_IN_LONG)
    {
      j=0; k++; z[k]=0;
    }
    if (x[i]&1L)
      z[k]|=1UL<<j;
  }
  return z;
}

GEN
ZM_to_F2m(GEN x)
{
  long j, l = lg(x);
  GEN y = cgetg(l,t_MAT);
  if (l == 1) return y;
  for (j=1; j<l; j++) gel(y,j) = ZV_to_F2v(gel(x,j));
  return y;
}

GEN
Flm_to_F2m(GEN x)
{
  long j, l = lg(x);
  GEN y = cgetg(l,t_MAT);
  if (l == 1) return y;
  for (j=1; j<l; j++) gel(y,j) = Flv_to_F2v(gel(x,j));
  return y;
}

/* Allow lg(y)<lg(x) */
void
F2v_add_inplace(GEN x, GEN y)
{
  long n = lg(y);
  long r = (n-2)&7L, q = n-r, i;
  for (i = 2; i < q; i += 8)
  {
    x[  i] ^= y[  i]; x[1+i] ^= y[1+i]; x[2+i] ^= y[2+i]; x[3+i] ^= y[3+i];
    x[4+i] ^= y[4+i]; x[5+i] ^= y[5+i]; x[6+i] ^= y[6+i]; x[7+i] ^= y[7+i];
  }
  switch (r)
  {
    case 7: x[i] ^= y[i]; i++; case 6: x[i] ^= y[i]; i++;
    case 5: x[i] ^= y[i]; i++; case 4: x[i] ^= y[i]; i++;
    case 3: x[i] ^= y[i]; i++; case 2: x[i] ^= y[i]; i++;
    case 1: x[i] ^= y[i]; i++;
  }
}

/***********************************************************************/
/**                                                                   **/
/**                               F2xV                                **/
/**                                                                   **/
/***********************************************************************/
/* F2xV are t_VEC with F2x coefficients. */

GEN
F2xV_to_F2m(GEN v, long n)
{
  long j, N = lg(v);
  GEN y = cgetg(N, t_MAT);
  for (j=1; j<N; j++) gel(y,j) = F2x_to_F2v(gel(v,j), n);
  return y;
}
