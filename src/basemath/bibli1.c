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
/**                 LLL Algorithm and close friends                **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "parinf.h"
extern GEN ZV_lincomb(GEN u, GEN v, GEN X, GEN Y);
extern GEN roots_to_pol_r1r2(GEN a, long r1, long v);
extern GEN LLL_nfbasis(GEN x, GEN polr, GEN base, long prec);

/* default quality ratio for LLL: 99/100 */
#define LLLDFT 100

/* scalar product x.x */
GEN
sqscal(GEN x)
{
  long i, lx;
  gpmem_t av;
  GEN z;
  lx = lg(x);
  if (lx == 1) return gzero;
  av = avma;
  z = gsqr((GEN)x[1]);
  for (i=2; i<lx; i++)
    z = gadd(z, gsqr((GEN)x[i]));
  return gerepileupto(av,z);
}

/* scalar product x.y */
GEN
gscal(GEN x,GEN y)
{
  long i, lx;
  gpmem_t av;
  GEN z;
  if (x == y) return sqscal(x);
  lx = lg(x);
  if (lx == 1) return gzero;
  av = avma;
  z = gmul((GEN)x[1],(GEN)y[1]);
  for (i=2; i<lx; i++)
    z = gadd(z, gmul((GEN)x[i],(GEN)y[i]));
  return gerepileupto(av,z);
}

static GEN
sqscali(GEN x)
{
  long i, lx;
  gpmem_t av;
  GEN z;
  lx = lg(x);
  if (lx == 1) return gzero;
  av = avma;
  z = sqri((GEN)x[1]);
  for (i=2; i<lx; i++)
    z = addii(z, sqri((GEN)x[i]));
  return gerepileuptoint(av,z);
}

static GEN
gscali(GEN x,GEN y)
{
  long i, lx;
  gpmem_t av;
  GEN z;
  if (x == y) return sqscali(x);
  lx = lg(x);
  if (lx == 1) return gzero;
  av = avma;
  z = mulii((GEN)x[1],(GEN)y[1]);
  for (i=2; i<lx; i++)
    z = addii(z, mulii((GEN)x[i],(GEN)y[i]));
  return gerepileuptoint(av,z);
}

static GEN
lll_trivial(GEN x, long flag)
{
  GEN y;
  if (lg(x) == 1)
  { /* dim x = 0 */
    if (! (flag & lll_ALL)) return cgetg(1,t_MAT);
    y=cgetg(3,t_VEC);
    y[1]=lgetg(1,t_MAT);
    y[2]=lgetg(1,t_MAT); return y;
  }
  /* here dim = 1 */
  if (gcmp0((GEN)x[1]))
  {
    switch(flag & (~lll_GRAM))
    {
      case lll_KER: return idmat(1);
      case lll_IM : return cgetg(1,t_MAT);
      default: y=cgetg(3,t_VEC);
        y[1]=(long)idmat(1);
        y[2]=lgetg(1,t_MAT); return y;
    }
  }
  if (flag & lll_GRAM) flag ^= lll_GRAM; else x = NULL;
  switch (flag)
  {
    case lll_KER: return cgetg(1,t_MAT);
    case lll_IM : return idmat(1);
    default: y=cgetg(3,t_VEC);
      y[1]=lgetg(1,t_MAT);
      y[2]=x? lcopy(x): (long)idmat(1); return y;
  }
}

static GEN
lll_finish(GEN h,GEN fl,long flag)
{
  long i, k, l = lg(fl);
  GEN y, g;

  k=1; while (k<l && !fl[k]) k++;
  switch(flag & (~lll_GRAM))
  {
    case lll_KER: setlg(h,k);
      return h;

    case lll_IM: h += k-1; h[0] = evaltyp(t_MAT) | evallg(l-k+1);
      return h;
  }
  y = cgetg(3,t_VEC);
  g = cgetg(k, t_MAT); for (i=1; i<k; i++) g[i] = h[i];
  y[1] = (long)g;
  h += k-1; h[0] = evaltyp(t_MAT) | evallg(l-k+1);
  y[2] = (long)h; return y;
}

/********************************************************************/
/**                                                                **/
/**                          LLL ALGORITHM                         **/
/**                                                                **/
/********************************************************************/
#define swap(x,y) { long _t=x; x=y; y=_t; }
#define gswap(x,y) { GEN _t=x; x=y; y=_t; }

/* h[,k] += q * h[,l] */
static void
update_h(long k, long l, GEN q, long K, GEN h)
{
  GEN *hl, *hk;
  long i;

  if (!h) return;
  hl = (GEN*)h[l]; hk = (GEN*)h[k];
  if (is_pm1(q))
  {
    if (signe(q) > 0)
      for (i=1;i<=K;i++) { if (signe(hl[i])) hk[i] = addii(hk[i],hl[i]); }
    else
      for (i=1;i<=K;i++) { if (signe(hl[i])) hk[i] = subii(hk[i],hl[i]); }
  } else
      for (i=1;i<=K;i++) if (signe(hl[i])) hk[i] = addii(hk[i],mulii(q,hl[i]));
}

/* L[k,] += q * L[l,], l < k */
static void
Zupdate_L(long k, long l, GEN q, GEN L, GEN B)
{
  long i;
  if (is_pm1(q))
  {
    if (signe(q) > 0)
    {
      for (i=1;i<l; i++) coeff(L,k,i) = laddii(gcoeff(L,k,i),gcoeff(L,l,i));
      coeff(L,k,l) = laddii(gcoeff(L,k,l), B);
    } else {
      for (i=1;i<l; i++) coeff(L,k,i) = lsubii(gcoeff(L,k,i),gcoeff(L,l,i));
      coeff(L,k,l) = laddii(gcoeff(L,k,l), negi(B));
    }
  } else {
    for(i=1;i<l;i++)  coeff(L,k,i)=laddii(gcoeff(L,k,i),mulii(q,gcoeff(L,l,i)));
    coeff(L,k,l) = laddii(gcoeff(L,k,l), mulii(q,B));
  }
}

static void
update_L(long k, long l, GEN q, GEN L)
{
  long i;
  if (is_pm1(q))
  {
    if (signe(q) > 0)
    {
      for (i=1;i<l; i++) coeff(L,k,i) = lmpadd(gcoeff(L,k,i),gcoeff(L,l,i));
    } else {
      for (i=1;i<l; i++) coeff(L,k,i) = lmpsub(gcoeff(L,k,i),gcoeff(L,l,i));
    }
  } else {
    for(i=1;i<l;i++)  coeff(L,k,i)=lmpadd(gcoeff(L,k,i),mpmul(q,gcoeff(L,l,i)));
  }
  coeff(L,k,l) = lmpadd(gcoeff(L,k,l), q);
}

static void
ZRED_gram(long k, long l, GEN x, GEN h, GEN L, GEN B, long K)
{
  long i,lx;
  GEN q = truedvmdii(addii(B,shifti(gcoeff(L,k,l),1)), shifti(B,1), NULL);
  GEN xk,xl;
  if (!signe(q)) return;
  q = negi(q);
  xl = (GEN) x[l]; xk = (GEN) x[k];
  lx = lg(xl);
  if (is_pm1(q))
  {
    if (signe(q) > 0)
    {
      xk[k] = laddii((GEN)xk[k], (GEN)xl[k]);
      for (i=1;i<lx;i++) coeff(x,k,i) = xk[i] = laddii((GEN)xk[i], (GEN)xl[i]);
    } else {
      xk[k] = lsubii((GEN)xk[k], (GEN)xl[k]);
      for (i=1;i<lx;i++) coeff(x,k,i) = xk[i] = lsubii((GEN)xk[i], (GEN)xl[i]);
    }
  } else { /* h[,k] += q* h[,l]. x[,k] += q * x[,l]. L[k,] += q* L[l,] */
    xk[k] = laddii((GEN)xk[k], mulii(q,(GEN)xl[k]));
    for(i=1;i<lx;i++) coeff(x,k,i)=xk[i]=laddii((GEN)xk[i],mulii(q,(GEN)xl[i]));
  }
  Zupdate_L(k,l,q,L,B);
  update_h (k,l,q,K,h);
}

static void
ZRED(long k, long l, GEN x, GEN h, GEN L, GEN B, long K)
{
  GEN q = truedvmdii(addii(B,shifti(gcoeff(L,k,l),1)), shifti(B,1), NULL);
  if (!signe(q)) return;
  q = negi(q);
  Zupdate_L(k,l,q,L,B);
  update_h (k,l,q,K,h);
  x[k] = (long)ZV_lincomb(gun, q, (GEN)x[k], (GEN)x[l]);
}

static GEN
round_safe(GEN q)
{ 
  long e;
  if (typ(q) == t_INT) return q;
  if (expo(q) > 30)
  {
    q = grndtoi(q, &e);
    if (e > 0) return NULL;
  } else
    q = ground(q);
  return q;
}

/* b[k] <-- b[k] - round(L[k,l]) b[l], only b[1] ... b[K] modified so far
 * assume l < k and update x = Gram(b), L = Gram Schmidt coeffs. */
static int
RED_gram(long k, long l, GEN x, GEN h, GEN L, long K)
{
  long i,lx;
  GEN q = round_safe(gcoeff(L,k,l));
  GEN xk, xl;

  if (!q) return 0;
  if (!signe(q)) return 1;
  q = negi(q); lx = lg(x);
  xk = (GEN)x[k]; xl = (GEN)x[l];
  if (is_pm1(q))
  {
    if (signe(q) > 0)
    {
      xk[k] = lmpadd((GEN)xk[k], (GEN)xl[k]);
      for (i=1;i<lx;i++) coeff(x,k,i)=xk[i]=lmpadd((GEN)xk[i], (GEN)xl[i]);
    } else {
      xk[k] = lmpsub((GEN)xk[k], (GEN)xl[k]);
      for (i=1;i<lx;i++) coeff(x,k,i)=xk[i]=lmpsub((GEN)xk[i], (GEN)xl[i]);
    }
  } else {
    xk[k] = lmpadd((GEN)xk[k], mpmul(q,(GEN)xl[k]));
    for (i=1;i<lx;i++)
      coeff(x,k,i)=xk[i]=lmpadd((GEN)xk[i], mpmul(q,(GEN)xl[i]));
  }
  update_L(k,l,q,L);
  update_h(k,l,q,K,h); return 1;
}

static int
RED(long k, long l, GEN x, GEN h, GEN L, long K)
{
  long i,lx;
  GEN q = round_safe(gcoeff(L,k,l));
  GEN xk, xl;

  if (!q) return 0;
  if (!signe(q)) return 1;
  q = negi(q);
  xk = (GEN)x[k]; xl = (GEN)x[l];
  lx = lg(xk);
  if (is_pm1(q))
  {
    if (signe(q) > 0)
    {
      for (i=1;i<lx;i++) xk[i] = lmpadd((GEN)xk[i], (GEN)xl[i]);
    } else {
      for (i=1;i<lx;i++) xk[i] = lmpsub((GEN)xk[i], (GEN)xl[i]);
    }
  } else {
    for (i=1;i<lx;i++) xk[i] = lmpadd((GEN)xk[i], mpmul(q,(GEN)xl[i]));
  }
  update_L(k,l,q,L);
  update_h(k,l,q,K,h); return 1;
}

static int
do_ZSWAP(GEN x, GEN h, GEN L, GEN B, long kmax, long k, long D, GEN fl,
         int gram)
{
  GEN la,la2,p1,Bk;
  long i, j, lx;
  gpmem_t av;

  if (!fl[k-1]) return 0;
  av = avma;
  la = gcoeff(L,k,k-1); la2 = sqri(la);
  Bk = (GEN)B[k];
  if (fl[k])
  {
    GEN q;
    if (!D) return 0; /* only swap non-kernel + kernel vector */
    q = addii(la2, mulii((GEN)B[k-1],(GEN)B[k+1]));
    if (cmpii(mulsi(D-1,sqri(Bk)), mulsi(D,q)) <= 0) {
      avma = av; return 0;
    }
    B[k] = (long)diviiexact(q, Bk);
  }
  /* ZSWAP(k-1,k) */
  if (DEBUGLEVEL>3 && k==kmax)
  { /* output diagnostics associated to re-normalized rational quantities */
    gpmem_t av1 = avma;
    GEN d = mulii((GEN)B[k-1],(GEN)B[k+1]);
    p1 = subii(mulsi(D-1, sqri(Bk)), mulsi(D, la2));
    fprintferr(" (%ld)", expi(p1) - expi(mulsi(D, d)));
    avma = av1;
  }
  if (h) swap(h[k-1], h[k]);
  swap(x[k-1], x[k]); lx = lg(x);
  if (gram)
    for (j=1; j < lx; j++) swap(coeff(x,k-1,j), coeff(x,k,j));
  for (j=1; j<k-1; j++) swap(coeff(L,k-1,j), coeff(L,k,j))
  if (fl[k])
  {
    av = avma;
    for (i=k+1; i<=kmax; i++)
    {
      GEN t = gcoeff(L,i,k);
      p1 = subii(mulii((GEN)B[k+1],gcoeff(L,i,k-1)), mulii(la,t));
      p1 = diviiexact(p1, Bk);
      coeff(L,i,k) = (long)icopy_av(p1,(GEN)av);
      av = avma = (gpmem_t)coeff(L,i,k);

      p1 = addii(mulii(la,gcoeff(L,i,k-1)), mulii((GEN)B[k-1],t));
      p1 = diviiexact(p1, Bk);
      coeff(L,i,k-1) = (long)icopy_av(p1,(GEN)av);
      av = avma = (gpmem_t)coeff(L,i,k-1);
    }
  }
  else if (signe(la))
  {
    p1 = diviiexact(la2, Bk);
    B[k+1] = B[k] = (long)p1;
    for (i=k+2; i<=lx; i++) B[i] = (long)diviiexact(mulii(p1,(GEN)B[i]), Bk);
    for (i=k+1; i<=kmax; i++)
      coeff(L,i,k-1) = (long)diviiexact(mulii(la,gcoeff(L,i,k-1)), Bk);
    for (j=k+1; j<kmax; j++)
      for (i=j+1; i<=kmax; i++)
        coeff(L,i,j) = (long)diviiexact(mulii(p1,gcoeff(L,i,j)), Bk);
  }
  else
  {
    for (i=k+1; i<=kmax; i++)
    {
      coeff(L,i,k) = coeff(L,i,k-1);
      coeff(L,i,k-1) = zero;
    }
    B[k] = B[k-1]; fl[k] = 1; fl[k-1] = 0;
  }
  return 1;
}

static int
do_SWAP(GEN x, GEN h, GEN L, GEN B, long kmax, long k, GEN delta, int gram)
{
  GEN la,la2, BK,BB,q;
  long i, j, lx;
  gpmem_t av;

  av = avma;
  la = gcoeff(L,k,k-1); la2 = gsqr(la);
  q = mpmul((GEN)B[k-1], mpsub(delta,la2));
  if (mpcmp(q, (GEN)B[k]) <= 0) { avma = av; return 0; }

  /* SWAP(k-1,k) */
  if (DEBUGLEVEL>3 && k==kmax) {
    fprintferr(" (%ld)", gexpo(q) - gexpo((GEN)B[k])); flusherr();
  }
  BB = mpadd((GEN)B[k], mpmul((GEN)B[k-1],la2));
  if (!signe(BB)) { B[k] = 0; return 1; } /* precision pb */

  coeff(L,k,k-1) = lmpdiv(mpmul(la,(GEN)B[k-1]), BB);
  BK = mpdiv((GEN)B[k], BB);
  B[k] = lmpmul((GEN)B[k-1], BK);
  B[k-1] = (long)BB;

  swap(h[k-1],h[k]);
  swap(x[k-1],x[k]); lx = lg(x);
  if (gram)
    for (j=1; j < lx; j++) swap(coeff(x,k-1,j), coeff(x,k,j));
  for (j=1; j<k-1; j++) swap(coeff(L,k-1,j), coeff(L,k,j))
  for (i=k+1; i<=kmax; i++)
  {
    GEN t = gcoeff(L,i,k);
    coeff(L,i,k) = lmpsub(gcoeff(L,i,k-1), mpmul(la,t));
    coeff(L,i,k-1) = lmpadd(t, mpmul(gcoeff(L,k,k-1), gcoeff(L,i,k)));
  }
  return 1;
}
static void
ZincrementalGS(GEN x, GEN L, GEN B, long k, GEN fl, int gram)
{
  GEN u = NULL; /* gcc -Wall */
  long i, j, s;
  for (j=1; j<=k; j++)
    if (j==k || fl[j])
    {
      gpmem_t av = avma;
      u = gram? gcoeff(x,k,j): gscali((GEN)x[k], (GEN)x[j]);
      for (i=1; i<j; i++)
        if (fl[i])
        {
          u = subii(mulii((GEN)B[i+1], u), mulii(gcoeff(L,k,i), gcoeff(L,j,i)));
          u = diviiexact(u, (GEN)B[i]);
        }
      coeff(L,k,j) = (long)gerepileuptoint(av, u);
    }
  s = signe(u);
  if (s == 0) B[k+1] = B[k];
  else
  {
    if (s < 0) err(lllger3);
    B[k+1] = coeff(L,k,k); coeff(L,k,k) = un; fl[k] = 1;
  }
}

/* x integer matrix. Beware: this function can return NULL */
GEN
lllint_marked(long MARKED, GEN x, long D, int gram,
              GEN *pth, GEN *ptfl, GEN *ptB)
{
  long lx = lg(x), hx, i, j, k, l, n, kmax;
  gpmem_t av, lim;
  GEN B,L,h,fl;

  if (typ(x) != t_MAT) err(typeer,"lllint");
  n = lx-1; if (n <= 1) return NULL;
  hx = lg(x[1]);
  if (gram && hx != lx) err(mattype1,"lllint");
  fl = cgetg(lx,t_VECSMALL);

  av = avma; lim = stack_lim(av,1); x = dummycopy(x);
  B = gscalcol(gun, lx);
  L = cgetg(lx,t_MAT);
  for (j=1; j<lx; j++)
  {
    for (i=1; i<hx; i++)
      if (typ(gcoeff(x,i,j)) != t_INT) err(lllger4);
    fl[j] = 0; L[j] = (long)zerocol(n);
  }
  h = pth? idmat(n): NULL;
  ZincrementalGS(x, L, B, 1, fl, gram);
  kmax = 1;
  if (DEBUGLEVEL>5) fprintferr("k = ");
  for (k=2;;)
  {
    if (k > kmax)
    {
      if (DEBUGLEVEL>3) fprintferr("K%ld ",k);
      ZincrementalGS(x, L, B, k, fl, gram);
      kmax = k;
    }
    if (k != MARKED)
    {
      if (!gram) ZRED(k,k-1, x,h,L,(GEN)B[k],kmax);
      else  ZRED_gram(k,k-1, x,h,L,(GEN)B[k],kmax);
    }
    if (do_ZSWAP(x,h,L,B,kmax,k,D,fl,gram))
    {
      if      (MARKED == k)   MARKED = k-1;
      else if (MARKED == k-1) MARKED = k;
      if (k > 2) k--;
    }
    else
    {
      if (k != MARKED)
        for (l=k-2; l; l--)
        {
          if (!gram) ZRED(k,l, x,h,L,(GEN)B[l+1],kmax);
          else  ZRED_gram(k,l, x,h,L,(GEN)B[l+1],kmax);
          if (low_stack(lim, stack_lim(av,1)))
          {
            if(DEBUGMEM>1) err(warnmem,"lllint[1]");
            gerepileall(av,h?4:3,&B,&L,&x,&h);
          }
        }
      if (++k > n) break;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"lllint[2]");
      gerepileall(av,h?4:3,&B,&L,&x,&h);
    }
  }
  if (DEBUGLEVEL>3) fprintferr("\n");
  if (ptB)  *ptB  = B;
  if (ptfl) *ptfl = fl;
  if (pth)  *pth = h;
  if (MARKED && MARKED != 1)
  {
    if (h) { swap(h[1], h[MARKED]); } else swap(x[1], x[MARKED]);
  }
  return h? h: x;
}

/* Beware: this function can return NULL (dim x <= 1) */
GEN
lllint_i(GEN x, long D, int gram, GEN *pth, GEN *ptfl, GEN *ptB)
{
  return lllint_marked(0, x,D,gram,pth,ptfl,ptB);
}

/* return x * lllint(x). No garbage collection */
GEN
lllint_ip(GEN x, long D)
{
  GEN h = lllint_i(x, D, 0, NULL, NULL, NULL); 
  if (!h) h = x;
  return h;
}

GEN
lllall(GEN x, long D, int gram, long flag)
{
  gpmem_t av = avma;
  GEN fl, junk, h = lllint_i(x, D, gram, &junk, &fl, NULL);
  if (!h) return lll_trivial(x,flag);
  return gerepilecopy(av, lll_finish(h,fl,flag));
}

GEN
lllint(GEN x) { return lllall(x,LLLDFT,0, lll_IM); }

GEN
lllkerim(GEN x) { return lllall(x,LLLDFT,0, lll_ALL); }

GEN
lllgramint(GEN x) { return lllall(x,LLLDFT,1, lll_IM | lll_GRAM); }

GEN
lllgramkerim(GEN x) { return lllall(x,LLLDFT,1, lll_ALL | lll_GRAM); }

static int
pslg(GEN x)
{
  long tx;
  if (gcmp0(x)) return 2;
  tx = typ(x); return is_scalar_t(tx)? 3: lgef(x);
}

static GEN
to_mp(GEN x, long prec)
{
  GEN y;
  if (typ(x) == t_INT) return x;
  y = cgetr(prec);
  gaffect(x, y); return y;
}
static GEN
col_to_mp(GEN x, long prec)
{
  long j, l = lg(x);
  GEN y = cgetg(l, t_COL);
  for (j=1; j<l; j++) y[j] = (long)to_mp((GEN)x[j], prec);
  return y;
}
static GEN
mat_to_mp(GEN x, long prec)
{
  long j, l = lg(x);
  GEN y = cgetg(l, t_MAT);
  for (j=1; j<l; j++) y[j] = (long)col_to_mp((GEN)x[j], prec);
  return y;
}


static int
REDgen(long k, long l, GEN h, GEN L, GEN B)
{
  GEN u, q, cq;
  long i;

  u = gcoeff(L,k,l);
  if (pslg(u) < pslg((GEN)B[l+1])) return 0;

  q = gdeuc(u,(GEN)B[l+1]);
  cq = ginv(content(q));
  q = gneg(gmul(q,cq));
  h[k] = ladd(gmul(cq,(GEN)h[k]), gmul(q,(GEN)h[l]));
  coeff(L,k,l) = ladd(gmul(cq,gcoeff(L,k,l)), gmul(q,(GEN)B[l+1]));
  for (i=1; i<l; i++)
    coeff(L,k,i) = ladd(gmul(cq,gcoeff(L,k,i)), gmul(q,gcoeff(L,l,i)));
  return 1;
}

static int
do_SWAPgen(GEN h, GEN L, GEN B, long k, GEN fl, int *flc)
{
  GEN p1, la, la2, Bk;
  long ps1, ps2, i, j, lx;

  if (!fl[k-1]) return 0;

  la = gcoeff(L,k,k-1); la2 = gsqr(la);
  Bk = (GEN)B[k];
  if (fl[k])
  {
    GEN q = gadd(la2, gmul((GEN)B[k-1],(GEN)B[k+1]));
    ps1 = pslg(gsqr(Bk));
    ps2 = pslg(q);
    if (ps1 <= ps2 && (ps1 < ps2 || !*flc)) return 0;
    *flc = (ps1 != ps2);
    B[k] = ldiv(q, Bk);
  }

  swap(h[k-1], h[k]); lx = lg(L);
  for (j=1; j<=k-2; j++) swap(coeff(L,k-1,j), coeff(L,k,j));
  if (fl[k])
  {
    for (i=k+1; i<lx; i++)
    {
      GEN t = gcoeff(L,i,k);
      p1 = gsub(gmul((GEN)B[k+1],gcoeff(L,i,k-1)), gmul(la,t));
      coeff(L,i,k)   = ldiv(p1, Bk);
      p1 = gadd(gmul(la,gcoeff(L,i,k-1)), gmul((GEN)B[k-1],t));
      coeff(L,i,k-1) = ldiv(p1, Bk);
    }
  }
  else if (!gcmp0(la))
  {
    p1 = gdiv(la2, Bk);
    B[k+1] = B[k] = (long)p1;
    for (i=k+2; i<=lx; i++) B[i] = ldiv(gmul(p1,(GEN)B[i]),Bk);
    for (i=k+1; i<lx; i++)
      coeff(L,i,k-1) = ldiv(gmul(la,gcoeff(L,i,k-1)), Bk);
    for (j=k+1; j<lx-1; j++)
      for (i=j+1; i<lx; i++)
        coeff(L,i,j) = ldiv(gmul(p1,gcoeff(L,i,j)), Bk);
  }
  else
  {
    coeff(L,k,k-1) = zero;
    for (i=k+1; i<lx; i++)
    {
      coeff(L,i,k) = coeff(L,i,k-1);
      coeff(L,i,k-1) = zero;
    }
    B[k] = B[k-1]; fl[k] = 1; fl[k-1] = 0;
  }
  return 1;
}

static void
incrementalGSgen(GEN x, GEN L, GEN B, long k, GEN fl)
{
  GEN u = NULL; /* gcc -Wall */
  long i, j, tu;
  for (j=1; j<=k; j++)
    if (j==k || fl[j])
    {
      u = gcoeff(x,k,j); tu = typ(u);
      if (! is_scalar_t(tu) && tu != t_POL) err(lllger4);
      for (i=1; i<j; i++)
        if (fl[i])
        {
          u = gsub(gmul((GEN)B[i+1],u), gmul(gcoeff(L,k,i),gcoeff(L,j,i)));
          u = gdiv(u, (GEN)B[i]);
        }
      coeff(L,k,j) = (long)u;
    }
  if (gcmp0(u)) B[k+1] = B[k];
  else
  {
    B[k+1] = coeff(L,k,k); coeff(L,k,k) = un; fl[k] = 1;
  }
}

static GEN
lllgramallgen(GEN x, long flag)
{
  long lx = lg(x), i, j, k, l, n;
  gpmem_t av0 = avma, av, lim;
  GEN B, L, h, fl;
  int flc;

  if (typ(x) != t_MAT) err(typeer,"lllgramallgen");
  n = lx-1; if (n<=1) return lll_trivial(x,flag);
  if (lg(x[1]) != lx) err(mattype1,"lllgramallgen");

  fl = cgetg(lx, t_VECSMALL);

  av = avma; lim = stack_lim(av,1);
  B = gscalcol(gun, lx);
  L = cgetg(lx,t_MAT);
  for (j=1; j<lx; j++) { L[j] = (long)zerocol(n); fl[j] = 0; }

  h = idmat(n);
  for (i=1; i<lx; i++)
    incrementalGSgen(x, L, B, i, fl);
  flc = 0;
  for(k=2;;)
  {
    if (REDgen(k, k-1, h, L, B)) flc = 1;
    if (do_SWAPgen(h, L, B, k, fl, &flc)) { if (k > 2) k--; }
    else
    {
      for (l=k-2; l>=1; l--)
        if (REDgen(k, l, h, L, B)) flc = 1;
      if (++k > n) break;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"lllgramallgen");
      gerepileall(av,3,&B,&L,&h);
    }
  }
  return gerepilecopy(av0, lll_finish(h,fl,flag));
}

/* zero x[1..k-1] */
static int
FindApplyH(GEN x, GEN mu, GEN B, long k, GEN P, long prec)
{
  long i, lx = lg(x)-1, lv = lx - (k-1);
  GEN v, p1, beta, Nx, x2, x1, xd = x + (k-1);

  x1 = (GEN)xd[1];
  x2 = gsqr(x1);
  if (k < lx)
  {
    v = cgetg(lv+1, t_VEC);
    for (i=2; i<=lv; i++) x2 = mpadd(x2, gsqr((GEN)xd[i]));
    if (gcmp0(x2)) return 0;

    Nx = gsqrt(x2, prec);
    if (signe(x1) < 0) setsigne(Nx, -1);
    v[1] = lmpadd(x1, Nx);
    for (i=2; i<=lv; i++) v[i] = xd[i];

    beta = ginv(mpadd(x2, mpmul(Nx,x1)));
    p1 = cgetg(3,t_VEC); P[k] = (long)p1;
    p1[1] = (long)beta;
    p1[2] = (long)v;

    coeff(mu,k,k) = lmpneg(Nx);
  }
  else
    coeff(mu,k,k) = x[k];
  for (i=1; i<k; i++) coeff(mu,k,i) = x[i];
  B[k] = (long)x2; return 1;
}

static void
ApplyH(GEN P, GEN r)
{
  GEN s, rd, beta = (GEN)P[1], v = (GEN)P[2];
  long i, l = lg(v), lr = lg(r);

  rd = r + (lr - l);
  s = mpmul((GEN)v[1], (GEN)rd[1]);
  for (i=2; i<l; i++) s = mpadd(s, mpmul((GEN)v[i] ,(GEN)rd[i]));
  s = mpneg(mpmul(beta, s));
  for (i=1; i<l; i++) rd[i] = lmpadd((GEN)rd[i], mpmul(s, (GEN)v[i]));
}

/* compute B[k] = | x[k] |^2, update mu(k, 1..k-1) using Householder matrices
 * (P = Householder(x[1..k-1]) in factored form) */
static int
incrementalH(GEN x, GEN L, GEN B, long k, GEN P, long prec)
{
  gpmem_t av = avma;
  GEN r = dummycopy((GEN)x[k]);
  long j;
  for (j=1; j<k; j++) ApplyH((GEN)P[j], r);
  r = gerepilecopy(av, r);
  return FindApplyH(r, L, B, k, P, prec);
}

static int
Householder_get_mu(GEN x, GEN L, GEN B, long k, long prec)
{
  GEN Nx, invNx, m, P = cgetg(k+1, t_VEC);
  long i, j;
  for (j=1; j<=k; j++)
    if (! incrementalH(x,L,B,j,P,prec)) return 0;
  for (j=1; j<=k; j++)
  {
    m = (GEN)L[j]; Nx = (GEN)m[j]; m[j] = un;
    if (j == k) break;
    invNx = ginv(Nx); 
    for (i=j+1; i<=k; i++) m[i] = lmpmul(invNx, (GEN)m[i]);
  }
  return 1;
}

GEN
R_from_QR(GEN x, long prec)
{
  long j, k = lg(x)-1;
  GEN L, B = zerovec(k), P = cgetg(k+1, t_VEC);
  L = cgetg(k+1, t_MAT);
  for (j=1; j<=k; j++) L[j] = (long)zerocol(k);
  for (j=1; j<=k; j++)
    if (! incrementalH(x,L,B,j,P,prec)) return NULL;
  return L;
}

/* compute B[k] = | x[k] |^2, update mu(k, 1..k-1).
 * Classical Gram-Schmidt (unstable!) */
static int
incrementalGS(GEN x, GEN mu, GEN B, long k)
{
  GEN s,A = cgetg(k+1, t_COL); /* scratch space */
  long i, j;
  gpmem_t av;
  A[1] = coeff(x,k,1);
  for(j=1;j<k;)
  {
    coeff(mu,k,j) = lmpdiv((GEN)A[j], (GEN)B[j]);
    j++; av = avma;
    /* A[j] <-- x[k,j] - sum_{i<j} mu[j,i] A[i] */
    s = mpmul(gcoeff(mu,j,1),(GEN)A[1]);
    for (i=2; i<j; i++) s = mpadd(s, mpmul(gcoeff(mu,j,i),(GEN)A[i]));
    s = mpneg(s); A[j] = (long)gerepileuptoleaf(av, mpadd(gcoeff(x,k,j), s));
  }
  B[k] = A[k]; return (signe((GEN)B[k]) > 0);
}

/* x = Gram(b_i). If precision problems return NULL if flag=1, error otherwise.
 * Quality ratio = delta = (D-1)/D. Suggested value: D = 100
 *
 * If MARKED != 0 make sure e[MARKED] is the first vector of the output basis
 * (which may then not be LLL-reduced) */
GEN
lllfp_marked(int MARKED, GEN x, long D, long flag, long prec, int gram)
{
  GEN xinit,L,h,B,L1,delta;
  long retry = 2, lx = lg(x), hx, l, i, j, k, k1, n, kmax, KMAX;
  gpmem_t av0 = avma, av, lim;

  if (typ(x) != t_MAT) err(typeer,"lllfp");
  n = lx-1; if (n <= 1) return idmat(n);
  hx = lg(x[1]);
  if (gram && hx != lx) err(mattype1,"lllfp");
  delta = cgetr(DEFAULTPREC); affsr(D-1,delta);
  delta = divrs(delta,D);
  xinit = x;
  av = avma; lim = stack_lim(av,1);
  if (gram) {
    for (k=2,j=1; j<lx; j++)
    {
      GEN p1=(GEN)x[j];
      for (i=1; i<=j; i++)
        if (typ(p1[i]) == t_REAL) { l = lg(p1[i]); if (l>k) k=l; }
    }
  } else {
    for (k=2,j=1; j<lx; j++)
    {
      GEN p1=(GEN)x[j];
      for (i=1; i<hx; i++)
        if (typ(p1[i]) == t_REAL) { l = lg(p1[i]); if (l>k) k=l; }
    }
  }
  if (k == 2)
  {
    if (!prec) return gram? lllgramint(x): lllint(x);
    x = gmul(x, realun(prec+1));
  }
  else
  {
    if (prec < k) prec = k;
    x = mat_to_mp(x, prec+1);
  }
 /* kmax = maximum column index attained during this run
  * KMAX = same over all runs (after PRECPB) */
  kmax = KMAX = 1;

PRECPB:
  switch(retry--)
  {
    case 2: h = idmat(n); break; /* entry */
    case 1:
      if (flag == 2) return _vec(h);
      if (gram && kmax > 2)
      { /* some progress but precision loss, try again */
        prec = (prec<<1)-2; kmax = 1;
        if (DEBUGLEVEL > 3) fprintferr("\n");
        if (DEBUGLEVEL) err(warnprec,"lllfp",prec);
        x = gprec_w(xinit,prec);
        if (gram) x = qf_base_change(x,h,1); else x = gmul(x,h);
        gerepileall(av,2,&h,&x);
        if (DEBUGLEVEL) err(warner,"lllfp starting over");
        break;
      } /* fall through */
    case 0: /* give up */
      if (DEBUGLEVEL > 3) fprintferr("\n");
      if (DEBUGLEVEL) err(warner,"lllfp giving up");
      if (flag) { avma=av; return NULL; }
      if (DEBUGLEVEL) outerr(xinit);
      err(lllger3);
  }

  L=cgetg(lx,t_MAT);
  B=cgetg(lx,t_COL);
  for (j=1; j<lx; j++) { L[j] = (long)zerocol(n); B[j] = zero; }
  if (gram && !incrementalGS(x, L, B, 1))
  {
    if (!flag) return NULL; 
    err(lllger3);
  }
  if (DEBUGLEVEL>5) fprintferr("k =");
  for(k=2;;)
  {
    if (k > kmax)
    {
      kmax = k; if (KMAX < kmax) KMAX = kmax;
      if (DEBUGLEVEL>3) {fprintferr(" K%ld",k);flusherr();}
      if (gram) j = incrementalGS(x, L, B, k);
      else      j = Householder_get_mu(x, L, B, k, prec);
      if (!j) goto PRECPB;
    }
    else if (DEBUGLEVEL>5) fprintferr(" %ld",k);
    L1 = gcoeff(L,k,k-1);
    if (typ(L1) == t_REAL && expo(L1) + 20 > bit_accuracy(lg(L1)))
    {
      if (DEBUGLEVEL>3)
	fprintferr("\nRecomputing Gram-Schmidt, kmax = %ld\n", kmax);
      if (!gram) goto PRECPB;
      for (k1=1; k1<=kmax; k1++)
        if (!incrementalGS(x, L, B, k1)) goto PRECPB;
    }
    if (k != MARKED)
    {
      if (!gram) j = RED(k,k-1, x,h,L,KMAX);
      else j = RED_gram(k,k-1, x,h,L,KMAX);
      if (!j) goto PRECPB;
    }
    if (do_SWAP(x,h,L,B,kmax,k,delta,1))
    {
      if      (MARKED == k)   MARKED = k-1;
      else if (MARKED == k-1) MARKED = k;
      if (!B[k]) goto PRECPB;
      if (k>2) k--;
    }
    else
    {
      if (k != MARKED)
        for (l=k-2; l; l--)
        {
          if (!gram) j = RED(k,l, x,h,L,KMAX);
          else  j = RED_gram(k,l, x,h,L,KMAX);
          if (!j) goto PRECPB;
          if (low_stack(lim, stack_lim(av,1)))
          {
            if(DEBUGMEM>1) err(warnmem,"lllfp[1]");
            gerepileall(av,4,&B,&L,&h,&x);
          }
        }
      if (++k > n) break;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"lllfp[2]");
      gerepileall(av,4,&B,&L,&h,&x);
    }
  }
  if (DEBUGLEVEL>3) fprintferr("\n");
  if (MARKED && MARKED != 1) swap(h[1], h[MARKED]);
  return gerepilecopy(av0, h);
}

GEN
lllgramintern(GEN x, long D, long flag, long prec)
{
  return lllfp_marked(0, x,D,flag,prec,1);
}

GEN
lllintern(GEN x, long D, long flag, long prec)
{
  return lllfp_marked(0, x,D,flag,prec,0);
}

GEN
lllgram(GEN x,long prec) { return lllgramintern(x,LLLDFT,0,prec); }

GEN
lll(GEN x,long prec) { return lllintern(x,LLLDFT,0,prec); }

GEN
qflll0(GEN x, long flag, long prec)
{
  switch(flag)
  {
    case 0: return lll(x,prec);
    case 1: return lllint(x);
    case 2: return lllintpartial(x);
    case 4: return lllkerim(x);
    case 5: return lllkerimgen(x);
    case 8: return lllgen(x);
    default: err(flagerr,"qflll");
  }
  return NULL; /* not reached */
}

GEN
qflllgram0(GEN x, long flag, long prec)
{
  switch(flag)
  {
    case 0: return lllgram(x,prec);
    case 1: return lllgramint(x);
    case 4: return lllgramkerim(x);
    case 5: return lllgramkerimgen(x);
    case 8: return lllgramgen(x);
    default: err(flagerr,"qflllgram");
  }
  return NULL; /* not reached */
}

static GEN
gram(GEN b)
{
  long i,j, lx = lg(b);
  GEN g;
  if (typ(b) != t_MAT) err(typeer,"gram");
  g = cgetg(lx,t_MAT);
  for (i=1; i<lx; i++)
  {
    g[i] = lgetg(lx,t_COL);
    for (j=1; j<=i; j++)
      coeff(g,i,j) = coeff(g,j,i) = (long)gscal((GEN)b[i],(GEN)b[j]);
  }
  return g;
}

GEN
lllgen(GEN x) {
  gpmem_t av = avma;
  return gerepileupto(av, lllgramgen(gram(x)));
}

GEN
lllkerimgen(GEN x) {
  gpmem_t av = avma;
  return gerepileupto(av, lllgramallgen(gram(x),lll_ALL));
}

GEN
lllgramgen(GEN x) { return lllgramallgen(x,lll_IM); }

GEN
lllgramkerimgen(GEN x) { return lllgramallgen(x,lll_ALL); }

/*  This routine is functionally similar to lllint when all = 0.
 *
 *    The input is an integer matrix mat (not necessarily square) whose
 *  columns are linearly independent.  It outputs another matrix T such that
 *  mat * T is partially reduced.  If all = 0, the size of mat * T is the
 *  same as the size of mat.  If all = 1 the number of columns of mat * T
 *  is at most equal to its number of rows.  A matrix M is said to be
 *  -partially reduced- if | m1 +- m2 | >= |m1| for any two distinct
 *  columns m1, m2, in M.
 *
 *    This routine is designed to quickly reduce lattices in which one row
 *  is huge compared to the other rows.  For example, when searching for a
 *  polynomial of degree 3 with root a mod p, the four input vectors might
 *  be the coefficients of
 *      X^3 - (a^3 mod p), X^2 - (a^2 mod p), X - (a mod p), p.
 *  All four constant coefficients are O(p) and the rest are O(1). By the
 *  pigeon-hole principle, the coefficients of the smallest vector in the
 *  lattice are O(p^(1/4)), Hence significant reduction of vector lengths
 *  can be anticipated.
 *
 *  		Peter Montgomery (July, 1994)
 *
 *  If flag = 1 complete the reduction using lllint, otherwise return
 *  partially reduced basis.
 */
GEN
lllintpartialall(GEN m, long flag)
{
  const long ncol = lg(m)-1;
  const gpmem_t ltop1 = avma;
  long ncolnz;
  GEN tm1, tm2, mid;

  if (typ(m) != t_MAT) err(typeer,"lllintpartialall");
  if (ncol <= 1) return idmat(ncol);

  {
    GEN dot11 = sqscali((GEN)m[1]);
    GEN dot22 = sqscali((GEN)m[2]);
    GEN dot12 = gscali((GEN)m[1], (GEN)m[2]);
    GEN tm  = idmat(2); /* For first two columns only */

    int progress = 0;
    long npass2 = 0;

/* Try to row reduce the first two columns of m.
 * Our best result so far is (first two columns of m)*tm.
 *
 * Initially tm = 2 x 2 identity matrix.
 * The inner products of the reduced matrix are in
 * dot11, dot12, dot22.
 */
    while (npass2 < 2 || progress)
    {
      GEN dot12new,q = diviiround(dot12, dot22);

      npass2++; progress = signe(q);
      if (progress)
      {
       /* Conceptually replace (v1, v2) by (v1 - q*v2, v2),
        * where v1 and v2 represent the reduced basis for the
        * first two columns of the matrix.
        *
        * We do this by updating tm and the inner products.
        *
        * An improved algorithm would look only at the leading
        * digits of dot11, dot12, dot22.  It would use
        * single-precision calculations as much as possible.
        */
        q = negi(q);
        dot12new = addii(dot12, mulii(q, dot22));
        dot11 = addii(dot11, mulii(q, addii(dot12, dot12new)));
        dot12 = dot12new;
        tm[1] = (long)ZV_lincomb(gun,q, (GEN)tm[1],(GEN)tm[2]);
      }

      /* Interchange the output vectors v1 and v2.  */
      gswap(dot11,dot22); swap(tm[1],tm[2]);

      /* Occasionally (including final pass) do garbage collection.  */
      if (npass2 % 8 == 0 || !progress)
        gerepileall(ltop1, 4, &dot11,&dot12,&dot22,&tm);
    } /* while npass2 < 2 || progress */

    {
      long icol;
      GEN det12 = subii(mulii(dot11, dot22), mulii(dot12, dot12));

      tm1 = idmat(ncol);
      mid = cgetg(ncol+1, t_MAT);
      for (icol = 1; icol <= 2; icol++)
      {
        coeff(tm1,1,icol) = coeff(tm,1,icol);
	coeff(tm1,2,icol) = coeff(tm,2,icol);
        mid[icol] = (long)ZV_lincomb(
           gcoeff(tm,1,icol),gcoeff(tm,2,icol), (GEN)m[1],(GEN)m[2]);
      }
      for (icol = 3; icol <= ncol; icol++)
      {
        GEN curcol = (GEN)m[icol];
	GEN dot1i = gscali((GEN)mid[1], curcol);
        GEN dot2i = gscali((GEN)mid[2], curcol);
       /* Try to solve
        *
        * ( dot11  dot12 ) (q1)    ( dot1i )
        * ( dot12  dot22 ) (q2)  = ( dot2i )
        *
        * Round -q1 and -q2 to the nearest integer.
        * Then compute curcol - q1*mid[1] - q2*mid[2].
        * This will be approximately orthogonal to the
        * first two vectors in the new basis.
        */
	GEN q1neg = subii(mulii(dot12, dot2i), mulii(dot22, dot1i));
        GEN q2neg = subii(mulii(dot12, dot1i), mulii(dot11, dot2i));

        q1neg = diviiround(q1neg, det12);
        q2neg = diviiround(q2neg, det12);
        coeff(tm1, 1, icol) = ladd(gmul(q1neg, gcoeff(tm,1,1)),
				   gmul(q2neg, gcoeff(tm,1,2)));
        coeff(tm1, 2, icol) = ladd(gmul(q1neg, gcoeff(tm,2,1)),
				   gmul(q2neg, gcoeff(tm,2,2)));
        mid[icol] = ladd(curcol,
          ZV_lincomb(q1neg,q2neg, (GEN)mid[1],(GEN)mid[2]));
      } /* for icol */
    } /* local block */
  }
  if (DEBUGLEVEL>6)
  {
    fprintferr("tm1 = %Z",tm1);
    fprintferr("mid = %Z",mid);
  }
  gerepileall(ltop1,2, &tm1, &mid);
  {
   /* For each pair of column vectors v and w in mid * tm2,
    * try to replace (v, w) by (v, v - q*w) for some q.
    * We compute all inner products and check them repeatedly.
    */
    const gpmem_t ltop3 = avma; /* Excludes region with tm1 and mid */
    const gpmem_t lim = stack_lim(ltop3,1);
    long icol, reductions, npass = 0;
    GEN dotprd = cgetg(ncol+1, t_MAT);

    tm2 = idmat(ncol);
    for (icol=1; icol <= ncol; icol++)
    {
      long jcol;

      dotprd[icol] = lgetg(ncol+1,t_COL);
      for (jcol=1; jcol <= icol; jcol++)
	coeff(dotprd,jcol,icol) = coeff(dotprd,icol,jcol) =
          (long)gscali((GEN)mid[icol], (GEN)mid[jcol]);
    } /* for icol */
    for(;;)
    {
      reductions = 0;
      for (icol=1; icol <= ncol; icol++)
      {
	long ijdif, jcol, k1, k2;
	GEN codi, q;

        for (ijdif=1; ijdif < ncol; ijdif++)
	{
          const gpmem_t previous_avma = avma;

          jcol = (icol + ijdif - 1) % ncol; jcol++; /* Hack for NeXTgcc 2.5.8 */
          k1 = (cmpii(gcoeff(dotprd,icol,icol),
		      gcoeff(dotprd,jcol,jcol) ) > 0)
		? icol : jcol; 	/* index of larger column */
	  k2 = icol + jcol - k1; 	/* index of smaller column */
	  codi = gcoeff(dotprd,k2,k2);
	  q = gcmp0(codi)? gzero: diviiround(gcoeff(dotprd,k1,k2), codi);

	  /* Try to subtract a multiple of column k2 from column k1.  */
	  if (gcmp0(q)) avma = previous_avma;
          else
	  {
	    long dcol;

	    reductions++; q = negi(q);
	    tm2[k1]=(long)
              ZV_lincomb(gun,q, (GEN)tm2[k1], (GEN)tm2[k2]);
	    dotprd[k1]=(long)
              ZV_lincomb(gun,q, (GEN)dotprd[k1], (GEN)dotprd[k2]);
	    coeff(dotprd, k1, k1) = laddii(gcoeff(dotprd,k1,k1),
				           mulii(q, gcoeff(dotprd,k2,k1)));
	    for (dcol = 1; dcol <= ncol; dcol++)
	      coeff(dotprd,k1,dcol) = coeff(dotprd,dcol,k1);
	  } /* if q != 0 */
        } /* for ijdif */
        if (low_stack(lim, stack_lim(ltop3,1)))
	{
          if(DEBUGMEM>1) err(warnmem,"lllintpartialall");
	  gerepileall(ltop3, 2, &dotprd,&tm2);
        }
      } /* for icol */
      if (!reductions) break;
      if (DEBUGLEVEL>6)
      {
	GEN diag_prod = dbltor(1.0);
	for (icol = 1; icol <= ncol; icol++)
	  diag_prod = gmul(diag_prod, gcoeff(dotprd,icol,icol));
        npass++;
	fprintferr("npass = %ld, red. last time = %ld, diag_prod = %Z\n\n",
	            npass, reductions, diag_prod);
      }
    } /* for(;;)*/

   /* Sort columns so smallest comes first in m * tm1 * tm2.
    * Use insertion sort.
    */
    for (icol = 1; icol < ncol; icol++)
    {
      long jcol, s = icol;

      for (jcol = icol+1; jcol <= ncol; jcol++)
	if (cmpii(gcoeff(dotprd,s,s),gcoeff(dotprd,jcol,jcol)) > 0) s = jcol;
      if (icol != s)
      { /* Exchange with proper column */
        /* Only diagonal of dotprd is updated */
        swap(tm2[icol], tm2[s]);
        swap(coeff(dotprd,icol,icol), coeff(dotprd,s,s));
      }
    } /* for icol */
    icol=1;
    while (icol <= ncol && !signe(gcoeff(dotprd,icol,icol))) icol++;
    ncolnz = ncol - icol + 1;
  } /* local block */

  if (flag)
  {
    if (ncolnz == lg((GEN)m[1])-1)
    {
      tm2 += (ncol-ncolnz);
      tm2[0]=evaltyp(t_MAT)|evallg(ncolnz+1);
    }
    else
    {
      tm1 = gmul(tm1, tm2);
      tm2 = lllint(gmul(m, tm1));
    }
  }
  if (DEBUGLEVEL>6)
    fprintferr("lllintpartial output = %Z", gmul(tm1, tm2));
  return gerepileupto(ltop1, gmul(tm1, tm2));
}

GEN
lllintpartial(GEN mat)
{
  return lllintpartialall(mat,1);
}

/********************************************************************/
/**                                                                **/
/**                   LINEAR & ALGEBRAIC DEPENDENCE                **/
/**                                                                **/
/********************************************************************/

GEN pslq(GEN x, long prec);
GEN pslqtwolevel(GEN x, long prec);

GEN
lindep0(GEN x,long bit,long prec)
{
  switch (bit)
  {
    case 0: return pslq(x,prec);
    case -1: return lindep(x,prec);
    case -2: return deplin(x);
    case -3: return pslqtwolevel(x,prec);
    default: return lindep2(x,labs(bit));
  }
}

static int
real_indep(GEN re, GEN im, long bitprec)
{
  GEN p1 = gsub(gmul((GEN)re[1],(GEN)im[2]),
                gmul((GEN)re[2],(GEN)im[1]));
  return (!gcmp0(p1) && gexpo(p1) > - bitprec);
}

GEN
lindep2(GEN x, long bit)
{
  long tx=typ(x), lx=lg(x), ly, i, j, e;
  gpmem_t av = avma;
  GEN re,im,p1,p2;

  if (! is_vec_t(tx)) err(typeer,"lindep2");
  if (lx<=2) return cgetg(1,t_VEC);
  re = greal(x);
  im = gimag(x); bit = (long) (bit/L2SL10);
  /* independant over R ? */
  if (lx == 3 && real_indep(re,im,bit))
    { avma = av; return cgetg(1, t_VEC); }

  if (gcmp0(im)) im = NULL;
  ly = im? lx+2: lx+1;
  p2=cgetg(lx,t_MAT);
  for (i=1; i<lx; i++)
  {
    p1 = cgetg(ly,t_COL); p2[i] = (long)p1;
    for (j=1; j<lx; j++) p1[j] = (i==j)? un: zero;
    p1[lx]           = lcvtoi(gshift((GEN)re[i],bit),&e);
    if (im) p1[lx+1] = lcvtoi(gshift((GEN)im[i],bit),&e);
  }
  p1 = (GEN)lllint_ip(p2,100)[1];
  p1[0] = evaltyp(t_VEC) | evallg(lx);
  return gerepilecopy(av, p1);
}

#define quazero(x) (gcmp0(x) || (typ(x)==t_REAL && expo(x) < EXP))
GEN
lindep(GEN x, long prec)
{
  GEN *b,*be,*bn,**m,qzer;
  GEN c1,c2,c3,px,py,pxy,re,im,p1,p2,r,f,em;
  long i,j,fl,k, lx = lg(x), tx = typ(x), n = lx-1;
  gpmem_t av = avma, lim = stack_lim(av,1), av0, av1;
  const long EXP = - bit_accuracy(prec) + 2*n;

  if (! is_vec_t(tx)) err(typeer,"lindep");
  if (n <= 1) return cgetg(1,t_VEC);
  x = gmul(x, realun(prec));
  re = greal(x);
  im = gimag(x);
  /* independant over R ? */
  if (n == 2 && real_indep(re,im,bit_accuracy(prec)))
    { avma = av; return cgetg(1, t_VEC); }
  if (EXP > -10) err(precer,"lindep");

  qzer = cgetg(lx, t_VECSMALL);
  b = (GEN*)idmat(n);
  be= (GEN*)new_chunk(lx);
  bn= (GEN*)new_chunk(lx);
  m = (GEN**)new_chunk(lx);
  for (i=1; i<=n; i++)
  {
    bn[i] = cgetr(prec+1);
    be[i] = cgetg(lx,t_COL);
    m[i]  = (GEN*)new_chunk(lx);
    for (j=1; j<i ; j++) m[i][j] = cgetr(prec+1);
    for (j=1; j<=n; j++) be[i][j]= lgetr(prec+1);
  }
  px = sqscal(re);
  py = sqscal(im); pxy = gscal(re,im);
  p1 = mpsub(mpmul(px,py), gsqr(pxy));
  if (quazero(px)) { re = im; px = py; fl = 1; } else fl = quazero(p1);
  av0 = av1 = avma;
  for (i=1; i<=n; i++)
  {
    p2 = gscal(b[i],re);
    if (fl) p2 = gmul(gdiv(p2,px),re);
    else
    {
      GEN p5,p6,p7;
      p5 = gscal(b[i],im);
      p6 = gdiv(gsub(gmul(py,p2),gmul(pxy,p5)), p1);
      p7 = gdiv(gsub(gmul(px,p5),gmul(pxy,p2)), p1);
      p2 = gadd(gmul(p6,re), gmul(p7,im));
    }
    if (tx != t_COL) p2 = gtrans(p2);
    p2 = gsub(b[i],p2);
    for (j=1; j<i; j++)
      if (qzer[j]) affrr(bn[j], m[i][j]);
      else
      {
        gdivz(gscal(b[i],be[j]),bn[j], m[i][j]);
        p2 = gsub(p2, gmul(m[i][j],be[j]));
      }
    gaffect(p2,          be[i]);
    affrr(sqscal(be[i]), bn[i]);
    qzer[i] = quazero(bn[i]); avma = av1;
  }
  while (qzer[n])
  {
    long e;
    if (DEBUGLEVEL>8)
    {
      fprintferr("qzer[%ld]=%ld\n",n,qzer[n]);
      for (k=1; k<=n; k++)
	for (i=1; i<k; i++) output(m[k][i]);
    }
    em=bn[1]; j=1;
    for (i=2; i<n; i++)
    {
      p1=shiftr(bn[i],i);
      if (cmprr(p1,em)>0) { em=p1; j=i; }
    }
    i=j; k=i+1;
    avma = av1; r = grndtoi(m[k][i], &e);
    if (e >= 0) err(precer,"lindep");
    r  = negi(r);
    p1 = ZV_lincomb(gun,r, b[k],b[i]);
    b[k] = b[i];
    b[i]  = p1;
    av1 = avma;
    f = addir(r,m[k][i]);
    for (j=1; j<i; j++)
      if (!qzer[j])
      {
        p1 = mpadd(m[k][j], mulir(r,m[i][j]));
        affrr(m[i][j],m[k][j]);
        mpaff(p1,m[i][j]);
      }
    c1 = addrr(bn[k], mulrr(gsqr(f),bn[i]));
    if (!quazero(c1))
    {
      c2 = divrr(mulrr(bn[i],f),c1); affrr(c2, m[k][i]);
      c3 = divrr(bn[k],c1);
      mulrrz(c3,bn[i], bn[k]); qzer[k] = quazero(bn[k]);
      affrr(c1,        bn[i]); qzer[i] = 0;
      for (j=i+2; j<=n; j++)
      {
        p1 = addrr(mulrr(m[j][k],c3), mulrr(m[j][i],c2));
        subrrz(m[j][i],mulrr(f,m[j][k]), m[j][k]);
        affrr(p1, m[j][i]);
      }
    }
    else
    {
      affrr(bn[i], bn[k]); qzer[k] = qzer[i];
      affrr(c1,    bn[i]); qzer[i] = 1;
      for (j=i+2; j<=n; j++) affrr(m[j][i], m[j][k]);
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"lindep");
      b = (GEN*)gerepilecopy(av0, (GEN)b);
      av1 = avma;
    }
  }
  p1 = cgetg(lx,t_COL); p1[n] = un; for (i=1; i<n; i++) p1[i] = zero;
  p2 = (GEN)b; p2[0] = evaltyp(t_MAT) | evallg(lx);
  p2 = gauss(gtrans_i(p2),p1);
  return gerepileupto(av, gtrans(p2));
}

/* PSLQ Programs. Not nice to have global variables. Change */

static GEN y, H, A, B, Abargen, Bbargen;
static double *ybar, **Hbar, **Abar, **Bbar, *Wbar, **Pbar;
static double *ybarst, **Hbarst, **Abarst, **Bbarst;

/* attention : pour les matrices en double, A[i] est la i-ieme LIGNE de A */


double
sqrd(double a)
{
  return a*a;
}

static GEN
cxground(GEN x)
{
  GEN p1;

  if (typ(x)==t_COMPLEX)
  {
    p1 = cgetg(3,t_COMPLEX);
    p1[1]=(long)ground((GEN)x[1]); p1[2]=(long)ground((GEN)x[2]);
    return p1;
  }
  else return ground(x);
}

static void
redall(long i, long jsup)
{
  long j, k;
  GEN t,p2;
  const GEN p1 = (GEN)B[i];

  for (j=jsup; j>=1; j--)
  {
    p2 = (GEN)B[j];
/* modifier en grndtoi */
    t = cxground(gdiv(gcoeff(H,i,j),gcoeff(H,j,j)));
    y[j] = ladd((GEN)y[j],gmul(t,(GEN)y[i]));
    for (k=1; k<=j; k++)
      coeff(H,i,k) = lsub(gcoeff(H,i,k),gmul(t,gcoeff(H,j,k)));
    for (k=1; k<lg(y); k++)
    {
      coeff(A,i,k) = lsub(gcoeff(A,i,k),gmul(t,gcoeff(A,j,k)));
      p2[k] = ladd((GEN)p2[k],gmul(t,(GEN)p1[k]));
    }
  }
}

static void
redallbar(long i, long jsup)
{
  long j, k;
  double t;
  double *p1 = Hbar[i], *p2 = Abar[i], *p3, *p4;

  for (j=jsup; j>=1; j--)
  {
    p3 = Hbar[j]; p4 = Abar[j];
    t = floor(0.5+p1[j]/p3[j]);
    ybar[j] += t*ybar[i];
    for (k=1; k<=j; k++) p1[k] -= t*p3[k];
    for (k=1; k<lg(y); k++) {p2[k] -= t*p4[k]; Bbar[k][j] += t*Bbar[k][i];}
  }
}

long
vecmaxind(GEN v)
{
  long n = lg(v), m, i;
  GEN la;

  la=(GEN)v[1]; m=1;
  for (i=2; i<n; i++)
    if (gcmp((GEN)v[i],la)>0) {la=(GEN)v[i]; m=i;}
  return m;
}

long
vecmaxindbar(double *v, long n)
{
  long m, i;
  double la;

  la=v[1]; m=1;
  for (i=2; i<=n; i++)
    if (v[i]>la) {la=v[i]; m=i;}
  return m;
}

GEN
maxnorml2()
{
  long n = lg(y) - 1, i, j;
  GEN ma = gzero,s;

  for (i=1; i<=n; i++)
  {
    s = gzero;
    for (j=1; j<n; j++)
      s = gadd(s,gnorm(gcoeff(H,i,j)));
    ma = gmax(ma,s);
  }
  return ma;
}

double
maxnorml2bar()
{
  long n = lg(y) - 1, i, j;
  double ma = 0.0,s;

  for (i=1; i<=n; i++)
  {
    s = 0.0;
    for (j=1; j<n; j++) s += sqrd(Hbar[i][j]);
    if (s > ma) ma = s;
  }
  return ma;
}

GEN
pslq(GEN x, long prec)
{
  GEN ga,tabga,s,s1,sinv,p1,p2,res,t0,t1,t2,t3,t4,tinv,M;
  long lx = lg(x), tx = typ(x), n = lx-1, k, i, j, m, ct, fl, flreal;
  gpmem_t av = avma, lim = stack_lim(av,1), av0,tetpil;
  long tvmind=0, t12=0, t1234=0, treda=0, tfin=0;
  const long EXP = - bit_accuracy(prec) + 2*n;

  if (! is_vec_t(tx)) err(typeer,"pslq");
  if (n <= 1) return cgetg(1,t_VEC);
  if (DEBUGLEVEL>=3) (void)timer();
  if (gexpo(gimag(x)) > EXP)
  {
    return lindep(x,prec);
/*    err(impl,"pslq for complex arguments"); */
    ga = gsqrt(gdeux,prec); flreal = 0;
  }
  else
  {
    x = greal(x); flreal = 1;
    ga = gsqrt(gdiv(stoi(4),stoi(3)),prec);
  }
  x = gmul(x, realun(prec));
  tabga = cgetg(n,t_VEC); tabga[1] = (long)ga;
  for (i=2; i<n; i++) tabga[i] = lmul((GEN)tabga[i-1],ga);
  A = idmat(n); B = idmat(n);
  s1 = cgetg(lx,t_VEC); s = cgetg(lx,t_VEC);
  s1[n] = lnorm((GEN)x[n]); s[n] = (long)gabs((GEN)x[n],prec);
  for (k=n-1; k>=1; k--)
  {
    s1[k] = ladd((GEN)s1[k+1],gnorm((GEN)x[k]));
    s[k] = (long)gsqrt((GEN)s1[k],prec);
  }
  sinv = ginv((GEN)s[1]);
  y = gmul(sinv,x);
  s = gmul(sinv,s);
  H = cgetg(n,t_MAT);
  for (j=1; j<n; j++)
  {
    p1 = cgetg(lx,t_COL); H[j] = (long)p1;
    for (i=1; i<j; i++) p1[i] = zero;
    p1[j] = ldiv((GEN)s[j+1],(GEN)s[j]);
    p2 = gneg(gdiv((GEN)y[j],gmul((GEN)s[j],(GEN)s[j+1])));
    for (i=j+1; i<=n; i++) p1[i] = lmul(gconj((GEN)y[i]),p2);
  }
  for (i=2; i<=n; i++) redall(i,i-1);
  av0 = avma; ct = 0;
  if (DEBUGLEVEL>=3) printf("Initialization time = %ld\n",timer());
  for (;;)
  {
    ct++;
    p1 = cgetg(n,t_VEC);
    for (i=1; i<n; i++) p1[i] = lmul((GEN)tabga[i],gabs(gcoeff(H,i,i),prec));
    m = vecmaxind(p1);
    if (DEBUGLEVEL>=4) tvmind += timer();
    res = (GEN)y[m]; y[m] = y[m+1]; y[m+1] = (long)res;
    for (j=1; j<=n; j++)
    {
      res = gcoeff(A,m,j); coeff(A,m,j) = coeff(A,m+1,j);
      coeff(A,m+1,j)=(long)res;
    }
    for (j=1; j<n; j++)
    {
      res = gcoeff(H,m,j); coeff(H,m,j) = coeff(H,m+1,j);
      coeff(H,m+1,j)=(long)res;
    }
    res = (GEN)B[m]; B[m] = B[m+1]; B[m+1] = (long)res;
    if (m <= n-2)
    {
      t0 = gsqrt(gadd(gnorm(gcoeff(H,m,m)),gnorm(gcoeff(H,m,m+1))),prec);
      tinv = ginv(t0);
      t1 = gmul(tinv,gcoeff(H,m,m)); t2 = gmul(tinv,gcoeff(H,m,m+1));
      if (DEBUGLEVEL>=4) t12 += timer();
      for (i=m; i<=n; i++)
      {
	t3 = gcoeff(H,i,m); t4 = gcoeff(H,i,m+1);
	if (flreal) coeff(H,i,m) = ladd(gmul(t1,t3),gmul(t2,t4));
	else coeff(H,i,m) = ladd(gmul(gconj(t1),t3),gmul(gconj(t2),t4));
	coeff(H,i,m+1) = lsub(gmul(t1,t4),gmul(t2,t3));
      }
      if (DEBUGLEVEL>=4) t1234 += timer();
    }
    fl = 1;
    for (i=1; i<=n-1; i++)
      if (gexpo(gcoeff(H,i,i))<=EXP) {fl = 0; break;}
    if (fl)
    {
      for (i=m+1; i<=n; i++) redall(i,min(i-1,m+1));
      M = ginv(gsqrt(maxnorml2(),prec));
      if (DEBUGLEVEL>=4) treda += timer();
      if (gexpo(vecmax(gabs(A,prec)))>= -EXP)
      {
	tetpil = avma; return gerepile(av,tetpil,gcopy(M));
      }
    }
    if ((!fl) || gexpo(vecmin(gabs(y,prec)))<= EXP)
    {
      m = vecmaxind(gneg(gabs(y,prec)));
      tetpil = avma; return gerepile(av,tetpil,gcopy((GEN)B[m]));
    }
    if (low_stack(lim, stack_lim(av0,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"pslq");
      gerepileall(av0,4,&y,&H,&A,&B);
    }
    if (DEBUGLEVEL>=4) tfin += timer();
    if (DEBUGLEVEL==3 && (ct%100) == 0)
    {
      printf("time for ct = %ld : %ld\n",ct,timer());
      fflush(stdout);
    }
    if (DEBUGLEVEL>=4 && (ct%100) == 0)
    {
      printf("time [vecmax,t12,loop,reds,fin] = [%ld, %ld, %ld, %ld, %ld]\n",tvmind,t12,t1234,treda,tfin);
      fflush(stdout);
    }
  }
}

/* W de longueur n-1 */

static double
dnorml2(double *W, long row)
{
  const long n = lg(y)-1;
  long i;
  double s = 0.;

  for (i=row; i<n; i++) s += W[i]*W[i];
  return s;
}

/* computes Hbar*Pbar */

static void
dmatmul(long row)
{
  const long n = lg(y)-1;
  long i, j, k;
  double s;

  for (i=row; i<=n; i++)
  {
    for (j=row; j<n; j++)
    {
      s = 0.;
      for (k=row; k<n; k++) s += Hbar[i][k]*Pbar[k][j];
      Wbar[j] = s;
    }
    for (j=row; j<n; j++) Hbar[i][j] = Wbar[j];
  }
}

/* compute n-1 times n-1 matrix Pbar */

static void
dmakep(double *C, long row)
{
  const n = lg(y)-1;
  long i, j;
  double pro, nc;

  nc = sqrt(dnorml2(C,row));
  Wbar[row] = (C[row] < 0) ? C[row] - nc : C[row] + nc;
  for (i=row; i<n; i++) Wbar[i] = C[i];
  pro = -2.0/dnorml2(Wbar,row);
      /* dnorml2(Wbar,row) doit etre egal a 2*nc*(nc+fabs(C[1])) */
  for (j=row; j<n; j++)
  {
    for (i=j+1; i<n; i++)
    {
      Pbar[j][i] = Pbar[i][j] = pro*Wbar[i]*Wbar[j];
    }
    Pbar[j][j] = 1.0 + pro*Wbar[j]*Wbar[j];
  }
}

static void
dLQdec()
{
  const long n = lg(y)-1;
  long row, j;

  for (row=1; row<n; row++)
  {
    dmakep(Hbar[row],row);
    dmatmul(row);
    for (j=row+1; j<n; j++) Hbar[row][j] = 0.0;
  }
}

void
dprintvec(double *V, long m)
{
  long i;
  printf("[");
  for (i=1; i<m; i++) printf("%15.15e, ",V[i]);
  printf("%15.15e]\n",V[m]); fflush(stdout);
}

void
dprintmat(double **M, long r, long c)
{
  long i, j;
  printf("[");
  for (i=1; i<r; i++)
  {
    for (j=1; j<c; j++) printf("%15.15e, ",M[i][j]);
    printf("%15.15e; ",M[i][c]);
  }
  for (j=1; j<c; j++) printf("%15.15e, ",M[r][j]);
  printf("%15.15e]\n",M[r][c]); fflush(stdout);
}

static long
initializedoubles(long prec)
{
  long flit, i, j, n = lg(y)-1;
  GEN ypro;
  gpmem_t av = avma;

  ypro = gdiv(y,vecmax(gabs(y,prec)));
  flit = 1;
  for (i=1; i<=n; i++)
  {
    if (gexpo((GEN)ypro[i])< -0x3ff) {flit = 0; break;}
    else ybar[i] = rtodbl((GEN)ypro[i]);
  }
  avma = av;
  if (flit)
    for (j=1; j<=n; j++)
    {
      for (i=1; i<=n; i++)
      {
	if (i==j) Abar[i][j] = Bbar[i][j] = 1.0;
	else Abar[i][j] = Bbar[i][j] = 0.0;
	if (j<n)
	{
	  GEN pro = gcoeff(H,i,j);
	
	  if ((!gcmp0(pro)) && (labs(gexpo(pro))> 0x3ff)) {flit = 0; break;}
	  else Hbar[i][j] = rtodbl(gcoeff(H,i,j));
	}
      }
      if (!flit) break;
    }
  return flit;
}

void
storeprecdoubles()
{
  long n = lg(y)-1, i, j;

  for (i=1; i<=n; i++)
  {
    for (j=1; j<n; j++)
    {
      Hbarst[i][j] = Hbar[i][j];
      Abarst[i][j] = Abar[i][j];
      Bbarst[i][j] = Bbar[i][j];
    }
    Abarst[i][n] = Abar[i][n]; Bbarst[i][n] = Bbar[i][n];
    ybarst[i] = ybar[i];
  }
}

void
restoreprecdoubles()
{
  long n = lg(y)-1, i, j;

  for (i=1; i<=n; i++)
  {
    for (j=1; j<n; j++)
    {
      Hbar[i][j] = Hbarst[i][j];
      Abar[i][j] = Abarst[i][j];
      Bbar[i][j] = Bbarst[i][j];
    }
    Abar[i][n] = Abarst[i][n]; Bbar[i][n] = Bbarst[i][n];
    ybar[i] = ybarst[i];
  }
}

/* a mettre dans mp.c. Recupere l'exposant d'un double */

#ifdef LONG_IS_64BIT

long
expodb(double x)
{
  union { double f; ulong i; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */

  if (x==0) return -308;
  fi.f = x;
  return ((fi.i & (HIGHBIT-1)) >> mant_len) - exp_mid;
}

#else /* LONG_IS_32BIT */

#if   PARI_DOUBLE_FORMAT == 1
#  define INDEX0 1
#elif PARI_DOUBLE_FORMAT == 0
#  define INDEX0 0
#endif

long
expodb(double x)
{
  union { double f; ulong i[2]; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */
  const int shift = mant_len-32;
  const ulong a = fi.i[INDEX0];

  if (x==0) return -308;
  fi.f = x;
  return ((a & (HIGHBIT-1)) >> shift) - exp_mid;
}

#endif

long
checkentries()
{
  long n = lg(y)-1, i, j;
  double *p1, *p2;

  for (i=1; i<=n; i++)
  {
    p1 = Abar[i]; p2 = Bbar[i];
    for (j=1; j<=n; j++)
      if ((expodb(p1[j]) > 43) || (expodb(p2[j]) > 43)) return 0;
    if (expodb(ybar[i]) < -46) return 0;
  }
  return 1;
}

long
makeABbargen()
{
  long n = lg(y)-1, i, j;
  double *p1, *p2;

  for (i=1; i<=n; i++)
  {
    p1 = Abar[i]; p2 = Bbar[i];
    for (j=1; j<=n; j++)
    {
      if ((expodb(p1[j]) >= 52) || (expodb(p2[j]) >= 52)) return 0;
      coeff(Abargen,i,j) = (long)mpent(dbltor(p1[j]));
      coeff(Bbargen,i,j) = (long)mpent(dbltor(p2[j]));
    }
  }
  return 1;
}

static double
conjd(double x)
{
  return x;
}

static long
checkend(GEN *ptres, long prec)
{
  long fl, i, m, n=lg(y)-1;
  const long EXP = - bit_accuracy(prec) + 2*n;
  GEN M;

  fl = 1;
  for (i=1; i<=n-1; i++) if (gexpo(gcoeff(H,i,i))<=EXP) {fl = 0; break;}
  if (fl)
  {
    M = ginv(gsqrt(maxnorml2(),prec));
    if (gexpo(vecmax(gabs(A,prec)))>= -EXP) {*ptres = M; return 1;}
  }
  if ((!fl) || gexpo(vecmin(gabs(y,prec)))<= EXP)
  {
    m = vecmaxind(gneg(gabs(y,prec)));
    *ptres = (GEN)B[m]; return 1;
  }
  return 0;
}

GEN
pslqtwolevel(GEN x, long prec)
{
  GEN ga,tabga,s,s1,sinv,p1,p2,res,t0,t1,t2,t3,t4,tinv,M;
  long lx = lg(x), tx = typ(x), n = lx-1, k, i, j, m, ct, ctpro, fl, flreal, flit, flilong;
  gpmem_t av = avma, lim = stack_lim(av,1), av0,tetpil;
  long tvmind=0, t12=0, t1234=0, treda=0, tfin=0;
  const long EXP = - bit_accuracy(prec) + 2*n;
  double *tabgabar, gabar, resbar, *respt, tinvbar, t1bar, t2bar, t3bar, t4bar;

  if (! is_vec_t(tx)) err(typeer,"pslq");
  if (n <= 1) return cgetg(1,t_COL);
  if (DEBUGLEVEL>=3) (void)timer();
  if (gexpo(gimag(x)) > EXP)
  {
    return lindep(x,prec);
/*    err(impl,"pslq for complex arguments"); */
    ga = gsqrt(gdeux,prec); flreal = 0;
  }
  else
  {
    x = greal(x); flreal = 1;
    ga = gsqrt(gdiv(stoi(4),stoi(3)),prec);
  }
  x = gmul(x, realun(prec));
  settyp(x,t_VEC);
  tabga = cgetg(n,t_VEC); tabga[1] = (long)ga;
  for (i=2; i<n; i++) tabga[i] = lmul((GEN)tabga[i-1],ga);
  A = idmat(n); B = idmat(n); Abargen = idmat(n); Bbargen = idmat(n);
  s1 = cgetg(lx,t_VEC); s = cgetg(lx,t_VEC);
  s1[n] = lnorm((GEN)x[n]); s[n] = (long)gabs((GEN)x[n],prec);
  for (k=n-1; k>=1; k--)
  {
    s1[k] = ladd((GEN)s1[k+1],gnorm((GEN)x[k]));
    s[k] = (long)gsqrt((GEN)s1[k],prec);
  }
  sinv = ginv((GEN)s[1]);
  y = gmul(sinv,x);
  s = gmul(sinv,s);
  H = cgetg(n,t_MAT);
  for (j=1; j<n; j++)
  {
    p1 = cgetg(lx,t_COL); H[j] = (long)p1;
    for (i=1; i<j; i++) p1[i] = zero;
    p1[j] = ldiv((GEN)s[j+1],(GEN)s[j]);
    p2 = gneg(gdiv((GEN)y[j],gmul((GEN)s[j],(GEN)s[j+1])));
    for (i=j+1; i<=n; i++) p1[i] = lmul(gconj((GEN)y[i]),p2);
  }
  for (i=2; i<=n; i++) redall(i,i-1);
  av0 = avma; ct = 0;
  if (DEBUGLEVEL>=3) printf("Initialization time = %ld\n",timer());

  tabgabar = (double*)malloc((n+1)*sizeof(double));
  gabar=gtodouble(ga);
  tabgabar[1] = gabar;
  for (i=2; i<n; i++) tabgabar[i] = tabgabar[i-1]*gabar;
  ybar = (double*)malloc((n+1)*sizeof(double));
  Hbar = (double**)malloc((n+1)*sizeof(double*));
  for (i=1; i<=n; i++) Hbar[i] = (double*)malloc(n*sizeof(double));
  Abar = (double**)malloc((n+1)*sizeof(double*));
  for (i=1; i<=n; i++) Abar[i] = (double*)malloc((n+1)*sizeof(double));
  Bbar = (double**)malloc((n+1)*sizeof(double*));
  for (i=1; i<=n; i++) Bbar[i] = (double*)malloc((n+1)*sizeof(double));
  ybarst = (double*)malloc((n+1)*sizeof(double));
  Hbarst = (double**)malloc((n+1)*sizeof(double*));
  for (i=1; i<=n; i++) Hbarst[i] = (double*)malloc(n*sizeof(double));
  Abarst = (double**)malloc((n+1)*sizeof(double*));
  for (i=1; i<=n; i++) Abarst[i] = (double*)malloc((n+1)*sizeof(double));
  Bbarst = (double**)malloc((n+1)*sizeof(double*));
  for (i=1; i<=n; i++) Bbarst[i] = (double*)malloc((n+1)*sizeof(double));
  Wbar = (double*)malloc((n+1)*sizeof(double));
  Pbar = (double**)malloc(n*sizeof(double*));
  for (i=1; i<n; i++) Pbar[i] = (double*)malloc((n+1)*sizeof(double));
startagain:
  flit = initializedoubles(prec);
  ctpro = 0;
  storeprecdoubles();
  if (flit) dLQdec();
  for (;;)
  {
    ct++;
    if (flit)
    {
      ctpro++;
      for (i=1; i<n; i++) Wbar[i] = tabgabar[i]*fabs(Hbar[i][i]);
      m = vecmaxindbar(Wbar,n-1);
      resbar = ybar[m]; ybar[m] = ybar[m+1]; ybar[m+1] = resbar;
      respt = Abar[m]; Abar[m] = Abar[m+1]; Abar[m+1] = respt;
      respt = Hbar[m]; Hbar[m] = Hbar[m+1]; Hbar[m+1] = respt;
      for (j=1; j<=n; j++)
      {
	resbar = Bbar[j][m]; Bbar[j][m] = Bbar[j][m+1]; Bbar[j][m+1] = resbar;
      }
      if (m <= n-2)
      {
	tinvbar = 1.0/sqrt(sqrd(Hbar[m][m]) + sqrd(Hbar[m][m+1]));
	t1bar = tinvbar*Hbar[m][m]; t2bar = tinvbar*Hbar[m][m+1];
	if (DEBUGLEVEL>=4) t12 += timer();
	for (i=m; i<=n; i++)
	{
	  t3bar = Hbar[i][m]; t4bar = Hbar[i][m+1];
	  if (flreal) Hbar[i][m] = t1bar*t3bar + t2bar*t4bar;
	  else Hbar[i][m] = conjd(t1bar)*t3bar + conjd(t2bar)*t4bar;
	  Hbar[i][m+1] = t1bar*t4bar - t2bar*t3bar;
	}
	if (DEBUGLEVEL>=4) t1234 += timer();
      }
      flit = checkentries();

      if (!flit)
      {
	flilong = makeABbargen();
	if (flilong)
	{
	  y = gmul(y,Bbargen);
	  B = gmul(B,Bbargen);
	  A = gmul(Abargen,A);
	  H = gmul(Abargen,H);
	  if (checkend(&res,prec)) goto endpslqtwo;
	  else goto startagain;
	}
	else
	{
	  if (ctpro>1)
	  {
	    restoreprecdoubles();
	    flilong = makeABbargen();
	    if (!flilong) err(talker,"bug in pslqtwolevel");
	    y = gmul(y,Bbargen);
	    B = gmul(B,Bbargen);
	    A = gmul(Abargen,A);
	    H = gmul(Abargen,H);
	    if (checkend(&res,prec)) goto endpslqtwo;
	    else goto startagain;
	  }
	  else goto dogen;
	}
      }
      else
      {
	storeprecdoubles();
	for (i=m+1; i<=n; i++) redallbar(i,min(i-1,m+1));
      }
    }
    else
    {
dogen:
      p1 = cgetg(n,t_VEC);
      for (i=1; i<n; i++) p1[i] = lmul((GEN)tabga[i],gabs(gcoeff(H,i,i),prec));
      m = vecmaxind(p1);
      if (DEBUGLEVEL>=4) tvmind += timer();
      res = (GEN)y[m]; y[m] = y[m+1]; y[m+1] = (long)res;
      for (j=1; j<=n; j++)
      {
	res = gcoeff(A,m,j); coeff(A,m,j) = coeff(A,m+1,j);
	coeff(A,m+1,j)=(long)res;
      }
      for (j=1; j<n; j++)
      {
	res = gcoeff(H,m,j); coeff(H,m,j) = coeff(H,m+1,j);
	coeff(H,m+1,j)=(long)res;
      }
      res = (GEN)B[m]; B[m] = B[m+1]; B[m+1] = (long)res;
      if (m <= n-2)
      {
	t0 = gsqrt(gadd(gnorm(gcoeff(H,m,m)),gnorm(gcoeff(H,m,m+1))),prec);
	tinv = ginv(t0);
	t1 = gmul(tinv,gcoeff(H,m,m)); t2 = gmul(tinv,gcoeff(H,m,m+1));
	if (DEBUGLEVEL>=4) t12 += timer();
	for (i=m; i<=n; i++)
        {
	  t3 = gcoeff(H,i,m); t4 = gcoeff(H,i,m+1);
	  if (flreal) coeff(H,i,m) = ladd(gmul(t1,t3),gmul(t2,t4));
	  else coeff(H,i,m) = ladd(gmul(gconj(t1),t3),gmul(gconj(t2),t4));
	  coeff(H,i,m+1) = lsub(gmul(t1,t4),gmul(t2,t3));
	}
	if (DEBUGLEVEL>=4) t1234 += timer();
      }
      fl = 1;
      for (i=1; i<=n-1; i++)
	if (gexpo(gcoeff(H,i,i))<=EXP) {fl = 0; break;}
      if (fl)
      {
	for (i=m+1; i<=n; i++) redall(i,min(i-1,m+1));
	M = ginv(gsqrt(maxnorml2(),prec));
	if (DEBUGLEVEL>=4) treda += timer();
	if (gexpo(vecmax(gabs(A,prec)))>= -EXP)
        {
	  res = M; goto endpslqtwo;
	}
      }
      if ((!fl) || gexpo(vecmin(gabs(y,prec)))<= EXP)
      {
	m = vecmaxind(gneg(gabs(y,prec)));
	res = (GEN)B[m]; goto endpslqtwo;
      }
    }
    if (low_stack(lim, stack_lim(av0,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"pslq");
      gerepileall(av0,4,&y,&H,&A,&B);
    }
    if (DEBUGLEVEL>=4) tfin += timer();
    if (DEBUGLEVEL==3 && (ct%100) == 0)
    {
      printf("time for ct = %ld : %ld\n",ct,timer());
      fflush(stdout);
    }
    if (DEBUGLEVEL>=4 && (ct%100) == 0)
    {
      printf("time [vecmax,t12,loop,reds,fin] = [%ld, %ld, %ld, %ld, %ld]\n",tvmind,t12,t1234,treda,tfin);
      fflush(stdout);
    }
  }
endpslqtwo:
  for (i=1; i<=n; i++)
  {
    free(Hbar[i]); free(Abar[i]); free(Bbar[i]);
    if (i<n) free(Pbar[i]);
    free(Bbarst[i]); free(Abarst[i]); free(Hbarst[i]);
  }
  free(tabgabar); free(ybar); free(Hbar); free(Abar); free(Bbar);
  free(ybarst); free(Hbarst); free(Abarst); free(Bbarst);
  tetpil = avma; return gerepile(av,tetpil,gcopy(res));
}

/* x is a vector of elts of a p-adic field */
GEN
plindep(GEN x)
{
  long i, j, prec = VERYBIGINT, lx = lg(x)-1, ly, v;
  gpmem_t av = avma;
  GEN p = NULL, pn,p1,m,a;

  if (lx < 2) return cgetg(1,t_VEC);
  for (i=1; i<=lx; i++)
  {
    p1 = (GEN)x[i];
    if (typ(p1) != t_PADIC) continue;

    j = precp(p1); if (j < prec) prec = j;
    if (!p) p = (GEN)p1[2];
    else if (!egalii(p, (GEN)p1[2]))
      err(talker,"inconsistent primes in plindep");
  }
  if (!p) err(talker,"not a p-adic vector in plindep");
  v = ggval(x,p); pn = gpowgs(p,prec);
  if (v != 0) x = gmul(x, gpowgs(p, -v));
  x = lift_intern(gmul(x, gmodulcp(gun, pn)));

  ly = 2*lx - 1;
  m = cgetg(ly+1,t_MAT);
  for (j=1; j<=ly; j++)
  {
    p1 = cgetg(lx+1, t_COL); m[j] = (long)p1;
    for (i=1; i<=lx; i++) p1[i] = zero;
  }
  a = negi((GEN)x[1]);
  for (i=1; i<lx; i++)
  {
    coeff(m,1+i,i) = (long)a;
    coeff(m,1  ,i) = x[i+1];
  }
  for (i=1; i<=lx; i++) coeff(m,i,lx-1+i) = (long)pn;
  p1 = lllint(m);
  return gerepileupto(av, gmul(m, (GEN)p1[1]));
}

GEN
algdep0(GEN x, long n, long bit, long prec)
{
  long tx=typ(x), i, k;
  gpmem_t av;
  GEN y,p1;

  if (! is_scalar_t(tx)) err(typeer,"algdep0");
  if (tx==t_POLMOD) { y=forcecopy((GEN)x[1]); setvarn(y,0); return y; }
  if (gcmp0(x)) return gzero;
  if (!n) return gun;

  av=avma; p1=cgetg(n+2,t_COL);
  p1[1] = un;
  p1[2] = (long)x; /* n >= 1 */
  for (i=3; i<=n+1; i++) p1[i]=lmul((GEN)p1[i-1],x);
  if (typ(x) == t_PADIC)
    p1 = plindep(p1);
  else
  {
    switch(bit)
    {
      case 0: p1 = pslq(p1,prec); break;
      case -1: p1 = lindep(p1,prec); break;
      case -2: p1 = deplin(p1); break;
      default: p1 = lindep2(p1,bit);
    }
  }
  if ((!bit) && (typ(p1) == t_REAL))
  {
    y = gcopy(p1); return gerepileupto(av,y);
  }
  if (lg(p1) < 2)
    err(talker,"higher degree than expected in algdep");
  y=cgetg(n+3,t_POL);
  y[1] = evalsigne(1) | evalvarn(0);
  k=1; while (gcmp0((GEN)p1[k])) k++;
  for (i=0; i<=n+1-k; i++) y[i+2] = p1[k+i];
  (void)normalizepol_i(y, n+4-k);
  y = (gsigne(leading_term(y)) > 0)? gcopy(y): gneg(y);
  return gerepileupto(av,y);
}

GEN
algdep2(GEN x, long n, long bit)
{
  return algdep0(x,n,bit,0);
}

GEN
algdep(GEN x, long n, long prec)
{
  return algdep0(x,n,0,prec);
}

/********************************************************************/
/**                                                                **/
/**                   INTEGRAL KERNEL (LLL REDUCED)                **/
/**                                                                **/
/********************************************************************/

GEN
matkerint0(GEN x, long flag)
{
  switch(flag)
  {
    case 0: return kerint(x);
    case 1: return kerint1(x);
    default: err(flagerr,"matkerint");
  }
  return NULL; /* not reached */
}

GEN
kerint1(GEN x)
{
  gpmem_t av=avma, tetpil;
  GEN p1,p2;

  p1=matrixqz3(ker(x)); p2=lllint(p1); tetpil=avma;
  return gerepile(av,tetpil,gmul(p1,p2));
}

GEN
kerint(GEN x)
{
  gpmem_t av = avma;
  GEN fl, junk, h = lllint_i(x, 0, 0, &junk, &fl, NULL);
  if (h) h = lll_finish(h,fl, lll_KER);
  else   h = lll_trivial(x, lll_KER);
  if (lg(h)==1) { avma = av; return cgetg(1, t_MAT); }
  return gerepileupto(av, gmul(h, lllint(h)));
}

/********************************************************************/
/**                                                                **/
/**                        POLRED & CO.                            **/
/**                                                                **/
/********************************************************************/
/* remove duplicate polynomials in y, updating a (same indexes), in place */
static long
remove_duplicates(GEN y, GEN a)
{
  long k, i, nv = lg(y);
  gpmem_t av = avma;
  GEN z;

  if (nv < 2) return nv;
  z = new_chunk(3);
  z[1] = (long)y;
  z[2] = (long)a; (void)sort_factor(z, gcmp);
  for  (k=1, i=2; i<nv; i++)
    if (!gegal((GEN)y[i], (GEN)y[k]))
    {
      k++;
      a[k] = a[i];
      y[k] = y[i];
    }
  nv = k+1; setlg(a,nv); setlg(y,nv);
  avma = av; return nv;
}

/* in place; make sure second non-zero coeff is negative (choose x or -x) */
int
canon_pol(GEN z)
{
  long i,s;

  for (i=lgef(z)-2; i>=2; i-=2)
  {
    s = signe(z[i]);
    if (s > 0)
    {
      for (; i>=2; i-=2) z[i]=lnegi((GEN)z[i]);
      return -1;
    }
    if (s) return 1;
  }
  return 0;
}

static GEN
pols_for_polred(GEN x, GEN a, GEN *pta,
		int (*check)(void *, GEN), void *arg)
{
  long i, v = varn(x), n = lg(a);
  GEN ch,d,y;

  y=cgetg(n,t_VEC);
  for (i=1; i<n; i++)
  {
    if (DEBUGLEVEL > 2) { fprintferr("i = %ld\n",i); flusherr(); }
    ch = QX_caract(x, (GEN)a[i], v);
    d = modulargcd(derivpol(ch), ch);
    if (degpol(d)) ch = gdivexact(ch,d);

    if (canon_pol(ch) < 0 && pta) a[i] = (long)gneg_i((GEN)a[i]);
    if (DEBUGLEVEL > 3) outerr(ch);
    if (check && check(arg, ch)) return ch;
    y[i] = (long)ch;
  }
  if (check) return NULL; /* no suitable polynomial found */
  (void)remove_duplicates(y,a);
  if (pta) *pta = a;
  return y;
}

/* x can be a polynomial, but also an nf, or [pol, integer basis]
 * if check != NULL, return the first polynomial pol found such that
 * check(arg, pol) != 0; return NULL if there are no such pol */
static GEN
allpolred0(GEN x, GEN *pta, long code, long prec,
	   int (*check)(void *,GEN), void *arg)
{
  GEN y, base = NULL, nf = NULL;
  gpmem_t av = avma;

  if (typ(x) == t_POL)
  {
    GEN p1;
    if (!signe(x)) return gcopy(x);
    check_pol_int(x,"polred");
    if (!gcmp1(leading_term(x)))
      err(impl,"allpolred for nonmonic polynomials");
    base = allbase4(x,code,&p1,NULL); /* p1 is junk */
  }
  else
  {
    long i = lg(x);
    if (typ(x) == t_VEC && i==3 && typ(x[1])==t_POL)
    { /* polynomial + integer basis */
      base = (GEN)x[2]; x = (GEN)x[1];
    }
    else
    {
      nf = checknf(x);
      base = (GEN)nf[7]; x = (GEN)nf[1];
    }
  }
  if (!nf) base = gmul(base, LLL_nfbasis(x,NULL,base,prec));
  y = pols_for_polred(x, base, pta, check, arg);
  if (check)
  {
    if (y) return gerepileupto(av, y);
    avma = av; return NULL;
  }

  if (pta) gerepileall(av,2,&y,pta); else y = gerepileupto(av,y);
  return y;
}

static GEN
allpolred(GEN x, GEN *pta, long code, long prec)
{
  return allpolred0(x,pta,code,prec,NULL,NULL);
}

GEN
polred0(GEN x,long flag, GEN p, long prec)
{
  GEN y;
  long smll = (flag & 1);

  if (p && !gcmp0(p)) smll=(long) p; /* factored polred */
  if (flag & 2) /* polred2 */
  {
    y=cgetg(3,t_MAT);
    y[2]=(long)allpolred(x,(GEN*)(y+1),smll,prec);
    return y;
  }
  return allpolred(x,NULL,smll,prec);
}

GEN
ordred(GEN x, long prec)
{
  GEN base,y;
  long n=degpol(x), i, v = varn(x);
  gpmem_t av=avma;

  if (typ(x) != t_POL) err(typeer,"ordred");
  if (!signe(x)) return gcopy(x);
  if (!gcmp1((GEN)x[n+2])) err(impl,"ordred for nonmonic polynomials");

  base = cgetg(n+1,t_VEC); /* power basis */
  for (i=1; i<=n; i++)
    base[i] = lpowgs(polx[v],i-1);
  y = cgetg(3,t_VEC);
  y[1] = (long)x;
  y[2] = (long)base;
  return gerepileupto(av, allpolred(y,NULL,0,prec));
}

GEN
sum(GEN v, long a, long b)
{
  GEN p;
  long i;
  if (a > b) return gzero;
  p = (GEN)v[a];
  for (i=a+1; i<=b; i++) p = gadd(p, (GEN)v[i]);
  return p;
}

GEN
T2_from_embed_norm(GEN x, long r1)
{
  GEN p = sum(x, 1, r1);
  GEN q = sum(x, r1+1, lg(x)-1);
  if (q != gzero) p = gadd(p, gmul2n(q,1));
  return p;
}

GEN
T2_from_embed(GEN x, long r1)
{
  return T2_from_embed_norm(gnorm(x), r1);
}

/* return T2 norm of the polynomial defining nf */
static GEN
get_Bnf(GEN nf)
{
  return T2_from_embed((GEN)nf[6], nf_get_r1(nf));
}

typedef struct {
  long r1;
  GEN ZKembed; /* embeddings of LLL-reduced Zk basis */
  GEN ZKLLL; /* LLL reduced Zk basis (in M_n(Z)) */
} CG_data;

/* characteristic pol of x */
static GEN
get_polchar(CG_data *d, GEN x)
{
  GEN g = gmul(d->ZKembed,x);
  long e;
  g = grndtoi(roots_to_pol_r1r2(g, d->r1, 0), &e);
  if (e > -5) err(precer, "get_polchar");
  return g;
}

/* return a defining polynomial for Q(x) */
static GEN
get_polmin(CG_data *d, GEN x)
{
  GEN g = get_polchar(d,x);
  GEN h = modulargcd(g,derivpol(g));
  if (degpol(h)) g = gdivexact(g,h);
  return g;
}

/* does x generate the correct field ? */
static GEN
chk_gen(void *data, GEN x)
{
  gpmem_t av = avma;
  GEN g = get_polchar((CG_data*)data,x);
  GEN h = modulargcd(g,derivpol(g));
  if (degpol(h)) { avma = av; return NULL; }
  if (DEBUGLEVEL>3) fprintferr("  generator: %Z\n",g);
  return g;
}

/* mat = base change matrix, gram = LLL-reduced T2 matrix */
static GEN
chk_gen_init(FP_chk_fun *chk, GEN nf, GEN gram, GEN mat, long *ptprec)
{
  GEN P,bound,prev,x,B, M = gmael(nf,5,1);
  long N = lg(nf[7]), n = N-1,i,prec,prec2;
  int skipfirst = 0;
  CG_data *d = (CG_data*)new_chunk(sizeof(CG_data));

  d->r1 = itos(gmael(nf,2,1));
  d->ZKembed = gmul(M, mat);
  d->ZKLLL   = gmul((GEN)nf[7],mat);
  chk->data = (void*)d;

  bound = get_Bnf(nf); prev = NULL;
  x = zerocol(N-1);
  for (i=1; i<N; i++)
  {
    B = gcoeff(gram,i,i);
    if (gcmp(B,bound) >= 0 && skipfirst != i-1) continue;

    x[i] = un; P = get_polmin(d,x);
    x[i] = zero;
    if (degpol(P) == n)
    {
      if (gcmp(B,bound) < 0) bound = B ;
      continue;
    }

    if (DEBUGLEVEL>2) fprintferr("chk_gen_init: subfield %Z\n",P);
    if (skipfirst == i-1)
    {
      if (prev && !gegal(prev,P))
      {
        if (degpol(prev) * degpol(P) > 32) continue; /* too expensive */
        P = (GEN)compositum(prev,P)[1];
        if (degpol(P) == n) continue;
        if (DEBUGLEVEL>2 && lgef(P)>lgef(prev))
          fprintferr("chk_gen_init: subfield %Z\n",P);
      }
      skipfirst++; prev = P;
    }
  }
  /* x_1,...,x_skipfirst generate a strict subfield [unless n=skipfirst=1] */
  chk->skipfirst = skipfirst;
  if (DEBUGLEVEL>2) fprintferr("chk_gen_init: skipfirst = %ld\n",skipfirst);

  /* should be gexpo( [max_k C^n_k (bound/k) ^ k] ^ (1/2) ) */
  prec2 = (1 + (((gexpo(bound)*n)/2) >> TWOPOTBITS_IN_LONG));
  if (prec2 < 0) prec2 = 0;
  prec = 3 + prec2;
  prec2= nfgetprec(nf);
  if (DEBUGLEVEL)
    fprintferr("chk_gen_init: estimated prec = %ld (initially %ld)\n",
                prec, prec2);
  if (prec > prec2) return NULL;
  if (prec < prec2) d->ZKembed = gprec_w(d->ZKembed, prec);
  *ptprec = prec; return bound;
}

static GEN
chk_gen_post(void *data, GEN res)
{
  GEN basis = ((CG_data*)data)->ZKLLL;
  GEN p1 = (GEN)res[2];
  long i, l = lg(p1);
  for (i=1; i<l; i++) p1[i] = lmul(basis, (GEN)p1[i]);
  return res;
}

/* no garbage collecting, done in polredabs0 */
static GEN
findmindisc(GEN nf, GEN y, GEN a, GEN phimax, long flun)
{
  long i,k, c = lg(y);
  GEN v,dmin,z,beta,discs = cgetg(c,t_VEC);

  for (i=1; i<c; i++) discs[i] = labsi(ZX_disc((GEN)y[i]));
  v = sindexsort(discs);
  k = v[1];
  dmin = (GEN)discs[k];
  z    = (GEN)y[k];
  beta = (GEN)a[k];
  for (i=2; i<c; i++)
  {
    k = v[i];
    if (!egalii((GEN)discs[k], dmin)) break;
    if (gpolcomp((GEN)y[k],z) < 0) { z = (GEN)y[k]; beta = (GEN)a[k]; }
  }
  if (flun & nf_RAW)
  {
    y=cgetg(3,t_VEC);
    y[1]=lcopy(z);
    y[2]=lcopy(beta);
  }
  else if (phimax)
  {
    y=cgetg(3,t_VEC);
    y[1]=lcopy(z);
    beta=polymodrecip(gmodulcp(beta,(GEN)nf[1]));
    y[2]=(long)poleval(phimax,beta);
  }
  else y = gcopy(z);
  return y;
}

/* no garbage collecting, done in polredabs0 */
static GEN
storeallpols(GEN nf, GEN z, GEN a, GEN phimax, long flun)
{
  GEN p1,y,beta;

  if (flun & nf_RAW)
  {
    long i, c = lg(z);
    y=cgetg(c,t_VEC);
    for (i=1; i<c; i++)
    {
      p1=cgetg(3,t_VEC); y[i]=(long)p1;
      p1[1]=lcopy((GEN)z[i]);
      p1[2]=lcopy((GEN)a[i]);
    }
  }
  else if (phimax)
  {
    long i, c = lg(z);
    beta = new_chunk(c);
    for (i=1; i<c; i++)
      beta[i] = (long)polymodrecip(gmodulcp((GEN)a[i],(GEN)nf[1]));

    y=cgetg(c,t_VEC);
    for (i=1; i<c; i++)
    {
      p1=cgetg(3,t_VEC); y[i]=(long)p1;
      p1[1]=lcopy((GEN)z[i]);
      p1[2]=(long)poleval(phimax,(GEN)beta[i]);
    }
  }
  else y = gcopy(z);
  return y;
}

GEN
polredabs0(GEN x, long flun, long prec)
{
  long i, nv;
  gpmem_t av = avma;
  GEN nf,v,y,a,phimax;
  GEN (*storepols)(GEN, GEN, GEN, GEN, long);
  FP_chk_fun *chk;

  chk = (FP_chk_fun*)new_chunk(sizeof(FP_chk_fun));
  chk->f         = &chk_gen;
  chk->f_init    = &chk_gen_init;
  chk->f_post    = &chk_gen_post;

  if ((ulong)flun >= 16) err(flagerr,"polredabs");
  nf = initalgall0(x,nf_SMALL|nf_REGULAR,prec);
  if (lg(nf) == 3)
  {
    phimax = lift_to_pol((GEN)nf[2]);
    nf = (GEN)nf[1];
  }
  else
    phimax = (flun & nf_ORIG)? polx[0]: (GEN)NULL;
  prec = nfgetprec(nf);
  x = (GEN)nf[1];

  if (degpol(x) == 1)
  {
    y = _vec(polx[varn(x)]);
    a = _vec(gsub((GEN)y[1], (GEN)x[2]));
  }
  else
  {
    for (i=1; ; i++)
    {
      v = fincke_pohst(nf,NULL,5000,3,prec, chk);
      if (v) break;
      if (i==MAXITERPOL) err(accurer,"polredabs0");
      prec = (prec<<1)-2; nf = nfnewprec(nf,prec);
      if (DEBUGLEVEL) err(warnprec,"polredabs0",prec);
    }
    a = (GEN)v[2];
    y = (GEN)v[1];
  }
  nv = lg(a);
  for (i=1; i<nv; i++)
    if (canon_pol((GEN)y[i]) < 0) a[i] = (long)gneg_i((GEN)a[i]);
  nv = remove_duplicates(y,a);

  if (DEBUGLEVEL)
    { fprintferr("%ld minimal vectors found.\n",nv-1); flusherr(); }
  if (nv >= 10000) flun &= (~nf_ALL); /* should not happen */
  storepols = (flun & nf_ALL)? storeallpols: findmindisc;

  if (DEBUGLEVEL) fprintferr("\n");
  if (nv==1)
  {
    y = _vec(x);
    a = _vec(polx[varn(x)]);
  }
  if (varn(y[1]) != varn(x))
  {
    long vx = varn(x);
    for (i=1; i<nv; i++) setvarn(y[i], vx);
  }
  return gerepileupto(av, storepols(nf,y,a,phimax,flun));
}

GEN
polredabsall(GEN x, long flun, long prec)
{
  return polredabs0(x, flun | nf_ALL, prec);
}

GEN
polredabs(GEN x, long prec)
{
  return polredabs0(x,nf_REGULAR,prec);
}

GEN
polredabs2(GEN x, long prec)
{
  return polredabs0(x,nf_ORIG,prec);
}

GEN
polredabsnored(GEN x, long prec)
{
  return polredabs0(x,nf_NORED,prec);
}

GEN
polred(GEN x, long prec)
{
  return allpolred(x,NULL,0,prec);
}

GEN
polredfirstpol(GEN x, long prec, int (*check)(void *,GEN), void *arg)
{
  return allpolred0(x,NULL,0,prec,check,arg);
}

GEN
smallpolred(GEN x, long prec)
{
  return allpolred(x,NULL,1,prec);
}

GEN
factoredpolred(GEN x, GEN p, long prec)
{
  return allpolred(x,NULL,(long)p,prec);
}

GEN
polred2(GEN x, long prec)
{
  GEN y=cgetg(3,t_MAT);

  y[2]= (long) allpolred(x,(GEN*)(y+1),0,prec);
  return y;
}

GEN
smallpolred2(GEN x, long prec)
{
  GEN y=cgetg(3,t_MAT);

  y[2]= (long) allpolred(x,(GEN*)(y+1),1,prec);
  return y;
}

GEN
factoredpolred2(GEN x, GEN p, long prec)
{
  GEN y=cgetg(3,t_MAT);

  y[2]= (long) allpolred(x,(GEN*)(y+1),(long)p,prec);
  return y;
}

/********************************************************************/
/**                                                                **/
/**                              MINIM                             **/
/**                                                                **/
/********************************************************************/
int addcolumntomatrix(GEN V,GEN INVP,GEN L);

/* x is a non-empty matrix, y is a compatible VECSMALL (dimension > 0). */
GEN
gmul_mat_smallvec(GEN x, GEN y)
{
  long c = lg(x), l = lg(x[1]), i, j;
  gpmem_t av;
  GEN z=cgetg(l,t_COL), s;

  for (i=1; i<l; i++)
  {
    av = avma; s = gmulgs(gcoeff(x,i,1),y[1]);
    for (j=2; j<c; j++)
       if (y[j]) s = gadd(s, gmulgs(gcoeff(x,i,j),y[j]));
    z[i] = lpileupto(av,s);
  }
  return z;
}

/* same, x integral */
GEN
gmul_mati_smallvec(GEN x, GEN y)
{
  long c = lg(x), l = lg(x[1]), i, j;
  gpmem_t av;
  GEN z=cgetg(l,t_COL), s;

  for (i=1; i<l; i++)
  {
    av = avma; s = mulis(gcoeff(x,i,1),y[1]);
    for (j=2; j<c; j++)
      if (y[j]) s = addii(s, mulis(gcoeff(x,i,j),y[j]));
    z[i]=(long)gerepileuptoint(av,s);
  }
  return z;
}

void
minim_alloc(long n, double ***q, GEN *x, double **y,  double **z, double **v)
{
  long i, s;
  double **Q;

  *x = cgetg(n, t_VECSMALL);
  *q = (double**) new_chunk(n);

  /* correct alignment for the following */
  avma -= avma % sizeof(double);
  if (avma<bot) err(errpile);

  s = (n * sizeof(double))/sizeof(long);
  *y = (double*) new_chunk(s);
  *z = (double*) new_chunk(s);
  *v = (double*) new_chunk(s); Q = *q;
  for (i=1; i<n; i++) Q[i] = (double*) new_chunk(s);
}

/* Minimal vectors for the integral definite quadratic form: a.
 * Result u:
 *   u[1]= Number of vectors of square norm <= BORNE
 *   u[2]= maximum norm found
 *   u[3]= list of vectors found (at most STOCKMAX)
 *
 *  If BORNE = gzero: Minimal non-zero vectors.
 *  flag = min_ALL,   as above
 *  flag = min_FIRST, exits when first suitable vector is found.
 *  flag = min_PERF,  only compute rank of the family of v.v~ (v min.)
 */
static GEN
minim00(GEN a, GEN BORNE, GEN STOCKMAX, long flag)
{
  GEN x,res,p1,u,r,liste,gnorme,invp,V, *gptr[2];
  long n = lg(a), i, j, k, s, maxrank;
  gpmem_t av0 = avma, av1, av, tetpil, lim;
  double p,maxnorm,BOUND,*v,*y,*z,**q, eps = 0.000001;

  maxrank = 0; res = V = invp = NULL; /* gcc -Wall */
  switch(flag)
  {
    case min_FIRST:
      if (gcmp0(BORNE)) err(talker,"bound = 0 in minim2");
      res = cgetg(3,t_VEC); break;
    case min_ALL: res = cgetg(4,t_VEC); break;
    case min_PERF: break;
    default: err(talker, "incorrect flag in minim00");
  }
  if (n == 1)
  {
    switch(flag)
    {
      case min_FIRST: avma=av0; return cgetg(1,t_VEC);
      case min_PERF:  avma=av0; return gzero;
    }
    res[1]=res[2]=zero;
    res[3]=lgetg(1,t_MAT); return res;
  }

  av = avma;
  minim_alloc(n, &q, &x, &y, &z, &v);
  av1 = avma;

  u = lllgramint(a);
  if (lg(u) != n)
    err(talker,"not a definite form in minim00");
  a = qf_base_change(a,u,1);

  n--;
  a = gmul(a, realun(DEFAULTPREC)); r = sqred1(a);
  if (DEBUGLEVEL>4) { fprintferr("minim: r = "); outerr(r); }
  for (j=1; j<=n; j++)
  {
    v[j] = rtodbl(gcoeff(r,j,j));
    for (i=1; i<j; i++) q[i][j] = rtodbl(gcoeff(r,i,j));
  }

  if (flag==min_PERF || gcmp0(BORNE))
  {
    double c, b = rtodbl(gcoeff(a,1,1));

    for (i=2; i<=n; i++)
      { c=rtodbl(gcoeff(a,i,i)); if (c<b) b=c; }
    BOUND = b+eps;
    BORNE = ground(dbltor(BOUND));
    maxnorm = -1.; /* don't update maxnorm */
  }
  else
  {
    BORNE = gfloor(BORNE);
    BOUND = gtodouble(BORNE)+eps;
    maxnorm = 0.;
  }

  switch(flag)
  {
    case min_ALL:
      maxrank=itos(STOCKMAX);
      liste = new_chunk(1+maxrank);
      break;
    case min_PERF:
      BORNE = gerepileupto(av1,BORNE);
      maxrank = (n*(n+1))>>1;
      liste = cgetg(1+maxrank, t_VECSMALL);
      V     = cgetg(1+maxrank, t_VECSMALL);
      for (i=1; i<=maxrank; i++) liste[i]=0;
  }

  s=0; av1=avma; lim = stack_lim(av1,1);
  k = n; y[n] = z[n] = 0;
  x[n] = (long) sqrt(BOUND/v[n]);
  if (flag == min_PERF) invp = idmat(maxrank);
  for(;;x[1]--)
  {
    do
    {
      if (k>1)
      {
        long l = k-1;
	z[l]=0;
	for (j=k; j<=n; j++) z[l] += q[l][j]*x[j];
	p = x[k]+z[k];
	y[l] = y[k] + p*p*v[k];
	x[l] = (long) floor(sqrt((BOUND-y[l])/v[l])-z[l]);
        k = l;
      }
      for(;;)
      {
	p = x[k]+z[k];
	if (y[k] + p*p*v[k] <= BOUND) break;
	k++; x[k]--;
      }
    }
    while (k>1);
    if (! x[1] && y[1]<=eps) break;
    p = x[1]+z[1]; p = y[1] + p*p*v[1]; /* norm(x) */
    if (maxnorm >= 0)
    {
      if (flag == min_FIRST)
      {
        gnorme = dbltor(p);
        tetpil=avma; gnorme = ground(gnorme); r = gmul_mati_smallvec(u,x);
        gptr[0]=&gnorme; gptr[1]=&r; gerepilemanysp(av,tetpil,gptr,2);
        res[1]=(long)gnorme;
        res[2]=(long)r; return res;
      }
      if (p > maxnorm) maxnorm = p;
    }
    else
    {
      gpmem_t av2 = avma;
      gnorme = ground(dbltor(p));
      if (gcmp(gnorme,BORNE) >= 0) avma = av2;
      else
      {
        BOUND=gtodouble(gnorme)+eps; s=0;
        affii(gnorme,BORNE); avma=av1;
        if (flag == min_PERF) invp = idmat(maxrank);
      }
    }
    s++;

    switch(flag)
    {
      case min_ALL:
        if (s<=maxrank)
        {
          p1 = new_chunk(n+1); liste[s] = (long) p1;
          for (i=1; i<=n; i++) p1[i] = x[i];
        }
        break;

      case min_PERF:
      {
        long I=1;
        gpmem_t av2=avma;

        for (i=1; i<=n; i++)
          for (j=i; j<=n; j++,I++) V[I] = x[i]*x[j];
        if (! addcolumntomatrix(V,invp,liste))
        {
          if (DEBUGLEVEL>1) { fprintferr("."); flusherr(); }
          s--; avma=av2; continue;
        }

        if (DEBUGLEVEL>1) { fprintferr("*"); flusherr(); }
        if (s == maxrank)
        {
          if (DEBUGLEVEL>1) { fprintferr("\n"); flusherr(); }
          avma=av0; return stoi(s);
        }

        if (low_stack(lim, stack_lim(av1,1)))
        {
          if(DEBUGMEM>1) err(warnmem,"minim00, rank>=%ld",s);
          invp = gerepilecopy(av1, invp);
        }
      }
    }
  }
  switch(flag)
  {
    case min_FIRST:
      avma=av0; return cgetg(1,t_VEC);
    case min_PERF:
      if (DEBUGLEVEL>1) { fprintferr("\n"); flusherr(); }
      avma=av0; return stoi(s);
  }
  k = min(s,maxrank);

  tetpil = avma; p1=cgetg(k+1,t_MAT);
  for (j=1; j<=k; j++)
    p1[j] = (long) gmul_mati_smallvec(u,(GEN)liste[j]);
  liste = p1;
  r = (maxnorm >= 0) ? ground(dbltor(maxnorm)): BORNE;

  r=icopy(r); gptr[0]=&r; gptr[1]=&liste;
  gerepilemanysp(av,tetpil,gptr,2);
  res[1]=lstoi(s<<1);
  res[2]=(long)r;
  res[3]=(long)liste; return res;
}

GEN
qfminim0(GEN a, GEN borne, GEN stockmax, long flag, long prec)
{
  switch(flag)
  {
    case 0: return minim00(a,borne,stockmax,min_ALL);
    case 1: return minim00(a,borne,gzero   ,min_FIRST);
    case 2: return fincke_pohst(a,borne,itos(stockmax),0,prec,NULL);
    default: err(flagerr,"qfminim");
  }
  return NULL; /* not reached */
}

GEN
minim(GEN a, GEN borne, GEN stockmax)
{
  return minim00(a,borne,stockmax,min_ALL);
}

GEN
minim2(GEN a, GEN borne, GEN stockmax)
{
  return minim00(a,borne,stockmax,min_FIRST);
}

GEN
perf(GEN a)
{
  return minim00(a,gzero,gzero,min_PERF);
}

/* general program for positive definit quadratic forms (real coeffs).
 * One needs BORNE != 0; LLL reduction done in fincke_pohst().
 * If (flag & 2) stop as soon as stockmax is reached.
 * If (flag & 1) return NULL on precision problems (no error).
 * If (check != NULL consider only vectors passing the check [ assumes
 *   stockmax > 0 and we only want the smallest possible vectors ] */
static GEN
smallvectors(GEN a, GEN BORNE, long stockmax, long flag, FP_chk_fun *CHECK)
{
  long N, n, i, j, k, s, epsbit, prec, checkcnt = 1;
  gpmem_t av, av1, lim;
  GEN u,S,x,y,z,v,q,norme1,normax1,borne1,borne2,eps,p1,alpha,norms,dummy;
  GEN (*check)(void *,GEN) = CHECK? CHECK->f: NULL;
  void *data = CHECK? CHECK->data: NULL;
  int skipfirst = CHECK? CHECK->skipfirst: 0;

  if (DEBUGLEVEL)
    fprintferr("smallvectors looking for norm <= %Z\n",gprec_w(BORNE,3));

  q = sqred1intern(a,flag&1);
  if (q == NULL) return NULL;
  if (DEBUGLEVEL>5) fprintferr("q = %Z",q);
  prec = gprecision(q);
  epsbit = bit_accuracy(prec) >> 1;
  eps = realun(prec); setexpo(eps,-epsbit);
  alpha = dbltor(0.95);
  normax1 = gzero;
  borne1= gadd(BORNE,eps);
  borne2 = mpmul(borne1,alpha);
  N = lg(q); n = N-1;
  v = cgetg(N,t_VEC);
  dummy = cgetg(1,t_STR);

  av = avma; lim = stack_lim(av,1);
  if (check) norms = cgetg(stockmax+1,t_VEC);
  S = cgetg(stockmax+1,t_VEC);
  x = cgetg(N,t_COL);
  y = cgetg(N,t_COL);
  z = cgetg(N,t_COL);
  for (i=1; i<N; i++) { v[i] = coeff(q,i,i); x[i]=y[i]=z[i] = zero; }

  x[n] = lmpent(mpsqrt(gdiv(borne1,(GEN)v[n])));
  if (DEBUGLEVEL>3) { fprintferr("\nx[%ld] = %Z\n",n,x[n]); flusherr(); }

  s = 0; k = n;
  for(;; x[k] = laddis((GEN)x[k],-1)) /* main */
  {
    do
    {
      int fl = 0;
      if (k > 1)
      {
        av1=avma; k--; p1 = mpmul(gcoeff(q,k,k+1),(GEN)x[k+1]);
	for (j=k+2; j<N; j++)
	  p1 = mpadd(p1, mpmul(gcoeff(q,k,j),(GEN)x[j]));
        z[k] = (long)gerepileuptoleaf(av1,p1);

        av1=avma; p1 = gsqr(mpadd((GEN)x[k+1],(GEN)z[k+1]));
        p1 = mpadd((GEN)y[k+1], mpmul(p1,(GEN)v[k+1]));
	y[k] = (long)gerepileuptoleaf(av1, p1);

        av1=avma; p1 = mpsub(borne1, (GEN)y[k]);
	if (signe(p1) < 0) { avma=av1; fl = 1; }
        else
        {
          p1 = mpadd(eps,mpsub(mpsqrt(gdiv(p1,(GEN)v[k])), (GEN)z[k]));
          x[k] = (long)gerepileuptoleaf(av1,mpent(p1));
        }
        /* reject the [x_1,...,x_skipfirst,0,...,0] */
        if (k <= skipfirst && !signe(y[skipfirst])) goto END;
      }
      for(;; x[k] = laddis((GEN)x[k],-1))
      {
	if (!fl)
	{
          av1 = avma; /* p1 >= 0 */
	  p1 = mpmul((GEN)v[k], gsqr(mpadd((GEN)x[k],(GEN)z[k])));
	  i = mpcmp(mpsub(mpadd(p1,(GEN)y[k]), borne1), gmul2n(p1,-epsbit));
          avma = av1; if (i <= 0) break;
	}
        k++; fl=0;
      }

      if (low_stack(lim, stack_lim(av,1)))
      {
        int cnt = 4;
	if(DEBUGMEM>1) err(warnmem,"smallvectors");
	if (stockmax)
        { /* initialize to dummy values */
          GEN T = S;
          for (i=s+1; i<=stockmax; i++) S[i]=(long)dummy;
          S = gclone(S); if (isclone(T)) gunclone(T);
        }
        if (check)
        {
          cnt+=3;
          for (i=s+1; i<=stockmax; i++) norms[i]=(long)dummy;
        }
	gerepileall(av,cnt,&x,&y,&z,&normax1,&borne1,&borne2,&norms);
      }
      if (DEBUGLEVEL>3)
      {
	if (DEBUGLEVEL>5) fprintferr("%ld ",k);
	if (k==n) fprintferr("\nx[%ld] = %Z\n",n,x[n]);
	flusherr();
      }
    }
    while (k > 1);

    /* x = 0: we're done */
    if (!signe(x[1]) && !signe(y[1])) goto END;

    av1=avma; p1 = gsqr(mpadd((GEN)x[1],(GEN)z[1]));
    norme1 = mpadd((GEN)y[1], mpmul(p1, (GEN)v[1]));
    if (mpcmp(norme1,borne1) > 0) { avma=av1; continue; /* main */ }

    norme1 = gerepileupto(av1,norme1);
    if (check)
    {
      if (checkcnt < 5 && mpcmp(norme1, borne2) < 0)
      {
        if (check(data,x))
        {
          borne1 = mpadd(norme1,eps);
          borne2 = mpmul(borne1,alpha);
          s = 0; checkcnt = 0;
        }
        else { checkcnt++ ; continue; /* main */}
      }
    }
    else if (mpcmp(norme1,normax1) > 0) normax1 = norme1;
    if (++s <= stockmax)
    {
      if (check) norms[s] = (long)norme1;
      S[s] = (long)dummycopy(x);
      if (s == stockmax && (flag&2) && check)
      {
        gpmem_t av1 = avma;
        GEN per = sindexsort(norms);
        if (DEBUGLEVEL) fprintferr("sorting...\n");
        for (i=1; i<=s; i++)
        {
          long k = per[i];
          if (check(data,(GEN)S[k]))
          {
            S[1] = S[k]; avma = av1;
            borne1 = mpadd(norme1,eps);
            borne2 = mpmul(borne1,alpha);
            s = 1; checkcnt = 0; break;
          }
        }
        if (checkcnt) s = 0;
      }
    }
  }
END:
  if (s < stockmax) stockmax = s;
  if (check)
  {
    GEN per, alph,pols,p;
    if (DEBUGLEVEL) fprintferr("final sort & check...\n");
    setlg(norms,s+1); per = sindexsort(norms);
    alph = cgetg(s+1,t_VEC);
    pols = cgetg(s+1,t_VEC);
    for (j=0,i=1; i<=s; i++)
    {
      long k = per[i];
      if (j && mpcmp((GEN)norms[k], borne1) > 0) break;
      if ((p = check(data,(GEN)S[k])))
      {
        if (!j) borne1 = gadd((GEN)norms[k],eps);
        j++; pols[j]=(long)p; alph[j]=S[k];
      }
    }
    u = cgetg(3,t_VEC);
    setlg(pols,j+1); u[1] = (long)pols;
    setlg(alph,j+1); u[2] = (long)alph;
    if (isclone(S)) { u[2] = (long)forcecopy(alph); gunclone(S); }
    return u;
  }
  u = cgetg(4,t_VEC);
  u[1] = lstoi(s<<1);
  u[2] = (long)normax1;
  if (stockmax)
  {
    setlg(S,stockmax+1);
    settyp(S,t_MAT);
    if (isclone(S)) { p1 = S; S = forcecopy(S); gunclone(p1); }
  }
  else
    S = cgetg(1,t_MAT);
  u[3] = (long)S; return u;
}

/* solve x~.a.x <= bound, a > 0. If check is non-NULL keep x only if check(x).
 * flag & 1, return NULL in case of precision problems (sqred1 or lllgram)
 *   raise an error otherwise.
 * flag & 2, return as soon as stockmax vectors found.
 * If a is a number field, use its T2 matrix
 */
GEN
fincke_pohst(GEN a,GEN B0,long stockmax,long flag, long PREC, FP_chk_fun *CHECK)
{
  VOLATILE gpmem_t av = avma;
  VOLATILE long pr,i,j,n;
  VOLATILE GEN B,nf,r,rinvtrans,u,v,res,z,vnorm,sperm,perm,uperm,gram;
  VOLATILE GEN bound = B0;
  void *catcherr = NULL;
  long prec = PREC;

  if (DEBUGLEVEL>2) { fprintferr("entering fincke_pohst\n"); flusherr(); }
  if (typ(a) == t_VEC) { nf = checknf(a); a = gmael(nf,5,3); } else nf = NULL;
  pr = gprecision(a);
  if (pr) prec = pr; else a = gmul(a,realun(prec));
  n = lg(a);
  if (n == 1)
  {
    if (CHECK) err(talker, "dimension 0 in fincke_pohst");
    avma = av; z=cgetg(4,t_VEC);
    z[1]=z[2]=zero;
    z[3]=lgetg(1,t_MAT); return z;
  }
  if (nf)
  { /* T2 already LLL-reduced */
    u = idmat(n-1);
    r = a;
  }
  else
  {
    if (DEBUGLEVEL>2) fprintferr("first LLL: prec = %ld\n", prec);
    u = lllgramintern(a,4,flag&1, (prec<<1)-2);
    if (!u) goto PRECPB;
    r = qf_base_change(a,u,1);
  }
  r = sqred1intern(r,flag&1);
  if (!r) goto PRECPB;
  for (i=1; i<n; i++)
  {
    GEN p1 = gsqrt(gcoeff(r,i,i), prec);
    coeff(r,i,i)=(long)p1;
    for (j=i+1; j<n; j++)
      coeff(r,i,j) = lmul(p1, gcoeff(r,i,j));
  }
  /* now r~ * r = a in approximate LLL basis */
  rinvtrans = gtrans(invmat(r));

  v = NULL;
  for (i=1; i<6; i++) /* try to get close to a genuine LLL basis */
  {
    GEN p1;
    if (DEBUGLEVEL>2)
      fprintferr("final LLLs: prec = %ld, precision(rinvtrans) = %ld\n",
                  prec,gprecision(rinvtrans));
    p1 = lllintern(rinvtrans, 100, flag&1, 0);
    if (!p1) goto PRECPB;
    if (ishnfall(p1)) break; /* upper triangular */
    if (v) v = gmul(v,p1); else v = p1;
    rinvtrans = gmul(rinvtrans,p1);
  }
  if (i == 6) goto PRECPB; /* diverges... */

  if (v)
  {
    GEN u2 = ZM_inv(gtrans(v),gun);
    r = gmul(r,u2); /* r = LLL basis now */
    u = gmul(u,u2);
  }

  vnorm = cgetg(n,t_VEC);
  for (j=1; j<n; j++) vnorm[j] = lnorml2((GEN)rinvtrans[j]);
  sperm = cgetg(n,t_MAT);
  uperm = cgetg(n,t_MAT); perm = sindexsort(vnorm);
  for (i=1; i<n; i++) { uperm[n-i] = u[perm[i]]; sperm[n-i] = r[perm[i]]; }

  gram = gram_matrix(sperm);
  B = gcoeff(gram,n-1,n-1);
  if (gexpo(B) >= bit_accuracy(lg(B)-2)) goto PRECPB;

  { /* catch precision problems (truncation error) */
    jmp_buf env;
    if (setjmp(env)) goto PRECPB;
    catcherr = err_catch(precer, env, NULL);
  }
  if (CHECK && CHECK->f_init)
  {
    bound = CHECK->f_init(CHECK,nf,gram,uperm, &prec);
    if (!bound) goto PRECPB;
  }
  if (!bound)
  { /* set bound */
    GEN x = cgetg(n,t_COL);
    if (nf) bound = get_Bnf(nf);
    for (i=2; i<n; i++) x[i]=zero;
    for (i=1; i<n; i++)
    {
      x[i] = un; B = gcoeff(gram,i,i);
      if (!bound || mpcmp(B,bound) < 0) bound = B;
      x[i] = zero;
    }
  }

  if (DEBUGLEVEL>2) {fprintferr("entering smallvectors\n"); flusherr();}
  for (i=1; i<n; i++)
  {
    res = smallvectors(gram, bound? bound: gcoeff(gram,i,i),
                       stockmax,flag,CHECK);
    if (!res) goto PRECPB;
    if (!CHECK || bound || lg(res[2]) > 1) break;
    if (DEBUGLEVEL>2) fprintferr("  i = %ld failed\n",i);
  }
  err_leave(&catcherr); catcherr = NULL;
  if (CHECK)
  {
    if (CHECK->f_post) res = CHECK->f_post(CHECK->data, res);
    return res;
  }

  if (DEBUGLEVEL>2) {fprintferr("leaving fincke_pohst\n"); flusherr();}
  z=cgetg(4,t_VEC);
  z[1]=lcopy((GEN)res[1]);
  z[2]=pr? lcopy((GEN)res[2]) : lround((GEN)res[2]);
  z[3]=lmul(uperm, (GEN)res[3]); return gerepileupto(av,z);
PRECPB:
  if (catcherr) err_leave(&catcherr);
  if (!(flag & 1))
    err(talker,"not a positive definite form in fincke_pohst");
  avma = av; return NULL;
}
