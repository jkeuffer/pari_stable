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

/*******************************************************************/
/*                                                                 */
/*                       MAXIMAL ORDERS                            */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "parinf.h"

#define RXQX_rem(x,y,T) RXQX_divrem((x),(y),(T),ONLY_REM)
extern GEN addshiftw(GEN x, GEN y, long d);
extern GEN norm_by_embed(long r1, GEN x);
extern GEN ZX_resultant_all(GEN A, GEN B, GEN dB, ulong bound);
extern GEN polsym_gen(GEN P, GEN y0, long n, GEN T, GEN N);
extern GEN FqX_gcd(GEN P, GEN Q, GEN T, GEN p);
extern GEN FqX_factor(GEN x, GEN T, GEN p);
extern GEN DDF2(GEN x, long hint);
extern GEN eltabstorel(GEN x, GEN T, GEN pol, GEN k);
extern GEN element_powid_mod_p(GEN nf, long I, GEN n, GEN p);
extern GEN FqV_red(GEN z, GEN T, GEN p);
extern GEN Fp_factor_irred(GEN P,GEN l, GEN Q);
extern GEN RXQX_divrem(GEN x, GEN y, GEN T, GEN *pr);
extern GEN RXQX_mul(GEN x, GEN y, GEN T);
extern GEN ZY_ZXY_resultant_all(GEN A, GEN B0, long *lambda, GEN *LPRS);
extern GEN col_to_ff(GEN x, long v);
extern GEN element_mulidid(GEN nf, long i, long j);
extern GEN eltmulid_get_table(GEN nf, long i);
extern GEN idealaddtoone_i(GEN nf, GEN x, GEN y);
extern GEN merge_factor_i(GEN f, GEN g);
extern GEN mulmat_pol(GEN A, GEN x);
extern GEN nfgcd(GEN P, GEN Q, GEN nf, GEN den);
extern GEN pidealprimeinv(GEN nf, GEN x);
extern GEN pol_to_monic(GEN pol, GEN *lead);
extern GEN quicktrace(GEN x, GEN sym);
extern GEN sqr_by_tab(GEN tab, GEN x);
extern GEN to_polmod(GEN x, GEN mod);
extern GEN unnf_minus_x(GEN x);
extern int isrational(GEN x);
extern long int_elt_val(GEN nf, GEN x, GEN p, GEN bp, GEN *t);
extern GEN gauss_realimag(GEN x, GEN y);
extern void check_ZKmodule(GEN x, char *s);

/* FIXME: backward compatibility. Should use the proper nf_* equivalents */
#define compat_PARTIAL 1
#define compat_ROUND2  2

static void
allbase_check_args(GEN f, long flag, GEN *dx, GEN *ptw)
{
  GEN w = *ptw;

  if (DEBUGLEVEL) (void)timer2();
  if (typ(f)!=t_POL) err(notpoler,"allbase");
  if (degpol(f) <= 0) err(constpoler,"allbase");

  *dx = w? factorback(w, NULL): ZX_disc(f);
  if (!signe(*dx)) err(talker,"reducible polynomial in allbase");
  if (!w) *ptw = auxdecomp(absi(*dx), (flag & nf_PARTIALFACT)? 0: 1);
  if (DEBUGLEVEL) msgtimer("disc. factorisation");
}

/*******************************************************************/
/*                                                                 */
/*                            ROUND 2                              */
/*                                                                 */
/*******************************************************************/
/* companion matrix of unitary polynomial x */
static GEN
companion(GEN x) /* cf assmat */
{
  long i,j,l;
  GEN y;

  l=degpol(x)+1; y=cgetg(l,t_MAT);
  for (j=1; j<l; j++)
  {
    y[j] = lgetg(l,t_COL);
    for (i=1; i<l-1; i++)
      coeff(y,i,j)=(i+1==j)? un: zero;
    coeff(y,i,j) = lneg((GEN)x[j+1]);
  }
  return y;
}

/* assume x, y are square integer matrices of same dim. Multiply them */
static GEN
mulmati(GEN x, GEN y)
{
  pari_sp av;
  long n = lg(x),i,j,k;
  GEN z = cgetg(n,t_MAT),p1,p2;

  for (j=1; j<n; j++)
  {
    z[j] = lgetg(n,t_COL);
    for (i=1; i<n; i++)
    {
      p1=gzero; av=avma;
      for (k=1; k<n; k++)
      {
        p2=mulii(gcoeff(x,i,k),gcoeff(y,k,j));
        if (p2 != gzero) p1=addii(p1,p2);
      }
      coeff(z,i,j)=lpileupto(av,p1);
    }
  }
  return z;
}

static GEN
_mulmati(void *data /*ignored*/, GEN x, GEN y) {
  (void)data; return mulmati(x,y);
}
static GEN
_sqrmati(void *data /*ignored*/, GEN x) {
  (void)data; return mulmati(x,x);
}

static GEN
powmati(GEN x, GEN n)
{
  pari_sp av = avma;
  GEN y = leftright_pow(x, n, NULL, &_sqrmati, &_mulmati);
  return gerepileupto(av,y);
}

static GEN
rtran(GEN v, GEN w, GEN q)
{
  pari_sp av,tetpil;
  GEN p1;

  if (signe(q))
  {
    av=avma; p1=gneg(gmul(q,w)); tetpil=avma;
    return gerepile(av,tetpil,gadd(v,p1));
  }
  return v;
}

/* return (v - qw) mod m (only compute entries k0,..,n)
 * v and w are expected to have entries smaller than m */
static GEN
mtran(GEN v, GEN w, GEN q, GEN m, GEN mo2, long k0)
{
  long k;
  GEN p1;

  if (signe(q))
    for (k=lg(v)-1; k >= k0; k--)
    {
      pari_sp av = avma;
      p1 = subii((GEN)v[k], mulii(q,(GEN)w[k]));
      p1 = centermodii(p1, m, mo2);
      v[k] = lpileuptoint(av, p1);
    }
  return v;
}

/* entries of v and w are C small integers */
static GEN
mtran_long(GEN v, GEN w, long q, long m, long k0)
{
  long k, p1;

  if (q)
  {
    for (k=lg(v)-1; k>= k0; k--)
    {
      p1 = v[k] - q * w[k];
      v[k] = p1 % m;
    }
  }
  return v;
}

/* coeffs of a are C-long integers */
static void
rowred_long(GEN a, long rmod)
{
  long q,j,k,pro, c = lg(a), r = lg(a[1]);

  for (j=1; j<r; j++)
  {
    for (k=j+1; k<c; k++)
      while (coeff(a,j,k))
      {
	q = coeff(a,j,j) / coeff(a,j,k);
	pro=(long)mtran_long((GEN)a[j],(GEN)a[k],q,rmod, j);
	a[j]=a[k]; a[k]=pro;
      }
    if (coeff(a,j,j) < 0)
      for (k=j; k<r; k++) coeff(a,k,j)=-coeff(a,k,j);
    for (k=1; k<j; k++)
    {
      q = coeff(a,j,k) / coeff(a,j,j);
      a[k]=(long)mtran_long((GEN)a[k],(GEN)a[j],q,rmod, k);
    }
  }
  /* don't update the 0s in the last columns */
  for (j=1; j<r; j++)
    for (k=1; k<r; k++) coeff(a,j,k) = lstoi(coeff(a,j,k));
}

static void
rowred(GEN a, GEN rmod)
{
  long j,k,pro, c = lg(a), r = lg(a[1]);
  pari_sp av=avma, lim=stack_lim(av,1);
  GEN q, rmodo2 = shifti(rmod,-1);

  for (j=1; j<r; j++)
  {
    for (k=j+1; k<c; k++)
      while (signe(gcoeff(a,j,k)))
      {
	q=diviiround(gcoeff(a,j,j),gcoeff(a,j,k));
	pro=(long)mtran((GEN)a[j],(GEN)a[k],q,rmod,rmodo2, j);
	a[j]=a[k]; a[k]=pro;
      }
    if (signe(gcoeff(a,j,j)) < 0)
      for (k=j; k<r; k++) coeff(a,k,j)=lnegi(gcoeff(a,k,j));
    for (k=1; k<j; k++)
    {
      q=diviiround(gcoeff(a,j,k),gcoeff(a,j,j));
      a[k]=(long)mtran((GEN)a[k],(GEN)a[j],q,rmod,rmodo2, k);
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      long j1,k1;
      GEN p1 = a;
      if(DEBUGMEM>1) err(warnmem,"rowred j=%ld", j);
      p1 = gerepilecopy(av,a);
      for (j1=1; j1<r; j1++)
        for (k1=1; k1<c; k1++) coeff(a,j1,k1) = coeff(p1,j1,k1);
    }
  }
}

/* Calcule d/x  ou  d est entier et x matrice triangulaire inferieure
 * entiere dont les coeff diagonaux divisent d (resultat entier). */
static GEN
matinv(GEN x, GEN d)
{
  pari_sp av,av1;
  long i,j,k, n = lg(x[1]); /* Warning: lg(x) from ordmax is bogus */
  GEN y,h;

  y = idmat(n-1);
  for (i=1; i<n; i++)
    coeff(y,i,i) = (long)diviiexact(d,gcoeff(x,i,i));
  av=avma;
  for (i=2; i<n; i++)
    for (j=i-1; j; j--)
    {
      for (h=gzero,k=j+1; k<=i; k++)
      {
        GEN p1 = mulii(gcoeff(y,i,k),gcoeff(x,k,j));
        if (p1 != gzero) h=addii(h,p1);
      }
      setsigne(h,-signe(h)); av1=avma;
      coeff(y,i,j) = lpile(av,av1,divii(h,gcoeff(x,j,j)));
      av = avma;
    }
  return y;
}

static GEN
ordmax(GEN *cf, GEN p, long epsilon, GEN *ptdelta)
{
  long sp,i,n=lg(cf)-1;
  pari_sp av=avma, av2,limit;
  GEN T,T2,Tn,m,v,delta,hard_case_exponent, *w;
  const GEN pp = sqri(p);
  const GEN ppo2 = shifti(pp,-1);
  const long pps = (2*expi(pp)+2 < (long)BITS_IN_LONG)? pp[2]: 0;

  if (cmpis(p,n) > 0)
  {
    hard_case_exponent = NULL;
    sp = 0; /* gcc -Wall */
  }
  else
  {
    long k;
    k = sp = itos(p);
    i=1; while (k < n) { k *= sp; i++; }
    hard_case_exponent = stoi(i);
  }
  T=cgetg(n+1,t_MAT); for (i=1; i<=n; i++) T[i]=lgetg(n+1,t_COL);
  T2=cgetg(2*n+1,t_MAT); for (i=1; i<=2*n; i++) T2[i]=lgetg(n+1,t_COL);
  Tn=cgetg(n*n+1,t_MAT); for (i=1; i<=n*n; i++) Tn[i]=lgetg(n+1,t_COL);
  v = new_chunk(n+1);
  w = (GEN*)new_chunk(n+1);

  av2 = avma; limit = stack_lim(av2,1);
  delta=gun; m=idmat(n);

  for(;;)
  {
    long j, k, h;
    pari_sp av0 = avma;
    GEN t,b,jp,hh,index,p1, dd = sqri(delta), ppdd = mulii(dd,pp);
    GEN ppddo2 = shifti(ppdd,-1);

    if (DEBUGLEVEL > 3)
      fprintferr("ROUND2: epsilon = %ld\tavma = %ld\n",epsilon,avma);

    b=matinv(m,delta);
    for (i=1; i<=n; i++)
    {
      for (j=1; j<=n; j++)
        for (k=1; k<=n; k++)
        {
          p1 = j==k? gcoeff(m,i,1): gzero;
          for (h=2; h<=n; h++)
          {
	    GEN p2 = mulii(gcoeff(m,i,h),gcoeff(cf[h],j,k));
            if (p2!=gzero) p1 = addii(p1,p2);
          }
          coeff(T,j,k) = (long)centermodii(p1, ppdd, ppddo2);
        }
      p1 = mulmati(m, mulmati(T,b));
      for (j=1; j<=n; j++)
	for (k=1; k<=n; k++)
	  coeff(p1,j,k)=(long)centermodii(divii(gcoeff(p1,j,k),dd),pp,ppo2);
      w[i] = p1;
    }

    if (hard_case_exponent)
    {
      for (j=1; j<=n; j++)
      {
	for (i=1; i<=n; i++) coeff(T,i,j) = coeff(w[j],1,i);
	/* ici la boucle en k calcule la puissance p mod p de w[j] */
	for (k=1; k<sp; k++)
	{
	  for (i=1; i<=n; i++)
	  {
	    p1 = gzero;
	    for (h=1; h<=n; h++)
            {
              GEN p2=mulii(gcoeff(T,h,j),gcoeff(w[j],h,i));
	      if (p2!=gzero) p1 = addii(p1,p2);
            }
            v[i] = lmodii(p1, p);
	  }
	  for (i=1; i<=n; i++) coeff(T,i,j)=v[i];
	}
      }
      t = powmati(T, hard_case_exponent);
    }
    else
    {
      for (i=1; i<=n; i++)
	for (j=1; j<=n; j++)
	{
          pari_sp av1 = avma;
          p1 = gzero;
	  for (k=1; k<=n; k++)
	    for (h=1; h<=n; h++)
	    {
	      const GEN r=modii(gcoeff(w[i],k,h),p);
	      const GEN s=modii(gcoeff(w[j],h,k),p);
              const GEN p2 = mulii(r,s);
	      if (p2!=gzero) p1 = addii(p1,p2);
	    }
	  coeff(T,i,j) = lpileupto(av1,p1);
	}
      t = T;
    }

    if (pps)
    {
      long ps = p[2];
      for (i=1; i<=n; i++)
        for (j=1; j<=n; j++)
        {
          coeff(T2,j,i)=(i==j)? ps: 0;
          coeff(T2,j,n+i)=smodis(gcoeff(t,i,j),ps);
        }
      rowred_long(T2,pps);
    }
    else
    {
      for (i=1; i<=n; i++)
        for (j=1; j<=n; j++)
        {
          coeff(T2,j,i)=(i==j)? (long)p: zero;
          coeff(T2,j,n+i)=lmodii(gcoeff(t,i,j),p);
        }
      rowred(T2,pp);
    }
    jp=matinv(T2,p);
    if (pps)
    {
      for (k=1; k<=n; k++)
      {
        pari_sp av1=avma;
        t = mulmati(mulmati(jp,w[k]), T2);
        for (h=i=1; i<=n; i++)
          for (j=1; j<=n; j++)
            { coeff(Tn,k,h) = itos(divii(gcoeff(t,i,j), p)) % pps; h++; }
        avma=av1;
      }
      avma = av0;
      rowred_long(Tn,pps);
    }
    else
    {
      for (k=1; k<=n; k++)
      {
        t = mulmati(mulmati(jp,w[k]), T2);
        for (h=i=1; i<=n; i++)
          for (j=1; j<=n; j++)
            { coeff(Tn,k,h) = ldivii(gcoeff(t,i,j), p); h++; }
      }
      rowred(Tn,pp);
    }
    for (index=gun,i=1; i<=n; i++)
      index = mulii(index,gcoeff(Tn,i,i));
    if (gcmp1(index)) break;

    m = mulmati(matinv(Tn,index), m);
    hh = delta = mulii(index,delta);
    for (i=1; i<=n; i++)
      for (j=1; j<=n; j++)
        hh = mppgcd(gcoeff(m,i,j),hh);
    if (!is_pm1(hh))
    {
      m = gdiv(m,hh);
      delta = divii(delta,hh);
    }
    epsilon -= 2 * ggval(index,p);
    if (epsilon < 2) break;
    if (low_stack(limit,stack_lim(av2,1)))
    {
      GEN *gptr[3]; gptr[0]=&m; gptr[1]=&delta;
      if(DEBUGMEM>1) err(warnmem,"ordmax");
      gerepilemany(av2, gptr,2);
    }
  }
  {
    GEN *gptr[2]; gptr[0]=&m; gptr[1]=&delta;
    gerepilemany(av,gptr,2);
  }
  *ptdelta=delta; return m;
}

/* Input:
 *  x normalized integral polynomial of degree n, defining K=Q(theta).
 *
 *  code 0, 1 or (long)p if we want base, smallbase ou factoredbase (resp.).
 *  y is GEN *, which will receive the discriminant of K.
 *
 * Output
 *  1) A t_COL whose n components are rationnal polynomials (with degree
 *     0,1...n-1) : integral basis for K (putting x=theta).
 *     Rem: common denominator is in da.
 *
 *  2) discriminant of K (in *y).
 */
static GEN
allbase2(GEN f, int flag, GEN *dx, GEN *dK, GEN *ptw)
{
  GEN w,w1,w2,a,pro,at,bt,b,da,db,q, *cf,*gptr[2];
  pari_sp av=avma,tetpil;
  long n,h,j,i,k,r,s,t,mf;

  w = ptw? *ptw: NULL;
  allbase_check_args(f,flag,dx, &w);
  w1 = (GEN)w[1];
  w2 = (GEN)w[2];
  n = degpol(f); h = lg(w1)-1;
  cf = (GEN*)cgetg(n+1,t_VEC);
  cf[2]=companion(f);
  for (i=3; i<=n; i++) cf[i]=mulmati(cf[2],cf[i-1]);

  a=idmat(n); da=gun;
  for (i=1; i<=h; i++)
  {
    pari_sp av1 = avma;
    mf=itos((GEN)w2[i]); if (mf==1) continue;
    if (DEBUGLEVEL) fprintferr("Treating p^k = %Z^%ld\n",w1[i],mf);

    b=ordmax(cf,(GEN)w1[i],mf,&db);
    a=gmul(db,a); b=gmul(da,b);
    da=mulii(db,da);
    at=gtrans(a); bt=gtrans(b);
    for (r=n; r; r--)
      for (s=r; s; s--)
        while (signe(gcoeff(bt,s,r)))
        {
          q=diviiround(gcoeff(at,s,s),gcoeff(bt,s,r));
          pro=rtran((GEN)at[s],(GEN)bt[r],q);
          for (t=s-1; t; t--)
          {
            q=diviiround(gcoeff(at,t,s),gcoeff(at,t,t));
            pro=rtran(pro,(GEN)at[t],q);
          }
          at[s]=bt[r]; bt[r]=(long)pro;
        }
    for (j=n; j; j--)
    {
      for (k=1; k<j; k++)
      {
        while (signe(gcoeff(at,j,k)))
        {
          q=diviiround(gcoeff(at,j,j),gcoeff(at,j,k));
          pro=rtran((GEN)at[j],(GEN)at[k],q);
          at[j]=at[k]; at[k]=(long)pro;
        }
      }
      if (signe(gcoeff(at,j,j))<0)
        for (k=1; k<=j; k++) coeff(at,k,j)=lnegi(gcoeff(at,k,j));
      for (k=j+1; k<=n; k++)
      {
        q=diviiround(gcoeff(at,j,k),gcoeff(at,j,j));
        at[k]=(long)rtran((GEN)at[k],(GEN)at[j],q);
      }
    }
    for (j=2; j<=n; j++)
      if (egalii(gcoeff(at,j,j), gcoeff(at,j-1,j-1)))
      {
        coeff(at,1,j)=zero;
        for (k=2; k<=j; k++) coeff(at,k,j)=coeff(at,k-1,j-1);
      }
    tetpil=avma; a=gtrans(at);
    {
      GEN *gptr[2];
      da = icopy(da); gptr[0]=&a; gptr[1]=&da;
      gerepilemanysp(av1,tetpil,gptr,2);
    }
  }
  *dK = *dx;
  for (j=1; j<=n; j++)
    *dK = diviiexact(mulii(*dK,sqri(gcoeff(a,j,j))), sqri(da));
  tetpil=avma; *dK = icopy(*dK);
  at=cgetg(n+1,t_VEC);
  for (k=1; k<=n; k++)
  {
    q=cgetg(k+2,t_POL); q[1] = f[1]; at[k] = (long)q;
    for (j=1; j<=k; j++) q[j+1] = ldiv(gcoeff(a,k,j),da);
  }
  gptr[0] = &at; gptr[1] = dK;
  gerepilemanysp(av,tetpil,gptr,2);
  return at;
}

GEN
base2(GEN x, GEN *pdK) { return nfbasis(x, pdK, compat_ROUND2, NULL); }

GEN
discf2(GEN x) { return nfdiscf0(x, compat_ROUND2, NULL); }

/*******************************************************************/
/*                                                                 */
/*                            ROUND 4                              */
/*                                                                 */
/*******************************************************************/

GEN nilord(GEN p,GEN fx,long mf,GEN gx,long flag);
GEN Decomp(GEN p,GEN f,long mf,GEN theta,GEN chi,GEN nu,long r);
static GEN dbasis(GEN p, GEN f, long mf, GEN alpha, GEN U);
static GEN maxord(GEN p,GEN f,long mf);
static GEN testb2(GEN p,GEN fa,long Fa,GEN theta,GEN pmf,long Ft,GEN ns);
static GEN testc2(GEN p,GEN fa,GEN pmr,GEN pmf,GEN alph2,
		  long Ea,GEN thet2,long Et,GEN ns);

static int
fnz(GEN x,long j)
{
  long i;
  for (i=1; i<j; i++)
    if (signe(x[i])) return 0;
  return 1;
}

/* return list u[i], 2 by 2 coprime with the same prime divisors as ab */
static GEN
get_coprimes(GEN a, GEN b)
{
  long i, k = 1;
  GEN u = cgetg(3, t_COL);
  u[1] = (long)a;
  u[2] = (long)b;
  /* u1,..., uk 2 by 2 coprime */
  while (k+1 < lg(u))
  {
    GEN d, c = (GEN)u[k+1];
    if (is_pm1(c)) { k++; continue; }
    for (i=1; i<=k; i++)
    {
      if (is_pm1(u[i])) continue;
      d = mppgcd(c, (GEN)u[i]);
      if (d == gun) continue;
      c = diviiexact(c, d);
      u[i] = (long)diviiexact((GEN)u[i], d);
      u = concatsp(u, d);
    }
    u[++k] = (long)c;
  }
  for (i = k = 1; i < lg(u); i++)
    if (!is_pm1(u[i])) u[k++] = u[i];
  setlg(u, k); return u;
}

/* return integer basis. Set dK = disc(K), dx = disc(f), w (possibly partial)
 * factorization of dK. *ptw can be set by the caller, in which case it is
 * taken to be the factorization of disc(f), then overwritten
 * [no consistency check] */
GEN
allbase(GEN f, int flag, GEN *dx, GEN *dK, GEN *index, GEN *ptw)
{
  VOLATILE GEN w1, w2, a, da, p1, ordmax;
  VOLATILE long n, lw, i, j, k, l;
  GEN w;

  if (flag & nf_ROUND2) return allbase2(f,flag,dx,dK,ptw);
  w = ptw? *ptw: NULL;
  allbase_check_args(f, flag, dx, &w);
  w1 = (GEN)w[1];
  w2 = (GEN)w[2];
  n = degpol(f); lw = lg(w1);
  ordmax = cgetg(1, t_VEC);
  /* "complete" factorization first */
  for (i=1; i<lw; i++)
  {
    VOLATILE long mf = itos((GEN)w2[i]);
    if (mf == 1) { ordmax = concatsp(ordmax, gun); continue; }

    CATCH(invmoder) { /* caught false prime, update factorization */
      GEN x = (GEN)global_err_data;
      GEN p = mppgcd((GEN)x[1], (GEN)x[2]);
      GEN N, u;
      if (DEBUGLEVEL) err(warner,"impossible inverse: %Z", x);

      u = get_coprimes(p, diviiexact((GEN)x[1],p));
      l = lg(u);
      /* no small factors, but often a prime power */
      for (k = 1; k < l; k++) u[k] = coeff(auxdecomp((GEN)u[k], 2),1,1);

      w1[i] = u[1];
      w1 = concatsp(w1, vecextract_i(u, 2, l-1));
      N = *dx;
      w2[i] = lstoi(pvaluation(N, (GEN)w1[i], &N));
      k  = lw;
      lw = lg(w1);
      for ( ; k < lw; k++) w2[k] = lstoi(pvaluation(N, (GEN)w1[k], &N));
    } RETRY {
      if (DEBUGLEVEL) fprintferr("Treating p^k = %Z^%ld\n",w1[i],mf);
      ordmax = concatsp(ordmax, _vec( maxord((GEN)w1[i],f,mf) ));
    } ENDCATCH;
  }

  a = NULL; /* gcc -Wall */
  da = NULL;
  for (i=1; i<lw; i++)
  {
    GEN db, b = (GEN)ordmax[i];
    if (b == gun) continue;
    db = gun;
    for (j=1; j<=n; j++)
    {
      p1 = denom(gcoeff(b,j,j));
      if (cmpii(p1,db) > 0) db = p1;
    }
    if (db == gun) continue;

    /* db = denom(diag(b)), (da,db) = 1 */
    b = Q_muli_to_int(b,db);
    if (!da) { da = db; a = b; }
    else
    {
      j=1; while (j<=n && fnz((GEN)a[j],j) && fnz((GEN)b[j],j)) j++;
      b = gmul(da,b);
      a = gmul(db,a); da = mulii(da,db);
      k = j-1; p1 = cgetg(2*n-k+1,t_MAT);
      for (j=1; j<=k; j++)
      {
        p1[j] = a[j];
        coeff(p1,j,j) = lmppgcd(gcoeff(a,j,j),gcoeff(b,j,j));
      }
      for (  ; j<=n;     j++) p1[j] = a[j];
      for (  ; j<=2*n-k; j++) p1[j] = b[j+k-n];
      a = hnfmodid(p1, da);
    }
    if (DEBUGLEVEL>5) fprintferr("Result for prime %Z is:\n%Z\n",w1[i],b);
  }
  *dK = *dx;
  if (da)
  {
    *index = diviiexact(da, gcoeff(a,1,1));
    for (j=2; j<=n; j++) *index = mulii(*index, diviiexact(da, gcoeff(a,j,j)));
    *dK = diviiexact(*dK, sqri(*index));
    for (j=n-1; j; j--)
      if (cmpis(gcoeff(a,j,j),2) > 0)
      {
        p1 = shifti(gcoeff(a,j,j),-1);
        for (k=j+1; k<=n; k++)
          if (cmpii(gcoeff(a,j,k),p1) > 0)
            for (l=1; l<=j; l++)
              coeff(a,l,k) = lsubii(gcoeff(a,l,k),gcoeff(a,l,j));
      }
    a = gdiv(a, da);
  }
  else
  {
    *index = gun;
    a = idmat(n);
  }

  if (ptw)
  {
    long lfa = 1;
    GEN W1, W2, D = *dK;

    w = cgetg(3,t_MAT);
    W1 = cgetg(lw, t_COL); w[1] = (long)W1;
    W2 = cgetg(lw, t_COL); w[2] = (long)W2;
    for (j=1; j<lw; j++)
    {
      k = pvaluation(D, (GEN)w1[j], &D);
      if (k) { W1[lfa] = w1[j]; W2[lfa] = lstoi(k); lfa++; }
    }
    setlg(W1, lfa);
    setlg(W2, lfa); *ptw = w;
  }
  return mat_to_vecpol(a, varn(f));
}

static GEN
update_fact(GEN x, GEN f)
{
  GEN e,q,d = ZX_disc(x), g = cgetg(3, t_MAT), p = (GEN)f[1];
  long iq,i,k,l;
  if (typ(f)!=t_MAT || lg(f)!=3)
    err(talker,"not a factorisation in nfbasis");
  l = lg(p);
  q = cgetg(l,t_COL); g[1]=(long)q;
  e = cgetg(l,t_COL); g[2]=(long)e; iq = 1;
  for (i=1; i<l; i++)
  {
    k = pvaluation(d, (GEN)p[i], &d);
    if (k) { q[iq] = p[i]; e[iq] = lstoi(k); iq++; }
  }
  setlg(q,iq); setlg(e,iq);
  return merge_factor_i(decomp(d), g);
}

static GEN
unscale_vecpol(GEN v, GEN h)
{
  long i, l;
  GEN w;
  if (!h) return v;
  l = lg(v); w = cgetg(l, typ(v));
  for (i=1; i<l; i++) w[i] = (long)unscale_pol((GEN)v[i], h);
  return w;
}

/* FIXME: have to deal with compatibility flags */
static void
_nfbasis(GEN x0, long flag, GEN fa, GEN *pbas, GEN *pdK)
{
  GEN x, dx, dK, basis, lead, index;
  long fl = 0;

  if (typ(x0)!=t_POL) err(typeer,"nfbasis");
  if (!degpol(x0)) err(zeropoler,"nfbasis");
  check_pol_int(x0, "nfbasis");

  x = pol_to_monic(x0, &lead);
  if (fa && gcmp0(fa)) fa = NULL; /* compatibility. NULL is the proper arg */
  if (fa && lead) fa = update_fact(x, fa);
  if (flag & compat_PARTIAL) fl |= nf_PARTIALFACT;
  if (flag & compat_ROUND2)  fl |= nf_ROUND2;
  basis = allbase(x, fl, &dx, &dK, &index, &fa);
  if (pbas) *pbas = unscale_vecpol(basis, lead);
  if (pdK)  *pdK = dK;
}

GEN
nfbasis(GEN x, GEN *pdK, long flag, GEN fa)
{
  pari_sp av = avma;
  GEN bas; _nfbasis(x, flag, fa, &bas, pdK);
  gerepileall(av, pdK? 2: 1, &bas, pdK); return bas;
}

GEN
nfbasis0(GEN x, long flag, GEN fa)
{
  pari_sp av = avma;
  GEN bas; _nfbasis(x, flag, fa, &bas, NULL);
  return gerepilecopy(av, bas);
}

GEN
nfdiscf0(GEN x, long flag, GEN fa)
{
  pari_sp av = avma;
  GEN dK; _nfbasis(x, flag, fa, NULL, &dK);
  return gerepilecopy(av, dK);
}

GEN
base(GEN x, GEN *pdK) { return nfbasis(x, pdK, 0, NULL); }

GEN
smallbase(GEN x, GEN *pdK) { return nfbasis(x, pdK, compat_PARTIAL, NULL); }

GEN
factoredbase(GEN x, GEN fa, GEN *pdK) { return nfbasis(x, pdK, 0, fa); }

GEN
discf(GEN x) { return nfdiscf0(x, 0, NULL); }

GEN
smalldiscf(GEN x) { return nfdiscf0(x, nf_PARTIALFACT, NULL); }

GEN
factoreddiscf(GEN x, GEN fa) { return nfdiscf0(x, 0, fa); }


/* return U if Z[alpha] is not maximal or 2*dU < m-1; else return NULL */
static GEN
dedek(GEN f, long mf, GEN p,GEN g)
{
  GEN k,h;
  long dk;

  h = FpX_div(f,g,p);
  k = gdivexact(gadd(f, gneg_i(gmul(g,h))), p);
  k = FpX_gcd(k, FpX_gcd(g,h, p), p);

  dk = degpol(k);
  if (DEBUGLEVEL>2)
  {
    fprintferr("  dedek: gcd has degree %ld\n", dk);
    if (DEBUGLEVEL>5) fprintferr("initial parameters p=%Z,\n  f=%Z\n",p,f);
  }
  if (2*dk >= mf-1) return FpX_div(f,k,p);
  return dk? (GEN)NULL: f;
}

/* p-maximal order of Af; mf = v_p(Disc(f)) */
static GEN
maxord(GEN p,GEN f,long mf)
{
  const pari_sp av = avma;
  long j,r, flw = (cmpsi(degpol(f),p) < 0);
  GEN w,g,h,res;

  if (flw)
  {
    h = NULL; r = 0; /* gcc -Wall */
    g = FpX_div(f, FpX_gcd(f,derivpol(f), p), p);
  }
  else
  {
    w = (GEN)factmod0(f,p)[1]; r = lg(w)-1;
    g = h = (GEN)w[r]; /* largest factor */
    for (j=1; j<r; j++) g = FpX_red(gmul(g, (GEN)w[j]), p);
  }
  res = dedek(f,mf,p,g);
  if (res)
    res = dbasis(p,f,mf,polx[varn(f)],res);
  else
  {
    if (flw) { w = (GEN)factmod0(f,p)[1]; r = lg(w)-1; h = (GEN)w[r]; }
    res = (r==1)? nilord(p,f,mf,h,0): Decomp(p,f,mf,polx[varn(f)],f,h,0);
  }
  return gerepileupto(av,res);
}

/* do a centermod on integer or rational number */
static GEN
polmodiaux(GEN x, GEN y, GEN ys2)
{
  if (typ(x)!=t_INT) x = mulii((GEN)x[1], mpinvmod((GEN)x[2],y));
  return centermodii(x,y,ys2);
}

/* x polynomial with integer or rational coeff. Reduce them mod y IN PLACE */
GEN
polmodi(GEN x, GEN y)
{
  long lx=lg(x), i;
  GEN ys2 = shifti(y,-1);
  for (i=2; i<lx; i++) x[i]=(long)polmodiaux((GEN)x[i],y,ys2);
  return normalizepol_i(x, lx);
}

/* same but not in place */
GEN
polmodi_keep(GEN x, GEN y)
{
  long lx=lg(x), i;
  GEN ys2 = shifti(y,-1);
  GEN z = cgetg(lx,t_POL);
  for (i=2; i<lx; i++) z[i]=(long)polmodiaux((GEN)x[i],y,ys2);
  z[1]=x[1]; return normalizepol_i(z, lx);
}

static GEN
shiftpol(GEN x, long v)
{
  x = addshiftw(x, zeropol(v), 1);
  setvarn(x,v); return x;
}

/* Sylvester's matrix, mod p^m (assumes f1 monic) */
static GEN
sylpm(GEN f1,GEN f2,GEN pm)
{
  long n,j,v=varn(f1);
  GEN a,h;

  n=degpol(f1); a=cgetg(n+1,t_MAT);
  h = FpX_rem(f2,f1,pm);
  for (j=1;; j++)
  {
    a[j] = (long)pol_to_vec(h,n);
    if (j == n) break;
    h = FpX_rem(shiftpol(h,v),f1,pm);
  }
  return hnfmodid(a,pm);
}

/* polynomial gcd mod p^m (assumes f1 monic) */
GEN
gcdpm(GEN f1,GEN f2,GEN pm)
{
  pari_sp av=avma,tetpil;
  long n,c,v=varn(f1);
  GEN a,col;

  n=degpol(f1); a=sylpm(f1,f2,pm);
  for (c=1; c<=n; c++)
    if (signe(resii(gcoeff(a,c,c),pm))) break;
  if (c > n) { avma=av; return zeropol(v); }

  col = gdiv((GEN)a[c], gcoeff(a,c,c)); tetpil=avma;
  return gerepile(av,tetpil, gtopolyrev(col,v));
}

/* reduced resultant mod p^m (assumes x monic) */
GEN
respm(GEN x,GEN y,GEN pm)
{
  pari_sp av = avma;
  GEN p1 = sylpm(x,y,pm);

  p1 = gcoeff(p1,1,1);
  if (egalii(p1,pm)) { avma = av; return gzero; }
  return gerepileuptoint(av, icopy(p1));
}

static GEN
dbasis(GEN p, GEN f, long mf, GEN alpha, GEN U)
{
  long n=degpol(f),dU,i;
  GEN b,ha,pd,pdp;

  if (n == 1) return gscalmat(gun, 1);
  if (DEBUGLEVEL>5)
  {
    fprintferr("  entering Dedekind Basis with parameters p=%Z\n",p);
    fprintferr("  f = %Z,\n  alpha = %Z\n",f,alpha);
  }
  ha = pd = gpowgs(p,mf/2); pdp = mulii(pd,p);
  dU = typ(U)==t_POL? degpol(U): 0;
  b = cgetg(n,t_MAT); /* Z[a] + U/p Z[a] is maximal */
  /* skip first column = gscalcol(pd,n) */
  for (i=1; i<n; i++)
  {
    if (i == dU)
    {
      ha = gdiv(gmul(pd,RX_RXQ_compo(U,alpha,f)),p);
      ha = polmodi(ha,pdp);
    }
    else
    {
      GEN d, mod;
      ha = gmul(ha,alpha);
      ha = Q_remove_denom(ha, &d);
      mod = d? mulii(pdp,d): pdp;
      ha = FpX_rem(ha, f, mod);
      if (d) ha = gdivexact(ha,d);
    }
    b[i] = (long)pol_to_vec(ha,n);
  }
  b = hnfmodid(b,pd);
  if (DEBUGLEVEL>5) fprintferr("  new order: %Z\n",b);
  return gdiv(b, pd);
}

static GEN
get_partial_order_as_pols(GEN p, GEN f)
{
  GEN b = maxord(p,f, ggval(ZX_disc(f),p));
  return mat_to_vecpol(b, varn(f));
}

long
FpX_val(GEN x0, GEN t, GEN p, GEN *py)
{
  long k;
  GEN r, y, x = x0;

  for (k=0; ; k++)
  {
    y = FpX_divrem(x, t, p, &r);
    if (signe(r)) break;
    x = y;
  }
  *py = x; return k;
}

/* e in Qp, f i Zp. Return r = e mod (f, pk) */
static GEN
QpX_mod(GEN e, GEN f, GEN pk)
{
  GEN mod, d;
  e = Q_remove_denom(e, &d);
  mod = d? mulii(pk,d): pk;
  e = FpX_rem(e, centermod(f, mod), mod);
  e = FpX_center(e, mod);
  if (d) e = gdiv(e, d);
  return e;
}

/* if flag != 0, factorization to precision r (maximal order otherwise)
 * nu irreducible mod p, divides chi */
GEN
Decomp(GEN p,GEN f,long mf,GEN theta,GEN chi,GEN nu,long flag)
{
  GEN fred,res,pr,pk,ph,pdr,b1,b2,a,e,f1,f2;

  if (DEBUGLEVEL>2)
  {
    fprintferr("  entering Decomp ");
    if (DEBUGLEVEL>5)
    {
      fprintferr("with parameters: p=%Z, expo=%ld\n",p,mf);
      if (flag) fprintferr("precision = %ld\n",flag);
      fprintferr("  f=%Z",f);
    }
    fprintferr("\n");
  }

  if (!FpX_val(chi, nu, p, &b1))
    err(talker, "bug in Decomp (not a factor), is p = %Z a prime?", p);
  b2 = FpX_div(chi, b1, p);
  a = FpX_mul(FpXQ_inv(b2, b1, p), b2, p);
  pdr = respm(f, derivpol(f), gpowgs(p,mf+1));
  e = RX_RXQ_compo(a, theta, f);
  e = gdiv(polmodi(gmul(pdr,e), mulii(pdr,p)),pdr);

  pr = flag? gpowgs(p,flag): mulii(p,sqri(pdr));
  pk = p; ph = mulii(pdr,pr);
  /* E(t) - e(t) belongs to p^k Op, which is contained in p^(k-df)*Zp[xi] */
  while (cmpii(pk,ph) < 0)
  { /* e <-- e^2(3-2e) mod p^2k */
    pk = sqri(pk);
    e = gmul(gsqr(e), gsubsg(3,gmul2n(e,1)));
    e = QpX_mod(e, f, pk);
  }
  fred = centermod(f, ph);
  f1 = gcdpm(fred, gmul(pdr,gsubsg(1,e)), ph);
  fred = centermod(fred, pr); /* pr | ph */
  f1 = centermod(f1, pr);
  f2 = FpX_div(fred,f1, pr);
  f2 = FpX_center(f2, pr);

  if (DEBUGLEVEL>5)
  {
    fprintferr("  leaving Decomp");
    fprintferr(" with parameters: f1 = %Z\nf2 = %Z\ne = %Z\n\n", f1,f2,e);
  }

  if (flag)
  {
    b1 = factorpadic4(f1,p,flag);
    b2 = factorpadic4(f2,p,flag); res = cgetg(3,t_MAT);
    res[1] = (long)concatsp((GEN)b1[1],(GEN)b2[1]);
    res[2] = (long)concatsp((GEN)b1[2],(GEN)b2[2]); return res;
  }
  else
  {
    GEN ib1, ib2;
    long n, n1, n2, i;
    ib1 = get_partial_order_as_pols(p,f1); n1 = lg(ib1)-1;
    ib2 = get_partial_order_as_pols(p,f2); n2 = lg(ib2)-1;
    n = n1+n2;
    res = cgetg(n+1, t_VEC);
    for (i=1; i<=n1; i++)
      res[i] = (long)QpX_mod(gmul(gmul(pdr,(GEN)ib1[i]),e), f, pdr);
    e = gsubsg(1,e); ib2 -= n1;
    for (   ; i<=n; i++)
      res[i] = (long)QpX_mod(gmul(gmul(pdr,(GEN)ib2[i]),e), f, pdr);
    res = vecpol_to_mat(res, n);
    return gdiv(hnfmodid(res,pdr), pdr); /* normalized integral basis */
  }
}

/* minimum extension valuation: res[0]/res[1] (both are longs) */
static void
vstar(GEN p,GEN h, long *L, long *E)
{
  long m,first,j,k,v,w;

  m=degpol(h); first=1; k=1; v=0;
  for (j=1; j<=m; j++)
    if (! gcmp0((GEN)h[m-j+2]))
    {
      w = ggval((GEN)h[m-j+2],p);
      if (first || w*k < v*j) { v=w; k=j; }
      first=0;
    }
  m = cgcd(v,k);
  *L = v/m;
  *E = k/m;
}

/* reduce the element elt modulo rd, taking first care of the denominators */
static GEN
redelt(GEN elt, GEN rd, GEN pd)
{
  GEN den, nelt, nrd, relt;

  den  = ggcd(Q_denom(elt), pd);
  nelt = gmul(den, elt);
  nrd  = gmul(den, rd);

  if (typ(elt) == t_POL)
    relt = polmodi(nelt, nrd);
  else
    relt = centermod(nelt, nrd);

  return gdiv(relt, den);
}

/* compute the Newton sums of g(x) mod pp from its coefficients */
GEN
polsymmodpp(GEN g, GEN pp)
{
  pari_sp av1, av2;
  long d = degpol(g), i, k;
  GEN s , y;

  y = cgetg(d + 1, t_COL);
  y[1] = lstoi(d);
  for (k = 1; k < d; k++)
  {
    av1 = avma;
    s = centermod(gmulsg(k, polcoeff0(g,d-k,-1)), pp);
    for (i = 1; i < k; i++)
      s = gadd(s, gmul((GEN)y[k-i+1], polcoeff0(g,d-i,-1)));
    av2 = avma;
    y[k + 1] = lpile(av1, av2, centermod(gneg(s), pp));
  }

  return y;
}

/* no GC */
static GEN
manage_cache(GEN chi, GEN pp, GEN ns)
{
  long j, n = degpol(chi);
  GEN ns2, npp = (GEN)ns[n+1];

  if (gcmp(pp, npp) > 0)
  {
    if (DEBUGLEVEL > 4)
      fprintferr("newtonsums: result too large to fit in cache\n");
    return polsymmodpp(chi, pp);
  }

  if (!signe((GEN)ns[1]))
  {
    ns2 = polsymmodpp(chi, pp);
    for (j = 1; j <= n; j++)
      affii((GEN)ns2[j], (GEN)ns[j]);
  }

  return ns;
}

/* compute the Newton sums modulo pp of the characteristic
   polynomial of a(x) mod g(x) */
static GEN
newtonsums(GEN a, GEN chi, GEN pp, GEN ns)
{
  GEN va, pa, s, ns2;
  long j, k, n = degpol(chi);
  pari_sp av2, lim;

  ns2 = manage_cache(chi, pp, ns);

  av2 = avma;
  lim = stack_lim(av2, 1);

  pa = gun;
  va = zerovec(n);

  for (j = 1; j <= n; j++)
  {
    pa = gmul(pa, a);
    pa = polmodi(pa, pp);
    pa = gmod(pa, chi);
    pa = polmodi(pa, pp);

    s  = gzero;

    for (k = 0; k <= n-1; k++)
      s = addii(s, mulii(polcoeff0(pa, k, -1), (GEN)ns2[k+1]));

    va[j] = (long)centermod(s, pp);

    if (low_stack(lim, stack_lim(av2, 1)))
    {
      GEN *gptr[2];
      gptr[0]=&pa; gptr[1]=&va;
      if(DEBUGMEM>1) err(warnmem, "newtonsums");
      gerepilemany(av2, gptr, 2);
    }
  }

  return va;
}

/* compute the characteristic polynomial of a mod g
   to a precision of pp using Newton sums */
static GEN
newtoncharpoly(GEN a, GEN chi, GEN pp, GEN ns)
{
  GEN v, c, s, t;
  long n = degpol(chi), j, k, vn = varn(chi);
  pari_sp av = avma, av2, lim;

  v = newtonsums(a, chi, pp, ns);
  av2 = avma;
  lim = stack_lim(av2, 1);
  c = cgetg(n + 2, t_VEC);
  c[1] = un;
  if (n%2) c[1] = lneg((GEN)c[1]);
  for (k = 2; k <= n+1; k++) c[k] = zero;

  for (k = 2; k <= n+1; k++)
  {
    s = gzero;
    for (j = 1; j < k; j++)
    {
      t = gmul((GEN)v[j], (GEN)c[k-j]);
      if (!(j%2)) t = gneg(t);
      s = gadd(s, t);
    }
    c[k] = ldiv(s, stoi(k - 1));

    if (low_stack(lim, stack_lim(av2, 1)))
    {
      if(DEBUGMEM>1) err(warnmem, "newtoncharpoly");
      c = gerepilecopy(av2, c);
    }
  }

  k = (n%2)? 1: 2;
  for (  ; k <= n+1; k += 2)
    c[k] = lneg((GEN)c[k]);

  return gerepileupto(av, gtopoly(c, vn));
}

/* return v_p(n!) */
long
val_fact(ulong n, ulong p)
{
  ulong q = p, v = 0;
  do { v += n/q; q *= p; } while (n >= q);
  return (long)v;
}

static GEN
mycaract(GEN f, GEN beta, GEN p, GEN pp, GEN ns)
{
  GEN p1, chi, npp;
  long v = varn(f), n = degpol(f);

  if (gcmp0(beta)) return zeropol(v);

  beta = Q_primitive_part(beta,&p1);
  if (!pp)
    chi = ZX_caract(f, beta, v);
  else
  {
    npp = pp;
    if (lgefint(p) == 3) npp = mulii(npp, gpowgs(p, val_fact(n, itou(p))));
    if (p1) npp = mulii(npp, gpowgs(denom(p1), n));

    chi = newtoncharpoly(beta, f, npp, ns);
  }

  if (p1) chi = rescale_pol(chi,p1);

  if (!pp) return chi;

  /* this can happen only if gamma is incorrect (not an integer) */
  if (divise(Q_denom(chi), p)) return NULL;

  return redelt(chi, pp, pp);
}

/* Factor characteristic polynomial of beta mod p */
static GEN
factcp(GEN p, GEN f, GEN beta, GEN pp, GEN ns)
{
  pari_sp av;
  GEN chi,nu, b = cgetg(4,t_VEC);
  long l;

  chi = mycaract(f,beta,p,pp,ns);
  av = avma; nu = (GEN)factmod0(chi,p)[1]; l = lg(nu)-1;
  nu = (GEN)nu[1];
  b[1] = (long)chi;
  b[2] = lpilecopy(av,nu);
  b[3] = lstoi(l); return b;
}

/* return the prime element in Zp[phi] */
static GEN
getprime(GEN p, GEN chi, GEN phi, GEN chip, GEN nup, long *Lp, long *Ep)
{
  long v = varn(chi), L, E, r, s;
  GEN chin, pip, pp;

  if (gegal(nup, polx[v]))
    chin = chip;
  else
    chin = mycaract(chip, nup, p, NULL, NULL);

  vstar(p, chin, &L, &E);
  (void)cbezout(L, -E, &r, &s);
  if (r <= 0)
  {
    long q = 1 + ((-r) / E);
    r += q*E;
    s += q*L;
  }

  pip = RX_RXQ_compo(nup, phi, chi);
  pip = lift_intern(gpowgs(gmodulcp(pip, chi), r));
  pp  = gpowgs(p, s);

  *Lp = L;
  *Ep = E; return gdiv(pip, pp);
}

static GEN
update_alpha(GEN p, GEN fx, GEN alph, GEN chi, GEN pmr, GEN pmf, long mf,
	     GEN ns)
{
  long l, v = varn(fx);
  GEN nalph = NULL, nchi, w, nnu, pdr, npmr, rep;

  affii(gzero, (GEN)ns[1]); /* kill cache */

  if (!chi)
    nchi = mycaract(fx, alph, p, pmf, ns);
  else
  {
    nchi  = chi;
    nalph = alph;
  }

  pdr = respm(nchi, derivpol(nchi), pmr);
  for (;;)
  {
    if (signe(pdr)) break;
    if (!nalph) nalph = gadd(alph, gmul(p, polx[v]));
    /* nchi was too reduced at this point; try a larger precision */
    pmf  = sqri(pmf);
    nchi = mycaract(fx, nalph, p, pmf, ns);
    pdr  = respm(nchi, derivpol(nchi), pmf);
    if (signe(pdr)) break;
    if (DEBUGLEVEL >= 6)
      fprintferr("  inseparable polynomial in update_alpha!\n");
    /* at this point, we assume that chi is not square-free */
    nalph = gadd(nalph, gmul(p, polx[v]));
    w = factcp(p, fx, nalph, NULL, ns);
    nchi = (GEN)w[1];
    nnu  = (GEN)w[2];
    l    = itos((GEN)w[3]);
    if (l > 1) return Decomp(p, fx, mf, nalph, nchi, nnu, 0);
    pdr = respm(nchi, derivpol(nchi), pmr);
  }

  if (is_pm1(pdr))
    npmr = gun;
  else
  {
    npmr  = mulii(sqri(pdr), p);
    nchi  = polmodi(nchi, npmr);
    nalph = redelt(nalph? nalph: alph, npmr, pmf);
  }

  affii(gzero, (GEN)ns[1]); /* kill cache again (contains data for fx) */

  rep = cgetg(5, t_VEC);
  rep[1] = (long)nalph;
  rep[2] = (long)nchi;
  rep[3] = (long)npmr;
  rep[4] = lmulii(p, pdr);

  return rep;
}

/* flag != 0 iff we're looking for the p-adic factorization,
   in which case it is the p-adic precision we want */
GEN
nilord(GEN p, GEN fx, long mf, GEN gx, long flag)
{
  long L, E, Fa, La, Ea, oE, Fg, eq, er, v = varn(fx), i, nv, Le, Ee, N, l, vn;
  GEN p1, alph, chi, nu, w, phi, pmf, pdr, pmr, kapp, pie, chib, ns;
  GEN gamm, chig, nug, delt, beta, eta, chie, nue, pia, opa;

  if (DEBUGLEVEL>2)
  {
    fprintferr("  entering Nilord");
    if (DEBUGLEVEL>4)
    {
      fprintferr(" with parameters: p = %Z, expo = %ld\n", p, mf);
      fprintferr("  fx = %Z, gx = %Z", fx, gx);
    }
    fprintferr("\n");
  }

  pmf = gpowgs(p, mf + 1);
  pdr = respm(fx, derivpol(fx), pmf);
  pmr = mulii(sqri(pdr), p);
  pdr = mulii(p, pdr);
  chi = polmodi_keep(fx, pmr);

  alph = polx[v];
  nu = gx;
  N  = degpol(fx);
  oE = 0;
  opa = NULL;

  /* used to cache the newton sums of chi */
  ns = cgetg(N + 2, t_COL);
  p1 = powgi(p, gceil(gdivsg(N, mulii(p, subis(p, 1))))); /* p^(N/(p(p-1))) */
  p1 = mulii(p1, mulii(pmf, gpowgs(pmr, N)));
  l  = lgefint(p1); /* enough in general... */
  for (i = 1; i <= N + 1; i++) ns[i] = lgeti(l);
  ns[N+1] = (long)p1;
  affii(gzero, (GEN)ns[1]); /* zero means: need to be computed */

  for(;;)
  {
    /* kappa needs to be recomputed */
    kapp = NULL;
    Fa   = degpol(nu);
    /* the prime element in Zp[alpha] */
    pia  = getprime(p, chi, polx[v], chi, nu, &La, &Ea);

    if (Ea < oE)
    {
      alph = gadd(alph, opa);
      w = update_alpha(p, fx, alph, NULL, pmr, pmf, mf, ns);
      alph = (GEN)w[1];
      chi  = (GEN)w[2];
      pmr  = (GEN)w[3];
      pdr  = (GEN)w[4];
      pia  = getprime(p, chi, polx[v], chi, nu, &La, &Ea);
    }
    pia  = redelt(pia, pmr, pmf);

    oE = Ea; opa = RX_RXQ_compo(pia, alph, fx);

    if (DEBUGLEVEL >= 5)
      fprintferr("  Fa = %ld and Ea = %ld \n", Fa, Ea);

    /* we change alpha such that nu = pia */
    if (La > 1)
    {
      alph = gadd(alph, RX_RXQ_compo(pia, alph, fx));
      w = update_alpha(p, fx, alph, NULL, pmr, pmf, mf, ns);
      alph = (GEN)w[1];
      chi  = (GEN)w[2];
      pmr  = (GEN)w[3];
      pdr  = (GEN)w[4];
    }

    /* if Ea*Fa == N then O = Zp[alpha] */
    if (Ea*Fa == N)
    {
      if (flag) return NULL;

      alph = redelt(alph, sqri(p), pmf);
      return dbasis(p, fx, mf, alph, p);
    }

    /* during the process beta tends to a factor of chi */
    beta  = lift_intern(gpowgs(gmodulcp(nu, chi), Ea));

    for (;;)
    {
      if (DEBUGLEVEL >= 5)
	fprintferr("  beta = %Z\n", beta);

      /* if pmf divides norm(beta) then it's useless */
      p1 = gmod(gnorm(gmodulcp(beta, chi)), pmf);
      if (signe(p1))
      {
	chib = NULL;
	vn = ggval(p1, p);
	eq = (long)(vn / N);
	er = (long)(vn*Ea/N - eq*Ea);
      }
      else
      {
	chib = mycaract(chi, beta, NULL, NULL, ns);
	vstar(p, chib, &L, &E);
	eq = (long)(L / E);
	er = (long)(L*Ea / E - eq*Ea);
      }

      /* eq and er are such that gamma = beta.p^-eq.nu^-er is a unit */
      if (eq) gamm = gdiv(beta, gpowgs(p, eq)); else gamm = beta;
      if (er)
      {
	/* kappa = nu^-1 in Zp[alpha] */
	if (!kapp)
	{
	  kapp = QX_invmod(nu, chi);
	  kapp = redelt(kapp, pmr, pmf);
	  kapp = gmodulcp(kapp, chi);
	}
	gamm = lift(gmul(gamm, gpowgs(kapp, er)));
	gamm = redelt(gamm, p, pmf);
      }

      if (DEBUGLEVEL >= 6)
	fprintferr("  gamma = %Z\n", gamm);

      if (er || !chib)
	chig = mycaract(chi, gamm, p, pmf, ns);
      else
      {
	chig = poleval(chib, gmul(polx[v], gpowgs(p, eq)));
	chig = gdiv(chig, gpowgs(p, N*eq));
	chig = polmodi(chig, pmf);
      }

      if (!chig || !gcmp1(Q_denom(chig)))
      {
	/* Valuation of beta was wrong. This means that
	   gamma fails the v*-test */
	chib = mycaract(chi, beta, p, NULL, ns);
	vstar(p, chib, &L, &E);
	eq = (long)(-L / E);
	er = (long)(-L*Ea / E - eq*Ea);

	if (eq) gamm = gmul(beta, gpowgs(p, eq)); else gamm = beta;
	if (er)
	{
	  gamm = gmul(gamm, gpowgs(nu, er));
	  gamm = gmod(gamm, chi);
	  gamm = redelt(gamm, p, pmr);
	}
	chig = mycaract(chi, gamm, p, pmf, ns);
      }

      nug  = (GEN)factmod0(chig, p)[1];
      l    = lg(nug) - 1;
      nug  = (GEN)nug[l];

      if (l > 1)
      {
	/* there are at least 2 factors mod. p => chi can be split */
	phi  = RX_RXQ_compo(gamm, alph, fx);
	phi  = redelt(phi, p, pmf);
	if (flag) mf += 3;
        return Decomp(p, fx, mf, phi, chig, nug, flag);
      }

      Fg = degpol(nug);
      if (Fa%Fg)
      {
	if (DEBUGLEVEL >= 5)
	  fprintferr("  Increasing Fa\n");
	/* we compute a new element such F = lcm(Fa, Fg) */
	w = testb2(p, chi, Fa, gamm, pmf, Fg, ns);
	if (gcmp1((GEN)w[1]))
	{
	  /* there are at least 2 factors mod. p => chi can be split */
	  phi = RX_RXQ_compo((GEN)w[2], alph, fx);
	  phi = redelt(phi, p, pmf);
          if (flag) mf += 3;
          return Decomp(p, fx, mf, phi, (GEN)w[3], (GEN)w[4], flag);
	}
	break;
      }

      /* we look for a root delta of nug in Fp[alpha] such that
	 vp(gamma - delta) > 0. This root can then be used to
	 improved the approximation given by beta */
      nv = fetch_var();
      w = Fp_factor_irred(nug, p, gsubst(nu, varn(nu), polx[nv]));
      if (degpol(w[1]) != 1)
        err(talker,"bug in nilord (no root). Is p = %Z a prime ?", p);

      for (i = 1;; i++)
      {
	if (i >= lg(w))
          err(talker, "bug in nilord (no root), is p = %Z a prime?", p);
        delt = gneg_i(gsubst(gcoeff(w, 2, i), nv, polx[v]));
        eta  = gsub(gamm, delt);	
        if (typ(delt) == t_INT)
        {
          chie = poleval(chig, gadd(polx[v], delt));
          nue  = (GEN)factmod0(chie, p)[1];
          l    = lg(nue) - 1;
          nue  = (GEN)nue[l];
        }
        else
        {
          p1   = factcp(p, chi, eta, pmf, ns);
          chie = (GEN)p1[1];
          nue  = (GEN)p1[2];
          l    = itos((GEN)p1[3]);
        }
        if (l > 1)
        {
          /* there are at least 2 factors mod. p => chi can be split */
          (void)delete_var();
          phi = RX_RXQ_compo(eta, alph, fx);
          phi = redelt(phi, p, pmf);
          if (flag) mf += 3;
          return Decomp(p, fx, mf, phi, chie, nue, flag);
        }

        /* if vp(eta) = vp(gamma - delta) > 0 */
        if (gegal(nue, polx[v])) break;
      }
      (void)delete_var();

      if (!signe(modii(constant_term(chie), pmr)))
	chie = mycaract(chi, eta, p, pmf, ns);
	
      pie = getprime(p, chi, eta, chie, nue, &Le, &Ee);
      if (Ea%Ee)
      {
	if (DEBUGLEVEL >= 5)
	  fprintferr("  Increasing Ea\n");
	pie = redelt(pie, p, pmf);
	/* we compute a new element such E = lcm(Ea, Ee) */	
	w = testc2(p, chi, pmr, pmf, nu, Ea, pie, Ee, ns);
	if (gcmp1((GEN)w[1]))
	{
	  /* there are at least 2 factors mod. p => chi can be split */
	  phi = RX_RXQ_compo((GEN)w[2], alph, fx);
	  phi = redelt(phi, p, pmf);
          if (flag) mf += 3;
          return Decomp(p, fx, mf, phi, (GEN)w[3], (GEN)w[4], flag);
	}
	break;
      }

      if (eq) delt = gmul(delt, gpowgs(p, eq));
      if (er) delt = gmul(delt, gpowgs(nu, er));
      beta = gsub(beta, delt);
    }

    /* we replace alpha by a new alpha with a larger F or E */
    alph = RX_RXQ_compo((GEN)w[2], alph, fx);
    chi  = (GEN)w[3];
    nu   = (GEN)w[4];

    w = update_alpha(p, fx, alph, chi, pmr, pmf, mf, ns);
    alph = (GEN)w[1];
    chi  = (GEN)w[2];
    pmr  = (GEN)w[3];
    pdr  = (GEN)w[4];

    /* that can happen if p does not divide the field discriminant! */
    if (is_pm1(pmr))
    {
      if (flag)
      {
	p1 = (GEN)factmod0(chi, p)[1];
	l  = lg(p1) - 1;
	if (l == 1) return NULL;
	phi = redelt(alph, p, pmf);
	return Decomp(p, fx, ggval(pmf, p), phi, chi, (GEN)p1[l], flag);
      }
      else
	return dbasis(p, fx, mf, alph, chi);
    }
  }
}

/* Returns [1,phi,chi,nu] if phi non-primary
 *         [2,phi,chi,nu] with F_phi = lcm (F_alpha, F_theta)
 *                         and E_phi = E_alpha
 */
static GEN
testb2(GEN p, GEN fa, long Fa, GEN theta, GEN pmf, long Ft, GEN ns)
{
  long Dat, v = varn(fa);
  ulong t, m;
  GEN b, w, phi, h;

  Dat = clcm(Fa, Ft) + 3;
  b = cgetg(5, t_VEC);
  m = p[2];
  if (degpol(p) > 0 || ((long)m) < 0) m = 0;

  for (t = 1;; t++)
  {
    h = m? stopoly(t, m, v): scalarpol(utoi(t), v);
    phi = gadd(theta, gmod(h, fa));
    w = factcp(p, fa, phi, pmf, ns);
    h = (GEN)w[3];
    if (h[2] > 1) { b[1] = un; break; }
    if (lg(w[2]) == Dat) { b[1] = deux; break; }
  }

  b[2] = (long)phi;
  b[3] = w[1];
  b[4] = w[2];
  return b;
}

/* Returns [1, phi, chi, nu] if phi non-primary
 *         [2, phi, chi, nu] if E_phi = lcm (E_alpha, E_theta)
 */
static GEN
testc2(GEN p, GEN fa, GEN pmr, GEN pmf, GEN alph2, long Ea, GEN thet2,
       long Et, GEN ns)
{
  GEN b, c1, c2, c3, psi, phi, w, h;
  long r, s, t, v = varn(fa);

  b=cgetg(5, t_VEC);

  (void)cbezout(Ea, Et, &r, &s); t = 0;
  while (r < 0) { r = r + Et; t++; }
  while (s < 0) { s = s + Ea; t++; }

  c1 = lift_intern(gpowgs(gmodulcp(alph2, fa), s));
  c2 = lift_intern(gpowgs(gmodulcp(thet2, fa), r));
  c3 = gdiv(gmod(gmul(c1, c2), fa), gpowgs(p, t));

  psi = redelt(c3, pmr, pmr);
  phi = gadd(polx[v], psi);

  w = factcp(p, fa, phi, pmf, ns);
  h = (GEN)w[3];
  b[1] = (h[2] > 1)? un: deux;
  b[2] = (long)phi;
  b[3] = w[1];
  b[4] = w[2];
  return b;
}

/*******************************************************************/
/*                                                                 */
/*    2-ELT REPRESENTATION FOR PRIME IDEALS (dividing index)       */
/*                                                                 */
/*******************************************************************/
/* to compute norm of elt in algtobasis form */
typedef struct {
  long r1;
  GEN M;  /* via norm_by_embed */

  GEN D, w, T; /* via resultant if M = NULL */
} norm_S;

static GEN
get_norm(norm_S *S, GEN a)
{
  if (S->M)
  {
    long e;
    GEN N = grndtoi( norm_by_embed(S->r1, gmul(S->M, a)), &e );
    if (e > -5) err(precer, "get_norm");
    return N;
  }
  if (S->w) a = gmul(S->w, a);
  return ZX_resultant_all(S->T, a, S->D, 0);
}

/* q = p^(f+1). a/D in pr | p, norm(pr) = pf.
 * Return 1 if (a/D,p) = pr, and 0 otherwise */
static int
is_uniformizer(GEN a, GEN q, norm_S *S)
{
  return (resii(get_norm(S,a), q) != gzero);
}

/* return x * y, x, y are t_MAT (Fp-basis of in O_K/p), assume (x,y)=1.
 * x or y may be NULL (= ok), not both */
static GEN
mul_intersect(GEN x, GEN y, GEN p)
{
  if (!x) return y;
  if (!y) return x;
  return FpM_intersect(x, y, p);
}

static GEN
Fp_basis(GEN nf, GEN pr)
{
  long i, j, l;
  GEN x, y;
  if (typ(pr) == t_MAT) return pr;
  x = prime_to_ideal(nf, pr);
  l = lg(x);
  y = cgetg(l, t_MAT);
  for (i=j=1; i<l; i++)
    if (gcmp1(gcoeff(x,i,i))) y[j++] = x[i];
  setlg(y, j); return y;
}

static GEN
get_LV(GEN nf, GEN L, GEN p, long N)
{
  long i, l = lg(L)-1;
  GEN LV, LW, A, B;

  LV = cgetg(l+1, t_VEC);
  if (l == 1) { LV[1] = (long)idmat(N); return LV; }
  LW = cgetg(l+1, t_VEC);
  for (i=1; i<=l; i++) LW[i] = (long)Fp_basis(nf, (GEN)L[i]);

  /* A[i] = L[1]...L[i-1], i = 2..l */
  A = cgetg(l+1, t_VEC); A[1] = 0;
  for (i=1; i < l; i++) A[i+1] = (long)mul_intersect((GEN)A[i], (GEN)LW[i], p);
  /* B[i] = L[i+1]...L[l], i = 1..(l-1) */
  B = cgetg(l+1, t_VEC); B[l] = 0;
  for (i=l; i>=2; i--)  B[i-1] = (long)mul_intersect((GEN)B[i], (GEN)LW[i], p);
  for (i=1; i<=l; i++) LV[i] = (long)mul_intersect((GEN)A[i], (GEN)B[i], p);
  return LV;
}

static void
errprime(GEN p) { err(talker, "primedec: %Z is not prime", p); }

/* P = Fp-basis (over O_K/p) for pr.
 * V = Z-basis for I_p/pr. ramif != 0 iff some pr|p is ramified.
 * Return a p-uniformizer for pr. */
static GEN
uniformizer(GEN nf, norm_S *S, GEN P, GEN V, GEN p, int ramif)
{
  long i, l, f, m = lg(P)-1, N = degpol(nf[1]);
  GEN u, Mv, x, q;

  if (!m) return gscalcol_i(p,N);
  /* we want v_p(Norm(x)) = p^f, f = N-m */
  f = N - m;
  q = mulii(gpowgs(p,f), p);

  u = FpM_invimage(concatsp(P, V), vec_ei(N,1), p);
  setlg(u, lg(P));
  u = centermod(gmul(P, u), p);
  if (is_uniformizer(u, q, S)) return u;
  if (signe(u[1]) <= 0) /* make sure u[1] in ]-p,p] */
    u[1] = laddii((GEN)u[1], p); /* try u + p */
  else
    u[1] = lsubii((GEN)u[1], p); /* try u - p */
  if (!ramif || is_uniformizer(u, q, S)) return u;

  /* P/p ramified, u in P^2, not in Q for all other Q|p */
  Mv = eltmul_get_table(nf, unnf_minus_x(u));
  l = lg(P);
  for (i=1; i<l; i++)
  {
    x = centermod(gadd(u, gmul(Mv, (GEN)P[i])), p);
    if (is_uniformizer(x, q, S)) return x;
  }
  errprime(p);
  return NULL; /* not reached */
}

static void
init_norm(norm_S *S, GEN nf, GEN p)
{
  GEN T = (GEN)nf[1];
  long N = degpol(T);

  S->M = NULL;
  if (typ(nf[5]) == t_VEC) /* beware dummy nf from padicff */
  {
    GEN M = gmael(nf,5,1);
    long ex = gexpo(M) + gexpo(mulsi(8 * N, p));
    if (N * ex <= bit_accuracy(gprecision(M)))
    { /* enough prec to use norm_by_embed */
      S->M = M;
      S->r1 = nf_get_r1(nf);
    }
  }
  if (!S->M)
  {
    GEN a, D, Dp, w = Q_remove_denom((GEN)nf[7], &D);
    long i;
    if (D)
    {
      long v = pvaluation(D, p, &a);
      D = gpowgs(p, v);
      Dp = mulii(D, p);
    } else {
      w = dummycopy(w);
      Dp = p;
    }
    for (i=1; i<=N; i++) w[i] = (long)FpX_red((GEN)w[i], Dp);
    S->D = D;
    S->w = w;
    S->T = T;
  }
}

/* Assuming P = (p,u) prime, return tau such that p Z + tau Z = p P^(-1)*/
static GEN
anti_uniformizer(GEN nf, GEN p, GEN u)
{
  pari_sp av = avma;
  GEN mat = eltmul_get_table(nf, u);
  return gerepileupto(av, FpM_deplin(mat,p));
}

/*******************************************************************/
/*                                                                 */
/*                   BUCHMANN-LENSTRA ALGORITHM                    */
/*                                                                 */
/*******************************************************************/

/* pr = (p,u) of ramification index e */
GEN
apply_kummer(GEN nf,GEN u,GEN e,GEN p)
{
  GEN t, T = (GEN)nf[1], pr = cgetg(6,t_VEC);
  long f = degpol(u), N = degpol(T);

  pr[1] = (long)p;
  pr[3] = (long)e;
  pr[4] = lstoi(f);
  if (f == N) /* inert */
  {
    pr[2] = (long)gscalcol_i(p,N);
    pr[5] = (long)gscalcol_i(gun,N);
  }
  else
  { /* make sure v_pr(u) = 1 (automatic if e>1) */
    if (is_pm1(e))
    {
      norm_S S;
      S.D = S.w = S.M = NULL; S.T = T;
      if (!is_uniformizer(u, gpowgs(p,f+1), &S)) u[2] = laddii((GEN)u[2], p);  
    }
    t = algtobasis_i(nf, FpX_div(T,u,p));
    pr[2] = (long)algtobasis_i(nf,u);
    pr[5] = (long)centermod(t, p);
  }
  return pr;
}

/* return a Z basis of Z_K's p-radical, phi = x--> x^p-x */
static GEN
pradical(GEN nf, GEN p, GEN *phi)
{
  long i,N = degpol(nf[1]);
  GEN q,m,frob,rad;

  /* matrix of Frob: x->x^p over Z_K/p */
  frob = cgetg(N+1,t_MAT);
  for (i=1; i<=N; i++)
    frob[i] = (long)element_powid_mod_p(nf,i,p, p);

  m = frob; q = p;
  while (cmpis(q,N) < 0) { q = mulii(q,p); m = FpM_mul(m, frob, p); }
  rad = FpM_ker(m, p); /* m = Frob^k, s.t p^k >= N */
  for (i=1; i<=N; i++)
    coeff(frob,i,i) = lsubis(gcoeff(frob,i,i), 1);
  *phi = frob; return rad;
}

/* return powers of a: a^0, ... , a^d,  d = dim A */
static GEN
get_powers(GEN mul, GEN p)
{
  long i, d = lg(mul[1]);
  GEN z, pow = cgetg(d+2,t_MAT), P = pow+1;

  P[0] = (long)gscalcol_i(gun, d-1);
  z = (GEN)mul[1];
  for (i=1; i<=d; i++)
  {
    P[i] = (long)z; /* a^i */
    if (i!=d) z = FpM_FpV_mul(mul, z, p);
  }
  return pow;
}

/* minimal polynomial of a in A (dim A = d).
 * mul = multiplication table by a in A */
static GEN
pol_min(GEN mul, GEN p)
{
  pari_sp av = avma;
  GEN z, pow = get_powers(mul, p);
  z = FpM_deplin(pow, p);
  if (!z) errprime(p);
  return gerepileupto(av, gtopolyrev(z,0));
}

static GEN
get_pr(GEN nf, norm_S *S, GEN p, GEN P, GEN V, int ramif)
{
  GEN pr, u, t;
  long e, f;
  pari_sp av;

  if (typ(P) == t_VEC) return P; /* already done (Kummer) */

  av = avma;
  u = gerepilecopy(av, uniformizer(nf, S, P, V, p, ramif));
  t = anti_uniformizer(nf,p,u);
  if (!t) errprime(p);
  av = avma;
  e = ramif? 1 + int_elt_val(nf,t,p,t,NULL): 1;
  f = degpol(nf[1]) - (lg(P)-1);
  avma = av;
  pr = cgetg(6,t_VEC);
  pr[1] = (long)p;
  pr[2] = (long)u;
  pr[3] = lstoi(e);
  pr[4] = lstoi(f);
  pr[5] = (long)t; return pr;
}

/* prime ideal decomposition of p */
static GEN
_primedec(GEN nf, GEN p)
{
  long i, k, c, iL, N;
  GEN ex, F, L, Ip, H, phi, mat1, T, f, g, h, p1, UN;

  if (DEBUGLEVEL>2) (void)timer2();
  nf = checknf(nf); T = (GEN)nf[1];
  F = factmod(T,p);
  ex = (GEN)F[2];
  F  = (GEN)F[1]; F = centerlift(F);
  if (DEBUGLEVEL>5) msgtimer("factmod");

  k = lg(F);
  if (k == 1) errprime(p);
  if (signe(modii((GEN)nf[4],p))) /* p doesn't divide index */
  {
    L = cgetg(k,t_VEC);
    for (i=1; i<k; i++)
      L[i] = (long)apply_kummer(nf,(GEN)F[i],(GEN)ex[i],p);
    if (DEBUGLEVEL>5) msgtimer("simple primedec");
    return L;
  }

  g = (GEN)F[1];
  for (i=2; i<k; i++) g = FpX_mul(g,(GEN)F[i], p);
  h = FpX_div(T,g,p);
  f = FpX_red(gdivexact(gsub(gmul(g,h), T), p), p);

  N = degpol(T);
  L = cgetg(N+1,t_VEC); iL = 1;
  for (i=1; i<k; i++)
    if (is_pm1(ex[i]) || signe(FpX_rem(f,(GEN)F[i],p)))
      L[iL++] = (long)apply_kummer(nf,(GEN)F[i],(GEN)ex[i],p);
    else /* F[i] | (f,g,h), happens at least once by Dedekind criterion */
      ex[i] = 0;
  if (DEBUGLEVEL>2) msgtimer("%ld Kummer factors", iL-1);

  /* phi matrix of x -> x^p - x in algebra Z_K/p */
  Ip = pradical(nf,p,&phi);
  if (DEBUGLEVEL>2) msgtimer("pradical");

  /* split etale algebra Z_K / (p,Ip) */
  h = cgetg(N+1,t_VEC);
  if (iL > 1)
  { /* split off Kummer factors */
    GEN mulbeta, beta = NULL;
    for (i=1; i<k; i++)
      if (!ex[i]) beta = beta? FpX_mul(beta, (GEN)F[i], p): (GEN)F[i];
    if (!beta) errprime(p);
    beta = FpV_red(algtobasis_i(nf,beta), p);

    mulbeta = FpM_red(eltmul_get_table(nf, beta), p);
    p1 = concatsp(mulbeta, Ip);
    /* Fp-base of ideal (Ip, beta) in ZK/p */
    h[1] = (long)FpM_image(p1, p);
  }
  else
    h[1] = (long)Ip;

  UN = gscalcol(gun, N);
  for (c=1; c; c--)
  { /* Let A:= (Z_K/p) / Ip; try to split A2 := A / Im H ~ Im M2
       H * ? + M2 * Mi2 = Id_N ==> M2 * Mi2 projector A --> A2 */
    GEN M, Mi, M2, Mi2, phi2;
    long dim;

    H = (GEN)h[c]; k = lg(H)-1;
    M   = FpM_suppl(concatsp(H,UN), p);
    Mi  = FpM_inv(M, p);
    M2  = vecextract_i(M, k+1,N); /* M = (H|M2) invertible */
    Mi2 = rowextract_i(Mi,k+1,N);
    /* FIXME: FpM_mul(,M2) could be done with vecextract_p */
    phi2 = FpM_mul(Mi2, FpM_mul(phi,M2, p), p);
    mat1 = FpM_ker(phi2, p);
    dim = lg(mat1)-1; /* A2 product of 'dim' fields */
    if (dim > 1)
    { /* phi2 v = 0 <==> a = M2 v in Ker phi */
      GEN I,R,r,a,mula,mul2, v = (GEN)mat1[2];
      long n;

      a = FpM_FpV_mul(M2,v, p);
      mula = FpM_red(eltmul_get_table(nf, a), p);
      mul2 = FpM_mul(Mi2, FpM_mul(mula,M2, p), p);
      R = rootmod(pol_min(mul2,p), p); /* totally split mod p */

      n = lg(R)-1;
      for (i=1; i<=n; i++)
      {
        r = lift_intern((GEN)R[i]);
        I = gaddmat_i(negi(r), mula);
	h[c++] = (long)FpM_image(concatsp(H, I), p);
      }
      if (n == dim)
        for (i=1; i<=n; i++) { H = (GEN)h[--c]; L[iL++] = (long)H; }
    }
    else /* A2 field ==> H maximal, f = N-k = dim(A2) */
      L[iL++] = (long)H;
  }
  if (DEBUGLEVEL>2) msgtimer("splitting %ld factors",iL-1);
  setlg(L, iL);
{
  GEN Lpr = cgetg(iL, t_VEC);
  GEN LV = get_LV(nf, L,p,N);
  int ramif = divise((GEN)nf[3], p);
  norm_S S; init_norm(&S, nf, p);
  for (i=1; i<iL; i++)
    Lpr[i] = (long)get_pr(nf, &S, p, (GEN)L[i], (GEN)LV[i], ramif);
  if (DEBUGLEVEL>2) msgtimer("finding uniformizers");
  return Lpr;
}
}

GEN
primedec(GEN nf, GEN p)
{
  pari_sp av = avma;
  return gerepileupto(av, gen_sort(_primedec(nf,p), 0, cmp_prime_over_p));
}

/* return [Fp[x]: Fp] */
static long
ffdegree(GEN x, GEN frob, GEN p)
{
  pari_sp av = avma;
  long d, f = lg(frob)-1;
  GEN y = x;

  for (d=1; d < f; d++)
  {
    y = FpM_FpV_mul(frob, y, p);
    if (gegal(y, x)) break;
  }
  avma = av; return d;
}

static GEN
lift_to_zk(GEN v, GEN c, long N)
{
  GEN w = zerocol(N);
  long i, l = lg(c);
  for (i=1; i<l; i++) w[c[i]] = v[i];
  return w;
}

/* return integral x = 0 mod p/pr^e, (x,pr) = 1.
 * Don't reduce mod p here: caller may need result mod pr^k */
GEN
special_anti_uniformizer(GEN nf, GEN pr)
{
  GEN p = (GEN)pr[1], e = (GEN)pr[3];
  return gdivexact(element_pow(nf,(GEN)pr[5],e), gpowgs(p,itos(e)-1));
}

/* return t = 1 mod pr, t = 0 mod p / pr^e(pr/p) */
static GEN
anti_uniformizer2(GEN nf, GEN pr)
{
  GEN p = (GEN)pr[1], z;
  z = gmod(special_anti_uniformizer(nf, pr), p);
  z = hnfmodid(eltmul_get_table(nf, z), p);
  z = idealaddtoone_i(nf, pr, z);
  return unnf_minus_x(z);
}

#define mpr_TAU 1
#define mpr_FFP 2
#define mpr_PR  3
#define mpr_T   4
#define mpr_NFP 5
#define SMALLMODPR 4
#define LARGEMODPR 6
static GEN
modpr_TAU(GEN modpr)
{
  GEN tau = (GEN)modpr[mpr_TAU];
  if (typ(tau) == t_INT && signe(tau) == 0) tau = NULL;
  return tau;
}

/* prh = HNF matrix, which is identity but for the first line. Return a
 * projector to ZK / prh ~ Z/prh[1,1] */
GEN
dim1proj(GEN prh)
{
  long i, N = lg(prh)-1;
  GEN ffproj = cgetg(N+1, t_VEC);
  GEN x, q = gcoeff(prh,1,1);
  ffproj[1] = un;
  for (i=2; i<=N; i++)
  {
    x = gcoeff(prh,1,i);
    if (signe(x)) x = subii(q,x);
    ffproj[i] = (long)x;
  }
  return ffproj;
}

/* p not necessarily prime, but coprime to denom(basis) */
GEN
get_proj_modT(GEN basis, GEN T, GEN p)
{
  long i, l = lg(basis), f = degpol(T);
  GEN z = cgetg(l, t_MAT);
  for (i = 1; i < l; i++)
  {
    GEN cx, w = (GEN)basis[i];
    if (typ(w) != t_INT)
    {
      w = Q_primitive_part(w, &cx);
      w = FpX_rem(w, T, p);
      if (cx)
      {
        cx = gmod(cx, p);
        w = FpX_Fp_mul(w, cx, p);
      }
    }
    z[i] = (long)pol_to_vec(w, f); /* w_i mod (T,p) */
  }
  return z;
}

static GEN
modprinit(GEN nf, GEN pr, int zk)
{
  pari_sp av = avma;
  GEN res, tau, mul, x, p, T, pow, ffproj, nfproj, prh, c, gf;
  long N, i, k, f;

  nf = checknf(nf); checkprimeid(pr);
  gf = (GEN)pr[4];
  f = itos(gf);
  N = degpol(nf[1]);
  prh = prime_to_ideal(nf, pr);
  tau = zk? gzero: anti_uniformizer2(nf, pr);
  p = (GEN)pr[1];

  if (f == 1)
  {
    res = cgetg(SMALLMODPR, t_COL);
    res[mpr_TAU] = (long)tau;
    res[mpr_FFP] = (long)dim1proj(prh);
    res[mpr_PR ] = (long)pr; return gerepilecopy(av, res);
  }

  c = cgetg(f+1, t_VECSMALL);
  ffproj = cgetg(N+1, t_MAT);
  for (k=i=1; i<=N; i++)
  {
    x = gcoeff(prh, i,i);
    if (!is_pm1(x)) { c[k] = i; ffproj[i] = (long)vec_ei(N, i); k++; }
    else
      ffproj[i] = lneg((GEN)prh[i]);
  }
  ffproj = rowextract_p(ffproj, c);
  if (! divise((GEN)nf[4], p))
  {
    GEN basis = (GEN)nf[7];
    if (N == f) T = (GEN)nf[1]; /* pr inert */
    else
    {
      T = Q_primpart(gmul(basis, (GEN)pr[2]));
      basis = vecextract_p(basis, c);
    }
    ffproj = FpM_mul(get_proj_modT(basis, T, p), ffproj, p);

    res = cgetg(SMALLMODPR+1, t_COL);
    res[mpr_TAU] = (long)tau;
    res[mpr_FFP] = (long)ffproj;
    res[mpr_PR ] = (long)pr;
    res[mpr_T  ] = (long)T; return gerepilecopy(av, res);
  }

  if (isprime(gf))
  {
    mul = eltmulid_get_table(nf, c[2]);
    mul = vecextract_p(mul, c);
  }
  else
  {
    GEN v, u, u2, frob;
    long deg,deg1,deg2;

    /* matrix of Frob: x->x^p over Z_K/pr = < w[c1], ..., w[cf] > over Fp */
    frob = cgetg(f+1, t_MAT);
    for (i=1; i<=f; i++)
    {
      x = element_powid_mod_p(nf,c[i],p, p);
      frob[i] = (long)FpM_FpV_mul(ffproj, x, p);
    }
    u = vec_ei(f,2); k = 2;
    deg1 = ffdegree(u, frob, p);
    while (deg1 < f)
    {
      k++; u2 = vec_ei(f, k);
      deg2 = ffdegree(u2, frob, p);
      deg = clcm(deg1,deg2);
      if (deg == deg1) continue;
      if (deg == deg2) { deg1 = deg2; u = u2; continue; }
      u = gadd(u, u2);
      while (ffdegree(u, frob, p) < deg) u = gadd(u, u2);
      deg1 = deg;
    }
    v = lift_to_zk(u,c,N);

    mul = cgetg(f+1,t_MAT);
    mul[1] = (long)v; /* assume w_1 = 1 */
    for (i=2; i<=f; i++) mul[i] = (long)element_mulid(nf,v,c[i]);
  }

  /* Z_K/pr = Fp(v), mul = mul by v */
  mul = FpM_red(mul, p);
  mul = FpM_mul(ffproj, mul, p);

  pow = get_powers(mul, p);
  T = gtopolyrev(FpM_deplin(pow, p), varn(nf[1]));
  nfproj = cgetg(f+1, t_MAT);
  for (i=1; i<=f; i++) nfproj[i] = (long)lift_to_zk((GEN)pow[i], c, N);
  nfproj = gmul((GEN)nf[7], nfproj);

  setlg(pow, f+1);
  ffproj = FpM_mul(FpM_inv(pow, p), ffproj, p);

  res = cgetg(LARGEMODPR, t_COL);
  res[mpr_TAU] = (long)tau;
  res[mpr_FFP] = (long)ffproj;
  res[mpr_PR ] = (long)pr;
  res[mpr_T  ] = (long)T;
  res[mpr_NFP] = (long)nfproj; return gerepilecopy(av, res);
}

GEN
nfmodprinit(GEN nf, GEN pr) { return modprinit(nf, pr, 0); }
GEN
zkmodprinit(GEN nf, GEN pr) { return modprinit(nf, pr, 1); }

void
checkmodpr(GEN modpr)
{
  if (typ(modpr) != t_COL || lg(modpr) < SMALLMODPR)
    err(talker,"incorrect modpr format");
  checkprimeid((GEN)modpr[mpr_PR]);
}


static GEN
to_ff_init(GEN nf, GEN *pr, GEN *T, GEN *p, int zk)
{
  GEN modpr = (typ(*pr) == t_COL)? *pr: modprinit(nf, *pr, zk);
  *T = lg(modpr)==SMALLMODPR? NULL: (GEN)modpr[mpr_T];
  *pr = (GEN)modpr[mpr_PR];
  *p = (GEN)(*pr)[1]; return modpr;
}
GEN
nf_to_ff_init(GEN nf, GEN *pr, GEN *T, GEN *p) {
  GEN modpr = to_ff_init(nf,pr,T,p,0);
  GEN tau = modpr_TAU(modpr);
  if (!tau) modpr[mpr_TAU] = (long)anti_uniformizer2(nf, *pr);
  return modpr;
}
GEN
zk_to_ff_init(GEN nf, GEN *pr, GEN *T, GEN *p) {
  return to_ff_init(nf,pr,T,p,1);
}

/* assume x in 'basis' form (t_COL) */
GEN
zk_to_ff(GEN x, GEN modpr)
{
  GEN pr = (GEN)modpr[mpr_PR];
  GEN p = (GEN)pr[1];
  GEN y = gmul((GEN)modpr[mpr_FFP], x);
  if (lg(modpr) == SMALLMODPR) return modii(y,p);
  y = FpV_red(y, p);
  return col_to_ff(y, varn(modpr[mpr_T]));
}

/* REDUCTION Modulo a prime ideal */

/* assume x in t_COL form, v_pr(x) >= 0 */
static GEN
kill_denom(GEN x, GEN nf, GEN p, GEN modpr)
{
  GEN cx, den = denom(x);
  long v;
  if (gcmp1(den)) return x;

  v = ggval(den,p);
  if (v) 
  {
    GEN tau = modpr_TAU(modpr);
    if (!tau) err(talker,"modpr initialized for integers only!");
    x = element_mul(nf,x, element_pow(nf,tau,stoi(v)));
  }
  x = Q_primitive_part(x, &cx);
  x = FpV_red(x, p);
  if (cx) x = FpV_red(gmul(gmod(cx, p), x), p);
  return x;
}

/* x integral, reduce mod prh in HNF */
GEN
nfreducemodpr_i(GEN x, GEN prh)
{
  GEN p = gcoeff(prh,1,1);
  long i,j;

  x = dummycopy(x);
  for (i=lg(x)-1; i>=2; i--)
  {
    GEN t = (GEN)prh[i], p1 = resii((GEN)x[i], p);
    x[i] = (long)p1;
    if (signe(p1) && is_pm1(t[i]))
    {
      for (j=1; j<i; j++)
        x[j] = lsubii((GEN)x[j], mulii(p1, (GEN)t[j]));
      x[i] = zero;
    }
  }
  x[1] = lresii((GEN)x[1], p); return x;
}

GEN
nfreducemodpr(GEN nf, GEN x, GEN modpr)
{
  pari_sp av = avma;
  long i;
  GEN pr, p;

  checkmodpr(modpr);
  pr = (GEN)modpr[mpr_PR];
  p = (GEN)pr[1];
  x = _algtobasis(nf,x);
  for (i=lg(x)-1; i>0; i--)
    if (typ(x[i]) == t_INTMOD) { x = lift(x); break; }
  x = kill_denom(x, nf, p, modpr);
  x = ff_to_nf(zk_to_ff(x,modpr), modpr);
  return gerepileupto(av, FpV(_algtobasis(nf,x), p));
}

GEN
nf_to_ff(GEN nf, GEN x, GEN modpr)
{
  pari_sp av = avma;
  GEN pr = (GEN)modpr[mpr_PR];
  GEN p = (GEN)pr[1];
  long t = typ(x);

  if (t == t_POLMOD) { x = (GEN)x[2]; t = typ(x); }
  switch(t)
  {
    case t_INT: return modii(x, p);
    case t_FRAC: return gmod(x, p);
    case t_POL: x = algtobasis(nf, x); break;
    case t_COL: break;
    default: err(typeer,"nf_to_ff");
  }
  x = kill_denom(x, nf, p, modpr);
  return gerepilecopy(av, zk_to_ff(x, modpr));
}

GEN
ff_to_nf(GEN x, GEN modpr)
{
  if (lg(modpr) < LARGEMODPR) return x;
  return mulmat_pol((GEN)modpr[mpr_NFP], x);
}
GEN
modprM_lift(GEN x, GEN modpr)
{
  long i,j,h,l = lg(x);
  GEN y = cgetg(l, t_MAT);
  if (l == 1) return y;

  h = lg(x[1]);
  for (j=1; j<l; j++)
  {
    GEN p1 = cgetg(h,t_COL); y[j] = (long)p1;
    for (i=1; i<h; i++) p1[i]=(long)ff_to_nf(gcoeff(x,i,j), modpr);
  }
  return y;
}
GEN
modprX_lift(GEN x, GEN modpr)
{
  long i, l;
  GEN z;

  if (typ(x)!=t_POL) return gcopy(x); /* scalar */
  l = lg(x); z = cgetg(l, t_POL); z[1] = x[1];
  for (i=2; i<l; i++) z[i] = (long)ff_to_nf((GEN)x[i], modpr);
  return z;
}

/* reduce the coefficients of pol modulo modpr */
GEN
modprX(GEN x, GEN nf,GEN modpr)
{
  long i, l;
  GEN z;

  if (typ(x)!=t_POL) return nf_to_ff(nf,x,modpr);
  l = lg(x); z = cgetg(l,t_POL); z[1] = x[1];
  for (i=2; i<l; i++) z[i] = (long)nf_to_ff(nf,(GEN)x[i],modpr);
  return normalizepol(z);
}
GEN
modprV(GEN z, GEN nf,GEN modpr)
{
  long i,l = lg(z);
  GEN x;
  x = cgetg(l,typ(z));
  for (i=1; i<l; i++) x[i] = (long)nf_to_ff(nf,(GEN)z[i], modpr);
  return x;
}
/* assume z a t_VEC/t_COL/t_MAT */
GEN
modprM(GEN z, GEN nf,GEN modpr)
{
  long i,l = lg(z);
  GEN x;

  if (typ(z) != t_MAT) return modprV(z,nf,modpr);
  x = cgetg(l,t_MAT); if (l==1) return x;
  for (i=1; i<l; i++) x[i] = (long)modprV((GEN)z[i],nf,modpr);
  return x;
}

/*******************************************************************/
/*                                                                 */
/*                       RELATIVE ROUND 2                          */
/*                                                                 */
/*******************************************************************/

static void
fill(long l, GEN H, GEN Hx, GEN I, GEN Ix)
{
  long i;
  if (typ(Ix) == t_VEC) /* standard */
    for (i=1; i<l; i++) { H[i] = Hx[i]; I[i] = Ix[i]; }
  else /* constant ideal */
    for (i=1; i<l; i++) { H[i] = Hx[i]; I[i] = (long)Ix; }
}

/* given MODULES x and y by their pseudo-bases, returns a pseudo-basis of the
 * module generated by x and y. */
static GEN
rnfjoinmodules_i(GEN nf, GEN Hx, GEN Ix, GEN Hy, GEN Iy)
{
  long i, lx, ly;
  GEN H, I, x, z;

  lx = lg(Hx);
  ly = lg(Hy); i = lx+ly-1;
  z = (GEN)gpmalloc(sizeof(long*)*(3+2*i));
  *z = evaltyp(t_VEC)|evallg(3);
  H = z+3; z[1]=(long)H; *H = evaltyp(t_MAT)|evallg(i);
  I = H+i; z[2]=(long)I; *I = evaltyp(t_VEC)|evallg(i);
  fill(lx, H     , Hx, I     , Ix);
  fill(ly, H+lx-1, Hy, I+lx-1, Iy);
  x = nfhermite(nf,z); free(z); return x;
}
static GEN
rnfjoinmodules(GEN nf, GEN x, GEN y)
{
  if (!x) return y;
  if (!y) return x;
  return rnfjoinmodules_i(nf, (GEN)x[1], (GEN)x[2], (GEN)y[1], (GEN)y[2]);
}

typedef struct {
  GEN nf, multab, modpr,T,p;
  long h;
} rnfeltmod_muldata;

static GEN
_mul(void *data, GEN x, GEN y/* base; ignored */)
{
  rnfeltmod_muldata *D = (rnfeltmod_muldata *) data;
  GEN z = x? element_mulid(D->multab,x,D->h)
           : element_mulidid(D->multab,D->h,D->h);
  (void)y;
  return FqV_red(z,D->T,D->p);
}
static GEN
_sqr(void *data, GEN x)
{
  rnfeltmod_muldata *D = (rnfeltmod_muldata *) data;
  GEN z = x? sqr_by_tab(D->multab,x)
           : element_mulidid(D->multab,D->h,D->h);
  return FqV_red(z,D->T,D->p);
}

/* Compute W[h]^n mod pr in the extension, assume n >= 0 */
static GEN
rnfelementid_powmod(GEN multab, long h, GEN n, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN y;
  rnfeltmod_muldata D;

  if (!signe(n)) return gun;

  D.multab = multab;
  D.h = h;
  D.T = T;
  D.p = p;
  y = leftright_pow(NULL, n, (void*)&D, &_sqr, &_mul);
  return gerepilecopy(av, y);
}

#if 0
GEN
mymod(GEN x, GEN p)
{
  long i,lx, tx = typ(x);
  GEN y,p1;

  if (tx == t_INT) return resii(x,p);
  if (tx == t_FRAC)
  {
    p1 = resii((GEN)x[2], p);
    if (p1 != gzero) { cgiv(p1); return gmod(x,p); }
    return x;
  }
  if (!is_matvec_t(tx))
    err(bugparier, "mymod (missing type)");
  lx = lg(x); y = cgetg(lx,tx);
  for (i=1; i<lx; i++) y[i] = (long)mymod((GEN)x[i],p);
  return y;
}
#endif

/* Relative Dedekind criterion over nf, applied to the order defined by a
 * root of irreducible polynomial P, modulo the prime ideal pr. Assume
 * vdisc = v_pr( disc(P) ).
 * Return NULL if nf[X]/P is pr-maximal. Otherwise, return [flag, O, v]:
 *   O = enlarged order, given by a pseudo-basis
 *   flag = 1 iff O is pr-maximal
 *   v = v_pr(disc(O)). */
static GEN
rnfdedekind_i(GEN nf, GEN P, GEN pr, long vdisc)
{
  long vt, r, d, n, m, i, j;
  pari_sp av = avma;
  GEN Prd, A, I, p, tau, g, matid;
  GEN modpr, res, h, k, base, nfT, T, gzk, hzk, prinvp, X, pal;

  P = lift(P);
  nf = checknf(nf); nfT = (GEN)nf[1];
  res = cgetg(4,t_VEC);
  modpr = nf_to_ff_init(nf,&pr, &T, &p);
  tau = gmul((GEN)nf[7], (GEN)pr[5]);
  n = degpol(nfT);
  m = degpol(P);

  Prd = modprX(P, nf, modpr);
  A = (GEN)FqX_factor(Prd,T,p)[1];
  r = lg(A); if (r < 2) err(constpoler,"rnfdedekind");
  g = (GEN)A[1];
  for (i=2; i<r; i++) g = FqX_mul(g, (GEN)A[i], T, p);
  h = FqX_div(Prd,g, T, p);
  gzk = modprX_lift(g, modpr);
  hzk = modprX_lift(h, modpr);

  k = gsub(P, RXQX_mul(gzk,hzk, nfT));
  k = gdiv(RXQX_mul(tau,k,nfT), p);
  k = modprX(k, nf, modpr);
  k  = FqX_gcd(FqX_gcd(g,h,  T,p), k, T,p);
  d = degpol(k);  /* <= m */
  if (!d) return NULL; /* pr-maximal */

  vt = vdisc - 2*d;
  res[3] = lstoi(vt);
  res[1] = vt < 2? un: zero;

  base = cgetg(3,t_VEC);
  A = cgetg(m+d+1,t_MAT); base[1] = (long)A;
  I = cgetg(m+d+1,t_VEC); base[2] = (long)I;
 /* base[2] temporarily multiplied by p, for the final nfhermitemod,
  * which requires integral ideals */
  matid = gscalmat(p, n);
  prinvp = pidealprimeinv(nf,pr); /* again multiplied by p */
  for (j=1; j<=m; j++)
  {
    A[j] = (long)vec_ei(m, j);
    I[j] = (long)matid;
  }
  X = polx[varn(P)];
  pal = FqX_div(Prd,k, T,p);
  pal = modprX_lift(pal, modpr);
  for (   ; j<=m+d; j++)
  {
    A[j] = (long)pol_to_vec(pal,m);
    I[j] = (long)prinvp;
    pal = RXQX_rem(RXQX_mul(pal,X,nfT),P,nfT);
  }
  /* the modulus is integral */
  base = nfhermitemod(nf,base, gmul(gpowgs(p, m-d),
                                    idealpows(nf, prinvp, d)));
  base[2] = ldiv((GEN)base[2], p); /* cancel the factor p */
  res[2] = (long)base; return gerepilecopy(av, res);
}

/* [L:K] = n, [K:Q] = m */
static GEN
triv_order(long n, long m)
{
  GEN I, z = cgetg(3, t_VEC), id = idmat(m);
  long i;
  I = cgetg(n+1,t_VEC); for (i=1; i<=n; i++) I[i] = (long)id;
  z[1] = (long)idmat(n);
  z[2] = (long)I; return z;
}

/* FIXME: is it really necessary to export this routine ? */
GEN
rnfdedekind(GEN nf, GEN P, GEN pr)
{
  pari_sp av = avma;
  long v = element_val(nf, discsr(P), pr);
  GEN z;
  avma = av; z = rnfdedekind_i(nf, P, pr, v);
  if (!z) {
    z = cgetg(4, t_VEC);
    z[1] = un;
    z[2] = (long)triv_order(degpol(P), degpol(nf[1]));
    z[3] = lstoi(v);
  }
  return z;
}

/* return NULL if power order if pr-maximal */
static GEN
rnfordmax(GEN nf, GEN pol, GEN pr, long vdisc)
{
  pari_sp av = avma, av1, lim;
  long i, j, k, n, vpol, cmpt, sep;
  GEN q, q1, p, T, modpr, W, I, MW, C, p1;
  GEN Tauinv, Tau, prhinv, pip, nfT, id, rnfId;

  if (DEBUGLEVEL>1) fprintferr(" treating %Z\n",pr);
  modpr = nf_to_ff_init(nf,&pr,&T,&p);
  p1 = rnfdedekind_i(nf, pol, modpr, vdisc);
  if (!p1) { avma = av; return NULL; }
  if (gcmp1((GEN)p1[1])) return gerepilecopy(av,(GEN)p1[2]);
  sep = itos((GEN)p1[3]);
  W = gmael(p1,2,1);
  I = gmael(p1,2,2);

  pip = basistoalg(nf, (GEN)pr[2]);
  nfT = (GEN)nf[1];
  n = degpol(pol); vpol = varn(pol);
  q = T? gpowgs(p,degpol(T)): p;
  q1 = q; while (cmpis(q1,n) < 0) q1 = mulii(q1,q);
  rnfId = idmat(n);
  id    = idmat(degpol(nfT));

  prhinv = idealinv(nf, pr);
  C = cgetg(n+1, t_MAT);
  for (j=1; j<=n; j++) C[j] = lgetg(n*n+1, t_COL);
  MW = cgetg(n*n+1, t_MAT);
  for (j=1; j<=n*n; j++) MW[j] = lgetg(n+1, t_COL);
  Tauinv = cgetg(n+1, t_VEC);
  Tau    = cgetg(n+1, t_VEC);
  av1 = avma; lim = stack_lim(av1,1);
  for(cmpt=1; ; cmpt++)
  {
    GEN I0 = dummycopy(I), W0 = dummycopy(W), Wa;
    GEN Wainv, Waa;
    GEN Ip, A, Ainv, MWmod, F;
    GEN pseudo, G;
    if (DEBUGLEVEL>1) fprintferr("    %ld%s pass\n",cmpt,eng_ord(cmpt));
    for (j=1; j<=n; j++)
    {
      GEN tau, tauinv;
      long v1, v2;
      if (gegal((GEN)I[j],id)) { Tau[j] = Tauinv[j] = un; continue; }

      p1 = ideal_two_elt(nf,(GEN)I[j]);
      v1 = element_val(nf,(GEN)p1[1],pr);
      v2 = element_val(nf,(GEN)p1[2],pr);
      tau = (v1 > v2)? (GEN)p1[2]: (GEN)p1[1];
      tauinv = element_inv(nf, tau);
      Tau[j]    = (long)tau;
      Tauinv[j] = (long)tauinv;
      W[j] = (long)element_mulvec(nf, tau, (GEN)W[j]);
      I[j] = (long)idealmul(nf,    tauinv, (GEN)I[j]);
    }
    /* W = (Z_K/pr)-basis of O/pr. O = (W0,I0) ~ (W, I) */
    Wa = basistoalg(nf,W);

   /* compute MW: W_i*W_j = sum MW_k,(i,j) W_k */
    Waa = lift_intern(mat_to_vecpol(Wa,vpol));
    Wainv = lift_intern(ginv(Wa));
    for (i=1; i<=n; i++)
      for (j=i; j<=n; j++)
      {
        GEN z = RXQX_rem(gmul((GEN)Waa[i],(GEN)Waa[j]), pol, nfT);
        long tz = typ(z);
        if (is_scalar_t(tz) || (tz == t_POL && varn(z) > vpol))
          z = gmul(z, (GEN)Wainv[1]);
        else
          z = mulmat_pol(Wainv, z);
        for (k=1; k<=n; k++)
        {
          GEN c = gres((GEN)z[k], nfT);
          coeff(MW, k, (i-1)*n+j) = (long)c;
          coeff(MW, k, (j-1)*n+i) = (long)c;
        }
      }

    /* compute Ip =  pr-radical [ could use Ker(trace) if q large ] */
    MWmod = modprM(MW,nf,modpr);
    F = cgetg(n+1, t_MAT); F[1] = rnfId[1];
    for (j=2; j<=n; j++) F[j] = (long)rnfelementid_powmod(MWmod, j, q1, T,p);
    Ip = FqM_ker(F,T,p);
    if (lg(Ip) == 1) { W = W0; I = I0; break; }

    /* Fill C: W_k A_j = sum_i C_(i,j),k A_i */
    A = modprM_lift(FqM_suppl(Ip,T,p), modpr);
    for (j=1; j<lg(Ip); j++)
    {
      p1 = (GEN)A[j];
      for (i=1; i<=n; i++) p1[i] = (long)to_polmod((GEN)p1[i], nfT);
    }
    for (   ; j<=n; j++)
    {
      p1 = (GEN)A[j];
      for (i=1; i<=n; i++) p1[i] = lmul(pip, (GEN)p1[i]);
    }
    Ainv = lift_intern(ginv(A));
    A    = lift_intern(A);
    for (k=1; k<=n; k++)
      for (j=1; j<=n; j++)
      {
        GEN z = gmul(Ainv, gmod(element_mulid(MW, (GEN)A[j],k), nfT));
        for (i=1; i<=n; i++)
        {
          GEN c = gres((GEN)z[i], nfT);
          coeff(C, (j-1)*n+i, k) = (long)nf_to_ff(nf,c,modpr);
        }
      }
    G = modprM_lift(FqM_ker(C,T,p), modpr);

    pseudo = rnfjoinmodules_i(nf, G,prhinv, rnfId,I);
    /* express W in terms of the power basis */
    W = algtobasis(nf, gmul(Wa, basistoalg(nf,(GEN)pseudo[1])));
    I = (GEN)pseudo[2];
    /* restore the HNF property W[i,i] = 1. NB: Wa upper triangular, with
     * Wa[i,i] = Tau[i] */
    for (j=1; j<=n; j++)
      if (Tau[j] != un)
      {
        W[j] = (long)element_mulvec(nf, (GEN)Tauinv[j], (GEN)W[j]);
        I[j] = (long)idealmul(nf,       (GEN)Tau[j],    (GEN)I[j] );
      }
    if (DEBUGLEVEL>3) fprintferr(" new order:\n%Z\n%Z\n", W, I);
    if (sep <= 3 || gegal(I,I0)) break;

    if (low_stack(lim, stack_lim(av1,1)) || (cmpt & 3) == 0)
    {
      if(DEBUGMEM>1) err(warnmem,"rnfordmax");
      gerepileall(av1,2, &W,&I);
    }
  }
  {
    GEN res = cgetg(3,t_VEC);
    res[1] = (long)W;
    res[2] = (long)I; return gerepilecopy(av, res);
  }
}

static void
check_pol(GEN x, long v)
{
  long i,tx, lx = lg(x);
  if (varn(x) != v)
    err(talker,"incorrect variable in rnf function");
  for (i=2; i<lx; i++)
  {
    tx = typ(x[i]);
    if (!is_scalar_t(tx) || tx == t_POLMOD)
      err(talker,"incorrect polcoeff in rnf function");
  }
}

GEN
fix_relative_pol(GEN nf, GEN x, int chk_lead)
{
  GEN xnf = (typ(nf) == t_POL)? nf: (GEN)nf[1];
  long i, vnf = varn(xnf), lx = lg(x);
  if (typ(x) != t_POL || varn(x) >= vnf)
    err(talker,"incorrect polynomial in rnf function");
  x = dummycopy(x);
  for (i=2; i<lx; i++)
    switch(typ(x[i]))
    {
      case t_POL:
        check_pol((GEN)x[i], vnf);
        x[i] = lmodulcp((GEN)x[i], xnf); break;
      case t_POLMOD:
        if (!gegal(gmael(x,i,1), xnf)) err(consister,"rnf function");
        break;
    }

  if (chk_lead && !gcmp1(leading_term(x)))
    err(impl,"non-monic relative polynomials");
  return x;
}

/* determinant of the trace pairing */
static GEN
get_d(GEN nf, GEN pol, GEN A)
{
  long i, j, n = degpol(pol);
  GEN W = mat_to_vecpol(lift_intern(basistoalg(nf,A)), varn(pol));
  GEN T, nfT = (GEN)nf[1], sym = polsym_gen(pol, NULL, n-1, nfT, NULL);
  T = cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++) T[j] = lgetg(n+1,t_COL);
  for (j=1; j<=n; j++)
    for (i=j; i<=n; i++)
    {
      GEN c = RXQX_mul((GEN)W[i],(GEN)W[j], nfT);
      c = RXQX_rem(c, pol, nfT);
      c = simplify_i(quicktrace(c,sym));
      coeff(T,j,i) = coeff(T,i,j) = (long)c;
    }
  return algtobasis_i(nf, det(T));
}

/* nf = base field K
 * pol= monic polynomial, coefficients in Z_K, defining a relative
 *   extension L = K[X]/(pol). One MUST have varn(pol) < varn(nf[1]).
 * Returns a pseudo-basis [A,I] of Z_L, set (D,d) to the relative
 * discriminant, and f to the index-ideal */
GEN
rnfallbase(GEN nf, GEN pol, GEN *pD, GEN *pd, GEN *pf)
{
  long i, n, N, l, *ep;
  GEN p1, A, nfT, P, id, I, z, d, D, disc;

  nf = checknf(nf); nfT = (GEN)nf[1];
  pol = fix_relative_pol(nf,pol,1);
  N = degpol(nfT);
  n = degpol(pol);
  disc = discsr(pol); pol = lift(pol);
  P = idealfactor(nf, disc);
  ep= (long*)P[2];
  P = (GEN)  P[1]; l = lg(P);
  for (i=1; i < l; i++) ep[i] = itos((GEN)ep[i]);
  if (DEBUGLEVEL>1)
  {
    fprintferr("Ideals to consider:\n");
    for (i=1; i < l; i++)
      if (ep[i]>1) fprintferr("%Z^%ld\n",P[i],ep[i]);
    flusherr();
  }
  id = idmat(N); z = NULL;
  for (i=1; i < l; i++)
    if (ep[i] > 1)
    {
      GEN y = rnfordmax(nf, pol, (GEN)P[i], ep[i]);
      z = rnfjoinmodules(nf, z, y);
    }
  if (!z) z = triv_order(n, N);
  A = (GEN)z[1];
  I = (GEN)z[2];
  d = get_d(nf, pol, A);

  i=1; while (i<=n && gegal((GEN)I[i], id)) i++;
  if (i > n) { D = gun; if (pf) *pf = gun; }
  else
  {
    D = (GEN)I[i];
    for (i++; i<=n; i++) D = idealmul(nf,D,(GEN)I[i]);
    if (pf) *pf = idealinv(nf, D);
    D = idealpow(nf,D,gdeux);
  }
  p1 = core2partial(Q_content(d));
  *pd = gdiv(d, sqri((GEN)p1[2]));
  *pD = idealmul(nf,D,d); return z;
}

GEN
rnfpseudobasis(GEN nf, GEN pol)
{
  pari_sp av = avma;
  GEN D, d, y = cgetg(5, t_VEC), z = rnfallbase(nf,pol, &D, &d, NULL);
  y[1] = z[1];
  y[2] = z[2];
  y[3] = (long)D;
  y[4] = (long)d; return gerepilecopy(av, y);
}

GEN
rnfdiscf(GEN nf, GEN pol)
{
  pari_sp av = avma;
  GEN D, d, y = cgetg(3, t_VEC); (void)rnfallbase(nf,pol, &D, &d, NULL);
  y[1] = (long)D;
  y[2] = (long)d; return gerepilecopy(av, y);
}

GEN
gen_if_principal(GEN bnf, GEN x)
{
  pari_sp av = avma;
  GEN z = isprincipalall(bnf,x, nf_GEN_IF_PRINCIPAL | nf_FORCE);
  if (typ(z) == t_INT) { avma = av; return NULL; }
  return z;
}

/* given bnf and a pseudo-basis of an order in HNF [A,I] (or [A,I,D,d] it
 * does not matter), tries to simplify the HNF as much as possible. The
 * resulting matrix will be upper triangular but the diagonal coefficients
 * will not be equal to 1. The ideals are guaranteed to be integral and
 * primitive. */
GEN
rnfsimplifybasis(GEN bnf, GEN x)
{
  pari_sp av = avma;
  long i, l;
  GEN p1, id, Az, Iz, nf, A, I;

  bnf = checkbnf(bnf); nf = (GEN)bnf[7];
  if (typ(x)!=t_VEC || lg(x)<3)
    err(talker,"not a pseudo-basis in nfsimplifybasis");
  x = dummycopy(x);
  A = (GEN)x[1];
  I = (GEN)x[2]; l = lg(I);
  id = idmat(degpol(nf[1]));
  Az = cgetg(l, t_MAT); x[1] = (long)Az;
  Iz = cgetg(l, t_VEC); x[2] = (long)Iz;
  for (i = 1; i < l; i++)
  {
    if (gegal((GEN)I[i],id)) { Iz[i] = (long)id; Az[i] = A[i]; continue; }

    Iz[i] = (long)Q_primitive_part((GEN)I[i], &p1);
    Az[i] = p1? lmul((GEN)A[i],p1): A[i];
    if (p1 && gegal((GEN)Iz[i], id)) continue;

    p1 = gen_if_principal(bnf, (GEN)Iz[i]);
    if (p1)
    {
      Iz[i] = (long)id;
      Az[i] = (long)element_mulvec(nf,p1,(GEN)Az[i]);
    }
  }
  return gerepilecopy(av, x);
}

extern GEN prodid(GEN nf, GEN I);
GEN
rnfdet2(GEN nf, GEN A, GEN I)
{
  pari_sp av = avma;
  GEN p1;
  nf = checknf(nf);
  p1 = idealmul(nf, det(matbasistoalg(nf, A)), prodid(nf, I));
  return gerepileupto(av, p1);
}

GEN
rnfdet(GEN nf, GEN order)
{
  if (typ(order)!=t_VEC || lg(order)<3)
    err(talker,"not a pseudo-matrix in rnfdet");
  return rnfdet2(nf,(GEN)order[1],(GEN)order[2]);
}

GEN
rnfdet0(GEN nf, GEN x, GEN y)
{
  return y? rnfdet2(nf,x,y): rnfdet(nf,x);
}

/* Given two fractional ideals a and b, gives x in a, y in b, z in b^-1,
   t in a^-1 such that xt-yz=1. In the present version, z is in Z. */
static GEN
nfidealdet1(GEN nf, GEN a, GEN b)
{
  pari_sp av = avma;
  GEN x,p1,res,u,v,da,db;

  a = idealinv(nf,a);
  da = denom(a); if (!gcmp1(da)) a = gmul(da,a);
  db = denom(b); if (!gcmp1(db)) b = gmul(db,b);
  x = idealcoprime(nf,a,b);
  p1 = idealaddtoone(nf, idealmul(nf,x,a), b);
  u = (GEN)p1[1];
  v = (GEN)p1[2];

  res = cgetg(5,t_VEC);
  res[1] = (long)gmul(x,da);
  res[2] = (long)gdiv(v,db);
  res[3] = lnegi(db);
  res[4] = (long)element_div(nf, u, (GEN)res[1]);
  return gerepilecopy(av,res);
}

static GEN
get_order(GEN nf, GEN O, char *s)
{
  if (typ(O) == t_POL)
    return rnfpseudobasis(nf, O);
  if (typ(O)!=t_VEC || lg(O) < 3)
    err(talker,"not a pseudo-matrix in %s", s);
  return O;
}

/* given a pseudo-basis of an order in HNF [A,I] (or [A,I,D,d]), gives an
 * n x n matrix (not in HNF) of a pseudo-basis and an ideal vector
 * [id,id,...,id,I] such that order = nf[7]^(n-1) x I.
 * Uses the approximation theorem ==> slow. */
GEN
rnfsteinitz(GEN nf, GEN order)
{
  pari_sp av = avma;
  long i,n,l;
  GEN Id,A,I,p1,a,b;

  nf = checknf(nf);
  Id = idmat(degpol(nf[1]));
  order = get_order(nf, order, "rnfsteinitz");
  A = matalgtobasis(nf, (GEN)order[1]);
  I = dummycopy((GEN)order[2]); n=lg(A)-1;
  if (typ(A) != t_MAT || typ(I) != t_VEC || lg(I) != n+1)
    err(typeer,"rnfsteinitz");
  for (i=1; i<n; i++)
  {
    GEN c1,c2;
    a = (GEN)I[i]; if (gegal(a,Id)) continue;

    c1 = (GEN)A[i];
    c2 = (GEN)A[i+1];
    b = (GEN)I[i+1];
    if (gegal(b,Id))
    {
      A[i]  = (long)c2;
      A[i+1]= lneg(c1);
      I[i]  = (long)b;
      I[i+1]= (long)a;
    }
    else
    {
      p1 = nfidealdet1(nf,a,b);
      A[i]  = ladd(element_mulvec(nf, (GEN)p1[1], c1),
                   element_mulvec(nf, (GEN)p1[2], c2));
      A[i+1]= ladd(element_mulvec(nf, (GEN)p1[3], c1),
                   element_mulvec(nf, (GEN)p1[4], c2));
      I[i]  = (long)Id;
      I[i+1]= (long)Q_primitive_part(idealmul(nf,a,b), &p1);
      if (p1) A[i+1] = (long)element_mulvec(nf, p1,(GEN)A[i+1]);
    }
  }
  l = lg(order);
  p1 = cgetg(l,t_VEC);
  p1[1]=(long)A;
  p1[2]=(long)I; for (i=3; i<l; i++) p1[i]=order[i];
  return gerepilecopy(av, p1);
}

/* Given bnf and either an order as output by rnfpseudobasis or a polynomial,
 * and outputs a basis if it is free, an n+1-generating set if it is not */
GEN
rnfbasis(GEN bnf, GEN order)
{
  pari_sp av = avma;
  long j, n;
  GEN nf, A, I, cl, col, a, id;

  bnf = checkbnf(bnf); nf = (GEN)bnf[7];
  id = idmat(degpol(nf[1]));
  order = get_order(nf, order, "rnfbasis");
  I = (GEN)order[2]; n = lg(I)-1;
  j=1; while (j<n && gegal((GEN)I[j],id)) j++;
  if (j<n)
  {
    order = rnfsteinitz(nf,order);
    I = (GEN)order[2];
  }
  A = (GEN)order[1];
  col= (GEN)A[n]; A = vecextract_i(A, 1, n-1);
  cl = (GEN)I[n];
  a = gen_if_principal(bnf, cl);
  if (!a)
  {
    GEN p1 = ideal_two_elt(nf, cl);
    A = concatsp(A, gmul((GEN)p1[1], col));
    a = (GEN)p1[2];
  }
  A = concatsp(A, element_mulvec(nf, a, col));
  return gerepilecopy(av, A);
}

/* Given bnf and either an order as output by rnfpseudobasis or a polynomial,
 * and outputs a basis (not pseudo) in Hermite Normal Form if it exists, zero
 * if not
 */
GEN
rnfhermitebasis(GEN bnf, GEN order)
{
  pari_sp av = avma;
  long j, n;
  GEN nf, A, I, a, id;

  bnf = checkbnf(bnf); nf = (GEN)bnf[7];
  id = idmat(degpol(nf[1]));
  order = get_order(nf, order, "rnfbasis");
  A = (GEN)order[1]; A = dummycopy(A);
  I = (GEN)order[2]; n = lg(A)-1;
  for (j=1; j<=n; j++)
  {
    if (gegal((GEN)I[j],id)) continue;

    a = gen_if_principal(bnf, (GEN)I[j]);
    if (!a) { avma = av; return gzero; }
    A[j] = (long)element_mulvec(nf, a, (GEN)A[j]);
  }
  return gerepilecopy(av,A);
}

static long
_rnfisfree(GEN bnf, GEN order)
{
  long n, j;
  GEN nf, p1, id, I;

  bnf = checkbnf(bnf);
  if (gcmp1(gmael3(bnf,8,1,1))) return 1;

  nf = (GEN)bnf[7]; id = idmat(degpol(nf[1]));
  order = get_order(nf, order, "rnfisfree");
  I = (GEN)order[2]; n = lg(I)-1;
  j=1; while (j<=n && gegal((GEN)I[j],id)) j++;
  if (j>n) return 1;

  p1 = (GEN)I[j];
  for (j++; j<=n; j++)
    if (!gegal((GEN)I[j],id)) p1 = idealmul(nf,p1,(GEN)I[j]);
  return gcmp0( isprincipal(bnf,p1) );
}

long
rnfisfree(GEN bnf, GEN order)
{
  pari_sp av = avma;
  long n = _rnfisfree(bnf, order);
  avma = av; return n;
}

/**********************************************************************/
/**								     **/
/**		      COMPOSITUM OF TWO NUMBER FIELDS                **/
/**								     **/
/**********************************************************************/
/* modular version */
GEN
polcompositum0(GEN A, GEN B, long flall)
{
  pari_sp av = avma;
  int same = (A == B || gegal(A,B));
  long v, k;
  GEN C, D, LPRS;

  if (typ(A)!=t_POL || typ(B)!=t_POL) err(typeer,"polcompositum0");
  if (degpol(A)<=0 || degpol(B)<=0) err(constpoler,"compositum");
  v = varn(A);
  if (varn(B) != v) err(talker,"not the same variable in compositum");
  A = Q_primpart(A); check_pol_int(A,"compositum");
  if (!ZX_is_squarefree(A)) err(talker,"compositum: %Z inseparable", A);
  if (!same) {
    B = Q_primpart(B); check_pol_int(B,"compositum");
    if (!ZX_is_squarefree(B)) err(talker,"compositum: %Z inseparable", B);
  }

  D = NULL; /* -Wall */
  k = same? -1: 1; 
  C = ZY_ZXY_resultant_all(A, B, &k, flall? &LPRS: NULL);
  if (same) { D = rescale_pol(A, stoi(1 - k)); C = gdivexact(C, D); }
  C = DDF2(C, 0); /* C = Res_Y (A, B(X + kY)) guaranteed squarefree */
  if (same) C = concatsp(C, D);
  C = sort_vecpol(C, &cmpii);
  if (flall)
  {
    long i,l = lg(C);
    GEN w,a,b; /* a,b,c root of A,B,C = compositum, c = b - k a */
    for (i=1; i<l; i++)
    { /* invmod possibly very costly */
      a = gmul((GEN)LPRS[1], QX_invmod((GEN)LPRS[2], (GEN)C[i]));
      a = gneg_i(gmod(a, (GEN)C[i]));
      b = gadd(polx[v], gmulsg(k,a));
      w = cgetg(5,t_VEC); /* [C, a, b, n ] */
      w[1] = C[i];
      w[2] = (long)to_polmod(a, (GEN)w[1]);
      w[3] = (long)to_polmod(b, (GEN)w[1]);
      w[4] = lstoi(-k); C[i] = (long)w;
    }
  }
  settyp(C, t_VEC); return gerepilecopy(av, C);
}

GEN
compositum(GEN pol1,GEN pol2)
{
  return polcompositum0(pol1,pol2,0);
}

GEN
compositum2(GEN pol1,GEN pol2)
{
  return polcompositum0(pol1,pol2,1);
}

int
nfissquarefree(GEN nf, GEN x)
{
  pari_sp av = avma;
  GEN g, y = derivpol(x);
  if (isrational(x))
    g = modulargcd(x, y);
  else
    g = nfgcd(x, y, nf, NULL);
  avma = av; return (degpol(g) == 0);
}

GEN
_rnfequation(GEN A, GEN B, long *pk, GEN *pLPRS)
{
  long k, lA, lB;
  GEN nf, C;

  A = get_nfpol(A, &nf);       lA = lg(A);
  B = fix_relative_pol(A,B,1); lB = lg(B);
  if (lA<=3 || lB<=3) err(constpoler,"rnfequation");

  check_pol_int(A,"rnfequation");
  B = primpart(lift_intern(B));
  for (k=2; k<lB; k++)
    if (lg(B[k]) >= lA) B[k] = lres((GEN)B[k],A);

  if (!nfissquarefree(A,B))
    err(talker,"inseparable relative equation in rnfequation");

  *pk = 0; C = ZY_ZXY_resultant_all(A, B, pk, pLPRS);
  if (gsigne(leading_term(C)) < 0) C = gneg_i(C);
  *pk = -*pk; return primpart(C);
}

GEN
rnfequation0(GEN A, GEN B, long flall)
{
  pari_sp av = avma;
  long k;
  GEN LPRS, nf, C;

  A = get_nfpol(A, &nf);
  C = _rnfequation(A, B, &k, flall? &LPRS: NULL);
  if (flall)
  {
    GEN w,a; /* a,b,c root of A,B,C = compositum, c = b + k a */
    /* invmod possibly very costly */
    a = gmul((GEN)LPRS[1], QX_invmod((GEN)LPRS[2], C));
    a = gneg_i(gmod(a, C));
    /* b = gadd(polx[varn(A)], gmulsg(k,a)); */
    w = cgetg(4,t_VEC); /* [C, a, n ] */
    w[1] = (long)C;
    w[2] = (long)to_polmod(a, (GEN)w[1]);
    w[3] = lstoi(k); C = w;
  }
  return gerepilecopy(av, C);
}

GEN
rnfequation(GEN nf,GEN pol2)
{
  return rnfequation0(nf,pol2,0);
}

GEN
rnfequation2(GEN nf,GEN pol2)
{
  return rnfequation0(nf,pol2,1);
}

static GEN
nftau(long r1, GEN x)
{
  long i, l = lg(x);
  GEN s = r1? (GEN)x[1]: gmul2n(real_i((GEN)x[1]),1);
  for (i=2; i<=r1; i++) s = gadd(s, (GEN)x[i]);
  for (   ; i < l; i++) s = gadd(s, gmul2n(real_i((GEN)x[i]),1));
  return s;
}

static GEN
initmat(long l)
{
  GEN x = cgetg(l, t_MAT);
  long i;
  for (i = 1; i < l; i++) x[i] = lgetg(l, t_COL);
  return x;
}

static GEN
nftocomplex(GEN nf, GEN x)
{
  return gmul(gmael(nf,5,1), _algtobasis(nf, x));
}
/* assume x a square t_MAT, return a t_VEC of embeddings of its columns */
static GEN
mattocomplex(GEN nf, GEN x)
{
  long i,j, l = lg(x);
  GEN v = cgetg(l, t_VEC);
  for (j=1; j<l; j++)
  {
    GEN c = (GEN)x[j], b = cgetg(l, t_MAT);
    for (i=1; i<l; i++) b[i] = (long)nftocomplex(nf, (GEN)c[i]);
    b = gtrans_i(b); settyp(b, t_COL);
    v[j] = (long)b;
  }
  return v;
}

static GEN
nf_all_roots(GEN nf, GEN x, long prec)
{
  long i, j, l = lg(x), ru = lg(nf[6]);
  GEN y = cgetg(l, t_POL), v, z;

  x = unifpol(nf, x, t_COL);
  y[1] = x[1];
  for (i=2; i<l; i++) y[i] = (long) nftocomplex(nf, (GEN)x[i]);
  i = gprecision(y); if (i && i <= 3) return NULL;

  v = cgetg(ru, t_VEC);
  z = cgetg(l, t_POL); z[1] = x[1];
  for (i=1; i<ru; i++)
  {
    for (j = 2; j < l; j++) z[j] = mael(y,j,i);
    v[i] = (long)cleanroots(z, prec);
  }
  return v;
}

static GEN
rnfscal(GEN m, GEN x, GEN y)
{
  long i, l = lg(m);
  GEN z = cgetg(l, t_COL);
  for (i = 1; i < l; i++)
    z[i] = lmul(gconj(gtrans_i((GEN)x[i])), gmul((GEN)m[i], (GEN)y[i]));
  return z;
}

static GEN
findmin(GEN nf, GEN x, GEN muf)
{
  pari_sp av = avma;
  long e;
  GEN cx, y, m, M = gmael(nf,5,1);

  x = Q_primitive_part(x, &cx);
  if (gcmp1(gcoeff(x,1,1))) y = M;
  else
  {
    GEN G = gmael(nf,5,2);
    m = lllintern(gmul(G, x), 4, 1, 0);
    if (!m)
    {
      x = lllint_ip(x,4);
      m = lllintern(gmul(G, x), 4, 1, 0);
      if (!m) err(precer,"rnflllgram");
    }
    x = gmul(x, m);
    y = gmul(M, x);
  }
  m = gauss_realimag(y, muf);
  if (cx) m = gdiv(m, cx);
  m = grndtoi(m, &e);
  if (e >= 0) return NULL; /* precision problem */
  if (cx) m = gmul(m, cx);
  return gerepileupto(av, gmul(x,m));
}

static int
RED(long k, long l, GEN U, GEN mu, GEN MC, GEN nf, GEN I, GEN *Ik_inv)
{
  GEN x, xc, ideal;
  long i;

  if (!*Ik_inv) *Ik_inv = idealinv(nf, (GEN)I[k]);
  ideal = idealmul(nf,(GEN)I[l], *Ik_inv);
  x = findmin(nf, ideal, gcoeff(mu,k,l));
  if (!x) return 0;
  if (gcmp0(x)) return 1;

  xc = nftocomplex(nf,x);
  MC[k] = lsub((GEN)MC[k], vecmul(xc,(GEN)MC[l]));
  U[k] = lsub((GEN)U[k], gmul(basistoalg(nf,x), (GEN)U[l]));
  coeff(mu,k,l) = lsub(gcoeff(mu,k,l), xc);
  for (i=1; i<l; i++)
    coeff(mu,k,i) = lsub(gcoeff(mu,k,i), vecmul(xc,gcoeff(mu,l,i)));
  return 1;
}

static int
check_0(GEN B)
{
  long i, l = lg(B);
  for (i = 1; i < l; i++)
    if (gsigne((GEN)B[i]) <= 0) return 1;
  return 0;
}

#define swap(x,y) { long _t=x; x=y; y=_t; }
static int
do_SWAP(GEN I, GEN MC, GEN MCS, GEN h, GEN mu, GEN B, long kmax, long k,
        const int alpha, long r1)
{
  GEN p1, p2, muf, mufc, Bf, temp;
  long i, j;

  p1 = nftau(r1, gadd((GEN) B[k],
                      gmul(gnorml2(gcoeff(mu,k,k-1)), (GEN)B[k-1])));
  p2 = nftau(r1, (GEN)B[k-1]);
  if (gcmp(gmulsg(alpha,p1), gmulsg(alpha-1,p2)) > 0) return 0;

  swap(MC[k-1],MC[k]);
  swap(h[k-1],  h[k]);
  swap(I[k-1],  I[k]);
  for (j=1; j<=k-2; j++) swap(coeff(mu,k-1,j),coeff(mu,k,j));
  muf = gcoeff(mu,k,k-1);
  mufc = gconj(muf); 
  Bf = gadd((GEN)B[k], vecmul(real_i(vecmul(muf,mufc)), (GEN)B[k-1]));
  if (check_0(Bf)) return 1; /* precision problem */

  p1 = vecdiv((GEN)B[k-1],Bf);
  coeff(mu,k,k-1) = (long)vecmul(mufc,p1);
  temp = (GEN)MCS[k-1];
  MCS[k-1] = ladd((GEN)MCS[k], vecmul(muf,(GEN)MCS[k-1]));
  MCS[k] = lsub(vecmul(vecdiv((GEN)B[k],Bf), temp),
                vecmul(gcoeff(mu,k,k-1), (GEN)MCS[k]));
  B[k] = (long)vecmul((GEN)B[k],p1);
  B[k-1] = (long)Bf;
  for (i=k+1; i<=kmax; i++)
  {
    temp = gcoeff(mu,i,k);
    coeff(mu,i,k) = lsub(gcoeff(mu,i,k-1), vecmul(muf, gcoeff(mu,i,k)));
    coeff(mu,i,k-1) = ladd(temp, vecmul(gcoeff(mu,k,k-1),gcoeff(mu,i,k)));
  }
  return 1;
}

static GEN
rel_T2(GEN nf, GEN pol, long lx, long prec)
{
  long ru, i, j, k, l;
  GEN T2, s, unro, roorder, powreorder;

  roorder = nf_all_roots(nf, pol, prec);
  if (!roorder) return NULL;
  ru = lg(roorder);
  unro = cgetg(lx,t_COL); for (i=1; i<lx; i++) unro[i] = un;
  powreorder = cgetg(lx,t_MAT); powreorder[1] = (long)unro;
  T2 = cgetg(ru, t_VEC);
  for (i = 1; i < ru; i++)
  {
    GEN ro = (GEN)roorder[i];
    GEN m = initmat(lx);
    for (k=2; k<lx; k++)
    {
      GEN c = cgetg(lx, t_COL); powreorder[k] = (long)c;
      for (j=1; j < lx; j++)
	c[j] = lmul((GEN)ro[j], gmael(powreorder,k-1,j));
    }
    for (l = 1; l < lx; l++)
      for (k = 1; k <= l; k++)
      {
        s = gzero;
        for (j = 1; j < lx; j++)
          s = gadd(s, gmul(gconj(gmael(powreorder,k,j)),
                                 gmael(powreorder,l,j)));
        if (l == k)
          coeff(m, l, l) = lreal(s);
        else
        {
          coeff(m, k, l) = (long)s;
          coeff(m, l, k) = lconj(s);
        }
      }
    T2[i] = (long)m;
  }
  return T2;
}

/* given a base field nf (e.g main variable y), a polynomial pol with
 * coefficients in nf    (e.g main variable x), and an order as output
 * by rnfpseudobasis, outputs a reduced order. */
GEN
rnflllgram(GEN nf, GEN pol, GEN order,long prec)
{
  pari_sp av = avma, lim = stack_lim(av,2);
  long j, k, l, kmax, r1, lx, count = 0;
  GEN M, I, h, H, mth, MC, MPOL, MCS, B, mu, y, z;
  const int alpha = 10, MAX_COUNT = 4;

  nf = checknf(nf); r1 = nf_get_r1(nf);
  check_ZKmodule(order, "rnflllgram");
  M = (GEN)order[1];
  I = (GEN)order[2]; lx = lg(I);
  if (lx < 3) return gcopy(order);
  if (lx-1 != degpol(pol)) err(consister,"rnflllgram");
  I = dummycopy(I);
  H = NULL;
  MPOL = matbasistoalg(nf, M);
  MCS = idmat(lx-1); /* dummy for gerepile */
PRECNF:
  if (count == MAX_COUNT)
  { 
    prec = (prec<<1)-2; count = 0;
    if (DEBUGLEVEL) err(warnprec,"rnflllgram",prec);
    nf = nfnewprec(nf,prec);
  }
  mth = rel_T2(nf, pol, lx, prec);
  if (!mth) { count = MAX_COUNT; goto PRECNF; }
  h = NULL;
PRECPB:
  if (h)
  { /* precision problem, recompute. If no progress, increase nf precision */
    if (++count == MAX_COUNT || isidentity(h)) {count = MAX_COUNT; goto PRECNF;}
    H = H? gmul(H, h): h;
    MPOL = gmul(MPOL, h);
  }
  h = idmat(lx-1);
  MC = mattocomplex(nf, MPOL);
  mu = cgetg(lx,t_MAT);
  B  = cgetg(lx,t_COL);
  for (j=1; j<lx; j++)
  {
    mu[j] = (long)zerocol(lx - 1);
    B[j] = zero;
  }
  if (DEBUGLEVEL) fprintferr("k = ");
  B[1] = lreal(rnfscal(mth,(GEN)MC[1],(GEN)MC[1]));
  MCS[1] = MC[1];
  kmax = 1; k = 2;
  do
  {
    GEN Ik_inv = NULL;
    if (DEBUGLEVEL) fprintferr("%ld ",k);
    if (k > kmax)
    { /* Incremental Gram-Schmidt */
      kmax = k; MCS[k] = MC[k];
      for (j=1; j<k; j++)
      {
	coeff(mu,k,j) = (long) vecdiv(rnfscal(mth,(GEN)MCS[j],(GEN)MC[k]),
	                              (GEN) B[j]);
	MCS[k] = lsub((GEN)MCS[k], vecmul(gcoeff(mu,k,j),(GEN)MCS[j]));
      }
      B[k] = lreal(rnfscal(mth,(GEN)MCS[k],(GEN)MCS[k]));
      if (check_0((GEN)B[k])) goto PRECPB;
    }
    if (!RED(k, k-1, h, mu, MC, nf, I, &Ik_inv)) goto PRECPB;
    if (do_SWAP(I,MC,MCS,h,mu,B,kmax,k,alpha, r1))
    {
      if (!B[k]) goto PRECPB;
      if (k > 2) k--;
    }
    else
    {
      for (l=k-2; l; l--) 
        if (!RED(k, l, h, mu, MC, nf, I, &Ik_inv)) goto PRECPB;
      k++;
    }
    if (low_stack(lim, stack_lim(av,2)))
    {
      if(DEBUGMEM>1) err(warnmem,"rnflllgram");
      gerepileall(av, H?10:9, &nf,&mth,&h,&MPOL,&B,&MC,&MCS,&mu,&I,&H);
    }
  }
  while (k < lx);
  MPOL = gmul(MPOL,h);
  if (H) h = gmul(H, h);
  if (DEBUGLEVEL) fprintferr("\n");
  y = cgetg(3,t_VEC);
  z = cgetg(3,t_VEC);
  z[1] = (long)algtobasis(nf,MPOL);
  z[2] = lcopy(I);
  y[1] = (long)z;
  y[2] = (long)algtobasis(nf,h);
  return gerepileupto(av, y);
}

GEN
rnfpolred(GEN nf, GEN pol, long prec)
{
  pari_sp av = avma;
  long i, j, n, v = varn(pol);
  GEN id, al, w, I, O, bnf;

  if (typ(pol)!=t_POL) err(typeer,"rnfpolred");
  bnf = nf; nf = checknf(bnf);
  bnf = (nf == bnf)? NULL: checkbnf(bnf);
  if (degpol(pol) <= 1) return _vec(polx[v]);

  id = rnfpseudobasis(nf,pol);
  if (bnf && gcmp1(gmael3(bnf,8,1,1))) /* if bnf is principal */
  {
    GEN newI, newO, zk = idmat(degpol(nf[1]));
    O = (GEN)id[1];
    I = (GEN)id[2]; n = lg(I)-1;
    newI = cgetg(n+1,t_VEC);
    newO = cgetg(n+1,t_MAT);
    for (j=1; j<=n; j++)
    {
      newI[j] = (long)zk; al = gen_if_principal(bnf,(GEN)I[j]);
      newO[j] = (long)element_mulvec(nf, al, (GEN)O[j]);
    }
    id = cgetg(3,t_VEC);
    id[1] = (long)newO;
    id[2] = (long)newI;
  }
  
  id = (GEN)rnflllgram(nf,pol,id,prec)[1];
  O = (GEN)id[1];
  I = (GEN)id[2]; n = lg(I)-1;
  w = cgetg(n+1,t_VEC);
  pol = lift(pol);
  for (j=1; j<=n; j++)
  {
    GEN p1, newpol;

    p1 = (GEN)I[j]; al = gmul(gcoeff(p1,1,1),(GEN)O[j]);
    p1 = basistoalg(nf,(GEN)al[n]);
    for (i=n-1; i; i--)
      p1 = gadd(basistoalg(nf,(GEN)al[i]), gmul(polx[v],p1));
    p1 = gmodulcp(gtovec(caract2(pol,lift(p1),v)), (GEN)nf[1]);
    newpol = gtopoly(p1, v);

    p1 = ggcd(newpol, derivpol(newpol));
    if (degpol(p1) > 0)
    {
      newpol = gdiv(newpol, p1);
      newpol = gdiv(newpol, leading_term(newpol));
    }
    w[j] = (long)newpol;
  }
  return gerepilecopy(av,w);
}

/* given a relative polynomial pol over nf, compute a pseudo-basis for the
 * extension, then an absolute basis */
static GEN
makebasis(GEN nf, GEN pol, GEN rnfeq)
{
  GEN elts,ids,polabs,plg,plg0,B,bs,p1,den,vbs,d,vpro;
  pari_sp av = avma;
  long n,N,m,i,j,k, v = varn(pol);

  polabs= (GEN)rnfeq[1];
  plg   = (GEN)rnfeq[2]; plg = lift_intern(plg);
  p1 = rnfpseudobasis(nf,pol);
  elts= (GEN)p1[1];
  ids = (GEN)p1[2];
  if (DEBUGLEVEL>1) fprintferr("relative basis computed\n");
  N = degpol(pol);
  n = degpol(nf[1]); m = n*N;

  plg0= Q_remove_denom(plg, &den); /* plg = plg0/den */
  /* nf = K = Q(a), vbs[i+1] = a^i as an elt of L = Q[X] / polabs */
  vbs = RXQ_powers(plg0, polabs, n-1);
  if (den)
  { /* restore denominators */
    vbs[2] = (long)plg; d = den;
    for (i=3; i<=n; i++) { d = mulii(d,den); vbs[i] = ldiv((GEN)vbs[i], d); }
  }

  /* bs = integer basis of K, as elements of L */
  bs = gmul(vbs, vecpol_to_mat((GEN)nf[7],n));

  vpro = cgetg(N+1,t_VEC);
  for (i=1; i<=N; i++) vpro[i] = lpowgs(polx[v], i-1);
  vpro = gmul(vpro, elts);
  B = cgetg(m+1, t_MAT);
  for(i=k=1; i<=N; i++)
  {
    GEN w = element_mulvec(nf, (GEN)vpro[i], (GEN)ids[i]);
    for(j=1; j<=n; j++)
    {
      p1 = gres(gmul(bs, (GEN)w[j]), polabs);
      B[k++] = (long)pol_to_vec(p1, m);
    }
  }
  B = Q_remove_denom(B, &den);
  if (den) { B = hnfmodid(B, den); B = gdiv(B, den); } else B = idmat(m);
  p1 = cgetg(3,t_VEC);
  p1[1] = (long)polabs;
  p1[2] = (long)B; return gerepilecopy(av, p1);
}

/* relative polredabs. Returns relative polynomial by default (flag = 0)
 * flag & nf_ORIG: + element (base change)
 * flag & nf_ADDZK: + integer basis
 * flag & nf_ABSOLUTE: absolute polynomial */
GEN
rnfpolredabs(GEN nf, GEN relpol, long flag)
{
  GEN red, bas, z, elt, POL, pol, T, a;
  long v, fl = (flag & nf_ADDZK)? nf_ADDZK: nf_RAW;
  pari_sp av = avma;

  if (typ(relpol)!=t_POL) err(typeer,"rnfpolredabs");
  nf = checknf(nf); v = varn(relpol);
  if (DEBUGLEVEL>1) (void)timer2();
  relpol = unifpol(nf, relpol, t_POLMOD);
  T = (GEN)nf[1];
  if ((flag & nf_ADDZK) && !(flag & nf_ABSOLUTE))
    err(impl,"this combination of flags in rnfpolredabs");
  if (flag & nf_PARTIALFACT)
  {
    long sa;
    fl |= nf_PARTIALFACT;
    POL = _rnfequation(nf, relpol, &sa, NULL);
    bas = POL;
    a = stoi(sa);
  }
  else
  {
    GEN rel, eq = rnfequation2(nf,relpol);
    POL = (GEN)eq[1];
    a   = (GEN)eq[3];
    rel = poleval(relpol, gsub(polx[v],
                               gmul(a, gmodulcp(polx[varn(T)],T))));
    bas = makebasis(nf, rel, eq);
    if (DEBUGLEVEL>1)
    {
      msgtimer("absolute basis");
      fprintferr("original absolute generator: %Z\n", POL);
    }
  }
  red = polredabs0(bas, fl);
  pol = (GEN)red[1];
  if (DEBUGLEVEL>1) fprintferr("reduced absolute generator: %Z\n",pol);
  if (flag & nf_ABSOLUTE)
  {
    if (flag & nf_ADDZK)
    {
      z = cgetg(3, t_VEC);
      z[1] = (long)pol;
      z[2] = red[2]; pol = z;
    }
    return gerepilecopy(av, pol);
  }

  elt = eltabstorel((GEN)red[2], T, relpol, a);
  pol = rnfcharpoly(nf,relpol,elt,v);
  if (!(flag & nf_ORIG)) return gerepileupto(av, pol);
  z = cgetg(3,t_VEC);
  z[1] = (long)pol;
  z[2] = (long)to_polmod(modreverse_i((GEN)elt[2],(GEN)elt[1]), pol);
  return gerepilecopy(av, z);
}
