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
#define FpX_rem(x,y,p) FpX_divres((x),(y),(p),ONLY_REM)
extern GEN DDF2(GEN x, long hint);
extern GEN eltabstorel(GEN x, GEN T, GEN pol, GEN k);
extern GEN element_powid_mod_p(GEN nf, long I, GEN n, GEN p);
extern GEN FpVQX_red(GEN z, GEN T, GEN p);
extern GEN Fp_factor_irred(GEN P,GEN l, GEN Q);
extern GEN RXQX_divrem(GEN x, GEN y, GEN T, GEN *pr);
extern GEN RXQX_mul(GEN x, GEN y, GEN T);
extern GEN ZY_ZXY_resultant_all(GEN A, GEN B0, long *lambda, GEN *LPRS);
extern GEN _ei(long n, long i);
extern GEN col_to_ff(GEN x, long v);
extern GEN element_mulidid(GEN nf, long i, long j);
extern GEN eleval(GEN f,GEN h,GEN a);
extern GEN eltmulid_get_table(GEN nf, long i);
extern GEN ideal_better_basis(GEN nf, GEN x, GEN M);
extern GEN idealaddtoone_i(GEN nf, GEN x, GEN y);
extern GEN mat_to_vecpol(GEN x, long v);
extern GEN merge_factor_i(GEN f, GEN g);
extern GEN mulmat_pol(GEN A, GEN x);
extern GEN nfgcd(GEN P, GEN Q, GEN nf, GEN den);
extern GEN pol_to_monic(GEN pol, GEN *lead);
extern GEN pol_to_vec(GEN x, long N);
extern GEN quicktrace(GEN x, GEN sym);
extern GEN respm(GEN f1,GEN f2,GEN pm);
extern GEN sqr_by_tab(GEN tab, GEN x);
extern GEN to_polmod(GEN x, GEN mod);
extern GEN unnf_minus_x(GEN x);
extern GEN vecpol_to_mat(GEN v, long n);
extern int isrational(GEN x);
extern long int_elt_val(GEN nf, GEN x, GEN p, GEN bp, GEN *t);

static void
allbase_check_args(GEN f, long code, GEN *y, GEN *ptw1, GEN *ptw2)
{
  GEN w;
  if (typ(f)!=t_POL) err(notpoler,"allbase");
  if (degpol(f) <= 0) err(constpoler,"allbase");
  if (DEBUGLEVEL) timer2();
  switch(code)
  {
    case 0: case 1:
      *y = ZX_disc(f);
      if (!signe(*y)) err(talker,"reducible polynomial in allbase");
      w = auxdecomp(absi(*y),1-code);
      break;
    default:
      w = (GEN)code;
      *y = factorback(w, NULL);
  }
  if (DEBUGLEVEL) msgtimer("disc. factorisation");
  *ptw1 = (GEN)w[1];
  *ptw2 = (GEN)w[2];
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
  gpmem_t av;
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
  gpmem_t av = avma;
  GEN y = leftright_pow(x, n, NULL, &_sqrmati, &_mulmati);
  return gerepileupto(av,y);
}

static GEN
rtran(GEN v, GEN w, GEN q)
{
  gpmem_t av,tetpil;
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
      gpmem_t av = avma;
      p1 = subii((GEN)v[k], mulii(q,(GEN)w[k]));
      p1 = centermodii(p1, m, mo2);
      v[k] = (long)gerepileuptoint(av, p1);
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
  gpmem_t av=avma, lim=stack_lim(av,1);
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
  gpmem_t av,av1;
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
  gpmem_t av=avma, av2,limit;
  GEN T,T2,Tn,m,v,delta,hard_case_exponent, *w;
  const GEN pp = sqri(p);
  const GEN ppo2 = shifti(pp,-1);
  const long pps = (2*expi(pp)+2<BITS_IN_LONG)? pp[2]: 0;

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
    gpmem_t av0 = avma;
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
          gpmem_t av1 = avma;
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
        gpmem_t av1=avma;
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
GEN
allbase(GEN f, long code, GEN *y)
{
  GEN w1,w2,a,pro,at,bt,b,da,db,q, *cf,*gptr[2];
  gpmem_t av=avma,tetpil;
  long n,h,j,i,k,r,s,t,v,mf;

  allbase_check_args(f,code,y, &w1,&w2);
  v = varn(f); n = degpol(f); h = lg(w1)-1;
  cf = (GEN*)cgetg(n+1,t_VEC);
  cf[2]=companion(f);
  for (i=3; i<=n; i++) cf[i]=mulmati(cf[2],cf[i-1]);

  a=idmat(n); da=gun;
  for (i=1; i<=h; i++)
  {
    gpmem_t av1 = avma;
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
  for (j=1; j<=n; j++)
    *y = divii(mulii(*y,sqri(gcoeff(a,j,j))), sqri(da));
  tetpil=avma; *y=icopy(*y);
  at=cgetg(n+1,t_VEC); v=varn(f);
  for (k=1; k<=n; k++)
  {
    q=cgetg(k+2,t_POL); at[k]=(long)q;
    q[1] = evalsigne(1) | evallgef(2+k) | evalvarn(v);
    for (j=1; j<=k; j++) q[j+1]=ldiv(gcoeff(a,k,j),da);
  }
  gptr[0]=&at; gptr[1]=y;
  gerepilemanysp(av,tetpil,gptr,2);
  return at;
}

GEN
base2(GEN x, GEN *y)
{
  return allbase(x,0,y);
}

GEN
discf2(GEN x)
{
  GEN y;
  gpmem_t av=avma,tetpil;

  allbase(x,0,&y); tetpil=avma;
  return gerepile(av,tetpil,icopy(y));
}

/*******************************************************************/
/*                                                                 */
/*                            ROUND 4                              */
/*                                                                 */
/*******************************************************************/

GEN nilord(GEN p,GEN fx,long mf,GEN gx,long flag);
GEN Decomp(GEN p,GEN f,long mf,GEN theta,GEN chi,GEN nu,long r);
static GEN dbasis(GEN p, GEN f, long mf, GEN alpha, GEN U);
static GEN maxord(GEN p,GEN f,long mf);
static GEN nbasis(GEN ibas,GEN pd);
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

/* retourne la base, dans y le discf et dans ptw la factorisation (peut
 etre partielle) de discf */
GEN
allbase4(GEN f,long code, GEN *y, GEN *ptw)
{
  GEN w,w1,w2,a,da,b,db,bas,q,p1,*gptr[3];
  long v,n,mf,h,lfa,i,j,k,l;
  gpmem_t tetpil,av = avma;

  allbase_check_args(f,code,y, &w1,&w2);
  v = varn(f); n = degpol(f); h = lg(w1)-1;
  a = NULL; /* gcc -Wall */
  da= NULL;
  for (i=1; i<=h; i++)
  {
    mf=itos((GEN)w2[i]); if (mf == 1) continue;
    if (DEBUGLEVEL) fprintferr("Treating p^k = %Z^%ld\n",w1[i],mf);

    b = maxord((GEN)w1[i],f,mf); db = gun;
    for (j=1; j<=n; j++)
    {
      p1 = denom(gcoeff(b,j,j));
      if (cmpii(p1,db) > 0) db = p1;
    }
    if (db != gun)
    { /* db = denom(diag(b)), (da,db) = 1 */
      b = gmul(b,db);
      if (!da) { da=db; a=b; }
      else
      {
        j=1; while (j<=n && fnz((GEN)a[j],j) && fnz((GEN)b[j],j)) j++;
        b = gmul(da,b); a = gmul(db,a);
        k=j-1; p1=cgetg(2*n-k+1,t_MAT);
        for (j=1; j<=k; j++)
        {
          p1[j] = a[j];
          coeff(p1,j,j) = lmppgcd(gcoeff(a,j,j),gcoeff(b,j,j));
        }
        for (  ; j<=n;     j++) p1[j] = a[j];
        for (  ; j<=2*n-k; j++) p1[j] = b[j+k-n];
        da = mulii(da,db); a = hnfmodid(p1, da);
      }
    }
    if (DEBUGLEVEL>5)
      fprintferr("Result for prime %Z is:\n%Z\n",w1[i],b);
  }
  if (da)
  {
    for (j=1; j<=n; j++)
      *y = mulii(divii(*y,sqri(da)),sqri(gcoeff(a,j,j)));
    for (j=n-1; j; j--)
      if (cmpis(gcoeff(a,j,j),2) > 0)
      {
        p1=shifti(gcoeff(a,j,j),-1);
        for (k=j+1; k<=n; k++)
          if (cmpii(gcoeff(a,j,k),p1) > 0)
            for (l=1; l<=j; l++)
              coeff(a,l,k)=lsubii(gcoeff(a,l,k),gcoeff(a,l,j));
      }
  }
  lfa = 0;
  if (ptw)
  {
    for (j=1; j<=h; j++)
    {
      k=ggval(*y,(GEN)w1[j]);
      if (k) { lfa++; w1[lfa]=w1[j]; w2[lfa]=k; }
    }
  }
  tetpil=avma; *y=icopy(*y);
  bas=cgetg(n+1,t_VEC); v=varn(f);
  for (k=1; k<=n; k++)
  {
    q=cgetg(k+2,t_POL); bas[k]=(long)q;
    q[1] = evalsigne(1) | evallgef(k+2) | evalvarn(v);
    if (da)
      for (j=1; j<=k; j++) q[j+1]=ldiv(gcoeff(a,j,k),da);
    else
    {
      for (j=2; j<=k; j++) q[j]=zero;
      q[j]=un;
    }
  }
  if (ptw)
  {
    *ptw=w=cgetg(3,t_MAT);
    w[1]=lgetg(lfa+1,t_COL);
    w[2]=lgetg(lfa+1,t_COL);
    for (j=1; j<=lfa; j++)
    {
      coeff(w,j,1)=(long)icopy((GEN)w1[j]);
      coeff(w,j,2)=lstoi(w2[j]);
    }
    gptr[2]=ptw;
  }
  gptr[0]=&bas; gptr[1]=y;
  gerepilemanysp(av,tetpil,gptr, ptw?3:2);
  return bas;
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

/* if y is non-NULL, it receives the discriminant
 * return basis if (ret_basis != 0), discriminant otherwise
 */
static GEN
nfbasis00(GEN x0, long flag, GEN p, long ret_basis, GEN *y)
{
  GEN x, disc, basis, lead;
  GEN *gptr[2];
  gpmem_t tetpil, av = avma;
  long l = lgef(x0), smll,k;

  if (typ(x0)!=t_POL) err(typeer,"nfbasis00");
  if (l<=3) err(zeropoler,"nfbasis00");
  for (k=2; k<l; k++)
    if (typ(x0[k])!=t_INT) err(talker,"polynomial not in Z[X] in nfbasis");

  x = pol_to_monic(x0,&lead);

  if (!p || gcmp0(p))
    smll = (flag & 1); /* small basis */
  else
  {
    if (lead) p = update_fact(x,p);
    smll = (long) p;   /* factored basis */
  }

  if (flag & 2)
    basis = allbase(x,smll,&disc); /* round 2 */
  else
    basis = allbase4(x,smll,&disc,NULL); /* round 4 */

  if (!ret_basis) return gerepilecopy(av,disc);

  tetpil=avma;
  if (!lead) basis = gcopy(basis);
  else
  {
    long v = varn(x);
    GEN pol = gmul(polx[v],lead);

    tetpil = avma; basis = gsubst(basis,v,pol);
  }
  if (!y)
    return gerepile(av,tetpil,basis);

  *y = gcopy(disc);
  gptr[0]=&basis; gptr[1]=y;
  gerepilemanysp(av,tetpil,gptr,2);
  return basis;
}

GEN
nfbasis(GEN x, GEN *y, long flag, GEN p)
{
  return nfbasis00(x,flag,p,1,y);
}

GEN
nfbasis0(GEN x, long flag, GEN p)
{
  return nfbasis00(x,flag,p,1,NULL);
}

GEN
nfdiscf0(GEN x, long flag, GEN p)
{
  return nfbasis00(x,flag,p,0,&p);
}

GEN
base(GEN x, GEN *y)
{
  return allbase4(x,0,y,NULL);
}

GEN
smallbase(GEN x, GEN *y)
{
  return allbase4(x,1,y,NULL);
}

GEN
factoredbase(GEN x, GEN p, GEN *y)
{
  return allbase4(x,(long)p,y,NULL);
}

GEN
discf(GEN x)
{
  GEN y;
  gpmem_t av=avma,tetpil;

  allbase4(x,0,&y,NULL); tetpil=avma;
  return gerepile(av,tetpil,icopy(y));
}

GEN
smalldiscf(GEN x)
{
  GEN y;
  gpmem_t av=avma,tetpil;

  allbase4(x,1,&y,NULL); tetpil=avma;
  return gerepile(av,tetpil,icopy(y));
}

GEN
factoreddiscf(GEN x, GEN p)
{
  GEN y;
  gpmem_t av=avma,tetpil;

  allbase4(x,(long)p,&y,NULL); tetpil=avma;
  return gerepile(av,tetpil,icopy(y));
}

/* return U if Z[alpha] is not maximal or 2*dU < m-1; else return NULL */
static GEN
dedek(GEN f, long mf, GEN p,GEN g)
{
  GEN k,h;
  long dk;

  if (DEBUGLEVEL>=3)
  {
    fprintferr("  entering dedek ");
    if (DEBUGLEVEL>5)
      fprintferr("with parameters p=%Z,\n  f=%Z",p,f);
    fprintferr("\n");
  }
  h = FpX_div(f,g,p);
  k = gdivexact(gadd(f, gneg_i(gmul(g,h))), p);
  k = FpX_gcd(k, FpX_gcd(g,h, p), p);

  dk = degpol(k);
  if (DEBUGLEVEL>=3) fprintferr("  gcd has degree %ld\n", dk);
  if (2*dk >= mf-1) return FpX_div(f,k,p);
  return dk? (GEN)NULL: f;
}

/* p-maximal order of Af; mf = v_p(Disc(f)) */
static GEN
maxord(GEN p,GEN f,long mf)
{
  const gpmem_t av = avma;
  long j,r, flw = (cmpsi(degpol(f),p) < 0);
  GEN w,g,h,res;

  if (flw)
  {
    h = NULL; r = 0; /* gcc -Wall */
    g = FpX_div(f, FpX_gcd(f,derivpol(f), p), p);
  }
  else
  {
    w=(GEN)factmod(f,p)[1]; r=lg(w)-1;
    g = h = lift_intern((GEN)w[r]); /* largest factor */
    for (j=1; j<r; j++) g = FpX_red(gmul(g, lift_intern((GEN)w[j])), p);
  }
  res = dedek(f,mf,p,g);
  if (res)
    res = dbasis(p,f,mf,polx[varn(f)],res);
  else
  {
    if (flw) { w=(GEN)factmod(f,p)[1]; r=lg(w)-1; h=lift_intern((GEN)w[r]); }
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
  long lx=lgef(x), i;
  GEN ys2 = shifti(y,-1);
  for (i=2; i<lx; i++) x[i]=(long)polmodiaux((GEN)x[i],y,ys2);
  return normalizepol_i(x, lx);
}

/* same but not in place */
GEN
polmodi_keep(GEN x, GEN y)
{
  long lx=lgef(x), i;
  GEN ys2 = shifti(y,-1);
  GEN z = cgetg(lx,t_POL);
  for (i=2; i<lx; i++) z[i]=(long)polmodiaux((GEN)x[i],y,ys2);
  z[1]=x[1]; return normalizepol_i(z, lx);
}

static GEN
dbasis(GEN p, GEN f, long mf, GEN alpha, GEN U)
{
  long n=degpol(f),dU,c;
  GEN b,ha,pd,pdp;

  if (n == 1) return gscalmat(gun, 1);
  if (DEBUGLEVEL>=3)
  {
    fprintferr("  entering Dedekind Basis ");
    if (DEBUGLEVEL>5)
    {
      fprintferr("with parameters p=%Z\n",p);
      fprintferr("  f = %Z,\n  alpha = %Z",f,alpha);
    }
    fprintferr("\n");
  }
  ha = pd = gpowgs(p,mf/2); pdp = mulii(pd,p);
  dU = typ(U)==t_POL? degpol(U): 0;
  b = cgetg(n,t_MAT); /* Z[a] + U/p Z[a] is maximal */
  /* skip first column = gscalcol(pd,n) */
  for (c=1; c<n; c++)
  {
    if (c == dU)
    {
      ha = gdiv(gmul(pd,eleval(f,U,alpha)),p);
      ha = polmodi(ha,pdp);
    }
    else
    {
      GEN p2, mod;
      ha = gmul(ha,alpha);
      p2 = content(ha); /* to cancel denominator */
      if (gcmp1(p2)) { p2 = NULL; mod = pdp; }
      else
      {
        ha = gdiv(ha,p2);
        if (typ(p2)==t_INT)
          mod = divii(pdp, mppgcd(pdp,p2));
        else
          mod = mulii(pdp, (GEN)p2[2]); /* p2 = a / p^e */
      }
      ha = FpX_res(ha, f, mod);
      if (p2) ha = gmul(ha,p2);
    }
    b[c] = (long)pol_to_vec(ha,n);
  }
  b = hnfmodid(b,pd);
  if (DEBUGLEVEL>5) fprintferr("  new order: %Z\n",b);
  return gdiv(b,pd);
}

static GEN
get_partial_order_as_pols(GEN p, GEN f)
{
  long i,j, n = degpol(f), vf = varn(f);
  GEN b,ib,h,col;

  b = maxord(p,f, ggval(ZX_disc(f),p));
  ib = cgetg(n+1,t_VEC);
  for (i=1; i<=n; i++)
  {
    h=cgetg(i+2,t_POL); ib[i]=(long)h; col=(GEN)b[i];
    h[1]=evalsigne(1)|evallgef(i+2)|evalvarn(vf);
    for (j=1;j<=i;j++) h[j+1]=col[j];
  }
  return ib;
}

/* if flag != 0, factorization to precision r (maximal order otherwise) */
GEN
Decomp(GEN p,GEN f,long mf,GEN theta,GEN chi,GEN nu,long flag)
{
  GEN res,pr,pk,ph,pdr,b1,b2,b3,a1,e,f1,f2;

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
  b1 = FpX_red(chi, p);
  a1 = gun; b2 = gun;
  b3 = FpX_red(nu, p);
  while (degpol(b3) > 0)
  {
    GEN p1;
    b1 = FpX_div(b1,b3, p);
    b2 = FpX_red(gmul(b2,b3), p);
    b3 = FpX_extgcd(b2,b1, p, &a1,&p1); /* p1 = junk */
    p1 = leading_term(b3);
    if (!gcmp1(p1))
    { /* FpX_extgcd does not return normalized gcd */
      p1 = mpinvmod(p1,p);
      b3 = gmul(b3,p1);
      a1 = gmul(a1,p1);
    }
  }
  pdr = respm(f,derivpol(f),gpowgs(p,mf+1));
  e = eleval(f,FpX_red(gmul(a1,b2), p),theta);
  e = gdiv(polmodi(gmul(pdr,e), mulii(pdr,p)),pdr);

  pr = flag? gpowgs(p,flag): mulii(p,sqri(pdr));
  pk=p; ph=mulii(pdr,pr);
  /* E(t) - e(t) belongs to p^k Op, which is contained in p^(k-df)*Zp[xi] */
  while (cmpii(pk,ph) < 0)
  {
    e = gmul(gsqr(e), gsubsg(3,gmul2n(e,1)));
    e = gres(e,f); pk = sqri(pk);
    e = gdiv(polmodi(gmul(pdr,e), mulii(pdr,pk)), pdr);
  }
  f1 = gcdpm(f,gmul(pdr,gsubsg(1,e)), ph);
  f1 = FpX_res(f1,f, pr);
  f2 = FpX_res(FpX_div(f,f1, pr), f, pr);

  if (DEBUGLEVEL>2)
  {
    fprintferr("  leaving Decomp");
    if (DEBUGLEVEL>5)
      fprintferr(" with parameters: f1 = %Z\nf2 = %Z\ne = %Z\n", f1,f2,e);
    fprintferr("\n");
  }

  if (flag)
  {
    b1=factorpadic4(f1,p,flag);
    b2=factorpadic4(f2,p,flag); res=cgetg(3,t_MAT);
    res[1]=(long)concatsp((GEN)b1[1],(GEN)b2[1]);
    res[2]=(long)concatsp((GEN)b1[2],(GEN)b2[2]); return res;
  }
  else
  {
    GEN ib1,ib2;
    long n1,n2,i;
    ib1 = get_partial_order_as_pols(p,f1); n1=lg(ib1)-1;
    ib2 = get_partial_order_as_pols(p,f2); n2=lg(ib2)-1;
    res=cgetg(n1+n2+1,t_VEC);
    for (i=1; i<=n1; i++)
      res[i]=(long)polmodi(gmod(gmul(gmul(pdr,(GEN)ib1[i]),e),f), pdr);
    e=gsubsg(1,e); ib2 -= n1;
    for (   ; i<=n1+n2; i++)
      res[i]=(long)polmodi(gmod(gmul(gmul(pdr,(GEN)ib2[i]),e),f), pdr);
    return nbasis(res,pdr);
  }
}

/* minimum extension valuation: res[0]/res[1] (both are longs) */
static long *
vstar(GEN p,GEN h)
{
  static long res[2];
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
  res[0]=v/m; res[1]=k/m; return res;
}

/* reduce the element elt modulo rd, taking first care of the denominators */
static GEN
redelt(GEN elt, GEN rd, GEN pd)
{
  GEN den, nelt, nrd, relt;

  den  = ggcd(denom(content(elt)), pd);
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
  gpmem_t av1, av2;
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
  gpmem_t av2, lim;

  ns2 = manage_cache(chi, pp, ns);

  av2 = avma;
  lim = stack_lim(av2, 1);

  pa = gun;
  va = zerovec(n);

  for (j = 1; j <= n; j++)
  {
    pa = gmul(pa, a);
    if (pp) pa = polmodi(pa, pp);
    pa = gmod(pa, chi);
    if (pp) pa = polmodi(pa, pp);

    s  = gzero;

    for (k = 0; k <= n-1; k++)
      s = addii(s, mulii(polcoeff0(pa, k, -1), (GEN)ns2[k+1]));

    if (pp) va[j] = (long)centermod(s, pp);

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
  gpmem_t av = avma, av2, lim;

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

static GEN
mycaract(GEN f, GEN beta, GEN p, GEN pp, GEN ns)
{
  GEN p1, chi, npp;
  long j, a, v = varn(f), n = degpol(f);

  if (gcmp0(beta)) return zeropol(v);

  beta = primitive_part(beta,&p1);
  if (!pp)
    chi = ZX_caract(f, beta, v);
  else
  {
    a = 0;
    for (j = 1; j <= n; j++) /* compute the extra precision needed */
      a += ggval(stoi(j), p);
    npp = mulii(pp, gpowgs(p, a));
    if (p1) npp = gmul(npp, gpowgs(denom(p1), n));

    chi = newtoncharpoly(beta, f, npp, ns);
  }

  if (p1) chi = rescale_pol(chi,p1);

  if (!pp) return chi;

  /* this can happen only if gamma is incorrect (not an integer) */
  if (divise(denom(content(chi)), p)) return NULL;

  return redelt(chi, pp, pp);
}

/* Factor characteristic polynomial of beta mod p */
static GEN
factcp(GEN p, GEN f, GEN beta, GEN pp, GEN ns)
{
  gpmem_t av;
  GEN chi,nu, b = cgetg(4,t_VEC);
  long l;

  chi=mycaract(f,beta,p,pp,ns);
  av=avma; nu=(GEN)factmod(chi,p)[1]; l=lg(nu)-1;
  nu=lift_intern((GEN)nu[1]);
  b[1]=(long)chi;
  b[2]=lpilecopy(av,nu);
  b[3]=lstoi(l); return b;
}

/* return the prime element in Zp[phi] */
static GEN
getprime(GEN p, GEN chi, GEN phi, GEN chip, GEN nup, long *Lp, long *Ep)
{
  long v = varn(chi), L, E, r, s;
  GEN chin, pip, pp, vn;

  if (gegal(nup, polx[v]))
    chin = chip;
  else
    chin = mycaract(chip, nup, p, NULL, NULL);

  vn = vstar(p, chin);
  L  = vn[0];
  E  = vn[1];

  cbezout(L, -E, &r, &s);

  if (r <= 0)
  {
    long q = (-r) / E;
    q++;
    r += q*E;
    s += q*L;
  }

  pip = eleval(chi, nup, phi);
  pip = lift_intern(gpowgs(gmodulcp(pip, chi), r));
  pp  = gpowgs(p, s);

  *Lp = L;
  *Ep = E;
  return gdiv(pip, pp);
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
    /* nchi was too reduced at this point */
    nchi = mycaract(fx, nalph, NULL, NULL, ns);
    pdr = respm(nchi, derivpol(nchi), pmf);
    if (signe(pdr)) break;
    if (DEBUGLEVEL >= 6)
      fprintferr("  non separable polynomial in update_alpha!\n");
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
    if (!nalph) nalph = redelt(alph, npmr, pmf);
    else nalph = redelt(nalph, npmr, pmf);
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
  long Fa, La, Ea, oE, Fg, eq, er, v = varn(fx), i, nv, Le, Ee, N, l, vn;
  GEN p1, alph, chi, nu, w, phi, pmf, pdr, pmr, kapp, pie, chib, ns;
  GEN gamm, chig, nug, delt, beta, eta, chie, nue, pia, vb, opa;

  if (DEBUGLEVEL >= 3)
  {
    if (flag)
      fprintferr("  entering Nilord2 (factorization)");
    else
      fprintferr("  entering Nilord2 (basis/discriminant)");
    if (DEBUGLEVEL >= 5)
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
  l  = lg(p1); /* enough in general... */
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
    pia  = redelt(pia, pmr, pmf);

    if (Ea < oE)
    {
      alph = gadd(alph, opa);
      w = update_alpha(p, fx, alph, NULL, pmr, pmf, mf, ns);
      alph = (GEN)w[1];
      chi  = (GEN)w[2];
      pmr  = (GEN)w[3];
      pdr  = (GEN)w[4];
      kapp = NULL;
      pia  = getprime(p, chi, polx[v], chi, nu, &La, &Ea);
      pia  = redelt(pia, pmr, pmf);
    }

    oE = Ea; opa = eleval(fx, pia, alph);

    if (DEBUGLEVEL >= 5)
      fprintferr("  Fa = %ld and Ea = %ld \n", Fa, Ea);

    /* we change alpha such that nu = pia */
    if (La > 1)
    {
      alph = gadd(alph, eleval(fx, pia, alph));

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
	vb = vstar(p, chib);
	eq = (long)(vb[0] / vb[1]);
	er = (long)(vb[0]*Ea / vb[1] - eq*Ea);
      }

      /* eq and er are such that gamma = beta.p^-eq.nu^-er is a unit */
      if (eq) gamm = gdiv(beta, gpowgs(p, eq));
      else gamm = beta;

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

      if (!chig || !gcmp1(denom(content(chig))))
      {
	/* the valuation of beta was wrong... This means that
	   either gamma fails the v*-test */
	if (!chib) chib = mycaract(chi, beta, p, NULL, ns);
	vb = vstar(p, chib);
	eq = (long)(-vb[0] / vb[1]);
	er = (long)(-vb[0]*Ea / vb[1] - eq*Ea);

 	if (eq) gamm = gmul(beta, gpowgs(p, eq));
	else gamm = beta;
	if (er)
	{
	  gamm = gmul(gamm, gpowgs(nu, er));
	  gamm = gmod(gamm, chi);
	  gamm = redelt(gamm, p, pmr);
	}
	if (eq || er) chig = mycaract(chi, gamm, p, pmf, ns);
	else chig = chib;
      }

      nug  = (GEN)factmod(chig, p)[1];
      l    = lg(nug) - 1;
      nug  = lift((GEN)nug[l]);

      if (l > 1)
      {
	/* there are at least 2 factors mod. p => chi can be split */
	phi  = eleval(fx, gamm, alph);
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
	  phi = eleval(fx, (GEN)w[2], alph);
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
        err(talker,"bug in nilord (no root). Is p a prime ?");

      for (i = 1;; i++)
      {
	if (i >= lg(w))
          err(talker, "bug in nilord (no suitable root), is p = %Z a prime?",
	      (long)p);
        delt = gneg_i(gsubst(gcoeff(w, 2, i), nv, polx[v]));
        eta  = gsub(gamm, delt);	
        if (typ(delt) == t_INT)
        {
          chie = poleval(chig, gadd(polx[v], delt));
          nue  = (GEN)factmod(chie, p)[1];
          l    = lg(nue) - 1;
          nue  = lift((GEN)nue[l]);
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
          delete_var();
          phi = eleval(fx, eta, alph);
          phi = redelt(phi, p, pmf);
          if (flag) mf += 3;
          return Decomp(p, fx, mf, phi, chie, nue, flag);
        }

        /* if vp(eta) = vp(gamma - delta) > 0 */
        if (gegal(nue, polx[v])) break;
      }
      delete_var();

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
	  phi = eleval(fx, (GEN)w[2], alph);
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
    alph = eleval(fx, (GEN)w[2], alph);
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
	p1 = lift((GEN)factmod(chi, p)[1]);
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
  long m, Dat, t, v = varn(fa);
  GEN b, w, phi, h;

  Dat = clcm(Fa, Ft) + 3;
  b = cgetg(5, t_VEC);
  m = p[2];
  if (degpol(p) > 0 || m < 0) m = 0;

  for (t = 1;; t++)
  {
    h = m? stopoly(t, m, v): scalarpol(stoi(t), v);
    phi = gadd(theta, gmod(h, fa));
    w = factcp(p, fa, phi, pmf, ns);
    h = (GEN)w[3];
    if (h[2] > 1) { b[1] = un; break; }
    if (lgef(w[2]) == Dat) { b[1] = deux; break; }
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

  cbezout(Ea, Et, &r, &s); t = 0;
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

/* evaluate h(a) mod f */
GEN
eleval(GEN f,GEN h,GEN a)
{
  gpmem_t av,tetpil;
  long n;
  GEN y;

  if (typ(h) != t_POL) return gcopy(h);
  av = tetpil = avma;
  n=lgef(h)-1; y=(GEN)h[n];
  for (n--; n>=2; n--)
  {
    y = gadd(gmul(y,a),(GEN)h[n]);
    tetpil=avma; y = gmod(y,f);
  }
  return gerepile(av,tetpil,y);
}

GEN addshiftw(GEN x, GEN y, long d);

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
  h = FpX_res(f2,f1,pm);
  for (j=1;; j++)
  {
    a[j] = (long)pol_to_vec(h,n);
    if (j == n) break;
    h = FpX_res(shiftpol(h,v),f1,pm);
  }
  return hnfmodid(a,pm);
}

/* polynomial gcd mod p^m (assumes f1 monic) */
GEN
gcdpm(GEN f1,GEN f2,GEN pm)
{
  gpmem_t av=avma,tetpil;
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
  gpmem_t av = avma;
  GEN p1 = sylpm(x,y,pm);

  p1 = gcoeff(p1,1,1);
  if (egalii(p1,pm)) { avma = av; return gzero; }
  return gerepileuptoint(av, icopy(p1));
}

/* Normalized integral basis */
static GEN
nbasis(GEN ibas,GEN pd)
{
  long k, n = lg(ibas)-1;
  GEN a = cgetg(n+1,t_MAT);
  for (k=1; k<=n; k++) a[k] = (long)pol_to_vec((GEN)ibas[k],n);
  return gdiv(hnfmodid(a,pd), pd);
}

/*******************************************************************/
/*                                                                 */
/*                   BUCHMANN-LENSTRA ALGORITHM                    */
/*                                                                 */
/*******************************************************************/
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
  gpmem_t av = avma;
  GEN z, pow = get_powers(mul, p);
  z = FpM_deplin(pow, p);
  return gerepileupto(av, gtopolyrev(z,0));
}

/* a in pr | p, norm(pr) = pf. Return 1 if (a,p) = pr, and 0 otherwise */
static int
is_uniformizer(GEN a, GEN T, GEN pf, GEN p)
{
  GEN N = subres(a,T); /* norm(a) */
  return (resii(diviiexact(N,pf), p) != gzero);
}

static GEN
prime_check_elt(GEN a, GEN T, GEN p, GEN pf)
{
  if (is_uniformizer(a,T,pf,p)) return a;
  /* FIXME: can't succeed if e > 1, can we know this at this point ? */
  if (is_uniformizer(gadd(a,p),T,pf,p)) return a;
  return NULL;
}

static GEN
random_uniformizer_loop(GEN beta, GEN pol, GEN p, GEN pf)
{
  gpmem_t av = avma;
  long z,i, m = lg(beta)-1;
  long keep = getrand();
  int c = 0;
  GEN a;

  for(i=1; i<=m; i++)
    if ((a = prime_check_elt((GEN)beta[i],pol,p,pf))) return a;
  (void)setrand(1);
  if (DEBUGLEVEL) fprintferr("uniformizer_loop, hard case: ");
  for(;;avma=av)
  {
    if (DEBUGLEVEL) fprintferr("%d ", ++c);
    a = gzero;
    for (i=1; i<=m; i++)
    {
      z = mymyrand() >> (BITS_IN_RANDOM-5); /* in [0,15] */
      if (z >= 9) z -= 7;
      a = gadd(a,gmulsg(z,(GEN)beta[i]));
    }
    if ((a = prime_check_elt(a,pol,p,pf)))
    {
      if (DEBUGLEVEL) fprintferr("\n");
      (void)setrand(keep); return a;
    }
  }
}

/* Input: an ideal mod p, P != Z_K (Fp-basis, in matrix form)
 * Output: x such that P = (p,x) */
static GEN
uniformizer(GEN nf, GEN p, GEN P)
{
  GEN beta,a,pf, T = (GEN)nf[1];
  long f, N=degpol(T), m=lg(P)-1;
  gpmem_t av;

  if (!m) return gscalcol_i(p,N);

  /* we want v_p(Norm(beta)) = p^f, f = N-m */
  av = avma; f = N-m; pf = gpowgs(p,f);
  P = centermod(P, p);
  P = concatsp(gscalcol(p,N), P);
  P = ideal_better_basis(nf, P, p);
  beta = gmul((GEN)nf[7], P);

  a = random_uniformizer_loop(beta,T,p,pf);
  a = centermod(algtobasis_i(nf,a), p);
  if (!is_uniformizer(gmul((GEN)nf[7],a), T,pf,p)) a[1] = laddii((GEN)a[1],p);

  return gerepilecopy(av,a);
}

/* pr = (p,u) of ramification index e */
GEN
apply_kummer(GEN nf,GEN u,GEN e,GEN p)
{
  GEN T = (GEN)nf[1], pr = cgetg(6,t_VEC);
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
  {
    GEN t, pf = f==1? p: gpowgs(p,f);
    /* make sure v_pr(u) = 1 (automatic if e>1) */
    if (is_pm1(e) && !is_uniformizer(u, T,pf,p))
      u[2] = laddii((GEN)u[2], p);
    t = algtobasis_i(nf, FpX_div(T,u,p));
    pr[2] = (long)algtobasis_i(nf,u);
    pr[5] = (long)centermod(t, p);
  }
  return pr;
}

/* Assuming P = (p,u) prime, return tau such that p Z + tau Z = p P^(-1)*/
static GEN
anti_uniformizer(GEN nf, GEN p, GEN u)
{
  gpmem_t av = avma;
  GEN mat = eltmul_get_table(nf, u);
  return gerepileupto(av, FpM_deplin(mat,p));
}

static GEN
get_pr(GEN nf, GEN p, GEN H, long f)
{
  GEN pr, u = uniformizer(nf,p,H);
  GEN t = anti_uniformizer(nf,p,u);
  gpmem_t av = avma;
  long e = 1 + int_elt_val(nf,t,p,t,NULL);
  avma = av;
  pr = cgetg(6,t_VEC);
  pr[1] = (long)p;
  pr[2] = (long)u;
  pr[3] = lstoi(e);
  pr[4] = lstoi(f);
  pr[5] = (long)t; return pr;
}

/* prime ideal decomposition of p sorted by increasing residual degree */
GEN
primedec(GEN nf, GEN p)
{
  gpmem_t av = avma;
  long i,k,c,iL,N;
  GEN ex,F,L,Ip,H,phi,mat1,T,f,g,h,p1,UN;

  if (DEBUGLEVEL>2) timer2();
  nf = checknf(nf); T = (GEN)nf[1];
  F = factmod(T,p);
  ex = (GEN)F[2];
  F  = (GEN)F[1]; F = centerlift(F);
  if (DEBUGLEVEL>5) msgtimer("factmod");

  k = lg(F);
  if (signe(modii((GEN)nf[4],p))) /* p doesn't divide index */
  {
    L = cgetg(k,t_VEC);
    for (i=1; i<k; i++)
      L[i] = (long)apply_kummer(nf,(GEN)F[i],(GEN)ex[i],p);
    if (DEBUGLEVEL>5) msgtimer("simple primedec");
    return gerepileupto(av, vecsort(L, stoi(4)));
  }

  g = (GEN)F[1];
  for (i=2; i<k; i++) g = FpX_mul(g,(GEN)F[i], p);
  h = FpX_div(T,g,p);
  f = FpX_red(gdivexact(gsub(gmul(g,h), T), p), p);

  N = degpol(T);
  L = cgetg(N+1,t_VEC); iL = 1;
  for (i=1; i<k; i++)
    if (is_pm1(ex[i]) || signe(FpX_res(f,(GEN)F[i],p)))
      L[iL++] = (long)apply_kummer(nf,(GEN)F[i],(GEN)ex[i],p);
    else /* F[i] | (f,g,h), happens at least once by Dedekind criterion */
      ex[i] = 0;
  if (DEBUGLEVEL>2) msgtimer("Kummer factors");

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
        for (i=1; i<=n; i++)
        {
          H = (GEN)h[--c]; k = lg(H)-1;
          L[iL++] = (long)get_pr(nf,p,H, N-k);
        }
    }
    else /* A2 field ==> H maximal, f = N-k = dim(A2) */
      L[iL++] = (long)get_pr(nf,p,H, N-k);
    if (DEBUGLEVEL>2) msgtimer("h[%ld]",c);
  }
  setlg(L, iL);
  return gerepileupto(av, gen_sort(L,0,cmp_prime_over_p));
}

/* return [Fp[x]: Fp] */
static long
ffdegree(GEN x, GEN frob, GEN p)
{
  gpmem_t av = avma;
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
  z = eltmul_get_table(nf, z);
  z = hnfmodid(z, p);
  z = idealaddtoone_i(nf,pr,z);
  return unnf_minus_x(z);
}

GEN
nfmodprinit(GEN nf, GEN pr)
{
  gpmem_t av = avma;
  GEN res, tau, mul, x, p, T, pow, ffproj, nfproj, prh, c, gf = (GEN)pr[4];
  long N, i, k, f = itos(gf);

  nf = checknf(nf); checkprimeid(pr);
  N = degpol(nf[1]);
  prh = prime_to_ideal(nf, pr);
  tau = anti_uniformizer2(nf, pr);
  p = (GEN)pr[1];

  if (f == 1)
  {
    ffproj = cgetg(N+1, t_VEC);
    ffproj[1] = un;
    for (i=2; i<=N; i++)
    {
      x = gcoeff(prh,1,i);
      if (signe(x)) x = subii(p,x);
      ffproj[i] = (long)x;
    }
    res = cgetg(5, t_COL);
    res[1] = (long)prh;
    res[2] = (long)tau;
    res[3] = (long)ffproj;
    res[4] = (long)pr; return gerepilecopy(av, res);
  }

  c = cgetg(f+1, t_VECSMALL);
  ffproj = cgetg(N+1, t_MAT);
  for (k=i=1; i<=N; i++)
  {
    x = gcoeff(prh, i,i);
    if (!is_pm1(x)) { c[k] = i; ffproj[i] = (long)_ei(N, i); k++; }
    else
      ffproj[i] = lneg((GEN)prh[i]);
  }
  ffproj = rowextract_p(ffproj, c);
  if (! divise((GEN)nf[4], p))
  {
    GEN basis, proj_modT;
    if (N == f) T = (GEN)nf[1]; /* pr inert */
    else
      T = primpart(gmul((GEN)nf[7], (GEN)pr[2]));

    basis = (GEN)nf[7];
    proj_modT = cgetg(f+1, t_MAT);
    for (i=1; i<=f; i++)
    {
      GEN cx, p1 = primitive_part((GEN)basis[c[i]], &cx);
      if (cx)
      {
        cx = gmod(cx, p);
        p1 = FpX_Fp_mul(FpX_rem(p1, T, p), cx, p);
      }
      proj_modT[i] = (long)pol_to_vec(p1, f);
    }
    ffproj = FpM_mul(proj_modT,ffproj,p);

    if (N == f) T = (GEN)nf[1]; /* pr inert */
    else
      T = primpart(gmul((GEN)nf[7], (GEN)pr[2]));
    res = cgetg(6, t_COL);
    res[1] = (long)prh;
    res[2] = (long)tau;
    res[3] = (long)ffproj;
    res[4] = (long)pr;
    res[5] = (long)T; return gerepilecopy(av, res);
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
    u = _ei(f,2); k = 2;
    deg1 = ffdegree(u, frob, p);
    while (deg1 < f)
    {
      k++; u2 = _ei(f, k);
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

  res = cgetg(7, t_COL);
  res[1] = (long)prh;
  res[2] = (long)tau;
  res[3] = (long)ffproj;
  res[4] = (long)pr;
  res[5] = (long)T;
  res[6] = (long)nfproj; return gerepilecopy(av, res);
}

void
checkmodpr(GEN modpr)
{
  if (typ(modpr) != t_COL || lg(modpr) < 5)
    err(talker,"incorrect modpr format");
  checkprimeid((GEN)modpr[4]);
}

GEN
nf_to_ff_init(GEN nf, GEN *pr, GEN *T, GEN *p)
{
  GEN modpr = (typ(*pr) == t_COL)? *pr: nfmodprinit(nf, *pr);
  *T = lg(modpr)==5? NULL: (GEN)modpr[5];
  *pr = (GEN)modpr[4];
  *p = (GEN)(*pr)[1]; return modpr;
}

/* assume x in 'basis' form (t_COL) */
GEN
zk_to_ff(GEN x, GEN modpr)
{
  GEN pr = (GEN)modpr[4];
  GEN p = (GEN)pr[1];
  GEN y = gmul((GEN)modpr[3], x);
  if (lg(modpr) == 5) return modii(y,p);
  y = FpV_red(y, p);
  return col_to_ff(y, varn(modpr[5]));
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
  if (v) x = element_mul(nf,x, element_pow(nf,(GEN)modpr[2],stoi(v)));
  x = primitive_part(x, &cx);
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
  gpmem_t av = avma;
  long i;
  GEN p, prh;

  checkmodpr(modpr);
  if (typ(x) != t_COL) x = algtobasis(nf,x);
  for (i=lg(x)-1; i>0; i--)
    if (typ(x[i]) == t_INTMOD) { x = lift(x); break; }
  prh = (GEN)modpr[1]; p = gcoeff(prh,1,1);
  x = kill_denom(x, nf, p, modpr);
  return gerepilecopy(av, nfreducemodpr_i(x, prh));
}

GEN
nf_to_ff(GEN nf, GEN x, GEN modpr)
{
  gpmem_t av = avma;
  GEN pr = (GEN)modpr[4];
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
  if (lg(modpr) < 7) return x;
  return mulmat_pol((GEN)modpr[6], x);
}

/* reduce the coefficients of pol modulo modpr */
GEN
modprX(GEN x, GEN nf,GEN modpr)
{
  long i, l;
  GEN z;

  if (typ(x)!=t_POL) return nf_to_ff(nf,x,modpr);
  l = lgef(x);
  z = cgetg(l,t_POL); z[1] = x[1];
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
  long i,l = lg(z), m;
  GEN x;

  if (typ(z) != t_MAT) return modprV(z,nf,modpr);
  x = cgetg(l,t_MAT); if (l==1) return x;
  m = lg((GEN)z[1]);
  for (i=1; i<l; i++) x[i] = (long)modprV((GEN)z[i],nf,modpr);
  return x;
}

/*                        relative ROUND 2
 *
 * input: nf = base field K
 *   x monic polynomial, coefficients in Z_K, degree n defining a relative
 *   extension L=K(theta).
 *   One MUST have varn(x) < varn(nf[1]).
 * output: a pseudo-basis [A,I] of Z_L, where A is in M_n(K) in HNF form and
 *   I a vector of n ideals.
 */

/* given MODULES x and y by their pseudo-bases in HNF, gives a
 * pseudo-basis of the module generated by x and y. */
static GEN
rnfjoinmodules(GEN nf, GEN x, GEN y)
{
  long i,lx,ly;
  GEN p1,p2,z,Hx,Hy,Ix,Iy;

  if (x == NULL) return y;
  Hx = (GEN)x[1]; lx = lg(Hx); Ix = (GEN)x[2];
  Hy = (GEN)y[1]; ly = lg(Hy); Iy = (GEN)y[2];
  i = lx+ly-1;
  z = (GEN)gpmalloc(sizeof(long*)*(3+2*i));
  *z = evaltyp(t_VEC)|evallg(3);
  p1 =  z+3; z[1]=(long)p1; *p1 = evaltyp(t_MAT)|evallg(i);
  p2 = p1+i; z[2]=(long)p2; *p2 = evaltyp(t_VEC)|evallg(i);

  for (i=1; i<lx; i++) { p1[i] = Hx[i]; p2[i] = Ix[i]; }
  p1 += lx-1;
  p2 += lx-1;
  for (i=1; i<ly; i++) { p1[i] = Hy[i]; p2[i] = Iy[i]; }
  x = nfhermite(nf,z); free(z); return x;
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
  return FpVQX_red(z,D->T,D->p);
}
static GEN
_sqr(void *data, GEN x)
{
  rnfeltmod_muldata *D = (rnfeltmod_muldata *) data;
  GEN z = x? sqr_by_tab(D->multab,x)
           : element_mulidid(D->multab,D->h,D->h);
  return FpVQX_red(z,D->T,D->p);
}

/* Compute x^n mod pr in the extension, assume n >= 0 */
static GEN
rnfelementid_powmod(GEN multab, long h, GEN n, GEN T, GEN p)
{
  gpmem_t av = avma;
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

static GEN
mat_ff_to_nf(GEN x, GEN modpr)
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

static GEN
rnfordmax(GEN nf, GEN pol, GEN pr)
{
  gpmem_t av=avma,av1,lim;
  long i,j,k,n,v1,v2,vpol,m,cmpt,sep;
  GEN p,T,q,q1,modpr,A,Aa,Aaa,A1,I,R,p1,p2,p3,multab,multabmod,Aainv;
  GEN pip,baseIp,baseOp,alpha,matprod,alphainv,matC,matG,vecpro,matH;
  GEN neworder,H,Hid,alphalistinv,alphalist,prhinv,nfT,id,rnfId;

  if (DEBUGLEVEL>1) fprintferr(" treating %Z\n",pr);
  modpr = nf_to_ff_init(nf,&pr,&T,&p);
  p1 = rnfdedekind(nf,pol,modpr);
  if (gcmp1((GEN)p1[1])) return gerepilecopy(av,(GEN)p1[2]);

  sep = itos((GEN)p1[3]);
  A = gmael(p1,2,1);
  I = gmael(p1,2,2);

  pip = basistoalg(nf, (GEN)pr[2]);
  nfT = (GEN)nf[1]; pol = lift(pol);
  n = degpol(pol); vpol = varn(pol);
  q = T? gpowgs(p,degpol(T)): p;
  q1 = q; while (cmpis(q1,n) < 0) q1 = mulii(q1,q);
  rnfId = idmat(degpol(pol));
  id    = idmat(degpol(nfT));

  multab = cgetg(n*n+1,t_MAT);
  for (j=1; j<=n*n; j++) multab[j] = lgetg(n+1,t_COL);
  prhinv = idealinv(nf, pr);
  alphalistinv = cgetg(n+1,t_VEC);
  alphalist    = cgetg(n+1,t_VEC);
  A1 = cgetg(n+1,t_MAT);
  av1 = avma; lim = stack_lim(av1,1);
  for(cmpt=1; ; cmpt++)
  {
    if (DEBUGLEVEL>1) fprintferr("    %ld%s pass\n",cmpt,eng_ord(cmpt));
    for (j=1; j<=n; j++)
    {
      if (gegal((GEN)I[j],id))
      {
        alphalist[j] = alphalistinv[j] = un;
        A1[j] = A[j]; continue;
      }

      p1 = ideal_two_elt(nf,(GEN)I[j]);
      if (gcmp0((GEN)p1[1]))
        alpha = (GEN)p1[2];
      else
      {
        v1 = element_val(nf,(GEN)p1[1],pr);
        v2 = element_val(nf,(GEN)p1[2],pr);
        alpha = (v1>v2)? (GEN)p1[2]: (GEN)p1[1];
      }
      alphalist[j]    = (long)alpha;
      alphalistinv[j] = (long)element_inv(nf,alpha);

      p1 = cgetg(n+1,t_COL); A1[j] = (long)p1;
      for (i=1; i<=n; i++)
        p1[i] = (long)element_mul(nf,gcoeff(A,i,j),alpha);
    }
    Aa = basistoalg(nf,A1);
    Aainv = lift_intern(ginv(Aa));
    Aaa = lift_intern(mat_to_vecpol(Aa,vpol));
    for (i=1; i<=n; i++)
      for (j=i; j<=n; j++)
      {
        long tp;
        p1 = RXQX_rem(gmul((GEN)Aaa[i],(GEN)Aaa[j]), pol, nfT);
        tp = typ(p1);
        if (is_scalar_t(tp) || (tp==t_POL && varn(p1)>vpol))
          p2 = gmul(p1, (GEN)Aainv[1]);
        else
          p2 = mulmat_pol(Aainv, p1);
        for (k=1; k<=n; k++)
        {
          GEN c = gres((GEN)p2[k], nfT);
          coeff(multab,k,(i-1)*n+j) = (long)c;
          coeff(multab,k,(j-1)*n+i) = (long)c;
        }
      }
    multabmod = modprM(multab,nf,modpr);
    R = cgetg(n+1,t_MAT);
    R[1] = rnfId[1];
    for (j=2; j<=n; j++)
      R[j] = (long) rnfelementid_powmod(multabmod,j,q1,T,p);
    baseIp = FqM_ker(R,T,p);
    baseOp = lg(baseIp)==1? rnfId: FqM_suppl(baseIp,T,p);
    alpha = mat_ff_to_nf(baseOp, modpr);
    for (j=1; j<lg(baseIp); j++)
    {
      p1 = (GEN)alpha[j];
      for (i=1; i<=n; i++) p1[i] = (long)to_polmod((GEN)p1[i], nfT);
    }
    for (   ; j<=n; j++)
    {
      p1 = (GEN)alpha[j];
      for (i=1; i<=n; i++) p1[i] = lmul(pip, (GEN)p1[i]);
    }
    alphainv = lift_intern(ginv(alpha));
    alpha = lift_intern(alpha);

    matprod = cgetg(n+1,t_MAT);
    for (j=1; j<=n; j++)
    {
      p1 = cgetg(n+1,t_COL); matprod[j] = (long)p1;
      for (i=1; i<=n; i++)
        p1[i] = (long)gmod(element_mulid(multab, (GEN)alpha[i],j), nfT);
    }
    matC = cgetg(n+1,t_MAT);
    for (j=1; j<=n; j++)
    {
      p1 = cgetg(n*n+1,t_COL); matC[j] = (long)p1;
      for (i=1; i<=n; i++)
      {
	p2 = gmul(alphainv, gcoeff(matprod,i,j));
	for (k=1; k<=n; k++)
        {
          GEN c = gres((GEN)p2[k], nfT);
          p1[(i-1)*n+k] = (long)nf_to_ff(nf,c,modpr);
        }
      }
    }
    matG = FqM_ker(matC,T,p); m = lg(matG)-1;
    matG = mat_ff_to_nf(matG, modpr);
    vecpro = cgetg(3,t_VEC);
    vecpro[1] = (long)concatsp(matG,rnfId);

    p2 = cgetg(n+m+1,t_VEC);
    vecpro[2] = (long)p2;
    for (j=1; j<=m; j++) p2[j] = (long)prhinv;
    p2 += m;
    for (j=1; j<=n; j++)
      p2[j] = (long)idealmul(nf,(GEN)I[j],(GEN)alphalistinv[j]);

    matH = nfhermite(nf,vecpro);
    p1 = algtobasis(nf, gmul(Aa, basistoalg(nf,(GEN)matH[1])));
    p2 = (GEN)matH[2];

    neworder = cgetg(3,t_VEC);
    H   = cgetg(n+1,t_MAT);
    Hid = cgetg(n+1,t_VEC);
    for (j=1; j<=n; j++)
    {
      alphainv = (GEN)alphalistinv[j];
      if (alphainv == gun) { H[j] = p1[j]; Hid[j] = p2[j]; continue; }

      p3=cgetg(n+1,t_COL); H[j]=(long)p3;
      for (i=1; i<=n; i++)
	p3[i] = (long)element_mul(nf,gcoeff(p1,i,j),alphainv);
      Hid[j] = (long)idealmul(nf,(GEN)p2[j],(GEN)alphalist[j]);
    }
    if (DEBUGLEVEL>3) { fprintferr(" new order:\n"); outerr(H); outerr(Hid); }
    if (sep == 2 || gegal(I,Hid))
    {
      neworder[1] = (long)H;
      neworder[2] = (long)Hid;
      return gerepilecopy(av, neworder);
    }

    A = H; I = Hid;
    if (low_stack(lim, stack_lim(av1,1)) || (cmpt & 3) == 0)
    {
      GEN *gptr[2]; gptr[0]=&A; gptr[1]=&I;
      if(DEBUGMEM>1) err(warnmem,"rnfordmax");
      gerepilemany(av1,gptr,2);
    }
  }
}

static void
check_pol(GEN x, long v)
{
  long i,tx, lx = lgef(x);
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
  long i, vnf = varn(xnf), lx = lgef(x);
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

static GEN
rnfround2all(GEN nf, GEN pol, long all)
{
  gpmem_t av = avma;
  long i,j,n,N,nbidp,vpol,*ep;
  GEN A,p1,p2,p3,p4,nfT,list,id,I,W,pseudo,y,d,D,sym,unnf;

  nf=checknf(nf); nfT=(GEN)nf[1]; vpol=varn(pol);
  pol = fix_relative_pol(nf,pol,1);
  N = degpol(nfT);
  n = degpol(pol);
  list = idealfactor(nf, discsr(pol));
  ep  = (long*)list[2];
  list= (GEN)  list[1];
  nbidp=lg(list)-1; for(i=1;i<=nbidp;i++) ep[i] = itos((GEN)ep[i]);
  if (DEBUGLEVEL>1)
  {
    fprintferr("Ideals to consider:\n");
    for (i=1; i<=nbidp; i++)
      if (ep[i]>1) fprintferr("%Z^%ld\n",list[i],ep[i]);
    flusherr();
  }
  id = idmat(N); unnf = (GEN)id[1];
  pseudo = NULL;
  for (i=1; i<=nbidp; i++)
    if (ep[i] > 1)
    {
      y = rnfordmax(nf,pol,(GEN)list[i]);
      pseudo = rnfjoinmodules(nf,pseudo,y);
    }
  if (pseudo)
  {
    A = (GEN)pseudo[1];
    I = (GEN)pseudo[2];
  }
  else
  {
    I = cgetg(n+1,t_VEC); for (i=1; i<=n; i++) I[i]=(long)id;
    A = idmat_intern(n, unnf, zerocol(N));
  }
  W = mat_to_vecpol(lift_intern(basistoalg(nf,A)), vpol);
  sym = polsym(pol,n-1);
  pol = lift(pol);
  p2 = cgetg(n+1,t_MAT); for (j=1; j<=n; j++) p2[j] = lgetg(n+1,t_COL);
  for (j=1; j<=n; j++)
    for (i=j; i<=n; i++)
    {
      p1 = RXQX_mul((GEN)W[i],(GEN)W[j], nfT);
      p1 = RXQX_rem(p1, pol, nfT);
      coeff(p2,j,i)=coeff(p2,i,j)=(long)quicktrace(p1,sym);
    }
  d = algtobasis_i(nf, det(p2));

  i=1; while (i<=n && gegal((GEN)I[i],id)) i++;
  if (i>n) D=id;
  else
  {
    D = (GEN)I[i];
    for (i++; i<=n; i++)
      if (!gegal((GEN)I[i],id)) D = idealmul(nf,D,(GEN)I[i]);
    D = idealpow(nf,D,gdeux);
  }
  p4 = gun; p3 = auxdecomp(content(d),0);
  for (i=1; i<lg(p3[1]); i++)
    p4 = gmul(p4, gpowgs(gcoeff(p3,i,1), itos(gcoeff(p3,i,2))>>1));
  p4 = gsqr(p4);
  i = all? 2: 0;
  p1=cgetg(3 + i,t_VEC);
  if (i) { p1[1] = lcopy(A); p1[2] = lcopy(I); }
  p1[1+i] = (long)idealmul(nf,D,d);
  p1[2+i] = ldiv(d,p4);
  return gerepileupto(av,p1);
}

GEN
rnfpseudobasis(GEN nf, GEN pol)
{
  return rnfround2all(nf,pol,1);
}

GEN
rnfdiscf(GEN nf, GEN pol)
{
  return rnfround2all(nf,pol,0);
}

/* given bnf as output by buchinit and a pseudo-basis of an order
 * in HNF [A,I] (or [A,I,D,d] it does not matter), tries to simplify the
 * HNF as much as possible. The resulting matrix will be upper triangular
 * but the diagonal coefficients will not be equal to 1. The ideals
 * are guaranteed to be integral and primitive.
 */
GEN
rnfsimplifybasis(GEN bnf, GEN order)
{
  gpmem_t av=avma,tetpil;
  long j,N,n;
  GEN p1,id,Az,Iz,nf,A,I;

  bnf = checkbnf(bnf);
  if (typ(order)!=t_VEC || lg(order)<3)
    err(talker,"not a pseudo-basis in nfsimplifybasis");
  A=(GEN)order[1]; I=(GEN)order[2]; n=lg(A)-1; nf=(GEN)bnf[7];
  N=degpol(nf[1]); id=idmat(N); Iz=cgetg(n+1,t_VEC); Az=cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++)
  {
    if (gegal((GEN)I[j],id)) { Iz[j]=(long)id; Az[j]=A[j]; }
    else
    {
      p1=content((GEN)I[j]);
      if (!gcmp1(p1))
      {
	Iz[j]=(long)gdiv((GEN)I[j],p1); Az[j]=lmul((GEN)A[j],p1);
      }
      else Az[j]=A[j];
      if (!gegal((GEN)Iz[j],id))
      {
	p1=isprincipalgen(bnf,(GEN)Iz[j]);
	if (gcmp0((GEN)p1[1]))
	{
	  p1=(GEN)p1[2]; Iz[j]=(long)id;
	  Az[j]=(long)element_mulvec(nf,p1,(GEN)Az[j]);
	}
      }
    }
  }
  tetpil=avma; p1=cgetg(lg(order),t_VEC); p1[1]=lcopy(Az); p1[2]=lcopy(Iz);
  for (j=3; j<lg(order); j++) p1[j]=lcopy((GEN)order[j]);
  return gerepile(av,tetpil,p1);
}

GEN
rnfdet2(GEN nf, GEN A, GEN I)
{
  gpmem_t av,tetpil;
  long i;
  GEN p1;

  nf=checknf(nf); av = tetpil = avma;
  p1=idealhermite(nf,det(matbasistoalg(nf,A)));
  for(i=1;i<lg(I);i++) { tetpil=avma; p1=idealmul(nf,p1,(GEN)I[i]); }
  tetpil=avma; return gerepile(av,tetpil,p1);
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
  gpmem_t av = avma;
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

/* given a pseudo-basis of an order in HNF [A,I] (or [A,I,D,d]), gives an
 * n x n matrix (not in HNF) of a pseudo-basis and an ideal vector
 * [id,id,...,id,I] such that order = nf[7]^(n-1) x I.
 * Uses the approximation theorem ==> slow. */
GEN
rnfsteinitz(GEN nf, GEN order)
{
  gpmem_t av = avma;
  long i,n,l;
  GEN Id,A,I,p1,a,b;

  nf = checknf(nf);
  Id = idmat(degpol(nf[1]));
  if (typ(order) == t_POL) order = rnfpseudobasis(nf,order);
  l = lg(order);
  if (typ(order)!=t_VEC || l < 3)
    err(talker,"not a pseudo-matrix in rnfsteinitz");
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
      I[i+1]= (long)primitive_part(idealmul(nf,a,b), &p1);
      if (p1) A[i+1] = (long)element_mulvec(nf, p1,(GEN)A[i+1]);
    }
  }
  p1 = cgetg(l,t_VEC);
  p1[1]=(long)A;
  p1[2]=(long)I; for (i=3; i<l; i++) p1[i]=order[i];
  return gerepilecopy(av, p1);
}

/* Given bnf as output by buchinit and either an order as output by
 * rnfpseudobasis or a polynomial, and outputs a basis if it is free,
 * an n+1-generating set if it is not
 */
GEN
rnfbasis(GEN bnf, GEN order)
{
  gpmem_t av = avma;
  long j,N,n;
  GEN nf,A,I,classe,p1,p2,id;

  bnf = checkbnf(bnf);
  nf=(GEN)bnf[7]; N=degpol(nf[1]); id=idmat(N);
  if (typ(order)==t_POL) order=rnfpseudobasis(nf,order);
  if (typ(order)!=t_VEC || lg(order)<3)
    err(talker,"not a pseudo-matrix in rnfbasis");
  A=(GEN)order[1]; I=(GEN)order[2]; n=lg(A)-1;
  j=1; while (j<n && gegal((GEN)I[j],id)) j++;
  if (j<n) order=rnfsteinitz(nf,order);
  A=(GEN)order[1]; I=(GEN)order[2]; classe=(GEN)I[n];
  p1=isprincipalgen(bnf,classe);
  if (gcmp0((GEN)p1[1]))
  {
    p2=cgetg(n+1,t_MAT);
    p2[n]=(long)element_mulvec(nf,(GEN)p1[2],(GEN)A[n]);
  }
  else
  {
    p1=ideal_two_elt(nf,classe);
    p2=cgetg(n+2,t_MAT);
    p2[n]=lmul((GEN)p1[1],(GEN)A[n]);
    p2[n+1]=(long)element_mulvec(nf,(GEN)p1[2],(GEN)A[n]);
  }
  for (j=1; j<n; j++) p2[j]=A[j];
  return gerepilecopy(av,p2);
}

/* Given bnf as output by buchinit and either an order as output by
 * rnfpseudobasis or a polynomial, and outputs a basis (not pseudo)
 * in Hermite Normal Form if it exists, zero if not
 */
GEN
rnfhermitebasis(GEN bnf, GEN order)
{
  gpmem_t av = avma;
  long j,n;
  GEN nf,A,I,p1,id;

  bnf = checkbnf(bnf); nf=(GEN)bnf[7];
  id = idmat(degpol(nf[1]));
  if (typ(order)==t_POL)
  {
    order = rnfpseudobasis(nf,order);
    A = (GEN)order[1];
  }
  else
  {
    if (typ(order)!=t_VEC || lg(order)<3)
      err(talker,"not a pseudo-matrix in rnfbasis");
    A = dummycopy((GEN)order[1]);
  }
  I=(GEN)order[2]; n=lg(A)-1;
  for (j=1; j<=n; j++)
  {
    if (gegal((GEN)I[j],id)) continue;

    p1 = isprincipalgen(bnf,(GEN)I[j]);
    if (!gcmp0((GEN)p1[1])) { avma = av; return gzero; }
    A[j] = (long)element_mulvec(nf,(GEN)p1[2],(GEN)A[j]);
  }
  return gerepilecopy(av,A);
}

long
rnfisfree(GEN bnf, GEN order)
{
  gpmem_t av=avma;
  long n,N,j;
  GEN nf,p1,id,I;

  bnf = checkbnf(bnf);
  if (gcmp1(gmael3(bnf,8,1,1))) return 1;

  nf=(GEN)bnf[7]; N=degpol(nf[1]); id=idmat(N);
  if (typ(order)==t_POL) order=rnfpseudobasis(nf,order);
  if (typ(order)!=t_VEC || lg(order)<3)
    err(talker,"not a pseudo-matrix in rnfisfree");

  I=(GEN)order[2]; n=lg(I)-1;
  j=1; while (j<=n && gegal((GEN)I[j],id)) j++;
  if (j>n) { avma=av; return 1; }

  p1=(GEN)I[j];
  for (j++; j<=n; j++)
    if (!gegal((GEN)I[j],id)) p1=idealmul(nf,p1,(GEN)I[j]);
  j = gcmp0(isprincipal(bnf,p1));
  avma=av; return j;
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
  gpmem_t av = avma;
  long v,k;
  GEN C, LPRS;

  if (typ(A)!=t_POL || typ(B)!=t_POL) err(typeer,"polcompositum0");
  if (degpol(A)<=0 || degpol(B)<=0) err(constpoler,"compositum");
  v = varn(A);
  if (varn(B) != v) err(talker,"not the same variable in compositum");
  C = content(A); if (!gcmp1(C)) A = gdiv(A, C);
  C = content(B); if (!gcmp1(C)) B = gdiv(B, C);
  check_pol_int(A,"compositum");
  check_pol_int(B,"compositum");
  if (!ZX_is_squarefree(A)) err(talker,"compositum: %Z not separable", A);
  if (!ZX_is_squarefree(B)) err(talker,"compositum: %Z not separable", B);

  k = 1; C = ZY_ZXY_resultant_all(A, B, &k, flall? &LPRS: NULL);
  C = DDF2(C, 0); /* C = Res_Y (A, B(X + kY)) guaranteed squarefree */
  C = sort_vecpol(C);
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
  gpmem_t av = avma;
  GEN g, y = derivpol(x);
  if (isrational(x))
    g = modulargcd(x, y);
  else
    g = nfgcd(x, y, nf, NULL);
  avma = av; return (degpol(g) == 0);
}

GEN
rnfequation0(GEN nf, GEN B, long flall)
{
  gpmem_t av = avma;
  long v,vpol,k,lA,lB;
  GEN A,C,LPRS;

  if (typ(nf)==t_POL) A=nf; else { nf=checknf(nf); A=(GEN)nf[1]; }
  B = fix_relative_pol(nf,B,1);
  v   = varn(A); lA = lgef(A);
  vpol= varn(B); lB = lgef(B);
  if (lA<=3 || lB<=3) err(constpoler,"rnfequation");

  check_pol_int(A,"rnfequation");
  B = primpart(lift_intern(B));
  for (k=2; k<lB; k++)
    if (lgef(B[k]) >= lA) B[k] = lres((GEN)B[k],A);

  if (!nfissquarefree(A,B))
    err(talker,"not k separable relative equation in rnfequation");

  k = 0; C = ZY_ZXY_resultant_all(A, B, &k, flall? &LPRS: NULL);
  if (gsigne(leadingcoeff(C)) < 0) C = gneg_i(C);
  C = primpart(C);
  if (flall)
  {
    GEN w,a,b; /* a,b,c root of A,B,C = compositum, c = b - k a */
    /* invmod possibly very costly */
    a = gmul((GEN)LPRS[1], QX_invmod((GEN)LPRS[2], C));
    a = gneg_i(gmod(a, C));
    b = gadd(polx[v], gmulsg(k,a));
    w = cgetg(4,t_VEC); /* [C, a, n ] */
    w[1] = (long)C;
    w[2] = (long)to_polmod(a, (GEN)w[1]);
    w[3] = lstoi(-k); C = w;
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
  long i, ru = lg(x);
  GEN s;

  s = r1 ? (GEN)x[1] : gmul2n(greal((GEN)x[1]),1);
  for (i=2; i<=r1; i++) s=gadd(s,(GEN)x[i]);
  for ( ; i<ru; i++) s=gadd(s,gmul2n(greal((GEN)x[i]),1));
  return s;
}

static GEN
nftocomplex(GEN nf, GEN x)
{
  long ru,vnf,k;
  GEN p2,p3,ronf;

  p2 = (typ(x)==t_POLMOD)? (GEN)x[2]: gmul((GEN)nf[7],x);
  vnf=varn(nf[1]);
  ronf=(GEN)nf[6]; ru=lg(ronf); p3=cgetg(ru,t_COL);
  for (k=1; k<ru; k++) p3[k]=lsubst(p2,vnf,(GEN)ronf[k]);
  return p3;
}

static GEN
rnfscal(GEN mth, GEN xth, GEN yth)
{
  long n,ru,i,j,kk;
  GEN x,y,m,res,p1,p2;

  n=lg(mth)-1; ru=lg(gcoeff(mth,1,1));
  res=cgetg(ru,t_COL);
  for (kk=1; kk<ru; kk++)
  {
    m=cgetg(n+1,t_MAT);
    for (j=1; j<=n; j++)
    {
      p1=cgetg(n+1,t_COL); m[j]=(long)p1;
      for (i=1; i<=n; i++) { p2=gcoeff(mth,i,j); p1[i]=p2[kk]; }
    }
    x=cgetg(n+1,t_VEC);
    for (j=1; j<=n; j++) x[j]=(long)gconj((GEN)((GEN)xth[j])[kk]);
    y=cgetg(n+1,t_COL);
    for (j=1; j<=n; j++) y[j]=((GEN)yth[j])[kk];
    res[kk]=(long)gmul(x,gmul(m,y));
  }
  return res;
}

static GEN
rnfdiv(GEN x, GEN y)
{
  long i, ru = lg(x);
  GEN z;

  z=cgetg(ru,t_COL);
  for (i=1; i<ru; i++) z[i]=(long)gdiv((GEN)x[i],(GEN)y[i]);
  return z;
}

static GEN
rnfmul(GEN x, GEN y)
{
  long i, ru = lg(x);
  GEN z;

  z=cgetg(ru,t_COL);
  for (i=1; i<ru; i++) z[i]=(long)gmul((GEN)x[i],(GEN)y[i]);
  return z;
}

static GEN
rnfvecmul(GEN x, GEN v)
{
  long i, lx = lg(v);
  GEN y;

  y=cgetg(lx,typ(v));
  for (i=1; i<lx; i++) y[i]=(long)rnfmul(x,(GEN)v[i]);
  return y;
}

static GEN
allonge(GEN v, long N)
{
  long r,r2,i;
  GEN y;

  r=lg(v)-1; r2=N-r;
  y=cgetg(N+1,t_COL);
  for (i=1; i<=r; i++) y[i]=v[i];
  for ( ; i<=N; i++) y[i]=(long)gconj((GEN)v[i-r2]);
  return y;
}

static GEN
findmin(GEN nf, GEN ideal, GEN muf,long prec)
{
  gpmem_t av=avma,tetpil;
  long N,i;
  GEN m,y;

  m = qf_base_change(gmael(nf,5,3), ideal, 0); /* nf[5][3] = T2 */
  m = lllgramintern(m,4,1,prec);
  if (!m)
  {
    m = lllint(ideal);
    m = qf_base_change(gmael(nf,5,3), gmul(ideal,m), 0);
    m = lllgramintern(m,4,1,prec);
    if (!m) err(precer,"rnflllgram");
  }
  ideal=gmul(ideal,m);
  N=lg(ideal)-1; y=cgetg(N+1,t_MAT);
  for (i=1; i<=N; i++)
    y[i] = (long) allonge(nftocomplex(nf,(GEN)ideal[i]),N);
  m=ground(greal(gauss(y,allonge(muf,N))));
  tetpil=avma; return gerepile(av,tetpil,gmul(ideal,m));
}

#define swap(x,y) { long _t=x; x=y; y=_t; }

/* given a base field nf (e.g main variable y), a polynomial pol with
 * coefficients in nf    (e.g main variable x), and an order as output
 * by rnfpseudobasis, outputs a reduced order.
 */
GEN
rnflllgram(GEN nf, GEN pol, GEN order,long prec)
{
  gpmem_t av=avma,tetpil;
  long i,j,k,l,kk,kmax,r1,ru,lx,vnf;
  GEN p1,p2,M,I,U,ronf,poll,unro,roorder,powreorder,mth,s,MC,MPOL,MCS;
  GEN B,mu,Bf,temp,ideal,x,xc,xpol,muf,mufc,muno,y,z,Ikk_inv;

/* Initializations and verifications */

  nf=checknf(nf);
  if (typ(order)!=t_VEC || lg(order)<3)
    err(talker,"not a pseudo-matrix in rnflllgram");
  M=(GEN)order[1]; I=(GEN)order[2]; lx=lg(I);
  if (lx < 3) return gcopy(order);
  if (lx-1 != degpol(pol)) err(consister,"rnflllgram");
  U=idmat(lx-1); I = dummycopy(I);

/* Compute the relative T2 matrix of powers of theta */

  vnf=varn(nf[1]); ronf=(GEN)nf[6]; ru=lg(ronf); poll=lift(pol);
  r1 = nf_get_r1(nf);
  unro=cgetg(lx,t_COL); for (i=1; i<lx; i++) unro[i]=un;
  roorder=cgetg(ru,t_VEC);
  for (i=1; i<ru; i++)
    roorder[i]=lroots(gsubst(poll,vnf,(GEN)ronf[i]),prec);
  powreorder=cgetg(lx,t_MAT);
  p1=cgetg(ru,t_COL); powreorder[1]=(long)p1;
  for (i=1; i<ru; i++) p1[i]=(long)unro;
  for (k=2; k<lx; k++)
  {
    p1=cgetg(ru,t_COL); powreorder[k]=(long)p1;
    for (i=1; i<ru; i++)
    {
      p2=cgetg(lx,t_COL); p1[i]=(long)p2;
      for (j=1; j<lx; j++)
	p2[j] = lmul(gmael(roorder,i,j),gmael3(powreorder,k-1,i,j));
    }
  }
  mth=cgetg(lx,t_MAT);
  for (l=1; l<lx; l++)
  {
    p1=cgetg(lx,t_COL); mth[l]=(long)p1;
    for (k=1; k<lx; k++)
    {
      p2=cgetg(ru,t_COL); p1[k]=(long)p2;
      for (i=1; i<ru; i++)
      {
	s=gzero;
	for (j=1; j<lx; j++)
	  s = gadd(s,gmul(gconj(gmael3(powreorder,k,i,j)),
	                  gmael3(powreorder,l,i,j)));
	p2[i]=(long)s;
      }
    }
  }

/* Transform the matrix M into a matrix with coefficients in K and also
   with coefficients polymod */

  MC=cgetg(lx,t_MAT); MPOL=cgetg(lx,t_MAT);
  for (j=1; j<lx; j++)
  {
    p1=cgetg(lx,t_COL); MC[j]=(long)p1;
    p2=cgetg(lx,t_COL); MPOL[j]=(long)p2;
    for (i=1; i<lx; i++)
    {
      p2[i]=(long)basistoalg(nf,gcoeff(M,i,j));
      p1[i]=(long)nftocomplex(nf,(GEN)p2[i]);
    }
  }
  MCS=cgetg(lx,t_MAT);

/* Start LLL algorithm */

  mu=cgetg(lx,t_MAT); B=cgetg(lx,t_COL);
  for (j=1; j<lx; j++)
  {
    p1=cgetg(lx,t_COL); mu[j]=(long)p1; for (i=1; i<lx; i++) p1[i]=zero;
    B[j]=zero;
  }
  kk=2; if (DEBUGLEVEL) fprintferr("kk = %ld ",kk);
  kmax=1; B[1]=lreal(rnfscal(mth,(GEN)MC[1],(GEN)MC[1]));
  MCS[1]=lcopy((GEN)MC[1]);
  do
  {
    if (kk>kmax)
    {
/* Incremental Gram-Schmidt */
      kmax=kk; MCS[kk]=lcopy((GEN)MC[kk]);
      for (j=1; j<kk; j++)
      {
	coeff(mu,kk,j) = (long) rnfdiv(rnfscal(mth,(GEN)MCS[j],(GEN)MC[kk]),
	                              (GEN) B[j]);
	MCS[kk] = lsub((GEN) MCS[kk], rnfvecmul(gcoeff(mu,kk,j),(GEN)MCS[j]));
      }
      B[kk] = lreal(rnfscal(mth,(GEN)MCS[kk],(GEN)MCS[kk]));
      if (gcmp0((GEN)B[kk])) err(lllger3);
    }

/* RED(k,k-1) */
    l=kk-1; Ikk_inv=idealinv(nf, (GEN)I[kk]);
    ideal=idealmul(nf,(GEN)I[l],Ikk_inv);
    x=findmin(nf,ideal,gcoeff(mu,kk,l),2*prec-2);
    if (!gcmp0(x))
    {
      xpol=basistoalg(nf,x); xc=nftocomplex(nf,xpol);
      MC[kk]=lsub((GEN)MC[kk],rnfvecmul(xc,(GEN)MC[l]));
      U[kk]=lsub((GEN)U[kk],gmul(xpol,(GEN)U[l]));
      coeff(mu,kk,l)=lsub(gcoeff(mu,kk,l),xc);
      for (i=1; i<l; i++)
	coeff(mu,kk,i)=lsub(gcoeff(mu,kk,i),rnfmul(xc,gcoeff(mu,l,i)));
    }
/* Test LLL condition */
    p1=nftau(r1,gadd((GEN) B[kk],
                     gmul(gnorml2(gcoeff(mu,kk,kk-1)),(GEN)B[kk-1])));
    p2=gdivgs(gmulsg(9,nftau(r1,(GEN)B[kk-1])),10);
    if (gcmp(p1,p2)<=0)
    {
/* Execute SWAP(k) */
      k=kk;
      swap(MC[k-1],MC[k]);
      swap(U[k-1],U[k]);
      swap(I[k-1],I[k]);
      for (j=1; j<=k-2; j++) swap(coeff(mu,k-1,j),coeff(mu,k,j));
      muf=gcoeff(mu,k,k-1);
      mufc=gconj(muf); muno=greal(rnfmul(muf,mufc));
      Bf=gadd((GEN)B[k],rnfmul(muno,(GEN)B[k-1]));
      p1=rnfdiv((GEN)B[k-1],Bf);
      coeff(mu,k,k-1)=(long)rnfmul(mufc,p1);
      temp=(GEN)MCS[k-1];
      MCS[k-1]=ladd((GEN)MCS[k],rnfvecmul(muf,(GEN)MCS[k-1]));
      MCS[k]=lsub(rnfvecmul(rnfdiv((GEN)B[k],Bf),temp),
		  rnfvecmul(gcoeff(mu,k,k-1),(GEN)MCS[k]));
      B[k]=(long)rnfmul((GEN)B[k],p1); B[k-1]=(long)Bf;
      for (i=k+1; i<=kmax; i++)
      {
	temp=gcoeff(mu,i,k);
	coeff(mu,i,k)=lsub(gcoeff(mu,i,k-1),rnfmul(muf,gcoeff(mu,i,k)));
	coeff(mu,i,k-1) = ladd(temp, rnfmul(gcoeff(mu,k,k-1),gcoeff(mu,i,k)));
      }
      if (kk>2) { kk--; if (DEBUGLEVEL) fprintferr("%ld ",kk); }
    }
    else
    {
      for (l=kk-2; l; l--)
      {
/* RED(k,l) */
	ideal=idealmul(nf,(GEN)I[l],Ikk_inv);
	x=findmin(nf,ideal,gcoeff(mu,kk,l),2*prec-2);
	if (!gcmp0(x))
	{
          xpol=basistoalg(nf,x); xc=nftocomplex(nf,xpol);
	  MC[kk]=(long)gsub((GEN)MC[kk],rnfvecmul(xc,(GEN)MC[l]));
	  U[kk]=(long)gsub((GEN)U[kk],gmul(xpol,(GEN)U[l]));
	  coeff(mu,kk,l)=lsub(gcoeff(mu,kk,l),xc);
	  for (i=1; i<l; i++)
	    coeff(mu,kk,i) = lsub(gcoeff(mu,kk,i), rnfmul(xc,gcoeff(mu,l,i)));
	}
      }
      kk++; if (DEBUGLEVEL) fprintferr("%ld ",kk);
    }
  }
  while (kk<lx);
  if (DEBUGLEVEL) fprintferr("\n");
  p1=gmul(MPOL,U); tetpil=avma;
  y=cgetg(3,t_VEC); z=cgetg(3,t_VEC); y[1]=(long)z;
  z[2]=lcopy(I); z[1]=(long)algtobasis(nf,p1);
  y[2]=(long)algtobasis(nf,U);
  return gerepile(av,tetpil,y);
}

GEN
rnfpolred(GEN nf, GEN pol, long prec)
{
  gpmem_t av = avma;
  long i,j,k,n,N, vpol = varn(pol);
  GEN id,id2,newid,newor,p1,p2,al,newpol,w,z;
  GEN bnf,zk,newideals,ideals,order,neworder;

  if (typ(pol)!=t_POL) err(typeer,"rnfpolred");
  if (typ(nf)!=t_VEC) err(idealer1);
  switch(lg(nf))
  {
    case 10: bnf = NULL; break;
    case 11: bnf = nf; nf = checknf((GEN)nf[7]); break;
    default: err(idealer1);
      return NULL; /* not reached */
  }
  if (degpol(pol) <= 1)
  {
    w=cgetg(2,t_VEC);
    w[1]=lpolx[vpol]; return w;
  }
  id=rnfpseudobasis(nf,pol); N=degpol(nf[1]);
  if (bnf && gcmp1(gmael3(bnf,8,1,1))) /* if bnf is principal */
  {
    ideals=(GEN)id[2]; n=lg(ideals)-1; order=(GEN)id[1];
    newideals=cgetg(n+1,t_VEC); neworder=cgetg(n+1,t_MAT);
    zk=idmat(N);
    for (j=1; j<=n; j++)
    {
      newideals[j]=(long)zk; p1=cgetg(n+1,t_COL); neworder[j]=(long)p1;
      p2=(GEN)order[j];
      al=(GEN)isprincipalgen(bnf,(GEN)ideals[j])[2];
      for (k=1; k<=n; k++)
	p1[k]=(long)element_mul(nf,(GEN)p2[k],al);
    }
    id=cgetg(3,t_VEC); id[1]=(long)neworder; id[2]=(long)newideals;
  }
  id2=rnflllgram(nf,pol,id,prec);
  z=(GEN)id2[1]; newid=(GEN)z[2]; newor=(GEN)z[1];
  n=lg(newor)-1; w=cgetg(n+1,t_VEC);
  for (j=1; j<=n; j++)
  {
    p1=(GEN)newid[j]; al=gmul(gcoeff(p1,1,1),(GEN)newor[j]);
    p1=basistoalg(nf,(GEN)al[n]);
    for (i=n-1; i; i--)
      p1=gadd(basistoalg(nf,(GEN)al[i]),gmul(polx[vpol],p1));
    newpol=gtopoly(gmodulcp(gtovec(caract2(lift(pol),lift(p1),vpol)),
                            (GEN) nf[1]), vpol);
    p1 = ggcd(newpol, derivpol(newpol));
    if (degpol(p1)>0)
    {
      newpol=gdiv(newpol,p1);
      newpol=gdiv(newpol,leading_term(newpol));
    }
    w[j]=(long)newpol;
    if (DEBUGLEVEL>=4) outerr(newpol);
  }
  return gerepilecopy(av,w);
}

/* given a relative polynomial pol over nf, compute a pseudo-basis for the
 * extension, then an absolute basis */
static GEN
makebasis(GEN nf, GEN pol, GEN rnfeq)
{
  GEN elts,ids,polabs,plg,B,bs,p1,den,vbs,vbspro,vpro;
  gpmem_t av = avma;
  long n,N,m,i,j, v = varn(pol);

  polabs= (GEN)rnfeq[1];
  plg   = (GEN)rnfeq[2];
  p1 = rnfpseudobasis(nf,pol);
  elts= (GEN)p1[1];
  ids = (GEN)p1[2];
  if (DEBUGLEVEL>1) fprintferr("relative basis computed\n");
  N = degpol(pol);
  n = degpol(nf[1]); m = n*N;
  den = denom(content(lift(plg)));
  vbs = cgetg(n+1,t_VEC);
  vbs[1] = un;
  vbs[2] = (long)plg; vbspro = gmul(den,plg);
  for(i=3;i<=n;i++)
    vbs[i] = ldiv(gmul((GEN)vbs[i-1],vbspro),den);
  bs = gmul(vbs, vecpol_to_mat((GEN)nf[7],n));

  vpro = cgetg(N+1,t_VEC);
  for (i=1;i<=N;i++) vpro[i] = (long)to_polmod(gpowgs(polx[v],i-1), polabs);
  vpro = gmul(vpro,elts); B = cgetg(m+1, t_MAT);
  for(i=1;i<=N;i++)
    for(j=1;j<=n;j++)
    {
      p1 = gmul(bs, element_mul(nf,(GEN)vpro[i],gmael(ids,i,j)));
      B[(i-1)*n+j] = (long)pol_to_vec(lift_intern(p1), m);
    }
  p1 = denom(B); B = gmul(B,p1);
  B = hnfmodid(B, p1); B = gdiv(B,p1);
  p1 = cgetg(3,t_VEC);
  p1[1] = (long)polabs;
  p1[2] = (long)B; return gerepilecopy(av, p1);
}

/* relative polredabs. Returns
 * flag = 0: relative polynomial
 * flag = 1: relative polynomial + element
 * flag = 2: absolute polynomial */
GEN
rnfpolredabs(GEN nf, GEN relpol, long flag, long prec)
{
  GEN eq,p1,bpol,elt,pol,T,a;
  long v;
  gpmem_t av = avma;

  if (typ(relpol)!=t_POL) err(typeer,"rnfpolredabs");
  nf = checknf(nf); v = varn(relpol);
  if (DEBUGLEVEL>1) timer2();
  relpol = unifpol(nf,relpol,1);
  eq = rnfequation2(nf,relpol);
  a = (GEN)eq[3];
  T = (GEN)nf[1];
  if (signe(a))
    relpol = poleval(relpol, gsub(polx[v],
                             gmul(a, gmodulcp(polx[varn(T)],T))));
  p1 = makebasis(nf, relpol, eq);
  if (DEBUGLEVEL>1)
  {
    msgtimer("absolute basis");
    fprintferr("original absolute generator: %Z\n",p1[1]);
  }
  p1 = polredabs0(p1, nf_RAW | nf_NORED, prec);
  bpol = (GEN)p1[1];
  if (DEBUGLEVEL>1) fprintferr("reduced absolute generator: %Z\n",bpol);
  if (flag==2) return gerepileupto(av,bpol);

  elt = eltabstorel((GEN)p1[2], T, relpol, a);

  p1 = cgetg(3,t_VEC);
  pol = rnfcharpoly(nf,relpol,elt,v);
  if (!flag) p1 = pol;
  else
  {
    p1[1] = (long)pol;
    p1[2] = (long)polymodrecip(elt);
  }
  return gerepileupto(av,p1);
}
