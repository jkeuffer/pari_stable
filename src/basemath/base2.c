/*******************************************************************/
/*                                                                 */
/*                       MAXIMAL ORDERS                            */
/*                                                                 */
/*******************************************************************/
/* $Id$ */
#include "pari.h"

GEN caractducos(GEN p, GEN x, int v);
GEN element_muli(GEN nf, GEN x, GEN y);
GEN element_mulid(GEN nf, GEN x, long i);
GEN eleval(GEN f,GEN h,GEN a);
GEN ideal_better_basis(GEN nf, GEN x, GEN M);
long int_elt_val(GEN nf, GEN x, GEN p, GEN bp, long v);
GEN mat_to_vecpol(GEN x, long v);
GEN nfidealdet1(GEN nf, GEN a, GEN b);
GEN nfsuppl(GEN nf, GEN x, long n, GEN prhall);
GEN pol_to_monic(GEN pol, GEN *lead);
GEN pol_to_vec(GEN x, long N);
GEN quicktrace(GEN x, GEN sym);
GEN respm(GEN f1,GEN f2,GEN pm);

static void
allbase_check_args(GEN f, long code, GEN *y, GEN *ptw1, GEN *ptw2)
{
  GEN w,w1,w2,q;
  long i,h;

  if (typ(f)!=t_POL) err(notpoler,"allbase");
  if (lgef(f)<=3) err(constpoler,"allbase");
  *y=discsr(f);
  if (!signe(*y)) err(talker,"reducible polynomial in allbase");
  if (DEBUGLEVEL) timer2();
  switch(code)
  {
    case 0: case 1:
      w=auxdecomp(absi(*y),1-code);
      w1=(GEN)w[1]; w2=(GEN)w[2]; break;
    default: w=(GEN)code;
      if (typ(w)!=t_MAT || lg(w)!=3)
        err(talker,"not a n x 2 matrix as factorization in factoredbase");
      w1=(GEN)w[1]; w2=(GEN)w[2]; h=lg(w1); q=gun;
      for (i=1; i<h; i++)
	q=gmul(q,powgi((GEN)w1[i], (GEN)w2[i]));
      if (gcmp(absi(q), absi(*y)))
        err(talker,"incorrect factorization in factoredbase");
  }
  if (DEBUGLEVEL) msgtimer("disc. factorisation");
  *ptw1=w1; *ptw2=w2;
}

/*******************************************************************/
/*                                                                 */
/*                            ROUND 2                              */
/*                                                                 */
/*******************************************************************/
/*  Normalized quotient and remainder ( -1/2 |y| < r = x-q*y <= 1/2 |y| ) */
static GEN
rquot(GEN x, GEN y)
{
  long av=avma,av1;
  GEN u,v,w,p;

  u=absi(y); v=shifti(x,1); w=shifti(y,1);
  if (cmpii(u,v)>0) p=subii(v,u);
  else p=addsi(-1,addii(u,v));
  av1=avma; return gerepile(av,av1,divii(p,w));
}

/* space needed lx + 2*ly */
static GEN
rrmdr(GEN x, GEN y)
{
  long av=avma,tetpil,k;
  GEN r,ys2;

  if (!signe(x)) return gzero;
  r = resii(x,y); tetpil = avma;
  ys2 = shifti(y,-1);
  k = absi_cmp(r, ys2);
  if (k>0 || (k==0 && signe(r)>0))
  {
    avma = tetpil;
    if (signe(y) == signe(r)) r = subii(r,y); else r = addii(r,y);
    return gerepile(av,tetpil,r);
  }
  avma = tetpil; return r;
}

/* companion matrix of unitary polynomial x */
static GEN
companion(GEN x) /* cf assmat */
{
  long i,j,l;
  GEN y;

  l=lgef(x)-2; y=cgetg(l,t_MAT);
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
  long n = lg(x),i,j,k,av;
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
powmati(GEN x, long m)
{
  long av=avma,j;
  GEN y = x;

  j=1+bfffo(m); m<<=j; j = BITS_IN_LONG-j;
  for (; j; m<<=1,j--)
  {
    y=mulmati(y,y);
    if (m<0) y=mulmati(y,x);
  }
  return gerepileupto(av,y);
}

static GEN
rtran(GEN v, GEN w, GEN q)
{
  long av,tetpil;
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
mtran(GEN v, GEN w, GEN q, GEN m, long k0)
{
  long k,l;
  GEN p1;

  if (signe(q))
  {
    l = lgefint(m) << 2;
    for (k=lg(v)-1; k>= k0; k--)
    {
      long av = avma; (void)new_chunk(l);
      p1 = subii((GEN)v[k], mulii(q,(GEN)w[k]));
      avma = av; v[k]=(long)rrmdr(p1, m);
    }
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
  long av=avma, lim=stack_lim(av,1);
  GEN q;

  for (j=1; j<r; j++)
  {
    for (k=j+1; k<c; k++)
      while (signe(gcoeff(a,j,k)))
      {
	q=rquot(gcoeff(a,j,j),gcoeff(a,j,k));
	pro=(long)mtran((GEN)a[j],(GEN)a[k],q,rmod, j);
	a[j]=a[k]; a[k]=pro;
      }
    if (signe(gcoeff(a,j,j)) < 0)
      for (k=j; k<r; k++) coeff(a,k,j)=lnegi(gcoeff(a,k,j));
    for (k=1; k<j; k++)
    {
      q=rquot(gcoeff(a,j,k),gcoeff(a,j,j));
      a[k]=(long)mtran((GEN)a[k],(GEN)a[j],q,rmod, k);
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      long j1,k1, tetpil = avma;
      GEN p1 = a;
      if(DEBUGMEM>1) err(warnmem,"rowred j=%ld", j);
      p1 = gerepile(av,tetpil,gcopy(a));
      for (j1=1; j1<r; j1++)
        for (k1=1; k1<c; k1++) coeff(a,j1,k1) = coeff(p1,j1,k1);
    }
  }
}

/* Calcule d/x  ou  d est entier et x matrice triangulaire inferieure
 * entiere dont les coeff diagonaux divisent d (resultat entier).
 */
static GEN
matinv(GEN x, GEN d, long n)
{
  long i,j,k,av,av1;
  GEN y,h;

  y=idmat(n);
  for (i=1; i<=n; i++)
    coeff(y,i,i)=ldivii(d,gcoeff(x,i,i));
  av=avma;
  for (i=2; i<=n; i++)
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
  long sp,hard_case_exponent,i,n=lg(cf)-1,av=avma, av2,limit;
  GEN T,T2,Tn,m,v,delta, *w;
  const GEN pp = sqri(p);
  const long pps = (2*expi(pp)+2<BITS_IN_LONG)? pp[2]: 0;

  if (cmpis(p,n) > 0) hard_case_exponent = 0;
  else
  {
    long k;
    k = sp = itos(p);
    i=1; while (k < n) { k *= sp; i++; }
    hard_case_exponent = i;
  }
  T=cgetg(n+1,t_MAT); for (i=1; i<=n; i++) T[i]=lgetg(n+1,t_COL);
  T2=cgetg(2*n+1,t_MAT); for (i=1; i<=2*n; i++) T2[i]=lgetg(n+1,t_COL);
  Tn=cgetg(n*n+1,t_MAT); for (i=1; i<=n*n; i++) Tn[i]=lgetg(n+1,t_COL);
  v = new_chunk(n+1);
  w =  (GEN*)new_chunk(n+1);

  av2 = avma; limit = stack_lim(av2,1);
  delta=gun; m=idmat(n);

  for(;;)
  {
    long j,k,h, av0 = avma;
    GEN t,b,jp,hh,index,p1, dd = sqri(delta), ppdd = mulii(dd,pp);

    if (DEBUGLEVEL > 3)
      fprintferr("ROUND2: epsilon = %ld\tavma = %ld\n",epsilon,avma);

    b=matinv(m,delta,n);
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
          coeff(T,j,k) = (long)rrmdr(p1, ppdd);
        }
      p1 = mulmati(m, mulmati(T,b));
      for (j=1; j<=n; j++)
	for (k=1; k<=n; k++)
	  coeff(p1,j,k)=(long)rrmdr(divii(gcoeff(p1,j,k),dd),pp);
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
          long av1 = avma;
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
    jp=matinv(T2,p,n);
    if (pps)
    {
      for (k=1; k<=n; k++)
      {
        long av1=avma;
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

    m = mulmati(matinv(Tn,index,n), m);
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

#if 0
static void
to_col(GEN x, GEN col)
{
  long i,n = lg(col), k = lgef(x)-1;
  x++;
  for (i=1; i<k; i++) col[i] = x[i];
  for (   ; i<n; i++) col[i] = zero;
}

static GEN
ordmax2(GEN f, GEN p, long epsilon, GEN *ptdelta)
{
  long sp,i,n=lgef(f)-3,av=avma, av2,limit;
  GEN col,sym,hard_case_exponent,T2,Tn,m,v,delta,w,a;
  const GEN pp = sqri(p);

  if (cmpis(p,n) > 0)
  {
    hard_case_exponent = NULL;
    sym = polsym(f,n-1);
  }
  else
  {
    long k; k = sp = itos(p);
    while (k < n) k *= sp;
    hard_case_exponent = stoi(k);
  }
  col = cgetg(n+1,t_COL);
  T2=cgetg(2*n+1,t_MAT); for (i=1; i<=2*n; i++) T2[i]=lgetg(n+1,t_COL);
  Tn=cgetg(n*n+1,t_MAT); for (i=1; i<=n*n; i++) Tn[i]=lgetg(n+1,t_COL);
  v = new_chunk(n+1);

  av2 = avma; limit = stack_lim(av2,1);
  delta=gun; m=idmat(n);

  for(;;)
  {
    long j,k,h, av0 = avma;
    GEN hh,index,p1;

    if (DEBUGLEVEL > 3)
      fprintferr("ROUND2: epsilon = %ld\tavma = %ld\n",epsilon,avma);

    w = mat_to_vecpol(m, 0);
    if (hard_case_exponent)
    {
      for (i=1; i<=n; i++)
      {
        p1 = Fp_pow_mod_pol((GEN)w[i], hard_case_exponent, f,p);
        to_col(p1, (GEN)T2[i]);
      }
      for (i=1; i<=n; i++) /* transpose */
        for (j=1; j<i; j++)
        {
          p1 = gcoeff(T2,i,j);
          coeff(T2,i,j) = coeff(T2,j,i);
          coeff(T2,j,i)= (long)p1;
        }
    }
    else
    {
      for (i=1; i<=n; i++)
      {
	for (j=1; j<i; j++)
	{
          p1 = Fp_res(gmul((GEN)w[i], (GEN)w[j]), f, p);
	  coeff(T2,j,i) = coeff(T2,i,j) = lresii(quicktrace(p1,sym), p);
	}
        p1 = Fp_res(gsqr((GEN)w[i]), f, p);
        coeff(T2,i,i) = lresii(quicktrace(p1,sym), p);
      }
    }
    for (i=1; i<=n; i++)
      for (j=1; j<=n; j++)
	coeff(T2,j,n+i)=(i==j)? (long)p : zero;
    rowred(T2,pp);
    a = mat_to_vecpol(matinv(T2,p,n), 0);
    if (2*expi(pp)+2<BITS_IN_LONG)
    {
      for (k=1; k<=n; k++)
      {
        long av1=avma;
        for (h=i=1; i<=n; i++)
        {
          p1 = gres(gmul((GEN)a[i], (GEN)w[k]), f);
          to_col(p1, col);
          for (j=1; j<=n; j++)
            { coeff(Tn,k,h)=itos(divii((GEN)col[j],p)); h++; }
        }
        avma=av1;
      }
      avma = av0;
      rowred_long(Tn,pp[2]);
    }
    else
    {
      for (k=1; k<=n; k++)
      {
        for (h=i=1; i<=n; i++)
        {
          p1 = gres(gmul((GEN)a[i], (GEN)w[k]), f);
          to_col(p1, col);
          for (j=1; j<=n; j++)
  #if 0
            { coeff(Tn,k,h)=ldivii((GEN)col[j],p); h++; }
  #endif
            { coeff(Tn,k,h)=col[j]; h++; }
        }
      }
      rowred(Tn,pp);
    }
    for (index=gun,i=1; i<=n; i++)
      index = mulii(index,gcoeff(Tn,i,i));
    if (gcmp1(index)) break;

    m = mulmati(matinv(Tn,index,n), m);
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
#endif

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
  long av=avma,tetpil,n,h,j,i,k,r,s,t,v,mf;

  allbase_check_args(f,code,y, &w1,&w2);
  v = varn(f); n = lgef(f)-3; h = lg(w1)-1;
  cf = (GEN*)cgetg(n+1,t_VEC);
  cf[2]=companion(f);
  for (i=3; i<=n; i++) cf[i]=mulmati(cf[2],cf[i-1]);

  a=idmat(n); da=gun;
  for (i=1; i<=h; i++)
  {
    long av1 = avma;
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
          q=rquot(gcoeff(at,s,s),gcoeff(bt,s,r));
          pro=rtran((GEN)at[s],(GEN)bt[r],q);
          for (t=s-1; t; t--)
          {
            q=rquot(gcoeff(at,t,s),gcoeff(at,t,t));
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
          q=rquot(gcoeff(at,j,j),gcoeff(at,j,k));
          pro=rtran((GEN)at[j],(GEN)at[k],q);
          at[j]=at[k]; at[k]=(long)pro;
        }
      }
      if (signe(gcoeff(at,j,j))<0)
        for (k=1; k<=j; k++) coeff(at,k,j)=lnegi(gcoeff(at,k,j));
      for (k=j+1; k<=n; k++)
      {
        q=rquot(gcoeff(at,j,k),gcoeff(at,j,j));
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
  long av=avma,tetpil;

  allbase(x,0,&y); tetpil=avma;
  return gerepile(av,tetpil,icopy(y));
}

/*******************************************************************/
/*                                                                 */
/*                            ROUND 4                              */
/*                                                                 */
/*******************************************************************/

static GEN Decomp(GEN p,GEN f,long mf,GEN theta,GEN chi,GEN nu);
static GEN dbasis(GEN p, GEN f, long mf, GEN alpha, GEN U);
static GEN eltppm(GEN f,GEN pd,GEN theta,GEN k);
static GEN maxord(GEN p,GEN f,long mf);
static GEN nbasis(GEN ibas,GEN pd);
#if 0
static GEN nilord(GEN p,GEN fx,long mf,GEN gx);
#endif
static GEN nilord2(GEN p,GEN fx,long mf,GEN gx);
static GEN testd(GEN p,GEN fa,long c,long Da,GEN alph2,long Ma,GEN theta);
static GEN testb(GEN p,GEN fa,long Da,GEN theta,long Dt);
static GEN testb2(GEN p,GEN fa,long Fa,GEN theta,long Ft);
static GEN testc2(GEN p,GEN fa,GEN pmr,GEN alph2,long Ea,GEN thet2,long Et);

static long clcm(long a,long b);

static int
fnz(GEN x,long j)
{
  long i=1; while (!signe(x[i])) i++;
  return i==j;
}

/* retourne la base, dans y le discf et dans ptw la factorisation (peut
 etre partielle) de discf */
GEN
allbase4(GEN f,long code, GEN *y, GEN *ptw)
{
  GEN w,w1,w2,a,da,b,db,bas,q,p1,*gptr[3];
  long v,n,mf,h,lfa,i,j,k,l,first,tetpil,av = avma;

  allbase_check_args(f,code,y, &w1,&w2);
  first=1; v = varn(f); n = lgef(f)-3; h = lg(w1)-1;
  for (i=1; i<=h; i++)
  {
    mf=itos((GEN)w2[i]); if (mf == 1) continue;
    if (DEBUGLEVEL) fprintferr("Treating p^k = %Z^%ld\n",w1[i],mf);

    b = maxord((GEN)w1[i],f,mf);
    p1=cgetg(n+1,t_VEC); for (j=1; j<=n; j++) p1[j]=coeff(b,j,j);
    db=denom(p1);
    if (! gcmp1(db))
    {
      if (first==1) { da=db; a=gmul(b,db); first=0; }
      else
      {
        da=mulii(da,db); b=gmul(da,b); a=gmul(db,a);
        j=1; while (j<=n && fnz((GEN)a[j],j) && fnz((GEN)b[j],j)) j++;
        k=j-1; p1=cgetg(2*n-k+1,t_MAT);
        for (j=1; j<=k; j++)
        {
          p1[j]=a[j];
          coeff(p1,j,j) = lmppgcd(gcoeff(a,j,j),gcoeff(b,j,j));
        }
        for (  ; j<=n; j++) p1[j]=a[j];
        for (  ; j<=2*n-k; j++) p1[j]=b[j+k-n];
        a=hnfmod(p1,detint(p1));
      }
    }
    if (DEBUGLEVEL>5)
      fprintferr("Result for prime %Z is:\n%Z\n",w1[i],b);
  }
  if (!first)
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
  if (ptw)
  {
    lfa=0;
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
    if (!first)
      for (j=1; j<=k; j++) q[j+1]=ldiv(gcoeff(a,j,k),da);
    else
    {
      for (j=2; j<=k; j++) q[j]=zero;
      q[j]=un;
    }
  }
  if (ptw)
  {
    *ptw=w=cgetg(3,t_MAT); w[1]=lgetg(lfa+1,t_COL); w[2]=lgetg(lfa+1,t_COL);
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

/* if y is non-NULL, it receives the discriminant
 * return basis if (ret_basis != 0), discriminant otherwise
 */
static GEN
nfbasis00(GEN x, long flag, GEN p, long ret_basis, GEN *y)
{
  GEN disc, basis, lead;
  GEN *gptr[2];
  long k, tetpil, av = avma, n = lgef(x)-3, smll;

  if (typ(x)!=t_POL) err(typeer,"nfbasis00");
  if (n<=0) err(zeropoler,"nfbasis00");
  for (k=n+2; k>=2; k--)
    if (typ(x[k])!=t_INT) err(talker,"polynomial not in Z[X] in nfbasis");

  x = pol_to_monic(x,&lead);

  if (!p || gcmp0(p))
    smll = (flag & 1); /* small basis */
  else
    smll = (long) p;   /* factored basis */

  if (flag & 2)
    basis = allbase(x,smll,&disc); /* round 2 */
  else
    basis = allbase4(x,smll,&disc,NULL); /* round 4 */

  tetpil=avma;
  if (!ret_basis)
    return gerepile(av,tetpil,gcopy(disc));

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
  long av=avma,tetpil;

  allbase4(x,0,&y,NULL); tetpil=avma;
  return gerepile(av,tetpil,icopy(y));
}

GEN
smalldiscf(GEN x)
{
  GEN y;
  long av=avma,tetpil;

  allbase4(x,1,&y,NULL); tetpil=avma;
  return gerepile(av,tetpil,icopy(y));
}

GEN
factoreddiscf(GEN x, GEN p)
{
  GEN y;
  long av=avma,tetpil;

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
  h = Fp_deuc(f,g,p);
  k = gdiv(gadd(f, gneg_i(gmul(g,h))), p);
  k = Fp_pol_gcd(k, Fp_pol_gcd(g,h, p), p);

  dk = lgef(k)-3;
  if (DEBUGLEVEL>=3) fprintferr("  gcd has degree %ld\n", dk);
  if (2*dk >= mf-1) return Fp_deuc(f,k,p);
  return dk? (GEN)NULL: f;
}

/* p-maximal order of Af; mf = v_p(Disc(f)) */
static GEN
maxord(GEN p,GEN f,long mf)
{
  long j,r, av = avma, flw = (cmpsi(lgef(f)-3,p) < 0);
  GEN w,g,h,res;

  if (flw)
    g = Fp_deuc(f, Fp_pol_gcd(f,derivpol(f), p), p);
  else
  {
    w=(GEN)factmod(f,p)[1]; r=lg(w)-1;
    g = h = lift_intern((GEN)w[r]); /* largest factor */
    for (j=1; j<r; j++) g = Fp_pol_red(gmul(g, lift_intern((GEN)w[j])), p);
  }
  res = dedek(f,mf,p,g);
  if (res)
    res = dbasis(p,f,mf,polx[varn(f)],res);
  else
  {
    if (flw) { w=(GEN)factmod(f,p)[1]; r=lg(w)-1; h=lift_intern((GEN)w[r]); }
#if 0
    res = (r==1)? nilord(p,f,mf,h): Decomp(p,f,mf,polx[varn(f)],f,h);
#else
    res = (r==1)? nilord2(p,f,mf,h): Decomp(p,f,mf,polx[varn(f)],f,h);
#endif
  }
  return gerepileupto(av,res);
}

/* do a centermod on integer or rational number */
static GEN
polmodiaux(GEN x, GEN y, GEN ys2)
{
  if (typ(x)!=t_INT)
    x = mulii((GEN)x[1], mpinvmod((GEN)x[2],y));
  x = modii(x,y); 
  if (cmpii(x,ys2) > 0) x = subii(x,y);
  return x;
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
  long n=lgef(f)-3,dU,c,i,dh;
  GEN b,p1,ha,pd,pdp;

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
  ha = pd = gpuigs(p,mf/2); pdp = mulii(pd,p);
  dU = lgef(U)-3;
  b = cgetg(n,t_MAT); /* Z[a] + U/p Z[a] is maximal */
  /* skip first column = gscalcol(pd,n) */
  for (c=1; c<n; c++)
  {
    p1=cgetg(n+1,t_COL); b[c]=(long)p1;
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
      ha = Fp_res(ha, f, mod);
      if (p2) ha = gmul(ha,p2);
    }
    dh = lgef(ha)-2;
    for (i=1; i<=dh; i++) p1[i]=ha[i+1];
    for (   ; i<=n;  i++) p1[i]=zero;
  }
  b = hnfmodid(b,pd);
  if (DEBUGLEVEL>5) fprintferr("  new order: %Z\n",b);
  return gdiv(b,pd);
}

static GEN
get_partial_order_as_pols(GEN p, GEN f)
{
  long i,j,n=lgef(f)-3, vf = varn(f);
  GEN b,ib,h,col;

  b = maxord(p,f, ggval(discsr(f),p));
  ib = cgetg(n+1,t_VEC);
  for (i=1; i<=n; i++)
  {
    h=cgetg(i+2,t_POL); ib[i]=(long)h; col=(GEN)b[i];
    h[1]=evalsigne(1)|evallgef(i+2)|evalvarn(vf);
    for (j=1;j<=i;j++) h[j+1]=col[j];
  }
  return ib;
}

static GEN
Decomp(GEN p,GEN f,long mf,GEN theta,GEN chi,GEN nu)
{
  GEN pk,ph,pdr,pmr,unmodp;
  GEN b1,b2,b3,a1,e,f1,f2,ib1,ib2,ibas;
  long n1,n2,j;

  if (DEBUGLEVEL>=3)
  {
    fprintferr("  entering Decomp ");
    if (DEBUGLEVEL>5)
    {
      fprintferr("with parameters: p=%Z, expo=%ld\n",p,mf);
      fprintferr("  f=%Z",f);
    }
    fprintferr("\n");
  }
  pdr=respm(f,derivpol(f),gpuigs(p,mf));

  unmodp=gmodulsg(1,p);
  b1=lift_intern(gmul(chi,unmodp));
  a1=gun; b2=gun;
  b3=lift_intern(gmul(nu,unmodp));
  while (lgef(b3) > 3)
  {
    GEN p1;
    b1 = Fp_deuc(b1,b3, p);
    b2 = Fp_pol_red(gmul(b2,b3), p);
    b3 = Fp_pol_extgcd(b2,b1, p, &a1,&p1); /* p1 = junk */
    p1 = leading_term(b3);
    if (!gcmp1(p1))
    { /* Fp_pol_extgcd does not return normalized gcd */
      p1 = mpinvmod(p1,p);
      b3 = gmul(b3,p1);
      a1 = gmul(a1,p1);
    }
  }
  e=eleval(f,Fp_pol_red(gmul(a1,b2), p),theta);
  e=gdiv(polmodi(gmul(pdr,e), mulii(pdr,p)),pdr);

  pk=p; pmr=mulii(p,sqri(pdr)); ph=mulii(pdr,pmr);
  /* E(t)- e(t) belongs to p^k Op, which is contained in p^(k-df)*Zp[xi] */
  while (cmpii(pk,ph) < 0)
  {
    e = gmul(gsqr(e), gsubsg(3,gmul2n(e,1)));
    e = gres(e,f); pk = sqri(pk);
    e=gdiv(polmodi(gmul(pdr,e), mulii(pk,pdr)), pdr);
  }
  f1 = gcdpm(f,gmul(pdr,gsubsg(1,e)), ph);
  f1 = Fp_res(f1,f, pmr);
  f2 = Fp_res(Fp_deuc(f,f1, pmr), f, pmr);
  f1 = polmodi(f1,pmr);
  f2 = polmodi(f2,pmr);

  if (DEBUGLEVEL>=3)
  {
    fprintferr("  leaving Decomp");
    if (DEBUGLEVEL>5)
      fprintferr(" with parameters: f1 = %Z\nf2 = %Z\ne = %Z\n", f1,f2,e);
    fprintferr("\n");
  }
  ib1 = get_partial_order_as_pols(p,f1); n1=lg(ib1)-1;
  ib2 = get_partial_order_as_pols(p,f2); n2=lg(ib2)-1;
  ibas=cgetg(n1+n2+1,t_VEC);

  for (j=1; j<=n1; j++)
    ibas[j]=(long)polmodi(gmod(gmul(gmul(pdr,(GEN)ib1[j]),e),f), pdr);
  e=gsubsg(1,e);
  for (   ; j<=n1+n2; j++)
    ibas[j]=(long)polmodi(gmod(gmul(gmul(pdr,(GEN)ib2[j-n1]),e),f), pdr);
  return nbasis(ibas,pdr);
}

/* minimum extension valuation: res[0]/res[1] (both are longs) */
long *
vstar(GEN p,GEN h)
{
  static long res[2];
  long m,first,j,k,v,w;

  m=lgef(h)-3; first=1; k=1; v=0;
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

/* Returns [theta,chi,nu] with theta non-primary */
static GEN
csrch(GEN p,GEN fa,GEN gamma)
{
  GEN b,h,theta,w;
  long pp,t,v=varn(fa);

  pp = p[2]; if (lgef(p)>3 || pp<0) pp=0;
  for (t=1; ; t++)
  {
    h = pp? stopoly(t,pp,v): scalarpol(stoi(t),v);
    theta = gadd(gamma,gmod(h,fa));
    w=factcp(p,fa,theta); h=(GEN)w[3];
    if (h[2] > 1)
    {
      b=cgetg(5,t_VEC); b[1]=un; b[2]=(long)theta;
      b[3]=w[1]; b[4]=w[2]; return b;
    }
  }
}

/* Returns
 *  [1,theta,chi,nu] if theta non-primary
 *  [2,phi, * , * ]  if D_phi > D_alpha or M_phi > M_alpha
 */
GEN
bsrch(GEN p,GEN fa,long ka,GEN eta,long Ma)
{
  long n=lgef(fa)-3,Da=lgef(eta)-3;
  long c,r,j,MaVb,av=avma;
  GEN famod,pc,pcc,beta,gamma,delta,pik,w,h;

  pc=respm(fa,derivpol(fa),gpuigs(p,ka));
  c=ggval(pc,p); pcc=sqri(pc);
  famod=polmodi_keep(fa,pcc);

  r=1+(long)ceil(c/(double)(Da)+gtodouble(gdivsg(c*n-2,mulsi(Da,subis(p,1)))));

  beta=gdiv(lift_intern(gpuigs(gmodulcp(eta,famod),Ma)),p);

  for(;;)
  { /* Compute modulo pc. denom(pik, delta)=1. denom(beta, gamma) | pc */
    beta=gdiv(polmodi(gmul(pc,beta),pcc), pc);
    w=testd(p,fa,c,Da,eta,Ma,beta);
    h=(GEN)w[1]; if (h[2] < 3) return gerepileupto(av,w);

    w = vstar(p,(GEN)w[3]);
    MaVb = (w[0]*Ma) / w[1];
    pik=eltppm(famod,pc,eta,stoi(MaVb));

    gamma=gmod(gmul(beta,(GEN)(vecbezout(pik,famod))[1]),famod);
    gamma=gdiv(polmodi(gmul(pc,gamma),pcc),pc);
    w=testd(p,fa,c,Da,eta,Ma,gamma);
    h=(GEN)w[1]; if (h[2] < 3) return gerepileupto(av,w);

    delta=eltppm(famod,pc,gamma,gpuigs(p,r*Da));
    delta=gdiv(polmodi(gmul(pc,delta),pcc),pc);
    w=testd(p,fa,c,Da,eta,Ma,delta);
    h=(GEN)w[1]; if (h[2] < 3) return gerepileupto(av,w);

    for (j=lgef(delta)-1; j>1; j--)
      if (typ(delta[j]) != t_INT)
      {
        w = csrch(p,fa,gamma);
        return gerepileupto(av,gcopy(w));
      }
    beta=gsub(beta,gmod(gmul(pik,delta),famod));
  }
}

static GEN 
mycaract(GEN f, GEN beta)
{
  GEN chi,p1;
  long v = varn(f);

  if (gcmp0(beta)) return zeropol(v);
  p1 = content(beta);
  if (gcmp1(p1)) p1 = NULL; else beta = gdiv(beta,p1);
  chi = caractducos(f,beta,v);
  if (p1)
  {
    chi=poleval(chi,gdiv(polx[v],p1));
    p1=gpuigs(p1,lgef(f)-3); chi=gmul(chi,p1);
  }
  return chi;
}

/* USED TO Return [theta_1,theta_2,L_theta,M_theta] with theta non-primary */
/* Now return theta_2 */
GEN
setup(GEN p,GEN f,GEN theta,GEN nut, long *La, long *Ma)
{
  GEN t1,t2,v,dt,pv;
  long Lt,Mt,r,s,av=avma,tetpil,m,n,k;

  n=lgef(nut)-1; pv=p;
  for (m=1; ; m++) /* compute mod p^(2^m) */
  {
    t1=gzero; pv = sqri(pv);
    for (k=n; k>=2; k--)
    {
      t1 = gres(gadd(gmul(t1,theta),(GEN)nut[k]), f);
      dt = denom(content(t1));
      if (gcmp1(dt))
        t1 = polmodi(t1,pv);
      else
        t1 = gdiv(polmodi(gmul(t1,dt),mulii(dt,pv)),dt);
    }
    v = vstar(p, mycaract(f,t1));
    if (v[0] < (v[1]<<m)) break;
  }
  Lt=v[0]; Mt=v[1]; cbezout(Lt,-Mt,&r,&s);
  if (r<=0) { long q = (-r) / Mt; q++; r += q*Mt; s += q*Lt; }
  t2 = lift_intern(gpuigs(gmodulcp(t1,f),r));
  p = gpuigs(p,s); tetpil=avma; *La=Lt; *Ma=Mt;
  return gerepile(av,tetpil,gdiv(t2,p));
}

#define RED 1

#if 0
static GEN
nilord(GEN p,GEN fx,long mf,GEN gx)
{
  long La,Ma,first=1,v=varn(fx);
  GEN h,res,alpha,chi,nu,eta,w,phi,pmf,Dchi,pdr,pmr;

  if (DEBUGLEVEL>=3)
  {
    fprintferr("  entering Nilord");
    if (DEBUGLEVEL>5)
    {
      fprintferr(" with parameters: p=%Z, expo=%ld\n",p,mf);
      fprintferr("  fx=%Z, gx=%Z",fx,gx);
    }
    fprintferr("\n");
  }
  pmf=gpuigs(p,mf+1); alpha=polx[v];
  nu=gx; chi=fx; Dchi=gpuigs(p,mf);
#if RED
  pdr=respm(fx,derivpol(fx), Dchi);
  pmr=mulii(sqri(pdr),p); chi = dummycopy(chi);
#endif

  for(;;)
  {
#if RED
    chi = polmodi(chi, pmr);
#endif
    if (first) first=0;
    else
    {
      res=dedek(chi,mf,p,nu);
      if (res) return dbasis(p,fx,mf,alpha,res);
    }
    if (vstar(p,chi)[0] > 0)
    {
      alpha = gadd(alpha,gun);
      chi = poleval(chi, gsub(polx[v],gun));
#if RED
      chi = polmodi(chi, pmr);
#endif
      nu  = polmodi(poleval(nu, gsub(polx[v],gun)), p);
    }
    eta=setup(p,chi,polx[v],nu, &La,&Ma);
    if (La>1)
      alpha=gadd(alpha,eleval(fx,eta,alpha));
    else
    {
      w=bsrch(p,chi,ggval(Dchi,p),eta,Ma);
      phi=eleval(fx,(GEN)w[2],alpha);
      if (gcmp1((GEN)w[1]))
        return Decomp(p,fx,mf,phi,(GEN)w[3],(GEN)w[4]);
      alpha=gdiv(polmodi(gmul(pmf,phi), mulii(pmf,p)),pmf);
    }

    for (;;)
    {
      w=factcp(p,fx,alpha); chi=(GEN)w[1]; nu=(GEN)w[2]; h=(GEN)w[3];
      if (h[2] > 1) return Decomp(p,fx,mf,alpha,chi,nu);
#if 0
      Dchi = respm(chi,derivpol(chi), pmf);
#endif
      Dchi = modii(discsr(polmodi_keep(chi,pmf)), pmf);
      if (gcmp0(Dchi))
      {
        Dchi= discsr(chi);
        if (gcmp0(Dchi)) { alpha=gadd(alpha,gmul(p,polx[v])); continue; }
#if RED
        pmr = gpowgs(p, 2 * ggval(Dchi,p) + 1);
#endif
      }
      break;
    }
  }
}
#endif

/* reduce the element elt modulo rd, taking first of the denominators */
static GEN
redelt(GEN elt, GEN rd, GEN pd)
{
  GEN den, relt;

  den  = ggcd(denom(content(elt)), pd);
  relt = polmodi(gmul(den, elt), gmul(den, rd));
  return gdiv(relt, den);
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
    chin = mycaract(chip, nup);
  
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
  pip = lift_intern(gpuigs(gmodulcp(pip, chi), r));
  pp  = gpuigs(p, s); 

  *Lp = L; 
  *Ep = E;
  return gdiv(pip, pp);
}

static GEN
update_alpha(GEN p, GEN fx, GEN alph, GEN chi, GEN pmr, GEN pmf, long mf)
{
  long l, v = varn(fx);
  GEN nalph, nchi, w, nnu, pdr, npmr, rep;

  nalph = alph;
  if (!chi)
    nchi = mycaract(fx, alph);
  else
    nchi  = chi;

  pdr = modii(respm(nchi, derivpol(nchi), pmr), pmr);
  for (;;)
  {
    if (signe(pdr)) break;
    pdr = modii(respm(nchi, derivpol(nchi), pmf), pmf);
    if (signe(pdr)) break;
    if (DEBUGLEVEL >= 6)
      fprintferr("  non separable polynomial in update_alpha!\n");
    /* at this point, we assume that chi is not square-free */ 
    nalph = gadd(nalph, gmul(p, polx[v])); 
    w = factcp(p, fx, nalph); 
    nchi = (GEN)w[1]; 
    nnu  = (GEN)w[2]; 
    l    = itos((GEN)w[3]);
    if (l > 1) return Decomp(p, fx, mf, nalph, nchi, nnu);
    pdr = modii(respm(nchi, derivpol(nchi), pmr), pmr);
  }

  if (is_pm1(pdr))
    npmr = gun;
  else
  {
    npmr  = mulii(sqri(pdr), p);
    nchi  = polmodi(nchi, npmr);
    nalph = redelt(nalph, npmr, pmf);
  }

  rep = cgetg(5, t_VEC);
  rep[1] = (long)nalph;
  rep[2] = (long)nchi;
  rep[3] = (long)npmr;
  rep[4] = lmulii(p, pdr);

  return rep;
}

static GEN
nilord2(GEN p, GEN fx, long mf, GEN gx)
{
  long Fa, La, Ea, oE, Fg, eq, er, v = varn(fx), i, nv, Le, Ee, N, l, vn;
  GEN p1, alph, chi, nu, w, phi, pmf, pdr, pmr, kapp, pie, chib;
  GEN gamm, chig, nug, delt, beta, eta, chie, nue, pia, vb, opa;

  if (DEBUGLEVEL >= 3)
  {
    fprintferr("  entering Nilord2");
    if (DEBUGLEVEL >= 5)
    {
      fprintferr(" with parameters: p = %Z, expo = %ld\n", p, mf);
      fprintferr("  fx = %Z, gx = %Z", fx, gx);
    }
    fprintferr("\n");
  }

  /* this is quite arbitrary; what is important is that >= mf + 1 */
  pmf = gpuigs(p, mf + 3); 
  pdr = respm(fx, derivpol(fx), pmf);
  pmr = mulii(sqri(pdr), p);
  pdr = mulii(p, pdr);
  chi = polmodi_keep(fx, pmr);

  alph = polx[v];
  nu = gx; 
  N  = degree(fx);
  oE = 0;
  opa = NULL;

  for(;;)
  {
    /* kappa need to be recomputed */
    kapp = NULL;
    Fa   = degree(nu);
    /* the prime element in Zp[alpha] */
    pia  = getprime(p, chi, polx[v], chi, nu, &La, &Ea);
    pia  = redelt(pia, pmr, pmf);

    if (Ea < oE)
    {
      alph = gadd(alph, opa);
      w = update_alpha(p, fx, alph, NULL, pmr, pmf, mf);
      alph = (GEN)w[1];
      chi  = (GEN)w[2];
      pmr  = (GEN)w[3];
      pdr  = (GEN)w[4];
      kapp = NULL;
      pia  = getprime(p, chi, polx[v], chi, nu, &La, &Ea);
      pia  = redelt(pia, pmr, pmf);
    }
    
    oE = Ea; opa = pia;

    if (DEBUGLEVEL >= 5)
      fprintferr("  Fa = %ld and Ea = %ld \n", Fa, Ea);
   
    /* we change alpha such that nu = pia */
    if (La > 1)
    {
      alph = gadd(alph, eleval(fx, pia, alph));

      w = update_alpha(p, fx, alph, NULL, pmr, pmf, mf);
      alph = (GEN)w[1];
      chi  = (GEN)w[2];
      pmr  = (GEN)w[3];
      pdr  = (GEN)w[4];
    }
    
    /* if Ea*Fa == N then O = Zp[alpha] */
    if (Ea*Fa == N) 
    {
      alph = redelt(alph, sqri(p), pmf);
      return dbasis(p, fx, mf, alph, p);
    }

    /* during the process beta tends to a factor of chi */
    beta  = lift_intern(gpowgs(gmodulcp(nu, chi), Ea));

    for (;;)
    {
      if (DEBUGLEVEL >= 5)
	fprintferr("  beta = %Z\n", beta);

      p1 = gnorm(gmodulcp(beta, chi));
      if (signe(p1))
      {
	chib = NULL;
	vn = ggval(p1, p);
	eq = (long)(vn / N);
	er = (long)(vn*Ea/N - eq*Ea);
      }
      else  
      {
	chib = mycaract(chi, beta);
	vb = vstar(p, chib);
	eq = (long)(vb[0] / vb[1]);
	er = (long)(vb[0]*Ea / vb[1] - eq*Ea);
      }

      /* the following code can be used to check if beta approximates 
         a factor of chi well enough to derive a factorization of chi. 
	 However, in general, the process will always end before this 
         happens. */
#if 0
      {
	GEN quo, rem;

	 quo = poldivres(chi, beta, &rem);
	 p1 = content(lift(rem));
	 fprintferr(" val(rem) = %ld\n", ggval(p1, p));
	 p1 = respm(beta, quo, pmr);
	 fprintferr(" val(id)  = %ld\n", ggval(p1, p));
      }
#endif

      /* eq and er are such that gamma = beta.p^-eq.nu^-er is a unit */ 
      if (eq) gamm = gdiv(beta, gpowgs(p, eq));
      else gamm = beta;

      if (er)
      {
	/* kappa = nu^-1 in Zp[alpha] */
	if (!kapp)
	{
	  kapp = ginvmod(nu, chi);
	  kapp = redelt(kapp, pmr, pmr);
	  kapp = gmodulcp(kapp, chi);
	}
	gamm = lift(gmul(gamm, gpowgs(kapp, er)));
	gamm = redelt(gamm, p, pmr);
      }

      if (DEBUGLEVEL >= 6)
	fprintferr("  gamma = %Z\n", gamm);

      if (er || !chib)
      {
	p1   = mulii(pdr, ggcd(denom(content(gamm)), pdr));
	chig = mycaract(redelt(chi, mulii(pdr, p1), pdr), gamm); 
      }
      else
      {
	chig = poleval(chib, gmul(polx[v], gpowgs(p, eq)));
	chig = gdiv(chig, gpowgs(p, N*eq));
      }

      if (!gcmp1(denom(content(chig))))
      {
	/* the valuation of beta was wrong... This also means 
           that chi_gamma has more than one factor modulo p    */
	vb = vstar(p, chig);
	eq = (long)(-vb[0] / vb[1]);
	er = (long)(-vb[0]*Ea / vb[1] - eq*Ea);
	if (eq) gamm = gmul(gamm, gpowgs(p, eq));
	if (er) 
        {
	  gamm = gmul(gamm, gpowgs(nu, er));
	  gamm = gmod(gamm, chi);
	  gamm = redelt(gamm, p, pmr);
	}
	p1   = mulii(pdr, ggcd(denom(content(gamm)), pdr));
	chig = mycaract(redelt(chi, mulii(pdr, p1), pdr), gamm);
      }

      chig = polmodi(chig, pmr);
      nug  = (GEN)factmod(chig, p)[1];
      l    = lg(nug) - 1;
      nug  = lift((GEN)nug[l]);

      if (l > 1)
      {
	/* there are at least 2 factors mod. p => chi can be split */
	phi  = eleval(fx, gamm, alph);
	phi  = redelt(phi, p, pmf);
	return Decomp(p, fx, mf, phi, chig, nug);
      }

      Fg = degree(nug);
      if (Fa%Fg)
      {
	if (DEBUGLEVEL >= 5)
	  fprintferr("  Increasing Fa\n");
	/* we compute a new element such F = lcm(Fa, Fg) */
	w = testb2(p, chi, Fa, gamm, Fg);
	if (gcmp1((GEN)w[1]))
	{
	  /* there are at least 2 factors mod. p => chi can be split */
	  phi = eleval(fx, (GEN)w[2], alph);
	  phi = redelt(phi, p, pmf);
	  return Decomp(p, fx, mf, phi, (GEN)w[3], (GEN)w[4]);
	}
	break;
      }

      /* we look for a root delta of nug in Fp[alpha] such that
	 vp(gamma - delta) > 0. This root can then be used to
	 improved the approximation given by beta */
      nv = fetch_var();
      w = factmod9(nug, p, gsubst(nu, varn(nu), polx[nv]));
      w = lift(lift((GEN)w[1]));

      for (i = 1;; i++)
	if (degree((GEN)w[i]) == 1)
	{
	  delt = gneg_i(gsubst(gcoeff(w, 2, i), nv, polx[v]));
	  eta  = gsub(gamm, delt);	  
	  if (typ(delt) == t_INT)
	  {
	    chie = poleval(chig, gadd(polx[v], delt));
	    chie = polmodi(chie, pmr);
	    nue  = (GEN)factmod(chie, p)[1];
	    l    = lg(nue) - 1;
	    nue  = lift((GEN)nue[l]);
	  }
	  else
	  {
	    p1   = factcp(p, chi, eta);
	    chie = (GEN)p1[1]; 
	    chie = polmodi(chie, pmr);
	    nue  = (GEN)p1[2]; 
	    l    = itos((GEN)p1[3]);
	  }
	  if (l > 1)
	  {
            /* there are at least 2 factors mod. p => chi can be split */
	    delete_var();      
	    phi = eleval(fx, eta, alph);
	    phi = redelt(phi, p, pmf);
	    return Decomp(p, fx, mf, phi, chie, nue);
	  }
	  
	  /* if vp(eta) = vp(gamma - delta) > 0 */
	  if (gegal(nue, polx[v])) break;
	}
      delete_var();    

      pie = getprime(p, chi, eta, chie, nue, &Le, &Ee);
      if (Ea%Ee)
      {
	if (DEBUGLEVEL >= 5)
	  fprintferr("  Increasing Ea\n");
	pie = redelt(pie, p, pmf);
	/* we compute a new element such E = lcm(Ea, Ee) */	
	w = testc2(p, chi, pmr, nu, Ea, pie, Ee);
	if (gcmp1((GEN)w[1]))
	{
	  /* there are at least 2 factors mod. p => chi can be split */
	  phi = eleval(fx, (GEN)w[2], alph);
	  phi = redelt(phi, p, pmf);
	  return Decomp(p, fx, mf, phi, (GEN)w[3], (GEN)w[4]);
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

    w = update_alpha(p, fx, alph, chi, pmr, pmf, mf);
    alph = (GEN)w[1];
    chi  = (GEN)w[2];
    pmr  = (GEN)w[3];
    pdr  = (GEN)w[4];

    /* that can happen if p does not divide the field discriminant! */
    if (is_pm1(pmr))
      return dbasis(p, fx, mf, alph, chi);
  }
}

/* Returns [1,phi,chi,nu] if phi non-primary
 *         [2,phi,chi,nu] if D_phi = lcm (D_alpha, D_theta)
 */
static GEN
testb(GEN p,GEN fa,long Da,GEN theta,long Dt)
{
  long pp,Dat,t,v=varn(fa);
  GEN b,w,phi,h;

  Dat=clcm(Da,Dt)+3; b=cgetg(5,t_VEC);
  pp = p[2]; if (lgef(p)>3 || pp<0) pp=0;
  for (t=1; ; t++)
  {
    h = pp? stopoly(t,pp,v): scalarpol(stoi(t),v);
    phi = gadd(theta,gmod(h,fa));
    w=factcp(p,fa,phi); h=(GEN)w[3];
    if (h[2] > 1) { b[1]=un; break; }
    if (lgef(w[2]) == Dat) { b[1]=deux; break; }
  }
  b[2]=(long)phi; b[3]=w[1]; b[4]=w[2]; return b;
}

/* Returns [1,phi,chi,nu] if phi non-primary
 *         [2,phi,chi,nu] with F_phi = lcm (F_alpha, F_theta) 
 *                         and E_phi = E_alpha 
 */
static GEN
testb2(GEN p, GEN fa, long Fa, GEN theta, long Ft)
{
  long pp, Dat, t, v = varn(fa);
  GEN b, w, phi, h;

  Dat = clcm(Fa, Ft) + 3; 
  b  = cgetg(5, t_VEC);
  pp = p[2]; 
  if (lgef(p) > 3 || pp < 0) pp = 0;

  for (t = 1;; t++)
  {
    h = pp? stopoly(t, pp, v): scalarpol(stoi(t), v);
    phi = gadd(theta, gmod(h, fa));
    w = factcp(p, fa, phi); 
    h = (GEN)w[3];
    if (h[2] > 1) { b[1] = un; break; }
    if (lgef(w[2]) == Dat) { b[1] = deux; break; }
  }
  
  b[2] = (long)phi; 
  b[3] = w[1]; 
  b[4] = w[2]; 
  return b;
}

/* Returns [1,phi,chi,nu] if phi non-primary
 *         [2,phi,chi,nu] if M_phi = lcm (M_alpha, M_theta)
 */
static GEN
testc(GEN p, GEN fa, long c, GEN alph2, long Ma, GEN thet2, long Mt)
{
  GEN b,pc,ppc,c1,c2,c3,psi,phi,w,h;
  long r,s,t,v=varn(fa);

  b=cgetg(5,t_VEC); pc=gpuigs(p,c); ppc=mulii(pc,p);

  cbezout(Ma,Mt,&r,&s); t=0;
  while (r<0) { r=r+Mt; t++; }
  while (s<0) { s=s+Ma; t++; }

  c1=lift_intern(gpuigs(gmodulcp(alph2,fa),s));
  c2=lift_intern(gpuigs(gmodulcp(thet2,fa),r));
  c3=gdiv(gmod(gmul(c1,c2),fa),gpuigs(p,t));
  psi=gdiv(polmodi(gmul(pc,c3),ppc),pc);
  phi=gadd(polx[v],psi);

  w=factcp(p,fa,phi); h=(GEN)w[3];
  b[1] = (h[2] > 1)? un: deux;
  b[2]=(long)phi; b[3]=w[1]; b[4]=w[2]; return b;
}

/* Returns [1, phi, chi, nu] if phi non-primary
 *         [2, phi, chi, nu] if E_phi = lcm (E_alpha, E_theta)
 */
static GEN
testc2(GEN p, GEN fa, GEN pmr, GEN alph2, long Ea, GEN thet2, long Et)
{
  GEN b, c1, c2, c3, psi, phi, w, h;
  long r, s, t, v = varn(fa);

  b=cgetg(5, t_VEC);

  cbezout(Ea, Et, &r, &s); t = 0;
  while (r < 0) { r = r + Et; t++; }
  while (s < 0) { s = s + Ea; t++; }

  c1 = lift_intern(gpuigs(gmodulcp(alph2, fa), s));
  c2 = lift_intern(gpuigs(gmodulcp(thet2, fa), r));
  c3 = gdiv(gmod(gmul(c1, c2), fa), gpuigs(p, t));

  psi = redelt(c3, pmr, pmr);
  phi = gadd(polx[v], psi);

  w = factcp(p,fa,phi); h = (GEN)w[3];
  b[1] = (h[2] > 1)? un: deux;
  b[2] = (long)phi; 
  b[3] = w[1]; 
  b[4] = w[2]; 
  return b;
}

/* Returns
 *  [1,phi,chi,nu] if theta non-primary
 *  [2,phi,chi,nu] if D_phi > D_aplha or M_phi > M_alpha
 *  [3,phi,chi,nu] otherwise
 */
static GEN
testd(GEN p,GEN fa,long c,long Da,GEN alph2,long Ma,GEN theta)
{
  long Lt,Mt,Dt,av=avma,tetpil;
  GEN chi,nu,thet2,b,w,h;

  b=cgetg(5,t_VEC); w=factcp(p,fa,theta);
  chi=(GEN)w[1]; nu=(GEN)w[2]; h=(GEN)w[3];
  if (h[2] > 1)
  {
    b[1]=un; b[2]=(long)theta; b[3]=(long)chi; b[4]=(long)nu;
  }
  else
  {
    Dt=lgef(nu)-3;
    if (Da < clcm(Da,Dt)) b = testb(p,fa,Da,theta,Dt);
    else
    {
      thet2=setup(p,fa,theta,nu, &Lt,&Mt);
      if (Ma < clcm(Ma,Mt)) b = testc(p,fa,c,alph2,Ma,thet2,Mt);
      else
      {
        b[1]=lstoi(3); b[2]=(long)theta; b[3]=(long)chi; b[4]=(long)nu;
      }
    }
  }
  tetpil=avma; return gerepile(av,tetpil,gcopy(b));
}

/* Factor characteristic polynomial of beta mod p */
GEN
factcp(GEN p,GEN f,GEN beta)
{
  long av,tetpil,l;
  GEN chi,nu, b = cgetg(4,t_VEC);

  chi = mycaract(f,beta);
  av=avma; nu=(GEN)factmod(chi,p)[1]; l=lg(nu)-1;
  nu=lift_intern((GEN)nu[1]); tetpil=avma;
  b[1]=(long)chi;
  b[2]=lpile(av,tetpil,gcopy(nu));
  b[3]=lstoi(l); return b;
}

/* evaluate h(a) mod f */
GEN
eleval(GEN f,GEN h,GEN a)
{
  long n,av,tetpil;
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

/* Compute theta^k mod (f,pd) */
static GEN
eltppm(GEN f,GEN pd,GEN theta,GEN k)
{
  GEN phi,psi,D, q = k;
  long av = avma, av1, lim = stack_lim(av,2);

  if (!signe(k)) return polun[varn(f)];
  D = mulii(pd, sqri(pd)); av1 = avma;
  phi=pd; psi=gmul(pd,theta);

  for(;;)
  {
    if (mod2(q)) phi = gdivexact(Fp_res(gmul(phi,psi), f, D), pd);
    q=shifti(q,-1); if (!signe(q)) break;
    psi = gdivexact(Fp_res(gsqr(psi), f, D), pd);
    if (low_stack(lim,stack_lim(av,2)))
    {
      GEN *gptr[3]; gptr[0]=&psi; gptr[1]=&phi; gptr[2]=&q;
      if(DEBUGMEM>1) err(warnmem,"eltppm");
      gerepilemany(av1,gptr,3);
    }
  }
  return gerepileupto(av,gdiv(phi,pd));
}

/* Sylvester's matrix, mod p^m (assumes f1 monic) */
static GEN
sylpm(GEN f1,GEN f2,GEN pm)
{
  long n,deg,k,j,v=varn(f1);
  GEN a,h;

  n=lgef(f1)-3; a=cgetg(n+1,t_MAT);
  h = Fp_res(f2,f1,pm);
  for (j=1; j<=n; j++)
  {
    a[j] = lgetg(n+1,t_COL);
    deg=lgef(h)-3;
    for (k=1; k<=deg+1; k++) coeff(a,k,j)=h[k+1];
    for (   ; k<=n; k++) coeff(a,k,j)=zero;

    if (j<n) h = Fp_res(gmul(polx[v],h),f1,pm);
  }
  return hnfmodid(a,pm);
}

/* polynomial gcd mod p^m (assumes f1 monic) */
GEN
gcdpm(GEN f1,GEN f2,GEN pm)
{
  long n,c,v=varn(f1),av=avma,tetpil;
  GEN a,col;

  n=lgef(f1)-3; a=sylpm(f1,f2,pm);
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
  long av=avma,tetpil;

  x = sylpm(x,y,pm); tetpil=avma;
  return gerepile(av,tetpil, icopy(gcoeff(x,1,1)));
}

/* Normalized integral basis */
static GEN
nbasis(GEN ibas,GEN pd)
{
  long n,j,k,m;
  GEN a;

  n=lg(ibas)-1; m=lgef(ibas[1])-2;
  a=cgetg(n+1,t_MAT);
  for (k=1; k<=n; k++)
  {
    m=lgef(ibas[k])-2; a[k]=lgetg(n+1,t_COL);
    for (j=1; j<=m; j++) coeff(a,j,k)=coeff(ibas,j+1,k);
    for (   ; j<=n; j++) coeff(a,j,k)=zero;
  }
  return gdiv(hnfmodid(a,pd), pd);
}

static long
clcm(long a,long b)
{
  long d,r,v1;

  d=a; r=b;
  for(;;)
  {
    if (!r) return (a*b)/d;
    v1=r; r=d%r; d=labs(v1);
  }
}

/*******************************************************************/
/*                                                                 */
/*                   BUCHMANN-LENSTRA ALGORITHM                    */
/*                                                                 */
/*******************************************************************/
static GEN lens(GEN nf,GEN p,GEN a);
GEN element_powid_mod_p(GEN nf, long I, GEN n, GEN p);

/* return a Z basis of Z_K's p-radical, modfrob = x--> x^p-x */
static GEN
pradical(GEN nf, GEN p, GEN *modfrob)
{
  long i,N=lgef(nf[1])-3;
  GEN p1,m,frob,rad;

  frob = cgetg(N+1,t_MAT);
  for (i=1; i<=N; i++)
    frob[i] = (long) element_powid_mod_p(nf,i,p, p);

  /* p1 = smallest power of p st p^k >= N */
  p1=p; while (cmpis(p1,N)<0) p1=mulii(p1,p);
  if (p1==p) m = frob;
  else
  {
    m=cgetg(N+1,t_MAT); p1 = divii(p1,p);
    for (i=1; i<=N; i++)
      m[i]=(long)element_pow_mod_p(nf,(GEN)frob[i],p1, p);
  }
  rad = ker_mod_p(m, p);
  for (i=1; i<=N; i++)
    coeff(frob,i,i) = lsubis(gcoeff(frob,i,i), 1);
  *modfrob = frob; return rad;
}

static GEN
project(GEN algebre, GEN x, long k, long kbar)
{
  x = inverseimage(algebre,x);
  x += k; x[0] = evaltyp(t_COL) | evallg(kbar+1);
  return x;
}

/* Calcule le polynome minimal de alpha dans algebre (coeffs dans Z) */
static GEN
pol_min(GEN alpha,GEN nf,GEN algebre,long kbar,GEN p)
{
  long av=avma,tetpil,i,N,k;
  GEN p1,puiss;

  N = lg(nf[1])-3; puiss=cgetg(N+2,t_MAT);
  k = N-kbar; p1=alpha;
  puiss[1] = (long)gscalcol_i(gun,kbar);
  for (i=2; i<=N+1; i++)
  {
    if (i>2) p1 = element_mul(nf,p1,alpha);
    puiss[i] = (long) project(algebre,p1,k,kbar);
  }
  puiss = lift_intern(puiss);
  p1 = (GEN)ker_mod_p(puiss, p)[1]; tetpil=avma;
  return gerepile(av,tetpil,gtopolyrev(p1,0));
}

/* Evalue le polynome pol en alpha,element de nf */
static GEN
eval_pol(GEN nf,GEN pol,GEN alpha,GEN algebre,GEN algebre1)
{
  long av=avma,tetpil,i,kbar,k, lx = lgef(pol)-1, N = lgef(nf[1])-3;
  GEN res;

  kbar = lg(algebre1)-1; k = N-kbar;
  res = gscalcol_i((GEN)pol[lx], N);
  for (i=2; i<lx; i++)
  {
    res = element_mul(nf,alpha,res);
    res[1] = ladd((GEN)res[1],(GEN)pol[i]);
  }
  res = project(algebre,res,k,kbar); tetpil=avma;
  return gerepile(av,tetpil,gmul(algebre1,res));
}

static GEN
kerlens2(GEN x, GEN p)
{
  long i,j,k,t,nbc,nbl,av,av1;
  GEN a,c,l,d,y,q;

  av=avma; a=gmul(x,gmodulsg(1,p));
  nbl=nbc=lg(x)-1;
  c=new_chunk(nbl+1); for (i=1; i<=nbl; i++) c[i]=0;
  l=new_chunk(nbc+1);
  d=new_chunk(nbc+1);
  k = t = 1;
  while (t<=nbl && k<=nbc)
  {
    for (j=1; j<k; j++)
      for (i=1; i<=nbl; i++)
	if (i!=l[j])
	  coeff(a,i,k) = lsub(gmul((GEN)d[j],gcoeff(a,i,k)),
	                      gmul(gcoeff(a,l[j],k),gcoeff(a,i,j)));
    t=1; while (t<=nbl && (c[t] || gcmp0(gcoeff(a,t,k)))) t++;
    if (t<=nbl) { d[k]=coeff(a,t,k); c[t]=k; l[k]=t; k++; }
  }
  if (k>nbc) err(bugparier,"kerlens2");
  y=cgetg(nbc+1,t_COL);
  y[1]=(k>1)?coeff(a,l[1],k):un;
  for (q=gun,j=2; j<k; j++)
  {
    q=gmul(q,(GEN)d[j-1]);
    y[j]=lmul(gcoeff(a,l[j],k),q);
  }
  if (k>1) y[k]=lneg(gmul(q,(GEN)d[k-1]));
  for (j=k+1; j<=nbc; j++) y[j]=zero;
  av1=avma; return gerepile(av,av1,lift(y));
}

static GEN
kerlens(GEN x, GEN pgen)
{
  long av = avma, i,j,k,t,nbc,nbl,p,q,*c,*l,*d,**a;
  GEN y;

  if (cmpis(pgen, MAXHALFULONG>>1) > 0)
    return kerlens2(x,pgen);
  /* ici p <= (MAXHALFULONG>>1) ==> long du C */
  p=itos(pgen); nbl=nbc=lg(x)-1;
  a=(long**)new_chunk(nbc+1);
  for (j=1; j<=nbc; j++)
  {
    c=a[j]=new_chunk(nbl+1);
    for (i=1; i<=nbl; i++) c[i]=smodis(gcoeff(x,i,j),p);
  }
  c=new_chunk(nbl+1); for (i=1; i<=nbl; i++) c[i]=0;
  l=new_chunk(nbc+1);
  d=new_chunk(nbc+1);
  k = t = 1;
  while (t<=nbl && k<=nbc)
  {
    for (j=1; j<k; j++)
      for (i=1; i<=nbl; i++)
	if (i!=l[j])
          a[k][i] = (d[j]*a[k][i] - a[j][i]*a[k][l[j]]) % p;
    t=1; while (t<=nbl && (c[t] || !a[k][t])) t++;
    if (t<=nbl) { d[k]=a[k][t]; c[t]=k; l[k++]=t; }
  }
  if (k>nbc) err(bugparier,"kerlens");
  avma=av; y=cgetg(nbc+1,t_COL);
  t=(k>1) ? a[k][l[1]]:1;
  y[1]=(t>0)? lstoi(t):lstoi(t+p);
  for (q=1,j=2; j<k; j++)
  {
    q = (q*d[j-1]) % p;
    t = (a[k][l[j]]*q) % p;
    y[j] = (t>0) ? lstoi(t) : lstoi(t+p);
  }
  if (k>1)
  {
    t = (q*d[k-1]) % p;
    y[k] = (t>0) ? lstoi(p-t) : lstoi(-t);
  }
  for (j=k+1; j<=nbc; j++) y[j]=zero;
  return y;
}

/* Calcule la constante de lenstra de l'ideal p.Z_K+a.Z_K ou a est un
vecteur sur la base d'entiers */
static GEN
lens(GEN nf, GEN p, GEN a)
{
  long av=avma,tetpil,N=lgef(nf[1])-3,j;
  GEN mat=cgetg(N+1,t_MAT);
  for (j=1; j<=N; j++) mat[j]=(long)element_mulid(nf,a,j);
  tetpil=avma; return gerepile(av,tetpil,kerlens(mat,p));
}

GEN det_mod_P_n(GEN a, GEN N, GEN P);
GEN sylvestermatrix_i(GEN x, GEN y);

/* check if p^va doesnt divide norm x (or norm(x+p)) */
#if 0
/* compute norm mod p^whatneeded using Sylvester's matrix */
/* looks slower than the new subresultant. Have to re-check this */
static GEN
prime_check_elt(GEN a, GEN pol, GEN p, GEN pf)
{
  GEN M,mod,x, c = denom(content(a));
  long v = pvaluation(c, p, &x); /* x is junk */

  mod = mulii(pf, gpowgs(p, (lgef(pol)-3)*v + 1));

  x = Fp_pol_red(gmul(a,c), mod);
  M = sylvestermatrix_i(pol,x);
  if (det_mod_P_n(M,mod,p) == gzero)
  {
    x[2] = ladd((GEN)x[2], mulii(p,c));
    M = sylvestermatrix_i(pol,x);
    if (det_mod_P_n(M,mod,p) == gzero) return NULL;
    a[2] = ladd((GEN)a[2], p);
  }
  return a;
}
#else
/* use subres to compute norm */
static GEN
prime_check_elt(GEN a, GEN pol, GEN p, GEN pf)
{
  GEN norme=subres(pol,a);
  if (resii(divii(norme,pf),p) != gzero) return a;
  a=gadd(a,p); norme=subres(pol,a);
  if (resii(divii(norme,pf),p) != gzero) return a;
  return NULL;
}
#endif

#if 0
GEN
prime_two_elt_loop(GEN beta, GEN pol, GEN p, GEN pf)
{
  long av, m = lg(beta)-1;
  int i,j,K, *x = (int*)new_chunk(m+1);
  GEN a;

  K = 1; av = avma;
  for(;;)
  { /* x runs through strictly increasing sequences of length K,
     * 1 <= x[i] <= m */
nextK:
    if (DEBUGLEVEL) fprintferr("K = %d\n", K);
    for (i=1; i<=K; i++) x[i] = i;
    for(;;)
    {
      if (DEBUGLEVEL > 1)
      {
        for (i=1; i<=K; i++) fprintferr("%d ",x[i]);
        fprintferr("\n"); flusherr();
      }
      a = (GEN)beta[x[1]];
      for (i=2; i<=K; i++) a = gadd(a, (GEN)beta[x[i]]);
      if ((a = prime_check_elt(a,pol,p,pf))) return a;
      avma = av;

      /* start: i = K+1; */
      do
      {
        if (--i == 0)
        {
          if (++K > m) return NULL; /* fail */
          goto nextK;
        }
        x[i]++;
      } while (x[i] > m - K + i);
      for (j=i; j<K; j++) x[j+1] = x[j]+1;
    }
  }
}
#endif

GEN
random_prime_two_elt_loop(GEN beta, GEN pol, GEN p, GEN pf)
{
  long av = avma, z,i, m = lg(beta)-1;
  long keep = getrand();
  int c = 0;
  GEN a;

  for(i=1; i<=m; i++)
    if ((a = prime_check_elt((GEN)beta[i],pol,p,pf))) return a;
  (void)setrand(1);
  if (DEBUGLEVEL) fprintferr("prime_two_elt_loop, hard case: ");
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

/* Input: an ideal mod p (!= Z_K)
 * Output: a 2-elt representation [p, x] */
static GEN
prime_two_elt(GEN nf, GEN p, GEN ideal)
{
  GEN beta,a,pf, pol = (GEN)nf[1];
  long av,tetpil,f, N=lgef(pol)-3, m=lg(ideal)-1;

  if (!m) return gscalcol_i(p,N);

  /* we want v_p(Norm(beta)) = p^f, f = N-m */
  av = avma; f = N-m; pf = gpuigs(p,f);
  ideal = centerlift(ideal);
  ideal = concatsp(gscalcol(p,N), ideal);
  ideal = ideal_better_basis(nf, ideal, p);
  beta = gmul((GEN)nf[7], ideal);

#if 0
  a = prime_two_elt_loop(beta,pol,p,pf);
  if (!a) err(bugparier, "prime_two_elt (failed)");
#else
  a = random_prime_two_elt_loop(beta,pol,p,pf);
#endif

  a = centermod(algtobasis_intern(nf,a), p);
  if (resii(divii(subres(gmul((GEN)nf[7],a),pol),pf),p) == gzero)
    a[1] = laddii((GEN)a[1],p);
  tetpil = avma; return gerepile(av,tetpil,gcopy(a));
}

static GEN
apply_kummer(GEN nf,GEN pol,GEN e,GEN p,long N,GEN *beta)
{
  GEN T,p1, res = cgetg(6,t_VEC);
  long f = lgef(pol)-3;

  res[1]=(long)p;
  res[3]=(long)e;
  res[4]=lstoi(f);
  if (f == N) /* inert */
  {
    res[2]=(long)gscalcol_i(p,N);
    res[5]=(long)gscalcol_i(gun,N);
  }
  else
  {
    T = (GEN) nf[1];
    if (ggval(subres(pol,T),p) > f)
      pol[2] = laddii((GEN)pol[2],p);
    res[2] = (long) algtobasis_intern(nf,pol);

    p1 = Fp_deuc(T,pol,p);
    res[5] = (long) centermod(algtobasis_intern(nf,p1), p);

    if (beta)
      *beta = *beta? Fp_deuc(*beta,pol,p): p1;
  }
  return res;
}

/* prime ideal decomposition of p sorted by increasing residual degree */
GEN
primedec(GEN nf, GEN p)
{
  long av=avma,tetpil,i,j,k,kbar,np,c,indice,N,lp;
  GEN ex,f,list,ip,elth,h;
  GEN modfrob,algebre,algebre1,b,mat1,T,nfp;
  GEN alpha,beta,p1,p2,unmodp,zmodp,idmodp;

  if (DEBUGLEVEL>=3) timer2();
  nf=checknf(nf); T=(GEN)nf[1]; N=lgef(T)-3;
  f=factmod(T,p); ex=(GEN)f[2];
  f=centerlift((GEN)f[1]); np=lg(f);
  if (DEBUGLEVEL>=6) msgtimer("factmod");

  if (signe(modii((GEN)nf[4],p))) /* p doesn't divide index */
  {
    list=cgetg(np,t_VEC);
    for (i=1; i<np; i++)
      list[i]=(long)apply_kummer(nf,(GEN)f[i],(GEN)ex[i],p,N, NULL);
    if (DEBUGLEVEL>=6) msgtimer("simple primedec");
    p1=stoi(4); tetpil=avma;
    return gerepile(av,tetpil,vecsort(list,p1));
  }

  p1 = (GEN)f[1];
  for (i=2; i<np; i++)
    p1 = Fp_pol_red(gmul(p1, (GEN)f[i]), p);
  p1 = Fp_pol_red(gdiv(gadd(gmul(p1, Fp_deuc(T,p1,p)), gneg(T)), p), p);
  list = cgetg(N+1,t_VEC);
  indice=1; beta=NULL;
  for (i=1; i<np; i++) /* e = 1 or f[i] does not divide p1 (mod p) */
    if (is_pm1(ex[i]) || signe(Fp_res(p1,(GEN)f[i],p)))
      list[indice++] = (long)apply_kummer(nf,(GEN)f[i],(GEN)ex[i],p,N,&beta);
  if (DEBUGLEVEL>=3) msgtimer("unramified factors");

  /* modfrob = modified Frobenius: x -> x^p - x mod p */
  ip = pradical(nf,p,&modfrob);
  if (DEBUGLEVEL>=3) msgtimer("pradical");

  if (beta)
  {
    beta = algtobasis_intern(nf,beta);
    lp=lg(ip)-1; p1=cgetg(2*lp+N+1,t_MAT);
    for (i=1; i<=N; i++) p1[i]=(long)element_mulid(nf,beta,i);
    for (   ; i<=N+lp; i++)
    {
      p2 = (GEN) ip[i-N];
      p1[i+lp] = (long) p2;
      p1[i] = ldiv(element_mul(nf,lift(p2),beta),p);
    }
    ip = image_mod_p(p1, p);
    if (lg(ip)>N) err(bugparier,"primedec (bad pradical)");
  }
  unmodp=gmodulsg(1,p); zmodp=gmodulsg(0,p);
  idmodp = idmat_intern(N,unmodp,zmodp);
  ip = gmul(ip, unmodp);
  nfp = gscalcol_i(p,N);

  h=cgetg(N+1,t_VEC); h[1]=(long)ip;
  for (c=1; c; c--)
  {
    elth=(GEN)h[c]; k=lg(elth)-1; kbar=N-k;
    p1 = concatsp(elth,(GEN)idmodp[1]);
    algebre = suppl_intern(p1,idmodp);
    algebre1 = cgetg(kbar+1,t_MAT);
    for (i=1; i<=kbar; i++) algebre1[i]=algebre[i+k];
    b = gmul(modfrob,algebre1);
    for (i=1;i<=kbar;i++)
      b[i] = (long) project(algebre,(GEN) b[i],k,kbar);
    mat1 = ker_mod_p(lift_intern(b), p);
    if (lg(mat1)>2)
    {
      GEN mat2 = cgetg(k+N+1,t_MAT);
      for (i=1; i<=k; i++) mat2[i]=elth[i];
      alpha=gmul(algebre1,(GEN)mat1[2]);
      p1 = pol_min(alpha,nf,algebre,kbar,p);
      p1 = (GEN)factmod(p1,p)[1];
      for (i=1; i<lg(p1); i++)
      {
	beta = eval_pol(nf,(GEN)p1[i],alpha,algebre,algebre1);
        beta = lift_intern(beta);
	for (j=1; j<=N; j++)
	  mat2[k+j] = (long)Fp_vec(element_mulid(nf,beta,j), p);
	h[c] = (long) image(mat2); c++;
      }
    }
    else
    {
      long av1; p1 = cgetg(6,t_VEC);
      list[indice++] = (long)p1;
      p1[1]=(long)p; p1[4]=lstoi(kbar);
      p1[2]=(long)prime_two_elt(nf,p,elth);
      p1[5]=(long)lens(nf,p,(GEN)p1[2]);
      av1=avma;
      i = int_elt_val(nf,nfp,p,(GEN)p1[5],N);
      avma=av1;
      p1[3]=lstoi(i);
    }
    if (DEBUGLEVEL>=3) msgtimer("h[%ld]",c);
  }
  setlg(list, indice); tetpil=avma;
  return gerepile(av,tetpil,gen_sort(list,0,cmp_prime_over_p));
}

/* REDUCTION Modulo a prime ideal */

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

/* for internal use */
GEN
nfreducemodpr(GEN nf, GEN x, GEN prhall)
{
  long i,v;
  GEN p,prh,den;

  for (i=lg(x)-1; i>0; i--)
    if (typ(x[i]) == t_INTMOD) { x=lift_intern(x); break; }
  prh=(GEN)prhall[1]; p=gcoeff(prh,1,1);
  den=denom(x);
  if (!gcmp1(den))
  {
    v=ggval(den,p);
    if (v) x=element_mul(nf,x,element_pow(nf,(GEN)prhall[2],stoi(v)));
    x = gmod(x,p);
  }
  return Fp_vec(nfreducemodpr_i(x, prh), p);
}

/* public function */
GEN
nfreducemodpr2(GEN nf, GEN x, GEN prhall)
{
  long av = avma; checkprhall(prhall);
  if (typ(x) != t_COL) x = algtobasis(nf,x);
  return gerepileupto(av, nfreducemodpr(nf,x,prhall));
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
 * pseudo-basis of the module generated by x and y. For internal use.
 */
static GEN
rnfjoinmodules(GEN nf, GEN x, GEN y)
{
  long i,lx,ly;
  GEN p1,p2,z,Hx,Hy,Ix,Iy;

  if (x == NULL) return y;
  Hx=(GEN)x[1]; lx=lg(Hx); Ix=(GEN)x[2];
  Hy=(GEN)y[1]; ly=lg(Hy); Iy=(GEN)y[2];
  i = lx+ly-1;
  z = (GEN)gpmalloc(sizeof(long*)*(3+2*i));
  *z = evaltyp(t_VEC)|evallg(3);
  p1 =  z+3; z[1]=(long)p1; *p1 = evaltyp(t_MAT)|evallg(i);
  p2 = p1+i; z[2]=(long)p2; *p2 = evaltyp(t_VEC)|evallg(i);

  for (i=1; i<lx; i++) { p1[i]=Hx[i]; p2[i]=Ix[i]; }
  for (   ; i<lx+ly-1; i++) { p1[i]=Hy[i-lx+1]; p2[i]=Iy[i-lx+1]; }
  x = nfhermite(nf,z); free(z); return x;
}

/* a usage interne, pas de gestion de pile : x et y sont des vecteurs dont
 * les coefficients sont les composantes sur nf[7]; avec reduction mod pr sauf
 * si prhall=NULL
 */
static GEN
rnfelement_mulidmod(GEN nf, GEN multab, GEN unnf, GEN x, long h, GEN prhall)
{
  long j,k,N;
  GEN p1,c,v,s,znf;

  if (h==1) return gcopy(x);
  N = lg(x)-1; multab += (h-1)*N;
  x = lift(x); v = cgetg(N+1,t_COL);
  znf = gscalcol_i(gzero,lg(unnf)-1);
  for (k=1; k<=N; k++)
  {
    s = gzero;
    for (j=1; j<=N; j++)
      if (!gcmp0(p1 = (GEN)x[j]) && !gcmp0(c = gcoeff(multab,k,j)))
      {
        if (!gegal(c,unnf)) p1 = element_mul(nf,p1,c);
        s = gadd(s,p1);
      }
    if (s == gzero) s = znf;
    else
      if (prhall) s = nfreducemodpr(nf,s,prhall);
    v[k] = (long)s;
  }
  return v;
}

/* a usage interne, pas de gestion de pile : x est un vecteur dont
 * les coefficients sont les composantes sur nf[7]
 */
static GEN
rnfelement_sqrmod(GEN nf, GEN multab, GEN unnf, GEN x, GEN prhall)
{
  long i,j,k,n;
  GEN p1,c,z,s;

  n=lg(x)-1; x=lift(x); z=cgetg(n+1,t_COL);
  for (k=1; k<=n; k++)
  {
    if (k == 1)
      s = element_sqr(nf,(GEN)x[1]);
    else
      s = gmul2n(element_mul(nf,(GEN)x[1],(GEN)x[k]), 1);
    for (i=2; i<=n; i++)
    {
      c = gcoeff(multab,k,(i-1)*n+i);
      if (!gcmp0(c))
      {
	p1=element_sqr(nf,(GEN)x[i]);
	if (!gegal(c,unnf)) p1 = element_mul(nf,p1,c);
        s = gadd(s,p1);
      }
      for (j=i+1; j<=n; j++)
      {
	c = gcoeff(multab,k,(i-1)*n+j);
	if (!gcmp0(c))
	{
	  p1=gmul2n(element_mul(nf,(GEN)x[i],(GEN)x[j]),1);
	  if (!gegal(c,unnf)) p1 = element_mul(nf,p1,c);
          s = gadd(s,p1);
	}
      }
    }
    if (prhall) s = nfreducemodpr(nf,s,prhall);
    z[k]=(long)s;
  }
  return z;
}

/* Compute x^n mod pr in the extension, assume n >= 0 */
static GEN
rnfelementid_powmod(GEN nf, GEN multab, GEN matId, long h, GEN n, GEN prhall)
{
  long i,m,av=avma,tetpil;
  GEN y, unrnf=(GEN)matId[1], unnf=(GEN)unrnf[1];
  ulong j;

  if (!signe(n)) return unrnf;
  y=(GEN)matId[h]; i = lgefint(n)-1; m=n[i]; j=HIGHBIT;
  while ((m&j)==0) j>>=1;
  for (j>>=1; j; j>>=1)
  {
    y = rnfelement_sqrmod(nf,multab,unnf,y,prhall);
    if (m&j) y = rnfelement_mulidmod(nf,multab,unnf,y,h,prhall);
  }
  for (i--; i>=2; i--)
    for (m=n[i],j=HIGHBIT; j; j>>=1)
    {
      y = rnfelement_sqrmod(nf,multab,unnf,y,prhall);
      if (m&j) y = rnfelement_mulidmod(nf,multab,unnf,y,h,prhall);
    }
  tetpil=avma; return gerepile(av,tetpil,gcopy(y));
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
rnfordmax(GEN nf, GEN pol, GEN pr, GEN unnf, GEN id, GEN matId)
{
  long av=avma,tetpil,av1,lim,i,j,k,n,v1,v2,vpol,m,cmpt,sep;
  GEN p,q,q1,prhall,A,Aa,Aaa,A1,I,R,p1,p2,p3,multab,multabmod,Aainv;
  GEN pip,baseIp,baseOp,alpha,matprod,alphainv,matC,matG,vecpro,matH;
  GEN neworder,H,Hid,alphalistinv,alphalist,prhinv;

  if (DEBUGLEVEL>1) fprintferr(" treating %Z\n",pr);
  prhall=nfmodprinit(nf,pr);
  q=cgetg(3,t_VEC); q[1]=(long)pr;q[2]=(long)prhall;
  p1=rnfdedekind(nf,pol,q);
  if (gcmp1((GEN)p1[1]))
    {tetpil=avma; return gerepile(av,tetpil,gcopy((GEN)p1[2]));}

  sep=itos((GEN)p1[3]);
  A=gmael(p1,2,1);
  I=gmael(p1,2,2);

  n=lgef(pol)-3; vpol=varn(pol);
  p=(GEN)pr[1]; q=powgi(p,(GEN)pr[4]); pip=(GEN)pr[2];
  q1=q; while (cmpis(q1,n)<0) q1=mulii(q1,q);

  multab=cgetg(n*n+1,t_MAT);
  for (j=1; j<=n*n; j++) multab[j]=lgetg(n+1,t_COL);
  prhinv = idealinv(nf,(GEN)prhall[1]);
  alphalistinv=cgetg(n+1,t_VEC);
  alphalist=cgetg(n+1,t_VEC);
  A1=cgetg(n+1,t_MAT);
  av1=avma; lim=stack_lim(av1,1);
  for(cmpt=1; ; cmpt++)
  {
    if (DEBUGLEVEL>1)
    {
      fprintferr("    %ld%s pass\n",cmpt,eng_ord(cmpt));
      flusherr();
    }
    for (i=1; i<=n; i++)
    {
      if (gegal((GEN)I[i],id)) alphalist[i]=alphalistinv[i]=(long)unnf;
      else
      {
	p1=ideal_two_elt(nf,(GEN)I[i]);
	v1=gcmp0((GEN)p1[1])? EXP220
                            : element_val(nf,(GEN)p1[1],pr);
	v2=element_val(nf,(GEN)p1[2],pr);
	if (v1>v2) p2=(GEN)p1[2]; else p2=(GEN)p1[1];
	alphalist[i]=(long)p2;
        alphalistinv[i]=(long)element_inv(nf,p2);
      }
    }
    for (j=1; j<=n; j++)
    {
      p1=cgetg(n+1,t_COL); A1[j]=(long)p1;
      for (i=1; i<=n; i++)
	p1[i] = (long)element_mul(nf,gcoeff(A,i,j),(GEN)alphalist[j]);
    }
    Aa=basistoalg(nf,A1); Aainv=lift_intern(ginv(Aa));
    Aaa=mat_to_vecpol(Aa,vpol);
    for (i=1; i<=n; i++) for (j=i; j<=n; j++)
    {
      long tp;
      p1 = lift_intern(gres(gmul((GEN)Aaa[i],(GEN)Aaa[j]), pol));
      tp = typ(p1);
      if (is_scalar_t(tp) || (tp==t_POL && varn(p1)>vpol))
	p2 = gmul(p1, (GEN)Aainv[1]);
      else
        p2 = gmul(Aainv, pol_to_vec(p1, n));

      p3 = algtobasis(nf,p2);
      for (k=1; k<=n; k++)
      {
	coeff(multab,k,(i-1)*n+j) = p3[k];
	coeff(multab,k,(j-1)*n+i) = p3[k];
      }
    }
    R=cgetg(n+1,t_MAT); multabmod = mymod(multab,p);
    R[1] = matId[1];
    for (j=2; j<=n; j++)
      R[j] = (long) rnfelementid_powmod(nf,multabmod,matId, j,q1,prhall);
    baseIp = nfkermodpr(nf,R,prhall);
    baseOp = lift_intern(nfsuppl(nf,baseIp,n,prhall));
    alpha=cgetg(n+1,t_MAT);
    for (j=1; j<lg(baseIp); j++) alpha[j]=baseOp[j];
    for (   ; j<=n; j++)
    {
      p1=cgetg(n+1,t_COL); alpha[j]=(long)p1;
      for (i=1; i<=n; i++)
	p1[i]=(long)element_mul(nf,pip,gcoeff(baseOp,i,j));
    }
    matprod=cgetg(n+1,t_MAT);
    for (j=1; j<=n; j++)
    {
      p1=cgetg(n+1,t_COL); matprod[j]=(long)p1;
      for (i=1; i<=n; i++)
      {
        p2 = rnfelement_mulidmod(nf,multab,unnf, (GEN)alpha[i],j, NULL);
        for (k=1; k<=n; k++)
          p2[k] = lmul((GEN)nf[7], (GEN)p2[k]);
        p1[i] = (long)p2;
      }
    }
    alphainv = lift_intern(ginv(basistoalg(nf,alpha)));
    matC = cgetg(n+1,t_MAT);
    for (j=1; j<=n; j++)
    {
      p1=cgetg(n*n+1,t_COL); matC[j]=(long)p1;
      for (i=1; i<=n; i++)
      {
	p2 = gmul(alphainv, gcoeff(matprod,i,j));
	for (k=1; k<=n; k++)
	  p1[(i-1)*n+k]=(long)nfreducemodpr(nf,algtobasis(nf,(GEN)p2[k]),prhall);
      }
    }
    matG=nfkermodpr(nf,matC,prhall); m=lg(matG)-1;
    vecpro=cgetg(3,t_VEC);
    p1=cgetg(n+m+1,t_MAT); vecpro[1]=(long)p1;
    p2=cgetg(n+m+1,t_VEC); vecpro[2]=(long)p2;
    for (j=1; j<=m; j++)
    {
      p1[j] = llift((GEN)matG[j]);
      p2[j] = (long)prhinv;
    }
    p1 += m;
    p2 += m;
    for (j=1; j<=n; j++)
    {
      p1[j] = matId[j];
      p2[j] = (long)idealmul(nf,(GEN)I[j],(GEN)alphalistinv[j]);
    }
    matH=nfhermite(nf,vecpro);
    p1=algtobasis(nf,gmul(Aa,basistoalg(nf,(GEN)matH[1])));
    p2=(GEN)matH[2];

    tetpil=avma; neworder=cgetg(3,t_VEC);
    H=cgetg(n+1,t_MAT); Hid=cgetg(n+1,t_VEC);
    for (j=1; j<=n; j++)
    {
      p3=cgetg(n+1,t_COL); H[j]=(long)p3;
      for (i=1; i<=n; i++)
	p3[i]=(long)element_mul(nf,gcoeff(p1,i,j),(GEN)alphalistinv[j]);
      Hid[j]=(long)idealmul(nf,(GEN)p2[j],(GEN)alphalist[j]);
    }
    if (DEBUGLEVEL>3)
      { fprintferr(" new order:\n"); outerr(H); outerr(Hid); }
    if (sep == 2 || gegal(I,Hid))
    {
      neworder[1]=(long)H; neworder[2]=(long)Hid;
      return gerepile(av,tetpil,neworder);
    }

    A=H; I=Hid;
    if (low_stack(lim, stack_lim(av1,1)))
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
fix_relative_pol(GEN nf, GEN x)
{
  GEN xnf = (typ(nf) == t_POL)? nf: (GEN)nf[1];
  long i, vnf = varn(xnf), lx = lg(x);
  if (typ(x) != t_POL || varn(x) >= vnf)
    err(talker,"incorrect polynomial in rnf function");
  x = dummycopy(x);
  for (i=2; i<lx; i++)
    if (typ(x[i]) == t_POL)
    {
      check_pol((GEN)x[i], vnf);
      x[i] = lmodulcp((GEN)x[i], xnf);
    }
  return x;
}

static GEN
rnfround2all(GEN nf, GEN pol, long all)
{
  long av=avma,tetpil,i,j,n,N,nbidp,vpol,*ep;
  GEN p1,p2,p3,p4,polnf,list,unnf,id,matId,I,W,pseudo,y,discpol,d,D,sym;

  nf=checknf(nf); polnf=(GEN)nf[1]; vpol=varn(pol);
  pol = fix_relative_pol(nf,pol);
  N=lgef(polnf)-3; n=lgef(pol)-3; discpol=discsr(pol);
  list=idealfactor(nf,discpol); ep=(long*)list[2]; list=(GEN)list[1];
  nbidp=lg(list)-1; for(i=1;i<=nbidp;i++) ep[i]=itos((GEN)ep[i]);
  if (DEBUGLEVEL>1)
  {
    fprintferr("Ideals to consider:\n");
    for (i=1; i<=nbidp; i++)
      if (ep[i]>1) fprintferr("%Z^%ld\n",list[i],ep[i]);
    flusherr();
  }
  id=idmat(N); unnf=gscalcol_i(gun,N);
  matId=idmat_intern(n,unnf, gscalcol_i(gzero,N));
  pseudo = NULL;
  for (i=1; i<=nbidp; i++)
    if (ep[i] > 1)
    {
      y=rnfordmax(nf,pol,(GEN)list[i],unnf,id,matId);
      pseudo = rnfjoinmodules(nf,pseudo,y);
    }
  if (!pseudo)
  {
    I=cgetg(n+1,t_VEC); for (i=1; i<=n; i++) I[i]=(long)id;
    pseudo=cgetg(3,t_VEC); pseudo[1]=(long)matId; pseudo[2]=(long)I;
  }
  W=gmodulcp(mat_to_vecpol(basistoalg(nf,(GEN)pseudo[1]),vpol),pol);
  p2=cgetg(n+1,t_MAT); for (j=1; j<=n; j++) p2[j]=lgetg(n+1,t_COL);
  sym=polsym(pol,n-1);
  for (j=1; j<=n; j++)
    for (i=j; i<=n; i++)
    {
      p1 = lift_intern(gmul((GEN)W[i],(GEN)W[j]));
      coeff(p2,j,i)=coeff(p2,i,j)=(long)quicktrace(p1,sym);
    }
  d = algtobasis_intern(nf,det(p2));

  I=(GEN)pseudo[2];
  i=1; while (i<=n && gegal((GEN)I[i],id)) i++;
  if (i>n) D=id;
  else
  {
    D = (GEN)I[i];
    for (i++; i<=n; i++)
      if (!gegal((GEN)I[i],id)) D = idealmul(nf,D,(GEN)I[i]);
    D = idealpow(nf,D,gdeux);
  }
  p4=gun; p3=auxdecomp(content(d),0);
  for (i=1; i<lg(p3[1]); i++)
    p4 = gmul(p4, gpuigs(gcoeff(p3,i,1), itos(gcoeff(p3,i,2))>>1));
  p4 = gsqr(p4); tetpil=avma;
  i = all? 2: 0;
  p1=cgetg(3 + i,t_VEC);
  if (i) { p1[1]=lcopy((GEN)pseudo[1]); p1[2]=lcopy(I); }
  p1[1+i] = (long)idealmul(nf,D,d);
  p1[2+i] = ldiv(d,p4);
  return gerepile(av,tetpil,p1);
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
  long av=avma,tetpil,j,N,n;
  GEN p1,id,Az,Iz,nf,A,I;

  bnf = checkbnf(bnf);
  if (typ(order)!=t_VEC || lg(order)<3)
    err(talker,"not a pseudo-basis in nfsimplifybasis");
  A=(GEN)order[1]; I=(GEN)order[2]; n=lg(A)-1; nf=(GEN)bnf[7];
  N=lgef(nf[1])-3; id=idmat(N); Iz=cgetg(n+1,t_VEC); Az=cgetg(n+1,t_MAT);
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
  long av,tetpil,i;
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

/* given a pseudo-basis of an order in HNF [A,I] (or [A,I,D,d] it does
 * not matter), gives an nxn matrix (not in HNF) of a pseudo-basis and
 * an ideal vector [id,id,...,id,I] such that order=nf[7]^(n-1)xI.
 * Since it uses the approximation theorem, can be long.
 */
GEN
rnfsteinitz(GEN nf, GEN order)
{
  long av=avma,tetpil,N,j,n;
  GEN id,A,I,p1,p2,a,b;

  nf=checknf(nf);
  N=lgef(nf[1])-3; id=idmat(N);
  if (typ(order)==t_POL) order=rnfpseudobasis(nf,order);
  if (typ(order)!=t_VEC || lg(order)<3)
    err(talker,"not a pseudo-matrix in rnfsteinitz");
  A=gcopy((GEN)order[1]); I=gcopy((GEN)order[2]); n=lg(A)-1;
  for (j=1; j<=n-1; j++)
  {
    a=(GEN)I[j];
    if (!gegal(a,id))
    {
      b=(GEN)I[j+1];
      if (gegal(b,id))
      {
	p1=(GEN)A[j]; A[j]=A[j+1]; A[j+1]=lneg(p1);
	I[j]=(long)b; I[j+1]=(long)a;
      }
      else
      {
	p2=nfidealdet1(nf,a,b);
	p1=gadd(element_mulvec(nf,(GEN)p2[1],(GEN)A[j]),
		element_mulvec(nf,(GEN)p2[2],(GEN)A[j+1]));
	A[j+1]= (long) gadd(element_mulvec(nf,(GEN)p2[3],(GEN)A[j]),
	                    element_mulvec(nf,(GEN)p2[4],(GEN)A[j+1]));
	A[j]=(long)p1;
	I[j]=(long)id; I[j+1]=(long)idealmul(nf,a,b);
	p1=content((GEN)I[j+1]);
	if (!gcmp1(p1))
	{
	  I[j+1] = (long) gdiv((GEN)I[j+1],p1);
	  A[j+1]=lmul(p1,(GEN)A[j+1]);
	}
      }
    }
  }
  tetpil=avma; p1=cgetg(lg(order),t_VEC);
  p1[1]=lcopy(A); p1[2]=lcopy(I);
  for (j=3; j<lg(order); j++) p1[j]=lcopy((GEN)order[j]);
  return gerepile(av,tetpil,p1);
}

/* Given bnf as output by buchinit and either an order as output by
 * rnfpseudobasis or a polynomial, and outputs a basis if it is free,
 * an n+1-generating set if it is not
 */
GEN
rnfbasis(GEN bnf, GEN order)
{
  long av=avma,tetpil,j,N,n;
  GEN nf,A,I,classe,p1,p2,id;

  bnf = checkbnf(bnf);
  nf=(GEN)bnf[7]; N=lgef(nf[1])-3; id=idmat(N);
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
  tetpil = avma; return gerepile(av,tetpil,gcopy(p2));
}

/* Given bnf as output by buchinit and either an order as output by
 * rnfpseudobasis or a polynomial, and outputs a basis (not pseudo)
 * in Hermite Normal Form if it exists, zero if not
 */
GEN
rnfhermitebasis(GEN bnf, GEN order)
{
  long av=avma,tetpil,j,N,n;
  GEN nf,A,I,p1,id;

  bnf = checkbnf(bnf); nf=(GEN)bnf[7];
  N=lgef(nf[1])-3; id=idmat(N);
  if (typ(order)==t_POL)
  {
    order=rnfpseudobasis(nf,order);
    A=(GEN)order[1];
  }
  else
  {
    if (typ(order)!=t_VEC || lg(order)<3)
      err(talker,"not a pseudo-matrix in rnfbasis");
    A=gcopy((GEN)order[1]);
  }
  I=(GEN)order[2]; n=lg(A)-1;
  for (j=1; j<=n; j++)
  {
    if (!gegal((GEN)I[j],id))
    {
      p1=isprincipalgen(bnf,(GEN)I[j]);
      if (gcmp0((GEN)p1[1]))
	A[j]=(long)element_mulvec(nf,(GEN)p1[2],(GEN)A[j]);
      else { avma=av; return gzero; }
    }
  }
  tetpil=avma; return gerepile(av,tetpil,gcopy(A));
}

long
rnfisfree(GEN bnf, GEN order)
{
  long av=avma,n,N,j;
  GEN nf,p1,id,I;

  bnf = checkbnf(bnf);
  if (gcmp1(gmael3(bnf,8,1,1))) return 1;

  nf=(GEN)bnf[7]; N=lgef(nf[1])-3; id=idmat(N);
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

#define nexta(a) (a>0 ? -a : 1-a)

GEN
polcompositum0(GEN pol1, GEN pol2, long flall)
{
  long av=avma,tetpil,i,v,a,l;
  GEN pro1,p1,p2,p3,p4,p5,fa,rk,y;

  if (typ(pol1)!=t_POL || typ(pol2)!=t_POL) err(typeer,"polcompositum0");
  v=varn(pol1);
  if (varn(pol2)!=v) err(talker,"not the same variable in compositum");
  if (lgef(pol1)<=3 || lgef(pol2)<=3)
    err(constpoler,"compositum");
  if (lgef(ggcd(pol1,derivpol(pol1)))>3 || lgef(ggcd(pol2,derivpol(pol2)))>3)
    err(talker,"not a separable polynomial in compositum");

  for (a=1; ; a=nexta(a))
  {
    avma=av;
    if (DEBUGLEVEL>=2)
    {
      fprintferr("trying beta ");
      if (a>0) fprintferr("- "); else fprintferr("+ ");
      if (labs(a)>1) fprintferr("%ld ",labs(a));
      fprintferr("alpha\n"); flusherr();
    }
    pro1 = gadd(polx[MAXVARN],gmulsg(a,polx[v]));
    p1 = gsubst(pol2,v,pro1);
    p2 = subresall(pol1,p1,&rk);
    if (lgef(ggcd(p2,deriv(p2,MAXVARN)))==3)
    {
      p2 = gsubst(p2,MAXVARN,polx[v]);
      fa = factor(p2); fa = (GEN)fa[1];
      if (typ(rk)==t_POL && lgef(rk)==4)
      {
	if (flall)
	{
	  l=lg(fa); y=cgetg(l,t_VEC);
	  for (i=1; i<l; i++)
	  {
	    p3=cgetg(5,t_VEC); p3[1]=fa[i]; y[i]=(long)p3;
	    p4=gmodulcp(polx[v],(GEN)fa[i]);
	    p5=gneg_i(gdiv(gsubst((GEN)rk[2],MAXVARN,p4),
	                   gsubst((GEN)rk[3],MAXVARN,p4)));
	    p3[2]=(long)p5;
            p3[3]=ladd(p4,gmulsg(a,p5));
            p3[4]=lstoi(-a);
	  }
	}
	else y=fa;
	tetpil=avma; return gerepile(av,tetpil,gcopy(y));
      }
    }
  }
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

GEN
rnfequation0(GEN nf, GEN pol2, long flall)
{
  long av=avma,av1,tetpil,v,vpol,a,l1,l2;
  GEN pol1,pro1,p1,p2,p4,p5,rk,y;

  if (typ(nf)==t_POL) pol1=nf; else { nf=checknf(nf); pol1=(GEN)nf[1]; }
  pol2 = fix_relative_pol(nf,pol2);
  v=varn(pol1); vpol=varn(pol2);

  l1=lgef(pol1); l2=lgef(pol2);
  if (l1<=3 || l2<=3) err(constpoler,"rnfequation");

  p2=cgetg(l2,t_POL); p2[1]=pol2[1];
  for (a=2; a<l2; a++)
    p2[a] = (lgef(pol2[a]) < l1)? pol2[a]: lres((GEN)pol2[a],pol1);
  pol2=p2;
  if (lgef(ggcd(pol2,derivpol(pol2)))>3)
    err(talker,"not a separable relative equation in rnfequation");
  pol2=lift_intern(pol2);

  a=0; av1=avma;
  for(;;)
  {
    avma=av1;
    if (DEBUGLEVEL>=2)
    {
      fprintferr("trying beta ");
      if (a)
      {
	if (a>0) fprintferr("- "); else fprintferr("+ ");
	if (labs(a)>1) fprintferr("%ld alpha\n",labs(a));
	else fprintferr("alpha\n");
      }
      flusherr();
    }
    pro1=gadd(polx[MAXVARN],gmulsg(a,polx[v]));
    p1=poleval(pol2,pro1);
    p2=subresall(pol1,p1,&rk);
    if (rk != gzero && lgef(rk)==4 && lgef(ggcd(p2,deriv(p2,MAXVARN)))==3)
    {
      p2=gsubst(p2,MAXVARN,polx[vpol]);
      if (gsigne(leadingcoeff(p2))<0) p2=gneg_i(p2);
      if (flall)
      {
        y=cgetg(4,t_VEC); y[1]=(long)p2;
        p4=gmodulcp(polx[vpol],p2);
        p5=gneg_i(gdiv(gsubst((GEN)rk[2],MAXVARN,p4),
                       gsubst((GEN)rk[3],MAXVARN,p4)));
        y[3]=(long)stoi(-a);
        y[2]=lmul(gmodulcp(polun[vpol],p2),p5);
      }
      else y=p2;
      if (DEBUGLEVEL>=2) fprintferr("ok! leaving rnfequation\n");
      tetpil=avma; return gerepile(av,tetpil,gcopy(y));
    }
    a=nexta(a);
  }
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
  long av=avma,N,tetpil,i;
  GEN m,y;

  m = qf_base_change(gmael(nf,5,3), ideal, 0); /* nf[5][3] = T2 */
  m = lllgramintern(m,4,1,prec);
  if (!m)
  {
    m = lllint(ideal);
    m = qf_base_change(gmael(nf,5,3), gmul(ideal,m), 0);
    m = lllgramintern(m,4,1,prec);
    if (!m) err(talker,"precision too low in rnflllgram");
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
  long av=avma,tetpil,i,j,k,l,kk,kmax,r1,ru,lx,n,vnf;
  GEN p1,p2,M,I,U,ronf,poll,unro,roorder,powreorder,mth,s,MC,MPOL,MCS;
  GEN B,mu,Bf,temp,ideal,x,xc,xpol,muf,mufc,muno,y,z,Ikk_inv;

/* Initializations and verifications */

  nf=checknf(nf);
  if (typ(order)!=t_VEC || lg(order)<3)
    err(talker,"not a pseudo-matrix in rnflllgram");
  M=(GEN)order[1]; I=gcopy((GEN)order[2]); lx=lg(I); n=lg(I)-1;

/* Initialize U to the n x n identity matrix with coefficients in nf in
   the form of polymods */

  U=cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++)
  {
    p1=cgetg(n+1,t_COL); U[j]=(long)p1;
    for (i=1; i<=n; i++) p1[i]=(i==j)?un:zero;
  }

/* Compute the relative T2 matrix of powers of theta */

  vnf=varn(nf[1]); ronf=(GEN)nf[6]; ru=lg(ronf); poll=lift(pol);
  r1=itos(gmael(nf,2,1));
  unro=cgetg(n+1,t_COL); for (i=1; i<=n; i++) unro[i]=un;
  roorder=cgetg(ru,t_VEC);
  for (i=1; i<ru; i++)
    roorder[i]=lroots(gsubst(poll,vnf,(GEN)ronf[i]),prec);
  powreorder=cgetg(n+1,t_MAT);
  p1=cgetg(ru,t_COL); powreorder[1]=(long)p1;
  for (i=1; i<ru; i++) p1[i]=(long)unro;
  for (k=2; k<=n; k++)
  {
    p1=cgetg(ru,t_COL); powreorder[k]=(long)p1;
    for (i=1; i<ru; i++)
    {
      p2=cgetg(n+1,t_COL); p1[i]=(long)p2;
      for (j=1; j<=n; j++)
	p2[j] = lmul(gmael(roorder,i,j),gmael3(powreorder,k-1,i,j));
    }
  }
  mth=cgetg(n+1,t_MAT);
  for (l=1; l<=n; l++)
  {
    p1=cgetg(n+1,t_COL); mth[l]=(long)p1;
    for (k=1; k<=n; k++)
    {
      p2=cgetg(ru,t_COL); p1[k]=(long)p2;
      for (i=1; i<ru; i++)
      {
	s=gzero;
	for (j=1; j<=n; j++)
	  s = gadd(s,gmul(gconj(gmael3(powreorder,k,i,j)),
	                  gmael3(powreorder,l,i,j)));
	p2[i]=(long)s;
      }
    }
  }

/* Transform the matrix M into a matrix with coefficients in K and also
   with coefficients polymod */

  MC=cgetg(lx,t_MAT); MPOL=cgetg(lx,t_MAT);
  for (j=1; j<=n; j++)
  {
    p1=cgetg(lx,t_COL); MC[j]=(long)p1;
    p2=cgetg(lx,t_COL); MPOL[j]=(long)p2;
    for (i=1; i<=n; i++)
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
  while (kk<=n);
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
  long av=avma,tetpil,i,j,k,n,N,vpol,flbnf;
  GEN id,id2,newid,newor,p1,p2,al,newpol,w,z;
  GEN bnf,zk,newideals,ideals,order,neworder;

  if (typ(nf)!=t_VEC) err(idealer1);
  switch(lg(nf))
  {
    case 10: flbnf=0; break;
    case 11: flbnf=1; bnf=nf; nf=checknf((GEN)nf[7]); break;
    default: err(idealer1);
  }
  id=rnfpseudobasis(nf,pol); N=lgef(nf[1])-3;
  if (flbnf && gcmp1(gmael3(bnf,8,1,1))) /* if bnf is principal */
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
  n=lg(newor)-1; w=cgetg(n+1,t_VEC); vpol=varn(pol);
  for (j=1; j<=n; j++)
  {
    p1=(GEN)newid[j]; al=gmul(gcoeff(p1,1,1),(GEN)newor[j]);
    p1=basistoalg(nf,(GEN)al[n]);
    for (i=n-1; i; i--)
      p1=gadd(basistoalg(nf,(GEN)al[i]),gmul(polx[vpol],p1));
    newpol=gtopoly(gmodulcp(gtovec(caract2(lift(pol),lift(p1),vpol)),
                            (GEN) nf[1]), vpol);
    p1 = ggcd(newpol, derivpol(newpol));
    if (degree(p1)>0)
    {
      newpol=gdiv(newpol,p1);
      newpol=gdiv(newpol,leading_term(newpol));
    }
    w[j]=(long)newpol;
    if (DEBUGLEVEL>=4) outerr(newpol);
  }
  tetpil=avma; return gerepile(av,tetpil,gcopy(w));
}

GEN
makebasis(GEN nf,GEN pol)
/* Etant donne un corps de nombres nf et un polynome relatif relpol,
   construit une pseudo-base de l'extension puis calcule une base absolue
   de cette extension pour une racine \theta de relpol. Renvoie le
   polynome irreductible de theta sur Q et la matrice de la base */
{
  GEN elts,ids,polabs,plg,B,bs,p1,colonne,p2,rep,a;
  GEN den,vbs,vbspro,mpro,vpro,rnf;
  long av=avma,tetpil,n,N,m,i,j,k,v1,v2;

  v1=varn((GEN)nf[1]); v2=varn(pol);
  p1=rnfequation2(nf,pol);
  polabs=(GEN)p1[1]; plg=(GEN)p1[2];
  a=(GEN)p1[3];
  rnf=cgetg(12,t_VEC); rnf[1]=(long)pol;
  for (i=2;i<=9;i++) rnf[i]=zero;
  rnf[10]=(long)nf;
  p2=cgetg(4,t_VEC); p2[1] = p2[2] = zero;
  p2[3]=(long)a; rnf[11]=(long)p2;
  if (signe(a))
    pol=gsubst(pol,v2,gsub(polx[v2],
                           gmul(a,gmodulcp(polx[v1],(GEN)nf[1]))));
  p1=rnfpseudobasis(nf,pol);
  if (DEBUGLEVEL>=2) { fprintferr("relative basis computed\n"); flusherr(); }
  elts=(GEN)p1[1];ids=(GEN)p1[2];
  N=lgef(pol)-3;n=lgef((GEN)nf[1])-3;m=n*N;
  den=denom(content(lift(plg)));
  vbs=cgetg(n+1,t_VEC);
  vbs[1]=un;vbs[2]=(long)plg;
  vbspro=gmul(den,plg);
  for(i=3;i<=n;i++)
    vbs[i]=ldiv(gmul((GEN)vbs[i-1],vbspro),den);
  mpro=cgetg(n+1,t_MAT);
  for(j=1;j<=n;j++)
  {
    p2=cgetg(n+1,t_COL);mpro[j]=(long)p2;
    for(i=1;i<=n;i++)
      p2[i]=(long)truecoeff(gmael(nf,7,j),i-1);
  }
  bs=gmul(vbs,mpro); B=idmat(m);
  vpro=cgetg(N+1,t_VEC);
  for (i=1;i<=N;i++)
  {
    p1=cgetg(3,t_POLMOD);
    p1[1]=(long)polabs;
    p1[2]=lpuigs(polx[v2],i-1); vpro[i]=(long)p1;
  }
  vpro=gmul(vpro,elts);
  for(i=1;i<=N;i++)
    for(j=1;j<=n;j++)
    {
      colonne=gmul(bs,element_mul(nf,(GEN)vpro[i],gmael(ids,i,j)));
      p1=gtovec(lift_intern(colonne));
      p2=cgetg(m+1,t_COL);
      for(k=1;k<lg(p1);k++) p2[lg(p1)-k]=p1[k];
      for(   ;k<=m;k++) p2[k]=zero;
      B[(i-1)*n+j]=(long)p2;
    }
  rep=cgetg(4,t_VEC);
  rep[1]=(long)polabs;
  rep[2]=(long)B;
  rep[3]=(long)rnf;
  tetpil=avma;
  return gerepile(av,tetpil,gcopy(rep));
}
