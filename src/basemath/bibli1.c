/********************************************************************/
/**                                                                **/
/**                 LLL Algorithm and close friends                **/
/**                                                                **/
/********************************************************************/
/* $Id$ */
#include "pari.h"
#include "parinf.h"
extern GEN lincomb_integral(GEN u, GEN v, GEN X, GEN Y);

/* scalar product x.x */
GEN
sqscal(GEN x)
{
  long i,av,lx;
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
  long i,av,lx;
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
  long i,av,lx;
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
  long i,av,lx;
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
lllall_trivial(GEN x, long n, long flag)
{
  GEN y;
  if (!n)
  {
    if (flag != lll_ALL) return cgetg(1,t_MAT);
    y=cgetg(3,t_VEC);
    y[1]=lgetg(1,t_MAT);
    y[2]=lgetg(1,t_MAT); return y;
  }
  /* here n = 1 */
  if (gcmp0((GEN)x[1]))
  {
    switch(flag ^ lll_GRAM)
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
lllgramall_finish(GEN h,GEN fl,long flag,long n)
{
  long k;
  GEN y;

  k=1; while (k<=n && !fl[k]) k++;
  switch(flag)
  {
    case lll_KER: setlg(h,k);
      y = gcopy(h); break;

    case lll_IM: h += k-1; h[0] = evaltyp(t_MAT)| evallg(n-k+2);
      y = gcopy(h); break;

    default: setlg(h,k); y=cgetg(3,t_VEC);
      y[1] = lcopy(h);
      h += k-1; h[0] = evaltyp(t_MAT)| evallg(n-k+2);
      y[2] = lcopy(h);
      break;
  }
  return y;
}

/********************************************************************/
/**                                                                **/
/**                          LLL with content                      **/
/**                                                                **/
/********************************************************************/

/* real Gram matrix has coeffs X[i,j] = x[i,j]*veccon[i]*veccon[j] */
static GEN
lllgramintwithcontent(GEN x, GEN veccon, long flag)
{
  long av0=avma,av,tetpil,lx=lg(x),i,j,k,l,n,lim,kmax;
  GEN u,u2,B,lam,q,r,h,la,bb,p1,p2,p3,p4,fl,corr,corr2,newcon;
  GEN *gptr[8];

  if (typ(x) != t_MAT) err(typeer,"lllgramintwithcontent");
  n=lx-1; if (n<=1) return lllall_trivial(x,n,flag);
  if (lg((GEN)x[1])!=lx) err(mattype1,"lllgramintwithcontent");
  fl = new_chunk(lx);

  av=avma; lim=stack_lim(av,1);
  x=dummycopy(x); veccon=dummycopy(veccon);
  B=cgetg(lx+1,t_COL); B[1]=un;
  /* B[i+1]=B_i; le vrai B_i est B_i*prod(1,j=1,i,veccon[j]^2) */

  for (i=1; i<lx; i++) { B[i+1]=zero; fl[i]=0; }
  lam=cgetg(lx,t_MAT);
  for (j=1; j<lx; j++)
  { p2=cgetg(lx,t_COL); lam[j]=(long)p2; for (i=1; i<lx; i++) p2[i]=zero; }
/* le vrai lam[i,j] est
   lam[i,j]*veccon[i]*veccon[j]*prod(1,l=1,j-1,veccon[l]^2) */
  k=2; h=idmat(n); kmax=1;
  u=gcoeff(x,1,1); if (typ(u)!=t_INT) err(lllger4);
  if (signe(u)) { B[2]=(long)u; coeff(lam,1,1)=un; fl[1]=1; }
  else { B[2]=un; fl[1]=0; }
  if (DEBUGLEVEL>5) { fprintferr("k = %ld",k); flusherr(); }
  for(;;)
  {
    if (k>kmax)
    {
      kmax=k;
      for (j=1; j<=k; j++)
      {
	if (j==k || fl[j])
	{
	  u=gcoeff(x,k,j); if (typ(u)!=t_INT) err(lllger4);
	  for (i=1; i<j; i++)
	    if (fl[i])
	      u=divii(subii(mulii((GEN)B[i+1],u),mulii(gcoeff(lam,k,i),gcoeff(lam,j,i))),(GEN)B[i]);
	  if (j<k) coeff(lam,k,j)=(long)u;
	  else
	  {
	    if (signe(u)) { B[k+1]=(long)u; coeff(lam,k,k)=un; fl[k]=1; }
	    else { B[k+1]=B[k]; fl[k]=0; }
	  }
	}
      }
      if (low_stack(lim, stack_lim(av,1)))
      {
	if(DEBUGMEM>1) err(warnmem,"[1]: lllgramintwithcontent");
	gptr[0]=&B; gptr[1]=&lam; gptr[2]=&h;
	gptr[3]=&x; gptr[4]=&veccon; gerepilemany(av,gptr,5);
      }
    }
    u=shifti(mulii(gcoeff(lam,k,k-1),(GEN)veccon[k]),1);
    u2=mulii((GEN)B[k],(GEN)veccon[k-1]);
    if (cmpii(absi(u),u2)>0)
    {
      q=dvmdii(addii(u,u2),shifti(u2,1),&r);
      if (signe(r)<0) q=addsi(-1,q);
      h[k]=lsub((GEN)h[k],gmul(q,(GEN)h[k-1]));
      newcon=mppgcd((GEN)veccon[k],(GEN)veccon[k-1]);
      corr=divii((GEN)veccon[k],newcon); veccon[k]=(long)newcon;
      if(!gcmp1(corr))
      {
	corr2=sqri(corr);
	for (j=1; j<=n; j++)
	  coeff(x,j,k)=coeff(x,k,j)=lmulii(corr,gcoeff(x,k,j));
	coeff(x,k,k)=lmulii(corr,gcoeff(x,k,k));
	for (j=k; j<=kmax; j++) B[j+1]=lmulii(corr2,(GEN)B[j+1]);
	for (i=1; i<k; i++) coeff(lam,k,i)=lmulii(corr,gcoeff(lam,k,i));
	for (i=k+1; i<=kmax; i++)
	{
	  coeff(lam,i,k)=lmulii(corr,gcoeff(lam,i,k));
	  for (j=k+1; j<i; j++)
	    coeff(lam,i,j)=lmulii(corr2,gcoeff(lam,i,j));
	}
      }
      r=negi(mulii(q,divii((GEN)veccon[k-1],(GEN)veccon[k])));
      p1=gcoeff(x,k,k-1);
      for (j=1; j<=n; j++)
	coeff(x,j,k)=coeff(x,k,j)=laddii(gcoeff(x,j,k),mulii(r,(j==k)?p1:gcoeff(x,j,k-1)));
      coeff(x,k,k)=laddii(gcoeff(x,k,k),mulii(r,gcoeff(x,k-1,k)));
      coeff(lam,k,k-1)=laddii(gcoeff(lam,k,k-1),mulii(r,(GEN)B[k]));
      for (i=1; i<k-1; i++)
	coeff(lam,k,i)=laddii(gcoeff(lam,k,i),mulii(r,gcoeff(lam,k-1,i)));
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"[2]: lllgramintwithcontent");
      gptr[0]=&B; gptr[1]=&lam; gptr[2]=&h;
      gptr[3]=&x; gptr[4]=&veccon; gerepilemany(av,gptr,5);
    }
    p3=mulii((GEN)B[k-1],(GEN)B[k+1]);la=gcoeff(lam,k,k-1);p4=mulii(la,la);
    p2=mulsi(100,mulii(mulii((GEN)veccon[k],(GEN)veccon[k]),addii(p3,p4)));
    p1=mulii((GEN)veccon[k-1],(GEN)B[k]);p1=mulsi(99,mulii(p1,p1));
    if (fl[k-1] && (cmpii(p1,p2)>0 || !fl[k]))
    {
      if (DEBUGLEVEL>=4 && k==n)
	{ fprintferr(" (%ld)", expi(p1)-expi(p2)); flusherr(); }
      p1=(GEN)h[k-1]; h[k-1]=h[k]; h[k]=(long)p1;
      p1=(GEN)x[k-1]; x[k-1]=x[k]; x[k]=(long)p1;
      for (j=1; j<=n; j++)
      { p1=gcoeff(x,k-1,j); coeff(x,k-1,j)=coeff(x,k,j); coeff(x,k,j)=(long)p1; }
      p1=(GEN)veccon[k-1]; veccon[k-1]=veccon[k]; veccon[k]=(long)p1;
      for (j=1; j<=k-2; j++)
      { p1=gcoeff(lam,k-1,j); coeff(lam,k-1,j)=coeff(lam,k,j); coeff(lam,k,j)=(long)p1; }
      if (fl[k])
      {
	for (i=k+1; i<=kmax; i++)
	{
	  bb=gcoeff(lam,i,k);
	  coeff(lam,i,k)=ldivii(subii(mulii((GEN)B[k+1],gcoeff(lam,i,k-1)),mulii(la,bb)),(GEN)B[k]);
	  coeff(lam,i,k-1)=ldivii(addii(mulii(la,gcoeff(lam,i,k-1)),mulii((GEN)B[k-1],bb)),(GEN)B[k]);
          if (low_stack(lim, stack_lim(av,1)))
	  {
	    if(DEBUGMEM>1) err(warnmem,"[3]: lllgramintwithcontent");
	    gptr[0]=&B; gptr[1]=&lam; gptr[2]=&h;
	    gptr[3]=&x; gptr[4]=&la; gptr[5]=&veccon; gptr[6]=&p3;
	    gptr[7]=&p4; gerepilemany(av,gptr,8);
	  }
	}
	B[k]=ldivii(addii(p3,p4),(GEN)B[k]);
      }
      else
      {
	if (signe(la))
	{
	  p2=(GEN)B[k]; p1=divii(p4,p2);
	  for (i=k+1; i<=kmax; i++)
	    coeff(lam,i,k-1)=ldivii(mulii(la,gcoeff(lam,i,k-1)),p2);
	  for (j=k+1; j<kmax; j++)
	  {
	    for (i=j+1; i<=kmax; i++)
	      coeff(lam,i,j)=ldivii(mulii(p1,gcoeff(lam,i,j)),p2);
            if (low_stack(lim, stack_lim(av,1)))
	    {
	      if(DEBUGMEM>1) err(warnmem,"[4]: lllgramintwithcontent");
	      gptr[0]=&B; gptr[1]=&lam; gptr[2]=&h;
	      gptr[3]=&x; gptr[4]=&la; gptr[5]=&veccon; gptr[6]=&p1;
	      gptr[7]=&p2; gerepilemany(av,gptr,8);
	    }
	  }
	  B[k+1]=B[k]=(long)p1;
	  for (i=k+2; i<=lx; i++)
	    B[i]=ldivii(mulii(p1,(GEN)B[i]),p2);
	}
	else
	{
	  coeff(lam,k,k-1)=zero;
	  for (i=k+1; i<=kmax; i++)
	  {
	    coeff(lam,i,k)=coeff(lam,i,k-1);
	    coeff(lam,i,k-1)=zero;
	  }
	  B[k]=B[k-1]; fl[k]=1; fl[k-1]=0;
	}

        if (low_stack(lim, stack_lim(av,1)))
	{
	  if(DEBUGMEM>1) err(warnmem,"[5]: lllgramintwithcontent");
	  gptr[0]=&B; gptr[1]=&lam; gptr[2]=&h;
	  gptr[3]=&x; gptr[4]=&veccon;
	  gerepilemany(av,gptr,5);
	}
      }
      if (k>2) k--;
      if (DEBUGLEVEL>5) { fprintferr(" %ld",k); flusherr(); }
    }
    else
    {
      for (l=k-2; l>=1; l--)
      {
	u=shifti(mulii(gcoeff(lam,k,l),(GEN)veccon[k]),1);
	u2=mulii((GEN)B[l+1],(GEN)veccon[l]);
	if (cmpii(absi(u),u2)>0)
	{
	  q=dvmdii(addii(u,u2),shifti(u2,1),&r);
	  if (signe(r)<0) q=addsi(-1,q);
	  h[k]=lsub((GEN)h[k],gmul(q,(GEN)h[l]));
	  newcon=mppgcd((GEN)veccon[k],(GEN)veccon[l]);
	  corr=divii((GEN)veccon[k],newcon); veccon[k]=(long)newcon;
	  if(!gcmp1(corr))
	  {
	    corr2=sqri(corr);
	    for (j=1; j<=n; j++)
	      coeff(x,j,k)=coeff(x,k,j)=lmulii(corr,gcoeff(x,k,j));
	    coeff(x,k,k)=lmulii(corr,gcoeff(x,k,k));
	    for (j=k; j<=kmax; j++) B[j+1]=lmulii(corr2,(GEN)B[j+1]);
	    for (i=1; i<k; i++) coeff(lam,k,i)=lmulii(corr,gcoeff(lam,k,i));
	    for (i=k+1; i<=kmax; i++)
	    {
	      coeff(lam,i,k)=lmulii(corr,gcoeff(lam,i,k));
	      for (j=k+1; j<i; j++)
		coeff(lam,i,j)=lmulii(corr2,gcoeff(lam,i,j));
	    }
	  }
	  r=negi(mulii(q,divii((GEN)veccon[l],(GEN)veccon[k])));
	  p1=gcoeff(x,k,l);
	  for (j=1; j<=n; j++)
	    coeff(x,j,k)=coeff(x,k,j)=laddii(gcoeff(x,j,k),mulii(r,(j==k)?p1:gcoeff(x,j,l)));
	  coeff(x,k,k)=laddii(gcoeff(x,k,k),mulii(r,gcoeff(x,l,k)));
	  coeff(lam,k,l)=laddii(gcoeff(lam,k,l),mulii(r,(GEN)B[l+1]));
	  for (i=1; i<l; i++)
	    coeff(lam,k,i)=laddii(gcoeff(lam,k,i),mulii(r,gcoeff(lam,l,i)));
	}
        if (low_stack(lim, stack_lim(av,1)))
	{
	  if(DEBUGMEM>1) err(warnmem,"[6]: lllgramintwithcontent");
	  gptr[0]=&B; gptr[1]=&lam; gptr[2]=&h;
	  gptr[3]=&x; gptr[4]=&veccon; gerepilemany(av,gptr,5);
	}
      }
      k++; if (DEBUGLEVEL>5) { fprintferr(" %ld",k); flusherr(); }
      if (k>n)
      {
        if (DEBUGLEVEL>5) { fprintferr("\n"); flusherr(); }
	tetpil=avma;
	return gerepile(av0,tetpil,lllgramall_finish(h,fl,flag,n));
      }
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"[7]: lllgramintwithcontent");
      gptr[0]=&B; gptr[1]=&lam; gptr[2]=&h;
      gptr[3]=&x; gptr[4]=&veccon; gerepilemany(av,gptr,5);
    }
  }
}

static GEN
lllintwithcontent(GEN x)
{
  long lx=lg(x),i,j,av,tetpil;
  GEN veccon,con,xred,g;

  if (typ(x) != t_MAT) err(typeer,"lllintwithcontent");
  if (lx==1) return cgetg(1,t_MAT);
  av=avma; veccon=cgetg(lx,t_VEC); g=cgetg(lx,t_MAT); xred=cgetg(lx,t_MAT);
  for (j=1; j<lx; j++)
  {
    g[j]=lgetg(lx,t_COL); con=content((GEN)x[j]);
    xred[j]=ldiv((GEN)x[j],con); veccon[j]=(long)con;
  }
  for (i=1; i<lx; i++)
    for (j=1; j<=i; j++)
      coeff(g,i,j)=coeff(g,j,i)=(long)gscal((GEN)xred[i],(GEN)xred[j]);
  tetpil=avma;
  return gerepile(av,tetpil,lllgramintwithcontent(g,veccon,2));
}

/********************************************************************/
/**                                                                **/
/**                          LLL ALGORITHM                         **/
/**                                                                **/
/********************************************************************/
#define swap(x,y) { long _t=x; x=y; y=_t; }
#define gswap(x,y) { GEN _t=x; x=y; y=_t; }

static void
REDI(GEN x, GEN h, GEN L, GEN B, long K, long k, long l)
{
  long i,lx;
  GEN q = truedvmdii(addii(B,shifti(gcoeff(L,k,l),1)), shifti(B,1), NULL);
  GEN *hk,*hl,xk,xl;
  if (!signe(q)) return;
  q = negi(q); lx = lg(x);
  xl = (GEN)x[l]; hl = (GEN*)h[l];
  xk = (GEN)x[k]; hk = (GEN*)h[k];
  if (is_pm1(q))
  {
    if (signe(q) > 0)
    {
      for (i=1;i<=K;i++) hk[i]=addii(hk[i],hl[i]);
      xk[k] = laddii((GEN)xk[k], (GEN)xl[k]);
      for (i=1;i<lx;i++) coeff(x,k,i)=xk[i]=laddii((GEN)xk[i], (GEN)xl[i]);
      for (i=1;i<l; i++) coeff(L,k,i)=laddii(gcoeff(L,k,i),gcoeff(L,l,i));
      q = B;
    } else {
      for (i=1;i<=K;i++) hk[i]=subii(hk[i],hl[i]);
      xk[k] = lsubii((GEN)xk[k], (GEN)xl[k]);
      for (i=1;i<lx;i++) coeff(x,k,i)=xk[i]=lsubii((GEN)xk[i], (GEN)xl[i]);
      for (i=1;i<l; i++) coeff(L,k,i)=lsubii(gcoeff(L,k,i),gcoeff(L,l,i));
      q = negi(B);
    }
  } else {
    for(i=1;i<=K;i++) hk[i]=addii(hk[i],mulii(q,hl[i]));
    xk[k] = laddii((GEN)xk[k], mulii(q,(GEN)xl[k]));
    for(i=1;i<lx;i++) coeff(x,k,i)=xk[i]=laddii((GEN)xk[i],mulii(q,(GEN)xl[i]));
    for(i=1;i<l;i++)  coeff(L,k,i)=laddii(gcoeff(L,k,i),mulii(q,gcoeff(L,l,i)));
    q = mulii(q,B);
  }
  coeff(L,k,l) = laddii(gcoeff(L,k,l), q);
}

/* b[k] <-- b[k] - round(L[k,l]) b[l], only b[1] ... b[K] modified so far
 * assume l < k and update x = Gram(b), L = Gram Schmidt coeffs. */
static void
RED(GEN x, GEN h, GEN L, long K, long k, long l)
{
  long e,i,lx;
  GEN q = grndtoi(gcoeff(L,k,l),&e);
  GEN *hk,*hl,xk,xl;
  if (DEBUGLEVEL>8)
    fprintferr("error bits when rounding in lllgram: %ld\n",e);
  if (!signe(q)) return;
  q = negi(q); lx = lg(x);
  xl = (GEN)x[l]; hl = (GEN*)h[l];
  xk = (GEN)x[k]; hk = (GEN*)h[k];
  if (is_pm1(q))
  {
    if (signe(q) > 0)
    {
      for (i=1;i<=K;i++) hk[i]=addii(hk[i],hl[i]);
      xk[k] = ladd((GEN)xk[k], (GEN)xl[k]);
      for (i=1;i<lx;i++) coeff(x,k,i)=xk[i]=ladd((GEN)xk[i], (GEN)xl[i]);
      for (i=1;i<l; i++) coeff(L,k,i)=ladd(gcoeff(L,k,i),gcoeff(L,l,i));
    } else {
      for (i=1;i<=K;i++) hk[i]=subii(hk[i],hl[i]);
      xk[k] = lsub((GEN)xk[k], (GEN)xl[k]);
      for (i=1;i<lx;i++) coeff(x,k,i)=xk[i]=lsub((GEN)xk[i], (GEN)xl[i]);
      for (i=1;i<l; i++) coeff(L,k,i)=lsub(gcoeff(L,k,i),gcoeff(L,l,i));
    }
  } else {
    for (i=1;i<=K;i++) hk[i]=addii(hk[i],mulii(q,hl[i]));
    xk[k] = ladd((GEN)xk[k], gmul(q,(GEN)xl[k]));
    for (i=1;i<lx;i++) coeff(x,k,i)=xk[i]=ladd((GEN)xk[i], gmul(q,(GEN)xl[i])); 
    for (i=1;i<l; i++) coeff(L,k,i)=ladd(gcoeff(L,k,i),gmul(q,gcoeff(L,l,i)));
  }
  coeff(L,k,l) = ladd(gcoeff(L,k,l),q);
}

static int
do_SWAPI(GEN x, GEN h, GEN L, GEN B, long kmax, long k, long alpha, GEN fl)
{
  GEN la,la2,p1,p2,Bk;
  long av,i,j,lx;

  if (!fl[k-1]) return 0;
  lx = lg(x); av = avma;
  la = gcoeff(L,k,k-1); la2 = sqri(la);
  p2 = addii(la2, mulii((GEN)B[k-1],(GEN)B[k+1]));
  Bk = (GEN)B[k];
  if (fl[k] && cmpii(mulsi(alpha-1,sqri(Bk)), mulsi(alpha,p2)) <= 0)
    { avma = av; return 0; }

  /* SWAPI(k-1,k) */
  if (DEBUGLEVEL>3 && k==kmax) {
    fprintferr(" (%ld)", expi(mulsi(alpha-1,sqri(Bk)))
                       - expi(mulsi(alpha,p2))); flusherr();
  }
  swap(h[k-1], h[k]);
  swap(x[k-1], x[k]);
  for (j=1; j< lx; j++) swap(coeff(x,k-1,j), coeff(x,k,j));
  for (j=1; j<k-1; j++) swap(coeff(L,k-1,j), coeff(L,k,j))
  if (fl[k])
  {
    av = avma;
    for (i=k+1; i<=kmax; i++)
    {
      GEN t = gcoeff(L,i,k);
      p1 = subii(mulii((GEN)B[k+1],gcoeff(L,i,k-1)), mulii(la,t));
      p1 = divii(p1, Bk);
      av = avma = coeff(L,i,k) = (long)icopy_av(p1,(GEN)av);

      p1 = addii(mulii(la,gcoeff(L,i,k-1)), mulii((GEN)B[k-1],t));
      p1 = divii(p1, Bk);
      av = avma = coeff(L,i,k-1) = (long)icopy_av(p1,(GEN)av);
    }
    B[k] = ldivii(p2,Bk);
  }
  else
  {
    if (signe(la))
    {
      p1 = divii(la2, Bk);
      B[k+1] = B[k] = (long)p1;
      for (i=k+2; i<=lx; i++) B[i] = ldivii(mulii(p1,(GEN)B[i]), Bk);
      for (i=k+1; i<=kmax; i++)
        coeff(L,i,k-1) = ldivii(mulii(la,gcoeff(L,i,k-1)), Bk);
      for (j=k+1; j<kmax; j++)
        for (i=j+1; i<=kmax; i++)
          coeff(L,i,j) = ldivii(mulii(p1,gcoeff(L,i,j)), Bk);
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
  }
  return 1;
}

static int
do_SWAP(GEN x, GEN h, GEN L, GEN B, long kmax, long k, GEN QR)
{
  GEN la,la2, BK,BB,q;
  long av,i,j,lx;

  lx = lg(x); av = avma;
  la = gcoeff(L,k,k-1); la2 = gsqr(la);
  q = gmul((GEN)B[k-1], gsub(QR,la2));
  if (gcmp(q, (GEN)B[k]) <= 0) { avma = av; return 0; }

  /* SWAP(k-1,k) */
  if (DEBUGLEVEL>3 && k==kmax) {
    fprintferr(" (%ld)", gexpo(q) - gexpo((GEN)B[k])); flusherr();
  }
  BB = gadd((GEN)B[k], gmul((GEN)B[k-1],la2));
  if (gcmp0(BB)) { B[k] = 0; return 1; } /* precision pb */

  coeff(L,k,k-1) = ldiv(gmul(la,(GEN)B[k-1]), BB);
  BK = gdiv((GEN)B[k], BB);
  B[k] = lmul((GEN)B[k-1], BK);
  B[k-1] = (long)BB;

  swap(h[k-1],h[k]);
  swap(x[k-1],x[k]);
  for (j=1; j<lx ; j++) swap(coeff(x,k-1,j), coeff(x,k,j));
  for (j=1; j<k-1; j++) swap(coeff(L,k-1,j), coeff(L,k,j))
  for (i=k+1; i<=kmax; i++)
  {
    GEN t = gcoeff(L,i,k);
    coeff(L,i,k) = lsub(gcoeff(L,i,k-1), gmul(la,t));
    coeff(L,i,k-1) = ladd(gmul(gcoeff(L,k,k-1),gcoeff(L,i,k-1)), gmul(BK,t));
   /*              = ladd(t, gmul(gcoeff(L,k,k-1), gcoeff(L,i,k)));
    * would save one multiplication, but loses precision faster... */
  }
  return 1;
}

/* x integer matrix */
GEN
lllgramall(GEN x, long alpha, long flag)
{
  long av0=avma,av,tetpil,lim,lx=lg(x),i,j,k,l,n,s,kmax;
  GEN u,B,L,h,fl, *gptr[4];

  if (typ(x) != t_MAT) err(typeer,"lllgramall");
  n=lx-1; if (n<=1) return lllall_trivial(x,n,flag);
  if (lg((GEN)x[1])!=lx) err(mattype1,"lllgramall");
  fl = cgetg(lx,t_VECSMALL);

  av=avma; lim=stack_lim(av,1); x=dummycopy(x);
  B=gscalcol(gun, lx);
  L=cgetg(lx,t_MAT);
  for (j=1; j<lx; j++)
  {
    for (i=1; i<lx; i++)
      if (typ(gcoeff(x,i,j))!=t_INT) err(lllger4);
    fl[j] = 0; L[j] = (long)zerocol(n);
  }
  k=2; h=idmat(n); kmax=1;
  u=gcoeff(x,1,1); s= signe(u);
  if (s == 0) B[2]=un;
  else
  {
    if (s < 0) err(lllger3);
    B[2]=(long)u; coeff(L,1,1)=un; fl[1]=1;
  }
  if (DEBUGLEVEL>5) fprintferr("k =");
  for(;;)
  {
    if (k > kmax)
    {
      if (DEBUGLEVEL>3) {fprintferr(" K%ld",k);flusherr();}
      kmax = k;
      for (j=1; j<=k; j++)
	if (j==k || fl[j])
	{
          long av1 = avma;
	  u = gcoeff(x,k,j);
	  for (i=1; i<j; i++) if (fl[i])
            u = divii(subii(mulii((GEN)B[i+1],u),
                            mulii(gcoeff(L,k,i),gcoeff(L,j,i))),
                      (GEN)B[i]);
          u = gerepileuptoint(av1, u);
	  if (j<k) coeff(L,k,j)=(long)u;
	  else
	  {
            s = signe(u);
            if (s < 0) err(lllger3);
	    if (s)
              { B[k+1]=(long)u; coeff(L,k,k)=un; fl[k]=1; }
	    else
              { B[k+1]=B[k]; fl[k]=0; }
	  }
	}
    } else if (DEBUGLEVEL>5) {fprintferr(" %ld",k); flusherr();}
    REDI(x,h,L,(GEN)B[k],kmax,k,k-1);
    if (do_SWAPI(x,h,L,B,kmax,k,alpha,fl))
    {
      if (k>2) k--;
    }
    else
    {
      for (l=k-2; l; l--)
      {
        REDI(x,h,L,(GEN)B[l+1],kmax,k,l);
        if (low_stack(lim, stack_lim(av,1)))
        {
          if(DEBUGMEM>1) err(warnmem,"lllgramall[1]");
          gptr[0]=&B; gptr[1]=&L; gptr[2]=&h; gptr[3]=&x;
          gerepilemany(av,gptr,4);
        }
      }
      if (++k > n) break;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"lllgramall[2]");
      gptr[0]=&B; gptr[1]=&L; gptr[2]=&h; gptr[3]=&x;
      gerepilemany(av,gptr,4);
    }
  }
  if (DEBUGLEVEL>3) fprintferr("\n");
  tetpil=avma; return gerepile(av0,tetpil,lllgramall_finish(h,fl,flag,n));
}

static GEN
lllgramall0(GEN x, long flag) { return lllgramall(x,100,flag); }

static int
pslg(GEN x)
{
  long tx;
  if (gcmp0(x)) return 2;
  tx=typ(x); return is_scalar_t(tx)? 3: lgef(x);
}

static GEN
lllgramallgen(GEN x, long flag)
{
  long av0=avma,av,tetpil,lx=lg(x),tu,i,j,k,l,n,lim;
  GEN u,B,lam,q,cq,h,la,bb,p1,p2,p3,p4,fl;
  int ps1,ps2,flc;

  if (typ(x) != t_MAT) err(typeer,"lllgramallgen");
  n=lx-1; if (n<=1) return lllall_trivial(x,n,flag);
  if (lg((GEN)x[1])!=lx) err(mattype1,"lllgramallgen");

  fl = new_chunk(lx);

  av=avma; lim=stack_lim(av,1);
  B=cgetg(lx+1,t_COL);
  B[1]=un; lam=cgetg(lx,t_MAT);
  for (j=1; j<lx; j++) lam[j]=lgetg(lx,t_COL);
  for (i=1; i<lx; i++)
    for (j=1; j<=i; j++)
    {
      if (j<i && !fl[j]) coeff(lam,i,j)=coeff(lam,j,i)=zero;
      else
      {
	u=gcoeff(x,i,j); tu=typ(u);
	if (! is_scalar_t(tu) && tu != t_POL) err(lllger4);
	for (k=1; k<j; k++)
	  if (fl[k])
	    u=gdiv(gsub( gmul((GEN)B[k+1],u),
                         gmul(gcoeff(lam,i,k),gcoeff(lam,j,k)) ),
		   (GEN)B[k]);
	if (j<i) { coeff(lam,i,j)=(long)u; coeff(lam,j,i)=zero; }
	else
	{
	  if (!gcmp0(u)) { B[i+1]=(long)u; coeff(lam,i,i)=un; fl[i]=1; }
	  else { B[i+1]=B[i]; coeff(lam,i,i)=zero; fl[i]=0; }
	}
      }
    }
  k=2; h=idmat(n); flc=0;
  for(;;)
  {
    u=gcoeff(lam,k,k-1);
    if (pslg(u) >= pslg((GEN)B[k]))
    {
      q=gdeuc(u,(GEN)B[k]); cq=gdivsg(1,content(q)); q=gmul(q,cq); flc=1;
      h[k]=lsub(gmul(cq,(GEN)h[k]),gmul(q,(GEN)h[k-1]));
      coeff(lam,k,k-1)=lsub(gmul(cq,gcoeff(lam,k,k-1)),gmul(q,(GEN)B[k]));
      for (i=1; i<k-1; i++)
	coeff(lam,k,i)=lsub(gmul(cq,gcoeff(lam,k,i)),gmul(q,gcoeff(lam,k-1,i)));
    }
    ps1 = pslg(gsqr((GEN)B[k]));
    p3 = gmul((GEN)B[k-1],(GEN)B[k+1]);
    la=gcoeff(lam,k,k-1); p4 = gmul(la,gcoeff(lam,k,k-1));
    ps2=pslg(gadd(p3,p4));
    if (fl[k-1] && (ps1>ps2 || (ps1==ps2 && flc) || !fl[k]))
    {
      flc = (ps1!=ps2);
      swap(h[k-1],h[k]);
      for (j=1; j<=k-2; j++) swap(coeff(lam,k-1,j), coeff(lam,k,j));
      if (fl[k])
      {
	for (i=k+1; i<=n; i++)
	{
	  bb=gcoeff(lam,i,k);
	  coeff(lam,i,k)=ldiv(gsub(gmul((GEN)B[k+1],gcoeff(lam,i,k-1)),gmul(la,bb)),(GEN)B[k]);
	  coeff(lam,i,k-1)=ldiv(gadd(gmul(la,gcoeff(lam,i,k-1)),gmul((GEN)B[k-1],bb)),(GEN)B[k]);
	 }
	B[k]=ldiv(gadd(p3,p4),(GEN)B[k]);
      }
      else
      {
	if (!gcmp0(la))
	{
	  p2=(GEN)B[k]; p1=gdiv(p4,p2);
	  for (i=k+1; i<lx; i++)
	    coeff(lam,i,k-1)=ldiv(gmul(la,gcoeff(lam,i,k-1)),p2);
	  for (j=k+1; j<lx-1; j++)
	    for (i=j+1; i<lx; i++)
	      coeff(lam,i,j)=ldiv(gmul(p1,gcoeff(lam,i,j)),p2);
	  B[k+1]=B[k]=(long)p1;
	  for (i=k+2; i<=lx; i++)
	    B[i]=ldiv(gmul(p1,(GEN)B[i]),p2);
	 }
	else
	{
	  coeff(lam,k,k-1)=zero;
	  for (i=k+1; i<lx; i++)
	  { coeff(lam,i,k)=coeff(lam,i,k-1); coeff(lam,i,k-1)=zero; }
	  B[k]=B[k-1]; fl[k]=1; fl[k-1]=0;
	 }
      }
      if (k>2) k--;
    }
    else
    {
      for (l=k-2; l>=1; l--)
      {
	u=gcoeff(lam,k,l);
	if (pslg(u)>=pslg((GEN)B[l+1]))
	{
	  q=gdeuc(u,(GEN)B[l+1]); cq=gdivsg(1,content(q));
          q=gmul(q,cq); flc=1;
	  h[k]=lsub(gmul(cq,(GEN)h[k]),gmul(q,(GEN)h[l]));
	  coeff(lam,k,l)=lsub(gmul(cq,gcoeff(lam,k,l)),gmul(q,(GEN)B[l+1]));
	  for (i=1; i<l; i++)
            coeff(lam,k,i)=lsub(gmul(cq,gcoeff(lam,k,i)),gmul(q,gcoeff(lam,l,i)));
	}
      }
      if (++k > n) break;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[4];
      if(DEBUGMEM>1) err(warnmem,"lllgramallgen");
      gptr[0]=&B; gptr[1]=&lam; gptr[2]=&h;
      gerepilemany(av,gptr,3);
    }
  }
  tetpil=avma;
  return gerepile(av0,tetpil,lllgramall_finish(h,fl,flag,n));
}

/* compute B[k], update mu(k,1..k-1) */
static int
get_Gram_Schmidt(GEN x, GEN mu, GEN B, long k)
{
  GEN s,A = cgetg(k+1, t_COL); /* scratch space */
  long av,i,j;
  A[1] = coeff(x,k,1);
  for(j=1;j<k;)
  {
    coeff(mu,k,j) = ldiv((GEN)A[j],(GEN)B[j]);
    j++; av = avma;
    /* A[j] <-- x[k,j] - sum_{i<j} mu[j,i] A[i] */
    s = gmul(gcoeff(mu,j,1),(GEN)A[1]);
    for (i=2; i<j; i++) s = gadd(s, gmul(gcoeff(mu,j,i),(GEN)A[i]));
    s = gneg(s); A[j] = lpileupto(av, gadd(gcoeff(x,k,j),s));
  }
  B[k] = A[k]; return (gsigne((GEN)B[k]) > 0);
}

/* x = Gram(b_i). If precision problems return NULL if flag=1, error otherwise.
 * Quality ratio = Q = (alpha-1)/alpha. Suggested value: alpha = 100
 */
GEN
lllgramintern(GEN x, long alpha, long flag, long prec)
{
  GEN xinit,L,h,B,L1,QR;
  long retry = 2, av = avma,lim,l,i,j,k,k1,lx=lg(x),n,kmax,KMAX;
  long last_prec;

  if (typ(x) != t_MAT) err(typeer,"lllgram");
  n=lx-1; if (n && lg((GEN)x[1])!=lx) err(mattype1,"lllgram");
  if (n<=1) return idmat(n);
  xinit = x; lim = stack_lim(av,1);
  for (k=2,j=1; j<lx; j++)
  {
    GEN p1=(GEN)x[j];
    for (i=1; i<=j; i++)
      if (typ(p1[i]) == t_REAL) { l = lg((GEN)p1[i]); if (l>k) k=l; }
  }
  if (k == 2)
  {
    if (!prec) return lllgramint(x);
    x = gmul(x, realun(prec+1));
  }
  else 
  {
    if (prec < k) prec = k;
    x = gprec_w(x, prec+1);
  }
 /* kmax = maximum column index attained during this run 
  * KMAX = same over all runs (after PRECPB) */
  kmax = KMAX = 1;

PRECPB:
  switch(retry--)
  {
    case 2: h = idmat(n); break; /* entry */
    case 1:
      if (kmax > 2)
      { /* some progress but precision loss, try again */
        prec = (prec<<1)-2; kmax = 1;
        if (DEBUGLEVEL > 3) fprintferr("\n");
        if (DEBUGLEVEL) err(warnprec,"lllgramintern",prec);
        x = qf_base_change(gprec_w(xinit,prec),h,1);
        {
          GEN *gsav[2]; gsav[0]=&h; gsav[1]=&x;
          gerepilemany(av, gsav, 2);
        }
        if (DEBUGLEVEL) err(warner,"lllgramintern starting over");
        break;
      } /* fall through */
    case 0: /* give up */
      if (DEBUGLEVEL > 3) fprintferr("\n");
      if (DEBUGLEVEL) err(warner,"lllgramintern giving up");
      if (flag) { avma=av; return NULL; }
      if (DEBUGLEVEL) outerr(xinit);
      err(lllger3);
  }
  last_prec = prec;
  QR = cgetr(prec+1); affsr(alpha-1,QR);
  QR = divrs(QR,alpha);

  L=cgetg(lx,t_MAT);
  B=cgetg(lx,t_COL);
  for (j=1; j<lx; j++) { L[j] = (long)zerocol(n); B[j] = zero; }
  k=2; B[1]=coeff(x,1,1);
  if (gcmp0((GEN)B[1]))
  {
    if (flag) return NULL;
    err(lllger3);
  }
  if (DEBUGLEVEL>5) fprintferr("k =");
  for(;;)
  {
    if (k>kmax)
    {
      kmax = k; if (KMAX < kmax) KMAX = kmax;
      if (DEBUGLEVEL>3) {fprintferr(" K%ld",k);flusherr();}
      if (!get_Gram_Schmidt(x,L,B,k)) goto PRECPB;
    }
    else if (DEBUGLEVEL>5) fprintferr(" %ld",k);
    L1 = gcoeff(L,k,k-1);
    if (typ(L1) == t_REAL &&
        (2*gexpo(L1) > bit_accuracy(lg(L1)) || 2*lg(L1) < last_prec))
    {
      last_prec = lg(L1);
      if (DEBUGLEVEL>3)
	fprintferr("\nRecomputing Gram-Schmidt, kmax = %ld, prec was %ld\n",
                   kmax,last_prec);
      for (k1=1; k1<=kmax; k1++)
        if (!get_Gram_Schmidt(x,L,B,k1)) goto PRECPB;
    }
    RED(x,h,L,KMAX,k,k-1);
    if (do_SWAP(x,h,L,B,kmax,k,QR))
    {
      if (!B[k]) goto PRECPB;
      if (k>2) k--;
    }
    else
    {
      for (l=k-2; l; l--) RED(x,h,L,KMAX,k,l);
      if (++k > n) break;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[5]; gptr[0]=&B; gptr[1]=&L; gptr[2]=&h; gptr[3]=&x; gptr[4]=&QR;
      if(DEBUGMEM>1) 
      {
        if (DEBUGLEVEL > 3) fprintferr("\n");
        err(warnmem,"lllgram");
      }
      gerepilemany(av,gptr,5);
    }
  }
  if (DEBUGLEVEL>3) fprintferr("\n");
  return gerepileupto(av, gcopy(h));
}

static GEN
lllgram_noerr(GEN x,long prec) { return lllgramintern(x,100,1,prec); }

GEN
lllgram(GEN x,long prec) { return lllgramintern(x,100,0,prec); }

GEN
qflll0(GEN x, long flag, long prec)
{
  switch(flag)
  {
    case 0: return lll(x,prec);
    case 1: return lllint(x);
    case 2: return lllintpartial(x);
    case 3: return lllrat(x);
    case 4: return lllkerim(x);
    case 5: return lllkerimgen(x);
    case 7: return lll1(x,prec);
    case 8: return lllgen(x);
    case 9: return lllintwithcontent(x);
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
    case 7: return lllgram1(x,prec);
    case 8: return lllgramgen(x);
    default: err(flagerr,"qflllgram");
  }
  return NULL; /* not reached */
}

/* x est la matrice d'une base b_i; retourne la matrice u (entiere
 * unimodulaire) d'une base LLL-reduite c_i en fonction des b_i (la base
 * reduite est c=b*u).
 */
static GEN
lll_proto(GEN x, GEN f(GEN, long), long prec)
{
  long lx=lg(x),i,j,av,av1;
  GEN g;

  if (typ(x) != t_MAT) err(typeer,"lll_proto");
  if (lx==1) return cgetg(1,t_MAT);
  av=avma; g=cgetg(lx,t_MAT);
  for (j=1; j<lx; j++) g[j]=lgetg(lx,t_COL);
  for (i=1; i<lx; i++)
    for (j=1; j<=i; j++)
      coeff(g,i,j)=coeff(g,j,i)=(long)gscal((GEN)x[i],(GEN)x[j]);
  av1=avma; x = f(g,prec);
  if (!x) { avma=av; return NULL; }
  return gerepile(av,av1,x);
}

GEN
lllintern(GEN x,long flag,long prec)
{
  return lll_proto(x,flag? lllgram_noerr: lllgram,prec);
}

GEN
lll(GEN x,long prec) { return lll_proto(x,lllgram,prec); }

GEN
lll1(GEN x,long prec) { return lll_proto(x,lllgram1,prec); }

GEN
lllrat(GEN x) { return lll_proto(x,lllgram,lll_ALL); }

GEN
lllint(GEN x) { return lll_proto(x,lllgramall0,lll_IM); }

GEN
lllgen(GEN x) { return lll_proto(x,lllgramallgen,lll_IM); }

GEN
lllgramgen(GEN x) { return lllgramallgen(x,lll_IM); }

GEN
lllgramkerimgen(GEN x) { return lllgramallgen(x,lll_ALL); }

static GEN
lllkerim_proto(GEN x, GEN f(GEN,long))
{
  long lx=lg(x), i,j,av,av1;
  GEN g;

  if (typ(x) != t_MAT) err(typeer,"lllkerim_proto");
  if (lx==1)
  {
    g=cgetg(3,t_VEC);
    g[1]=lgetg(1,t_MAT);
    g[2]=lgetg(1,t_MAT); return g;
  }
  if (lg((GEN)x[1])==1)
  {
    g=cgetg(3,t_VEC);
    g[1]=(long)idmat(lx-1);
    g[2]=lgetg(1,t_MAT); return g;
  }
  av=avma; g=cgetg(lx,t_MAT);
  for (j=1; j<lx; j++) g[j]=lgetg(lx,t_COL);
  for (i=1; i<lx; i++)
    for (j=1; j<=i; j++)
      coeff(g,i,j)=coeff(g,j,i)=(long)gscal((GEN)x[i],(GEN)x[j]);
  av1=avma; return gerepile(av,av1,f(g,lll_ALL));
}

GEN
lllkerim(GEN x) { return lllkerim_proto(x,lllgramall0); }

GEN
lllkerimgen(GEN x) { return lllkerim_proto(x,lllgramallgen); }

/* x est ici la matrice de GRAM des bi.  */
GEN
lllgram1(GEN x, long prec)
{
  GEN mu,u,B,BB,BK,p,q,r,cst,unreel,sv,mu1,mu2;
  long av,tetpil,lim,l,i,j,k,lx=lg(x),n,e;

  if (typ(x) != t_MAT) err(typeer,"lllgram1");
  if (lg((GEN)x[1])!=lx) err(mattype1,"lllgram1"); n=lx-1;
  if (n<=1) return idmat(n);
  cst=gdivgs(stoi(99),100); /* LLL proposent 0.75 */
  if (prec)
  {
    unreel = realun(prec+1);
    x = gmul(x,unreel);
    cst = gmul(cst,unreel);
  }
  av=avma; lim=stack_lim(av,1);
  mu=gtrans(sqred(x)); B=cgetg(lx,t_COL);
  for (i=1,l=0; i<=n; i++)
  {
    if (gsigne((GEN)(B[i]=coeff(mu,i,i)))>0) l++;
    coeff(mu,i,i)=un;
  }
  if (l<n) err(lllger3);

  u=idmat(n); k=2;
  do
  {
    if (!gcmp0(r=grndtoi(gcoeff(mu,k,k-1),&e)))
    {
      u[k]=lsub((GEN)u[k],gmul(r,(GEN)u[k-1]));
      for (j=1; j<k-1; j++)
	coeff(mu,k,j)=lsub(gcoeff(mu,k,j),gmul(r,gcoeff(mu,k-1,j)));
      mu1=(GEN)(coeff(mu,k,k-1)=lsub(gcoeff(mu,k,k-1),r));
    }
    else mu1=gcoeff(mu,k,k-1);
    q=gmul((GEN)B[k-1],gsub(cst,mu2=gsqr(mu1)));
    if (gcmp(q,(GEN)B[k])>0)
    {
      BB=gadd((GEN)B[k],gmul((GEN)B[k-1],mu2));
      coeff(mu,k,k-1)=ldiv(gmul(mu1,(GEN)B[k-1]),BB);
      B[k]=lmul((GEN)B[k-1],BK=gdiv((GEN)B[k],BB));
      B[k-1]=(long)BB;
      swap(u[k-1],u[k]);
      for (j=1; j<=k-2; j++) swap(coeff(mu,k-1,j), coeff(mu,k,j));
      for (i=k+1; i<=n; i++)
      {
	p=gcoeff(mu,i,k);
	coeff(mu,i,k)=lsub(gcoeff(mu,i,k-1),gmul(mu1,p));
	coeff(mu,i,k-1)=ladd(gmul(BK,p),gmul(gcoeff(mu,k,k-1),gcoeff(mu,i,k-1)));
      }
      if (k>2) k--;
    }
    else
    {
      for (l=k-2; l; l--)
      {
	if (!gcmp0(r=grndtoi(gcoeff(mu,k,l),&e)))
	{
	  u[k]=lsub((GEN)u[k],gmul(r,(GEN)u[l]));
	  for (j=1; j<l; j++)
	    coeff(mu,k,j)=lsub(gcoeff(mu,k,j),gmul(r,gcoeff(mu,l,j)));
	  coeff(mu,k,l)=lsub(gcoeff(mu,k,l),r);
	 }
      }
      k++;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"lllgram1");
      tetpil=avma;
      sv=cgetg(4,t_VEC);
      sv[1]=lcopy(B); sv[2]=lcopy(u); sv[3]=lcopy(mu);
      sv=gerepile(av,tetpil,sv);
      B=(GEN)sv[1]; u=(GEN)sv[2]; mu=(GEN)sv[3];
    }
  }
  while (k<=n);
  tetpil=avma; return gerepile(av,tetpil,gcopy(u));
}

GEN
lllgramint(GEN x)
{
  return lllgramall0(x,lll_IM);
}

GEN
lllgramkerim(GEN x)
{
  return lllgramall0(x,lll_ALL);
}

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
  const long ltop1 = avma;
  long ncolnz;
  GEN tm1, tm2, mid, *gptr[4];

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
      GEN dot12new,q = gdivround(dot12, dot22);

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
        tm[1] = (long)lincomb_integral(gun,q, (GEN)tm[1],(GEN)tm[2]);
      }

      /* Interchange the output vectors v1 and v2.  */
      gswap(dot11,dot22); swap(tm[1],tm[2]);

      /* Occasionally (including final pass) do garbage collection.  */
      if (npass2 % 8 == 0 || !progress)
      {
        gptr[0] = &dot11; gptr[1] = &dot12;
        gptr[2] = &dot22; gptr[3] = &tm;
        gerepilemany(ltop1, gptr, 4);
      }
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
        mid[icol] = (long)lincomb_integral(
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

        q1neg = gdivround(q1neg, det12);
        q2neg = gdivround(q2neg, det12);
        coeff(tm1, 1, icol) = ladd(gmul(q1neg, gcoeff(tm,1,1)),
				   gmul(q2neg, gcoeff(tm,1,2)));
        coeff(tm1, 2, icol) = ladd(gmul(q1neg, gcoeff(tm,2,1)),
				   gmul(q2neg, gcoeff(tm,2,2)));
        mid[icol] = ladd(curcol,
          lincomb_integral(q1neg,q2neg, (GEN)mid[1],(GEN)mid[2]));
      } /* for icol */
    } /* local block */
  }
  if (DEBUGLEVEL>6)
  {
    fprintferr("tm1 = %Z",tm1);
    fprintferr("mid = %Z",mid);
  }
  gptr[0] = &tm1; gptr[1] = &mid;
  gerepilemany(ltop1, gptr, 2);
  {
   /* For each pair of column vectors v and w in mid * tm2,
    * try to replace (v, w) by (v, v - q*w) for some q.
    * We compute all inner products and check them repeatedly.
    */
    const long ltop3 = avma; /* Excludes region with tm1 and mid */
    long icol, lim, reductions, npass = 0;
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
    lim = stack_lim(ltop3,1);
    for(;;)
    {
      reductions = 0;
      for (icol=1; icol <= ncol; icol++)
      {
	long ijdif, jcol, k1, k2;
	GEN codi, q;

        for (ijdif=1; ijdif < ncol; ijdif++)
	{
          const long previous_avma = avma;

          jcol = (icol + ijdif - 1) % ncol; jcol++; /* Hack for NeXTgcc 2.5.8 */
          k1 = (cmpii(gcoeff(dotprd,icol,icol),
		      gcoeff(dotprd,jcol,jcol) ) > 0)
		? icol : jcol; 	/* index of larger column */
	  k2 = icol + jcol - k1; 	/* index of smaller column */
	  codi = gcoeff(dotprd,k2,k2);
	  q = gcmp0(codi)? gzero: gdivround(gcoeff(dotprd,k1,k2), codi);

	  /* Try to subtract a multiple of column k2 from column k1.  */
	  if (gcmp0(q)) avma = previous_avma;
          else
	  {
	    long dcol;

	    reductions++; q = negi(q);
	    tm2[k1]=(long)
              lincomb_integral(gun,q, (GEN)tm2[k1], (GEN)tm2[k2]);
	    dotprd[k1]=(long)
              lincomb_integral(gun,q, (GEN)dotprd[k1], (GEN)dotprd[k2]);
	    coeff(dotprd, k1, k1) = laddii(gcoeff(dotprd,k1,k1),
				           mulii(q, gcoeff(dotprd,k2,k1)));
	    for (dcol = 1; dcol <= ncol; dcol++)
	      coeff(dotprd,k1,dcol) = coeff(dotprd,dcol,k1);
	  } /* if q != 0 */
        } /* for ijdif */
        if (low_stack(lim, stack_lim(ltop3,1)))
	{
          if(DEBUGMEM>1) err(warnmem,"lllintpartialall");
	  gptr[0] = &dotprd; gptr[1] = &tm2;
	  gerepilemany(ltop3, gptr, 2);
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
/**                   LINEAR & ALGEBRAIC DEPENDANCE                **/
/**                                                                **/
/********************************************************************/

GEN
lindep0(GEN x,long bit,long prec)
{
  if (!bit) return lindep(x,prec);
  if (bit>0) return lindep2(x,bit);
  return deplin(x);
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
  long tx=typ(x),lx=lg(x),ly,i,j,e, av = avma;
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
  p1 = (GEN)gmul(p2,lllint(p2))[1];
  p1[0] = evaltyp(t_VEC) | evallg(lx);
  return gerepileupto(av, gcopy(p1));
}

#define quazero(x) (gcmp0(x) || (typ(x)==t_REAL && expo(x) < EXP))
GEN
lindep(GEN x, long prec)
{
  GEN *b,*be,*bn,**m,qzer;
  GEN c1,c2,c3,px,py,pxy,re,im,p1,p2,r,f,em;
  long i,j,fl,i1, lx = lg(x), tx = typ(x), n = lx-1;
  long av = avma, lim = stack_lim(av,1), av0,av1,tetpil;
  const long EXP = - bit_accuracy(prec) + 2*n;

  if (! is_vec_t(tx)) err(typeer,"lindep");
  if (lx<=2) return cgetg(1,t_VEC);
  x = gmul(x, realun(prec));
  re=greal(x); im=gimag(x);
  /* independant over R ? */
  if (lx == 3 && real_indep(re,im,bit_accuracy(prec)))
    { avma = av; return cgetg(1, t_VEC); }

  qzer = new_chunk(lx);
  b = (GEN*)idmat(n);
  be= (GEN*)new_chunk(lx);
  bn= (GEN*)new_chunk(lx);
  m = (GEN**)new_chunk(lx);
  for (i=1; i<=n; i++)
  {
    bn[i]=cgetr(prec+1);
    be[i]=cgetg(lx,t_COL);
    m[i] = (GEN*)new_chunk(lx);
    for (j=1; j<i ; j++) m[i][j]=cgetr(prec+1);
    for (j=1; j<=n; j++) be[i][j]=lgetr(prec+1);
  }
  px=sqscal(re);
  py=sqscal(im); pxy=gscal(re,im);
  p1=mpsub(mpmul(px,py),gsqr(pxy));
  if (quazero(re)) { re=im; px=py; fl=1; } else fl=quazero(p1);
  av0 = av1 = avma;
  for (i=1; i<=n; i++)
  {
    p2 = gscal(b[i],re);
    if (fl) p2=gmul(gdiv(p2,px),re);
    else
    {
      GEN p5,p6,p7;
      p5=gscal(b[i],im);
      p6=gdiv(gsub(gmul(py,p2),gmul(pxy,p5)),p1);
      p7=gdiv(gsub(gmul(px,p5),gmul(pxy,p2)),p1);
      p2=gadd(gmul(p6,re),gmul(p7,im));
    }
    if (tx!=t_COL) p2=gtrans(p2);
    p2=gsub(b[i],p2);
    for (j=1; j<i; j++)
      if (qzer[j]) affrr(bn[j],m[i][j]);
      else
      {
        gdivz(gscal(b[i],be[j]),bn[j],m[i][j]);
        p2=gsub(p2,gmul(m[i][j],be[j]));
      }
    gaffect(p2,be[i]); affrr(sqscal(be[i]),bn[i]);
    qzer[i]=quazero(bn[i]); avma=av1;
  }
  while (qzer[n])
  {
    long e;
    if (DEBUGLEVEL>9)
    {
      fprintferr("qzer[%ld]=%ld\n",n,qzer[n]);
      for (i1=1; i1<=n; i1++)
	for (i=1; i<i1; i++) output(m[i1][i]);
    }
    em=bn[1]; j=1;
    for (i=2; i<n; i++)
    {
      p1=shiftr(bn[i],i);
      if (cmprr(p1,em)>0) { em=p1; j=i; }
    }
    i=j; i1=i+1;
    avma = av1; r = grndtoi(m[i1][i], &e);
    if (e >= 0) err(talker,"precision too low in lindep");
    r  = negi(r);
    p1 = lincomb_integral(gun,r, b[i1],b[i]);
    av1 = avma;
    b[i1]=b[i]; b[i]=p1; f=addir(r,m[i1][i]);
    for (j=1; j<i; j++)
      if (!qzer[j])
      {
        p1=mpadd(m[i1][j],mulir(r,m[i][j]));
        affrr(m[i][j],m[i1][j]); mpaff(p1,m[i][j]);
      }
    c1=addrr(bn[i1],mulrr(gsqr(f),bn[i]));
    if (!quazero(c1))
    {
      c2=divrr(mulrr(bn[i],f),c1); affrr(c2,m[i1][i]);
      c3=divrr(bn[i1],c1); mulrrz(c3,bn[i],bn[i1]);
      affrr(c1,bn[i]); qzer[i1]=quazero(bn[i1]); qzer[i]=0;
      for (j=i+2; j<=n; j++)
      {
        p1=addrr(mulrr(m[j][i1],c3),mulrr(m[j][i],c2));
        subrrz(m[j][i],mulrr(f,m[j][i1]), m[j][i1]);
        affrr(p1,m[j][i]);
      }
    }
    else
    {
      qzer[i1]=qzer[i]; qzer[i]=1;
      affrr(bn[i],bn[i1]); affrr(c1,bn[i]);
      for (j=i+2; j<=n; j++) affrr(m[j][i],m[j][i1]);
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"lindep");
      b = (GEN*)gerepileupto(av0, gcopy((GEN)b));
      av1 = avma;
    }
  }
  p1=cgetg(lx,t_COL); p1[n]=un; for (i=1; i<n; i++) p1[i]=zero;
  p2 = (GEN)b; p2[0] = evaltyp(t_MAT) | evallg(lx);
  p2=gauss(gtrans(p2),p1); tetpil=avma;
  return gerepile(av,tetpil,gtrans(p2));
}

/* x is a vector of elts of a p-adic field */
GEN
plindep(GEN x)
{
  long av = avma,i,j, prec = VERYBIGINT, lx = lg(x)-1, ly,v;
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
  long tx=typ(x),av,i,k;
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
    p1 = bit? lindep2(p1,bit): lindep(p1,prec);
  if (lg(p1) < 2)
    err(talker,"higher degree than expected in algdep");

  y=cgetg(n+3,t_POL);
  y[1] = evalsigne(1) | evalvarn(0);
  k=1; while (gcmp0((GEN)p1[k])) k++;
  for (i=0; i<=n+1-k; i++) y[i+2] = p1[k+i];
  normalizepol_i(y, n+4-k);
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
    case 2: return kerint2(x);
    default: err(flagerr,"matkerint");
  }
  return NULL; /* not reached */
}

GEN
kerint1(GEN x)
{
  long av=avma,tetpil;
  GEN p1,p2;

  p1=matrixqz3(ker(x)); p2=lllint(p1); tetpil=avma;
  return gerepile(av,tetpil,gmul(p1,p2));
}

GEN
kerint2(GEN x)
{
  long lx=lg(x), i,j,av,av1;
  GEN g,p1;

  if (typ(x) != t_MAT) err(typeer,"kerint2");
  av=avma; g=cgetg(lx,t_MAT);
  for (j=1; j<lx; j++) g[j]=lgetg(lx,t_COL);
  for (i=1; i<lx; i++)
    for (j=1; j<=i; j++)
      coeff(g,i,j) = coeff(g,j,i) = (long)gscal((GEN)x[i],(GEN)x[j]);
  g=lllgramall0(g,lll_KER); p1=lllint(g);
  av1=avma; return gerepile(av,av1,gmul(g,p1));
}

static GEN
lllall0(GEN x, long flag)
{
  long av0=avma,av,tetpil,lx=lg(x),i,j,k,l,n,lim,kmax;
  GEN u,B,L,q,r,h,la,p1,p2,p4,fl;

  if (typ(x) != t_MAT) err(typeer,"lllall0");
  n=lx-1; if (n<=1) return lllall_trivial(x,n, flag | lll_GRAM);
  fl = new_chunk(lx);

  av=avma; lim=stack_lim(av,1); x=dummycopy(x);
  B=gscalcol(gun, lx);
  L=cgetg(lx,t_MAT);
  for (k=lg(x[1]),j=1; j<lx; j++)
  {
    for (i=1; i<k; i++)
      if (typ(gcoeff(x,i,j))!=t_INT) err(lllger4);
    fl[j] = 0; L[j] = (long)zerocol(n);
  }
  k=2; h=idmat(n); kmax=1;
  u=sqscali((GEN)x[1]);
  if (signe(u)) { B[2]=(long)u; coeff(L,1,1)=un; fl[1]=1; } else B[2]=un;
  for(;;)
  {
    if (k > kmax)
    {
      kmax = k;
      for (j=1; j<=k; j++)
      {
	if (j==k || fl[j])
	{
          long av1 = avma;
	  u=gscali((GEN)x[k],(GEN)x[j]);
	  for (i=1; i<j; i++)
	    if (fl[i])
              u = divii(subii(mulii((GEN)B[i+1],u),
                              mulii(gcoeff(L,k,i),gcoeff(L,j,i))),
                        (GEN)B[i]);
          u = gerepileuptoint(av1, u);
	  if (j<k) coeff(L,k,j)=(long)u;
	  else
	  {
	    if (signe(u)) { B[k+1]=(long)u; coeff(L,k,k)=un; fl[k]=1; }
	    else { B[k+1]=B[k]; fl[k]=0; }
	  }
	}
      }
    }
    if (fl[k-1] && !fl[k])
    {
      u = shifti(gcoeff(L,k,k-1),1);
      if (absi_cmp(u, (GEN)B[k]) > 0)
      {
	q = truedvmdii(addii(u,(GEN)B[k]),shifti((GEN)B[k],1), NULL);
        r = negi(q);
        h[k] = (long)lincomb_integral(gun,r, (GEN)h[k],(GEN)h[k-1]);
        x[k] = (long)lincomb_integral(gun,r, (GEN)x[k],(GEN)x[k-1]);
	coeff(L,k,k-1)=laddii(gcoeff(L,k,k-1),mulii(r,(GEN)B[k]));
	for (i=1; i<k-1; i++)
	  coeff(L,k,i)=laddii(gcoeff(L,k,i),mulii(r,gcoeff(L,k-1,i)));
      }
      la=gcoeff(L,k,k-1); p4=sqri(la);
      swap(h[k-1], h[k]);
      swap(x[k-1], x[k]);
      for (j=1; j<k-1; j++) swap(coeff(L,k-1,j), coeff(L,k,j));
      if (signe(la))
      {
	p2=(GEN)B[k]; p1=divii(p4,p2);
	B[k+1]=B[k]=(long)p1;
	for (i=k+1; i<=kmax; i++)
	  coeff(L,i,k-1)=ldivii(mulii(la,gcoeff(L,i,k-1)),p2);
	for (j=k+1; j<kmax; j++)
	  for (i=j+1; i<=kmax; i++)
	    coeff(L,i,j)=ldivii(mulii((GEN)p1,gcoeff(L,i,j)),p2);
	for (i=k+2; i<=kmax+1; i++)
	  B[i]=ldivii(mulii((GEN)p1,(GEN)B[i]),p2);
      }
      else
      {
	for (i=k+1; i<=kmax; i++)
	{ coeff(L,i,k)=coeff(L,i,k-1); coeff(L,i,k-1)=zero; }
	B[k]=B[k-1]; fl[k]=1; fl[k-1]=0;
      }
      if (k>2) k--;
    }
    else
    {
      for (l=k-1; l>=1; l--)
      {
        u = shifti(gcoeff(L,k,l),1);
	if (absi_cmp(u,(GEN)B[l+1]) > 0)
	{
	  q = truedvmdii(addii(u,(GEN)B[l+1]),shifti((GEN)B[l+1],1), NULL);
          r = negi(q);
	  h[k] = (long)lincomb_integral(gun,r,(GEN)h[k],(GEN)h[l]);
	  x[k] = (long)lincomb_integral(gun,r,(GEN)x[k],(GEN)x[l]);
	  coeff(L,k,l)=laddii(gcoeff(L,k,l),mulii(r,(GEN)B[l+1]));
	  for (i=1; i<l; i++)
	    coeff(L,k,i)=laddii(gcoeff(L,k,i),mulii(r,gcoeff(L,l,i)));
	 }
      }
      if (++k > n) break;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      GEN *gptr[4];
      if(DEBUGMEM>1) err(warnmem,"lllall0");
      gptr[0]=&B; gptr[1]=&L; gptr[2]=&h;
      gptr[3]=&x; gerepilemany(av,gptr,4);
    }
  }
  tetpil=avma;
  return gerepile(av0,tetpil,lllgramall_finish(h,fl,flag,n));
}

GEN
kerint(GEN x)
{
  long av=avma,av1;
  GEN g,p1;

  g=lllall0(x,lll_KER); if (lg(g)==1) return g;
  p1=lllint(g); av1=avma;
  return gerepile(av,av1,gmul(g,p1));
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
  long k,i, nv = lg(y), av = avma;
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

extern GEN caractducos(GEN p, GEN x, int v);

static GEN
pols_for_polred(GEN x, GEN base, GEN LLLbase, GEN *pta, 
		int (*check)(GEN, GEN), GEN arg)
{
  long i,j, v = varn(x), n = lg(base);
  GEN p1,p2,p3,y, a = cgetg(n,t_VEC);

  for (i=1; i<n; i++) a[i] = lmul(base,(GEN)LLLbase[i]);
  y=cgetg(n,t_VEC);
  for (i=1; i<n; i++)
  {
    if (DEBUGLEVEL > 2) { fprintferr("i = %ld\n",i); flusherr(); }
    p1=(GEN)a[i]; p3=content(p1);
    if (gcmp1(p3)) p3 = NULL; else p1 = gdiv(p1,p3);
    p1 = caractducos(x,p1,v);
    if (p3)
      for (p2=gun, j=lgef(p1)-2; j>=2; j--)
      {
        p2 = gmul(p2,p3); p1[j] = lmul((GEN)p1[j], p2);
      }
    p2 = modulargcd(derivpol(p1),p1);
    p3 = leading_term(p2); if (!gcmp1(p3)) p2=gdiv(p2,p3);
    p1 = gdiv(p1,p2);
    if (canon_pol(p1) < 0 && pta) a[i] = (long)gneg_i((GEN)a[i]);
    y[i] = (long)p1; if (DEBUGLEVEL > 3) outerr(p1);
    if (check && check(arg, p1)) return p1; 
  }
  if (check) return NULL; /* no suitable polynomial found */
  (void)remove_duplicates(y,a);
  if (pta) *pta = a;
  return y;
}

GEN
nf_get_T2(GEN base, GEN polr)
{
  long i,j, n = lg(base);
  GEN p1,p2=cgetg(n,t_MAT);

  for (i=1; i<n; i++)
  {
    p1=cgetg(n,t_COL); p2[i]=(long)p1;
    for (j=1; j<n; j++)
      p1[j] = (long) poleval((GEN)base[i],(GEN)polr[j]);
  }
  return mulmat_real(gconj(gtrans(p2)),p2);
}

/* compute Tr(w_i w_j) */
static GEN
nf_get_T(GEN x, GEN w)
{
  long i,j,k, n = lgef(x)-3;
  GEN p1,p2,p3;
  GEN ptrace = cgetg(n+2,t_VEC);
  GEN den = cgetg(n+1,t_VEC);
  GEN T = cgetg(n+1,t_MAT);

  ptrace[2]=lstoi(n);
  for (k=2; k<=n; k++)
  { /* cf polsym */
    GEN y = x + (n-k+1);
    p1 = mulsi(k-1,(GEN)y[2]);
    for (i=3; i<=k; i++)
      p1 = addii(p1,mulii((GEN)y[i],(GEN)ptrace[i]));
    ptrace[i] = lnegi(p1);
  }
  w = dummycopy(w);
  for (i=1; i<=n; i++)
  {
    den[i] = (long)denom(content((GEN)w[i]));
    w[i] = lmul((GEN)w[i],(GEN)den[i]);
  }
  
  for (i=1; i<=n; i++)
  {
    p1=cgetg(n+1,t_COL); T[i]=(long)p1;
    for (j=1; j<i ; j++) p1[j] = coeff(T,i,j);
    for (   ; j<=n; j++)
    { /* cf quicktrace */
      p2 = gres(gmul((GEN)w[i],(GEN)w[j]),x);
      p3 = gzero;
      for (k=lgef(p2)-1; k>1; k--)
        p3 = addii(p3, mulii((GEN)p2[k],(GEN)ptrace[k]));
      p1[j]=(long)divii(p3, mulii((GEN)den[i],(GEN)den[j]));
    }
  }
  return T;
}

/* Return the base change matrix giving the an LLL-reduced basis for the
 * maximal order of the nf given by x. Expressed in terms of the standard
 * HNF basis (as polynomials) given in base (ignored if x is an nf)
 */
GEN
LLL_nfbasis(GEN *ptx, GEN polr, GEN base, long prec)
{
  GEN T2,p1, x = *ptx;
  int totally_real,n,i;

  if (typ(x) != t_POL)
  {
    p1=checknf(x); *ptx=x=(GEN)p1[1];
    base=(GEN)p1[7]; n=lgef(x)-3;
    totally_real = !signe(gmael(p1,2,2));
    T2=gmael(p1,5,3); if (totally_real) T2 = ground(T2);
  }
  else
  {
    n=lgef(x)-3; totally_real = (!prec || sturm(x)==n);
    if (typ(base) != t_VEC || lg(base)-1 != n)
      err(talker,"incorrect Zk basis in LLL_nfbasis");
    if (!totally_real)
      T2 = nf_get_T2(base,polr? polr: roots(x,prec));
    else
      T2 = nf_get_T(x, base);
  }
  if (totally_real) return lllgramint(T2);
  for (i=1; ; i++)
  {
    if ((p1 = lllgramintern(T2,100,1,prec))) return p1;
    if (i == MAXITERPOL) err(accurer,"allpolred");
    prec=(prec<<1)-2; 
    if (DEBUGLEVEL) err(warnprec,"allpolred",prec);
    T2=nf_get_T2(base,roots(x,prec));
  }
}

/* x can be a polynomial, but also an nf or a bnf */
/* if check != NULL, return the first polynomial pol
   found such that check(arg, pol) != 0; return NULL
   if there are no such pol */
static GEN
allpolred0(GEN x, GEN *pta, long code, long prec, 
	   int (*check)(GEN,GEN), GEN arg)
{
  GEN y,p1, base = NULL, polr = NULL;
  long av = avma;

  if (typ(x) == t_POL)
  {
    if (!signe(x)) return gcopy(x);
    check_pol_int(x);
    if (!gcmp1(leading_term(x)))
      err(impl,"allpolred for nonmonic polynomials");
    base = allbase4(x,code,&p1,NULL); /* p1 is junk */
  }
  else
  {
    long i = lg(x);
    if (typ(x) == t_VEC && i<=4 && i>=3 && typ(x[1])==t_POL)
    { /* polynomial + integer basis */
      base=(GEN)x[2]; x=(GEN)x[1];
    }
    else
    {
      x = checknf(x);
      base=(GEN)x[7]; x=(GEN)x[1];
    }
  }
  p1 = LLL_nfbasis(&x,polr,base,prec);
  y = pols_for_polred(x,base,p1,pta,check,arg);
  if (check)
  {
    if (y) return gerepileupto(av, y);
    avma = av; return NULL;
  }

  if (pta)
  {
    GEN *gptr[2]; gptr[0]=&y; gptr[1]=pta;
    gerepilemany(av,gptr,2); return y;
  }
  return gerepileupto(av,y);
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
  long n=lgef(x)-3,i,av=avma,v = varn(x);

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

GEN roots_to_pol_r1r2(GEN a, long r1, long v);

/* return T2 norm of the polynomial defining nf */
static GEN 
get_Bnf(GEN nf)
{
  GEN p = gzero, r = (GEN)nf[6];
  long i, r1 = itos(gmael(nf,2,1)), ru = lg(r)-1;
  for (i=ru; i>0; i--)
  {
    if (i == r1) p = gmul2n(p, 1);
    p = gadd(p, gnorm((GEN)r[i]));
  }
  if (i == r1) p = gmul2n(p, 1);
  return p;
}

/* characteristic pol of x */
static GEN
get_polchar(GEN data, GEN x)
{
  GEN basis_embed = (GEN)data[1];
  GEN g = gmul(basis_embed,x);
  return ground(roots_to_pol_r1r2(g, data[0], 0));
}

/* return a defining polynomial for Q(x) */
static GEN
get_polmin(GEN data, GEN x)
{
  GEN g = get_polchar(data,x);
  GEN h = modulargcd(g,derivpol(g));
  if (lgef(h) > 3) g = gdivexact(g,h);
  return g;
}

/* does x generate the correct field ? */
static GEN
chk_gen(GEN data, GEN x)
{
  long av = avma;
  GEN g = get_polchar(data,x);
  if (lgef(modulargcd(g,derivpol(g))) > 3) { avma=av; return NULL; }
  if (DEBUGLEVEL>3) fprintferr("  generator: %Z\n",g);
  return g;
}

/* mat = base change matrix, gram = LLL-reduced T2 matrix */
static GEN
chk_gen_init(FP_chk_fun *chk, GEN nf, GEN gram, GEN mat, long *ptprec)
{
  GEN P,bound,prev,x,B,data, M = gmael(nf,5,1);
  long N = lg(nf[7]), n = N-1,i,prec,prec2;
  int skipfirst = 1; /* [1,0...0] --> x rational */

/* data[0] = r1
 * data[1] = embeddings of LLL-reduced Zk basis
 * data[2] = LLL reduced Zk basis (in M_n(Z)) */
  data = new_chunk(3);
  data[0] = itos(gmael(nf,2,1));
  data[1] = lmul(M, mat);
  data[2] = lmul((GEN)nf[7],mat);
  chk->data = data;

  x = cgetg(N,t_COL);
  bound = get_Bnf(nf); prev = NULL;
  for (i=1; i<N; i++) x[i]=zero;
  for (i=2; i<N; i++)
  {
    x[i] = un;
    P = get_polmin(data,x);
    x[i] = zero;
    if (lgef(P)-3 == n)
    {
      B = gcoeff(gram,i,i);
      if (gcmp(B,bound) < 0) bound = B ;
    }
    else
    {
      if (DEBUGLEVEL>2) fprintferr("chk_gen_init: subfield %Z\n",P);
      if (skipfirst == i-1)
      {
        if (prev && !gegal(prev,P))
        {
          if (degree(prev) * degree(P) > 32) continue; /* too expensive */
          P = (GEN)compositum(prev,P)[1];
          if (lgef(P)-3 == n) continue;
          if (DEBUGLEVEL>2 && lgef(P)>lgef(prev))
            fprintferr("chk_gen_init: subfield %Z\n",P);
        }
        skipfirst++; prev = P;
      }
    }
  }
  /* x_1,...,x_skipfirst generate a strict subfield [unless n=skipfirst=1] */
  chk->skipfirst = skipfirst;
  if (DEBUGLEVEL>2) fprintferr("chk_gen_init: skipfirst = %ld\n",skipfirst);

  /* should be gexpo( [max_k C^n_k (bound/k) ^ k] ^ (1/2) ) */
  prec2 = (1 + (((gexpo(bound)*n)/2) >> TWOPOTBITS_IN_LONG));
  if (prec2 < 0) prec2 = 0;
  prec = 3 + prec2;
  prec2= (long)nfnewprec(nf,-1);
  if (DEBUGLEVEL)
    fprintferr("chk_gen_init: estimated prec = %ld (initially %ld)\n",
                prec, prec2);
  if (prec > prec2) return NULL;
  if (prec < prec2) data[1] = (long)gprec_w((GEN)data[1], prec);
  *ptprec = prec; return bound;
}

static GEN
chk_gen_post(GEN data, GEN res)
{
  GEN basis = (GEN)data[2];
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

  for (i=1; i<c; i++) discs[i] = labsi(discsr((GEN)y[i]));
  v = sindexsort(discs);
  k = v[1]; dmin = (GEN)discs[k]; z = (GEN)y[k]; beta = (GEN)a[k];
  for (i=2; i<c; i++)
  {
    k = v[i];
    if (!egalii((GEN)discs[k],dmin)) break;
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
  long i,nv, av = avma;
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
  prec = (long)nfnewprec(nf,0);

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
  nv = lg(a);
  for (i=1; i<nv; i++)
    if (canon_pol((GEN)y[i]) < 0 && phimax)
      a[i] = (long) gneg_i((GEN)a[i]);
  nv = remove_duplicates(y,a);

  if (DEBUGLEVEL)
    { fprintferr("%ld minimal vectors found.\n",nv-1); flusherr(); }
  if (nv >= 10000) flun &= (~nf_ALL); /* should not happen */
  storepols = (flun & nf_ALL)? storeallpols: findmindisc;

  if (DEBUGLEVEL) fprintferr("\n");
  x = (GEN)nf[1];
  if (nv==1)
  {
    y = cgetg(2,t_VEC); y[1]=(long)x;
    a = cgetg(2,t_VEC); a[1]=(long)polx[varn(x)];
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
  return allpolred(x,(GEN*)0,0,prec);
}

GEN 
polredfirstpol(GEN x, long prec, int (*check)(GEN,GEN), GEN arg)
{
  return allpolred0(x,(GEN*)0,0,prec,check,arg);
}

GEN
smallpolred(GEN x, long prec)
{
  return allpolred(x,(GEN*)0,1,prec);
}

GEN
factoredpolred(GEN x, GEN p, long prec)
{
  return allpolred(x,(GEN*)0,(long)p,prec);
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

extern GEN makebasis(GEN nf,GEN pol);
/* relative polredabs. Returns
 * flag = 0: relative polynomial
 * flag = 1: relative polynomial + element
 * flag = 2: absolute polynomial */
GEN
rnfpolredabs(GEN nf, GEN relpol, long flag, long prec)
{
  GEN p1,bpol,rnf,elt,pol;
  long va, av = avma;

  if (typ(relpol)!=t_POL) err(typeer,"rnfpolredabs");
  nf=checknf(nf); va = varn(relpol);
  if (DEBUGLEVEL>1) timer2();
  p1 = makebasis(nf, unifpol(nf,relpol,1));
  rnf = (GEN)p1[3];
  if (DEBUGLEVEL>1) 
  {
    msgtimer("absolute basis");
    fprintferr("original absolute generator: %Z\n",p1[1]);
  }
  p1 = polredabs0(p1, nf_RAW | nf_NORED, prec);
  bpol = (GEN)p1[1];
  if (DEBUGLEVEL>1) fprintferr("reduced absolute generator: %Z\n",bpol);
  if (flag==2) return gerepileupto(av,bpol);

  elt = rnfelementabstorel(rnf,(GEN)p1[2]);
  p1=cgetg(3,t_VEC);
  pol = rnfcharpoly(nf,relpol,elt,va);
  if (!flag) p1 = pol;
  else
  {
    p1[1]=(long)pol;
    p1[2]=(long)polymodrecip(elt);
  }
  return gerepileupto(av,p1);
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
  long c = lg(x), l = lg(x[1]), av,i,j;
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
  long c = lg(x), l = lg(x[1]), av,i,j;
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
  s = avma % sizeof(double); avma -= s;
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
  GEN x,res,p1,u,r,liste,gnorme,gnorme_max,invp,V, *gptr[2];
  long n = lg(a), av0 = avma, av1,av,tetpil,lim, i,j,k,s,maxrank;
  double p,BOUND,*v,*y,*z,**q, eps = 0.000001;

  maxrank = 0; res = V = invp = NULL; /* gcc -Wall */
  switch(flag)
  {
    case min_FIRST: res = cgetg(3,t_VEC); break;
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
    gnorme_max = NULL;
  }
  else
  {
    BORNE = gfloor(BORNE);
    BOUND = gtodouble(BORNE)+eps;
    gnorme_max = gzero;
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
    p = x[1]+z[1]; gnorme = ground( dbltor(y[1] + p*p*v[1]) );
    if (gnorme_max)
      { if (gcmp(gnorme,gnorme_max) > 0) gnorme_max=gnorme; }
    else if (gcmp(gnorme,BORNE) < 0)
    {
      BOUND=gtodouble(gnorme)+eps; s=0;
      affii(gnorme,BORNE); avma=av1;
      if (flag == min_PERF) invp = idmat(maxrank);
    }

    switch(flag)
    {
      case min_ALL:
        s++;
        if (s<=maxrank)
        {
          p1 = new_chunk(n+1); liste[s] = (long) p1;
          for (i=1; i<=n; i++) p1[i] = x[i];
        }
        break;

      case min_FIRST:
        if (! gnorme_max || gcmp(gnorme,BORNE)>0) break;

        tetpil=avma; gnorme = icopy(gnorme); r = gmul_mat_smallvec(r,x);
        gptr[0]=&gnorme; gptr[1]=&r; gerepilemanysp(av,tetpil,gptr,2);
        res[1]=(long)gnorme;
        res[2]=(long)r; return res;

      case min_PERF:
      {
        long av2=avma, I=1;

        for (i=1; i<=n; i++)
          for (j=i; j<=n; j++,I++) V[I] = x[i]*x[j];
        if (! addcolumntomatrix(V,invp,liste))
        {
          if (DEBUGLEVEL>1) { fprintferr("."); flusherr(); }
          avma=av2; continue;
        }

        if (DEBUGLEVEL>1) { fprintferr("*"); flusherr(); }
        if (++s == maxrank)
        {
          if (DEBUGLEVEL>1) { fprintferr("\n"); flusherr(); }
          avma=av0; return stoi(s);
        }

        if (low_stack(lim, stack_lim(av1,1)))
        {
          if(DEBUGMEM>1) err(warnmem,"minim00");
          if (DEBUGLEVEL>1)
          { 	
            fprintferr("\ngerepile in qfperfection. rank>=%ld\n",s);
            flusherr();
          }
          tetpil=avma; invp = gerepile(av1,tetpil,gcopy(invp));
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
    p1[j] = (long) gmul_mat_smallvec(u,(GEN)liste[j]);
  liste = p1;
  r = gnorme_max? gnorme_max: BORNE;

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
  long av,av1,lim,N,n,i,j,k,s,epsbit,prec,checkcnt = 0;
  GEN u,S,x,y,z,v,q,norme1,normax1,borne1,borne2,eps,p1,alpha,norms,dummy;
  GEN (*check)(GEN,GEN) = CHECK? CHECK->f: NULL;
  GEN data = CHECK? CHECK->data: NULL;
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
	GEN *gptr[7];
        int cnt = 4;
	if(DEBUGMEM>1) err(warnmem,"smallvectors");
	gptr[0]=&x; gptr[1]=&y; gptr[2]=&z; gptr[3]=&normax1;
	if (stockmax)
        { /* initialize to dummy values */
          GEN T = S;
          for (i=s+1; i<=stockmax; i++) S[i]=(long)dummy;
          S = gclone(S); if (isclone(T)) gunclone(T);
        }
        if (check)
        {
          cnt+=3; gptr[4]=&borne1; gptr[5]=&borne2; gptr[6]=&norms;
          for (i=s+1; i<=stockmax; i++) norms[i]=(long)dummy;
        }
	gerepilemany(av,gptr,cnt);
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
        long av1 = avma;
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
  VOLATILE long pr,av=avma,i,j,n;
  VOLATILE GEN B,nf,r,rinvtrans,v,v1,u,s,res,z,vnorm,sperm,perm,uperm,gram;
  VOLATILE GEN bound = B0;
  void *catcherr = NULL;
  long prec = PREC;

  if (DEBUGLEVEL>2) { fprintferr("entering fincke_pohst\n"); flusherr(); }
  if (typ(a) == t_VEC) { nf = checknf(a); a = gmael(nf,5,3); } else nf = NULL;
  pr = gprecision(a);
  if (pr) prec = pr; else a = gmul(a,realun(prec));
  if (DEBUGLEVEL>2) fprintferr("first LLL: prec = %ld\n", prec);
  if (nf && !signe(gmael(nf,2,2))) /* totally real */
  {
    GEN T = nf_get_T((GEN)nf[1], (GEN)nf[7]);
    v1 = lllgramint(T);
    prec += 2 * ((gexpo(v1) + gexpo((GEN)nf[1])) >> TWOPOTBITS_IN_LONG);
    nf = nfnewprec(nf, prec);
    r = qf_base_change(T,v1,1);
    i = PREC + (gexpo(r) >> TWOPOTBITS_IN_LONG);
    if (i < prec) prec = i;
    r = gmul(r, realun(prec));
  }
  else
  {
    v1 = lllgramintern(a,4,flag&1, (prec<<1)-2);
    if (!v1) goto PRECPB;
    r = qf_base_change(a,v1,1);
  }
  r = sqred1intern(r,flag&1);
  if (!r) goto PRECPB;

  n = lg(a);
  if (n == 1)
  {
    if (CHECK) err(talker, "dimension 0 in fincke_pohst");
    avma = av; z=cgetg(4,t_VEC);
    z[1]=z[2]=zero;
    z[3]=lgetg(1,t_MAT); return z;
  }
  for (i=1; i<n; i++)
  {
    GEN p1 = gsqrt(gcoeff(r,i,i), prec);
    coeff(r,i,i)=(long)p1;
    for (j=i+1; j<n; j++)
      coeff(r,i,j) = lmul(p1, gcoeff(r,i,j));
  }
  /* now r~ * r = a in LLL basis */
  rinvtrans = gtrans(invmat(r));
  if (DEBUGLEVEL>2)
    fprintferr("final LLL: prec = %ld, precision(rinvtrans) = %ld\n",
                prec,gprecision(rinvtrans));
  v = lllintern(rinvtrans,flag&1, (gprecision(rinvtrans)<<1)-2);
  if (!v) goto PRECPB;
  rinvtrans = gmul(rinvtrans,v);

  u = invmat(gtrans(v)); s = gmul(r,u);
  u = gmul(v1, u);
  vnorm=cgetg(n,t_VEC);
  for (j=1; j<n; j++) vnorm[j] = lnorml2((GEN)rinvtrans[j]);
  perm = sindexsort(vnorm);
  sperm = cgetg(n,t_MAT);
  uperm = cgetg(n,t_MAT);
  for (i=1; i<n; i++) { uperm[n-i] = u[perm[i]]; sperm[n-i] = s[perm[i]]; }

  gram = gram_matrix(sperm);
  B = gcoeff(gram,n-1,n-1);
  if (gexpo(B) >= bit_accuracy(lg(B)-2)) goto PRECPB;

  { /* catch precision problems (truncation error) */
    jmp_buf env;
    if (setjmp(env)) goto PRECPB;
    catcherr = err_catch(truer2, env, NULL);
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
