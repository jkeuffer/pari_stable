/*******************************************************************/
/*                                                                 */
/*                ROOTS OF COMPLEX POLYNOMIALS                     */
/*                (written by Xavier Gourdon)                      */
/*                                                                 */
/*******************************************************************/
/* $Id$ */
#include "pari.h"

GEN polrecip_i(GEN x);
#define pariINFINITY 100000
#define NEWTON_MAX 10

static GEN gunr, globalu;
static long KARASQUARE_LIMIT, COOK_SQUARE_LIMIT, Lmax, step4;
static GEN *radius;

/********************************************************************/
/**                                                                **/
/**                      ARITHMETIQUE RAPIDE                       **/
/**                                                                **/
/********************************************************************/

/* fast product of x,y which must be integer or complex of integer */
static GEN
quickmulcc(GEN x, GEN y)
{
  long tx=typ(x),ty=typ(y);
  GEN z;

  if (tx==t_INT)
  {
    if (ty==t_INT) return mulii(x,y);
    if (ty==t_COMPLEX)
    {
      z=cgetg(3,t_COMPLEX);
      z[1]=(long) mulii(x,(GEN) y[1]);
      z[2]=(long) mulii(x,(GEN) y[2]);
      return z;
    }
  }

  if (tx==t_COMPLEX)
  {
    if (ty==t_INT)
    {
      z=cgetg(3,t_COMPLEX);
      z[1]=(long) mulii((GEN)x[1],y);
      z[2]=(long) mulii((GEN)x[2],y);
      return z;
    }
    if (ty==t_COMPLEX)
    {
      long av,tetpil;
      GEN p1,p2;

      z=cgetg(3,t_COMPLEX); av=avma;
      p1=mulii((GEN)x[1],(GEN)y[1]); p2=mulii((GEN)x[2],(GEN)y[2]);
      x=addii((GEN)x[1],(GEN)x[2]); y=addii((GEN)y[1],(GEN)y[2]);
      y=mulii(x,y); x=addii(p1,p2);
      tetpil=avma; z[1]=lsubii(p1,p2); z[2]=lsubii(y,x);
      gerepilemanyvec(av,tetpil,z+1,2);
      return z;
    }
  }
  err(talker,"bug in quickmulcc");
  return NULL; /* not reached */
}

static void
set_karasquare_limit(long bitprec)
{
  if (bitprec<600) { KARASQUARE_LIMIT=8; COOK_SQUARE_LIMIT=400; return; }
  if (bitprec<2000) { KARASQUARE_LIMIT=4; COOK_SQUARE_LIMIT=200; return; }
  if (bitprec<3000) { KARASQUARE_LIMIT=4; COOK_SQUARE_LIMIT=125; return; }
  if (bitprec<5000) { KARASQUARE_LIMIT=2; COOK_SQUARE_LIMIT=75; return; }
  KARASQUARE_LIMIT=1; COOK_SQUARE_LIMIT=50;
}

/* the pari library does not have specific procedure for the square of
polynomials. This one is twice faster than gmul */
static GEN
mysquare(GEN p)
{
  GEN s,aux1,aux2;
  long i,j,n=lgef(p)-3,nn,ltop,lbot;

  if (n==-1) return gcopy(p);
  nn=n<<1; s=cgetg(nn+3,t_POL);
  s[1] = evalsigne(1) | evalvarn(varn(p)) | evallgef(nn+3);
  for (i=0; i<=n; i++)
  {
    aux1=gzero; ltop=avma;
    for (j=0; j<(i+1)>>1; j++)
    {
      aux2=quickmulcc((GEN) p[j+2],(GEN)p[i-j+2]);
      aux1=gadd(aux1,aux2);
    }
    if (i%2==1) { lbot=avma; s[i+2]=lpile(ltop,lbot,gshift(aux1,1)); }
    else
    {
      aux1=gshift(aux1,1);
      aux2=quickmulcc((GEN)p[2+(i>>1)],(GEN)p[2+(i>>1)]);
      lbot=avma; s[i+2]=lpile(ltop,lbot,gadd(aux1,aux2));
    }
  }
  for (i=n+1; i<=nn; i++)
  {
    aux1=gzero; ltop=avma;
    for (j=i-n; j<(i+1)>>1; j++)
    {
      aux2=quickmulcc((GEN)p[j+2],(GEN)p[i-j+2]);
      aux1=gadd(aux1,aux2);
    }
    if (i%2==1) { lbot=avma; s[i+2]=lpile(ltop,lbot,gshift(aux1,1)); }
    else
    {
      aux1=gshift(aux1,1);
      aux2=quickmulcc((GEN)p[2+(i>>1)],(GEN)p[2+(i>>1)]);
      lbot=avma; s[i+2]=lpile(ltop,lbot,gadd(aux1,aux2));
    }
  }
  return s;
}

static GEN
karasquare(GEN p)
{
  GEN p1,s0,s1,s2,aux;
  long n=lgef(p)-3,n0,n1,i,var,nn0,ltop,lbot;

  if (n<=KARASQUARE_LIMIT) return mysquare(p);
  ltop=avma;
  var=evalsigne(1)+evalvarn(varn(p)); n0=n>>1; n1=n-n0-1;
  setlgef(p,n0+3); /* hack to have the first half of p */
  s0=karasquare(p);
  p1=cgetg(n1+3,t_POL); p1[1]=var+evallgef(n1+3);
  for (i=2; i<=n1+2; i++) p1[i]=p[1+i+n0];
  s2=karasquare(p1);
  s1=karasquare(gadd(p,p1));
  s1=gsub(s1,gadd(s0,s2));
  nn0=n0<<1;
  aux=cgetg((n<<1)+3,t_POL); aux[1]=var+evallgef(2*n+3);
  var=lgef(s0);
  for (i=2; i<var; i++) aux[i]=s0[i];
  for (   ; i<=nn0+2; i++) aux[i]=zero;
  var=lgef(s2);
  for (i=2; i<var; i++) aux[2+i+nn0]=s2[i];
  for (i=var-2; i<=(n1<<1); i++) aux[4+i+nn0]=zero;
  aux[3+nn0]=zero;
  for (i=3; i<=lgef(s1); i++)
    aux[i+n0]=ladd((GEN) aux[i+n0],(GEN) s1[i-1]);
  setlgef(p,n+3); /* recover all the polynomial p */
  lbot=avma; return gerepile(ltop,lbot,gcopy(aux));
}

static GEN
cook_square(GEN p)
{
  GEN p0,p1,p2,p3,q,aux0,aux1,r,aux,plus,moins;
  long n=lgef(p)-3,n0,n3,i,j,ltop=avma,lbot,var;

  if (n<=COOK_SQUARE_LIMIT) return karasquare(p);

  n0=(n+1)/4; n3=n+1-3*n0;
  p0=cgetg(n0+2,t_POL); p1=cgetg(n0+2,t_POL); p2=cgetg(n0+2,t_POL);
  p3=cgetg(n3+2,t_POL);
  var=evalsigne(1)|evalvarn(varn(p));
  p0[1]=p1[1]=p2[1]=var|evallgef(n0+2); p3[1]=var|evallgef(n3+2);

  for (i=0; i<n0; i++)
  {
    p0[i+2]=p[i+2]; p1[i+2]=p[i+n0+2]; p2[i+2]=p[i+2*n0+2];
  }
  for (i=0; i<n3; i++) p3[i+2]=p[i+3*n0+2];

  q=cgetg(8,t_VEC); q=q+4;

  q[0]=(long) p0;
  aux0=gadd(p0,p2); aux1=gadd(p1,p3);
  q[-1]=lsub(aux0,aux1); q[1]=ladd(aux0,aux1);
  aux0=gadd(p0,gmulgs(p2,4)); aux1=gmulgs(gadd(p1,gmulgs(p3,4)),2);
  q[-2]=lsub(aux0,aux1); q[2]=ladd(aux0,aux1);
  aux0=gadd(p0,gmulgs(p2,9)); aux1=gmulgs(gadd(p1,gmulgs(p3,9)),3);
  q[-3]=lsub(aux0,aux1); q[3]=ladd(aux0,aux1);
  for (i=-3; i<=3; i++) q[i]=(long) cook_square((GEN)q[i]);
  r=new_chunk(7);
  plus=cgetg(4,t_VEC); moins=cgetg(4,t_VEC);
  for (i=1; i<=3; i++)
  {
    plus[i]=ladd((GEN)q[-i],(GEN)q[i]);
    moins[i]=lsub((GEN)q[-i],(GEN)q[i]);
  }
  r[0]=q[0];
  r[1]=ldivgs(
	      gsub(
		   gsub(gmulgs((GEN)moins[2],9),(GEN)moins[3]),
		   gmulgs((GEN)moins[1],45)),
	      60);
  r[2]=ldivgs(
	      gadd(
		   gadd(gmulgs((GEN)plus[1],270),gmulgs((GEN)q[0],-490)),
		   gadd(gmulgs((GEN)plus[2],-27),gmulgs((GEN)plus[3],2))),
	      360);
  r[3]=ldivgs(
	      gadd(
		   gadd(gmulgs((GEN)moins[1],13),gmulgs((GEN)moins[2],-8)),
		   (GEN)moins[3]),
	      48);
  r[4]=ldivgs(
	      gadd(
		   gadd(gmulgs((GEN)q[0],56),gmulgs((GEN)plus[1],-39)),
		   gsub(gmulgs((GEN)plus[2],12),(GEN)plus[3])),
	      144);
  r[5]=ldivgs(
	      gsub(
		   gadd(gmulgs((GEN)moins[1],-5),gmulgs((GEN)moins[2],4)),
		   (GEN)moins[3]),
	      240);
  r[6]=ldivgs(
	      gadd(
		   gadd(gmulgs((GEN)q[0],-20),gmulgs((GEN)plus[1],15)),
		   gadd(gmulgs((GEN)plus[2],-6),(GEN)plus[3])),
	      720);
  q=cgetg(2*n+3,t_POL); q[1]=var|evallgef(2*n+3);
  for (i=0; i<=2*n; i++) q[i+2]=zero;
  for (i=0; i<=6; i++)
  {
    aux=(GEN) r[i];
    for (j=0; j<=lgef(aux)-3; j++)
      q[n0*i+j+2]=ladd((GEN)q[n0*i+j+2],(GEN)aux[j+2]);
  }
  lbot=avma; return gerepile(ltop,lbot,gcopy(q));
}

static GEN
graeffe(GEN p)
{
  GEN p0,p1,s0,s1,ss1;
  long n=lgef(p)-3,n0,n1,i,auxi,ns1;

  if (n==0) return gcopy(p);
  n0=n>>1; n1=(n-1)>>1;
  auxi=evalsigne(1)|evalvarn(varn(p));
  p0=cgetg(n0+3,t_POL); p0[1]=auxi|evallgef(n0+3);
  p1=cgetg(n1+3,t_POL); p1[1]=auxi|evallgef(n1+3);
  for (i=0; i<=n0; i++) p0[i+2]=p[2+(i<<1)];
  for (i=0; i<=n1; i++) p1[i+2]=p[3+(i<<1)];

  s0=cook_square(p0);
  s1=cook_square(p1); ns1 = lgef(s1)-3;
  ss1 = cgetg(ns1+4, t_POL);
  ss1[1] = auxi | evallgef(ns1+4);
  ss1[2]=zero;
  for (i=0; i<=ns1; i++) ss1[3+i]=lneg((GEN)s1[2+i]);
  /* now ss1 contains -x * s1 */
  return gadd(s0,ss1);
}

/********************************************************************/
/**                                                                **/
/**        FACTORISATION SQUAREFREE AVEC LE GCD MODULAIRE          **/
/**                                                                **/
/********************************************************************/

/* return a n x 2 matrix:
 *   col 1 contains the i's such that A_i non constant
 *   col 2 the A_i's, s.t. pol = A_i1^i1.A_i2^i2...A_in^in.
 * if pol is constant return [;]
 */
GEN
square_free_factorization(GEN pol)
{
  long deg,i,j,m;
  GEN p1,x,t1,v1,t,v,A;

  if (typ(pol)!=t_POL) err(typeer,"square_free_factorization");
  deg=lgef(pol)-3; if (deg<1) return cgetg(1,t_MAT);
  p1 = content(pol); if (!gcmp1(p1)) pol = gdiv(pol,p1);

  x=cgetg(3,t_MAT);
  if (deg > 1)
  {
    t1 = modulargcd(pol,derivpol(pol));
    if (isscalar(t1)) deg = 1;
  }
  if (deg==1)
  {
    x[1]=lgetg(2,t_COL); p1=(GEN)x[1]; p1[1]=un;
    x[2]=lgetg(2,t_COL); p1=(GEN)x[2]; p1[1]=(long)pol; return x;
  }
  A=new_chunk(deg+1); v1=gdivexact(pol,t1); v=v1; i=0;
  while (lgef(v)>3)
  {
    v=modulargcd(t1,v1); i++;
    A[i]=(long)gdivexact(v1,v);
    t=gdivexact(t1,v); v1=v; t1=t;
  }
  m=1; x[1]=lgetg(deg+1,t_COL); x[2]=lgetg(deg+1,t_COL);
  for (j=1; j<=i; j++)
    if (isnonscalar(A[j]))
    {
      p1=(GEN)x[1]; p1[m] = lstoi(j);
      p1=(GEN)x[2]; p1[m] = A[j];
      m++;
    }
  setlg(x[1],m); setlg(x[2],m); return x;
}

/********************************************************************/
/**                                                                **/
/**                 CALCUL DU MODULE DES RACINES                   **/
/**                                                                **/
/********************************************************************/

static double
log2ir(GEN x)
{
  double l;

  if (signe(x)==0) return (double) -pariINFINITY;
  if (typ(x)==t_INT)
  {
    if (lgefint(x)==3) return (double) log2( (double)(ulong) x[2]);
    l=(double)(ulong) x[2]+
	(double)(ulong) x[3] / exp2((double) BITS_IN_LONG);
    return log2(l)+ (double) BITS_IN_LONG * (lgefint(x)-3.);
  }
  /* else x is real */
  return 1.+ (double) expo(x)+log2( (double)(ulong) x[2]) - (double) BITS_IN_LONG;
}

static double
mylog2(GEN z)
{
  double x,y;

  if (typ(z)!=t_COMPLEX) return log2ir(z);

  x = log2ir((GEN) z[1]);
  y = log2ir((GEN) z[2]);
  if (fabs(x-y)>10) return (x>y)? x: y;
  return x+0.5*log2( 1 + exp2(2*(y-x)));
}

static long
findpower(GEN p)
{
  double x, logbinomial,pente,pentemax=-pariINFINITY;
  long n=lgef(p)-3,i;

  logbinomial = mylog2((GEN) p[n+2]);
  for (i=n-1; i>=0; i--)
  {
    logbinomial += log2((double) (i+1) / (double) (n-i));
    x = mylog2((GEN) p[2+i])-logbinomial;
    if (x>-pariINFINITY)
    {
      pente = x/ (double) (n-i);
      if (pente > pentemax) pentemax = pente;
    }
  }
  return (long) -floor(pentemax);
}

/* returns the exponent for the procedure modulus, from the newton diagram */
static long
polygone_newton(GEN p, long k)
{
  double *logcoef,pente;
  long n=lgef(p)-3,i,j,h,l,*sommet,pentelong;

  logcoef=(double*) gpmalloc((n+1)*sizeof(double));
  sommet=(long*) gpmalloc((n+1)*sizeof(long));

  /* sommet[i]=1 si i est un sommet, =0 sinon */
  for (i=0; i<=n; i++) { logcoef[i]=mylog2((GEN)p[2+i]); sommet[i]=0; }
  sommet[0]=1; i=0;
  while (i<n)
  {
    pente=logcoef[i+1]-logcoef[i];
    h=i+1;
    for (j=i+1; j<=n; j++)
    {
      if (pente<(logcoef[j]-logcoef[i])/(double)(j-i))
      {
	h=j;
	pente=(logcoef[j]-logcoef[i])/(double)(j-i);
      }
    }
    i=h;
    sommet[h]=1;
  }
  h=k; while (!sommet[h]) h++;
  l=k-1; while (!sommet[l]) l--;
  pentelong=(long) floor((logcoef[h]-logcoef[l])/(double)(h-l)+0.5);
  free(logcoef); free(sommet); return pentelong;
}

/* change z into z*2^e, where z is real or complex of real */
static void
myshiftrc(GEN z, long e)
{
  if (typ(z)==t_COMPLEX)
  {
    if (signe(z[1])!=0) setexpo(z[1], expo(z[1])+e);
    if (signe(z[2])!=0) setexpo(z[2], expo(z[2])+e);
  }
  else
    if (signe(z)!=0) setexpo(z,expo(z)+e);
}

/* return z*2^e, where z is integer or complex of integer (destroy z) */
static GEN
myshiftic(GEN z, long e)
{
  if (typ(z)==t_COMPLEX)
  {
    z[1]=signe(z[1])? lmpshift((GEN) z[1],e): zero;
    z[2]=lmpshift((GEN) z[2],e);
    return z;
  }
  return signe(z)? mpshift(z,e): gzero;
}

static GEN
mygprecrc(GEN x, long bitprec, long e)
{
  long tx=typ(x);
  GEN y;

  if (bitprec<0) bitprec=0; /* should rarely happen */
  switch(tx)
  {
    case t_REAL:
      y=cgetr(bitprec/BITS_IN_LONG+3); affrr(x,y);
      if (!signe(x)) setexpo(y,-bitprec+e);
      break;
    case t_COMPLEX:
      y=cgetg(3,t_COMPLEX);
      y[1]=(long) mygprecrc((GEN)x[1],bitprec,e);
      y[2]=(long) mygprecrc((GEN)x[2],bitprec,e);
      break;
    default: y=gcopy(x);
  }
  return y;
}

/* gprec behaves badly with the zero for polynomials.
The second parameter in mygprec is the precision in base 2 */
static GEN
mygprec(GEN x, long bitprec)
{
  long tx=typ(x),lx,i,e;
  GEN y;

  switch(tx)
  {
    case t_POL:
      lx=lgef(x); y=cgetg(lx,tx); y[1]=x[1]; e=gexpo(x);
      for (i=2; i<lx; i++) y[i]=(long) mygprecrc((GEN)x[i],bitprec,e);
      break;

    default: y=mygprecrc(x,bitprec,0);
  }
  return y;
}

/* the round fonction has a bug in pari. Thus I create mygfloor, using gfloor
which has no bug (destroy z)*/
static GEN
mygfloor(GEN z)
{
  if (typ(z)!=t_COMPLEX) return gfloor(z);
  z[1]=lfloor((GEN)z[1]); z[2]=lfloor((GEN)z[2]); return z;
}

/* returns a polynomial q in (Z[i])[x] keeping bitprec bits of p */
static GEN
eval_rel_pol(GEN p,long bitprec)
{
  long e=gexpo(p),n=lgef(p),i,shift;
  GEN q = gprec(p,(long) ((double) bitprec * L2SL10)+2);

  shift=bitprec-e+1;
  for (i=2; i<n; i++)
    q[i]=(long) mygfloor(myshiftic((GEN)q[i],shift));
  return q;
}

/* normalize a polynomial p, that is change it with coefficients in Z[i],
after making product by 2^bitprec */
static void
pol_to_gaussint(GEN p, long bitprec)
{
  long i,n=lgef(p);
  for (i=2; i<n; i++)
  {
    myshiftrc((GEN) p[i],bitprec);
    p[i]=(long) mygfloor((GEN) p[i]);
  }
}

/* returns p(R*x)/R^n (in R or R[i]), n=deg(p), bitprec bits of precision */
static GEN
homothetie(GEN p, GEN R, long bitprec)
{
  GEN q,r,gR,aux;
  long n=lgef(p)-3,i;

  gR=mygprec(ginv(R),bitprec);
  q=mygprec(p,bitprec);
  r=cgetg(n+3,t_POL); r[1]=p[1];
  aux=gR; r[n+2]=q[n+2];
  for (i=n-1; i>=0; i--)
  {
    r[i+2] = lmul(aux,(GEN)q[i+2]);
    aux = mulrr(aux,gR);
  }
  return r;
}

/* change q in 2^(n*e) p(x*2^(-e)), n=deg(q) */
static void
homothetie2n(GEN p, long e)
{
  if (e)
  {
    long i,n=lgef(p)-1;
    for (i=2; i<=n; i++) myshiftrc((GEN) p[i],(n-i)*e);
  }
}

/* return 2^f * 2^(n*e) p(x*2^(-e)), n=deg(q) */
static void
homothetie_gauss(GEN p, long e,long f)
{
  if (e||f)
  {
    long i, n=lgef(p)-1;
    for (i=2; i<=n; i++) p[i]=(long) myshiftic((GEN) p[i],f+(n-i)*e);
  }
}

static long
valuation(GEN p)
{
  long j=0,n=lgef(p)-3;

  while ((j<=n) && isexactzero((GEN)p[j+2])) j++;
  return j;
}

/* provides usually a good lower bound on the largest modulus of the roots,
puts in k an upper bound of the number of roots near the largest root
at a distance eps */
static double
lower_bound(GEN p, long *k, double eps)
{
  long n=lgef(p)-3,i,j,ltop=avma;
  GEN a,s,icd;
  double r,*rho;

  if (n<4) { *k=n; return 0.; }
  a=cgetg(6,t_POL); s=cgetg(6,t_POL);
  rho=(double *) gpmalloc(4*sizeof(double));
  icd=gdiv(gunr,(GEN) p[n+2]);
  for (i=1; i<=4; i++) a[i+1]=lmul(icd,(GEN)p[n+2-i]);
  for (i=1; i<=4; i++)
  {
    s[i+1]=lmulsg(i,(GEN)a[i+1]);
    for (j=1; j<i; j++)
      s[i+1]=ladd((GEN)s[i+1],gmul((GEN)s[j+1],(GEN)a[i+1-j]));
    s[i+1]=lneg((GEN)s[i+1]);
    r=gtodouble(gabs((GEN) s[i+1],3));
    if (r<=0.)  /* should not be strictly negative */
      rho[i-1]=0.;
    else
      rho[i-1]=exp(log(r/(double)n)/(double) i);
  }
  r=0.;
  for (i=0; i<4; i++) if (r<rho[i]) r=rho[i];
  if (r>0. && eps<1.2)
    *k=(long) floor((n*rho[0]/r+n)/(1+exp(-eps)*cos(eps)));
  else
    *k=n;
  free(rho); avma=ltop; return r;
}

/* returns the maximum of the modulus of p with a relative error tau */
static GEN
max_modulus(GEN p, double tau)
{
  GEN q,aux,new_gunr;
  long i,j,k,valuat,n=lgef(p)-3,nn,ltop=avma,bitprec,imax,e;
  double r=0.,rho,tau2,eps;

  if (tau>3.0) tau=3.0; /* fix PZ 7.2.98: ensures eps is positive */
  eps=1/log(4./tau); tau2=tau/6.;
  bitprec=(long) ((double) n*log2(1./tau2)+3*log2((double) n))+1;
  new_gunr=mygprec(gunr,bitprec+2*n);
  aux=gdiv(new_gunr,(GEN) p[2+n]);
  q=gmul(aux,p); q[2+n]=lcopy(new_gunr);
  k=nn=n;
  e=findpower(q); homothetie2n(q,e); r=-(double) e;
  q=mygprec(q,bitprec+(n<<1));
  pol_to_gaussint(q,bitprec);
  imax=(long) ((log(log(4.*n))+log(3./tau))/log(2.))+2;
  for (i=0,e=0;;)
  {
    rho=lower_bound(q,&k,eps);
    if (rho>exp2(-(double) e)) e = (long) -floor(log2(rho));
    r = r-(double) e/ exp2( (double) i);
    if (++i == imax)
    {
      avma=ltop;
      return gpui(dbltor(2.),dbltor(r),DEFAULTPREC);
    }

    if (k<nn)
      bitprec=(long) ((double) k* log2(1./tau2)+
                      (double) (nn-k)*log2(1./eps)+
                      3*log2((double) nn))+1;
    else
      bitprec=(long) ((double) nn* log2(1./tau2)+
                      3.*log2((double) nn))+1;
    homothetie_gauss(q,e,bitprec-(long)floor(mylog2((GEN) q[2+nn])+0.5));
    valuat=valuation(q);
    if (valuat>0)
    {
      nn-=valuat; setlgef(q,nn+3);
      for (j=0; j<=nn; j++) q[2+j]=q[2+valuat+j];
    }
    set_karasquare_limit(gexpo(q));
    q = gerepileupto(ltop, graeffe(q));
    tau2=1.5*tau2; eps=1/log(1./tau2);
    e = findpower(q);
  }
}

/* return the k-th modulus (in ascending order) of p, rel. error tau*/
static GEN
modulus(GEN p, long k, double tau)
{
  GEN q,new_gunr;
  long i,j,kk=k,imax,n=lgef(p)-3,nn,nnn,valuat,av,ltop=avma,bitprec,decprec,e;
  double tau2,r;

  tau2=tau/6; nn=n;
  bitprec= (long) ((double) n*(2.+log2(3.*(double) n)+log2(1./tau2)));
  decprec=(long) ((double) bitprec * L2SL10)+1;
  new_gunr=gprec(gunr,decprec);
  av = avma;
  q=gprec(p,decprec);
  q=gmul(new_gunr,q);
  e=polygone_newton(q,k);
  homothetie2n(q,e);
  r=(double) e;
  imax=(long) ((log2(3./tau)+log2(log(4.*(double) n)) ))+1;
  for (i=1; i<imax; i++)
  {
    q=eval_rel_pol(q,bitprec);

    nnn=lgef(q)-3; valuat=valuation(q);
    if (valuat>0)
    {
      kk-=valuat;
      for (j=0; j<=nnn-valuat; j++) q[2+j]=q[2+valuat+j];
      setlgef(q,nnn-valuat+3);
    }
    nn=nnn-valuat;

    set_karasquare_limit(bitprec);
    q = gerepileupto(av, graeffe(q));
    e=polygone_newton(q,kk);
    r=r+e/exp2((double)i);
    q=gmul(new_gunr,q);
    homothetie2n(q,e);

    tau2=1.5*tau2; if (tau2>1.) tau2=1.;
    bitprec= 1+(long) ((double) nn*(2.+log2(3.*(double) nn)+log2(1./tau2)));
  }
  avma=ltop; return mpexp(dbltor(-r * LOG2));
}

/* return the k-th modulus r_k of p, rel. error tau, knowing that
rmin < r_k < rmax. This helps because the information enable us to use
less precision... quicker ! */
static GEN
pre_modulus(GEN p, long k, double tau, GEN rmin, GEN rmax)
{
  GEN R, q, aux;
  long n=lgef(p)-3,i,imax,imax2,bitprec,ltop=avma, av;
  double tau2, aux2;

  tau2=tau/6.;
  aux = mulrr(mpsqrt(divrr(rmax,rmin)), dbltor(exp(4*tau2)));
  imax = (long) log2(log((double)n)/ rtodbl(mplog(aux)));
  if (imax<=0) return modulus(p,k,tau);

  R = mpsqrt(mulrr(rmin,rmax));
  av = avma;
  bitprec = (long) ((double) n*(2. + log2ir(aux) - log2(tau2)));
  q = homothetie(p,R,bitprec);
  imax2 = (long) ((log2(3./tau)+log2(log(4.*(double) n)) ))+1;
  if (imax>imax2) imax=imax2;

  for (i=0; i<imax; i++)
  {
    q = eval_rel_pol(q,bitprec);
    set_karasquare_limit(bitprec);
    q = gerepileupto(av, graeffe(q));
    affrr(mulrr(gsqr(aux), dbltor(exp(2*tau2))), aux);
    tau2 *= 1.5;
    bitprec= (long) ((double) n*(2. + log2ir(aux) - log2(1-exp(-tau2))));
    q = gmul(mygprec(gunr,bitprec),q);
  }

  aux2 = rtodbl(mplog(modulus(q,k,exp2((double)imax)*tau/3.)));
  R = mulrr(R, dbltor(exp(aux2*exp2(-(double)imax))));
  return gerepileupto(ltop, R);
}

/* returns the minimum of the modulus of p with a relative error tau */
static GEN
min_modulus(GEN p, double tau)
{
  long av=avma;
  GEN r;

  if (isexactzero((GEN)p[2])) return realzero(3);
  r = max_modulus(polrecip_i(p),tau);
  return gerepileupto(av, ginv(r));
}

/* returns k such that r_k e^(-tau) < R < r_{ k+1 } e^tau.
l is such that you know in advance that l<= k <= n-l */
static long
dual_modulus(GEN p, GEN R, double tau, long l)
{
  GEN q;
  long i,j,imax,k,delta_k=0,n=lgef(p)-3,nn,nnn,valuat,ltop=avma,bitprec,ll=l;
  double logmax,aux,tau2;

  tau2=7.*tau/8.;
  bitprec=6*n-5*l+(long) ((double) n*(log2(1/tau2)+8.*tau2/7.));
  q=homothetie(p,R,bitprec);
  nn=n;
  imax=(long)(log(log(2.*(double)n)/tau2)/log(7./4.)+1);

  for (i=0; i<imax; i++)
  {
    bitprec=6*nn-5*ll+(long) ((double) nn*(log2(1/tau2)+8.*tau2/7.));

    q=eval_rel_pol(q,bitprec);
    nnn=lgef(q)-3; valuat=valuation(q);
    if (valuat>0)
    {
      delta_k+=valuat;
      for (j=0; j<=nnn-valuat; j++) q[2+j]=q[2+valuat+j];
      setlgef(q,nnn-valuat+3);
    }
    ll= (-valuat<nnn-n)? ll-valuat: ll+nnn-n; /* min(ll-valuat,ll+nnn-n) */
    if (ll<0) ll=0;

    nn=nnn-valuat;
    if (nn==0) return delta_k;

    set_karasquare_limit(bitprec);
    q = gerepileupto(ltop, graeffe(q));
    tau2=tau2*7./4.;
  }
  k=-1; logmax=- (double) pariINFINITY;
  for (i=0; i<=lgef(q)-3; i++)
  {
    aux=mylog2((GEN)q[2+i]);
    if (aux>logmax) { logmax=aux; k=i; }
  }
  avma=ltop; return delta_k+k;
}

/********************************************************************/
/**                                                                **/
/**       CALCUL D'UN FACTEUR PAR INTEGRATION SUR LE CERCLE        **/
/**                                                                **/
/********************************************************************/

static GEN
gmulbyi(GEN z)
{
  GEN aux = cgetg(3,t_COMPLEX);

  if (typ(z)!=t_COMPLEX)
  {
    aux[1]=zero;
    aux[2]=(long) z;
  }
  else
  {
    aux[1]=lneg((GEN)z[2]);
    aux[2]=z[1];
  }
  return aux;
}

static void
fft(GEN Omega, GEN p, GEN f, long step, long l)
{
  long i,l1,l2,l3,rap=Lmax/l,rapi,step4,ltop,lbot;
  GEN f1,f2,f3,f02,f13,g02,g13,ff;

  if (l==2)
  {
    f[0]=ladd((GEN)p[0],(GEN)p[step]);
    f[1]=lsub((GEN)p[0],(GEN)p[step]); return;
  }
  if (l==4)
  {
    f1=gadd((GEN)p[0],(GEN)p[(step<<1)]);
    f3=gadd((GEN)p[step],(GEN)p[3*step]);
    f[0]=ladd(f1,f3);
    f[2]=lsub(f1,f3);

    f2=gsub((GEN)p[0],(GEN)p[(step<<1)]);
    f02=gsub((GEN)p[step],(GEN)p[3*step]);
    f02=gmulbyi(f02);
    f[1]=ladd(f2,f02);
    f[3]=lsub(f2,f02);
    return;
  }

  l1=(l>>2); l2=(l1<<1); l3=l1+l2; step4=(step<<2);

  ltop=avma;
  fft(Omega,p,f,step4,l1);
  fft(Omega,p+step,f+l1,step4,l1);
  fft(Omega,p+(step<<1),f+l2,step4,l1);
  fft(Omega,p+3*step,f+l3,step4,l1);

  ff=cgetg(l+1,t_VEC);
  for (i=0; i<l1; i++)
  {
    rapi=rap*i;
    f1=gmul((GEN)Omega[rapi],(GEN) f[i+l1]);
    f2=gmul((GEN)Omega[(rapi<<1)],(GEN) f[i+l2]);
    f3=gmul((GEN)Omega[3*rapi],(GEN) f[i+l3]);

    f02=gadd((GEN)f[i],f2);
    g02=gsub((GEN)f[i],f2);
    f13=gadd(f1,f3);
    g13=gmulbyi(gsub(f1,f3));

    ff[i+1]=ladd(f02,f13);
    ff[i+l1+1]=ladd(g02,g13);
    ff[i+l2+1]=lsub(f02,f13);
    ff[i+l3+1]=lsub(g02,g13);
  }
  lbot=avma; ff=gerepile(ltop,lbot,gcopy(ff));
  for (i=0; i<l; i++) f[i]=ff[i+1];
}

/* returns a vector RU which contains exp(2*i*k*Pi/NN), k=0..NN-1 */
static GEN
initRU(long NN, long bitprec)
{
  GEN prim,aux,RU,mygpi;
  long i,N2=(NN>>1),N4=(NN>>2),N8=(NN>>3),decprec;

  RU=cgetg(NN+1,t_VEC); RU++;
  mygpi=mppi(bitprec/BITS_IN_LONG+3);
  aux=gmul(gi,gdivgs(mygpi,NN/2)); /* 2i Pi/NN */
  decprec=(long) ((double) bitprec * L2SL10)+1;
  prim=gexp(aux,decprec);
  RU[0]=lprec(gunr,decprec);

  for (i=1; i<=N8; i++) RU[i]=lmul(prim,(GEN)RU[i-1]);
  for (i=1; i<N8; i++)
  {
    aux=cgetg(3,t_COMPLEX);
    aux[1]=((GEN)RU[i])[2]; aux[2]=((GEN)RU[i])[1];
    RU[N4-i]=(long) aux;
  }
  for (i=0; i<N4; i++) RU[i+N4]=(long)gmulbyi((GEN)RU[i]);
  for (i=0; i<N2; i++) RU[i+N2]=lneg((GEN)RU[i]);
  return RU;
}

/* returns 1 if p has only real coefficients, 0 else */
static long
isreal(GEN p)
{
  long n=lgef(p)-3,i=0;

  while (i<=n && typ(p[i+2])!=t_COMPLEX) i++;
  return (i>n);
}

static void
parameters(GEN p, double *mu, double *gamma,
           long polreal, double param, double param2)
{
  GEN q,pc,Omega,coef,RU,prim,aux,ggamma,gx,mygpi;
  long ltop=avma,limite=stack_lim(ltop,1),n=lgef(p)-3,bitprec,NN,K,i,j,ltop2;
  double lx;

  bitprec=gexpo(p)+(long)param2+8;
  NN=(long) (param*3.14)+1; if (NN<Lmax) NN=Lmax;
  K=NN/Lmax; if (K%2==1) K++; NN=Lmax*K;
  mygpi=mppi(bitprec/BITS_IN_LONG+3);
  aux=gmul(gi,gdivgs(mygpi,NN/2)); /* 2i Pi/NN */
  prim=gexp(aux,(long) ((double) bitprec * L2SL10)+1);
  RU=mygprec(gunr,bitprec);

  Omega=initRU(Lmax,bitprec);

  q=mygprec(p,bitprec);
  pc=cgetg(Lmax+1,t_VEC); pc++;
  for (i=n+1; i<Lmax; i++) pc[i]=zero;

  coef=cgetg(Lmax+1,t_VEC); coef++;
  *mu=(double)pariINFINITY; *gamma=0.;
  ggamma=gmul(gzero,gunr);
  if (polreal) K=K/2+1;
  ltop2=avma;
  for (i=0; i<K; i++)
  {
    aux=mygprec(gunr,bitprec);
    for (j=0; j<=n; j++)
    {
      pc[j]=lmul((GEN)q[j+2],aux);
      aux=gmul(aux,RU); /* RU = prim^i, aux=prim^(ij) */
    }

    fft(Omega,pc,coef,1,Lmax);
    for (j=0; j<Lmax; j++)
    {
      aux=gprec((GEN)coef[j],DEFAULTPREC);
      gx=gabs(aux,DEFAULTPREC);
      lx=gtodouble(mplog(gx));
      if (lx<*mu) *mu=lx;
      if (polreal && (i>0 && i<K-1))
      {
	gx=gdiv(gdeux,gx);
	ggamma=gadd(ggamma,gx);
      }
      else
	ggamma=gadd(ggamma,ginv(gx));
    }
    RU=gmul(RU,prim);
    if (low_stack(limite, stack_lim(ltop,1)))
    {
      GEN *gptr[2];
      if(DEBUGMEM>1) err(warnmem,"parameters");
      gptr[0]=&ggamma; gptr[1]=&RU; gerepilemany(ltop2,gptr,2);
    }
  }
  ggamma=gdivgs(ggamma,NN);
  *gamma=gtodouble(glog(ggamma,DEFAULTPREC))/log(2.);
  avma=ltop;
}

/* NN is a multiple of Lmax */
static void
dft(GEN p, long k, long NN, long bitprec, GEN F, GEN H, long polreal)
{
  GEN Omega,q,qd,pc,pdc,alpha,beta,gamma,RU,aux,U,W,mygpi,prim,prim2;
  long limite,n=lgef(p)-3,i,j,K,ltop;

  mygpi=mppi(bitprec/BITS_IN_LONG+3);
  aux=gmul(gi,gdivgs(mygpi,NN/2)); /* 2i Pi/NN */
  prim=gexp(aux,(long) ((double) bitprec * L2SL10)+1);
  prim2=mygprec(gunr,bitprec);
  RU=cgetg(n+2,t_VEC); RU++;

  Omega=initRU(Lmax,bitprec);
  K=NN/Lmax; q=mygprec(p,bitprec);
  qd=derivpol(q);

  pc=cgetg(Lmax+1,t_VEC); pc++;
  for (i=n+1; i<Lmax; i++) pc[i]=zero;
  pdc=cgetg(Lmax+1,t_VEC); pdc++;
  for (i=n; i<Lmax; i++) pdc[i]=zero;

  alpha=cgetg(Lmax+1,t_VEC); alpha++;
  beta=cgetg(Lmax+1,t_VEC); beta++;
  gamma=cgetg(Lmax+1,t_VEC); gamma++;

  if (polreal) K=K/2+1;

  ltop=avma; limite = stack_lim(ltop,1);
  W=cgetg(k+1,t_VEC); U=cgetg(k+1,t_VEC);
  for (i=1; i<=k; i++) W[i]=U[i]=zero;

  for (i=0; i<K; i++)
  {
    RU[0]=(long) gun;
    for (j=1; j<=n; j++) RU[j]=lmul((GEN)RU[j-1],prim2);
    /* RU[j]=prim^{ ij }=prim2^j */

    for (j=0; j<n; j++) pdc[j]=lmul((GEN)qd[j+2],(GEN)RU[j]);
    fft(Omega,pdc,alpha,1,Lmax);
    for (j=0; j<=n; j++) pc[j]=lmul((GEN)q[j+2],(GEN)RU[j]);
    fft(Omega,pc,beta,1,Lmax);
    for (j=0; j<Lmax; j++) gamma[j]=linv((GEN)beta[j]);
    for (j=0; j<Lmax; j++) beta[j]=lmul((GEN)alpha[j],(GEN)gamma[j]);
    fft(Omega,beta,alpha,1,Lmax);
    fft(Omega,gamma,beta,1,Lmax);

    if (polreal) /* p has real coefficients */
    {
      if (i>0 && i<K-1)
      {
	for (j=1; j<=k; j++)
	{
	  aux=gmul((GEN)alpha[j+1],(GEN)RU[j+1]);
	  W[j]=ladd((GEN)W[j],gshift(greal(aux),1));
	  aux=gmul((GEN)beta[j],(GEN)RU[j]);
	  U[j]=ladd((GEN)U[j],gshift(greal(aux),1));
	}
      }
      else
      {
	for (j=1; j<=k; j++)
	{
	  aux=gmul((GEN)alpha[j+1],(GEN)RU[j+1]);
	  W[j]=ladd((GEN)W[j],greal(aux));
	  aux=gmul((GEN)beta[j],(GEN)RU[j]);
	  U[j]=ladd((GEN)U[j],greal(aux));
	}
      }
    }
    else
    {
      for (j=1; j<=k; j++)
      {
	W[j]=ladd((GEN)W[j],gmul((GEN)alpha[j+1],(GEN)RU[j+1]));
	U[j]=ladd((GEN)U[j],gmul((GEN)beta[j],(GEN)RU[j]));
      }
    }
    prim2=gmul(prim2,prim);
    if (low_stack(limite, stack_lim(ltop,1)))
    {
      GEN *gptr[3];
      if(DEBUGMEM>1) err(warnmem,"dft");
      gptr[0]=&W; gptr[1]=&U; gptr[2]=&prim2;
      gerepilemany(ltop,gptr,3);
    }
  }

  for (i=1; i<=k; i++)
  {
    aux=(GEN)W[i];
    for (j=1; j<i; j++) aux=gadd(aux,gmul((GEN)W[i-j],(GEN)F[k+2-j]));
    F[k+2-i] = ldivgs(aux,-i*NN);
  }
  for (i=0; i<k; i++)
  {
    aux=(GEN)U[k-i];
    for (j=1+i; j<k; j++) aux=gadd(aux,gmul((GEN)F[2+j],(GEN)U[j-i]));
    H[i+2] = ldivgs(aux,NN);
  }
}

static GEN
refine_H(GEN F, GEN G, GEN HH, long bitprec, long shiftbitprec)
{
  GEN H=HH,D,aux;
  long ltop=avma, limite=stack_lim(ltop,1),error=0,i,bitprec1,bitprec2,lbot;

  D=gsub(gun,gres(gmul(HH,G),F)); error=gexpo(D);
  bitprec2=bitprec+shiftbitprec;

  for (i=0; (error>-bitprec && i<NEWTON_MAX) && error<=0; i++)
  {
    if (low_stack(limite, stack_lim(ltop,1)))
    {
      GEN *gptr[2];
      if(DEBUGMEM>1) err(warnmem,"refine_H");
      gptr[0]=&D; gptr[1]=&H; gerepilemany(ltop,gptr,2);
    }
    bitprec1=-error+shiftbitprec;
    aux=gmul(mygprec(H,bitprec1),mygprec(D,bitprec1));
    aux=mygprec(aux,bitprec1);
    aux=gres(aux,mygprec(F,bitprec1));

    bitprec1=-error*2+shiftbitprec;
    if (bitprec1>bitprec2) bitprec1=bitprec2;
    H=gadd(mygprec(H,bitprec1),aux);
    D=gsub(gun,gres(gmul(H,G),F));
    error=gexpo(D); if (error<-bitprec1) error=-bitprec1;
  }
  if (error<=-bitprec/2) { lbot=avma; return gerepile(ltop,lbot,gcopy(H)); }
  avma=ltop; return gzero; /* procedure failed */
}

/* return 0 if fails, 1 else */
static long
refine_F(GEN p, GEN *F, GEN *G, GEN H, long bitprec, double gamma)
{
  GEN pp,FF,GG,r,HH,f0;
  long error,i,bitprec1=0,bitprec2,ltop=avma,shiftbitprec;
  long shiftbitprec2,n=lgef(p)-3,enh,normF,normG,limite=stack_lim(ltop,1);

  FF=*F; HH=H;
  GG=poldivres(p,*F,&r);
  normF=gexpo(FF);
  normG=gexpo(GG);
  enh=gexpo(H); if (enh<0) enh=0;
  shiftbitprec=normF+2*normG+enh+(long) (4.*log2((double)n)+gamma) +1;
  shiftbitprec2=enh+2*(normF+normG)+(long) (2.*gamma+5.*log2((double)n))+1;
  bitprec2=bitprec+shiftbitprec;
  error=gexpo(r);
  if (error<-bitprec) error=1-bitprec;
  for (i=0; (error>-bitprec && i<NEWTON_MAX) && error<=0; i++)
  {
    if ((bitprec1==bitprec2) && (i>=2))
    {
      shiftbitprec+=n; shiftbitprec2+=n; bitprec2+=n;
    }
    if (low_stack(limite, stack_lim(ltop,1)))
    {
      GEN *gptr[4];
      if(DEBUGMEM>1) err(warnmem,"refine_F");
      gptr[0]=&FF; gptr[1]=&GG; gptr[2]=&r; gptr[3]=&HH;
      gerepilemany(ltop,gptr,4);
    }

    bitprec1=-error+shiftbitprec2;
    HH=refine_H(mygprec(FF,bitprec1),mygprec(GG,bitprec1),
		mygprec(HH,bitprec1),1-error,shiftbitprec2);
    if (HH==gzero) return 0; /* procedure failed */

    bitprec1=-error+shiftbitprec;
    r=gmul(mygprec(HH,bitprec1),mygprec(r,bitprec1));
    r=mygprec(r,bitprec1);
    f0=gres(r,mygprec(FF,bitprec1));

    bitprec1=-2*error+shiftbitprec;
    if (bitprec1>bitprec2) bitprec1=bitprec2;
    FF=gadd(mygprec(FF,bitprec1),f0);

    bitprec1=-3*error+shiftbitprec;
    if (bitprec1>bitprec2) bitprec1=bitprec2;
    pp=mygprec(p,bitprec1);
    GG=poldivres(pp,mygprec(FF,bitprec1),&r);
    error=gexpo(r); if (error<-bitprec1) error=-bitprec1;
  }
  if (error<=-bitprec)
  {
    *F=FF; *G=GG;
    return 1; /* procedure succeeds */
  }
  return 0; /* procedure failed */
}

/* returns F and G from the unit circle U such that |p-FG|<2^(-bitprec) |cd|,
where cd is the leading coefficient of p */
static void
split_fromU(GEN p, long k, double delta, long bitprec,
            GEN *F, GEN *G, double param, double param2)
{
  GEN pp,FF,GG,H;
  long n=lgef(p)-3,NN,bitprec2,
  ltop=avma,polreal=isreal(p);
  double mu,gamma;

  pp=gdiv(p,(GEN)p[2+n]);
  Lmax=4; while (Lmax<=n) Lmax=(Lmax<<1);
  parameters(pp,&mu,&gamma,polreal,param,param2);

  H =cgetg(k+2,t_POL); H[1] =evalsigne(1) | evalvarn(varn(p)) | evallgef(k+2);
  FF=cgetg(k+3,t_POL); FF[1]=evalsigne(1) | evalvarn(varn(p)) | evallgef(k+3);
  FF[k+2]=un;

  NN=(long) (0.5/delta); NN+=(NN%2); if (NN<2) NN=2;
  NN=NN*Lmax; ltop=avma;
  for(;;)
  {
    bitprec2=(long) (((double) NN*delta-mu)/log(2.))+gexpo(pp)+8;
    dft(pp,k,NN,bitprec2,FF,H,polreal);
    if (refine_F(pp,&FF,&GG,H,bitprec,gamma)) break;
    NN=(NN<<1); avma=ltop;
  }
  *G=gmul(GG,(GEN)p[2+n]); *F=FF;
}

static void
optimize_split(GEN p, long k, double delta, long bitprec,
            GEN *F, GEN *G, double param, double param2)
{
  long n=lgef(p)-3;
  GEN FF,GG;

  if (k<=n/2)
    split_fromU(p,k,delta,bitprec,F,G,param,param2);
  else
  { /* start from the reciprocal of p */
    split_fromU(polrecip_i(p),n-k,delta,bitprec,&FF,&GG,param,param2);
    *F=polrecip(GG); *G=polrecip(FF);
  }
}

/********************************************************************/
/**                                                                **/
/**             RECHERCHE DU CERCLE DE SEPARATION                  **/
/**                                                                **/
/********************************************************************/

/* return p(2^e*x) *2^(-n*e) */
static void
scalepol2n(GEN p, long e)
{
  long i,n=lgef(p)-1;
  for (i=2; i<=n; i++) p[i]=lmul2n((GEN)p[i],(i-n)*e);
}

/* returns p(x/R)*R^n */
static GEN
scalepol(GEN p, GEN R, long bitprec)
{
  GEN q,aux,gR;
  long i;

  aux = gR = mygprec(R,bitprec); q = mygprec(p,bitprec);
  for (i=lgef(p)-2; i>=2; i--)
  {
    q[i]=lmul(aux,(GEN)q[i]);
    aux = gmul(aux,gR);
  }
  return q;
}

/* returns q(x)=p(b), where b is (usually) a polynomial  */
static GEN
shiftpol(GEN p, GEN b)
{
  long av = avma,i, limit = stack_lim(av,1);
  GEN q = gzero;

  for (i=lgef(p)-1; i>=2; i--)
  {
    q = gadd((GEN)p[i], gmul(q,b));
    if (low_stack(limit, stack_lim(av,1))) q = gerepileupto(av,q);
  }
  return gerepileupto(av,q);
}

/* return (aX-1)^n * p[ (X-a) / (aX-1) ] */
static GEN
conformal_pol(GEN p, GEN a, long bitprec)
{
  GEN r,pui,num,aux;
  long n=lgef(p)-3, i;

  aux = pui = cgetg(4,t_POL);
  pui[1] = evalsigne(1) | evalvarn(varn(p)) | evallgef(4);
  pui[2] = (long) mygprec(gneg_i(gunr),bitprec);
  pui[3] = lconj(a);
  num = cgetg(4,t_POL);
  num[1] = pui[1];
  num[2] = lneg(a);
  num[3] = (long) mygprec(gunr,bitprec);
  r=(GEN)p[2+n];
  for (i=n-1; ; i--)
  {
    r=gadd(gmul(r,num),gmul(aux,(GEN) p[2+i]));
    if (i==0) return r;
    aux=gmul(pui,aux);
  }
}

/* apply the conformal mapping then split from U */
static void
conformal_mapping(GEN p, long k, long bitprec, double aux,GEN *F,GEN *G)
{
  long bitprec2,n=lgef(p)-3,decprec,i,ltop = avma, av;
  GEN q,FF,GG,a,R,aux2, *gptr[3];
  GEN rmin,rmax,rho,invrho;
  double delta,param,param2;

  bitprec2=bitprec+(long) (n*(2.*log2(2.732)+log2(1.5)))+1;
  a=gsqrt(stoi(3),10);
  a=gmul(mygprec(a,bitprec2),mygprec(globalu,bitprec2));
  a=gdivgs(a,-6); /* a=-globalu/2/sqrt(3) */

  av = avma; q=mygprec(p,bitprec2);
  q = conformal_pol(q,a,bitprec2);
  for (i=1; i<=n; i++)
    if (signe(radius[i])) /* updating array radius */
    {
      long a = avma;
      GEN p1 = gsqr(radius[i]);
      p1 = divrr(gmul2n((subrs(p1,1)),1),
                   subrr(p1, mulsr(3,subrs(radius[i],1))));
      affrr(mpsqrt(addsr(1,p1)), radius[i]);
      avma = a;
    }
  if (k>1)
  {
    i=k-1; while (i>0 && !signe(radius[i])) i--;
    rmin = pre_modulus(q,k,aux/10., radius[i], radius[k]);
  }
  else
    rmin = min_modulus(q,aux/10.);
  affrr(rmin, radius[k]);

  if (k+1<n)
  {
    i=k+2; while (i<=n && !signe(radius[i])) i++;
    rmax = pre_modulus(q,k+1,aux/10., radius[k+1], radius[i]);
  }
  else /* k+1=n */
    rmax = max_modulus(q,aux/10.);
  affrr(rmax, radius[k+1]);

  rho = mpsqrt(mulrr(rmin,rmax));
  delta = rtodbl(gmul2n(mplog(divrr(rmax,rmin)), -1));
  if (delta>1.) delta=1.;

  bitprec2 += (long) (((double)n) * fabs(log2ir(rho)) + 1.);

  invrho = ginv(rho);
  R=mygprec(invrho,bitprec2);
  q=scalepol(q,R,bitprec2);
  gptr[0]=&q; gptr[1]=&R; gptr[2]=&invrho;
  gerepilemany(av,gptr,3);

  aux2 = radius[k];
  for (i=k-1; i>=1; i--)
  {
    if (!signe(radius[i]))
      affrr(aux2, radius[i]);
    else
      aux2 = radius[i];
  }
  aux2 = radius[k+1];
  for (i=k+1; i<=n; i++)
  {
    if (!signe(radius[i]))
      affrr(aux2, radius[i]);
    else
      aux2 = radius[i];
  }
  param=0.; param2=0.;
  for (i=1; i<=n; i++)
  {
    affrr(mulrr(radius[i], invrho), radius[i]);
    aux2 = ginv(subsr(1, radius[i]));
    param += fabs(rtodbl(aux2));
    if (cmprs(aux2, 1) > 0) param2 += log2ir(aux2);
  }
  optimize_split(q,k,delta,bitprec2,&FF,&GG,param,param2);
  bitprec2 += n; R = ginv(R);
  FF=scalepol(FF,R,bitprec2);
  GG=scalepol(GG,R,bitprec2);

  a=mygprec(a,bitprec2);
  FF=conformal_pol(FF,a,bitprec2);
  GG=conformal_pol(GG,a,bitprec2);
  a=ginv(gsub(gun,gmul(a,gconj(a))));
  a=glog(a,(long) (bitprec2 * L2SL10)+1);

  decprec=(long) ((bitprec+n) * L2SL10)+1;
  FF=gmul(FF,gexp(gmulgs(a,k),decprec));
  GG=gmul(GG,gexp(gmulgs(a,n-k),decprec));

  *F=mygprec(FF,bitprec+n);
  *G=mygprec(GG,bitprec+n);
  gptr[0]=F; gptr[1]=G; gerepilemany(ltop,gptr,2);
}

/* split p, this time with no scaling. returns in F and G two polynomials
such that |p-FG|< 2^(-bitprec)|p| */
static void
split_2(GEN p, long bitprec, double thickness, GEN *F, GEN *G)
{
  GEN rmin,rmax,rho,invrho;
  double kappa,aux,delta,param,param2;
  long n=lgef(p)-3,i,j,k,disti,diste,bitprec2;
  GEN q,FF,GG,R,aux2;

  radius = (GEN*) cgetg(n+1, t_VEC);
  for (i=1; i<n; i++) radius[i]=realzero(3);
  radius[1] = rmin = min_modulus(p, thickness/(double) n/4.);
  radius[n] = rmax = max_modulus(p, thickness/(double) n/4.);
  i=1; j=n;
  rho = mpsqrt(mulrr(rmin,rmax));
  k=dual_modulus(p,rho,thickness/(double) n/4.,1);
  if (k<n/5. || (n/2.<k && k<(4*n)/5.))
    { rmax=rho; j=k+1; affrr(rho, radius[j]); }
  else
    { rmin=rho; i=k; affrr(rho, radius[i]); }
  while (j>i+1)
  {
    disti= (i<n-j)? i: n-j; /* min(i,n-j) */
    diste= (j<n-i)? j: n-i;
    kappa=1. - log(1.+(double)disti) / log(1.+(double)diste);
    if (i+j<n+1)
      rho = mpexp(
        divrr(addrr( mulrr(mplog(rmax),dbltor(1+kappa)), mplog(rmin) ),
              dbltor(2+kappa))
      );
    else if (i+j==n+1)
      rho = mpsqrt(mulrr(rmin,rmax));
    else
      rho = mpexp(
        divrr(addrr( mulrr(mplog(rmin),dbltor(1+kappa)), mplog(rmax)),
              dbltor(2+kappa))
      );
    aux = rtodbl(mplog(divrr(rmax,rmin))) / (j-i) / 4.;

    k = min(i,n+1-j);
    k = dual_modulus(p,rho,aux,k);
    if (k-i < j-k-1)
      { rmax=rho; j=k+1; affrr(mulrr(rho, dbltor(exp(-aux))), radius[j]); }
    else
    {
      if (k-i > j-k-1)
        { rmin=rho; i=k; affrr(mulrr(rho, dbltor(exp(aux))), radius[i]); }
      else
      {
	if (2*k>n)
          { rmax=rho; j=k+1; affrr(mulrr(rho, dbltor(exp(-aux))), radius[j]); }
	else
          { rmin=rho; i=k; affrr(mulrr(rho, dbltor(exp(aux))), radius[i]); }
      }
    }
  }
  aux = rtodbl(mplog(divrr(rmax, rmin)));

  if (step4==0)
  {
    if (k>1)
    {
      i=k-1; while (i>0 && !signe(radius[i])) i--;
      rmin = pre_modulus(p,k,aux/10., radius[i], radius[k]);
    }
    else /* k=1 */
      rmin = min_modulus(p,aux/10.);
    affrr(rmin, radius[k]);

    if (k+1<n)
    {
      i=k+2; while (i<=n && !signe(radius[i])) i++;
      rmax = pre_modulus(p,k+1,aux/10., radius[k+1], radius[i]);
    }
    else /* k+1=n */
      rmax = max_modulus(p,aux/10.);
    affrr(rmax, radius[k+1]);

    rho = mpsqrt(mulrr(rmin,rmax));
    delta = rtodbl(gmul2n(mplog(divrr(rmax, rmin)), -1));

    aux2 = radius[k];
    for (i=k-1; i>=1; i--)
    {
      if (!signe(radius[i]))
        affrr(aux2, radius[i]);
      else
        aux2 = radius[i];
    }
    aux2 = radius[k+1];
    for (i=k+1; i<=n; i++)
    {
      if (!signe(radius[i]))
        affrr(aux2, radius[i]);
      else      
        aux2 = radius[i];
    }
    invrho = ginv(rho);
    param = 0.;param2 = 0.;
    for (i=1; i<=n; i++)
    {
      affrr(mulrr(radius[i], invrho), radius[i]);
      aux2 = ginv(subsr(1, radius[i]));
      param += fabs(rtodbl(aux2));
      if (cmprs(aux2, 1) > 0) param2 += log2ir(aux2);
    }
    bitprec2 = bitprec + (long) ((double)n * fabs(log2ir(rho)) + 1.);

    R=mygprec(invrho,bitprec2);
    q=scalepol(p,R,bitprec2);
    optimize_split(q,k,delta,bitprec2,&FF,&GG,param,param2);
    bitprec2 += n; R=ginv(R);
  }
  else
  {
    rho = mpsqrt(mulrr(rmax,rmin));
    invrho = ginv(rho);
    bitprec2 = bitprec + (long) ((double)n * fabs(log2ir(rho)) + 1.);

    R = mygprec(invrho,bitprec2);
    q = scalepol(p,R,bitprec2);
    for (i=1; i<=n; i++)
      if (signe(radius[i])) affrr(mulrr(radius[i],invrho), radius[i]);

    conformal_mapping(q, k, bitprec2, aux, &FF, &GG);
    bitprec2 += n; R = ginv(mygprec(R,bitprec2));
  }
  *F = mygprec(scalepol(FF,R,bitprec2), bitprec+n);
  *G = mygprec(scalepol(GG,R,bitprec2), bitprec+n);
}

/* procedure corresponding to steps 5,6,.. page 44 in the RR n. 1852 */
/* put in F and G two polynomial such that |p-FG|<2^(-bitprec)|p|
where the maximum modulus of the roots of p is <=1 and the sum of roots
is zero */

static void
split_1(GEN p, long bitprec, GEN *F, GEN *G)
{
  long bitprec2,bitprec3,i,imax,n=lgef(p)-3, polreal = isreal(p);
  GEN rmax,rmin,thickness,quo;
  GEN q,qq,newq,FF,GG,v,gr,r;

  r=max_modulus(p,0.01);
  bitprec2=bitprec+n;
  gr=mygprec(ginv(r),bitprec2);
  q=scalepol(p,gr,bitprec2);

  bitprec2=bitprec+gexpo(q)-gexpo(p);

  bitprec3=bitprec2+(long)((double)n*2.*log2(3.)+1);
  v=cgetg(5,t_VEC); v++;
  v[0]=lmul2n(mygprec(gunr,bitprec3), 1);
  v[1]=lneg((GEN)v[0]);
  v[2]=lmul((GEN)v[0],gi);
  v[3]=lneg((GEN)v[2]);
  imax = polreal? 3: 4;
  q=mygprec(q,bitprec3); thickness=realun(3);
  for (i=0; i<imax; i++)
  {
    qq = shiftpol(q,gadd(polx[varn(p)],(GEN)v[i]));
    rmin = min_modulus(qq,0.05);
    if (cmpsr(3, mulrr(rmin, thickness)) > 0)
    {
      rmax = max_modulus(qq,0.05);
      quo = divrr(rmax,rmin);
      if (cmprr(quo, thickness) > 0)
      {
	thickness=quo; newq=qq; globalu=(GEN)v[i];
      }
    }
    if (cmpsr(2 , thickness) < 0) break;
    if (polreal && i==1 && cmprr(thickness, dbltor(1.5)) > 0) break;
  }
  bitprec3=bitprec2+(long)((double) n*log2(3.)+1)+gexpo(newq)-gexpo(q);
  split_2(newq,bitprec3,rtodbl(mplog(thickness)),&FF,&GG);
  globalu=gsub(polx[varn(p)],mygprec(globalu,bitprec3));
  FF = shiftpol(FF,globalu);
  GG = shiftpol(GG,globalu);

  gr = ginv(gr);
  bitprec2 += gexpo(FF)+gexpo(GG)-gexpo(q);
  *F = scalepol(FF,gr,bitprec2);
  *G = scalepol(GG,gr,bitprec2);
}

/* put in F and G two polynomials such that |P-FG|<2^(-bitprec)|P|,
where the maximum modulus of the roots of p is < 0.5 */
static void
split_0_2(GEN p, long bitprec, GEN *F, GEN *G)
{
  GEN q,b,FF,GG;
  long n=lgef(p)-3,k,bitprec2,i, eq;
  double auxnorm;

  step4=1;
  auxnorm=(double) n*log2(1+exp2(mylog2((GEN)p[n+1])
				-mylog2((GEN)p[n+2]))/(double)n);
  bitprec2=bitprec+1+(long) (log2((double)n)+auxnorm);

  q=mygprec(p,bitprec2);
  b=gdivgs(gdiv((GEN)q[n+1],(GEN)q[n+2]),-n);
  q=shiftpol(q,gadd(polx[varn(p)],b));

  k=0; eq=gexpo(q);
  while
      (k <= n/2 && (gexpo((GEN)q[k+2]) < -(bitprec2+2*(n-k)+eq)
       || gcmp0((GEN)q[k+2]))) k++;
  if (k>0)
  {
    if (k>n/2) k=n/2;
    bitprec2+=(k<<1);
    FF=cgetg(k+3,t_POL); FF[1]=evalsigne(1)+evalvarn(varn(p))+evallgef(k+3);
    for (i=0; i<k; i++) FF[i+2]=zero;
    FF[k+2]=(long) mygprec(gunr,bitprec2);
    GG=cgetg(n-k+3,t_POL); GG[1]=evalsigne(1)+evalvarn(varn(p))+evallgef(n-k+3);
    for (i=0; i<=n-k; i++) GG[i+2]=q[i+k+2];
    b = gsub(polx[varn(p)],mygprec(b,bitprec2));
  }
  else
  {
    split_1(q,bitprec2,&FF,&GG);
    bitprec2 = bitprec+gexpo(FF)+gexpo(GG)-gexpo(p)+(long)auxnorm+1;
    b = gsub(polx[varn(p)],mygprec(b,bitprec2));
    FF = mygprec(FF,bitprec2);
  }
  GG = mygprec(GG,bitprec2);
  *F = shiftpol(FF,b);
  *G = shiftpol(GG,b);
}

/* put in F and G two polynomials such that |P-FG|<2^(-bitprec)|P|,
where the maximum modulus of the roots of p is <2 */
static void
split_0_1(GEN p, long bitprec, GEN *F, GEN *G)
{
  GEN q,FF,GG;
  long n=lgef(p)-3,bitprec2,normp,pow;
  double aux;

  normp=gexpo(p);
  aux=exp2(mylog2((GEN)p[n+1])-mylog2((GEN)p[n+2]))/(double)n;
  pow=2;
  if (aux<=2.5){ split_0_2(p,bitprec,F,G); return; }

  if (aux<=1.) pow=1;
  scalepol2n(p,pow); /* p <- 4^(-n) p(4*x) */
  bitprec2=bitprec+pow*n+gexpo(p)-normp;
  q=mygprec(p,bitprec2);
  split_1(q,bitprec2,&FF,&GG);
  scalepol2n(FF,-pow); scalepol2n(GG,-pow);
  bitprec2=bitprec+gexpo(FF)+gexpo(GG)-normp;
  *F=mygprec(FF,bitprec2); *G=mygprec(GG,bitprec2);
}

/* put in F and G two polynomials such that |P-FG|<2^(-bitprec)|P| */
static void
split_0(GEN p, long bitprec, GEN *F, GEN *G)
{
  GEN FF,GG,q,R;
  long n=lgef(p)-3,k=0,i;

  while (gexpo((GEN)p[k+2]) < -bitprec && k <= n/2) k++;
  if (k>0)
  {
    if (k>n/2) k=n/2;
    FF=cgetg(k+3,t_POL);
    FF[1]=evalsigne(1) | evalvarn(varn(p)) | evallgef(k+3);
    for (i=0; i<k; i++) FF[i+2]=lcopy(gzero);
    FF[k+2]=(long) mygprec(gunr,bitprec);
    GG=cgetg(n-k+3,t_POL);
    GG[1]=evalsigne(1) | evalvarn(varn(p)) | evallgef(n-k+3);
    for (i=0; i<=n-k; i++) GG[i+2]=p[i+k+2];
  }
  else
  {
    R = max_modulus(p,0.05);
    if (gexpo(R)<1 && gtodouble(R)<1.9) split_0_1(p,bitprec,&FF,&GG);
    else
    {
      q=cgetg(n+3,t_POL); q[1]=p[1];
      for (i=0; i<=n; i++) q[i+2]=p[n-i+2]; /* p^* with copy of ptr */
      R = max_modulus(q,0.05);
      if (gexpo(R)<1 && gtodouble(R)<1.9)
      {
	split_0_1(q,bitprec,&FF,&GG);
	FF=polrecip(FF); GG=polrecip(GG);
      }
      else
      {
	step4=0;
	split_2(p,bitprec,1.2837,&FF,&GG);
      }
    }
  }
  *F=FF; *G=GG;
}

/********************************************************************/
/**                                                                **/
/**     CALCUL A POSTERIORI DE L'ERREUR ABSOLUE SUR LES RACINES    **/
/**                                                                **/
/********************************************************************/

static GEN
root_error(long n, long k, GEN roots_pol, GEN sigma, GEN shatzle)
{
  GEN rho,d,eps,epsbis,eps2,prod,aux,rap=NULL;
  long i,j,m;

  d=cgetg(n+1,t_VEC);
  for (i=1; i<=n; i++)
  {
    if (i!=k)
    {
      aux=gsub((GEN)roots_pol[i],(GEN)roots_pol[k]);
      d[i]=(long) gabs(mygprec(aux,31),4);
    }
  }
  rho=gabs(mygprec((GEN)roots_pol[k],31),4);
  if (gcmp(rho,dbltor(1.))==-1) rho=gun;
  eps=gmul(rho,shatzle);
  aux=gmul(gpui(rho,stoi(n),4),sigma);

  for (j=1; j<=2 || (j<=5 && gcmp(rap,dbltor(1.2))==1); j++)
  {
    m=n; prod=gun;
    epsbis=gdivgs(gmulgs(eps,5),4);
    for (i=1; i<=n; i++)
    {
      if (i!=k && gcmp((GEN)d[i],epsbis)==1)
      {
	m--;
	prod=gmul(prod,gsub((GEN)d[i],eps));
      }
    }
    eps2=gdiv(gmul2n(aux,2*m-2),prod);
    eps2=gpui(eps2,dbltor(1./m),4);
    rap=gdiv(eps,eps2); eps=eps2;
  }
  return eps;
}

/* round a complex or real number x to an absolute value of 2^(-e) */
static GEN
mygprec_absolute(GEN x, long bitprec)
{
  long tx=typ(x),e;
  GEN y;

  switch(tx)
  {
    case t_REAL:
      e=gexpo(x);
      if (e<-bitprec || !signe(x)) { y=dbltor(0.); setexpo(y,-bitprec); }
      else y=mygprec(x,bitprec+e);
      break;
    case t_COMPLEX:
      if (gexpo((GEN)x[2])<-bitprec)
	y=mygprec_absolute((GEN)x[1],bitprec);
      else
      {
	y=cgetg(3,t_COMPLEX);
	y[1]=(long) mygprec_absolute((GEN)x[1],bitprec);
	y[2]=(long) mygprec_absolute((GEN)x[2],bitprec);
      }
      break;

    default: y=mygprec(x,bitprec);
  }
  return y;
}

static long
a_posteriori_errors(GEN p, GEN roots_pol, long err)
{
  GEN sigma,overn,shatzle,x;
  long i,n=lgef(p)-3,e,e_max;

  sigma = realun(3);
  setexpo(sigma,err+(long) log2((double) n)+1);
  overn=dbltor(1./n);
  shatzle=gdiv(gpui(sigma,overn,0),
	       gsub(gpui(gsub(gun,sigma),overn,0),
		    gpui(sigma,overn,0)));
  shatzle=gmul2n(shatzle,1); e_max=-pariINFINITY;
  for (i=1; i<=n; i++)
  {
    x=root_error(n,i,roots_pol,sigma,shatzle);
    e=gexpo(x); if (e>e_max) e_max=e;
    roots_pol[i]=(long) mygprec_absolute((GEN)roots_pol[i],-e);
  }
  return e_max;
}

/********************************************************************/
/**                                                                **/
/**                           MAIN                                 **/
/**                                                                **/
/********************************************************************/

/* compute roots in roots_pol so that |P-L_1...L_n|<2^(-bitprec)|P| , and
returns prod (x-roots_pol[i]) for i=1..degree(p) */
static GEN
split_complete(GEN p, long bitprec, GEN *roots_pol, long *iroots)
{
  long n=lgef(p)-3,decprec,ltop,lbot;
  GEN F,G,a,b,m1,m2,m;
  GEN *gptr[2];

  if (n==1)
  {
    a=gneg_i(gdiv((GEN)p[2],(GEN)p[3]));
    (*iroots)++; (*roots_pol)[*iroots]=(long) a;
    return p;
  }
  ltop=avma;
  if (n==2)
  {
    F=gsub(gsqr((GEN)p[3]),gmul2n(gmul((GEN)p[2],(GEN)p[4]),2));
    decprec=(long) ((double) bitprec * L2SL10)+1;
    F=gsqrt(F,decprec);
    a=gneg_i(gdiv(gadd((GEN)p[3],F),gmul2n((GEN)p[4],1)));
    b=gdiv(gsub(F,(GEN)p[3]),gmul2n((GEN)p[4],1));

    gptr[0]=&a; gptr[1]=&b;
    gerepilemany(ltop,gptr,2);
    (*iroots)++; (*roots_pol)[*iroots]=(long) a;
    (*iroots)++; (*roots_pol)[*iroots]=(long) b;
    m=gmul(gsub(polx[varn(p)],mygprec(a,3*bitprec)),
	   gsub(polx[varn(p)],mygprec(b,3*bitprec)));
    return gmul(m,(GEN)p[4]);
  }
  split_0(p,bitprec,&F,&G);
  m1=split_complete(F,bitprec,roots_pol,iroots);
  m2=split_complete(G,bitprec,roots_pol,iroots);
  lbot=avma;
  m=gmul(m1,m2); *roots_pol=gcopy(*roots_pol);
  gptr[0]=roots_pol; gptr[1]=&m;
  gerepilemanysp(ltop,lbot,gptr,2); return m;
}

/* compute a bound on the maximum modulus of roots of p */
static GEN
cauchy_bound(GEN p)
{
  long i,n=lgef(p)-3;
  GEN x=gzero,y,lc;

  lc=gabs((GEN)p[n+2],DEFAULTPREC); /* leading coefficient */
  lc=gdiv(dbltor(1.),lc);
  for (i=0; i<n; i++)
  {
    y=gmul(gabs((GEN) p[i+2],DEFAULTPREC),lc);
    y=gpui(y,dbltor(1./(n-i)),DEFAULTPREC);
    if (gcmp(y,x) > 0) x=y;
  }
  return x;
}

static GEN
mygprecrc_special(GEN x, long bitprec, long e)
{
  long tx=typ(x),lx,ex;
  GEN y;

  if (bitprec<=0) bitprec=0; /* should not happen */
  switch(tx)
  {
    case t_REAL:
      lx=bitprec/BITS_IN_LONG+3;
      if (lx<lg(x)) lx=lg(x);
      y=cgetr(lx); affrr(x,y); ex=-bitprec+e;
      if (!signe(x) && expo(x)>ex) setexpo(y,ex);
      break;
    case t_COMPLEX:
      y=cgetg(3,t_COMPLEX);
      y[1]=(long) mygprecrc_special((GEN)x[1],bitprec,e);
      y[2]=(long) mygprecrc_special((GEN)x[2],bitprec,e);
      break;
    default: y=gcopy(x);
  }
  return y;
}

/* like mygprec but keep at least the same precision as before */
static GEN
mygprec_special(GEN x, long bitprec)
{
  long tx=typ(x),lx,i,e;
  GEN y;

  switch(tx)
  {
    case t_POL:
      lx=lgef(x); y=cgetg(lx,tx); y[1]=x[1]; e=gexpo(x);
      for (i=2; i<lx; i++) y[i]=(long) mygprecrc_special((GEN)x[i],bitprec,e);
      break;

    default: y=mygprecrc_special(x,bitprec,0);
  }
  return y;
}

static GEN
all_roots(GEN p, long bitprec)
{
  GEN q,roots_pol,m;
  long bitprec2,n=lgef(p)-3,iroots,i,j,e,av,tetpil;

  roots_pol=cgetg(n+1,t_VEC); av=avma;
  for (i=1; i<=n; i++) roots_pol[i]=zero;
  for (j=1; j<=10; j++)
  {
    iroots=0; e = 2*gexpo(cauchy_bound(p)); if (e<0) e=0;
    bitprec2=bitprec+(1<<j)*n+gexpo(p)-gexpo((GEN)p[2+n])
      +(long) log2(n)+1+e;
    q=gmul(mygprec(gunr,bitprec2),mygprec(p,bitprec2));
    m=split_complete(q,bitprec2,&roots_pol,&iroots);
    e = gexpo(gsub(mygprec_special(p,bitprec2),m))
      - gexpo((GEN)q[2+n])+(long) log2((double)n)+1;
    if (e<-2*bitprec2) e=-2*bitprec2; /* to avoid e=-pariINFINITY */
    if (e < 0 && a_posteriori_errors(q,roots_pol,e) < -bitprec)
      return roots_pol;

    tetpil=avma; roots_pol=gerepile(av,tetpil,gcopy(roots_pol));
  }
  err(bugparier,"all_roots");
  return NULL; /* not reached */
}

/* true if x is an exact scalar, that is integer or rational */
static int
isexactscalar(GEN x)
{
  long tx=typ(x);
  return (tx==t_INT || is_frac_t(tx));
}

static int
isexactpol(GEN p)
{
  long i,n=lgef(p)-3;

  for (i=0; i<=n; i++)
    if (isexactscalar((GEN)p[i+2])==0) return 0;
  return 1;
}

static long
isvalidcoeff(GEN x)
{
  long tx=typ(x);

  switch(tx)
  {
    case t_INT: case t_REAL: case t_FRAC: case t_FRACN: return 1;
    case t_COMPLEX:
      if (isvalidcoeff((GEN)x[1]) && isvalidcoeff((GEN)x[2])) return 1;
  }
  return 0;
}

static long
isvalidpol(GEN p)
{
  long i,n = lgef(p);
  for (i=2; i<n; i++)
    if (!isvalidcoeff((GEN)p[i])) return 0;
  return 1;
}

static GEN
solve_exact_pol(GEN p, long bitprec)
{
  GEN S,ex,factors,roots_pol,roots_fact;
  long i,j,k,m,n,iroots;

  n=lgef(p)-3;

  iroots=0;
  roots_pol=cgetg(n+1,t_VEC); for (i=1; i<=n; i++) roots_pol[i]=zero;

  S=square_free_factorization(p);
  ex=(GEN) S[1]; factors=(GEN) S[2];
  for (i=1; i<lg(factors); i++)
  {
    roots_fact=all_roots((GEN)factors[i],bitprec);
    n=lgef(factors[i])-3; m=itos((GEN)ex[i]);
    for (j=1; j<=n; j++)
      for (k=1; k<=m; k++) roots_pol[++iroots] = roots_fact[j];
  }
  return roots_pol;
}

/* return the roots of p with absolute error bitprec */
static GEN
roots_com(GEN p, long l)
{
  long bitprec;

  if (typ(p)!=t_POL)
  {
    if (!isvalidcoeff(p)) err(typeer,"roots");
    return cgetg(1,t_VEC); /* constant polynomial */
  }
  if (!isvalidpol(p)) err(talker,"invalid coefficients in roots");
  if (lgef(p) == 3) return cgetg(1,t_VEC); /* constant polynomial */
  if (l<3) l=3;
  bitprec=bit_accuracy(l); gunr=realun(l);
  return isexactpol(p)? solve_exact_pol(p,bitprec): all_roots(p,bitprec);
}

static GEN
tocomplex(GEN x, long l)
{
  GEN y=cgetg(3,t_COMPLEX);

  y[1]=lgetr(l);
  if (typ(x) == t_COMPLEX)
    { y[2]=lgetr(l); gaffect(x,y); }
  else
    { gaffect(x,(GEN)y[1]); y[2]=(long)realzero(l); }
 return y;
}

/* Check if x is approximately real with precision e */
int
isrealappr(GEN x, long e)
{
  long tx=typ(x),lx,i;
  switch(tx)
  {
    case t_INT: case t_REAL: case t_FRAC: case t_FRACN:
      return 1;
    case t_COMPLEX:
      return (gexpo((GEN)x[2]) < e);
    case t_QUAD:
      err(impl,"isrealappr for type t_QUAD");
    case t_POL: case t_SER: case t_RFRAC: case t_RFRACN:
    case t_VEC: case t_COL: case t_MAT:
      lx = (tx==t_POL)?lgef(x): lg(x);
      for (i=lontyp[tx]; i<lx; i++)
        if (! isrealappr((GEN)x[i],e)) return 0;
      return 1;
    default: err(typeer,"isrealappr"); return 0;
  }
}

/* x,y sont de type t_COMPLEX */
static int
isconj(GEN x, GEN y, long e)
{
  return (gexpo( gsub((GEN)x[1],(GEN)y[1]) ) < e
       && gexpo( gadd((GEN)x[2],(GEN)y[2]) ) < e);
}

/* returns the vector of roots of p, with guaranteed absolute error
 * 2 ^ (- bit_accuracy(l))
 */
GEN
roots(GEN p, long l)
{
  long av,av1,tetpil,n,j,k,s;
  GEN p1,p2,p3,p22,res;

  if (gcmp0(p)) err(zeropoler,"roots");
  av=avma; p1=roots_com(p,l); n=lg(p1);
  if (n <= 1) return p1;
  if (isreal(p))
  {
    long e = 5 - bit_accuracy(l);
    p3=cgetg(n,t_COL); s=0;
    for (j=1; j<n; j++)
    {
      p2=(GEN)p1[j];
      if (typ(p2) != t_COMPLEX) { p3[++s]=(long)p2; p1[j]=zero; }
      else if (isrealappr(p2,e)) { p3[++s]=p2[1]; p1[j]=zero; }
    }
    setlg(p3,s+1); p2=sort(p3); setlg(p3,n);
    tetpil=avma; res=cgetg(n,t_COL);
    for (j=1; j<=s; j++) res[j]=(long)tocomplex((GEN)p2[j],l);
    for (j=1; j<n; j++)
    {
      p2=(GEN)p1[j];
      if (typ(p2) == t_COMPLEX)
      {
	res[++s]=(long)tocomplex(p2,l);
        av1=avma;
	for (k=j+1; k<n; k++)
	{
	  p22=(GEN)p1[k];
	  if (typ(p22) == t_COMPLEX && isconj(p2,p22,e))
          {
            avma=av1; res[++s]=(long)tocomplex(p22,l);
            p1[k]=zero; break;
          }
	}
	if (k==n) err(bugparier,"roots (conjugates)");
      }
    }
    return gerepile(av,tetpil,res);
  }
  tetpil=avma; res=cgetg(n,t_COL);
  for (j=1; j<n; j++) res[j]=(long)tocomplex((GEN)p1[j],l);
  return gerepile(av,tetpil,res);
}

GEN
roots0(GEN p, long flag,long l)
{
  switch(flag)
  {
    case 0: return roots(p,l);
    case 1: return rootsold(p,l);
    default: err(flagerr,"polroots");
  }
  return NULL; /* not reached */
}
