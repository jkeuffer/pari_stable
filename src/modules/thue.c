/* thue.c -- Thue equation solver. In all the forthcoming remarks, "paper"
 * designs the paper "Thue Equations of High Degree", by Yu. Bilu and
 * G. Hanrot, J. Number Theory (1996). Note that numbering of the constants
 * is that of Hanrot's thesis rather than that of the paper.
 * The last part of the program (bnfisintnorm) was written by K. Belabas.
 */
/* $Id$ */
#include "pari.h"

static int curne,r,s,t,deg,Prec,ConstPrec,numroot;
static GEN c1,c2,c3,c4,c5,c6,c7,c8,c10,c11,c12,c13,c14,c15,B0,x1,x2,x3,x0;
static GEN halpha,eps3,gdeg,A,MatNE,roo,MatFU,Delta,Lambda,delta,lambda;
static GEN Vect2,SOL,uftot;

GEN bnfisintnorm(GEN, GEN);

/* Check whether tnf is a valid structure */
static int
checktnf(GEN tnf)
{
  if (typ(tnf)!=t_VEC || (lg(tnf)!=8 && lg(tnf)!=3)) return 0;
  if (typ(tnf[1])!=t_POL) return 0;
  if (lg(tnf) != 8) return 1; /* s=0 */

  deg=lgef(tnf[1])-3;
  if (deg<=2) err(talker,"invalid polynomial in thue (need deg>2)");
  s=sturm((GEN)tnf[1]); t=(deg-s)>>1; r=s+t-1;
  (void)checkbnf((GEN)tnf[2]);
  if (typ(tnf[3]) != t_COL || lg(tnf[3]) != deg+1) return 0;
  if (typ(tnf[4]) != t_COL || lg(tnf[4]) != r+1) return 0;
  if (typ(tnf[5]) != t_MAT || lg(tnf[5]) != r+1
      || lg(gmael(tnf,5,1)) != deg+1) return 0;
  if (typ(tnf[6]) != t_MAT || lg(tnf[6])!=r+1
      || lg(gmael(tnf,6,1)) != r+1) return 0;
  if (typ(tnf[7]) != t_VEC || lg(tnf[7]) != 7) return 0;
  return 1;
}

static GEN distoZ(GEN z)
{
  GEN p1=gfrac(z);
  return gmin(p1, gsub(gun,p1));
}

/* Check whether a solution has already been found */
static int
_thue_new(GEN zz)
{
  int i;
  for (i=1; i<lg(SOL); i++)
    if (gegal(zz,(GEN)SOL[i])) return 0;
  return 1;
}

/* Compensates rounding errors for computation/display of the constants */
static GEN
myround(GEN Cst, GEN upd)
{
  return gmul(Cst, gadd(gun, gmul(upd,gpuigs(stoi(10),-10))));
}

/* Returns the index of the largest element in a vector */
static int
Vecmax(GEN Vec, int size)
{
  int k, tno = 1;
  GEN tmax = (GEN)Vec[1];
  for (k=2; k<=size; k++)
    if (gcmp((GEN)Vec[k],tmax)==1) { tmax=(GEN)Vec[k]; tno=k; }
  return tno;
}

/* Performs basic computations concerning the equation: buchinitfu, c1, c2 */
static void
inithue(GEN poly, long flag)
{
  GEN roo2, tmp, gpmin, de;
  int k,j;

  x0=gzero; x1=gzero; deg=lgef(poly)-3; gdeg=stoi(deg);

  if (!uftot)
  {
    uftot=bnfinit0(poly,1,NULL,Prec);
    if (flag) certifybuchall(uftot);
    s=itos(gmael3(uftot,7,2,1));
    t=itos(gmael3(uftot,7,2,2));
  }
  /* Switch the roots to get the usual order */
  roo=roots(poly, Prec); roo2=cgetg(deg+1,t_COL);
  for (k=1; k<=s; k++) roo2[k]=roo[k];
  for (k=1; k<=t; k++)
  {
    roo2[k+s]=roo[2*k-1+s];
    roo2[k+s+t]=lconj((GEN)roo2[k+s]);
  }
  roo=roo2;

  r=s+t-1; halpha=gun;
  for (k=1; k<=deg; k++)
    halpha = gmul(halpha,gmax(gun,gabs((GEN)roo[k],Prec)));
  halpha=gdiv(glog(halpha,Prec),gdeg);

  de=derivpol(poly); c1=gabs(poleval(de,(GEN)roo[1]),Prec);
  for (k=2; k<=s; k++)
  {
    tmp=gabs(poleval(de,(GEN)roo[k]),Prec);
    if (gcmp(tmp,c1)==-1) c1=tmp;
  }

  c1=gdiv(gpui(gdeux,gsub(gdeg,gun),Prec),c1); c1=myround(c1,gun);
  c2=gabs(gsub((GEN)roo[1],(GEN)roo[2]),Prec);

  for (k=1; k<=deg; k++)
    for (j=k+1; j<=deg; j++)
    {
      tmp=gabs(gsub((GEN)roo[j],(GEN)roo[k]),Prec);
      if (gcmp(c2,tmp)==1) c2=tmp;
    }

  c2=myround(c2,stoi(-1));
  if (t==0) x0=gun;
  else
  {
    gpmin=gabs(poleval(de,(GEN)roo[s+1]),Prec);
    for (k=2; k<=t; k++)
    {
      tmp=gabs(poleval(de,(GEN)roo[s+k]),Prec);
      if (gcmp(tmp,gpmin)==-1) gpmin=tmp;
    }

    /* Compute x0. See paper, Prop. 2.2.1 */
    x0=gpui(gdiv(gpui(gdeux,gsub(gdeg,gun),Prec),
                 gmul(gpmin,
		      gabs((GEN)gimag(roo)[Vecmax(gabs(gimag(roo),Prec),deg)],Prec))),
	    ginv(gdeg),Prec);
  }

  if (DEBUGLEVEL >=2) fprintferr("c1 = %Z\nc2 = %Z\n", c1, c2);

}

/* Computation of M, its inverse A and check of the precision (see paper) */
static void
T_A_Matrices()
{
  GEN mask, eps1, eps2, nia, m1, IntM;
  int i,j;

  m1=glog(gabs(MatFU,Prec),Prec); mask=gsub(gpui(gdeux,stoi(r),Prec),gun);
  m1=matextract(m1,mask,mask);

  A=invmat(m1); IntM=gsub(gmul(A,m1),idmat(r));

  eps2=gzero;
  for (i=1; i<=r; i++)
    for (j=1; j<=r; j++)
      if (gcmp(eps2,gabs(gcoeff(IntM,i,j),20)) == -1)
	eps2=gabs(gcoeff(IntM,i,j),20);

  eps1=gpui(gdeux,stoi((Prec-2)*32),Prec); eps2=gadd(eps2,ginv(eps1));

  nia=gzero;
  for (i=1; i<=r; i++)
    for (j=1; j<=r; j++)
      if (gcmp(nia,gabs(gcoeff(A,i,j),20)) == -1)
        nia = gabs(gcoeff(A,i,j),20);

  /* Check for the precision in matrix inversion. See paper, Lemma 2.4.2. */
  if (gcmp(gmul(gadd(gmul(stoi(r),gmul(nia,eps1)),eps2),
           gmul(gdeux,stoi(r))),gun) == -1)
    err(talker,"not enough precision in thue");

  eps3=gmul(gdeux,gmul(gmul(gsqr(stoi(r)),nia),
		       gadd(gmul(stoi(r),gdiv(nia,eps1)),eps2)));
  myround(eps3,gun);

  if (DEBUGLEVEL>=2) fprintferr("epsilon_3 -> %Z\n",eps3);
}

/* Computation of the constants c5, c7, c10, c12, c15 */
static void
ComputeConstants()
{
  int k;

  GEN Vect;

  Vect=cgetg(r+1,t_COL); for (k=1; k<=r; k++) Vect[k]=un;
  if (numroot <= r) Vect[numroot]=lsub(gun,gdeg);

  Delta=gmul(A,Vect);

  c5=(GEN)(gabs(Delta,Prec)[Vecmax(gabs(Delta,Prec),r)]);
  c5=myround(c5,gun); c7=mulsr(r,c5);
  c10=divsr(deg,c7); c13=divsr(deg,c5);


  if (DEBUGLEVEL>=2)
  {
    fprintferr("c5 = %Z\n",c5);
    fprintferr("c7 = %Z\n",c7);
    fprintferr("c10 = %Z\n",c10);
    fprintferr("c13 = %Z\n",c13);
  }
}

/* Computation of the constants c6, c8, c9 */
static void
ComputeConstants2(GEN poly, GEN rhs)
{
  GEN Vect1, tmp;
  int k;

  Vect1=cgetg(r+1,t_COL);
  for (k=1; k<=r; k++) Vect1[k]=un;
  Vect1=gmul(gabs(A,ConstPrec),Vect1);


  Vect2=cgetg(r+1,t_COL);
  for (k=1; k<=r; k++)
    { if (k!=numroot)
	{ Vect2[k]=llog(gabs(gdiv(gsub((GEN)roo[numroot],(GEN)roo[k]),
				  gcoeff(MatNE,k,curne)),Prec),Prec); }
      else { Vect2[k]=llog(gabs(gdiv(rhs,gmul(poleval(derivpol(poly)
						 ,(GEN)roo[numroot]),
					 gcoeff(MatNE,k,curne))),Prec),Prec);
      } 			
    }
  Lambda=gmul(A,Vect2);

  tmp=(GEN)Vect1[Vecmax(Vect1,r)];
  x2=gmax(x1,gpui(mulsr(10,mulrr(c4,tmp)),ginv(gdeg),ConstPrec));
  c14=mulrr(c4,tmp);

  c6=gabs((GEN)Lambda[Vecmax(gabs(Lambda,ConstPrec),r)],ConstPrec);
  c6=addrr(c6,dbltor(0.1)); c6=myround(c6,gun);

  c8=addrr(dbltor(1.23),mulsr(r,c6));
  c11=mulrr(mulsr(2,c3),gexp(divrr(mulsr(deg,c8),c7),ConstPrec));

  tmp=gexp(divrr(mulsr(deg,c6),c5),ConstPrec);
  c12=mulrr(mulsr(2,c3),tmp);
  c15=mulsr(2,mulrr(c14,tmp));

  if (DEBUGLEVEL>=2)
  {
    fprintferr("c6 = %Z\n",c6);
    fprintferr("c8 = %Z\n",c8);
    fprintferr("c11 = %Z\n",c11);
    fprintferr("c12 = %Z\n",c12);
    fprintferr("c14 = %Z\n",c14);
    fprintferr("c15 = %Z\n",c15);
  }
}

/* Computation of the logarithmic heights of the units */
static GEN
Logarithmic_Height(int s)
{
  int i;
  GEN LH=gun,mat;

  mat=gabs(MatFU,Prec);
  for (i=1; i<=deg; i++)
    LH = gmul(LH,gmax(gun,gabs(gcoeff(mat,i,s),Prec)));
  return gmul(gdeux,gdiv(glog(LH,Prec),gdeg));
}

/* Computation of the matrix ((\sigma_i(\eta_j)) used for M_1 and
   the computation of logarithmic heights */
static void
Compute_Fund_Units(GEN uf)
{
  int i,j;
  MatFU=cgetg(r+1,t_MAT);

  for (i=1; i<=r; i++)
    MatFU[i]=lgetg(deg+1,t_COL);
  for (i=1; i<=r; i++)
  {
    if (typ(uf[i])!=t_POL) err(talker,"incorrect system of units");
    for (j=1; j<=deg; j++)
      coeff(MatFU,j,i)=(long)poleval((GEN)uf[i],(GEN)roo[j]);
  }
}

/* Computation of the conjugates of the solutions to the norm equation */
static void
Conj_Norm_Eq(GEN ne, GEN *Hmu)
{
  int p,q,nesol,x;

  nesol=lg(ne); MatNE=(GEN)cgetg(nesol,t_MAT); (*Hmu)=cgetg(nesol,t_COL);

  for (p=1; p<nesol; p++) { MatNE[p]=lgetg(deg+1,t_COL); (*Hmu)[p]=un; }
  for (q=1; q<nesol; q++)
  {
    x=typ(ne[q]);
    if (x!=t_INT && x!=t_POL)
      err(talker,"incorrect solutions of norm equation");
    for (p=1; p<=deg; p++)
    {
      coeff(MatNE,p,q)=(long)poleval((GEN)ne[q],(GEN)roo[p]);
      /* Logarithmic height of the solutions of the norm equation */
      (*Hmu)[q]=lmul((GEN)(*Hmu)[q],gmax(gun,gabs(gcoeff(MatNE,p,q),Prec)));
    }
  }
  for (q=1; q<nesol; q++)
    (*Hmu)[q]=ldiv(glog((GEN)(*Hmu)[q],Prec),gdeg);
}

/* Compute Baker's bound c11, and B_0, the bound for the b_i's .*/
static void
Baker(GEN ALH, GEN Hmu)
{
  GEN c9=gun, gbak, hb0=gzero;
  int k,i1,i2;

  gbak = gmul(gmul(gdeg,gsub(gdeg,gun)),gsub(gdeg,gdeux));

  switch (numroot) {
  case 1: i1=2; i2=3; break;
  case 2: i1=1; i2=3; break;
  case 3: i1=1; i2=2; break;
  default: i1=1; i2=2; break;
  }

  /* For the symbols used for the computation of c11, see paper, Thm 2.3.1 */
  /* Compute h_1....h_r */
  for (k=1; k<=r; k++)
  {
    c9=gmul(c9,gmax((GEN)ALH[k],
		      gmax(ginv(gbak),
			   gdiv(gabs(glog(gdiv(gcoeff(MatFU,i1,k),
					       gcoeff(MatFU,i2,k)),
					  Prec),Prec),gbak))));
  }

  /* Compute a bound for the h_0 */
  hb0=gadd(gmul(stoi(4),halpha),gadd(gmul(gdeux,(GEN)Hmu[curne]),
                                     gmul(gdeux,glog(gdeux,Prec))));
  hb0=gmax(hb0,gmax(ginv(gbak),
                    gdiv(gabs(glog(gdiv(gmul(gsub((GEN)roo[numroot],
                                                  (GEN)roo[i2]),
                                             gcoeff(MatNE,i1,curne)),
                                        gmul(gsub((GEN)roo[numroot],
						  (GEN)roo[i1]),
                                             gcoeff(MatNE,i2,curne))),
                                   Prec),Prec),gbak)));
  c9=gmul(c9,hb0);
  /* Multiply c9 by the "constant" factor */
  c9=gmul(c9,gmul(gmul(gmul(stoi(18),mppi(Prec)),gpui(stoi(32),stoi(4+r),Prec)),
                  gmul(gmul(mpfact(r+3), gpowgs(gmul(gbak,stoi(r+2)), r+3)),
                         glog(gmul(gdeux,gmul(gbak,stoi(r+2))),Prec))));
  c9=myround(c9,gun);
  /* Compute B0 according to Lemma 2.3.3 */
  B0=gmax(gexp(gun,Prec),
	  mulsr(2,divrr(addrr(mulrr(c9,glog(divrr(c9,c10),ConstPrec)),
			      glog(c11,ConstPrec)),c10)));

  if (DEBUGLEVEL>=2) fprintferr("Baker -> %Z\nB0 -> %Z\n",c9,B0);
}

/* Compute delta and lambda */
static void
Create_CF_Values(int i1, int i2, GEN *errdelta)
{
  GEN eps5;

  if (r>1)
    {
      delta=divrr((GEN)Delta[i2],(GEN)Delta[i1]);
      eps5=mulrs(eps3,r);
      *errdelta=mulrr(addsr(1,delta),
		      divrr(eps5,subrr(gabs((GEN)Delta[i1],ConstPrec),eps5)));

      lambda=gdiv(gsub(gmul((GEN)Delta[i2],(GEN)Lambda[i1]),
		       gmul((GEN)Delta[i1],(GEN)Lambda[i2])),
		  (GEN)Delta[i1]);
    }
  else
    {
    GEN Pi2 = gmul2n(mppi(Prec),1);
      delta=gdiv(gcoeff(MatFU,2,1),gcoeff(MatFU,3,1));
    delta=gdiv(garg(delta,Prec),Pi2);
      *errdelta=gdiv(gpui(gdeux,stoi(-(Prec-2)*32+1),Prec),
		     gabs(gcoeff(MatFU,2,1),Prec));
      lambda=gmul(gdiv(gsub((GEN)roo[numroot],(GEN)roo[2]),
		       gsub((GEN)roo[numroot],(GEN)roo[3])),
		  gdiv(gcoeff(MatNE,3,curne),gcoeff(MatNE,2,curne)));
    lambda=gdiv(garg(lambda,Prec),Pi2);
  }
  if (DEBUGLEVEL>=2) outerr(*errdelta);
}

/* Try to reduce the bound through continued fractions; see paper. */
static int
CF_First_Pass(GEN kappa, GEN errdelta)
{
  GEN q,ql,qd,l0;

  if (gcmp(gmul(dbltor(0.1),gsqr(mulri(B0,kappa))),ginv(errdelta))==1)
  {
    return -1;
  }

  q=denom(bestappr(delta, mulir(kappa, B0))); ql=mulir(q,lambda);
  qd=gmul(q,delta); ql=gabs(subri(ql, ground(ql)),Prec);
  qd=gabs(mulrr(subri(qd,ground(qd)),B0),Prec);
  l0=subrr(ql,addrr(qd,divri(dbltor(0.1),kappa)));
  if (signe(l0) <= 0)
  {
    if (DEBUGLEVEL>=2)
      fprintferr("CF_First_Pass failed. Trying again with larger kappa\n");
    return 0;
  }

    if (r>1)
      B0=divrr(glog(divrr(mulir(q,c15),l0),ConstPrec),c13);
    else
    B0=divrr(glog(divrr(mulir(q,c11),mulrr(l0,gmul2n(mppi(ConstPrec),1))),ConstPrec),c10);

    if (DEBUGLEVEL>=2)
    fprintferr("CF_First_Pass successful !!\nB0 -> %Z\n",B0);
    return 1;
  }

/* Check whether a "potential" solution is truly a solution. */
static void
Check_Solutions(GEN xmay1, GEN xmay2, GEN poly, GEN rhs)
{
  GEN xx1, xx2, yy1, yy2, zz, u;

  yy1=ground(greal(gdiv(gsub(xmay2,xmay1), gsub((GEN)roo[1],(GEN)roo[2]))));
  yy2=gneg(yy1);

  xx1=greal(gadd(xmay1,gmul((GEN)roo[1],yy1)));
  xx2=gneg(xx1);

  if (gcmp(distoZ(xx1),dbltor(0.0001))==-1)
  {
    xx1=ground(xx1);
    if (!gcmp0(yy1))
    {
      if (gegal(gmul(poleval(poly,gdiv(xx1,yy1)),
		     gpui(yy1,gdeg,Prec)),(GEN)rhs))
      {
	zz=cgetg(2,t_VEC); u=cgetg(3,t_VEC);
	u[1]=(long)xx1; u[2]=(long)yy1; zz[1]=(long)u;
	if (_thue_new(u)) SOL=concatsp(SOL,zz);
      }
    }
    else if (gegal(gpui(xx1,gdeg,Prec),(GEN)rhs))
    {
      zz=cgetg(2,t_VEC); u=cgetg(3,t_VEC);
      u[1]=(long)xx1; u[2]=(long)gzero; zz[1]=(long)u;
      if (_thue_new(u)) SOL=concatsp(SOL,zz);
    }

    xx2=ground(xx2);
    if (!gcmp0(yy2))
    {
      if (gegal(gmul(poleval(poly,gdiv(xx2,yy2)),
		     gpui(yy2,gdeg,Prec)),(GEN)rhs))
      {
	zz=cgetg(2,t_VEC); u=cgetg(3,t_VEC);
	u[1]=(long)xx2; u[2]=(long)yy2; zz[1]=(long)u;
	if (_thue_new(u)) SOL=concatsp(SOL,zz);
      }
    }
    else if (gegal(gpui(xx2,gdeg,Prec),(GEN)rhs))
    {
      zz=cgetg(2,t_VEC); u=cgetg(3,t_VEC);
      u[1]=(long)xx2; u[2]=(long)gzero; zz[1]=(long)u;
      if (_thue_new(u)) SOL=concatsp(SOL,zz);
    }
  }
}

static GEN
GuessQi(GEN *q1, GEN *q2, GEN *q3)
{
  GEN C, Lat, eps;

  C=gpui(stoi(10),stoi(10),Prec);
  Lat=idmat(3); mael(Lat,1,3)=(long)C; mael(Lat,2,3)=lround(gmul(C,delta));
  mael(Lat,3,3)=lround(gmul(C,lambda));

  Lat=lllint(Lat);
  *q1=gmael(Lat,1,1); *q2=gmael(Lat,1,2); *q3=gmael(Lat,1,3);

  eps=gabs(gadd(gadd(*q1,gmul(*q2,delta)),gmul(*q3,lambda)),Prec);
  return(eps);
}

static void
TotRat()
{
  err(bugparier,"thue (totally rational case)");
}

/* Check for solutions under a small bound (see paper) */
static void
Check_Small(int bound, GEN poly, GEN rhs)
{
  GEN interm, xx, zz, u, maxr, tmp, ypot, xxn, xxnm1, yy;
  long av = avma, lim = stack_lim(av,1);
  int x, j, bsupy, y;
  double bndyx;

  maxr=gabs((GEN)roo[1],Prec); for(j=1; j<=deg; j++)
    { if(gcmp(tmp=gabs((GEN)roo[j],Prec),maxr)==1) maxr=tmp; }

  bndyx=gtodouble(gadd(gpui(gabs(rhs,Prec),ginv(gdeg),Prec),maxr));

  for (x=-bound; x<=bound; x++)
  {
    if (low_stack(lim,stack_lim(av,1)))
    {
      if(DEBUGMEM>1) err(warnmem,"Check_small");
      SOL = gerepileupto(av, gcopy(SOL));
    }
    if (x==0)
      {
	ypot=gmul(stoi(gsigne(rhs)),ground(gpui(gabs(rhs,0),ginv(gdeg),Prec)));
	if (gegal(gpui(ypot,gdeg,0),rhs))
	  {
	    zz=cgetg(2,t_VEC); u=cgetg(3,t_VEC);
	    u[1]=(long)ypot; u[2]=(long)gzero; zz[1]=(long)u;
	    if (_thue_new(u)) SOL=concatsp(SOL,zz);
	  }
	if (gegal(gpui(gneg(ypot),gdeg,0),rhs))
	  {
	    zz=cgetg(2,t_VEC); u=cgetg(3,t_VEC);
	    u[1]=(long)gneg(ypot); u[2]=(long)gzero; zz[1]=(long)u;
	    if (_thue_new(u)) SOL=concatsp(SOL,zz);
	  }
      }
    else
      {
	bsupy=(int)(x>0?bndyx*x:-bndyx*x);
	
	xx=stoi(x); xxn=gpui(xx,gdeg,Prec);
	interm=gsub((GEN)rhs,gmul(xxn,(GEN)poly[2]));

	/* Verifier ... */
	xxnm1=xxn; j=2;
	while(gcmp0(interm))
	  {
	    xxnm1=gdiv(xxnm1,xx);
	    interm=gmul((GEN)poly[++j],xxnm1);
	  }

	for(y=-bsupy; y<=bsupy; y++)
	  {
	    yy=stoi(y);
	    if(y==0) {
	      if (gegal(gmul((GEN)poly[2],xxn),rhs))
		{
		  zz=cgetg(2,t_VEC); u=cgetg(3,t_VEC);
		  u[1]=(long)gzero; u[2]=(long)xx; zz[1]=(long)u;
		  if (_thue_new(u)) SOL=concatsp(SOL,zz);
		}	
	    }
	     else if (gcmp0(gmod(interm,yy)))
	       if(gegal(poleval(poly,gdiv(yy,xx)),gdiv(rhs,xxn)))
		/* Remplacer par un eval *homogene* */
		 {
		   zz=cgetg(2,t_VEC); u=cgetg(3,t_VEC);
		   u[1]=(long)yy; u[2]=(long)xx; zz[1]=(long)u;
		   if (_thue_new(u)) SOL=concatsp(SOL,zz);
		}
	  }
      }
  }
}

/* Computes [x]! */
static double
fact(double x)
{
  double ft=1.0;
  x=(int)x; while (x>1) { ft*=x; x--; }
  return ft ;
}

/* From a polynomial and optionally a system of fundamental units for the
 * field defined by poly, computes all the relevant constants needed to solve
 * the equation P(x,y)=a whenever the solutions of N_{ K/Q }(x)=a.  Returns a
 * "tnf" structure containing
 *  1) the polynomial
 *  2) the bnf (used to solve the norm equation)
 *  3) roots, with presumably enough precision
 *  4) The logarithmic heights of units
 *  5) The matrix of conjugates of units
 *  6) its inverse
 *  7) a few technical constants
 */
GEN
thueinit(GEN poly, long flag, long prec)
{
  GEN thueres,ALH,csts,c0;
  long av,tetpil,k,st;
  double d,dr;

  av=avma;

  uftot=0;
  if (checktnf(poly)) { uftot=(GEN)poly[2]; poly=(GEN)poly[1]; }
  else
    if (typ(poly)!=t_POL) err(notpoler,"thueinit");

  if (!gisirreducible(poly)) err(redpoler,"thueinit");
  st=sturm(poly);
  if (st)
  {
    dr=(double)((st+lgef(poly)-5)>>1);
    d=(double)lgef(poly)-3; d=d*(d-1)*(d-2);
    /* Try to guess the precision by approximating Baker's bound.
     * Note that the guess is most of the time pretty generous,
     * ie 10 to 30 decimal digits above what is *really* necessary.
     * Note that the limiting step is the reduction. See paper.
     */
    Prec=3 + (long)((5.83 + (dr+4)*5 + log(fact(dr+3)) + (dr+3)*log(dr+2) +
		     (dr+3)*log(d) + log(log(2*d*(dr+2))) + (dr+1)) / 10.);
    ConstPrec=4;
    if (Prec<prec) Prec = prec;
    if (!checktnf(poly)) inithue(poly,flag);

    thueres=cgetg(8,t_VEC);
    thueres[1]=(long)poly;
    thueres[2]=(long)uftot;
    thueres[3]=(long)roo;
    Compute_Fund_Units(gmael(uftot,8,5));
    ALH=cgetg(r+1,t_COL);
    for (k=1; k<=r; k++) ALH[k]=(long)Logarithmic_Height(k);
    thueres[4]=(long)ALH;
    thueres[5]=(long)MatFU;
    T_A_Matrices();
    thueres[6]=(long)A;

    csts=cgetg(7,t_VEC);
    csts[1]=(long)c1; csts[2]=(long)c2; csts[3]=(long)halpha;
    csts[4]=(long)x0; csts[5]=(long)eps3;
    csts[6]=(long)stoi(Prec);

    thueres[7]=(long)csts; tetpil=avma;
    return gerepile(av,tetpil,gcopy(thueres));
  }

  thueres=cgetg(3,t_VEC); c0=gun; Prec=4;
  roo=roots(poly,Prec);
  for (k=1; k<lg(roo); k++)
    c0=gmul(c0, gimag((GEN)roo[k]));
  c0=ginv(gabs(c0,Prec));
  thueres[1]=(long)poly; thueres[2]=(long)c0;
  tetpil=avma; return gerepile(av,tetpil,gcopy(thueres));
}

/* Given a tnf structure as returned by thueinit, and a right-hand-side and
 * optionally the solutions to the norm equation, returns the solutions to
 * the Thue equation F(x,y)=a
 */
GEN
thue(GEN thueres, GEN rhs, GEN ne)
{
  GEN Kstart,Old_B0,ALH,errdelta,Hmu,c0,poly,csts,bd;
  GEN xmay1,xmay2,b,zp1,tmp,q1,q2,q3,ep;
  long Nb_It=0,upb,bi1,av,tetpil,i1,i2,i, flag,cf,fs;

  if (!checktnf(thueres)) err(talker,"not a tnf in thue");

  av=avma; SOL=cgetg(1,t_VEC);

  if (lg(thueres)==8)
  {
    poly=(GEN)thueres[1]; deg=lgef(poly)-3; gdeg=stoi(deg);
    uftot=(GEN)thueres[2];
    roo=gcopy((GEN)thueres[3]);
    ALH=(GEN)thueres[4];
    MatFU=gcopy((GEN)thueres[5]);
    A=gcopy((GEN)thueres[6]);
    csts=(GEN)thueres[7];

    if (!ne) ne = bnfisintnorm(uftot, rhs);
    if (lg(ne)==1) { avma=av; return cgetg(1,t_VEC); }

    c1=gmul(gabs(rhs,Prec), (GEN)csts[1]); c2=(GEN)csts[2];
    halpha=(GEN)csts[3];
    if (t)
      x0 = gmul((GEN)csts[4],gpui(gabs(rhs,Prec), ginv(gdeg), Prec));
    eps3=(GEN)csts[5];
    Prec=gtolong((GEN)csts[6]);
    b=cgetg(r+1,t_COL);
    tmp=divrr(c1,c2);
    x1=gmax(x0,gpui(mulsr(2,tmp),ginv(gdeg),ConstPrec));
    if(DEBUGLEVEL >=2) fprintferr("x1 -> %Z\n",x1);

    c3=mulrr(dbltor(1.39),tmp);
    c4=mulsr(deg-1,c3);

    for (numroot=1; numroot<=s; numroot++)
    {
      ComputeConstants();
      Conj_Norm_Eq(ne,&Hmu);
      for (curne=1; curne<lg(ne); curne++)
      {
	ComputeConstants2(poly,rhs);
	Baker(ALH,Hmu);
	
	i1=Vecmax(gabs(Delta,Prec),r);
	if (i1!=1) i2=1; else i2=2;
	do
	  {
	    fs=0; 	
	    Create_CF_Values(i1,i2,&errdelta);
	    if (DEBUGLEVEL>=2) fprintferr("Entering CF\n");
	    Old_B0=gmul(B0,gdeux);

	    /* Try to reduce B0 while
	     * 1) there was less than 10 reductions
	     * 2) the previous reduction improved the bound of more than 0.1.
	     */
	    while (Nb_It<10 && gcmp(Old_B0,gadd(B0,dbltor(0.1))) == 1 && fs<2)
	      {
		cf=0; Old_B0=B0; Nb_It++; Kstart=stoi(10);
		while (!fs && CF_First_Pass(Kstart,errdelta) == 0 && cf < 8 )
		  {
		    cf++;
		    Kstart=mulis(Kstart,10);
		  }	
		if ( CF_First_Pass(Kstart,errdelta) == -1 )
		  { ne = gerepileupto(av, gcopy(ne)); Prec+=10;
		  if(DEBUGLEVEL>=2) fprintferr("Increasing precision\n");
		  thueres=thueinit(thueres,0,Prec);
		  return(thue(thueres,rhs,ne)); }

		if (cf==8 || fs) /* Semirational or totally rational case */
		  {
		    if (!fs)
		      { ep=GuessQi(&q1,&q2,&q3); }
		    bd=gmul(denom(bestappr(delta,gadd(B0,gabs(q2,Prec))))
			    ,delta);
		    bd=gabs(gsub(bd,ground(bd)),Prec);
		    if(gcmp(bd,ep)==1 && !gcmp0(q3))
		      {
			fs=1;
                      B0=gdiv(glog(gdiv(gmul(q3,c15),gsub(bd,ep)), Prec),c13);
			if (DEBUGLEVEL>=2)
                        fprintferr("Semirat. reduction ok. B0 -> %Z\n",B0);
		      }
		    else fs=2;
		  }
		else fs=0;
		Nb_It=0; B0=gmin(Old_B0,B0); upb=gtolong(gceil(B0));
	      }
	    i2++; if (i2==i1) i2++;
	  }
	while (fs == 2 && i2 <= r);
	
	if (fs == 2) TotRat();

	if (DEBUGLEVEL >=2) fprintferr("x2 -> %Z\n",x2);

      /* For each possible value of b_i1, compute the b_i's
       * and 2 conjugates of x-\alpha y. Then check.
       */
	zp1=dbltor(0.01);
	x3=gmax(x2,gpui(mulsr(2,divrr(c14,zp1)),ginv(gdeg),ConstPrec));

	for (bi1=-upb; bi1<=upb; bi1++)
	{
	  flag=1;
	  xmay1=gun; xmay2=gun;
	  for (i=1; i<=r; i++)
	  {
	    b[i]=(long)gdiv(gsub(gmul((GEN)Delta[i],stoi(bi1)),
	                          gsub(gmul((GEN)Delta[i],(GEN)Lambda[i1]),
				       gmul((GEN)Delta[i1],(GEN)Lambda[i]))),
			     (GEN)Delta[i1]);
	    if (gcmp(distoZ((GEN)b[i]),zp1)==1) { flag=0; break; }
	  }
	
	  if(flag)
	    {
	      for(i=1; i<=r; i++)
		{
		  b[i]=lround((GEN)b[i]);
		  xmay1=gmul(xmay1,gpui(gcoeff(MatFU,1,i),(GEN)b[i],Prec));
		  xmay2=gmul(xmay2,gpui(gcoeff(MatFU,2,i),(GEN)b[i],Prec));
		}
	      xmay1=gmul(xmay1,gcoeff(MatNE,1,curne));
	      xmay2=gmul(xmay2,gcoeff(MatNE,2,curne));
	      Check_Solutions(xmay1,xmay2,poly,rhs);
	    }
	}
      }
    }
    if (DEBUGLEVEL>=2) fprintferr("Checking for small solutions\n");
    Check_Small((int)(gtodouble(x3)),poly,rhs);
    tetpil=avma; return gerepile(av,tetpil,gcopy(SOL));
  }

  /* Case s=0. All the solutions are "small". */
  Prec=DEFAULTPREC; poly=(GEN)thueres[1]; deg=lgef(poly)-3;
  gdeg=stoi(deg); c0=(GEN)thueres[2];
  roo=roots(poly,Prec);
  Check_Small(gtolong(ground(gpui(gmul((GEN)poly[2],gdiv(gabs(rhs,Prec),c0)),
                                  ginv(gdeg),Prec) )), poly, rhs);
  tetpil=avma; return gerepile(av,tetpil,gcopy(SOL));
}

static GEN *Relations; /* primes above a, expressed on generators of Cl(K) */
static GEN *Partial;   /* list of vvectors, Partial[i] = Relations[1..i] * u[1..i] */
static GEN *gen_ord;   /* orders of generators of Cl(K) given in bnf */

static long *f;        /* f[i] = f(Primes[i]/p), inertial degree */
static long *n;        /* a = prod p^{ n_p }. n[i]=n_p if Primes[i] divides p */
static long *inext;    /* index of first P above next p, 0 if p is last */
static long *S;        /* S[i] = n[i] - sum_{ 1<=k<=i } f[k].u[k] */
static long *u;        /* We want principal ideals I = prod Primes[i]^u[i] */
static long **normsol; /* lists of copies of the u[] which are solutions */

static long Nprimes; /* length(Relations) = #{max ideal above divisors of a} */
static long sindex, smax; /* current index in normsol; max. index */

/* u[1..i] has been filled. Norm(u) is correct.
 * Check relations in class group then save it.
 */
static void
test_sol(long i)
{
  long k,*sol;

  if (Partial)
  {
    long av=avma;
    for (k=1; k<lg(Partial[1]); k++)
      if ( signe(modii( (GEN)Partial[i][k], gen_ord[k] )) )
        { avma=av; return; }
    avma=av;
  }
  if (sindex == smax)
  {
    long new_smax = smax << 1;
    long **new_normsol = (long **) new_chunk(new_smax+1);

    for (k=1; k<=smax; k++) new_normsol[k] = normsol[k];
    normsol = new_normsol; smax = new_smax;
  }
  sol = cgetg(Nprimes+1,t_VECSMALL);
  normsol[++sindex] = sol;

  for (k=1; k<=i; k++) sol[k]=u[k];
  for (   ; k<=Nprimes; k++) sol[k]=0;
  if (DEBUGLEVEL > 2)
  {
    fprintferr("sol = %Z\n",sol);
    if (Partial) fprintferr("Partial = %Z\n",Partial);
    flusherr();
  }
}
static void
fix_Partial(long i)
{
  long k, av = avma;
  for (k=1; k<lg(Partial[1]); k++)
    addiiz(
      (GEN) Partial[i-1][k],
            mulis((GEN) Relations[i][k], u[i]),
      (GEN) Partial[i][k]
    );
  avma=av;
}

/* Recursive loop. Suppose u[1..i] has been filled
 * Find possible solutions u such that, Norm(prod Prime[i]^u[i]) = a, taking
 * into account:
 *  1) the relations in the class group if need be.
 *  2) the factorization of a.
 */
static void
isintnorm_loop(long i)
{
  if (S[i] == 0) /* sum u[i].f[i] = n[i], do another prime */
  {
    int k;
    if (inext[i] == 0) { test_sol(i); return; }

    /* there are some primes left */
    if (Partial) gaffect(Partial[i], Partial[inext[i]-1]);
    for (k=i+1; k < inext[i]; k++) u[k]=0;
    i=inext[i]-1;
  }
  else if (i == inext[i]-2 || i == Nprimes-1)
  {
    /* only one Prime left above prime; change prime, fix u[i+1] */
    if (S[i] % f[i+1]) return;
    i++; u[i] = S[i-1] / f[i];
    if (Partial) fix_Partial(i);
    if (inext[i]==0) { test_sol(i); return; }
  }

  i++; u[i]=0;
  if (Partial) gaffect(Partial[i-1], Partial[i]);
  if (i == inext[i-1])
  { /* change prime */
    if (inext[i] == i+1 || i == Nprimes) /* only one Prime above p */
    {
      S[i]=0; u[i] = n[i] / f[i]; /* we already know this is exact */
      if (Partial) fix_Partial(i);
    }
    else S[i] = n[i];
  }
  else S[i] = S[i-1]; /* same prime, different Prime */
  for(;;)
  {
    isintnorm_loop(i); S[i]-=f[i]; if (S[i]<0) break;
    if (Partial)
      gaddz(Partial[i], Relations[i], Partial[i]);
    u[i]++;
  }
}

static void
get_sol_abs(GEN bnf, GEN a, GEN **ptPrimes)
{
  GEN dec, fact, primes, *Primes, *Fact;
  long *gcdlist, gcd,nprimes,Ngen,i,j;

  if (gcmp1(a))
  {
    long *sol = new_chunk(Nprimes+1);
    sindex = 1; normsol = (long**) new_chunk(2);
    normsol[1] = sol; for (i=1; i<=Nprimes; i++) sol[i]=0;
    return;
  }

  fact=factor(a); primes=(GEN)fact[1];
  nprimes=lg(primes)-1; sindex = 0;
  gen_ord = (GEN *) mael3(bnf,8,1,2); Ngen = lg(gen_ord)-1;

  Fact = (GEN*) new_chunk(1+nprimes);
  gcdlist = new_chunk(1+nprimes);

  Nprimes=0;
  for (i=1; i<=nprimes; i++)
  {
    long ldec;

    dec = primedec(bnf,(GEN)primes[i]); ldec = lg(dec)-1;
    gcd = itos(gmael(dec,1,4));

    /* check that gcd_{P|p} f_P | n_p */
    for (j=2; gcd>1 && j<=ldec; j++)
      gcd = cgcd(gcd,itos(gmael(dec,j,4)));

    gcdlist[i]=gcd;

    if (gcd != 1 && smodis(gmael(fact,2,i),gcd))
    {
      if (DEBUGLEVEL>2)
        { fprintferr("gcd f_P  does not divide n_p\n"); flusherr(); }
      return;
    }
    Fact[i] = dec; Nprimes += ldec;
  }

  f = new_chunk(1+Nprimes); u = new_chunk(1+Nprimes);
  n = new_chunk(1+Nprimes); S = new_chunk(1+Nprimes);
  inext = new_chunk(1+Nprimes);
  Primes = (GEN*) new_chunk(1+Nprimes);
  *ptPrimes = Primes;

  if (Ngen)
  {
    Partial = (GEN*) new_chunk(1+Nprimes);
    Relations = (GEN*) new_chunk(1+Nprimes);
  }
  else /* trivial class group, no relations to check */
    Relations = Partial = NULL;

  j=0;
  for (i=1; i<=nprimes; i++)
  {
    long k,lim,v, vn=itos(gmael(fact,2,i));

    gcd = gcdlist[i];
    dec = Fact[i]; lim = lg(dec);
    v = (i==nprimes)? 0: j + lim;
    for (k=1; k < lim; k++)
    {
      j++; Primes[j] = (GEN)dec[k];
      f[j] = itos(gmael(dec,k,4)) / gcd;
      n[j] = vn / gcd; inext[j] = v;
      if (Partial)
	Relations[j] = isprincipal(bnf,Primes[j]);
    }
  }
  if (Partial)
  {
    for (i=1; i <= Nprimes; i++)
      if (!gcmp0(Relations[i])) break;
    if (i > Nprimes) Partial = NULL; /* all ideals dividing a are principal */
  }
  if (Partial)
    for (i=0; i<=Nprimes; i++) /* Partial[0] needs to be initialized */
    {
      Partial[i]=cgetg(Ngen+1,t_COL);
      for (j=1; j<=Ngen; j++)
      {
	Partial[i][j]=lgeti(4);
	gaffect(gzero,(GEN) Partial[i][j]);
      }
    }
  smax=511; normsol = (long**) new_chunk(smax+1);
  S[0]=n[1]; inext[0]=1; isintnorm_loop(0);
}

static long
get_unit_1(GEN bnf, GEN pol, GEN *unit)
{
  GEN fu;
  long j;

  if (DEBUGLEVEL > 2)
    fprintferr("looking for a fundamental unit of norm -1\n");

  *unit = gmael3(bnf,8,4,2);  /* torsion unit */
  if (signe( gnorm(gmodulcp(*unit,pol)) ) < 0) return 1;

  fu = gmael(bnf,8,5); /* fundamental units */
  for (j=1; j<lg(fu); j++)
  {
    *unit = (GEN)fu[j];
    if (signe( gnorm(gmodulcp(*unit,pol)) ) < 0) return 1;
  }
  return 0;
}

GEN
bnfisintnorm(GEN bnf, GEN a)
{
  GEN nf,pol,res,unit,x,id, *Primes;
  long av = avma, tetpil,sa,i,j,norm_1;

  bnf = checkbnf(bnf); nf = (GEN)bnf[7]; pol = (GEN)nf[1];
  if (typ(a)!=t_INT)
    err(talker,"expected an integer in bnfisintnorm");
  sa = signe(a);
  if (sa == 0)  { res=cgetg(2,t_VEC); res[1]=zero; return res; }
  if (gcmp1(a)) { res=cgetg(2,t_VEC); res[1]=un;   return res; }

  get_sol_abs(bnf, absi(a), &Primes);

  res = cgetg(1,t_VEC); unit = NULL;
  for (i=1; i<=sindex; i++)
  {
    id = gun; x = normsol[i];
    for (j=1; j<=Nprimes; j++) /* compute prod Primes[i]^u[i] */
      if (x[j])
      {
	GEN id2 = Primes[j];
	if (x[j] != 1) id2 = idealpow(nf,id2, stoi(x[j]));
	id = idealmul(nf,id,id2);
      }
    x = (GEN) isprincipalgenforce(bnf,id)[2];
    x = gmul((GEN)nf[7],x); /* x possible solution */
    if (signe(gnorm(gmodulcp(x,(GEN)nf[1]))) != sa)
    {
      if (! unit) norm_1 = get_unit_1(bnf,pol,&unit);
      if (norm_1) x = gmul(unit,x);
      else
      {
        if (DEBUGLEVEL > 2)
          fprintferr("%Z eliminated because of sign\n",x);
        x = NULL;
      }
    }
    if (x) res = concatsp(res, gmod(x,pol));
  }
  tetpil=avma; return gerepile(av,tetpil,gcopy(res));
}
