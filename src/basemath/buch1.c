/*******************************************************************/
/*                                                                 */
/*         CLASS GROUP AND REGULATOR (McCURLEY, BUCHMANN)          */
/*                   QUADRATIC FIELDS                              */
/*                                                                 */
/*******************************************************************/
/* $Id$ */
#include "pari.h"

/* See buch2.c:
 * precision en digits decimaux=2*(#digits decimaux de Disc)+50
 * on prendra les p decomposes tels que prod(p)>lim dans la subbase
 * LIMC=Max(c.(log(Disc))^2,exp((1/8).sqrt(log(Disc).loglog(Disc))))
 * LIMC2=Max(6.(log(Disc))^2,exp((1/8).sqrt(log(Disc).loglog(Disc))))
 * subbase contient les p decomposes tels que prod(p)>sqrt(Disc)
 * lgsub=subbase[0]=#subbase;
 * subfactorbase est la table des form[p] pour p dans subbase
 * nbram est le nombre de p divisant Disc elimines dans subbase
 * powsubfactorbase est la table des puissances des formes dans subfactorbase
 */
#define HASHT 1024
static const long CBUCH = 15; /* of the form 2^k-1 */
static const long randshift=BITS_IN_RANDOM-1 - 4; /* BITS_IN_RANDOM-1-k */

static long sens,KC,KC2,lgsub,limhash,RELSUP,PRECREG;
static long *primfact,*primfact1, *exprimfact,*exprimfact1, *badprim;
static long *factorbase,*numfactorbase, *subbase, *vectbase, **hashtab;
static GEN  **powsubfactorbase,vperm,subfactorbase,Disc,sqrtD,isqrtD;

GEN buchquad(GEN D, double c, double c2, long RELSUP0, long flag, long prec);
GEN roots_to_pol_intern(GEN L, GEN a, long v, int plus);

GEN
quadclassunit0(GEN x, long flag, GEN data, long prec)
{
  long lx,RELSUP0;
  double cbach, cbach2;

  if (!data) lx=1;
  else
  {
    lx = lg(data);
    if (typ(data)!=t_VEC || lx > 7)
      err(talker,"incorrect parameters in quadclassunit");
    if (lx > 4) lx = 4;
  }
  cbach = cbach2 = 0.1; RELSUP0 = 5;
  switch(lx)
  {
    case 4: RELSUP0 = itos((GEN)data[3]);
    case 3: cbach2 = gtodouble((GEN)data[2]);
    case 2: cbach  = gtodouble((GEN)data[1]);
  }
  return buchquad(x,cbach,cbach2,RELSUP0,flag,prec);
}

/*******************************************************************/
/*******************************************************************/
/*                                                                 */
/*     Corps de classe de Hilbert et de rayon avec CM (Schertz)    */
/*                                                                 */
/*******************************************************************/
/*******************************************************************/

int
isoforder2(GEN form)
{
  GEN a=(GEN)form[1],b=(GEN)form[2],c=(GEN)form[3];
  return !signe(b) || absi_equal(a,b) || egalii(a,c);
}

/* returns an equation for the Hilbert class field of the imaginary
 *  quadratic field of discriminant D if flag=0, a vector of
 *  two-component vectors [form,g(form)] where g() is the root of the equation
 *  if flag is non-zero.
 */
static GEN
quadhilbertimag(GEN D, GEN flag)
{
  long av=avma,a,b,c,d,dover3,b2,t,h,h2,ell,l,i,i1,i2,ex,prec;
  GEN z,form,L,LG,y,res,ga1,ga2,ga3,ga4,wp,court,p1,p2,qf1,qf2;
  GEN u1,u2,u,w,ag,bg,al,ag2,wlf;
  byteptr p = diffptr;
  int raw = ((typ(flag)==t_INT && signe(flag)));

  if (DEBUGLEVEL>=2) timer2();
  if (gcmpgs(D,-11)>=0) return polx[0];
  d=itos(D); L=cgetg(1,t_VEC);
  b2 = b = (d&1)?1:0; h=h2=0; z=gun; dover3=labs(d)/3;
  while (b2 <= dover3)
  {
    t=(b2-d)/4;
    for (a=b?b:1; a*a<=t; a++)
      if (t%a==0)
      {
	h++; c = t/a; z = mulsi(a,z);
        L = concatsp(L, qfi(stoi(a),stoi(b),stoi(c)));
	if (b && a != b && a*a != t)
	{
	  h++;
          L = concatsp(L, qfi(stoi(a),stoi(-b),stoi(c)));
	}
	else h2++;
      }
    b+=2; b2=b*b;
  }
  if (h==1) {avma=av; return polx[0];}
  if (DEBUGLEVEL>=2) msgtimer("class number = %ld",h);
  wp=cgetg(1,t_VEC); wlf=cgetg(1,t_VEC); court=stoi(5);
  if (typ(flag)==t_VEC)
  {
    for (i=1; i<lg(flag); i++)
    {
      ell=itos((GEN)flag[i]);
      if (smodis(z,ell) && kross(d,ell) > 0)
      {
	court[2]=ell; form=redimag(primeform(D,court,0));
	if (!gcmp1((GEN)form[1]))
	{
	  wp = concat(wp,court); wlf = concat(wlf,form);
	}
      }
    }
  }
  else
  {
    ell=0; ell += *p++; ell+= *p++;
    while (lg(wp)<=2 || ell<=300)
    {
      ell += *p++; if (!*p) err(primer1);
      if (smodis(z,ell) && kross(d,ell) > 0)
      {
	court[2]=ell; form=redimag(primeform(D,court,0));
	if (!gcmp1((GEN)form[1]))
	{
	  wp = concat(wp,court); wlf = concat(wlf,form);
	}
      }
    }
  }
  l = lg(wp)-1;
  if (l<2) { avma=av; return gzero; }
  if (typ(flag)==t_VEC) { i1=1; i2=2; p1=(GEN)wp[1]; }
  else
  {
    for(i=1; i<=l; i++)
      if (smodis((GEN)wp[i],3) == 1) break;
    i1=(i>l)?1:i; p1=(GEN)wp[i1]; form=(GEN)wlf[i1];
    if (isoforder2(form))
    {
      if (smodis(p1,4)==3)
      {
	for (i=1; i<=l && (smodis((GEN)wp[i],4) == 3 ||
	     (isoforder2((GEN)wlf[i]) && !gegal((GEN)wlf[i],form))); i++);
	if (i>l)
	{
	  for (i=1; i<=l && isoforder2((GEN)wlf[i]) && !gegal((GEN)wlf[i],form) ;i++);
	  if (i>l) { avma=av; return gzero; }
	}
      }
      else
      {
	for (i=1; i<=l && isoforder2((GEN)wlf[i]) && !gegal((GEN)wlf[i],form); i++);
	if (i>l) { avma=av; return gzero; }
      }
    }
    else
    {
      if (smodis(p1,4)==3)
      {
	for(i=1; i<=l; i++)
	  if (smodis((GEN)wp[i],4) == 1) break;
	if (i>l) i=1;
      }
      else i=1;
    }
    i2=i;
  }
  qf1 = primeform(D,p1,0); u1 = gmodulcp((GEN)qf1[2],shifti(p1,1));
  p2 = (GEN)wp[i2];
  qf2 = primeform(D,p2,0); u2 = gmodulcp((GEN)qf2[2],shifti(p2,1));
  ex=24/itos(ggcd(mulii(subis(p1,1),subis(p2,1)),stoi(24)));
  if(DEBUGLEVEL>=2)
    fprintferr("p1 = %Z, p2 = %Z, ex = %ld\n",p1,p2,ex);
  if (!egalii(p1,p2)) u=lift(chinois(u1,u2));
  else
  {
    if (!gegal(qf1,qf2)) err(bugparier,"quadhilbertimag (p1=p1, qf1!=qf2)");
    u=(GEN)compimagraw(qf1,qf2)[2];
  }
  u = gmodulcp(u, shifti(mulii(p1,p2),1));
  LG = cgetg(h+1,t_VEC); 
  prec = raw? DEFAULTPREC: 3;
  for(;;)
  {
    long av0 = avma, e, emax = 0;
    GEN lead, sqd = gsqrt(negi(D),prec);
    for (i=1; i<=h; i++)
    {
      form=(GEN)L[i];
      ag=(GEN)form[1]; ag2=shifti(ag,1);
      bg=(GEN)form[2];
      w = lift(chinois(gmodulcp(negi(bg),ag2), u));
      al=cgetg(3,t_COMPLEX);
      al[1]=lneg(gdiv(w,ag2));
      al[2]=ldiv(sqd,ag2);
      ga1 = trueeta(gdiv(al,p1),prec);
      ga2 = trueeta(gdiv(al,p2),prec);
      ga3 = trueeta(gdiv(al,mulii(p1,p2)),prec);
      ga4 = trueeta(al,prec);
      LG[i] = lpowgs(gdiv(gmul(ga1,ga2),gmul(ga3,ga4)), ex);
      e = gexpo((GEN)LG[i]); if (e > 0) emax += e; 
      if (DEBUGLEVEL > 2) fprintferr("%ld ",i);
    }
    if (DEBUGLEVEL > 2) fprintferr("\n");
    if (raw)
    {
      y=cgetg(h+1,t_VEC);
      for(i=1; i<=h; i++)
      {
        res=cgetg(3,t_VEC); y[i]=(long)res;
        res[1]=lcopy((GEN)L[i]);
        res[2]=lcopy((GEN)LG[i]);
      }
      break;
    }
    if (DEBUGLEVEL>=2) msgtimer("roots");
    /* to avoid integer overflow (1 + 0.) */
    lead = (emax < bit_accuracy(prec))? gun: realun(prec);

    y = greal(roots_to_pol_intern(lead,LG,0,0));
    y = grndtoi(y,&emax);
    if (DEBUGLEVEL>=2) msgtimer("product, error bits = %ld",emax);
    if (emax <= -10)
    {
      if (typ(flag)==t_VEC)
      {
        long av1 = avma;
        e = degree(modulargcd(y,derivpol(y)));
        avma = av1; if (e > 0) { avma=av; return gzero; }
      }
      break;
    }
    avma = av0; prec += (DEFAULTPREC-2) + (1 + (emax >> TWOPOTBITS_IN_LONG));
    if (DEBUGLEVEL) err(warnprec,"quadhilbertimag",prec);
  }
  return gerepileupto(av,y);
}

GEN quadhilbertreal(GEN D, long prec);

GEN
quadhilbert(GEN D, GEN flag, long prec)
{
  if (typ(D)!=t_INT)
  {
    D = checkbnf(D);
    if (degree(gmael(D,7,1))!=2)
      err(talker,"not a polynomial of degree 2 in quadhilbert");
    D=gmael(D,7,3);
  }
  else
  {
  if (!isfundamental(D))
    err(talker,"quadhilbert needs a fundamental discriminant");
  }
  if (signe(D)>0) return quadhilbertreal(D,prec);
  if (!flag) flag = gzero;
  return quadhilbertimag(D,flag);
}

/* AUXILLIARY ROUTINES FOR QUADRAYIMAGWEI */

static GEN
getal(GEN nf, GEN b, GEN a, long prec)
{
  GEN p1,D,os;

  p1=idealcoprime(nf,idealdiv(nf,b,a),b);
  D=(GEN)nf[3];
  os=mpodd(D) ? gun : gzero; os=gmul2n(gadd(os,gsqrt(D,prec)),-1);
  return gadd((GEN)p1[1],gmul((GEN)p1[2],os));
}

static GEN
epseta(GEN D, long p, long q, GEN tau, long prec)
{
  GEN p1,p2;

  if (gcmpgs(D,-4)<0)
  {
    p1=trueeta(gdivgs(tau,p),prec);
    p2=(p==q) ? p1 : trueeta(gdivgs(tau,q),prec);
    p1=gdiv(gmul(p1,p2),trueeta(gdivgs(tau,p*q),prec));
    return gmul(p1,gpuigs(trueeta(tau,prec),3));
  }
  else return gpuigs(trueeta(tau,prec),4);
}

static GEN
pppfun(GEN D, GEN z, GEN a, GEN den, long prec)
{
  GEN om, res, y, os;

  os=mpodd(D) ? gun : gzero; os=gmul2n(gadd(os,gsqrt(D,prec)),-1);
  om=cgetg(3,t_VEC);
  om[1]=ladd(gcoeff(a,1,2),gmul(gcoeff(a,2,2),os));
  om[2]=coeff(a,1,1);
  res=gdiv(ellwp0(om,z,0,prec,0),den); y=res;
  if (gcmpgs(D,-4)>=0) y=gmul(y,res);
  if (gcmpgs(D,-3)==0) y=gmul(y,res);
  return y;
}

static GEN
schertzc(GEN nf, GEN a, GEN den, long prec)
{
  GEN D,al,id,p1;
  long k2,k3,ell,j;
  byteptr p = diffptr;

  D=(GEN)nf[3];

  if (gcmpgs(D,-3)==0)
  {
    id=idealmul(nf,gdeux,(GEN)(primedec(nf,stoi(3))[1]));
    al=getal(nf,id,a,prec);
    return pppfun(D,al,a,den,prec);
  }
  if (gcmpgs(D,-4)==0)
  {
    id=idealmul(nf,(GEN)(primedec(nf,gdeux)[1]),(GEN)(primedec(nf,stoi(5))[1]));
    al=getal(nf,id,a,prec);
    return pppfun(D,al,a,den,prec);
  }
  k2=krogs(D,2); k3=krogs(D,3);
  if (k2==-1)
  {
    if (k3==-1) return gzero;
    else
    {
      ell=0; ell += *p++; ell += *p++;
      do
      {
	ell += *p++;
	if (!*p) err(primer1);
      }
      while (ell%3!=2 || krogs(D,ell)==1);
      al=getal(nf,idealhermite(nf,(GEN)(primedec(nf,stoi(ell))[1])),a,prec);
      p1=gzero;
      for (j=1; j<=((ell-1)>>1); j++)
	p1=gadd(p1,pppfun(D,gmulsg(j,al),a,den,prec));
      return gneg(p1);
    }
  }
  else
  {
    if (k3!=-1)
    {
      id=idealmul(nf,(GEN)(primedec(nf,gdeux)[1]),(GEN)(primedec(nf,stoi(3))[1]));
      al=getal(nf,id,a,prec);
      return pppfun(D,al,a,den,prec);
    }
    else
    {
      if (k2==1)
      {
	al=getal(nf,idealhermite(nf,gdeux),a,prec);
	return pppfun(D,al,a,den,prec);
      }
      else
      {
	ell=0; ell += *p++; ell += *p++;
	do
	{
	  ell += *p++;
	  if (!*p) err(primer1);
	}
	while (ell%4!=3 || krogs(D,ell)==1);
	al=getal(nf,idealhermite(nf,(GEN)(primedec(nf,stoi(ell))[1])),a,prec);
	p1=gzero;
	for (j=1; j<=((ell-1)>>1); j++)
	  p1=gadd(p1,pppfun(D,gmulsg(j,al),a,den,prec));
	return gmulsg(-krogs(gdeux,ell),p1);
      }
    }
  }
}

static GEN
getallelts(GEN nf, GEN clgp)
{
  GEN cyc,gen,listl,res;
  long lc,i,j,k,no,k1,pro;

  cyc=(GEN)clgp[2]; gen=(GEN)clgp[3]; lc=lg(cyc)-1;
  no=itos((GEN)clgp[1]);
  listl=cgetg(no+1,t_VEC);
  listl[1] = (long)idealhermite(nf,gun);
  for (j=1; j<no; j++)
  {
    k = j; res = gun;
    for (i=lc; k; i--)
    {
      pro=((GEN)cyc[i])[2]; /* attention: 1er et seul mot no code de cyc[i] */
      k1 = k%pro;
      if (k1) res=idealmul(nf,res,idealpows(nf,(GEN)gen[i],k1));
      k /= pro;
    }
    listl[j+1] = (long)res;
  }
  return listl;
}

/* If error and flag = 0 return error message, otherwise return empty vector */
static GEN
findbezk(GEN nf, GEN be, long flag, long prec)
{
  GEN a0,b0,a,b,D,pol,y;
  GEN eps=gpuigs(stoi(10),-8);
  long d0,ea,eb;

  D=(GEN)nf[3]; pol=(GEN)nf[1];
  a0=gmul2n(greal(be),1); a=grndtoi(a0,&ea);
  b0=gdiv(gmul2n(gimag(be),1),gsqrt(negi(D),prec)); b=grndtoi(b0,&eb);
  if (ea>-10 || eb>-10)
  {
    if (flag) return cgetg(1,t_VEC);
    else err(talker,"insufficient precision in findbezk");
  }
  if (gcmp(gadd(gabs(gsub(a,a0),prec),gabs(gsub(b,b0),prec)),eps)>0 || mpodd(addii(a,mulii(b,D))))
  {
    if (flag) return cgetg(1,t_VEC);
    else {outerr(be); err(talker," is not in ZK");}
  }
  y=cgetg(3,t_POLMOD);
  y[1]=(long)pol;
  d0=mpodd(D) ? -1 : 0;
  y[2]=ladd(gmul(b,polx[varn(pol)]),gmul2n(gadd(a,gmulgs(b,d0)),-1));
  return y;
}

/*  returns an equation for the ray class field of modulus f of the imaginary
 *  quadratic field bnf if flag=0, a vector of
 *  two-component vectors [id,g(id)] where g() is the root of the equation
 *  if flag is non-zero.
 */
static GEN
quadrayimagwei(GEN bnr, GEN flag, long prec)
{
  long av=avma,tetpil,vpol,clno,clrayno,lc,i,j,res,ell,inda,fl;
  byteptr p = diffptr;
  GEN allf,f,clray,bnf,nf,D,pol,fa,P2,P2new,pp,pi,pial,os,clgp,cyc,gen,listl;
  GEN listray,lista,listla,pp1,la,z,pr2,listden,listc,p1,pii2,ida,ap2;
  GEN om1,om2,tau,d,al,s,vpro;

  allf=conductor(bnr,gzero,1,prec);
  f=gmael(allf,1,1); clray=(GEN)allf[2];
  bnf=(GEN)bnr[1]; nf=(GEN)bnf[7]; D=(GEN)nf[3];
  pol=(GEN)nf[1]; vpol=varn(pol);
  fa=(GEN)idealfactor(nf,f)[1];
  fl=itos(flag);
  if (lg(fa)==1)
  {
    P2=quadhilbertimag(D,flag);
    if (fl)
    {
	  /* convertir les formes en ideaux */
    }
    tetpil=avma; return gerepile(av,tetpil,gcopy(P2));
  }
  os=mpodd(D) ? gun : gzero; os=gmul2n(gadd(os,gsqrt(D,prec)),-1);
  if (lg(fa)==2)
  {
    pp=(GEN)fa[1]; pi=(GEN)pp[1];
    if (fl) pial=gadd(gmul(gmael(pp,2,2),os),gmael(pp,2,1));
    else pial=basistoalg(nf,(GEN)pp[2]);
  }
  else { pi=gun; pial=gun; }
  clgp=gmael(bnf,8,1);
  clno=itos((GEN)clgp[1]); cyc=(GEN)clgp[2]; gen=(GEN)clgp[3];
  lc=lg(gen);
  listl   = getallelts(nf,clgp);
  listray = getallelts(nf,clray);
  clrayno=itos((GEN)clray[1]);
  lista  = cgetg(clrayno+1,t_VECSMALL);
  listla = cgetg(clrayno+1,t_VEC);
  for (i=1; i<=clrayno; i++)
  {
    pp = isprincipalgenforce(bnf,idealinv(nf,(GEN)listray[i]));
    pp1 = (GEN)pp[1];
    for (res=0,j=1; j<lc; j++)
      res = res*itos((GEN)cyc[j]) + itos((GEN)pp1[j]);
    lista[i] = res+1;
    la = gmul((GEN)nf[7],(GEN)pp[2]);
    listla[i] = lsubst(la,vpol,os);
  }
  z = dethnf(gmael3(bnr,2,1,1));
  for (i=1; i<=clno; i++) z=mulii(z,dethnf((GEN)listl[i]));
  if (gcmpgs(D,-4)<0)
  {
    GEN court=cgeti(3);

    court[1]=evallgefint(3) | evalsigne(1);
    ell=0;
    do
    {
      ell += *p++; court[2]=ell;
      if (!*p) err(primer1);
    }
    while (ell%12!=11 || !gcmp1(ggcd(court,z)) || krogs(D,ell)!=1);
    pr2=idealpows(nf,(GEN)(primedec(nf,stoi(ell))[1]),2);
  }
  else { pr2=idmat(2); ell=1; }
  listden=cgetg(clno+1,t_VEC); listc=cgetg(clno+1,t_VEC);
  p1=mppi(prec); setexpo(p1,2);
  pii2=cgetg(3,t_COMPLEX); pii2[1]=zero; pii2[2]=(long)p1;
  for (i=1; i<=clno; i++)
  {
    ida=(GEN)listl[i]; ap2=idealmul(nf,ida,pr2);
    om2=gcoeff(ida,1,1);
    om1=gadd(gcoeff(ap2,1,2),gmul(gcoeff(ap2,2,2),os));
    tau=gdiv(om1,om2);
    d=gmul(gsqr(gdiv(pii2,om2)),epseta(D,ell,ell,tau,prec));
    listden[i]=(long)d;
    listc[i]=(long)schertzc(nf,(GEN)listl[i],d,prec);
  }
  al = gsubst(gmul((GEN)nf[7],idealcoprime(nf,f,f)),vpol,os);
  P2 = fl? cgetg(clrayno+1,t_VEC): gun;
  for (j=1; j<=clrayno; j++)
  {
    inda=lista[j];
    s=pppfun(D,gdiv(al,(GEN)listla[j]),(GEN)listl[inda],(GEN)listden[inda],prec);
    s=gsub(s,(GEN)listc[inda]);

    if (fl)
    {
      s=gmul(pial,s);
      vpro=cgetg(3,t_VEC);
      vpro[1]=(long)listray[j];
      vpro[2]=(long)s;
      P2[j]=(long)vpro;
    }
    else P2=gmul(P2,gsub(polx[0],gmul(pi,s)));
  }
  if (DEBUGLEVEL)
  {
    fprintferr("P2 = "); outerr(P2);
  }
  if (!fl)
  {
    P2new=gzero;
    for (i=clrayno; i>=0; i--)
    {
      p1=findbezk(nf,truecoeff(P2,i),1,prec);
      if (typ(p1)==t_VEC) {avma=av; return cgetg(1,t_VEC);}
      else P2new=gadd(p1,gmul(polx[0],P2new));
    }
    P2=gsubst(P2new,0,gmul(gdiv(pi,pial),polx[0]));
    P2=gmul(P2,gpuigs(gdiv(pial,pi),clrayno));
  }
  tetpil=avma;
  return gerepile(av,tetpil,gcopy(P2));
}

/* AUXILLIARY ROUTINES FOR QUADRAYSIGMA */

/* Computes values 2*I*Pi, (om1_*om2-om1*om2_)/(2*I) and
   om1_*eta2-om2_*eta1 necessary for ellphist */

static GEN
ellphistinit(GEN om, long prec)
{
  GEN p1,p2,et,om1,om2,ar,pii2,res;

  p1=mppi(prec); setexpo(p1,2);
  pii2=cgetg(3,t_COMPLEX); pii2[1]=zero; pii2[2]=(long)p1;
  om1=(GEN)om[1]; om2=(GEN)om[2];
  if (gsigne(gimag(gdiv(om1,om2)))<0)
  {
    p1=om1; om1=om2; om2=p1;
    p1=cgetg(3,t_VEC); p1[1]=(long)om1; p1[2]=(long)om2;
  }
  et=elleta(om,prec);
  ar=gimag(gmul(p2=gconj(om1),om2));
  p1=gsub(gmul(p2,(GEN)et[2]),gmul(gconj(om2),(GEN)et[1]));
  res=cgetg(4,t_VEC);
  res[1]=(long)pii2; res[2]=(long)ar; res[3]=(long)p1;
  return res;
}

/* Computes log(phi^*(z,om)), using res computed by ellphistinit */

static GEN
ellphist(GEN om, GEN res, GEN z, long prec)
{
  GEN zst;

  zst=gdiv(gsub(gmul(z,(GEN)res[3]),gmul(gconj(z),(GEN)res[1])),gmul2n(gmul(gi,(GEN)res[2]),1));
  return gsub(ellsigma(om,z,1,prec),gmul2n(gmul(z,zst),-1));
}

/* Computes phi^*(la,om)/phi^*(1,om) where om is an oriented basis of the
   ideal gf*gc^{-1} */

static GEN
computeth2(GEN nf, GEN gf, GEN gc, GEN la, long prec)
{
  GEN D,os,p1,p2,fdiv,omdiv,lanum,res;

  D=(GEN)nf[3];
  os=mpodd(D) ? gun : gzero; os=gmul2n(gadd(os,gsqrt(D,prec)),-1);
  fdiv=idealdiv(nf,gf,gc);
  omdiv=cgetg(3,t_VEC); omdiv[2]=coeff(fdiv,1,1);
  omdiv[1]=ladd(gmul(gcoeff(fdiv,2,2),os),gcoeff(fdiv,1,2));
  la=lift(la);
  lanum=gadd(gmul(truecoeff(la,1),os),truecoeff(la,0));
  res=ellphistinit(omdiv,prec);
  p1=gsub(ellphist(omdiv,res,lanum,prec),ellphist(omdiv,res,gun,prec));
  p2=gimag(p1);
  if (gexpo(greal(p1))>20 || gexpo(p2)> bit_accuracy(min(prec,lg(p2)))-10)
    return cgetg(1,t_VEC);
  else return gexp(p1,prec);
}

/* Computes P_2(X)=polynomial in Z_K[X] closest to prod_gc(X-th2(gc)) where
   the product is over the ray class group bnr.*/

static GEN
computeP2(GEN bnr, GEN la, GEN flag, long prec)
{
  long av=avma,tetpil,clrayno,j,fl;
  GEN bnf,listray,nf,P,s,Pnew,gc,vpro,p1,gf;

  bnf=(GEN)bnr[1]; nf=(GEN)bnf[7]; gf=gmael3(bnr,2,1,1);
  listray=getallelts(nf,(GEN)bnr[5]);
  clrayno=lg(listray)-1;
  fl=itos(flag);
  if (fl) P=cgetg(clrayno+1,t_VEC);
  else P=gun;
  for (j=1; j<=clrayno; j++)
  {
    gc=(GEN)listray[j];
    s=computeth2(nf,gf,gc,la,prec);
    if (typ(s)==t_VEC) {avma=av; return cgetg(1,t_VEC);}
    if (fl)
    {
     vpro=cgetg(3,t_VEC);
     vpro[1]=(long)listray[j];
     vpro[2]=(long)s;
     P[j]=(long)vpro;
    }
    else P=gmul(P,gsub(polx[0],s));
  }
  if (!fl)
  {
    Pnew=gzero;
    for (j=clrayno; j>=0; j--)
    {
      p1=findbezk(nf,truecoeff(P,j),1,prec);
      if (typ(p1)==t_VEC)
      {
	prec=(prec<<1)-2; avma=av;
	if (DEBUGLEVEL) err(warnprec,"computeP2",prec);
	return computeP2(bnr,la,flag,prec);
      }
      Pnew=gadd(p1,gmul(polx[0],Pnew));
    }
    P=Pnew;
  }
  tetpil=avma; return gerepile(av,tetpil,gcopy(P));
}

#define nexta(a) (a>0 ? -a : 1-a)
static GEN
do_compo(GEN x, GEN y)
{
  long a, ph = degree(y);
  GEN z;
  y = gmul(gpuigs(polx[0],ph), gsubst(y,0,gdiv(polx[MAXVARN],polx[0])));
  for  (a = 0;; a = nexta(a))
  {
    if (a) x = gsubst(x, 0, gaddsg(a, polx[0]));
    z = subres(x,y);
    if (lgef(ggcd(z,derivpol(z))) < 4) break;
  }
  return gsubst(z,MAXVARN,polx[0]);
}
#undef nexta


static GEN
compocyclo(GEN nf, long m, long d, long prec)
{
  GEN p1,p2,p3,D,res,pol4,nf4;
  long ell,vx;

  D=(GEN)nf[3];
  p1=quadhilbertimag(D, gzero);
  p2=cyclo(m,0);
  if (d==1) return do_compo(p1,p2);

  ell = m%2 ? m : (m>>2);
  if (!signe(addsi(ell,D)))
  {
    p2=gcoeff(nffactor(nf,p2),1,1);
    return do_compo(p1,p2);
  }
  if (ell%4==3) ell= -ell;
  p3=cgetg(5,t_POL);
  p3[1]=evalsigne(1)|evallgef(5)|evalvarn(0);
  p3[2]=lstoi((1-ell)>>2);
  p3[3]=p3[4]=un;
  res=rnfequation2(nf,p3);
  vx=varn((GEN)nf[1]);
  pol4=gsubst((GEN)res[1],0,polx[vx]);
  nf4=initalg(pol4,prec);
  p1=gcoeff(nffactor(nf4,p1),1,1);
  p2=gcoeff(nffactor(nf4,p2),1,1);
  p3=do_compo(p1,p2);
  p1=gmodulcp(gsubst(lift((GEN)res[2]),0,polx[vx]),pol4);
  return gsubst(lift0(p3,vx),vx,p1);
}

static GEN
retflag(GEN x, GEN flag)
{
  if (itos(flag)) err(impl,"some special cases in quadray (flag=1)");
      /* to be done */
  return x;
}

/* Treat special cases directly. Exit with 0 if not special case. Internal,
   no stack treatment. */
static GEN
treatspecialsigma(GEN nf, GEN gf, GEN flag, long prec)
{
  GEN D,p1,p2,tryf,fa;
  long Ds,flf,lfa,i;

  D=(GEN)nf[3];
  if (cmpis(D,-3)==0)
  {
    p1=idmat(2); p2=gcoeff(gf,1,1);
    if (gegal(gf,gmul(p1,p2)) && (cmpis(p2,4)==0 || cmpis(p2,5)==0 || cmpis(p2,7)==0))
      return retflag(cyclo(itos(p2),0),flag);
    p1=idealpows(nf,(GEN)primedec(nf,stoi(3))[1],3);
    if (gegal(gf,p1))
    {
      p1=gcoeff(nffactor(nf,cyclo(3,0)),1,1);
      p1=gneg(polcoeff0(p1,0,0)); /* should be zeta_3 */
      p2=cgetg(6,t_POL);
      p2[1]=evalsigne(1)|evallgef(6)|evalvarn(0);
      p2[2]=(long)p1; p2[3]=p2[4]=zero; p2[5]=un;
      return retflag(p2,flag);
    }
    return gzero;
  }
  if (cmpis(D,-4)==0)
  {
    p1=idmat(2); p2=gcoeff(gf,1,1);
    if (gegal(gf,gmul(p1,p2)))
    {
      if (cmpis(p2,3)==0 || cmpis(p2,5)==0)
	return retflag(cyclo(itos(p2),0),flag);
      if (cmpis(p2,4)==0)
      {
	p1=gcoeff(nffactor(nf,cyclo(4,0)),1,1);
	p1=gneg(polcoeff0(p1,0,0)); /* should be zeta_4=I */
	p2=cgetg(5,t_POL);
	p2[1]=evalsigne(1)|evallgef(5)|evalvarn(0);
	p2[2]=(long)p1; p2[3]=zero; p2[4]=un;
	return retflag(p2,flag);
      }
    }
    return gzero;
  }
  p1=idmat(2); p2=gcoeff(gf,1,1); Ds=itos(modis(D,48));
  if (gegal(gf,gmul(p1,p2)))
  {
    if (cmpis(p2,2)==0 && Ds%16==8)
      return retflag(compocyclo(nf,4,1,prec),flag);
    if (cmpis(p2,3)==0 && Ds%3==1)
      return retflag(compocyclo(nf,3,1,prec),flag);
    if (cmpis(p2,4)==0 && Ds%8==1)
      return retflag(compocyclo(nf,4,1,prec),flag);
    if (cmpis(p2,6)==0 && Ds%48==40)
      return retflag(compocyclo(nf,12,1,prec),flag);
    return gzero;
  }
  p1=gcoeff(gf,2,2);
  if (gcmp1(p1)) {flf=1; tryf=p2;}
  else
  {
    if (cmpis(p1,2) || mpodd(p2) || mpodd(gcoeff(gf,1,2))) return gzero;
    flf=2; tryf=gmul2n(p2,-1);
  }
  fa=(GEN)factor(D)[1]; lfa=lg(fa);
  for (i=1; i<lfa; i++)
    if (cmpis((GEN)fa[i],3)>0 && gegal((GEN)fa[i],tryf))
    {
      if (flf==1) return retflag(compocyclo(nf,itos(tryf),2,prec),flag);
      if (Ds%16==8) return retflag(compocyclo(nf,4*itos(tryf),2,prec),flag);
      return gzero;
    }
  return gzero;
}

/* Compute ray class field polynomial using sigma; if flag=1, pairs
   [ideals,roots] are given instead so that congruence subgroups can be used */

static GEN
quadrayimagsigma(GEN bnr, GEN flag, long prec)
{
  long av=avma,tetpil,a,b,f2;
  GEN allf,bnf,nf,pol,w,wbas,gf,la,p1,p2,y,labas,gfi;

  allf=conductor(bnr,gzero,2,prec);
  bnr=(GEN)allf[2]; gf=gmael(allf,1,1);
  if (gcmp1(dethnf(gf)))
  {
    if (typ(flag)!=t_INT) flag=(GEN)flag[2];
    p1=quadhilbertimag(gmael3(bnr,1,7,3),flag);
    if (itos(flag))
    {
	  /* convertir les formes en ideaux */
    }
    tetpil=avma; return gerepile(av,tetpil,gcopy(p1));
  }
  bnf=(GEN)bnr[1]; nf=(GEN)bnf[7]; pol=(GEN)nf[1];
  p1=treatspecialsigma(nf,gf,flag,prec);
  if (!gcmp0(p1)) {tetpil=avma; return gerepile(av,tetpil,gcopy(p1));}
  w=gmodulcp(polx[varn(pol)],pol);
  wbas=algtobasis(nf,w);
  f2=itos(gmul2n(gcoeff(gf,1,1),1));
  gfi=invmat(gf);
  for (a=0; a<f2; a++)
  {
    for (b=0; b<f2; b++)
    {
      if (DEBUGLEVEL>=2) fprintferr("[%ld,%ld] ",a,b);
      la=gaddgs(gmulsg(a,w),b);
      p1=gnorm(la);
      if (gcmp1(modis(p1,f2)))
      {
	labas=gadd(gmulsg(a,wbas),algtobasis(nf,stoi(b)));
	if (gcmp1(denom(gmul(gfi,gadd(labas,algtobasis(nf,stoi(-1))))))) continue;
	if (gcmp1(denom(gmul(gfi,gadd(labas,algtobasis(nf,gun)))))) continue;
	if (!cmpis((GEN)nf[3],-4))
	{
	  p1=gcoeff(nffactor(nf,cyclo(4,0)),1,1);
	  p1=algtobasis(nf,polcoeff0(p1,0,0)); /* should be -I */
	  if (gcmp1(denom(gmul(gfi,gadd(labas,p1))))) continue;	
	  if (gcmp1(denom(gmul(gfi,gsub(labas,p1))))) continue;	
	}
	if (!cmpis((GEN)nf[3],-3))
	{
	  p1=(GEN)nffactor(nf,cyclo(3,0))[1];
	  p2=algtobasis(nf,polcoeff0((GEN)p1[1],0,0)); /* -zeta_3^2 */
	  p1=algtobasis(nf,polcoeff0((GEN)p1[2],0,0)); /* should be -zeta_3 */
	  if (gcmp1(denom(gmul(gfi,gadd(labas,p1))))) continue;	
	  if (gcmp1(denom(gmul(gfi,gsub(labas,p1))))) continue;	
	  if (gcmp1(denom(gmul(gfi,gadd(labas,p2))))) continue;	
	  if (gcmp1(denom(gmul(gfi,gsub(labas,p2))))) continue;	
	}
	if (DEBUGLEVEL)
	{
	  if (DEBUGLEVEL>=2) fprintferr("\n");
	  fprintferr("lambda = ");
	  outerr(la);
	}
	tetpil=avma;
	y=computeP2(bnr,la,flag,prec);
	return gerepile(av,tetpil,y);
      }
    }
  }
  err(talker,"bug in quadrayimagsigma, please report");
  return gzero;
}

GEN
quadray(GEN D, GEN f, GEN flag, long prec)
{
  long av=avma,tetpil;
  GEN bnr,y,p1,pol,bnf,flagnew;

  if (typ(D)!=t_INT)
  {
    bnf = checkbnf(D);
    if (degree(gmael(bnf,7,1))!=2)
      err(talker,"not a polynomial of degree 2 in quadray");
    D=gmael(bnf,7,3);
  }
  else
  {
    if (!isfundamental(D))
      err(talker,"quadray needs a fundamental discriminant");
    pol=quadpoly(D); setvarn(pol, fetch_user_var("y"));
    bnf=bnfinit0(pol,signe(D)>0?1:0,NULL,prec);
  }
  bnr=bnrinit0(bnf,f,1,prec);
  if (gcmp1(gmael(bnr,5,1)))
  {
    avma=av; if (!flag || gcmp0(flag)) return polx[0];
    y=cgetg(2,t_VEC); p1=cgetg(3,t_VEC); y[1]=(long)p1;
    p1[1]=(long)idmat(2); p1[2]=(long)polx[0];
    return y;
  }
  tetpil=avma;
  if (signe(D)>0)
    y=bnrstark(bnr,gzero,flag?5:1,prec);
  else
  {
    if (!flag) flag = gzero;
    flagnew=flag;
    if (typ(flagnew)==t_INT)
    {
      flagnew=absi(flagnew);
      if (cmpis(flagnew,1)<=0) y=quadrayimagsigma(bnr,flagnew,prec);
      else y=quadrayimagwei(bnr,mpodd(flagnew) ? gun : gzero,prec);
    }
    else
    {
      if (typ(flagnew)!=t_VEC || lg(flagnew)<=2) err(flagerr,"quadray");
      y=computeP2(bnr,(GEN)flagnew[1],(GEN)flagnew[2],prec);
    }
    if (typ(y)==t_VEC && lg(y)==1)
    {
      prec=(prec<<1)-2; avma=av;
      if (DEBUGLEVEL) err(warnprec,"quadray",prec);
      return quadray(D,f,flag,prec);
    }
  }
  return gerepile(av,tetpil,y);
}

/*******************************************************************/
/*                                                                 */
/*  Routines related to binary quadratic forms (for internal use)  */
/*                                                                 */
/*******************************************************************/

static void
rhoreal_aux2(GEN x, GEN y)
{
  GEN p1,p2;
  long s = signe(x[3]);

  y[1]=x[3]; setsigne(y[1],1);
  p2 = (cmpii(isqrtD,(GEN)y[1]) >= 0)? isqrtD: (GEN) y[1];
  p1 = shifti((GEN)y[1],1);
  p2 = divii(addii(p2,(GEN)x[2]), p1);
  y[2] = lsubii(mulii(p2,p1),(GEN)x[2]);

  setsigne(y[1],s);
  p1 = shifti(subii(sqri((GEN)y[2]),Disc),-2);
  y[3] = ldivii(p1,(GEN)y[1]);
}

static GEN
rhoreal_aux(GEN x)
{
  GEN y = cgetg(6,t_VEC);
  long e;

  rhoreal_aux2(x,y);
  switch(lg(x))
  {
    case 4: case 5: setlg(y,4); break;
    case 6:
      y[5]=lmulrr(divrr(addir((GEN)x[2],sqrtD),subir((GEN)x[2],sqrtD)),
                  (GEN)x[5]);
      e = expo(y[5]);
      if (e < EXP220) y[4]=x[4];
      else
      {
        y[4]=laddsi(1,(GEN)x[4]);
        setexpo(y[5], e - EXP220);
      }
    }
  return y;
}

static GEN
rhorealform(GEN x)
{
  long av=avma,tetpil;
  x = rhoreal_aux(x); tetpil=avma;
  return gerepile(av,tetpil,gcopy(x));
}

static GEN
redrealform(GEN x)
{
  long l;
  GEN p1;

  for(;;)
  {
    if (signe(x[2]) > 0 && cmpii((GEN)x[2],isqrtD) <= 0)
    {
      p1 = subii(isqrtD, shifti(absi((GEN)x[1]),1));
      l = absi_cmp((GEN)x[2],p1);
      if (l>0 || (l==0 && signe(p1)<0)) break;
    }
    x = rhoreal_aux(x);
  }
  if (signe(x[1]) < 0)
  {
    if (sens || (signe(x[3])>0 && !absi_cmp((GEN)x[1],(GEN)x[3])))
      return rhoreal_aux(x); /* narrow class group, or a = -c */
    setsigne(x[1],1); setsigne(x[3],-1);
  }
  return x;
}

static GEN
redrealform_init(GEN x)
{
  long av=avma, tetpil;
  GEN y = cgetg(6,t_VEC);

  y[1]=x[1]; y[2]=x[2]; y[3]=x[3]; y[4]=zero;
  y[5]=(long)realun(PRECREG);
  y = redrealform(y); tetpil=avma;
  return gerepile(av,tetpil,gcopy(y));
}

static void
compreal_aux(GEN x, GEN y, GEN z)
{
  GEN s,n,d,d1,x1,x2,y1,y2,v1,v2,b3,c3,m,p1,r;

  s=shifti(addii((GEN)x[2],(GEN)y[2]),-1);
  n=subii((GEN)y[2],s);
  d=bezout((GEN)y[1],(GEN)x[1],&y1,&x1);
  d1=bezout(s,d,&x2,&y2);
  v1=divii((GEN)x[1],d1);
  v2=divii((GEN)y[1],d1);
  m=addii(mulii(mulii(y1,y2),n),mulii((GEN)y[3],x2));
  setsigne(m,-signe(m));
  r=modii(m,v1); p1=mulii(v2,r); b3=shifti(p1,1);
  c3=addii(mulii((GEN)y[3],d1),mulii(r,addii((GEN)y[2],p1)));

  z[1]=lmulii(v1,v2);
  z[2]=laddii((GEN)y[2],b3);
  z[3]=ldivii(c3,v1);
}

static GEN
comprealform3(GEN x, GEN y)
{
  long av = avma, tetpil;
  GEN z = cgetg(4,t_VEC);
  compreal_aux(x,y,z); z=redrealform(z); tetpil=avma;
  return gerepile(av,tetpil,gcopy(z));
}

static GEN
comprealform5(GEN x, GEN y)
{
  long av = avma,tetpil,e;
  GEN p1, z = cgetg(6,t_VEC);

  compreal_aux(x,y,z);
  z[5]=lmulrr((GEN)x[5],(GEN)y[5]);
  e=expo(z[5]); p1 = addii((GEN)x[4],(GEN)y[4]);
  if (e < EXP220) z[4] = (long)p1;
  else
  {
    z[4] = laddsi(1,p1);
    setexpo(z[5], e-EXP220);
  }
  z=redrealform(z); tetpil=avma;
  return gerepile(av,tetpil,gcopy(z));
}

static GEN
initializeform5(long *ex)
{
  long av = avma, i;
  GEN form = powsubfactorbase[1][ex[1]];

  for (i=2; i<=lgsub; i++)
    form = comprealform5(form, powsubfactorbase[i][ex[i]]);
  i=avma; return gerepile(av,i,gcopy(form));
}

/*******************************************************************/
/*                                                                 */
/*                     Common subroutines                          */
/*                                                                 */
/*******************************************************************/
static void
buch_init(void)
{
  if (DEBUGLEVEL) timer2();
  primfact  = new_chunk(100);
  primfact1 = new_chunk(100);
  exprimfact  = new_chunk(100);
  exprimfact1 = new_chunk(100);
  badprim = new_chunk(100);
  hashtab = (long**) new_chunk(HASHT);
}

double
check_bach(double cbach, double B)
{
  if (cbach > B)
   err(talker,"sorry, buchxxx couldn't deal with this field PLEASE REPORT!");
  cbach *= 2; if (cbach > B) cbach = B;
  if (DEBUGLEVEL) fprintferr("\n*** Bach constant: %f\n", cbach);
  return cbach;
}

static long
factorisequad(GEN f, long kcz, long limp)
{
  long i,p,k,av,lo;
  GEN q,r, x = (GEN)f[1];

  if (is_pm1(x)) { primfact[0]=0; return 1; }
  av=avma; lo=0;
  if (signe(x) < 0) x = absi(x);
  for (i=1; ; i++)
  {
    p=factorbase[i]; q=dvmdis(x,p,&r);
    if (!signe(r))
    {
      k=0; while (!signe(r)) { x=q; k++; q=dvmdis(x,p,&r); }
      lo++; primfact[lo]=p; exprimfact[lo]=k;
    }
    if (cmpis(q,p)<=0) break;
    if (i==kcz) { avma=av; return 0; }
  }
  p = x[2]; avma=av;
  /* p = itos(x) if lgefint(x)=3 */
  if (lgefint(x)!=3 || p > limhash) return 0;

  if (p != 1 && p <= limp)
  {
    for (i=1; i<=badprim[0]; i++)
      if (p % badprim[i] == 0) return 0;
    lo++; primfact[lo]=p; exprimfact[lo]=1;
    p = 1;
  }
  primfact[0]=lo; return p;
}

static long *
largeprime(long q, long *ex, long np, long nrho)
{
  const long hashv = ((q&2047)-1)>>1;
  long *pt, i;

  for (pt = hashtab[hashv]; ; pt = (long*) pt[0])
  {
    if (!pt)
    {
      pt = (long*) gpmalloc((lgsub+4)<<TWOPOTBYTES_IN_LONG);
      *pt++ = nrho; /* nrho = pt[-3] */
      *pt++ = np;   /* np   = pt[-2] */
      *pt++ = q;    /* q    = pt[-1] */
      pt[0] = (long)hashtab[hashv];
      for (i=1; i<=lgsub; i++) pt[i]=ex[i];
      hashtab[hashv]=pt; return NULL;
    }
    if (pt[-1] == q) break;
  }
  for(i=1; i<=lgsub; i++)
    if (pt[i] != ex[i]) return pt;
  return (pt[-2]==np)? (GEN)NULL: pt;
}

static long
badmod8(GEN x)
{
  long r = mod8(x);
  if (!r) return 1;
  if (signe(Disc) < 0) r = 8-r;
  return (r < 4);
}

/* cree factorbase, numfactorbase, vectbase; affecte badprim */
static void
factorbasequad(GEN Disc, long n2, long n)
{
  long i,p,bad, av = avma;
  byteptr d=diffptr;

  numfactorbase = (long*) gpmalloc(sizeof(long)*(n2+1));
  factorbase    = (long*) gpmalloc(sizeof(long)*(n2+1));
  KC=0; bad=0; i=0; p = *d++;
  while (p<=n2)
  {
    switch(krogs(Disc,p))
    {
      case -1: break; /* inert */
      case  0: /* ramified */
      {
        GEN p1 = divis(Disc,p);
	if (smodis(p1,p) == 0)
          if (p!=2 || badmod8(p1)) { badprim[++bad]=p; break; }
        i++; numfactorbase[p]=i; factorbase[i] = -p; break;
      }
      default:  /* split */
        i++; numfactorbase[p]=i; factorbase[i] = p;
    }
    p += *d++; if (!*d) err(primer1);
    if (KC == 0 && p>n) KC = i;
  }
  if (!KC) { free(factorbase); free(numfactorbase); return; }
  KC2 = i;
  vectbase = (long*) gpmalloc(sizeof(long)*(KC2+1));
  for (i=1; i<=KC2; i++)
  {
    p = factorbase[i];
    vectbase[i]=p; factorbase[i]=labs(p);
  }
  if (DEBUGLEVEL)
  {
    msgtimer("factor base");
    if (DEBUGLEVEL>7)
    {
      fprintferr("factorbase:\n");
      for (i=1; i<=KC; i++) fprintferr("%ld ",factorbase[i]);
      fprintferr("\n"); flusherr();
    }
  }
  avma=av; badprim[0] = bad;
}

/* cree vectbase and subfactorbase. Affecte lgsub */
static long
subfactorbasequad(double ll, long KC)
{
  long i,j,k,nbidp,p,pro[100], ss;
  GEN p1,y;
  double prod;

  i=0; ss=0; prod=1;
  for (j=1; j<=KC && prod<=ll; j++)
  {
    p = vectbase[j];
    if (p>0) { pro[++i]=p; prod*=p; vperm[i]=j; } else ss++;
  }
  if (prod<=ll) return -1;
  nbidp=i;
  for (k=1; k<j; k++)
    if (vectbase[k]<=0) vperm[++i]=k;

  y=cgetg(nbidp+1,t_COL);
  if (PRECREG) /* real */
    for (j=1; j<=nbidp; j++)
    {
      p1=primeform(Disc,stoi(pro[j]),PRECREG);
      y[j] = (long) redrealform_init(p1);
    }
  else
    for (j=1; j<=nbidp; j++) /* imaginary */
    {
      p1=primeform(Disc,stoi(pro[j]),0);
      y[j] = (long)p1;
    }
  subbase = (long*) gpmalloc(sizeof(long)*(nbidp+1));
  lgsub = nbidp; for (j=1; j<=lgsub; j++) subbase[j]=pro[j];
  if (DEBUGLEVEL>7)
  {
    fprintferr("subfactorbase: ");
    for (i=1; i<=lgsub; i++)
      { fprintferr("%ld: ",subbase[i]); outerr((GEN)y[i]); }
    fprintferr("\n"); flusherr();
  }
  subfactorbase = y; return ss;
}

static void
powsubfact(long n, long a)
{
  GEN unform, **x = (GEN**) gpmalloc(sizeof(GEN*)*(n+1));
  long i,j;

  for (i=1; i<=n; i++)
    x[i] = (GEN*) gpmalloc(sizeof(GEN)*(a+1));
  if (PRECREG) /* real */
  {
    unform=cgetg(6,t_VEC);
    unform[1]=un;
    unform[2]=(mod2(Disc) == mod2(isqrtD))? (long)isqrtD: laddsi(-1,isqrtD);
    unform[3]=lshifti(subii(sqri((GEN)unform[2]),Disc),-2);
    unform[4]=zero;
    unform[5]=(long)realun(PRECREG);
    for (i=1; i<=n; i++)
    {
      x[i][0] = unform;
      for (j=1; j<=a; j++)
	x[i][j]=comprealform5(x[i][j-1],(GEN)subfactorbase[i]);
    }
  }
  else /* imaginary */
  {
    unform=cgetg(4,t_QFI);
    unform[1]=un;
    unform[2]=mod2(Disc)? un: zero;
    unform[3]=lshifti(absi(Disc),-2);
    for (i=1; i<=n; i++)
    {
      x[i][0] = unform;
      for (j=1; j<=a; j++)
	x[i][j]=compimag(x[i][j-1],(GEN)subfactorbase[i]);
    }
  }
  if (DEBUGLEVEL) msgtimer("powsubfact");
  powsubfactorbase = x;
}

static void
desalloc(long **mat)
{
  long i,*p,*q;

  free(vectbase); free(factorbase); free(numfactorbase);
  if (mat)
  {
    free(subbase);
    for (i=1; i<lg(subfactorbase); i++) free(powsubfactorbase[i]);
    for (i=1; i<lg(mat); i++) free(mat[i]);
    free(mat); free(powsubfactorbase);
    for (i=1; i<HASHT; i++)
      for (p = hashtab[i]; p; p = q) { q=(long*)p[0]; free(p-3); }
  }
}

/* L-function */
static GEN
lfunc(GEN Disc)
{
  long av=avma, p;
  GEN y=realun(DEFAULTPREC);
  byteptr d=diffptr;

  for(p = *d++; p<=30000; p += *d++)
  {
    if (!*d) err(primer1);
    y = mulsr(p, divrs(y, p-krogs(Disc,p)));
  }
  return gerepileupto(av,y);
}

#define comp(x,y) x? (PRECREG? compreal(x,y): compimag(x,y)): y
static GEN
get_clgp(GEN Disc, GEN W, GEN *ptmet, long prec)
{
  GEN p1,p2,res,*init, u1u2=smith2(W), u1=(GEN)u1u2[1], met=(GEN)u1u2[3];
  long c,i,j, l = lg(met);

  u1 = reducemodmatrix(ginv(u1), W);
  for (c=1; c<l; c++)
    if (gcmp1(gcoeff(met,c,c))) break;
  if (DEBUGLEVEL) msgtimer("smith/class group");
  res=cgetg(c,t_VEC); init = (GEN*)cgetg(l,t_VEC);
  for (i=1; i<l; i++)
    init[i] = primeform(Disc,stoi(labs(vectbase[vperm[i]])),prec);
  for (j=1; j<c; j++)
  {
    p1 = NULL;
    for (i=1; i<l; i++)
    {
      p2 = gpui(init[i], gcoeff(u1,i,j), prec);
      p1 = comp(p1,p2);
    }
    res[j] = (long)p1;
  }
  if (DEBUGLEVEL) msgtimer("generators");
  *ptmet = met; return res;
}

static GEN
extra_relations(long LIMC, long *ex, long nlze, GEN extramatc)
{
  long av,fpc,p,ep,i,j,k,nlze2, *col, *colg, s = 0, extrarel = nlze+2;
  long MAXRELSUP = min(50,4*KC);
  GEN p1,form, extramat = cgetg(extrarel+1,t_MAT);

  if (DEBUGLEVEL)
  {
    fprintferr("looking for %ld extra relations\n",extrarel);
    flusherr();
  }
  for (j=1; j<=extrarel; j++) extramat[j]=lgetg(KC+1,t_COL);
  nlze2 = PRECREG? max(nlze,lgsub): min(nlze+1,KC);
  if (nlze2 < 3 && KC > 2) nlze2 = 3;
  av = avma;
  while (s<extrarel)
  {
    form = NULL;
    for (i=1; i<=nlze2; i++)
    {
      ex[i]=mymyrand()>>randshift;
      if (ex[i])
      {
        p1 = primeform(Disc,stoi(factorbase[vperm[i]]),PRECREG);
        p1 = gpuigs(p1,ex[i]); form = comp(form,p1);
      }
    }
    if (!form) continue;

    fpc = factorisequad(form,KC,LIMC);
    if (fpc==1)
    {
      s++; col = (GEN)extramat[s];
      for (i=1; i<=nlze2; i++) col[vperm[i]] = -ex[i];
      for (   ; i<=KC; i++) col[vperm[i]]= 0;
      for (j=1; j<=primfact[0]; j++)
      {
        p=primfact[j]; ep=exprimfact[j];
        if (smodis((GEN)form[2], p<<1) > p) ep = -ep;
        col[numfactorbase[p]] += ep;
      }
      for (i=1; i<=KC; i++)
        if (col[i]) break;
      if (i>KC)
      {
        s--; avma = av;
        if (--MAXRELSUP == 0) return NULL;
      }
      else { av = avma; if (PRECREG) coeff(extramatc,1,s) = form[4]; }
    }
    else avma = av;
    if (DEBUGLEVEL)
    {
      if (fpc == 1) fprintferr(" %ld",s);
      else if (DEBUGLEVEL>1) fprintferr(".");
      flusherr();
    }
  }
  for (j=1; j<=extrarel; j++)
  {
    colg = cgetg(KC+1,t_COL);
    col = (GEN)extramat[j]; extramat[j] = (long) colg;
    for (k=1; k<=KC; k++)
      colg[k] = lstoi(col[vperm[k]]);
  }
  if (DEBUGLEVEL)
  {
    fprintferr("\n");
    msgtimer("extra relations");
  }
  return extramat;
}
#undef comp

/*******************************************************************/
/*                                                                 */
/*                    Imaginary Quadratic fields                   */
/*                                                                 */
/*******************************************************************/

static GEN
imag_random_form(long current, long *ex)
{
  long av = avma,i;
  GEN form,pc;

  for(;;)
  {
    form = pc = primeform(Disc,stoi(factorbase[current]),PRECREG);
    for (i=1; i<=lgsub; i++)
    {
      ex[i] = mymyrand()>>randshift;
      if (ex[i])
        form = compimag(form,powsubfactorbase[i][ex[i]]);
    }
    if (form != pc) return form;
    avma = av; /* ex = 0, try again */
  }
}

static void
imag_relations(long lim, long s, long LIMC, long *ex, long **mat)
{
  static long nbtest;
  long av = avma, i,j,pp,fpc,b1,b2,ep,current, first = (s==0);
  long *col,*fpd,*oldfact,*oldexp;
  GEN pc,form,form1;

  if (first) nbtest = 0 ;
  while (s<lim)
  {
    avma=av; nbtest++; current = first? 1+(s%KC): 1+s-RELSUP;
    form = imag_random_form(current,ex);
    fpc = factorisequad(form,KC,LIMC);
    if (!fpc)
    {
      if (DEBUGLEVEL>1) { fprintferr("."); flusherr(); }
      continue;
    }
    if (fpc > 1)
    {
      fpd = largeprime(fpc,ex,current,0);
      if (!fpd)
      {
        if (DEBUGLEVEL>1) { fprintferr("."); flusherr(); }
        continue;
      }
      form1 = powsubfactorbase[1][fpd[1]];
      for (i=2; i<=lgsub; i++)
        form1 = compimag(form1,powsubfactorbase[i][fpd[i]]);
      pc=primeform(Disc,stoi(factorbase[fpd[-2]]),0);
      form1=compimag(form1,pc);
      pp = fpc << 1;
      b1=smodis((GEN)form1[2], pp);
      b2=smodis((GEN)form[2],  pp);
      if (b1 != b2 && b1+b2 != pp) continue;

      s++; col = mat[s];
      if (DEBUGLEVEL) { fprintferr(" %ld",s); flusherr(); }
      oldfact = primfact; oldexp = exprimfact;
      primfact = primfact1; exprimfact = exprimfact1;
      factorisequad(form1,KC,LIMC);

      if (b1==b2)
      {
        for (i=1; i<=lgsub; i++)
          col[numfactorbase[subbase[i]]] = fpd[i]-ex[i];
        col[fpd[-2]]++;
        for (j=1; j<=primfact[0]; j++)
        {
          pp=primfact[j]; ep=exprimfact[j];
          if (smodis((GEN)form1[2], pp<<1) > pp) ep = -ep;
          col[numfactorbase[pp]] -= ep;
        }
      }
      else
      {
        for (i=1; i<=lgsub; i++)
          col[numfactorbase[subbase[i]]] = -fpd[i]-ex[i];
        col[fpd[-2]]--;
        for (j=1; j<=primfact[0]; j++)
        {
          pp=primfact[j]; ep=exprimfact[j];
          if (smodis((GEN)form1[2], pp<<1) > pp) ep = -ep;
          col[numfactorbase[pp]] += ep;
        }
      }
      primfact = oldfact; exprimfact = oldexp;
    }	
    else
    {
      s++; col = mat[s];
      if (DEBUGLEVEL) { fprintferr(" %ld",s); flusherr(); }
      for (i=1; i<=lgsub; i++)
        col[numfactorbase[subbase[i]]] = -ex[i];
    }
    for (j=1; j<=primfact[0]; j++)
    {
      pp=primfact[j]; ep=exprimfact[j];
      if (smodis((GEN)form[2], pp<<1) > pp) ep = -ep;
      col[numfactorbase[pp]] += ep;
    }
    col[current]--;
    if (!first && fpc == 1 && col[current] == 0)
    {
      s--; for (i=1; i<=KC; i++) col[i]=0;
    }
  }
  if (DEBUGLEVEL)
  {
    fprintferr("\nnbrelations/nbtest = %ld/%ld\n",s,nbtest);
    msgtimer("%s relations", first? "initial": "random");
  }
}

static int
imag_be_honest(long *ex)
{
  long p,fpc, s = KC, nbtest = 0, av = avma;
  GEN form;

  while (s<KC2)
  {
    p = factorbase[s+1];
    if (DEBUGLEVEL) { fprintferr(" %ld",p); flusherr(); }
    form = imag_random_form(s+1,ex);
    fpc = factorisequad(form,s,p-1);
    if (fpc == 1) { nbtest=0; s++; }
    else
    {
      nbtest++; if (nbtest>20) return 0;
    }
    avma = av;
  }
  return 1;
}

/*******************************************************************/
/*                                                                 */
/*                      Real Quadratic fields                      */
/*                                                                 */
/*******************************************************************/

static GEN
real_random_form(long *ex)
{
  long av = avma, i;
  GEN p1,form = NULL;

  for(;;)
  {
    for (i=1; i<=lgsub; i++)
    {
      ex[i] = mymyrand()>>randshift;
/*    if (ex[i]) KB: BUG if I put this in. Why ??? */
      {
        p1 = powsubfactorbase[i][ex[i]];
        form = form? comprealform3(form,p1): p1;
      }
    }
    if (form) return form;
    avma = av;
  }
}

static void
real_relations(long lim, long s, long LIMC, long *ex, long **mat, GEN glog2,
               GEN vecexpo)
{
  static long nbtest;
  long av = avma,av1,av2,tetpil,i,j,p,fpc,b1,b2,ep,current, first = (s==0);
  long *col,*fpd,*oldfact,*oldexp,limstack;
  long findecycle,nbrhocumule,nbrho;
  GEN p1,p2,form,form0,form1,form2;

  limstack=stack_lim(av,1);
  if (first) { nbtest = 0; current = 0; }
  while (s<lim)
  {
    form = real_random_form(ex);
    if (!first)
    {
      current = 1+s-RELSUP;
      p1=redrealform(primeform(Disc,stoi(factorbase[current]),PRECREG));
      form = comprealform3(form,p1);
    }
    form0 = form; form1 = NULL;
    findecycle = nbrhocumule = 0;
    nbrho = -1; av1 = avma;
    while (s<lim)
    {
      if (low_stack(limstack, stack_lim(av,1)))
      {
	tetpil=avma;
	if(DEBUGMEM>1) err(warnmem,"real_relations [1]");	
	if (!form1) form=gerepile(av1,tetpil,gcopy(form));
	else
	{
          GEN *gptr[2]; gptr[0]=&form1; gptr[1]=&form;
          gerepilemany(av1,gptr,2);
	}
      }
      if (nbrho < 0) nbrho = 0; /* first time in */
      else
      {
        if (findecycle) break;
        form = rhorealform(form);
        nbrho++; nbrhocumule++;
        if (first)
        {
          if (absi_equal((GEN)form[1],(GEN)form0[1])
               && egalii((GEN)form[2],(GEN)form0[2])
               && (!sens || signe(form0[1])==signe(form[1]))) findecycle=1;
        }
        else
        {
          if (sens)
            { form=rhorealform(form); nbrho++; }
          else if (!signe(addii((GEN)form[1],(GEN)form[3])))
          {
            if (absi_equal((GEN)form[1],(GEN)form0[1]) &&
                    egalii((GEN)form[2],(GEN)form0[2])) break;
            form=rhorealform(form); nbrho++;
          }
          else
            { setsigne(form[1],1); setsigne(form[3],-1); }
          if (egalii((GEN)form[1],(GEN)form0[1]) &&
              egalii((GEN)form[2],(GEN)form0[2])) break;
        }
      }
      nbtest++; fpc = factorisequad(form,KC,LIMC);
      if (!fpc)
      {
        if (DEBUGLEVEL>1) { fprintferr("."); flusherr(); }
        continue;
      }
      if (fpc > 1)
      {
	fpd = largeprime(fpc,ex,current,nbrhocumule);
        if (!fpd)
        {
          if (DEBUGLEVEL>1) { fprintferr("."); flusherr(); }
          continue;
        }
        if (!form1) form1 = initializeform5(ex);
        if (!first)
        {
          p1 = primeform(Disc,stoi(factorbase[current]),PRECREG);
          p1 = redrealform_init(p1); form1=comprealform5(form1,p1);
        }
	av2=avma;
        for (i=1; i<=nbrho; i++)
	{
	  form1 = rhorealform(form1);
          if (low_stack(limstack, stack_lim(av,1)))
	  {
	    if(DEBUGMEM>1) err(warnmem,"real_relations [2]");	
	    tetpil=avma; form1=gerepile(av2,tetpil,gcopy(form1));
	  }
	}
        nbrho = 0;

        form2=powsubfactorbase[1][fpd[1]];
        for (i=2; i<=lgsub; i++)
          form2 = comprealform5(form2,powsubfactorbase[i][fpd[i]]);
        if (fpd[-2])
        {
          p1 = primeform(Disc,stoi(factorbase[fpd[-2]]), PRECREG);
          p1 = redrealform_init(p1); form2=comprealform5(form2,p1);
        }
	av2=avma;
        for (i=1; i<=fpd[-3]; i++)
	{
          form2 = rhorealform(form2);
          if (low_stack(limstack, stack_lim(av,1)))
	  {
	    if(DEBUGMEM>1) err(warnmem,"real_relations [3]");	
	    tetpil=avma; form2=gerepile(av2,tetpil,gcopy(form2));
	  }
	}
        if (!sens && signe(addii((GEN)form2[1],(GEN)form2[3])))
        {
          setsigne(form2[1],1);
          setsigne(form2[3],-1);
        }
        p = fpc << 1;
        b1=smodis((GEN)form2[2], p);
        b2=smodis((GEN)form1[2], p);
        if (b1 != b2 && b1+b2 != p) continue;

        s++; col = mat[s]; if (DEBUGLEVEL) fprintferr(" %ld",s);
        oldfact = primfact; oldexp = exprimfact;
        primfact = primfact1; exprimfact = exprimfact1;
        factorisequad(form2,KC,LIMC);
        if (b1==b2)
        {
          for (i=1; i<=lgsub; i++)
            col[numfactorbase[subbase[i]]] = fpd[i]-ex[i];
          for (j=1; j<=primfact[0]; j++)
          {
            p=primfact[j]; ep=exprimfact[j];
            if (smodis((GEN)form2[2], p<<1) > p) ep = -ep;
            col[numfactorbase[p]] -= ep;
          }
          if (fpd[-2]) col[fpd[-2]]++; /* implies !first */
          p1 = subii((GEN)form1[4],(GEN)form2[4]);
          p2 = divrr((GEN)form1[5],(GEN)form2[5]);
        }
        else
        {
          for (i=1; i<=lgsub; i++)
            col[numfactorbase[subbase[i]]] = -fpd[i]-ex[i];
          for (j=1; j<=primfact[0]; j++)
          {
            p=primfact[j]; ep=exprimfact[j];
            if (smodis((GEN)form2[2], p<<1) > p) ep = -ep;
            col[numfactorbase[p]] += ep;
          }
          if (fpd[-2]) col[fpd[-2]]--;
          p1 = addii((GEN)form1[4],(GEN)form2[4]);
          p2 = mulrr((GEN)form1[5],(GEN)form2[5]);
        }
        primfact = oldfact; exprimfact = oldexp;
      }
      else
      {
	if (!form1) form1 = initializeform5(ex);
        if (!first)
        {
          p1 = primeform(Disc,stoi(factorbase[current]),PRECREG);
          p1 = redrealform_init(p1); form1=comprealform5(form1,p1);
        }
	av2=avma;
	for (i=1; i<=nbrho; i++)
	{
	  form1 = rhorealform(form1);
          if (low_stack(limstack, stack_lim(av,1)))
	  {
	    if(DEBUGMEM>1) err(warnmem,"real_relations [4]");	
	    tetpil=avma; form1=gerepile(av2,tetpil,gcopy(form1));
	  }
	}
        nbrho = 0;

	s++; col = mat[s]; if (DEBUGLEVEL) fprintferr(" %ld",s);
	for (i=1; i<=lgsub; i++)
          col[numfactorbase[subbase[i]]] = -ex[i];
        p1 = (GEN) form1[4];
        p2 = (GEN) form1[5];
      }
      for (j=1; j<=primfact[0]; j++)
      {
        p=primfact[j]; ep=exprimfact[j];
        if (smodis((GEN)form1[2], p<<1) > p) ep = -ep;
        col[numfactorbase[p]] += ep;
      }
      p1 = mpadd(mulir(mulsi(EXP220,p1), glog2), mplog(absr(p2)));
      affrr(shiftr(p1,-1), (GEN)vecexpo[s]);
      if (!first)
      {
        col[current]--;
        if (fpc == 1 && col[current] == 0)
          { s--; for (i=1; i<=KC; i++) col[i]=0; }
        break;
      }
    }
    avma = av;
  }
  if (DEBUGLEVEL)
  {
    fprintferr("\nnbrelations/nbtest = %ld/%ld\n",s,nbtest);
    msgtimer("%s relations", first? "initial": "random");
  }
}

static int
real_be_honest(long *ex)
{
  long p,fpc,s = KC,nbtest = 0,av = avma;
  GEN p1,form,form0;

  while (s<KC2)
  {
    p = factorbase[s+1];
    if (DEBUGLEVEL) { fprintferr(" %ld",p); flusherr(); }
    form = real_random_form(ex);
    p1 = redrealform(primeform(Disc,stoi(p),PRECREG));
    form = comprealform3(form,p1); form0=form;
    for(;;)
    {
      fpc = factorisequad(form,s,p-1);
      if (fpc == 1) { nbtest=0; s++; break; }
      form = rhorealform(form);
      nbtest++; if (nbtest>20) return 0;
      if (sens || !signe(addii((GEN)form[1],(GEN)form[3])))
	form = rhorealform(form);
      else
      {
	setsigne(form[1],1);
	setsigne(form[3],-1);
      }
      if (egalii((GEN)form[1],(GEN)form0[1])
       && egalii((GEN)form[2],(GEN)form0[2])) break;
    }
    avma=av;
  }
  return 1;
}

static GEN
gcdrealnoer(GEN a,GEN b,long *pte)
{
  long e;
  GEN k1,r;

  if (typ(a)==t_INT)
  {
    if (typ(b)==t_INT) return mppgcd(a,b);
    k1=cgetr(lg(b)); affir(a,k1); a=k1;
  }
  else if (typ(b)==t_INT)
    { k1=cgetr(lg(a)); affir(b,k1); b=k1; }
  if (expo(a)<-5) return absr(b);
  if (expo(b)<-5) return absr(a);
  a=absr(a); b=absr(b);
  while (expo(b) >= -5  && signe(b))
  {
    k1=gcvtoi(divrr(a,b),&e);
    if (e > 0) return NULL;
    r=subrr(a,mulir(k1,b)); a=b; b=r;
  }
  *pte=expo(b); return absr(a);
}

static GEN
get_reg(GEN matc, long sreg)
{
  long i,e,maxe;
  GEN reg = mpabs(gcoeff(matc,1,1));

  e = maxe = 0;
  for (i=2; i<=sreg; i++)
  {
    reg = gcdrealnoer(gcoeff(matc,1,i),reg,&e);
    if (!reg) return NULL;
    maxe = maxe? max(maxe,e): e;
  }
  if (DEBUGLEVEL)
  {
    if (DEBUGLEVEL>7) { fprintferr("reg = "); outerr(reg); }
    msgtimer("regulator");
  }
  return reg;
}

GEN
buchquad(GEN D, double cbach, double cbach2, long RELSUP0, long flag, long prec)
{
  long av0 = avma,av,tetpil,KCCO,KCCOPRO,i,j,s, *ex,**mat;
  long extrarel,nrelsup,nreldep,LIMC,LIMC2,cp,nbram,nlze;
  GEN p1,h,W,met,res,basecl,dr,c_1,pdep,C,B,extramat,extraC;
  GEN reg,vecexpo,glog2,cst;
  double drc,lim,LOGD;

  Disc = D; if (typ(Disc)!=t_INT) err(typeer,"buchquad");
  s=mod4(Disc);
  switch(signe(Disc))
  {
    case -1:
      if (cmpis(Disc,-4) >= 0)
      {
        p1=cgetg(6,t_VEC); p1[1]=p1[4]=p1[5]=un;
        p1[2]=p1[3]=lgetg(1,t_VEC); return p1;
      }
      if (s==2 || s==1) err(funder2,"buchquad");
      PRECREG=0; break;

    case 1:
      if (s==2 || s==3) err(funder2,"buchquad");
      if (flag)
        err(talker,"sorry, narrow class group not implemented. Use bnfnarrow");
      PRECREG=1; break;

    default: err(talker,"zero discriminant in quadclassunit");
  }
  if (carreparfait(Disc)) err(talker,"square argument in quadclassunit");
  if (!isfundamental(Disc))
    err(warner,"not a fundamental discriminant in quadclassunit");
  buch_init(); RELSUP = RELSUP0; sens = flag;
  dr=cgetr(3); affir(Disc,dr); drc=fabs(rtodbl(dr)); LOGD=log(drc);
  lim=sqrt(drc); cst = mulrr(lfunc(Disc), dbltor(lim));
  if (!PRECREG) lim /= sqrt(3.);
  cp = (long)exp(sqrt(LOGD*log(LOGD)/8.0));
  if (cp < 13) cp = 13;
  av = avma; cbach /= 2;

INCREASE: avma = av; cbach = check_bach(cbach,6.);
  nreldep = nrelsup = 0;
  LIMC = (long)(cbach*LOGD*LOGD);
  if (LIMC < cp) LIMC=cp;
  LIMC2 = max(20, (long)(max(cbach,cbach2)*LOGD*LOGD));
  if (LIMC2 < LIMC) LIMC2 = LIMC;
  if (PRECREG)
  {
    PRECREG = max(prec+1, MEDDEFAULTPREC + 2*(expi(Disc)>>TWOPOTBITS_IN_LONG));
    glog2  = glog(gdeux,PRECREG);
    sqrtD  = gsqrt(Disc,PRECREG);
    isqrtD = gfloor(sqrtD);
  }
  factorbasequad(Disc,LIMC2,LIMC);
  if (!KC) goto INCREASE;

  vperm = cgetg(KC+1,t_VECSMALL); for (i=1; i<=KC; i++) vperm[i]=i;
  nbram = subfactorbasequad(lim,KC);
  if (nbram == -1) { desalloc(NULL); goto INCREASE; }
  KCCO = KC + RELSUP;
  if (DEBUGLEVEL) { fprintferr("KC = %ld, KCCO = %ld\n",KC,KCCO); flusherr(); }
  powsubfact(lgsub,CBUCH+7);

  mat = (long**) gpmalloc((KCCO+1)*sizeof(long*));
  setlg(mat, KCCO+1);
  for (i=1; i<=KCCO; i++)
  {
    mat[i] = (long*) gpmalloc((KC+1)*sizeof(long));
    for (j=1; j<=KC; j++) mat[i][j]=0;
  }
  ex = new_chunk(lgsub+1);
  limhash = (LIMC<(MAXHALFULONG>>1))? LIMC*LIMC: HIGHBIT>>1;
  for (i=0; i<HASHT; i++) hashtab[i]=NULL;

  s = lgsub+nbram+RELSUP;
  if (PRECREG)
  {
    vecexpo=cgetg(KCCO+1,t_VEC);
    for (i=1; i<=KCCO; i++) vecexpo[i]=lgetr(PRECREG);
    real_relations(s,0,LIMC,ex,mat,glog2,vecexpo);
    real_relations(KCCO,s,LIMC,ex,mat,glog2,vecexpo);
  }
  else
  {
    imag_relations(s,0,LIMC,ex,mat);
    imag_relations(KCCO,s,LIMC,ex,mat);
  }
  if (KC2 > KC)
  {
    if (DEBUGLEVEL)
      fprintferr("be honest for primes from %ld to %ld\n",
                  factorbase[KC+1],factorbase[KC2]);
    s = PRECREG? real_be_honest(ex): imag_be_honest(ex);
    if (DEBUGLEVEL)
    {
      fprintferr("\n");
      msgtimer("be honest");
    }
    if (!s) { desalloc(mat); goto INCREASE; }
  }
  C=cgetg(KCCO+1,t_MAT);
  if (PRECREG)
  {
    for (i=1; i<=KCCO; i++)
    {
      C[i]=lgetg(2,t_COL); coeff(C,1,i)=vecexpo[i];
    }
    if (DEBUGLEVEL>7) { fprintferr("C: "); outerr(C); flusherr(); }
  }
  else
    for (i=1; i<=KCCO; i++) C[i]=lgetg(1,t_COL);
  W = hnfspec(mat,vperm,&pdep,&B,&C,lgsub);
  nlze = lg(pdep)>1? lg(pdep[1])-1: lg(B[1])-1;

  KCCOPRO=KCCO;
  if (nlze)
  {
EXTRAREL:
    s = PRECREG? 2: 1; extrarel=nlze+2;
    extraC=cgetg(extrarel+1,t_MAT);
    for (i=1; i<=extrarel; i++) extraC[i]=lgetg(s,t_COL);
    extramat = extra_relations(LIMC,ex,nlze,extraC);
    if (!extramat) { desalloc(mat); goto INCREASE; }
    W = hnfadd(W,vperm,&pdep,&B,&C, extramat,extraC);
    nlze = lg(pdep)>1? lg(pdep[1])-1: lg(B[1])-1;
    KCCOPRO += extrarel;
    if (nlze)
    {
      if (++nreldep > 5) { desalloc(mat); goto INCREASE; }
      goto EXTRAREL;
    }
  }
  /* tentative class number */
  h=gun; for (i=1; i<lg(W); i++) h=mulii(h,gcoeff(W,i,i));
  if (PRECREG)
  {
    /* tentative regulator */
    reg = get_reg(C, KCCOPRO - (lg(B)-1) - (lg(W)-1));
    if (!reg)
    {
      desalloc(mat);
      prec = (PRECREG<<1)-2; goto INCREASE;
    }
    if (gexpo(reg)<=-3)
    {
      if (++nrelsup <= 7)
      {
        if (DEBUGLEVEL) { fprintferr("regulateur nul\n"); flusherr(); }
        nlze=min(KC,nrelsup); goto EXTRAREL;
      }
      desalloc(mat); goto INCREASE;
    }
    c_1 = divrr(gmul2n(gmul(h,reg),1), cst);
  }
  else
  {
    reg = gun;
    c_1 = divrr(gmul(h,mppi(DEFAULTPREC)), cst);
  }

  if (gcmpgs(gmul2n(c_1,2),3)<0) { c_1=stoi(10); nrelsup=7; }
  if (gcmpgs(gmul2n(c_1,1),3)>0)
  {
    nrelsup++;
    if (nrelsup<=7)
    {
      if (DEBUGLEVEL)
        { fprintferr("***** check = %f\n\n",gtodouble(c_1)); flusherr(); }
      nlze=min(KC,nrelsup); goto EXTRAREL;
    }
    if (cbach < 5.99) { desalloc(mat); goto INCREASE; }
    err(warner,"suspicious check. Suggest increasing extra relations.");
  }
  basecl = get_clgp(Disc,W,&met,PRECREG);
  s = lg(basecl); desalloc(mat); tetpil=avma;

  res=cgetg(6,t_VEC);
  res[1]=lcopy(h); p1=cgetg(s,t_VEC);
  for (i=1; i<s; i++) p1[i] = (long)icopy(gcoeff(met,i,i));
  res[2]=(long)p1;
  res[3]=lcopy(basecl);
  res[4]=lcopy(reg);
  res[5]=lcopy(c_1); return gerepile(av0,tetpil,res);
}

GEN
buchimag(GEN D, GEN c, GEN c2, GEN REL)
{
  return buchquad(D,gtodouble(c),gtodouble(c2),itos(REL), 0,0);
}

GEN
buchreal(GEN D, GEN sens0, GEN c, GEN c2, GEN REL, long prec)
{
  return buchquad(D,gtodouble(c),gtodouble(c2),itos(REL), itos(sens0),prec);
}
