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
/**                   TRANSCENDENTAL FONCTIONS                     **/
/**                          (part 3)                              **/
/**                                                                **/
/********************************************************************/
#include "pari.h"

GEN
cgetc(long l)
{
  GEN u = cgetg(3,t_COMPLEX); u[1]=lgetr(l); u[2]=lgetr(l);
  return u;
}

static GEN
fix(GEN x, long l)
{
  GEN y;
  if (typ(x) == t_REAL) return x;
  y = cgetr(l); gaffect(x, y); return y;
}

/***********************************************************************/
/**                                                                   **/
/**                       K BESSEL FUNCTION                           **/
/**                                                                   **/
/***********************************************************************/

GEN
kbessel0(GEN nu, GEN gx, long flag, long prec)
{
  switch(flag)
  {
    case 0: return kbessel(nu,gx,prec);
    case 1: return kbessel2(nu,gx,prec);
    default: err(flagerr,"besselk");
  }
  return NULL; /* not reached */
}

GEN
kbessel(GEN nu, GEN gx, long prec)
{
  GEN x,y,p1,p2,zf,zz,s,t,q,r,u,v,e,f,c,d,ak,pitemp,nu2,w;
  long l,lbin,av,av1,k,k2,l1,n2,n;

  if (typ(nu)==t_COMPLEX) return kbessel2(nu,gx,prec);
  l = (typ(gx)==t_REAL)? lg(gx): prec;
  y=cgetr(l); l1=l+1;
  av=avma; x = fix(gx, l);
  u=cgetr(l1); v=cgetr(l1); c=cgetr(l1); d=cgetr(l1);
  e=cgetr(l1); f=cgetr(l1);
  nu2=gmulgs(gsqr(nu),-4);
  n = (long) (bit_accuracy(l)*LOG2 + PI*sqrt(gtodouble(gnorm(nu)))) / 2;
  n2=(n<<1); pitemp=mppi(l1);
  /* this 10 should really be a 5, but then kbessel(15.99) enters oo loop */
  lbin = 10 - bit_accuracy(l); av1=avma;
  if (gcmpgs(x,n)<0)
  {
    zf=gsqrt(gdivgs(pitemp,n2),prec);
    zz=cgetr(l1); gaffect(ginv(stoi(n2<<2)), zz);
    s=gun; t=gzero;
    for (k=n2,k2=2*n2-1; k > 0; k--,k2-=2)
    {
      if (k2 & ~(MAXHALFULONG>>1))
        p1 = gadd(mulss(k2,k2),nu2);
      else
        p1 = gaddsg(k2*k2,nu2);
      ak=gdivgs(gmul(p1,zz),-k);
      s=gadd(gun,gmul(ak,s));
      t=gaddsg(k2,gmul(ak,t));
    }
    gmulz(s,zf,u); t=gmul2n(t,-1);
    gdivgsz(gadd(gmul(t,zf),gmul(u,nu)),-n2,v); avma=av1;
    affsr(n2,q=cgetr(l1));
    r=gmul2n(x,1); av1=avma;
    for(;;)
    {
      p1=divsr(5,q); if (expo(p1) >= -1) p1=ghalf;
      p2=subsr(1,divrr(r,q));
      if (gcmp(p1,p2)>0) p1=p2;
      gnegz(p1,c); gaffsg(1,d); affrr(u,e); affrr(v,f);
      for (k=1; ; k++)
      {
	w=gadd(gmul(gsubsg(k,ghalf),u), gmul(subrs(q,k),v));
	w=gadd(w, gmul(nu,gsub(u,gmul2n(v,1))));
	gdivgsz(gmul(q,v),k,u);
	gdivgsz(w,k,v);
	gmulz(d,c,d);
	gaddz(e,gmul(d,u),e); p1=gmul(d,v);
	gaddz(f,p1,f);
	if (gexpo(p1)-gexpo(f) <= lbin) break;
	avma=av1;
      }
      p1=u; u=e; e=p1;
      p1=v; v=f; f=p1;
      gmulz(q,gaddsg(1,c),q);
      if (expo(subrr(q,r)) <= lbin) break;
    }
    gmulz(u,gpui(gdivgs(x,n),nu,prec),y);
  }
  else
  {
    p2=gmul2n(x,1);
    zf=gsqrt(gdiv(pitemp,p2),prec);
    zz=ginv(gmul2n(p2,2)); s=gun;
    for (k=n2,k2=2*n2-1; k > 0; k--,k2-=2)
    {
      if (k2 & ~(MAXHALFULONG>>1))
        p1=gadd(mulss(k2,k2),nu2);
      else
        p1=gaddsg(k2*k2,nu2);
      ak=gdivgs(gmul(p1,zz),k);
      s=gsub(gun,gmul(ak,s));
    }
    gmulz(s,zf,y);
  }
  gdivz(y,mpexp(x),y); avma=av; return y;
}

/***********************************************************************/
/*                                                                    **/
/**                    FONCTION U(a,b,z) GENERALE                     **/
/**                         ET CAS PARTICULIERS                       **/
/**                                                                   **/
/***********************************************************************/
/* Assume gx > 0 and a,b complex */
/* This might one day be extended to handle complex gx */
/* see Temme, N. M. "The numerical computation of the confluent        */
/* hypergeometric function U(a,b,z)" in Numer. Math. 41 (1983),        */
/* no. 1, 63--82.                                                      */
GEN
hyperu(GEN a, GEN b, GEN gx, long prec)
{
  GEN x,y,p1,p2,p3,zf,zz,s,t,q,r,u,v,e,f,c,d,w,a1,gn;
  long l,lbin,av,av1,av2,k,l1,n,ex;

  if(gsigne(gx) <= 0) err(talker,"hyperu's third argument must be positive");
  ex = (iscomplex(a) || iscomplex(b));

  l = (typ(gx)==t_REAL)? lg(gx): prec;
  if (ex) y=cgetc(l); else y=cgetr(l);
  l1=l+1; av=avma; x = fix(gx, l);
  a1=gaddsg(1,gsub(a,b));
  if (ex)
  {
    u=cgetc(l1); v=cgetc(l1); c=cgetc(l1);
    d=cgetc(l1); e=cgetc(l1); f=cgetc(l1);
  }
  else
  {
    u=cgetr(l1); v=cgetr(l1); c=cgetr(l1);
    d=cgetr(l1); e=cgetr(l1); f=cgetr(l1);
  }
  n=(long)(bit_accuracy(l)*LOG2 + PI*sqrt(gtodouble(gabs(gmul(a,a1),l1))));
  lbin = 10-bit_accuracy(l); av1=avma;
  if (gcmpgs(x,n)<0)
  {
    gn=stoi(n); zf=gpui(gn,gneg_i(a),l1);
    zz=gdivsg(-1,gn); s=gun; t=gzero;
    for (k=n-1; k>=0; k--)
    {
      p1=gdivgs(gmul(gmul(gaddgs(a,k),gaddgs(a1,k)),zz),k+1);
      s=gaddsg(1,gmul(p1,s));
      t=gadd(gaddsg(k,a),gmul(p1,t));
    }
    gmulz(s,zf,u); t=gmul(t,zz); gmulz(t,zf,v); avma=av1;
    q=cgetr(l1); affsr(n,q); r=x; av1=avma;
    do
    {
      p1=divsr(5,q); if (expo(p1)>= -1) p1=ghalf;
      p2=subsr(1,divrr(r,q)); if (gcmp(p1,p2)>0) p1=p2;
      gnegz(p1,c); avma=av1;
      k=0; gaffsg(1,d);
      gaffect(u,e); gaffect(v,f);
      p3=gsub(q,b); av2=avma;
      for(;;)
      {
	w=gadd(gmul(gaddsg(k,a),u),gmul(gaddsg(-k,p3),v));
	k++; gdivgsz(gmul(q,v),k,u);
	gdivgsz(w,k,v);
	gmulz(d,c,d);
	gaddz(e,gmul(d,u),e); p1=gmul(d,v);
	gaddz(f,p1,f);
	if (gexpo(p1)-gexpo(f) <= lbin) break;
	avma=av2;
      }
      p1=u; u=e; e=p1;
      p1=v; v=f; f=p1;
      gmulz(q,gadd(gun,c),q);
      p1=subrr(q,r); ex=expo(p1); avma=av1;
    }
    while (ex>lbin);
  }
  else
  {
    zf=gpui(x,gneg_i(a),l1);
    zz=gdivsg(-1,x); s=gun;
    for (k=n-1; k>=0; k--)
    {
      p1=gdivgs(gmul(gmul(gaddgs(a,k),gaddgs(a1,k)),zz),k+1);
      s=gadd(gun,gmul(p1,s));
    }
    u = gmul(s,zf);
  }
  gaffect(u,y); avma=av; return y;
}

GEN
kbessel2(GEN nu, GEN x, long prec)
{
  long av = avma,tetpil;
  GEN p1,p2,x2,a,pitemp;

  if (typ(x)==t_REAL) prec = lg(x);
  x2=gshift(x,1); pitemp=mppi(prec);
  if (gcmp0(gimag(nu))) a=cgetr(prec); else a=cgetc(prec);
  gaddz(gun,gshift(nu,1),a);
  p1=hyperu(gshift(a,-1),a,x2,prec);
  p1=gmul(gmul(p1,gpui(x2,nu,prec)),mpsqrt(pitemp));
  p2=gexp(x,prec); tetpil=avma;
  return gerepile(av,tetpil,gdiv(p1,p2));
}

GEN
incgam(GEN s, GEN x, long prec)
{
  GEN p1,z = cgetr(prec);
  long av = avma;

  if (gcmp0(x)) return ggamma(s,prec);
  if (typ(x)!=t_REAL) { gaffect(x,z); x=z; }
  if (gcmp(subrs(x,1),s) > 0 || gsigne(greal(s)) <= 0)
    p1 = incgam2(s,x,prec);
  else
    p1 = gsub(ggamma(s,prec), incgam3(s,x,prec));
  affrr(p1,z); avma = av; return z;
}

/* = incgam2(0, x, prec). typ(x) = t_REAL. Optimized for eint1 */
static GEN
incgam2_0(GEN x)
{
  long l,n,i;
  GEN p1;
  double m,mx;

  l = lg(x); mx = rtodbl(x);
  m = (bit_accuracy(l)*LOG2 + mx)/4; n=(long)(1+m*m/mx);
  p1 = divsr(-n, addsr(n<<1,x));
  for (i=n-1; i >= 1; i--)
    p1 = divsr(-i, addrr(addsr(i<<1,x), mulsr(i,p1)));
  return mulrr(divrr(mpexp(negr(x)), x), addrr(realun(l),p1));
}

GEN
incgam1(GEN a, GEN x, long prec)
{
  GEN p2,p3,y, z = cgetr(prec);
  long av=avma, av1, l,n,i;
  double m,mx;

  if (typ(x) != t_REAL) { gaffect(x,z); x=z; }
  l=lg(x); mx=rtodbl(x);
  m=(long) bit_accuracy(l)*LOG2; n=(long)(m/(log(m)-(1+log(mx))));
  p2 = cgetr(l); affrr(addir(gun,gsub(x,a)), p2);
  p3 = subrs(p2, n+1); av1 = avma;
  for (i=n; i>=1; i--)
  {
    affrr(addrr(subrs(p2,i), divrr(mulsr(i,x),p3)), p3);
    avma = av1;
  }
  y = mulrr(mpexp(negr(x)),gpui(x,a,prec));
  affrr(divrr(y,p3), z);
  avma = av; return z;
}

/* assume x != 0 */
GEN
incgam2(GEN a, GEN x, long prec)
{
  GEN b,p1,p2,p3,y, z = cgetr(prec);
  long av = avma,av1,l,n,i;
  double m,mx;

  if (typ(x) != t_REAL) { gaffect(x,z); x=z; }
  if (gcmp0(a)) { affrr(incgam2_0(x), z); avma = av; return z; }
  l=lg(x); mx=rtodbl(x);
  m = (bit_accuracy(l)*LOG2 + mx)/4; n=(long)(1+m*m/mx);
  i = typ(a);
  if (i == t_REAL) b = addsr(-1,a);
  else
  { /* keep b integral : final powering more efficient */
    gaffect(a,p1=cgetr(prec));
    b = (i == t_INT)? addsi(-1,a): addsr(-1,p1);
    a = p1;
  }
  p2 = cgetr(l); gaffect(subrr(x,a),p2);
  p3 = divrr(addsr(-n,a), addrs(p2,n<<1));
  av1 = avma;
  for (i=n-1; i>=1; i--)
  {
    affrr(divrr(addsr(-i,a), addrr(addrs(p2,i<<1),mulsr(i,p3))), p3);
    avma = av1;
  }
  y = gmul(mpexp(negr(x)), gpui(x,b,prec));
  affrr(mulrr(y, addsr(1,p3)), z);
  avma = av; return z;
}

GEN
incgam3(GEN s, GEN x, long prec)
{
  GEN b,p1,p2,p3,y, z = cgetr(prec);
  long av = avma, av1,l,n,i;

  if (typ(x) != t_REAL) { gaffect(x,z); x=z; }
  l=lg(x); n = -bit_accuracy(l)-1;
  p3 = realun(l);
  p2 = rcopy(p3);
  i = typ(s);
  if (i == t_REAL) b = s;
  else
  {
    gaffect(s,p1=cgetr(prec));
    b = (i == t_INT)? s: p1;
    s = p1;
  }
  if (signe(s) <= 0)
  {
    p1 = gcvtoi(s, &i);
    if (i < 5 - bit_accuracy(prec))
      err(talker,"negative argument too close to an integer in incgamc");
  }
  av1 = avma;
  for (i=1; expo(p2) >= n; i++)
  {
    affrr(divrr(mulrr(x,p2), addsr(i,s)), p2);
    affrr(addrr(p2,p3), p3); avma = av1;
  }
  y = gdiv(mulrr(mpexp(negr(x)), gpui(x,b,prec)), s);
  affrr(mulrr(y,p3), z);
  avma = av; return z;
}

/* Assumes that g=gamma(a,prec). Unchecked */
GEN
incgam4(GEN a, GEN x, GEN g, long prec)
{
  GEN p1, z = cgetr(prec);
  long av = avma;

  if (typ(x) != t_REAL) { gaffect(x,z); x=z; }
  if (gcmp(subrs(x,1),a) > 0 || gsigne(greal(a)) <= 0)
    p1 = incgam2(a,x,prec);
  else
    p1 = gsub(g, incgam3(a,x,prec));
  affrr(p1, z);
  avma = av; return z;
}

GEN
incgam0(GEN a, GEN x, GEN z,long prec)
{
  return z? incgam4(a,x,z,prec): incgam(a,x,prec);
}

GEN
eint1(GEN x, long prec)
{
  long av = avma,tetpil,l,n,i;
  GEN p1,p2,p3,p4,run,y;

  if (typ(x) != t_REAL) { gaffect(x,p1=cgetr(prec)); x = p1;}
  if (signe(x) >= 0)
  {
    if (expo(x) >= 4)
      return gerepileupto(av, incgam2_0(x));

    l = lg(x);
    n = -bit_accuracy(l)-1;
    
    run = realun(l);
    p4 = p3 = p2 = p1 = run;
    for (i=2; expo(p2)>=n; i++)
    {
      p1 = addrr(p1,divrs(run,i)); /* p1 = sum_{i=1} 1/i */
      p4 = divrs(mulrr(x,p4),i);   /* p4 = sum_{i=1} x^(i-1)/i */
      p2 = mulrr(p4,p1);
      p3 = addrr(p2,p3);
    }
    p3 = mulrr(x,mulrr(mpexp(negr(x)),p3));
    p1 = addrr(mplog(x), mpeuler(l));
    return gerepileupto(av, subrr(p3,p1));
  }
  else
  { /* written by Manfred Radimersky */
    l  = lg(x);
    n  = bit_accuracy(l);
    /* IS: line split to avoid a Workshop cc-5.0 bug (Sun BugID #4254959) */
    n  = 3 * n / 4;
    y  = negr(x);
    if(gcmpgs(y, n) < 0) {
      p1 = p2 = p3 = y;
      p4 = gzero;
      i  = 2;
      while(gcmp(p3, p4)) {
        p4 = p3;
        p1 = gmul(p1, gdivgs(y, i));
        p2 = gdivgs(p1, i);
        p3 = gadd(p3, p2);
        i++;
      }
      p1 = gadd(mplog(y), mpeuler(l));
      y  = gadd(p3, p1);
    } else {
      p1 = gdivsg(1, y);
      p2 = realun(l);
      p3 = p2;
      p4 = gzero;
      i  = 1;
      while(gcmp(p3, p4)) {
        p4 = p3;
        p2 = gmulgs(p2, i);
        p2 = gmul(p2, p1);
        p3 = gadd(p3, p2);
        i++;
      }
      p1 = gdiv(mpexp(y), y);
      y  = gmul(p3, p1);
    }
    tetpil = avma;
    y  = gerepile(av, tetpil, negr(y));
  }
  return y;
}

GEN
veceint1(GEN C, GEN nmax, long prec)
{
  long av,av1,k,n,nstop,i,cd,nmin,G,a;
  GEN y,e1,e2,F0,F,M2,f,den,minvn,mcn,p1,vdiff,ap,unr,zeror,deninit;

  if (!nmax) return eint1(C,prec);

  if (signe(nmax)<=0) return cgetg(1,t_VEC);
  if (DEBUGLEVEL>1) fprintferr("Entering veceint1:\n");
  if (typ(C) != t_REAL || lg(C) > prec)
    { y = cgetr(prec); gaffect(C,y); C = y; }
  if (signe(C) <= 0) err(talker,"negative or zero constant in veceint1");

  G = -bit_accuracy(prec);
  n=itos(nmax); y=cgetg(n+1,t_VEC);
  for(i=1; i<=n; i++) y[i]=lgetr(prec);
  av=avma;

  nstop = itos(gceil(divsr(4,C)));
  if (nstop<1) nstop=1;
  if (nstop>n) nstop=n;
  nmin=n-10; if (nmin<nstop) nmin=nstop;
  if(DEBUGLEVEL>1) fprintferr("nstop = %ld\n",nstop);

  e1=mpexp(negr(mulsr(n,C)));
  e2=mpexp(mulsr(10,C));
  unr = realun(prec);
  zeror=realzero(prec); deninit=negr(unr);
  f=cgetg(3,t_COL); M2=cgetg(3,t_VEC); av1=avma;

  F0=(GEN)y[n];
  affrr(eint1(mulsr(n,C),prec), F0);
  do
  {
    if (DEBUGLEVEL>1) fprintferr("%ld ",n);
    minvn=divrs(unr,-n); mcn=mulrr(C,minvn);
    M2[1] = (long)zeror; M2[2] = lsubrr(minvn,C);
    f[1]=(long)zeror; f[2]=ldivrs(e1,-n);
    affrr(mulrr(e1,e2), e1);
    vdiff=cgetg(2,t_VEC); vdiff[1]=f[2];
    for (cd=a=1,n--; n>=nmin; n--,a++)
    {
      F = F0;
      ap = stoi(a); den = deninit;
      for (k=1;;)
      {
	if (k>cd)
        {
          cd++; p1 = (GEN)f[2];
          f[2] = lmul(M2,f);
          f[1] = (long)p1;
          M2[1] = laddrr((GEN)M2[1],mcn);
          M2[2] = laddrr((GEN)M2[2],minvn);
          vdiff = concatsp(vdiff,(GEN)f[2]);
        }
	p1 = mulrr(mulri(den,ap),(GEN)vdiff[k]);
        if (expo(p1) < G) { affrr(F,(GEN)y[n]); break; }
	F = addrr(F,p1); ap = mulis(ap,a);
	k++; den = divrs(den,-k);
      }
    }
    avma=av1; n++; F0=(GEN)y[n]; nmin -= 10;
    if (nmin < nstop) nmin=nstop;
  }
  while(n>nstop);
  for(i=1; i<=nstop; i++)
    affrr(eint1(mulsr(i,C),prec), (GEN)y[i]);
  if (DEBUGLEVEL>1) fprintferr("\n");
  avma=av; return y;
}

GEN
gerfc(GEN x, long prec)
{
  long av=avma;
  GEN p1,p2;

  if (typ(x)!=t_REAL) { p1=cgetr(prec); gaffect(x,p1); x=p1; }
  av = avma; p1 = incgam(ghalf,gsqr(x),prec);
  p2 = mpsqrt(mppi(lg(x)));
  p1 = divrr(p1,p2);
  if (signe(x) < 0) p1 = subsr(2,p1);
  return gerepileupto(av,p1);
}

/***********************************************************************/
/**								      **/
/**		        FONCTION ZETA DE RIEMANN                      **/
/**								      **/
/***********************************************************************/

#if 0
static GEN
czeta(GEN s, long prec)
{
  long av,n,p,n1,flag1,flag2,i,i2;
  double st,sp,sn,ssig,ns,alpha,beta,maxbeta,xinf;
  GEN y,z,res,sig,ms,p1,p2,p3,p31,pitemp;

  i=precision(s); if (i) prec = i;
  if (typ(s)==t_COMPLEX)
  {
    res = cgetc(prec); av=avma;
    p1 = cgetc(prec+1);
    gaffect(s,p1); s=p1; sig=(GEN)s[1];
  }
  else
  {
    res = cgetr(prec); av=avma;
    p1 = cgetr(prec+1); affrr(s,p1); sig = s = p1;
  }

  if (signe(sig)>0 && expo(sig)>-2) flag1 = 0;
  else
  {
    if (gcmp0(gimag(s)) && gcmp0(gfrac(gmul2n(sig,-1))))
    {
      if (gcmp0(sig)) gaffect(gneg_i(ghalf),res); else gaffsg(0,res);
      avma=av; return res;
    }
    flag1 = 1; s = gsub(gun,s); sig = greal(s);
  }
  ssig=rtodbl(sig); st=fabs(rtodbl(gimag(s))); maxbeta = pow(3.0,-2.5);
  if (st)
  {
    ns = ssig*ssig + st*st;
    alpha=pariC2*(prec-2)-0.39-0.5*(ssig-1.0)*log(ns)-log(ssig)+ssig*2*pariC1;
    beta=(alpha+ssig)/st-atan(ssig/st);
    if (beta<=0)
    {
      if (ssig>=1.0)
      {
	p=0; sn=sqrt(ns);
	n=(long)(ceil(exp(pariC2*(prec-2)/ssig)*pow(sn/(2*ssig),1.0/ssig)));
      }
      else
      {
	p=1; sn=ssig+1; n=(long)ceil(sqrt(sn*sn+st*st)/(2*PI));
      }
    }
    else
    {
      if (beta<maxbeta) xinf=beta+pow(3*beta,1.0/3.0);
      else
      {
	double eps=0.0087, x00 = beta+PI/2.0, y00,x11;
        for(;;)
	{
	  y00=x00*x00; x11=(beta+atan(x00))*(1+y00)/y00-1/x00;
	  if (x00-x11 < eps) break;
	  x00 = x11;
	}
	xinf=x11;
      }
      sp=1.0-ssig+st*xinf;
      if (sp>0)
      {
	p=(long)ceil(sp/2.0); sn=ssig+2*p-1;
	n=(long)ceil(sqrt(sn*sn+st*st)/(2*PI));
      }
      else
      {
	p=0; sn=sqrt(ns);
	n=(long)ceil(exp(pariC2*(prec-2)/ssig)*pow(sn/(2*ssig),1.0/ssig));
      }
    }
  }
  else
  {
    beta=pariC2*(prec-2)+0.61+ssig*2*pariC1-ssig*log(ssig);
    if (beta>0)
    {
      p=(long)ceil(beta/2.0); sn=ssig+2*p-1;
      n=(long)ceil(sqrt(sn*sn+st*st)/(2*PI));
    }
    else
    {
      p=0; sn=sqrt(ssig*ssig+st*st);
      n=(long)ceil(exp(pariC2*(prec-2)/ssig)*pow(sn/(2*ssig),1.0/ssig));
    }
  }
  if (n < 46340) n1=n*n; else n1=0;
  y=gun; ms=gneg_i(s); p1=cgetr(prec+1); p2=gun;
  for (i=2; i<=n; i++)
  {
    affsr(i,p1); p2 = gexp(gmul(ms,mplog(p1)), prec+1);
    y = gadd(y,p2);
  }
  flag2 = (2*p < 46340);
  mpbern(p,prec+1); p31=cgetr(prec+1); z=gzero;
  for (i=p; i>=1; i--)
  {
    i2=i<<1;
    p1=gmul(gaddsg(i2-1,s),gaddsg(i2,s));
    p1=flag2? gdivgs(p1,i2*(i2+1)): gdivgs(gdivgs(p1,i2),i2+1);
    p1=n1? gdivgs(p1,n1): gdivgs(gdivgs(p1,n),n);
    p3 = bern(i);
    if (bernzone[2]>prec+1) { affrr(p3,p31); p3=p31; }
    z=gadd(divrs(p3,i),gmul(p1,z));
  }
  p1=gsub(gdivsg(n,gsubgs(s,1)),ghalf);
  z=gmul(gadd(p1,gmul(s,gdivgs(z,n<<1))),p2);
  y = gadd(y,z);
  if (flag1)
  {
    pitemp=mppi(prec+1); setexpo(pitemp,2);
    y=gmul(gmul(y,ggamma(s,prec+1)),gpui(pitemp,ms,prec+1));
    setexpo(pitemp,0);
    y=gmul2n(gmul(y,gcos(gmul(pitemp,s),prec+1)),1);
  }
  gaffect(y,res); avma = av; return res;
}

/* y = binomial(n,k-2). Return binomial(n,k) */
static GEN
next_bin(GEN y, long n, long k)
{
  y = divrs(mulrs(y, n-k+2), k-1);
  return divrs(mulrs(y, n-k+1), k);
}

static GEN
izeta(long k, long prec)
{
  long av=avma,av2,kk,n,li, limit;
  GEN y,p1,pi2,qn,z,q,binom;

  /* treat trivial cases */
  if (!k) return gneg(ghalf);
  if (k < 0)
  {
    if ((k&1) == 0) return gzero;
    y = bernreal(1-k,prec);
    return gerepileuptoleaf(av, divrs(y,k-1));
  }
  if (k > bit_accuracy(prec)+1) return realun(prec);
  pi2 = mppi(prec); setexpo(pi2,2); /* 2Pi */
  if ((k&1) == 0)
  {
    p1 = mulrr(gpuigs(pi2,k),absr(bernreal(k,prec)));
    y = divrr(p1, mpfactr(k,prec)); setexpo(y,expo(y)-1);
    return gerepileuptoleaf(av, y);
  }
  /* k > 1 odd */
  binom = realun(prec+1);
  q = mpexp(pi2); kk = k+1; /* >= 4 */
  li = -(1+bit_accuracy(prec));
  y = NULL; /* gcc -Wall */
  if ((k&3)==3)
  {
    for (n=0; n <= kk>>1; n+=2)
    {
      p1 = mulrr(bernreal(kk-n,prec),bernreal(n,prec));
      if (n) { binom = next_bin(binom,kk,n); setlg(binom,prec+1); }
      p1 = mulrr(binom,p1);
      if (n == kk>>1) setexpo(p1, expo(p1)-1);
      if ((n>>1)&1) setsigne(p1,-signe(p1));
      y = n? addrr(y,p1): p1;
    }
    y = mulrr(divrr(gpuigs(pi2,k),mpfactr(kk,prec)),y);

    av2 = avma; limit = stack_lim(av2,1);
    qn = gsqr(q); z = divsr(1,addrs(q,-1));
    for (n=2; ; n++)
    {
      p1 = divsr(1,mulir(gpuigs(stoi(n),k),addrs(qn,-1)));

      z = addrr(z,p1); if (expo(p1)< li) break;
      qn = mulrr(qn,q);
      if (low_stack(limit,stack_lim(av2,1)))
      {
        GEN *gptr[2]; gptr[0]=&z; gptr[1]=&qn;
        if (DEBUGMEM>1) err(warnmem,"izeta");
        gerepilemany(av2,gptr,2);
      }
    }
    setexpo(z,expo(z)+1);
    y = addrr(y,z); setsigne(y,-signe(y));
  }
  else
  {
    GEN p2 = divrs(pi2, k-1);
    for (n=0; n <= k>>1; n+=2)
    {
      p1 = mulrr(bernreal(kk-n,prec),bernreal(n,prec));
      if (n) binom = next_bin(binom,kk,n);
      p1 = mulrr(binom,p1);
      p1 = mulsr(kk-(n<<1),p1);
      if ((n>>1)&1) setsigne(p1,-signe(p1));
      y = n? addrr(y,p1): p1;
    }
    y = mulrr(divrr(gpuigs(pi2,k),mpfactr(kk,prec)),y);
    y = divrs(y,k-1);
    av2 = avma; limit = stack_lim(av2,1);
    qn = q; z=gzero;
    for (n=1; ; n++)
    {
      p1=mulir(gpuigs(stoi(n),k),gsqr(addrs(qn,-1)));
      p1=divrr(addrs(mulrr(qn,addsr(1,mulsr(n<<1,p2))),-1),p1);

      z=addrr(z,p1); if (expo(p1) < li) break;
      qn=mulrr(qn,q);
      if (low_stack(limit,stack_lim(av2,1)))
      {
        GEN *gptr[2]; gptr[0]=&z; gptr[1]=&qn;
        if (DEBUGMEM>1) err(warnmem,"izeta");
        gerepilemany(av2,gptr,2);
      }
    }
    setexpo(z,expo(z)+1);
    y = subrr(y,z);
  }
  return gerepileuptoleaf(av, y);
}
#endif

/* return x^n, assume n > 0 */
static long
pows(long x, long n)
{
  long i, y = x;
  for (i=1; i<n; i++) y *= x;
  return y;
}

/* return n^-s, n > 1 odd. tab[q] := q^-s, q prime power */
static GEN
n_s(long n, GEN *tab)
{
  byteptr d =  diffptr + 2;
  GEN x = NULL;
  long p, e;

  for (p = 3; n > 1; p += *d++)
  {
    e = svaluation(n, p, &n);
    if (e)
    {
      GEN y = tab[pows(p,e)];
      if (!x) x = y; else x = gmul(x,y);
    }
  }
  return x;
}

GEN czeta(GEN s0, long prec);

/* assume k != 1 */
static GEN
izeta(long k, long prec)
{
  long av = avma;
  GEN y,p1,pi2;

  /* treat trivial cases */
  if (!k) { y = realun(prec); setexpo(y,-1); setsigne(y,-1); return y; }
  if (k < 0)
  {
    if ((k&1) == 0) return gzero;
    y = bernreal(1-k,prec);
    return gerepileuptoleaf(av, divrs(y,k-1));
  }
  if (k > bit_accuracy(prec)+1) return realun(prec);
  if ((k&1) == 0)
  {
    pi2 = mppi(prec); setexpo(pi2,2); /* 2Pi */
    p1 = mulrr(gpuigs(pi2,k),absr(bernreal(k,prec)));
    y = divrr(p1, mpfactr(k,prec)); setexpo(y,expo(y)-1);
    return gerepileuptoleaf(av, y);
  }
  /* k > 1 odd */
  return czeta(stoi(k), prec);
}

extern GEN rpowsi(ulong a, GEN n, long prec);
extern GEN divrs2_safe(GEN x, long i);
extern void dcxlog(double s, double t, double *a, double *b);
extern double dnorm(double s, double t);
extern GEN trans_fix_arg(long *prec, GEN *s0, GEN *sig, long *av, GEN *res);

/* s0 a t_INT, t_REAL or t_COMPLEX.
 * If a t_INT, assume it's not a trivial case (i.e we have s0 > 1, odd)
 * */
GEN
czeta(GEN s0, long prec)
{
  GEN s, u, a, y, res, tes, sig, invn2, p1, unr;
  GEN sim, ms, s1, s2, s3, s4, s5, *tab, tabn;
  long p, i, sqn, nn, lim, lim2, ct, av, av2 = avma, avlim;
  int funeq = 0;
  byteptr d;

  if (DEBUGLEVEL) timer2();
  s = trans_fix_arg(&prec,&s0,&sig,&av,&res);
  if (gcmp0(s)) { y = gneg(ghalf); goto END; }
  if (signe(sig) <= 0 || expo(sig) < -1)
  { /* s <--> 1-s */
    if (typ(s0) == t_INT)
    {
      p = itos(s0); avma = av2;
      return izeta(p,prec);
    }
    funeq = 1; s = gsub(gun, s); sig = greal(s);
  }
  if (gcmp(sig, stoi(bit_accuracy(prec) + 1)) > 0) { y = gun; goto END; }

  { /* find "optimal" parameters [lim, nn] */
    double ssig = rtodbl(sig);
    double st = rtodbl(gimag(s));
    double ns = dnorm(ssig,st), l,l2;
    long la = 1;

    if (typ(s0) == t_INT)
    {
      long ss = itos(s0);
      switch(ss)
      { /* should depend on prec ? */
        case 3:  la = 6; break;
        default: la = 3; break;
      }
    }
    if (dnorm(ssig-1,st) < 0.1) /* |s - 1| < 0.1 */
      l2 = -(ssig - 0.5);
    else
    { /* l2 = Re( (s - 1/2) log (s-1) ) */
      double rlog, ilog; /* log(s-1) */
      dcxlog(ssig-1,st, &rlog,&ilog);
      l2 = (ssig - 0.5)*rlog - st*ilog;
    }
    l = (pariC2*(prec-2) - l2 + ssig*2*pariC1) / (2. * (1.+ log((double)la)));
    l2 = sqrt(ns)/2;
    if (l < l2) l = l2;
    lim = (long) ceil(l); if (lim < 2) lim = 2;
    l2 = (lim+ssig/2.-.25);
    nn = (long) 1 + ceil( sqrt(l2*l2 + st*st/4) * la / PI );
    if (DEBUGLEVEL) fprintferr("lim, nn: [%ld, %ld]\n",lim,nn);
    if ((ulong)nn >= maxprime()) err(primer1);
  }
  prec++; unr = realun(prec); /* one extra word of precision */
  
  tab = (GEN*)cgetg(nn, t_VEC); /* table of q^(-s), q = p^e */
  d = diffptr + 1;
  if (typ(s0) == t_INT)
  { /* no explog for 1/p^s */
    for (p=2; p < nn; p += *d++)
      tab[p] = divrr(unr, rpowsi(p, s0, prec));
    a = divrr(unr, rpowsi(nn, s0, prec));
  }
  else
  { /* general case */
    ms = gneg(s); p1 = cgetr(prec);
    for (p=2; p < nn; p += *d++)
    {
      affsr(p, p1);
      tab[p] = gexp(gmul(ms, mplog(p1)), prec);
    }
    affsr(nn,p1);
    a = gexp(gmul(ms, mplog(p1)), prec);
  }
  sqn = (long)sqrt(nn-1.);
  d = diffptr + 2; /* fill in odd prime powers */
  for (p=3; p <= sqn; p += *d++)
  {
    ulong oldq = p, q = p*p;
    while (q<(ulong)nn) { tab[q] = gmul(tab[p], tab[oldq]); oldq = q; q *= p; }
  }
  if (DEBUGLEVEL) msgtimer("tab[q^-s] from 1 to N-1"); 

  tabn = cgetg(nn, t_VECSMALL); ct = 0;
  for (i = nn-1; i; i>>=1) tabn[++ct] = (i-1)>>1;
  sim = y = unr;
  for (i=ct; i > 1; i--)
  {
    long j, av2 = avma;
    for (j=tabn[i]+1; j<=tabn[i-1]; j++)
      sim = gadd(sim, n_s(2*j+1, tab));
    sim = gerepileupto(av2, sim);
    y = gadd(sim, gmul(tab[2],y));
  }
  y = gadd(y, gmul2n(a,-1));
  if (DEBUGLEVEL) msgtimer("sum from 1 to N-1");

  invn2 = divrs(unr, nn*nn); lim2 = lim<<1;
  tes = bernreal(lim2, prec);
  if (typ(s0) == t_INT)
  {
    av2 = avma; avlim = stack_lim(av2,3);
    for (i=lim2-2; i>=2; i-=2)
    { /* using single prec (when (s0 + i) < 2^31) not faster (even at \p28) */
      u = mulri(mulrr(tes,invn2), mulii(addsi(i,s0), addsi(i-1,s0)));
      tes = addrr(bernreal(i,prec), divrs2_safe(u, i+1)); /* u / (i+1)(i+2) */
      if (low_stack(avlim,stack_lim(av2,3)))
      {
        if(DEBUGMEM>1) err(warnmem,"czeta");
        tes = gerepileuptoleaf(av2, tes);
      }
    }
    u = gmul(gmul(tes,invn2), gmul2n(mulii(s0, addsi(-1,s0)), -1));
    tes = gmulsg(nn, gaddsg(1, u));
  }
  else /* typ(s0) != t_INT */
  {
    s1 = gsub(gmul2n(s,1), unr);
    s2 = gmul(s, gsub(s,unr));
    s3 = gmul2n(invn2,3);
    av2 = avma; avlim = stack_lim(av2,3);
    s4 = gmul(invn2, gmul2n(gaddsg(4*lim-2,s1),1));
    s5 = gmul(invn2, gadd(s2, gmulsg(lim2, gaddgs(s1, lim2))));
    for (i = lim2-2; i>=2; i -= 2)
    {
      s5 = gsub(s5, s4);
      s4 = gsub(s4, s3);
      tes = gadd(bernreal(i,prec), gdivgs(gmul(s5,tes), (i+1)*(i+2)));
      if (low_stack(avlim,stack_lim(av2,3)))
      {
        GEN *gptr[3]; gptr[0]=&tes; gptr[1]=&s5; gptr[2]=&s4;
        if(DEBUGMEM>1) err(warnmem,"czeta");
        gerepilemany(av2,gptr,3);
      }
    }
    u = gmul(gmul(tes,invn2), gmul2n(s2, -1));
    tes = gmulsg(nn, gaddsg(1, u));
  }
  if (DEBUGLEVEL) msgtimer("Bernoulli sum");
  /* y += tes a / (s-1) */
  y = gadd(y, gmul(tes, gdiv(a, gsub(s, unr))));

END:
  if (funeq)
  {
    GEN pitemp = mppi(prec); setexpo(pitemp,2); /* 2Pi */
    y = gmul(gmul(y, ggamma(s,prec)), gpui(pitemp,gneg(s),prec));
    setexpo(pitemp,0); /* Pi/2 */
    y = gmul2n(gmul(y, gcos(gmul(pitemp,s),prec)), 1);
  }
  gaffect(y,res); avma = av; return res;
}

GEN
gzeta(GEN x, long prec)
{
  if (gcmp1(x)) err(talker,"argument equal to one in zeta");
  switch(typ(x))
  {
    case t_INT:
      if (is_bigint(x))
      {
        if (signe(x) > 0) return realun(prec);
        if (signe(x) < 0 && mod2(x) == 0) return realzero(prec);
      }
      return izeta(itos(x),prec);

    case t_REAL: case t_COMPLEX:
      return czeta(x,prec);

    case t_INTMOD: case t_PADIC:
      err(typeer,"gzeta");
    case t_SER:
      err(impl,"zeta of power series");
  }
  return transc(gzeta,x,prec);
}

void
gzetaz(GEN x, GEN y)
{
  long av=avma, prec = precision(y);

  if (!prec) err(infprecer,"gzetaz");
  gaffect(gzeta(x,prec),y); avma=av;
}

/***********************************************************************/
/**                                                                   **/
/**                    FONCTIONS POLYLOGARITHME                       **/
/**                                                                   **/
/***********************************************************************/

/* validity domain contains .005 < |x| < 230
 * Li_m(x = e^z) = sum_n=0 zeta(m-n) z^n / n!
 *    with zeta(1) := H_m - log(-z) */
static GEN
cxpolylog(long m, GEN x, long prec)
{
  long av=avma,li,i,n,bern_upto;
  GEN p1,z,h,q,s;

  if (gcmp1(x)) return izeta(m,prec);
  z=glog(x,prec); h=gneg_i(glog(gneg_i(z),prec));
  for (i=1; i<m; i++) h = gadd(h,ginv(stoi(i)));

  bern_upto=m+50; mpbern(bern_upto,prec);
  q=gun; s=izeta(m,prec);
  for (n=1; n<=m+1; n++)
  {
    q=gdivgs(gmul(q,z),n);
    s=gadd(s,gmul((n==(m-1))? h: izeta(m-n,prec),q));
  }

  n = m+3; z=gsqr(z); li = -(bit_accuracy(prec)+1);

  for(;;)
  {
    q = gdivgs(gmul(q,z),(n-1)*n);
    p1 = gmul(izeta(m-n,prec),q);
    s = gadd(s,p1);
    if (gexpo(p1) < li) break;
    n+=2;
    if (n>=bern_upto) { bern_upto += 50; mpbern(bern_upto,prec); }
  }
  return gerepileupto(av,s);
}

GEN
polylog(long m, GEN x, long prec)
{
  long av,av1,limpile,l,e,i,G,sx;
  GEN X,z,p1,p2,n,y,logx;

  if (m<0) err(talker,"negative index in polylog");
  if (!m) return gneg(ghalf);
  if (gcmp0(x)) return gcopy(x);
  av = avma;
  if (m==1)
    return gerepileupto(av, gneg(glog(gsub(gun,x), prec)));

  l = precision(x);
  if (!l) { l=prec; x=gmul(x, realun(l)); }
  e = gexpo(gnorm(x)); if (!e || e== -1) return cxpolylog(m,x,prec);
  X = (e > 0)? ginv(x): x;
  G = -bit_accuracy(l);
  n = icopy(gun);
  av1=avma; limpile=stack_lim(av1,1);
  y = p1 = X;
  for (i=2; ; i++)
  {
    n[2] = i; p1 = gmul(X,p1); p2 = gdiv(p1,gpuigs(n,m));
    y = gadd(y,p2);
    if (gexpo(p2) <= G) break;

    if (low_stack(limpile, stack_lim(av1,1)))
    { GEN *gptr[2]; gptr[0]=&y; gptr[1]=&p1;
      if(DEBUGMEM>1) err(warnmem,"polylog");
      gerepilemany(av1,gptr,2);
    }
  }
  if (e < 0) return gerepileupto(av, y);

  sx = gsigne(gimag(x));
  if (!sx)
  {
    if (m&1) sx = gsigne(gsub(gun,greal(x)));
    else     sx = - gsigne(greal(x));
  }
  z = cgetg(3,t_COMPLEX);
  z[1] = zero;
  z[2] = ldivri(mppi(l), mpfact(m-1));
  if (sx < 0) z[2] = lnegr((GEN)z[2]);
  logx = glog(x,l);

  if (m == 2)
  { /* same formula as below, written more efficiently */
    y = gneg_i(y);
    p1 = gmul2n(gsqr(gsub(logx, z)), -1); /* = (log(-x))^2 / 2 */
    p1 = gadd(divrs(gsqr(mppi(l)), 6), p1);
    p1 = gneg_i(p1);
  }
  else
  {
    GEN logx2 = gsqr(logx); p1 = gneg_i(ghalf);
    for (i=m-2; i>=0; i-=2)
      p1 = gadd(izeta(m-i,l), gmul(p1,gdivgs(logx2,(i+1)*(i+2))));
    if (m&1) p1 = gmul(logx,p1); else y = gneg_i(y);
    p1 = gadd(gmul2n(p1,1), gmul(z,gpuigs(logx,m-1)));
  }

  return gerepileupto(av, gadd(y,p1));
}

GEN
dilog(GEN x, long prec)
{
  return gpolylog(2, x, prec);
}

GEN
polylogd0(long m, GEN x, long flag, long prec)
{
  long k,l,av,fl,m2;
  GEN p1,p2,p3,y;

  m2=m&1; av=avma;
  if (gcmp0(x)) return gcopy(x);
  if (gcmp1(x) && m>=2) return m2?izeta(m,prec):gzero;
  l=precision(x);
  if (!l) { l=prec; x=gmul(x,realun(l)); }
  p1=gabs(x,prec); fl=0;
  if (gcmpgs(p1,1)>0) { x=ginv(x); p1=gabs(x,prec); fl=!m2; }

  p1=gneg_i(glog(p1,prec)); p2=gun;
  y=polylog(m,x,prec); y=m2?greal(y):gimag(y);
  for (k=1; k<m; k++)
  {
    p2=gdivgs(gmul(p2,p1),k);
    p3=m2?greal(polylog(m-k,x,prec)):gimag(polylog(m-k,x,prec));
    y=gadd(y,gmul(p2,p3));
  }
  if (m2)
  {
    if (flag)
      p2 = gdivgs(gmul(p2,p1),-2*m);
    else
      p2 = gdivgs(gmul(glog(gnorm(gsub(gun,x)),prec),p2),2*m);
    y=gadd(y,p2);
  }
  if (fl) y = gneg(y);
  return gerepileupto(av, y);
}

GEN
polylogd(long m, GEN x, long prec)
{
  return polylogd0(m,x,0,prec);
}

GEN
polylogdold(long m, GEN x, long prec)
{
  return polylogd0(m,x,1,prec);
}

GEN
polylogp(long m, GEN x, long prec)
{
  long k,l,av,fl,m2;
  GEN p1,y;

  m2=m&1; av=avma;
  if (gcmp0(x)) return gcopy(x);
  if (gcmp1(x) && m>=2) return m2?izeta(m,prec):gzero;
  l=precision(x);
  if (!l) { l=prec; x=gmul(x,realun(l)); }
  p1=gabs(x,prec); fl=0;
  if (gcmpgs(p1,1)>0) { x=ginv(x); p1=gabs(x,prec); fl=!m2; }

  p1=gmul2n(glog(p1,prec),1); mpbern(m>>1,prec);
  y=polylog(m,x,prec); y=m2?greal(y):gimag(y);

  if (m==1)
  {
    p1=gmul2n(p1,-2); y=gadd(y,p1);
  }
  else
  {
    GEN p2=gun, p3, p4, p5, p51=cgetr(prec);

    for (k=1; k<m; k++)
    {
      p2=gdivgs(gmul(p2,p1),k);
      if (!(k&1) || k==1)
      {
	if (k!=1)
	{
	  p5=(GEN)bern(k>>1);
	  if (bernzone[2]>prec) { affrr(p5,p51); p5=p51; }
	  p4=gmul(p2,p5);
	}
	else p4=gneg_i(gmul2n(p2,-1));
	p3=polylog(m-k,x,prec); p3=m2?greal(p3):gimag(p3);
	y=gadd(y,gmul(p4,p3));
      }
    }
  }
  if (fl) y = gneg(y);
  return gerepileupto(av, y);
}

GEN
gpolylog(long m, GEN x, long prec)
{
  long i,lx,av=avma,v,n;
  GEN y,p1,p2;

  if (m<=0)
  {
    p1=polx[0]; p2=gsub(gun,p1);
    for (i=1; i<=(-m); i++)
      p1=gmul(polx[0],gadd(gmul(p2,derivpol(p1)),gmulsg(i,p1)));
    p1=gdiv(p1,gpuigs(p2,1-m));
    return gerepileupto(av, poleval(p1,x));
  }

  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC: case t_FRACN:
    case t_COMPLEX: case t_QUAD:
      return polylog(m,x,prec);

    case t_INTMOD: case t_PADIC:
      err(impl, "padic polylogarithm");
    case t_POLMOD:
      p1=roots((GEN)x[1],prec); lx=lg(p1); p2=cgetg(lx,t_COL);
      for (i=1; i<lx; i++) p2[i]=lpoleval((GEN)x[2],(GEN)p1[i]);
      y=cgetg(lx,t_COL);
      for (i=1; i<lx; i++) y[i]=(long)polylog(m,(GEN)p2[i],prec);
      return gerepileupto(av, y);

    case t_POL: case t_RFRAC: case t_RFRACN:
      p1=tayl(x,gvar(x),precdl);
      return gerepileupto(av, gpolylog(m,p1,prec));

    case t_SER:
      if (!m) return gneg(ghalf);
      if (m==1)
      {
	p1=glog(gsub(gun,x),prec);
	return gerepileupto(av, gneg(p1));
      }
      if (valp(x)<=0) err(impl,"polylog around a!=0");
      v=varn(x); n=(lg(x)-2)/valp(x); y=ggrando(polx[v],lg(x)-2);
      for (i=n; i>=1; i--)
      {
	p1=gadd(gpuigs(stoi(i),-m),y);
	y=gmul(x,p1);
      }
      return gerepileupto(av, y);

    case t_VEC: case t_COL: case t_MAT:
      lx=lg(x); y=cgetg(lx,typ(x));
      for (i=1; i<lx; i++)
	y[i]=(long)gpolylog(m,(GEN)x[i],prec);
      return y;
  }
  err(typeer,"gpolylog");
  return NULL; /* not reached */
}

void
gpolylogz(long m, GEN x, GEN y)
{
  long av=avma, prec = precision(y);

  if (!prec) err(infprecer,"gpolylogz");
  gaffect(gpolylog(m,x,prec),y); avma=av;
}

GEN
polylog0(long m, GEN x, long flag, long prec)
{
  switch(flag)
  {
    case 0: return gpolylog(m,x,prec);
    case 1: return polylogd(m,x,prec);
    case 2: return polylogdold(m,x,prec);
    case 3: return polylogp(m,x,prec);
    default: err(flagerr,"polylog");
  }
  return NULL; /* not reached */
}

static GEN
qq(GEN x, long prec)
{
  long tx=typ(x);

  if (tx==t_PADIC) return x;
  if (is_scalar_t(tx))
  {
    long l=precision(x);
    GEN p1,p2,q;

    if (tx != t_COMPLEX || gcmp((GEN)x[2],gzero)<=0)
      err(talker,"argument must belong to upper half-plane");

    if (!l) l=prec; p1=mppi(l); setexpo(p1,2);
    p2=cgetg(3,t_COMPLEX); p2[1]=zero; p2[2]=(long)p1; /* 2*I*Pi */
    q=gmul(x,p2); return gexp(q,prec);
  }
  if (tx != t_POL && tx != t_SER)
    err(talker,"bad argument for modular function");

  return tayl(x,gvar(x),precdl);
}

static GEN
inteta(GEN q)
{
  long tx=typ(q);
  GEN p1,ps,qn,y;

  y=gun; qn=gun; ps=gun;
  if (tx==t_PADIC)
  {
    if (valp(q) <= 0)
      err(talker,"non-positive valuation in inteta");
    for(;;)
    {
      p1=gneg_i(gmul(ps,gmul(q,gsqr(qn))));
      y=gadd(y,p1); qn=gmul(qn,q); ps=gmul(p1,qn);
      p1=y; y=gadd(y,ps); if (gegal(p1,y)) return y;
    }
  }
  else
  {
    long l = 0, v = 0; /* gcc -Wall */
    long av = avma, lim = stack_lim(av,3);

    if (is_scalar_t(tx)) l = -bit_accuracy(precision(q));
    else
    {
      v=gvar(q); tx = 0;
      if (valp(q) <= 0)
        err(talker,"non-positive valuation in inteta");
    }
    for(;;)
    {
      p1=gneg_i(gmul(ps,gmul(q,gsqr(qn))));
      y=gadd(y,p1); qn=gmul(qn,q); ps=gmul(p1,qn);
      y=gadd(y,ps);
      if (tx)
        { if (gexpo(ps)-gexpo(y) < l) return y; }
      else
        { if (gval(ps,v)>=precdl) return y; }
      if (low_stack(lim, stack_lim(av,3)))
      {
        GEN *gptr[3];
        if(DEBUGMEM>1) err(warnmem,"inteta");
        gptr[0]=&y; gptr[1]=&qn; gptr[2]=&ps;
        gerepilemany(av,gptr,3);
      }
    }
  }
}

GEN
eta(GEN x, long prec)
{
  long av = avma;
  GEN q = qq(x,prec);
  return gerepileupto(av,inteta(q));
}

/* returns the true value of eta(x) for Im(x) > 0, using reduction */
GEN
trueeta(GEN x, long prec)
{
  long tx=typ(x), av=avma, tetpil,l;
  GEN p1,p2,q,q24,n,z,m,unapprox;

  if (!is_scalar_t(tx)) err(typeer,"trueeta");
  if (tx != t_COMPLEX || gsigne((GEN)x[2])<=0)
    err(talker,"argument must belong to upper half-plane");
  l=precision(x); if (l) prec=l;
  p1=mppi(prec); setexpo(p1,2);
  p2=cgetg(3,t_COMPLEX); p2[1]=zero; p2[2]=(long)p1; /* 2*I*Pi */
  z=gexp(gdivgs(p2,24),prec); /* exp(2*I*Pi/24) */
  unapprox=gsub(gun,gpuigs(stoi(10),-8));
  m=gun;
  for(;;)
  {
    n=ground(greal(x));
    if (signe(n)) {x=gsub(x,n); m=gmul(m,powgi(z,n));}
    if (gcmp(gnorm(x), unapprox)>=0) break;
    m=gmul(m,gsqrt(gdiv(gi,x),prec)); x=gdivsg(-1,x);
  }
  q=gmul(p2,x);
  q24=gexp(gdivgs(q,24),prec); q=gpuigs(q24,24);
  p1=gmul(m,q24); q = inteta(q); tetpil=avma;
  return gerepile(av,tetpil,gmul(p1,q));
}

GEN
eta0(GEN x, long flag,long prec)
{
  return flag? trueeta(x,prec): eta(x,prec);
}

GEN
jell(GEN x, long prec)
{
  long av=avma,tetpil,tx = typ(x);
  GEN p1;

  if (!is_scalar_t(tx) || tx == t_PADIC)
  {
    GEN p2,q = qq(x,prec);
    p1=gdiv(inteta(gsqr(q)), inteta(q));
    p1=gmul2n(gsqr(p1),1);
    p1=gmul(q,gpuigs(p1,12));
    p2=gaddsg(768,gadd(gsqr(p1),gdivsg(4096,p1)));
    p1=gmulsg(48,p1); tetpil=avma;
    return gerepile(av,tetpil,gadd(p2,p1));
  }
  p1=gdiv(trueeta(gmul2n(x,1),prec),trueeta(x,prec));
  p1=gsqr(gsqr(gsqr(p1)));
  p1=gadd(gmul2n(gsqr(p1),8), ginv(p1)); tetpil=avma;
  return gerepile(av,tetpil,gpuigs(p1,3));
}

GEN
wf2(GEN x, long prec)
{
  long av=avma,tetpil;
  GEN p1,p2;

  p1=gsqrt(gdeux,prec);
  p2=gdiv(trueeta(gmul2n(x,1),prec),trueeta(x,prec));
  tetpil=avma;
  return gerepile(av,tetpil,gmul(p1,p2));
}

GEN
wf1(GEN x, long prec)
{
  long av=avma,tetpil;
  GEN p1,p2;

  p1=trueeta(gmul2n(x,-1),prec); p2=trueeta(x,prec);
  tetpil=avma;
  return gerepile(av,tetpil,gdiv(p1,p2));
}

GEN
wf(GEN x, long prec)
{
  long av=avma,tetpil;
  GEN p1,p2;

  p1=gdiv(trueeta(gmul2n(gaddgs(x,1),-1),prec),trueeta(x,prec));
  p2=cgetg(3,t_COMPLEX); p2[1]=zero; p2[2]=ldivrs(mppi(prec),-24);
  p2=gexp(p2,prec); tetpil=avma;
  return gerepile(av,tetpil,gmul(p1,p2));
}

GEN
weber0(GEN x, long flag,long prec)
{
  switch(flag)
  {
    case 0: return wf(x,prec);
    case 1: return wf1(x,prec);
    case 2: return wf2(x,prec);
    default: err(flagerr,"weber");
  }
  return NULL; /* not reached */
}

static GEN
sagm(GEN x, long prec)
{
  GEN p1,a,b,a1,b1,y;
  long av,tetpil,l,ep;

  if (gcmp0(x)) return gcopy(x);
  switch(typ(x))
  {
    case t_REAL:
      l = precision(x); y = cgetr(l); av=avma;
      a1 = x; b1 = realun(l);
      l = 5-bit_accuracy(prec);
      do
      {
	a=a1; b=b1; a1 = addrr(a,b);
        setexpo(a1,expo(a1)-1);
	b1=mpsqrt(mulrr(a,b));
      }
      while (expo(subrr(b1,a1))-expo(b1) >= l);
      affrr(a1,y); avma=av; return y;

    case t_COMPLEX:
      if (gcmp0((GEN)x[2]))
        return transc(sagm,(GEN)x[1],prec);
      av=avma; l=precision(x); if (l) prec=l;
      a1=x; b1=gun; l = 5-bit_accuracy(prec);
      do
      {
	a=a1; b=b1;
	a1=gmul2n(gadd(a,b),-1);
	b1=gsqrt(gmul(a,b),prec);
      }
      while (gexpo(gsub(b1,a1))-gexpo(b1) >= l);
      tetpil=avma; return gerepile(av,tetpil,gcopy(a1));

    case t_PADIC:
      av=avma; a1=x; b1=gun; l=precp(x);
      do
      {
	a=a1; b=b1;
	a1=gmul2n(gadd(a,b),-1); b1=gsqrt(gmul(a,b),0);
	p1=gsub(b1,a1); ep=valp(p1)-valp(b1);
	if (ep<=0) { b1=gneg_i(b1); p1=gsub(b1,a1); ep=valp(p1)-valp(b1); }
      }
      while (ep<l && !gcmp0(p1));
      tetpil=avma; return gerepile(av,tetpil,gcopy(a1));

    case t_SER:
      av=avma; a1=x; b1=gun; l=lg(x)-2;
      do
      {
	a=a1; b=b1;
	a1=gmul2n(gadd(a,b),-1); b1=gsqrt(gmul(a,b),prec);
	p1=gsub(b1,a1); ep=valp(p1)-valp(b1);
      }
      while (ep<l && !gcmp0(p1));
      tetpil=avma; return gerepile(av,tetpil,gcopy(a1));

    case t_INTMOD:
      err(impl,"agm of mod");
  }
  return transc(sagm,x,prec);
}

GEN
agm(GEN x, GEN y, long prec)
{
  long av,tetpil, ty=typ(y);
  GEN z;

  if (is_matvec_t(ty))
  {
    ty=typ(x);
    if (is_matvec_t(ty)) err(talker,"agm of two vector/matrices");
    z=x; x=y; y=z;
  }
  if (gcmp0(y)) return gcopy(y);
  av=avma; z=sagm(gdiv(x,y),prec); tetpil=avma;
  return gerepile(av,tetpil,gmul(y,z));
}

GEN
logagm(GEN q)
{
  long av=avma,prec=lg(q),tetpil,s,n,lim;
  GEN y,q4,q1;

  if (typ(q)!=t_REAL) err(typeer,"logagm");
  if (signe(q)<=0) err(talker,"non positive argument in logagm");
  if (expo(q)<0) s=1; else { q=ginv(q); s=0; }
  lim = - (bit_accuracy(prec) >> 1);
  q1 = NULL; /* gcc -Wall */
  for (n=0; expo(q)>=lim; n++) { q1=q; q=gsqr(q); }
  q4=gmul2n(q,2);
  if (!n) q1=gsqrt(q,prec);
  y=divrr(mppi(prec), agm(addsr(1,q4),gmul2n(q1,2),prec));
  tetpil=avma; y=gmul2n(y,-n); if (s) setsigne(y,-1);
  return gerepile(av,tetpil,y);
}

GEN
glogagm(GEN x, long prec)
{
  long av,tetpil;
  GEN y,p1,p2;

  switch(typ(x))
  {
    case t_REAL:
      if (signe(x)>=0) return logagm(x);

      y=cgetg(3,t_COMPLEX); y[2]=lmppi(lg(x));
      setsigne(x,1); y[1]=(long)logagm(x);
      setsigne(x,-1); return y;

    case t_COMPLEX:
      y=cgetg(3,t_COMPLEX); y[2]=larg(x,prec);
      av=avma; p1=glogagm(gnorm(x),prec); tetpil=avma;
      y[1]=lpile(av,tetpil,gmul2n(p1,-1));
      return y;

    case t_PADIC:
      return palog(x);

    case t_SER:
      av=avma; if (valp(x)) err(negexper,"glogagm");
      p1=gdiv(derivser(x),x);
      p1=integ(p1,varn(x));
      if (gcmp1((GEN)x[2])) return gerepileupto(av,p1);
      p2=glogagm((GEN)x[2],prec); tetpil=avma;
      return gerepile(av,tetpil,gadd(p1,p2));

    case t_INTMOD:
      err(typeer,"glogagm");
  }
  return transc(glogagm,x,prec);
}

GEN
theta(GEN q, GEN z, long prec)
{
  long av=avma,tetpil,l,n;
  GEN ps,qn,qnold,y,zy,lq,ps2,p1,k,zold;

  l=precision(q); if (l) prec=l;
  p1=realun(prec); z=gmul(p1,z);
  if (!l) q=gmul(p1,q);
  if (gexpo(q)>=0) err(thetaer1);
  zy = gimag(z);
  zold = NULL; /* gcc -Wall */
  if (gcmp0(zy)) k=gzero;
  else
  {
    lq=glog(q,prec); k=ground(gdiv(zy,greal(lq)));
    if (!gcmp0(k)) { zold=z; z=gadd(z,gdiv(gmul(lq,k),gi)); }
  }
  y=gsin(z,prec); n=0; qn=gun;
  ps2=gsqr(q); ps=gneg_i(ps2);
  do
  {
    n++; p1=gsin(gmulsg(2*n+1,z),prec);
    qnold=qn; qn=gmul(qn,ps);
    ps=gmul(ps,ps2); p1=gmul(p1,qn); y=gadd(y,p1);
  }
  while (gexpo(qnold) >= -bit_accuracy(prec));
  if (signe(k))
  {
    y=gmul(y,gmul(gpui(q,gsqr(k),prec),
                  gexp(gmul2n(gmul(gmul(gi,zold),k),1),prec)));
    if (mod2(k)) y=gneg_i(y);
  }
  p1=gmul2n(gsqrt(gsqrt(q,prec),prec),1); tetpil=avma;
  return gerepile(av,tetpil,gmul(p1,y));
}

GEN
thetanullk(GEN q, long k, long prec)
{
  long av=avma,tetpil,l,n;
  GEN p1,ps,qn,y,ps2;

  l=precision(q);
  if (!l) { l=prec; q=gmul(q,realun(l)); }
  if (gexpo(q)>=0) err(thetaer1);

  if (!(k&1)) { avma = av; return gzero; }
  ps2=gsqr(q); ps=gneg_i(ps2);
  qn = gun; y = gun; n = 0;

  do
  {
    n++; p1=gpuigs(stoi(n+n+1),k); qn=gmul(qn,ps);
    ps=gmul(ps,ps2); p1=gmul(p1,qn); y=gadd(y,p1);
  }
  while (gexpo(p1) >= -bit_accuracy(l));
  p1=gmul2n(gsqrt(gsqrt(q,prec),prec),1); tetpil=avma;
  if (k&2) { p1=gneg_i(p1); tetpil=avma; }
  return gerepile(av,tetpil,gmul(p1,y));
}

GEN
jbesselh(GEN n, GEN z, long prec)
{
  long av,tetpil,k,l,i,lz;
  GEN y,p1,p2,zinv,p0,s,c;

  if (typ(n)!=t_INT) err(talker,"not an integer index in jbesselh");
  k=itos(n); if (k<0) err(impl,"ybesselh");

  switch(typ(z))
  {
    case t_REAL: case t_COMPLEX:
      if (gcmp0(z)) return gzero;
      av=avma; zinv=ginv(z);
      l=precision(z); if (l>prec) prec=l;
      gsincos(z,&s,&c,prec);
      p1=gmul(zinv,s);
      if (k)
      {
        p0=p1; p1=gmul(zinv,gsub(p0,c));
	for (i=2; i<=k; i++)
	{
	  p2=gsub(gmul(gmulsg(2*i-1,zinv),p1),p0);
          p0=p1; p1=p2;
	}
      }
      p2=gsqrt(gdiv(gmul2n(z,1),mppi(prec)),prec);
      tetpil=avma; return gerepile(av,tetpil,gmul(p2,p1));

    case t_VEC: case t_COL: case t_MAT:
      lz=lg(z); y=cgetg(lz,typ(z));
      for (i=1; i<lz; i++)
	y[i]=(long)jbesselh(n,(GEN)z[i],prec);
      return y;

    case t_INT: case t_FRAC: case t_FRACN:
      av=avma; p1=cgetr(prec); gaffect(z,p1); tetpil=avma;
      return gerepile(av,tetpil,jbesselh(n,p1,prec));

    case t_QUAD:
      av=avma; p1=gmul(z,realun(prec)); tetpil=avma;
      return gerepile(av,tetpil,jbesselh(n,p1,prec));

    case t_POL: case t_RFRAC: case t_RFRACN:
      av=avma; p1=tayl(z,gvar(z),precdl); tetpil=avma;
      return gerepile(av,tetpil,jbesselh(n,p1,prec));

    case t_POLMOD:
      av=avma; p1=roots((GEN)z[1],prec); lz=lg(p1); p2=cgetg(lz,t_COL);
      for (i=1; i<lz; i++) p2[i]=lpoleval((GEN)z[2],(GEN)p1[i]);
      tetpil=avma; y=cgetg(lz,t_COL);
      for (i=1; i<lz; i++) y[i]=(long)jbesselh(n,(GEN)p2[i],prec);
      return gerepile(av,tetpil,y);

    case t_PADIC:
      err(impl,"p-adic jbessel function");
    case t_SER:
      err(impl,"jbessel of power series");
  }
  err(typeer,"jbesselh");
  return NULL; /* not reached */
}
